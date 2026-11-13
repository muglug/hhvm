// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Module used to declare class types.
//! For each class we want to build a complete type, that is the type of
//! the methods defined in the class plus everything that was inherited.
//!
//! c.f. `hphp/hack/src/decl/decl_folded_class.ml`, which this follows
//! function by function. The recursion over the ancestors
//! (`declare_class_and_parents`, `class_parents_decl`,
//! `class_decl_if_missing`) is in `provider.rs`.
//!
//! What this does not do: the OCaml also builds the types of the members of
//! the class for its member heaps (`build_constructor_fun_elt`,
//! `build_prop_sprop_ty`, `build_method_fun_elt`), which have no counterpart
//! here: the typechecker looks member types up lazily (`Decl_class`).
//!
//! The OCaml lists that are built by consing are `VecDeque`s here (`x :: l`
//! is `l.push_front(x)`), so that `dc_decl_errors` is in the order of the
//! OCaml list (the typechecker reports the errors in that order).

use std::collections::VecDeque;
use std::sync::Arc;

use hash::IndexMap;
use hash::IndexSet;
use oxidized::decl_fold_options::DeclFoldOptions;
use pos::ClassConstName;
use pos::MethodName;
use pos::ModuleName;
use pos::Positioned;
use pos::PropName;
use pos::Symbol;
use pos::TypeConstName;
use pos::TypeName;
use special_names as sn;
use ty::decl::AbstractTypeconst;
use ty::decl::CeVisibility;
use ty::decl::ClassConst;
use ty::decl::ClassConstKind;
use ty::decl::ClassEltFlags;
use ty::decl::ClassEltFlagsArgs;
use ty::decl::ClassishKind;
use ty::decl::ConcreteTypeconst;
use ty::decl::ConsistentKind;
use ty::decl::FoldedClass;
use ty::decl::FoldedElement;
use ty::decl::ShallowClass;
use ty::decl::ShallowClassConst;
use ty::decl::ShallowMethod;
use ty::decl::ShallowProp;
use ty::decl::ShallowTypeconst;
use ty::decl::TaccessType;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::TypeConst;
use ty::decl::Typeconst;
use ty::decl::UserAttribute;
use ty::decl::Visibility;
use ty::decl::folded::Constructor;
use ty::decl::ty::UserAttributeParam;
use ty::decl_error::DeclError;
use ty::reason::Reason;

use super::Result;
use super::Substitution;
use super::decl_requirements;
use super::decl_requirements::ClassRequirements;
use super::inherit;
use super::inherit::Inherited;

mod decl_enum;

/// The folded decls of the ancestors of a class that could be declared
/// (`Decl_store.class_entries S_map.t`, without the member heaps).
pub type Parents<R> = IndexMap<TypeName, Arc<FoldedClass<R>>>;

#[derive(Debug)]
pub struct DeclFolder<'a, R: Reason> {
    /// Options affecting typechecking behaviors.
    opts: &'a DeclFoldOptions,
    /// The class whose folded decl we are producing.
    child: &'a ShallowClass<R>,
}

/// `` [ `Extends_pass | `Traits_pass | `Xhp_pass ] ``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pass {
    ExtendsPass,
    TraitsPass,
    XhpPass,
}

/// `Attributes.mem name attrs`
fn attributes_mem<P>(name: TypeName, attrs: &[UserAttribute<P>]) -> bool {
    attrs.iter().any(|ua| ua.name.id() == name)
}

/// `Attributes.find name attrs`
fn attributes_find<P>(name: TypeName, attrs: &[UserAttribute<P>]) -> Option<&UserAttribute<P>> {
    attrs.iter().find(|ua| ua.name.id() == name)
}

//*****************************************************************************
// Checking that the kind of a class is compatible with its parent
// For example, a class cannot extend an interface, an interface cannot
// extend a trait etc ...
//*****************************************************************************

pub fn check_extend_kind<P: Clone>(
    parent_pos: &P,
    parent_kind: ClassishKind,
    parent_name: TypeName,
    child_pos: &P,
    child_kind: ClassishKind,
    child_name: TypeName,
) -> Option<DeclError<P>> {
    match (parent_kind, child_kind) {
        // What is allowed
        (ClassishKind::Cclass(_), ClassishKind::Cclass(_))
        | (ClassishKind::Ctrait, ClassishKind::Ctrait)
        | (ClassishKind::Cinterface, ClassishKind::Cinterface) => None,
        // enums extend BuiltinEnum under the hood
        (ClassishKind::Cclass(k), ClassishKind::Cenum | ClassishKind::CenumClass(_))
            if k.is_abstract() =>
        {
            None
        }
        (ClassishKind::CenumClass(_), ClassishKind::CenumClass(_)) => None,
        _ => {
            // What is disallowed
            Some(DeclError::WrongExtendKind {
                parent_pos: parent_pos.clone(),
                parent_kind,
                parent_name,
                // TODO: T87242856 (`Pos_or_decl.unsafe_to_raw_pos`)
                pos: child_pos.clone(),
                kind: child_kind,
                name: child_name,
            })
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub fn check_use_kind<P: Clone>(
    parent_pos: &P,
    parent_kind: ClassishKind,
    parent_name: TypeName,
    parent_is_internal: bool,
    child_pos: &P,
    child_kind: ClassishKind,
    child_name: TypeName,
    child_is_module_level_trait: bool,
) -> Option<DeclError<P>> {
    match (parent_kind, child_kind) {
        (ClassishKind::Ctrait, ClassishKind::Ctrait)
            if child_is_module_level_trait && parent_is_internal =>
        {
            Some(DeclError::WrongUseKind {
                parent_pos: parent_pos.clone(),
                parent_name,
                // `Pos_or_decl.unsafe_to_raw_pos`
                pos: child_pos.clone(),
                name: child_name,
            })
        }
        _ => None,
    }
}

//*****************************************************************************
// Functions used retrieve everything implemented in parent classes
// The return values:
// env: the new environment
// parents: the name of all the parents and grand parents of the class this
//          includes traits.
// is_complete: true if all the parents live in Hack
//*****************************************************************************

/// `S_set.t * [ `Extends_pass | `Traits_pass | `Xhp_pass ] * decl_error list`
pub type ParentsAcc<R> = (
    IndexSet<TypeName>,
    Pass,
    VecDeque<DeclError<<R as Reason>::Pos>>,
);

/// Adds the traits/classes which are part of a class' hierarchy.
///
/// Traits are tracked separately but merged into the parents list when
/// typechecking so that the class can access the trait members which are
/// declared as private/protected.
pub fn add_grand_parents_or_traits<R: Reason>(
    parent_pos: &R::Pos,
    shallow_class: &ShallowClass<R>,
    acc: ParentsAcc<R>,
    parent_type: &FoldedClass<R>,
) -> ParentsAcc<R> {
    let (extends, pass, mut decl_errors) = acc;
    let class_pos = shallow_class.name.pos();
    let classish_kind = shallow_class.kind;
    let class_name = shallow_class.name.id();
    let class_is_module_level_trait = attributes_mem(
        *sn::user_attributes::uaModuleLevelTrait,
        &shallow_class.user_attributes,
    );
    match pass {
        Pass::ExtendsPass => match check_extend_kind(
            parent_pos,
            parent_type.kind,
            parent_type.name,
            class_pos,
            classish_kind,
            class_name,
        ) {
            Some(err) => decl_errors.push_front(err),
            None => {}
        },
        Pass::TraitsPass => match check_use_kind(
            parent_pos,
            parent_type.kind,
            parent_type.name,
            parent_type.is_internal,
            class_pos,
            classish_kind,
            class_name,
            class_is_module_level_trait,
        ) {
            Some(err) => decl_errors.push_front(err),
            None => {}
        },
        Pass::XhpPass => {}
    }

    // If we are crawling the xhp attribute deps, we need to merge their xhp deps
    // as well
    let mut extends_ = extends;
    if pass == Pass::XhpPass {
        extends_.extend(parent_type.extends.iter().copied());
        extends_.extend(parent_type.xhp_attr_deps.iter().copied());
    } else {
        extends_.extend(parent_type.extends.iter().copied());
    }
    (extends_, pass, decl_errors)
}

pub fn get_class_parent_or_trait<R: Reason>(
    shallow_class: &ShallowClass<R>,
    parent_cache: &Parents<R>,
    (mut parents, pass, decl_errors): ParentsAcc<R>,
    ty: &Ty<R>,
) -> ParentsAcc<R> {
    let (_, parent_pos_id, _) = ty.unwrap_class_type();
    let parent = parent_pos_id.id();
    // If we already had this exact trait, we need to flag trait reuse
    parents.insert(parent);
    // `Decl_env.get_class_and_add_dep ~cache:parent_cache ~shmem_fallback:false
    // ~fallback:Decl_env.no_fallback`
    let parent_type = parent_cache.get(&parent);
    match parent_type {
        None => (parents, pass, decl_errors),
        Some(parent_type) => {
            let acc = (parents, pass, decl_errors);
            add_grand_parents_or_traits(parent_pos_id.pos(), shallow_class, acc, parent_type)
        }
    }
}

/// The first set is the names of the `extend`ed parents, `use`d traits and XHP attributes.
/// It does not include the `implement`ed interfaces.
pub fn get_class_parents_and_traits<R: Reason>(
    shallow_class: &ShallowClass<R>,
    parent_cache: &Parents<R>,
    decl_errors: VecDeque<DeclError<R::Pos>>,
) -> (
    IndexSet<TypeName>,
    IndexSet<TypeName>,
    VecDeque<DeclError<R::Pos>>,
) {
    let parents = IndexSet::default();
    // extends parents
    let acc = (parents, Pass::ExtendsPass, decl_errors);
    let (parents, _, decl_errors) = (shallow_class.extends.iter()).fold(acc, |acc, ty| {
        get_class_parent_or_trait(shallow_class, parent_cache, acc, ty)
    });
    // traits
    let acc = (parents, Pass::TraitsPass, decl_errors);
    let (parents, _, decl_errors) = (shallow_class.uses.iter()).fold(acc, |acc, ty| {
        get_class_parent_or_trait(shallow_class, parent_cache, acc, ty)
    });
    // XHP classes whose attributes were imported via "attribute :foo;" syntax
    let acc = (IndexSet::default(), Pass::XhpPass, decl_errors);
    let (xhp_parents, _, decl_errors) = (shallow_class.xhp_attr_uses.iter())
        .fold(acc, |acc, ty| {
            get_class_parent_or_trait(shallow_class, parent_cache, acc, ty)
        });
    (parents, xhp_parents, decl_errors)
}

/// `Ast_defs.is_c_concrete`
fn is_c_concrete(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::Cclass(k) | ClassishKind::CenumClass(k) => k.is_concrete(),
        ClassishKind::Cinterface | ClassishKind::Ctrait | ClassishKind::Cenum => false,
    }
}

pub fn class_is_abstract<R: Reason>(c: &ShallowClass<R>) -> bool {
    match c.kind {
        ClassishKind::Cclass(k) => k.is_abstract(),
        ClassishKind::CenumClass(k) => k.is_abstract(),
        ClassishKind::Cinterface | ClassishKind::Ctrait | ClassishKind::Cenum => true,
    }
}

pub fn synthesize_const_defaults<R: Reason>(c: &mut ClassConst<R>) {
    match c.kind {
        ClassConstKind::CCAbstract(true) => c.kind = ClassConstKind::CCConcrete,
        _ => {}
    }
}

/// When all type constants have been inherited and declared, this step synthesizes
/// the defaults of abstract type constants into concrete type constants.
pub fn synthesize_typeconst_defaults<R: Reason>(
    k: TypeConstName,
    tc: &TypeConst<R>,
    (typeconsts, consts): (
        &mut IndexMap<TypeConstName, TypeConst<R>>,
        &mut IndexMap<ClassConstName, ClassConst<R>>,
    ),
) {
    match &tc.kind {
        Typeconst::TCAbstract(AbstractTypeconst {
            default: Some(default),
            ..
        }) => {
            let concrete = TypeConst {
                kind: Typeconst::TCConcrete(ConcreteTypeconst {
                    ty: default.clone(),
                }),
                is_concretized: true,
                ..tc.clone()
            };
            typeconsts.insert(k, concrete);
            // OCaml 4.06 has an update method that makes this operation much more ergonomic
            let constant = consts.get_mut(&ClassConstName(k.as_symbol()));
            if let Some(c) = constant {
                c.kind = ClassConstKind::CCConcrete;
            }
        }
        _ => {}
    }
}

pub fn extract_sealed_classnames<P>(
    attrs: Option<&UserAttribute<P>>,
) -> Option<IndexSet<TypeName>> {
    match attrs {
        None => None,
        Some(UserAttribute { params, .. }) => {
            let cn_params = (params.iter()).filter_map(|p| match p {
                UserAttributeParam::Classname(cn) => Some(*cn),
                _ => None,
            });
            Some(cn_params.collect())
        }
    }
}

pub fn get_class_sealed_allowlist<R: Reason>(c: &ShallowClass<R>) -> Option<IndexSet<TypeName>> {
    extract_sealed_classnames(attributes_find(
        *sn::user_attributes::uaSealed,
        &c.user_attributes,
    ))
}

pub fn get_method_sealed_allowlist<R: Reason>(m: &ShallowMethod<R>) -> Option<IndexSet<TypeName>> {
    extract_sealed_classnames(attributes_find(
        *sn::user_attributes::uaSealed,
        &m.attributes,
    ))
}

pub fn get_overlapping_tparams<R: Reason>(m: &ShallowMethod<R>) -> Option<IndexSet<Symbol>> {
    match attributes_find(*sn::user_attributes::uaOverlapping, &m.attributes) {
        None => None,
        Some(UserAttribute { params, .. }) => {
            let params = (params.iter()).filter_map(|p| match p {
                UserAttributeParam::String(s) => Some(Symbol::new(s.to_string())),
                _ => None,
            });
            Some(params.collect())
        }
    }
}

pub fn get_instantiated_ancestors_and_self<R: Reason>(
    parent_cache: &Parents<R>,
    ht: &Ty<R>,
) -> IndexMap<TypeName, Ty<R>> {
    let (_r, pos_id, paraml) = ht.unwrap_class_type();
    let class_name = pos_id.id();
    // `Decl_env.get_class_and_add_dep ~cache:parent_cache ~shmem_fallback:false
    // ~fallback:Decl_env.no_fallback`
    let class_ = parent_cache.get(&class_name);
    match class_ {
        None => {
            // The class lives in PHP land
            std::iter::once((class_name, ht.clone())).collect()
        }
        Some(class_) => {
            let subst = decl_requirements::make_substitution(class_, paraml);
            let substitution = Substitution { subst: &subst };
            let mut instantiated_ancestors: IndexMap<TypeName, Ty<R>> = (class_.ancestors.iter())
                .map(|(name, ty)| (*name, substitution.instantiate(ty)))
                .collect();
            instantiated_ancestors.insert(class_name, ht.clone());
            instantiated_ancestors
        }
    }
}

pub fn visibility(
    class_id: TypeName,
    module_: Option<ModuleName>,
    visibility: Visibility,
) -> CeVisibility {
    match visibility {
        Visibility::Public => CeVisibility::Public,
        Visibility::Protected => CeVisibility::Protected(class_id),
        Visibility::Private => CeVisibility::Private(class_id),
        Visibility::Internal => match module_ {
            Some(m) => CeVisibility::Internal(m),
            None => CeVisibility::Public,
        },
        Visibility::ProtectedInternal => match module_ {
            Some(m) => CeVisibility::ProtectedInternal(class_id, m),
            None => CeVisibility::Protected(class_id),
        },
    }
}

/// The element of the constructor (the OCaml also builds its `fun_elt` for
/// the member heaps).
pub fn build_constructor<R: Reason>(
    origin_class: &ShallowClass<R>,
    method_: &ShallowMethod<R>,
) -> Option<FoldedElement> {
    let class_name = origin_class.name.id();
    let vis = visibility(
        class_name,
        origin_class.module.as_ref().map(Positioned::id),
        method_.visibility,
    );
    let meth_flags = &method_.flags;
    let cstr = FoldedElement {
        flags: ClassEltFlags::new(ClassEltFlagsArgs {
            xhp_attr: None,
            is_final: meth_flags.is_final(),
            is_abstract: meth_flags.is_abstract(),
            is_lateinit: false,
            is_const: false,
            is_lsb: false,
            is_synthesized: false,
            is_superfluous_override: false,
            is_dynamicallycallable: false,
            is_readonly_prop_or_needs_concrete: false,
            supports_dynamic_type: meth_flags.supports_dynamic_type(),
            needs_init: false,
            no_auto_likes: meth_flags.is_no_auto_likes(),
            safe_global_variable: false,
            is_tests_bypass_visibility: meth_flags.tests_bypass_visibility(),
        }),
        visibility: vis,
        origin: class_name,
        deprecated: method_.deprecated,
        sealed_allowlist: None,
        overlapping_tparams: get_overlapping_tparams(method_),
        package_requirement: Some(method_.package_requirement.clone()),
    };
    Some(cstr)
}

pub fn constructor_decl_eager<R: Reason>(
    Constructor {
        elt: parent_cstr,
        consistency: pconsist,
    }: Constructor,
    class_: &ShallowClass<R>,
) -> Constructor {
    // constructors in children of class_ must be consistent?
    let cconsist = if class_.is_final {
        ConsistentKind::FinalClass
    } else if attributes_mem(
        *sn::user_attributes::uaConsistentConstruct,
        &class_.user_attributes,
    ) {
        ConsistentKind::ConsistentConstruct
    } else {
        ConsistentKind::Inconsistent
    };
    let cstr = match &class_.constructor {
        None => parent_cstr,
        Some(method_) => build_constructor(class_, method_),
    };
    Constructor::new(cstr, ConsistentKind::coalesce(pconsist, cconsist))
}

pub fn class_const_fold<R: Reason>(
    c: &ShallowClass<R>,
    acc: &mut IndexMap<ClassConstName, ClassConst<R>>,
    scc: &ShallowClassConst<R>,
) {
    let c_name = c.name.id();
    let cc = ClassConst {
        is_synthesized: false,
        kind: scc.kind,
        pos: scc.name.pos().clone(),
        ty: scc.ty.clone(),
        origin: c_name,
        refs: scc.refs.clone(),
        is_shape_key: scc.is_shape_key,
        value: scc.const_value.clone(),
    };
    acc.insert(scc.name.id(), cc);
}

/// Every class, interface, and trait implicitly defines a ::class to
/// allow accessing its fully qualified name as a string
pub fn class_class_decl<R: Reason>(
    opts: &DeclFoldOptions,
    class_id: &Positioned<TypeName, R::Pos>,
) -> ClassConst<R> {
    let (pos, name) = (class_id.pos(), class_id.id());
    // Examples: classname<C>, class<C>, concrete<classname<C>> ...
    let cc_type = {
        let reason = R::class_class(pos.clone(), name);
        let classname_or_class_ptr_ty = if opts.class_class_type {
            Ty::class_ptr(reason.clone(), Ty::this(reason))
        } else {
            Ty::apply(
                reason.clone(),
                Positioned::new(pos.clone(), *sn::classes::cClassname),
                [Ty::this(reason)].into(),
            )
        };
        classname_or_class_ptr_ty
    };
    ClassConst {
        kind: ClassConstKind::CCConcrete,
        pos: pos.clone(),
        is_synthesized: true,
        ty: cc_type,
        origin: name,
        refs: Box::default(),
        is_shape_key: false,
        value: ty::decl::ConstValue::CVAbsent,
    }
}

/// The element of a property (the OCaml also builds its type for the member
/// heaps).
pub fn prop_decl_eager<R: Reason>(
    c: &ShallowClass<R>,
    acc: &mut IndexMap<PropName, FoldedElement>,
    sp: &ShallowProp<R>,
) {
    let elt_origin = c.name.id();
    let vis = visibility(
        c.name.id(),
        c.module.as_ref().map(Positioned::id),
        sp.visibility,
    );
    let flags = &sp.flags;
    let elt = FoldedElement {
        flags: ClassEltFlags::new(ClassEltFlagsArgs {
            xhp_attr: sp.xhp_attr,
            is_final: true,
            is_lsb: false,
            is_synthesized: false,
            is_superfluous_override: false,
            is_const: flags.is_const(),
            is_lateinit: flags.is_lateinit(),
            is_abstract: flags.is_abstract(),
            is_dynamicallycallable: false,
            is_readonly_prop_or_needs_concrete: flags.is_readonly(),
            supports_dynamic_type: false,
            needs_init: flags.needs_init(),
            safe_global_variable: false,
            no_auto_likes: false,
            is_tests_bypass_visibility: flags.tests_bypass_visibility(),
        }),
        visibility: vis,
        origin: elt_origin,
        deprecated: None,
        sealed_allowlist: None,
        overlapping_tparams: None,
        package_requirement: None,
    };
    acc.insert(sp.name.id(), elt);
}

/// The element of a static property (the OCaml also builds its type for the
/// member heaps).
pub fn static_prop_decl_eager<R: Reason>(
    c: &ShallowClass<R>,
    acc: &mut IndexMap<PropName, FoldedElement>,
    sp: &ShallowProp<R>,
) {
    let vis = visibility(
        c.name.id(),
        c.module.as_ref().map(Positioned::id),
        sp.visibility,
    );
    let flags = &sp.flags;
    let elt = FoldedElement {
        flags: ClassEltFlags::new(ClassEltFlagsArgs {
            xhp_attr: sp.xhp_attr,
            is_final: true,
            is_const: flags.is_const(),
            is_lateinit: flags.is_lateinit(),
            is_lsb: flags.is_lsb(),
            is_superfluous_override: false,
            is_abstract: flags.is_abstract(),
            is_synthesized: false,
            is_dynamicallycallable: false,
            is_readonly_prop_or_needs_concrete: flags.is_readonly(),
            supports_dynamic_type: false,
            needs_init: false,
            no_auto_likes: false,
            safe_global_variable: flags.is_safe_global_variable(),
            is_tests_bypass_visibility: flags.tests_bypass_visibility(),
        }),
        visibility: vis,
        origin: c.name.id(),
        deprecated: None,
        sealed_allowlist: None,
        overlapping_tparams: None,
        package_requirement: None,
    };
    acc.insert(sp.name.id(), elt);
}

/// each concrete type constant T = <sometype> implicitly defines a
/// class constant with the same name which is TypeStructure<sometype>
pub fn typeconst_structure<R: Reason>(
    c: &ShallowClass<R>,
    stc: &ShallowTypeconst<R>,
) -> ClassConst<R> {
    let pos = stc.name.pos();
    let r = R::witness_from_decl(pos.clone());
    let tsid = Positioned::new(pos.clone(), *sn::fb::cTypeStructure);
    let ts_ty = Ty::apply(
        r.clone(),
        tsid,
        [Ty::access(
            r.clone(),
            TaccessType {
                ty: Ty::this(r),
                type_const: stc.name.clone(),
            },
        )]
        .into(),
    );
    let abstract_ = match &stc.kind {
        Typeconst::TCAbstract(AbstractTypeconst { default, .. }) => {
            ClassConstKind::CCAbstract(default.is_some())
        }
        Typeconst::TCConcrete(_) => ClassConstKind::CCConcrete,
    };
    ClassConst {
        kind: abstract_,
        pos: pos.clone(),
        is_synthesized: true,
        ty: ts_ty,
        origin: c.name.id(),
        refs: Box::default(),
        is_shape_key: false,
        value: ty::decl::ConstValue::CVAbsent,
    }
}

pub fn maybe_add_supportdyn_bound<R: Reason>(
    opts: &DeclFoldOptions,
    p: &R::Pos,
    kind: Typeconst<R>,
) -> Typeconst<R> {
    if opts.everything_sdt {
        match kind {
            Typeconst::TCAbstract(AbstractTypeconst {
                as_constraint: None,
                super_constraint,
                default,
            }) => Typeconst::TCAbstract(AbstractTypeconst {
                as_constraint: Some(decl_enforceability::supportdyn_mixed(
                    p.clone(),
                    R::witness_from_decl(p.clone()),
                )),
                super_constraint,
                default,
            }),
            Typeconst::TCAbstract(_) | Typeconst::TCConcrete(_) => kind,
        }
    } else {
        kind
    }
}

pub fn typeconst_fold<R: Reason>(
    opts: &DeclFoldOptions,
    c: &ShallowClass<R>,
    (typeconsts, consts): (
        &mut IndexMap<TypeConstName, TypeConst<R>>,
        &mut IndexMap<ClassConstName, ClassConst<R>>,
    ),
    stc: &ShallowTypeconst<R>,
) {
    match c.kind {
        ClassishKind::Cenum => {}
        ClassishKind::CenumClass(_)
        | ClassishKind::Ctrait
        | ClassishKind::Cinterface
        | ClassishKind::Cclass(_) => {
            let name = stc.name.id();
            let c_name = c.name.id();
            let ts = typeconst_structure(c, stc);
            consts.insert(ClassConstName(name.as_symbol()), ts);
            let ptc_opt = typeconsts.get(&name);
            let enforceable =
                // Without the positions, this is a simple OR, but this way allows us to
                // report the position of the <<__Enforceable>> attribute to the user
                if stc.enforceable.is_some() {
                    stc.enforceable.clone()
                } else {
                    match ptc_opt {
                        Some(ptc) => ptc.enforceable.clone(),
                        None => ty::decl::ty::Enforceable(None),
                    }
                };
            let reifiable = if stc.reifiable.is_some() {
                stc.reifiable.clone()
            } else {
                ptc_opt.and_then(|ptc| ptc.reifiable.clone())
            };
            let tc = TypeConst {
                is_synthesized: false,
                name: stc.name.clone(),
                kind: if stc.is_ctx {
                    stc.kind.clone()
                } else {
                    maybe_add_supportdyn_bound(opts, stc.name.pos(), stc.kind.clone())
                },
                origin: c_name,
                enforceable,
                reifiable,
                is_concretized: false,
                is_ctx: stc.is_ctx,
            };
            typeconsts.insert(stc.name.id(), tc);
        }
    }
}

/// The element of a method (the OCaml also builds its `fun_elt` for the
/// member heaps). The OCaml takes `is_static`, which only says which member
/// heap the `fun_elt` goes to.
pub fn method_decl_eager<R: Reason>(
    c: &ShallowClass<R>,
    acc: &mut IndexMap<MethodName, FoldedElement>,
    m: &ShallowMethod<R>,
) {
    let flags = &m.flags;
    // If method doesn't override anything but has the <<__Override>> attribute, then
    // set the override flag in ce_flags and let typing emit an appropriate error
    let superfluous_override = flags.is_override() && !acc.contains_key(&m.name.id());
    let id = m.name.id();
    let c_module = c.module.as_ref().map(Positioned::id);
    let vis = match (acc.get(&id), m.visibility) {
        (
            Some(FoldedElement {
                visibility: parent_vis @ CeVisibility::Protected(_),
                ..
            }),
            Visibility::Protected,
        ) => parent_vis.clone(),
        (
            Some(FoldedElement {
                visibility: CeVisibility::ProtectedInternal(class_id, _),
                ..
            }),
            Visibility::ProtectedInternal,
        ) => visibility(*class_id, c_module, m.visibility),
        _ => visibility(c.name.id(), c_module, m.visibility),
    };
    let support_dynamic_type = flags.supports_dynamic_type();
    let sealed_allowlist = get_method_sealed_allowlist(m);
    let parent_no_auto_likes = match acc.get(&id) {
        Some(FoldedElement { flags, .. }) => flags.contains(ClassEltFlags::NO_AUTO_LIKES),
        _ => false,
    };
    let no_auto_likes = parent_no_auto_likes || flags.is_no_auto_likes();
    let elt = FoldedElement {
        flags: ClassEltFlags::new(ClassEltFlagsArgs {
            xhp_attr: None,
            is_final: flags.is_final(),
            is_abstract: flags.is_abstract(),
            is_superfluous_override: superfluous_override,
            is_synthesized: false,
            is_lsb: false,
            is_const: false,
            is_lateinit: false,
            is_dynamicallycallable: flags.is_dynamicallycallable(),
            is_readonly_prop_or_needs_concrete: flags.is_needs_concrete(),
            supports_dynamic_type: support_dynamic_type,
            needs_init: false,
            no_auto_likes,
            safe_global_variable: false,
            is_tests_bypass_visibility: flags.tests_bypass_visibility(),
        }),
        visibility: vis,
        origin: c.name.id(),
        deprecated: m.deprecated,
        sealed_allowlist,
        overlapping_tparams: get_overlapping_tparams(m),
        package_requirement: Some(m.package_requirement.clone()),
    };
    acc.insert(id, elt);
}

/// The part of `decl_init_check.ml` that works on shallow declarations: the
/// init-requiring properties of a class and its ancestors.
pub mod decl_init_check {
    use super::*;

    /// `Decl_env.get_class_and_add_dep` with the class cache of the class
    /// being declared (the `get_class_add_dep` of `Decl_folded_class`).
    fn get_class_add_dep<R: Reason>(
        parents: &Parents<R>,
        name: TypeName,
    ) -> Option<&Arc<FoldedClass<R>>> {
        parents.get(&name)
    }

    // As above, but for shallow_class decls rather than class NASTs.
    fn add_parent_construct_from_shallow_decl<R: Reason>(
        parents: &Parents<R>,
        sc: &ShallowClass<R>,
        mut props: IndexSet<PropName>,
        parent_ty: &Ty<R>,
    ) -> IndexSet<PropName> {
        match parent_ty.node_ref() {
            Ty_::Tapply(id_and_args) => {
                let (parent, _) = &**id_and_args;
                match get_class_add_dep(parents, parent.id()) {
                    Some(class_)
                        if class_.has_concrete_constructor() && sc.constructor.is_some() =>
                    {
                        props.insert(*sn::members::parentConstruct);
                        props
                    }
                    _ => props,
                }
            }
            _ => props,
        }
    }

    // As above, but for shallow_class decls rather than class NASTs.
    fn parent_from_shallow_decl<R: Reason>(
        parents: &Parents<R>,
        sc: &ShallowClass<R>,
        acc: IndexSet<PropName>,
    ) -> IndexSet<PropName> {
        if sc.mode == oxidized::file_info::Mode::Mhhi {
            acc
        } else if sc.kind.is_ctrait() {
            (sc.req_extends.iter()).fold(acc, |acc, parent_ty| {
                add_parent_construct_from_shallow_decl(parents, sc, acc, parent_ty)
            })
        } else {
            match sc.extends.first() {
                None => acc,
                Some(parent_ty) => {
                    add_parent_construct_from_shallow_decl(parents, sc, acc, parent_ty)
                }
            }
        }
    }

    // As above, but for shallow_class decls rather than class NASTs.
    fn shallow_prop_may_need_init<R: Reason>(sp: &ShallowProp<R>) -> bool {
        if sp.xhp_attr.is_some() {
            false
        } else if sp.flags.is_lateinit() {
            false
        } else {
            sp.flags.needs_init()
        }
    }

    // As above, but for shallow_class decls rather than class NASTs.
    fn parent_props_from_shallow_decl<R: Reason>(
        parents: &Parents<R>,
        sc: &ShallowClass<R>,
        props: IndexSet<PropName>,
    ) -> IndexSet<PropName> {
        (sc.extends.iter()).fold(props, |mut acc, parent| match parent.node_ref() {
            Ty_::Tapply(id_and_args) => {
                let (parent, _) = &**id_and_args;
                let tc = get_class_add_dep(parents, parent.id());
                match tc {
                    None => acc,
                    Some(tc) => {
                        acc.extend(tc.deferred_init_members.iter().copied());
                        acc
                    }
                }
            }
            _ => acc,
        })
    }

    /// return all init-requiring props of the class and its ancestors from the
    /// given shallow class decl and the ancestors' folded decls.
    fn get_nonprivate_deferred_init_props<R: Reason>(
        parents: &Parents<R>,
        sc: &ShallowClass<R>,
    ) -> IndexSet<PropName> {
        let props = (sc.props.iter()).fold(IndexSet::default(), |mut props, sp| {
            if shallow_prop_may_need_init(sp) {
                props.insert(sp.name.id());
            }
            props
        });
        let props = parent_props_from_shallow_decl(parents, sc, props);
        parent_from_shallow_decl(parents, sc, props)
    }

    pub fn nonprivate_deferred_init_props<R: Reason>(
        has_own_cstr: bool,
        parents: &Parents<R>,
        sc: &ShallowClass<R>,
    ) -> IndexSet<PropName> {
        match sc.kind {
            ClassishKind::Cclass(k) if k.is_abstract() && !has_own_cstr => {
                get_nonprivate_deferred_init_props(parents, sc)
            }
            ClassishKind::Ctrait => get_nonprivate_deferred_init_props(parents, sc),
            ClassishKind::Cclass(_)
            | ClassishKind::Cinterface
            | ClassishKind::Cenum
            | ClassishKind::CenumClass(_) => IndexSet::default(),
        }
    }
}

impl<'a, R: Reason> DeclFolder<'a, R> {
    /// `Decl_folded_class.class_decl`, without the member heaps.
    ///
    /// `parents` are the folded ancestors of `child` that could be declared,
    /// as `class_parents_decl` finds them, and `decl_errors` the errors that
    /// it reported, in the order of the OCaml list (the last one first).
    /// `class_decl_if_missing` declares a class (with an empty stack of
    /// classes being declared): this needs it for `StringishObject`.
    pub fn decl_class(
        opts: &'a DeclFoldOptions,
        child: &'a ShallowClass<R>,
        parents: &'a Parents<R>,
        decl_errors: Vec<DeclError<R::Pos>>,
        class_decl_if_missing: &mut dyn FnMut(TypeName) -> Result<Option<Arc<FoldedClass<R>>>>,
    ) -> Result<Arc<FoldedClass<R>>> {
        let this = Self { opts, child };
        this.class_decl(parents, decl_errors, class_decl_if_missing)
    }

    fn class_decl(
        &self,
        parents: &Parents<R>,
        decl_errors: Vec<DeclError<R::Pos>>,
        class_decl_if_missing: &mut dyn FnMut(TypeName) -> Result<Option<Arc<FoldedClass<R>>>>,
    ) -> Result<Arc<FoldedClass<R>>> {
        let ctx = self.opts;
        let c = self.child;
        let is_abstract = class_is_abstract(c);
        let const_ = attributes_mem(*sn::user_attributes::uaConst, &c.user_attributes);
        // Support both attribute and keyword for now, until typechecker changes are made
        let internal = c.is_internal;
        let (p, cls_name) = (c.name.pos(), c.name.id());
        let Inherited {
            substs: ih_substs,
            props: ih_props,
            static_props: ih_sprops,
            methods: ih_methods,
            static_methods: ih_smethods,
            constructor: ih_cstr,
            consts: ih_consts,
            type_consts: ih_typeconsts,
            support_dynamic_type: ih_support_dynamic_type,
        } = inherit::make(c, parents);
        let mut props = ih_props;
        for sp in c.props.iter() {
            prop_decl_eager(c, &mut props, sp);
        }
        let mut methods = ih_methods;
        for m in c.methods.iter() {
            method_decl_eager(c, &mut methods, m);
        }
        let mut consts = ih_consts;
        for scc in c.consts.iter() {
            class_const_fold(c, &mut consts, scc);
        }
        if cls_name != *sn::typehints::hh_string {
            consts.insert(*sn::members::mClass, class_class_decl(ctx, &c.name));
        }
        let mut typeconsts = ih_typeconsts;
        for stc in c.typeconsts.iter() {
            typeconst_fold(ctx, c, (&mut typeconsts, &mut consts), stc);
        }
        if is_c_concrete(c.kind) {
            consts.values_mut().for_each(synthesize_const_defaults);
            // S_map.fold synthesize_typeconst_defaults typeconsts (typeconsts, consts)
            let original_typeconsts = typeconsts.clone();
            for (k, tc) in original_typeconsts.iter() {
                synthesize_typeconst_defaults(*k, tc, (&mut typeconsts, &mut consts));
            }
        }
        let mut static_props = ih_sprops;
        for sp in c.static_props.iter() {
            static_prop_decl_eager(c, &mut static_props, sp);
        }
        let mut static_methods = ih_smethods;
        for m in c.static_methods.iter() {
            method_decl_eager(c, &mut static_methods, m);
        }
        let parent_cstr = ih_cstr;
        let cstr = constructor_decl_eager(parent_cstr, c);
        let has_concrete_cstr = match &cstr.elt {
            None => false,
            Some(elt) if elt.is_abstract() => false,
            _ => true,
        };
        // Order matters - the earlier, the higher precedence its ancestors will have.
        // /!\ For soundness, the order here must be consistent with the traversal order for method folding!
        // see decl_inherit.ml
        // A type may implement an interface or use a trait at multiple instantations,
        // e.g. I<int> and I<string>. The order here determines which one will be used:
        // we'll use the first one encountered during traversal.
        // Since this is a recursive function, ancestor traversal is in effect a depth-first
        // traversal.
        // For interfaces, the typechecking code forces the winner instantiation
        // to be a subtype of each of the loser instantiations. This is necessary for soundness.
        // Users can influence which instantiation wins by reordering direct parents.
        // It's important that we start traversal with interfaces here,
        // otherwise interfaces which are ancestors of the base class would always win,
        // with no easy way to override them.
        let mut impl_: Vec<Ty<R>> = (c.implements.iter())
            .chain(c.extends.iter())
            .chain(c.uses.iter())
            .cloned()
            .collect();
        let mut parents_with_stringish;
        let parents = match (c.methods.iter()).find(|sm| sm.name.id() == *sn::members::__toString) {
            Some(sm) if cls_name != *sn::classes::cStringishObject => {
                let pos = sm.name.pos();
                // HHVM implicitly adds StringishObject interface for every class/iface/trait
                // with a __toString method; "string" also implements this interface
                // Declare StringishObject and parents if not already declared
                parents_with_stringish = parents.clone();
                // Ensure stringishObject is declared.
                match class_decl_if_missing(*sn::classes::cStringishObject)? {
                    None => {}
                    Some(stringish_cls) => {
                        parents_with_stringish
                            .insert(*sn::classes::cStringishObject, stringish_cls);
                    }
                }
                let ty = Ty::apply(
                    R::hint(pos.clone()),
                    Positioned::new(pos.clone(), *sn::classes::cStringishObject),
                    Box::new([]),
                );
                impl_.insert(0, ty);
                &parents_with_stringish
            }
            _ => parents,
        };
        let impl_ = (impl_.iter()).map(|ty| get_instantiated_ancestors_and_self(parents, ty));
        // List.fold ~f:(S_map.union ~combine:(fun _ ty1 _ty2 -> Some ty1)) ~init:S_map.empty
        let impl_: IndexMap<TypeName, Ty<R>> = impl_.fold(IndexMap::default(), |mut acc, m| {
            for (name, ty) in m {
                acc.entry(name).or_insert(ty);
            }
            acc
        });
        let decl_errors: VecDeque<DeclError<R::Pos>> = decl_errors.into();
        let (extends, xhp_attr_deps, decl_errors) =
            get_class_parents_and_traits(c, parents, decl_errors);
        let ClassRequirements {
            req_ancestors: cr_req_ancestors,
            req_ancestors_extends: cr_req_ancestors_extends,
            req_constraints_ancestors: cr_req_constraints_ancestors,
        } = decl_requirements::get_class_requirements(parents, c);

        let enum_ = c.enum_type.clone();
        let enum_inner_ty = typeconsts.get(&*sn::fb::tInner);
        // TODO(T88552052) can make logic more explicit now, enum members appear to
        // only need abstract without default and concrete type consts
        let enum_inner_ty = enum_inner_ty.and_then(|t| match &t.kind {
            Typeconst::TCConcrete(ConcreteTypeconst { ty: tc_type }) => Some(tc_type),
            Typeconst::TCAbstract(AbstractTypeconst {
                default: atc_default,
                ..
            }) => atc_default.as_ref(),
        });
        // `Decl_enum.rewrite_class`
        self.rewrite_class_consts_for_enum(enum_inner_ty, &impl_, &mut consts);
        let has_own_cstr = has_concrete_cstr && c.constructor.is_some();
        let deferred_members =
            decl_init_check::nonprivate_deferred_init_props(has_own_cstr, parents, c);
        let mut dc_tparams = c.tparams.clone();
        decl_enforceability::maybe_add_supportdyn_constraints(ctx, Some(c), p, &mut dc_tparams);
        let sealed_whitelist = get_class_sealed_allowlist(c);

        let tc = FoldedClass {
            is_final: c.is_final,
            is_const: const_,
            is_internal: internal,
            tests_bypass_visibility: attributes_mem(
                *sn::user_attributes::uaTestsBypassVisibility,
                &c.user_attributes,
            ),
            allow_unchecked_enum_values: attributes_mem(
                *sn::user_attributes::uaAllowUncheckedEnumValues,
                &c.user_attributes,
            ),
            // `dc_abstract = is_abstract` is `FoldedClass::is_abstract`, and
            // `dc_need_init = has_concrete_cstr` is
            // `FoldedClass::has_concrete_constructor`.
            deferred_init_members: deferred_members,
            kind: c.kind,
            is_xhp: c.is_xhp,
            has_xhp_keyword: c.has_xhp_keyword,
            module: c.module.clone(),
            is_module_level_trait: attributes_mem(
                *sn::user_attributes::uaModuleLevelTrait,
                &c.user_attributes,
            ),
            name: c.name.id(),
            pos: c.name.pos().clone(),
            tparams: dc_tparams,
            substs: ih_substs,
            consts,
            type_consts: typeconsts,
            props,
            static_props,
            methods,
            static_methods,
            constructor: cstr,
            ancestors: impl_,
            support_dynamic_type: c.support_dynamic_type
                || ih_support_dynamic_type && ctx.implicit_inherit_sdt
                || attributes_mem(
                    *sn::user_attributes::uaDynamicallyReferenced,
                    &c.user_attributes,
                ),
            extends,
            sealed_whitelist,
            xhp_attr_deps,
            xhp_enum_values: c.xhp_enum_values.clone(),
            xhp_marked_empty: c.xhp_marked_empty,
            req_ancestors: cr_req_ancestors.into_boxed_slice(),
            req_ancestors_extends: cr_req_ancestors_extends,
            req_constraints_ancestors: cr_req_constraints_ancestors.into_boxed_slice(),
            enum_type: enum_,
            decl_errors: Vec::from(decl_errors).into_boxed_slice(),
            docs_url: c.docs_url.clone(),
            allow_multiple_instantiations: attributes_mem(
                *sn::user_attributes::uaUnsafeAllowMultipleInstantiations,
                &c.user_attributes,
            ),
            package: c.package.clone(),
        };
        debug_assert_eq!(tc.is_abstract(), is_abstract);
        debug_assert_eq!(tc.has_concrete_constructor(), has_concrete_cstr);
        Ok(Arc::new(tc))
    }
}
