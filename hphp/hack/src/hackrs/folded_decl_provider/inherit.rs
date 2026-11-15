// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Module dealing with inheritance.
//! When we want to declare a new class, we first have to retrieve all the
//! types that were inherited from their parents.
//!
//! c.f. `hphp/hack/src/decl/decl_inherit.ml`, which this follows function by
//! function. The members are only their `Decl_defs.element`s
//! (`FoldedElement`): the member heaps of the OCaml (the `fun_elt option` and
//! `decl_ty option` paired with each element) have no counterpart here.
//!
//! `Decl_inherit.find_overridden_method` (and the parts of
//! `OverridePrecedence` and `OrderedParents` only it uses) works on the
//! class elements of the typechecker; it is in the `hh` crate
//! (`crate::folded_class::decl_inherit`).

use std::sync::Arc;

use hash::IndexMap;
use indexmap::map::Entry;
use pos::ClassConstName;
use pos::MethodName;
use pos::PropName;
use pos::TypeConstName;
use pos::TypeName;
use ty::decl::AbstractTypeconst;
use ty::decl::CeVisibility;
use ty::decl::ClassConst;
use ty::decl::ClassConstKind;
use ty::decl::ClassEltFlags;
use ty::decl::ClassishKind;
use ty::decl::FoldedClass;
use ty::decl::FoldedElement;
use ty::decl::ShallowClass;
use ty::decl::SubstContext;
use ty::decl::Ty;
use ty::decl::TypeConst;
use ty::decl::Typeconst;
use ty::decl::folded::Constructor;
use ty::decl::subst::Subst;
use ty::decl::ty::ConsistentKind;
use ty::decl::ty::DeclConstraintRequirement;
use ty::reason::Reason;

use super::subst::Substitution;

/// This is what we are trying to produce for a given class.
///
/// c.f. `Decl_inherit.inherited`
#[derive(Debug, Clone)]
pub struct Inherited<R: Reason> {
    /// `ih_substs`
    pub substs: IndexMap<TypeName, SubstContext<R>>,
    /// `ih_props`
    pub props: IndexMap<PropName, FoldedElement>,
    /// `ih_sprops`
    pub static_props: IndexMap<PropName, FoldedElement>,
    /// `ih_methods`
    pub methods: IndexMap<MethodName, FoldedElement>,
    /// `ih_smethods`
    pub static_methods: IndexMap<MethodName, FoldedElement>,
    /// `ih_cstr`
    pub constructor: Constructor,
    /// `ih_consts`
    pub consts: IndexMap<ClassConstName, ClassConst<R>>,
    /// `ih_typeconsts`
    pub type_consts: IndexMap<TypeConstName, TypeConst<R>>,
    /// `ih_support_dynamic_type`
    pub support_dynamic_type: bool,
}

/// `Decl_inherit.empty`
pub fn empty<R: Reason>() -> Inherited<R> {
    Inherited {
        substs: Default::default(),
        constructor: Constructor::new(None, ConsistentKind::Inconsistent),
        consts: Default::default(),
        type_consts: Default::default(),
        props: Default::default(),
        static_props: Default::default(),
        methods: Default::default(),
        static_methods: Default::default(),
        support_dynamic_type: false,
    }
}

impl<R: Reason> Default for Inherited<R> {
    fn default() -> Self {
        empty()
    }
}

//*****************************************************************************
// Functions used to merge an additional inherited class to the types
// we already inherited.
//*****************************************************************************

/// `module type Member_S`, for `Decl_defs.element` (`Decl_defs_element`);
/// the typechecker's class elements (`Typing_defs_class_elt`) are in the `hh`
/// crate.
pub trait MemberS {
    fn is_abstract(&self) -> bool;
    fn is_synthesized(&self) -> bool;
    fn has_lsb(&self) -> bool;
    fn visibility(&self) -> &CeVisibility;
}

/// `module Decl_defs_element : Member_S with type t = Decl_defs.element`
impl MemberS for FoldedElement {
    /// `get_elt_abstract`
    fn is_abstract(&self) -> bool {
        self.flags.contains(ClassEltFlags::ABSTRACT)
    }

    /// `get_elt_synthesized`
    fn is_synthesized(&self) -> bool {
        self.flags.contains(ClassEltFlags::SYNTHESIZED)
    }

    /// `get_elt_lsb`
    fn has_lsb(&self) -> bool {
        self.flags.contains(ClassEltFlags::LSB)
    }

    fn visibility(&self) -> &CeVisibility {
        &self.visibility
    }
}

/// The override precedence of a member is used to determine if a member
/// overrides previous members from other parents with the same name.
///
/// c.f. `Decl_inherit.OverridePrecedence` (`make`, `( > )`, `is_highest`)
pub mod override_precedence {
    use super::MemberS;

    #[derive(Clone, Copy, Debug)]
    pub struct T {
        is_concrete: bool,
        is_not_synthesized: bool,
    }

    pub fn make<M: MemberS + ?Sized>(member: &M) -> T {
        T {
            is_concrete: !member.is_abstract(),
            is_not_synthesized: !member.is_synthesized(),
        }
    }

    fn bool_to_int(b: bool) -> isize {
        if b { 1 } else { 0 }
    }

    fn to_int(
        T {
            is_concrete,
            is_not_synthesized,
        }: T,
    ) -> isize {
        (2 * bool_to_int(is_concrete)) + bool_to_int(is_not_synthesized)
    }

    /// `( > )`
    pub fn gt(x: T, y: T) -> bool {
        to_int(x) > to_int(y)
    }

    pub fn is_highest(
        T {
            is_concrete,
            is_not_synthesized,
        }: T,
    ) -> bool {
        is_concrete && is_not_synthesized
    }
}

/// Reasons to keep the old signature:
/// - We don't want to override a concrete method with
///   an abstract one.
/// - We don't want to override a method that's actually
///   implemented by the programmer with one that's "synthetic",
///   e.g. arising merely from a require-extends declaration in
///   a trait.
///
/// When these two considerations conflict, we give precedence to
/// abstractness for determining priority of the method.
/// It's possible to implement this boolean logic by just comparing
/// the boolean tuples (is_concrete, is_non_synthesized) of each member,
/// which we do in the OverridePrecedence module.
fn should_keep_old_sig(sig_: &FoldedElement, old_sig: &FoldedElement) -> bool {
    let precedence = override_precedence::make::<FoldedElement>;
    override_precedence::gt(precedence(old_sig), precedence(sig_))
}

fn add_method(
    name: MethodName,
    mut sig_: FoldedElement,
    methods: &mut IndexMap<MethodName, FoldedElement>,
) {
    match methods.entry(name) {
        Entry::Vacant(entry) => {
            // The method didn't exist so far, let's add it
            entry.insert(sig_);
        }
        Entry::Occupied(mut entry) => {
            // If `should_keep_old_sig`, the methods are left as they are.
            // Otherwise, we *are* overwriting a method definition. This is
            // OK when a naming conflict is parent class vs trait (trait
            // wins!), but not really OK when the naming conflict is trait vs
            // trait (we rely on HHVM to catch the error at runtime)
            if !should_keep_old_sig(&sig_, entry.get()) {
                // `reset_elt_superfluous_override`
                sig_.set_is_superfluous_override(false);
                entry.insert(sig_);
            }
        }
    }
}

fn add_methods(
    methods_: IndexMap<MethodName, FoldedElement>,
    acc: &mut IndexMap<MethodName, FoldedElement>,
) {
    for (name, sig_) in methods_ {
        add_method(name, sig_, acc)
    }
}

fn add_const<R: Reason>(
    name: ClassConstName,
    const_: ClassConst<R>,
    acc: &mut IndexMap<ClassConstName, ClassConst<R>>,
) {
    match acc.entry(name) {
        Entry::Vacant(e) => {
            e.insert(const_);
        }
        Entry::Occupied(mut e) => {
            let existing_const = e.get();
            match (
                const_.is_synthesized,
                existing_const.is_synthesized,
                const_.kind,
                existing_const.kind,
            ) {
                (true, false, _, _) => {
                    // Don't replace a constant with a synthesized constant. This
                    // covers the following case:
                    //
                    // class HasFoo { abstract const int FOO; }
                    // trait T { require extends Foo; }
                    // class Child extends HasFoo {
                    //    use T;
                    // }
                    //
                    // In this case, Child still doesn't have a value for the FOO
                    // constant.
                }
                (_, _, ClassConstKind::CCAbstract(false), ClassConstKind::CCAbstract(true))
                | (_, _, ClassConstKind::CCAbstract(_), ClassConstKind::CCConcrete) => {
                    // Don't replace a concrete constant with an abstract constant
                    // found later in the MRO.
                }
                (_, _, _, _) => {
                    e.insert(const_);
                }
            }
        }
    }
}

fn add_members<K: std::hash::Hash + Eq>(
    members: IndexMap<K, FoldedElement>,
    acc: &mut IndexMap<K, FoldedElement>,
) {
    // S_map.fold S_map.add members acc
    for (name, member) in members {
        acc.insert(name, member);
    }
}

fn add_typeconst<R: Reason>(
    c: &ShallowClass<R>,
    name: TypeConstName,
    sig_: TypeConst<R>,
    typeconsts: &mut IndexMap<TypeConstName, TypeConst<R>>,
) {
    match typeconsts.entry(name) {
        Entry::Vacant(e) => {
            // The type constant didn't exist so far, let's add it
            e.insert(sig_);
        }
        Entry::Occupied(mut e) => {
            // The match below is on the type constant that was there before
            // the enforceability is updated (`old_sig` in the OCaml).
            let old_sig = e.get().clone();
            // Boolean OR for the second element of the tuple. If some typeconst in
            // some ancestor was enforceable, then the child class' typeconst will be
            // enforceable too, even if we didn't take that ancestor typeconst.
            if sig_.enforceable.is_some() && !old_sig.enforceable.is_some() {
                e.get_mut().enforceable = sig_.enforceable.clone();
            }
            match (
                old_sig.is_synthesized,
                sig_.is_synthesized,
                &old_sig.kind,
                &sig_.kind,
            ) {
                (false, true, _, _) if c.kind.is_cclass() => {
                    // Don't replace a type constant with a synthesized type constant. This
                    // covers the following case:
                    //
                    // class A { const type T = int; }
                    // trait T { require extends A; }
                    // class Child extends A {
                    //    use T;
                    // }
                    //
                    // Child should not consider T to be synthesized.
                }
                // This covers the following case
                //
                // interface I1 { abstract const type T; }
                // interface I2 { const type T = int; }
                //
                // class C implements I1, I2 {}
                //
                // Then C::T == I2::T since I2::T is not abstract
                (_, _, Typeconst::TCConcrete(_), Typeconst::TCAbstract(_)) => {}
                // This covers the following case
                //
                // interface I {
                //   abstract const type T as arraykey;
                // }
                //
                // abstract class A {
                //   abstract const type T as arraykey = string;
                // }
                //
                // final class C extends A implements I {}
                //
                // C::T must come from A, not I, as A provides the default that will synthesize
                // into a concrete type constant in C.
                (
                    _,
                    _,
                    Typeconst::TCAbstract(AbstractTypeconst {
                        default: Some(_), ..
                    }),
                    Typeconst::TCAbstract(AbstractTypeconst { default: None, .. }),
                ) => {}
                (_, _, _, _) => {
                    // When a type constant is declared in multiple parents we need to make a
                    // subtle choice of what type we inherit. For example in:
                    //
                    // interface I1 { abstract const type t as Container<int>; }
                    // interface I2 { abstract const type t as KeyedContainer<int, int>; }
                    // abstract class C implements I1, I2 {}
                    //
                    // Depending on the order the interfaces are declared, we may report an error.
                    // Since this could be confusing there is special logic in Typing_extends that
                    // checks for this potentially ambiguous situation and warns the programmer to
                    // explicitly declare T in C.
                    let sig_ =
                        // Boolean OR for the second element of the tuple. If a typeconst we
                        // already inherited from some other ancestor was enforceable, then the
                        // one we inherit here will be enforceable too.
                        if old_sig.enforceable.is_some() && !sig_.enforceable.is_some() {
                            TypeConst {
                                enforceable: old_sig.enforceable.clone(),
                                ..sig_
                            }
                        } else {
                            sig_
                        };
                    e.insert(sig_);
                }
            }
        }
    }
}

/// `add_constructor (cstr, cstr_consist) (acc, acc_consist)`
fn add_constructor(cstr: Constructor, acc: Constructor) -> Constructor {
    let Constructor {
        elt: cstr,
        consistency: cstr_consist,
    } = cstr;
    let Constructor {
        elt: acc,
        consistency: acc_consist,
    } = acc;
    let ce = match (&cstr, &acc) {
        (None, _) => acc,
        (Some(ce), Some(acce)) if should_keep_old_sig(ce, acce) => acc,
        _ => cstr,
    };
    Constructor::new(ce, ConsistentKind::coalesce(acc_consist, cstr_consist))
}

fn add_inherited<R: Reason>(
    c: &ShallowClass<R>,
    inherited: Inherited<R>,
    acc: Inherited<R>,
) -> Inherited<R> {
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
    } = inherited;
    let mut acc = acc;
    // S_map.merge acc.ih_substs inherited.ih_substs
    for (key, new_subst) in ih_substs {
        match acc.substs.entry(key) {
            Entry::Vacant(e) => {
                e.insert(new_subst);
            }
            Entry::Occupied(mut e) => {
                let old_subst = e.get();
                // If the old subst_context came via require extends, then we want to use
                // the substitutions from the actual extends instead. e.g.,
                //
                // class Base<+T> {}
                // trait MyTrait { require extends Base<mixed>; }
                // class Child extends Base<int> { use MyTrait; }
                //
                // Here the subst_context (MyTrait/[T -> mixed]) should be overridden by
                // (Child/[T -> int]), because it's the actual extension of class Base.
                if !new_subst.from_req_extends || old_subst.from_req_extends {
                    e.insert(new_subst);
                }
            }
        }
    }
    let acc_cstr = std::mem::replace(
        &mut acc.constructor,
        Constructor::new(None, ConsistentKind::Inconsistent),
    );
    acc.constructor = add_constructor(ih_cstr, acc_cstr);
    for (name, const_) in ih_consts {
        add_const(name, const_, &mut acc.consts);
    }
    for (name, sig_) in ih_typeconsts {
        add_typeconst(c, name, sig_, &mut acc.type_consts);
    }
    add_members(ih_props, &mut acc.props);
    add_members(ih_sprops, &mut acc.static_props);
    add_methods(ih_methods, &mut acc.methods);
    add_methods(ih_smethods, &mut acc.static_methods);
    acc.support_dynamic_type = ih_support_dynamic_type || acc.support_dynamic_type;
    acc
}

//*****************************************************************************
// Helpers
//*****************************************************************************

fn make_substitution<R: Reason>(
    class_type: &FoldedClass<R>,
    class_parameters: &[Ty<R>],
) -> Subst<R> {
    // Inst.make_subst class_type.dc_tparams class_parameters
    Subst::new(&class_type.tparams, class_parameters)
}

fn mark_as_synthesized<R: Reason>(mut inh: Inherited<R>) -> Inherited<R> {
    // let mark_elt elt = Tuple.T2.map_fst elt ~f:set_elt_synthesized
    fn mark_elt(elt: &mut FoldedElement) {
        elt.set_is_synthesized(true)
    }
    (inh.substs.values_mut()).for_each(|sc| sc.from_req_extends = true);
    (inh.constructor.elt.iter_mut()).for_each(mark_elt);
    (inh.props.values_mut()).for_each(mark_elt);
    (inh.static_props.values_mut()).for_each(mark_elt);
    (inh.methods.values_mut()).for_each(mark_elt);
    (inh.static_methods.values_mut()).for_each(mark_elt);
    (inh.type_consts.values_mut()).for_each(|const_| const_.is_synthesized = true);
    (inh.consts.values_mut()).for_each(|const_| const_.is_synthesized = true);
    inh
}

//*****************************************************************************
// Code filtering the private members (useful for inheritance)
//*****************************************************************************

pub fn is_private<M: MemberS + ?Sized>(member: &M) -> bool {
    match member.visibility() {
        CeVisibility::Private(_) => !member.has_lsb(),
        CeVisibility::Public
        | CeVisibility::Protected(_)
        | CeVisibility::Internal(_)
        | CeVisibility::ProtectedInternal(..) => false,
    }
}

/// The members of `class_type` (`dc_props`, `dc_sprops`, `dc_methods`,
/// `dc_smethods`) without the private ones.
struct Members {
    props: IndexMap<PropName, FoldedElement>,
    static_props: IndexMap<PropName, FoldedElement>,
    methods: IndexMap<MethodName, FoldedElement>,
    static_methods: IndexMap<MethodName, FoldedElement>,
}

fn filter_privates<R: Reason>(class_type: &FoldedClass<R>) -> Members {
    fn should_keep<K>(_: &K, elt: &FoldedElement) -> bool {
        !is_private(elt) || elt.flags.contains(ClassEltFlags::TESTS_BYPASS_VISIBILITY)
    }
    fn filter<K: Copy + std::hash::Hash + Eq>(
        m: &IndexMap<K, FoldedElement>,
    ) -> IndexMap<K, FoldedElement> {
        (m.iter())
            .filter(|(k, elt)| should_keep(*k, elt))
            .map(|(k, elt)| (*k, elt.clone()))
            .collect()
    }
    Members {
        props: filter(&class_type.props),
        static_props: filter(&class_type.static_props),
        methods: filter(&class_type.methods),
        static_methods: filter(&class_type.static_methods),
    }
}

fn chown_private_and_protected<R: Reason>(owner: TypeName, class_type: &FoldedClass<R>) -> Members {
    fn chown(owner: TypeName, elt: &FoldedElement) -> FoldedElement {
        match elt.visibility {
            CeVisibility::Private(_) => FoldedElement {
                visibility: CeVisibility::Private(owner),
                ..elt.clone()
            },
            // Update protected member that's included via a `use` statement, unless
            // it's synthesized, in which case its owner will be the one specified
            // in `requires extends` or `requires implements`
            CeVisibility::Protected(_) if !elt.is_synthesized() => FoldedElement {
                visibility: CeVisibility::Protected(owner),
                ..elt.clone()
            },
            CeVisibility::ProtectedInternal(_, module_) if !elt.is_synthesized() => FoldedElement {
                visibility: CeVisibility::ProtectedInternal(owner, module_),
                ..elt.clone()
            },
            CeVisibility::Public
            | CeVisibility::Protected(_)
            | CeVisibility::Internal(_)
            | CeVisibility::ProtectedInternal(..) => elt.clone(),
        }
    }
    fn map<K: Copy + std::hash::Hash + Eq>(
        owner: TypeName,
        m: &IndexMap<K, FoldedElement>,
    ) -> IndexMap<K, FoldedElement> {
        (m.iter()).map(|(k, elt)| (*k, chown(owner, elt))).collect()
    }
    Members {
        props: map(owner, &class_type.props),
        static_props: map(owner, &class_type.static_props),
        methods: map(owner, &class_type.methods),
        static_methods: map(owner, &class_type.static_methods),
    }
}

//*****************************************************************************
// Builds the inherited type when the class lives in Hack
//*****************************************************************************

// `pair_with_heap_entries` pairs each element with its entry in the member
// heaps, which do not exist here: the elements are taken as they are.

fn inherit_hack_class<R: Reason>(
    child: &ShallowClass<R>,
    parent_name: TypeName,
    parent: &FoldedClass<R>,
    argl: &[Ty<R>],
) -> Inherited<R> {
    let subst = make_substitution(parent, argl);
    let members = match parent.kind {
        ClassishKind::Ctrait => {
            // Change the private/protected visibility to point to the inheriting class
            chown_private_and_protected(child.name.id(), parent)
        }
        ClassishKind::Cclass(_) | ClassishKind::Cinterface => filter_privates(parent),
        ClassishKind::Cenum | ClassishKind::CenumClass(_) => Members {
            props: parent.props.clone(),
            static_props: parent.static_props.clone(),
            methods: parent.methods.clone(),
            static_methods: parent.static_methods.clone(),
        },
    };
    let substitution = Substitution { subst: &subst };
    let typeconsts = (parent.type_consts.iter())
        .map(|(name, tc)| (*name, substitution.instantiate_type_const(tc)))
        .collect();
    let consts = (parent.consts.iter())
        .map(|(name, cc)| (*name, substitution.instantiate_class_const(cc)))
        .collect();
    let constructor = parent.constructor.clone();
    let subst_ctx = SubstContext {
        subst,
        class_context: child.name.id(),
        from_req_extends: false,
    };
    let mut substs = parent.substs.clone();
    substs.insert(parent_name, subst_ctx);
    Inherited {
        substs,
        constructor,
        consts,
        type_consts: typeconsts,
        props: members.props,
        static_props: members.static_props,
        methods: members.methods,
        static_methods: members.static_methods,
        support_dynamic_type: parent.support_dynamic_type,
    }
}

/// mostly copy paste of inherit_hack_class
fn inherit_hack_class_constants_only<R: Reason>(
    class_type: &FoldedClass<R>,
    argl: &[Ty<R>],
) -> Inherited<R> {
    let subst = make_substitution(class_type, argl);
    let substitution = Substitution { subst: &subst };
    let consts = (class_type.consts.iter())
        .map(|(name, cc)| (*name, substitution.instantiate_class_const(cc)))
        .collect();
    let typeconsts = (class_type.type_consts.iter())
        .map(|(name, tc)| (*name, substitution.instantiate_type_const(tc)))
        .collect();
    Inherited {
        consts,
        type_consts: typeconsts,
        ..empty()
    }
}

/// This logic deals with importing XHP attributes from an XHP class
/// via the "attribute :foo;" syntax.
fn inherit_hack_xhp_attrs_only<R: Reason>(class_type: &FoldedClass<R>) -> Inherited<R> {
    // Filter out properties that are not XHP attributes
    let props = (class_type.props.iter())
        .filter(|(_, prop)| prop.get_xhp_attr().is_some())
        .map(|(name, prop)| (*name, prop.clone()))
        .collect();
    Inherited { props, ..empty() }
}

//*****************************************************************************

/// The class entries of the ancestors of a class that are known
/// (`Decl_store.class_entries S_map.t`, without the member heaps).
pub type Parents<R> = IndexMap<TypeName, Arc<FoldedClass<R>>>;

/// Include definitions inherited from a class (extends) or a trait (use)
/// or requires extends
fn from_class<R: Reason>(
    c: &ShallowClass<R>,
    parents: &Parents<R>,
    parent_ty: &Ty<R>,
) -> Inherited<R> {
    let (_, parent_pos_id, parent_class_params) = parent_ty.unwrap_class_type();
    let parent_name = parent_pos_id.id();
    match parents.get(&parent_name) {
        None => {
            // The class lives in PHP, we don't know anything about it
            empty()
        }
        Some(class_) => {
            // The class lives in Hack
            inherit_hack_class(c, parent_name, class_, parent_class_params)
        }
    }
}

fn from_class_constants_only<R: Reason>(parents: &Parents<R>, ty: &Ty<R>) -> Inherited<R> {
    let (_, pos_id, class_params) = ty.unwrap_class_type();
    match parents.get(&pos_id.id()) {
        None => {
            // The class lives in PHP, we don't know anything about it
            empty()
        }
        Some(class_) => {
            // The class lives in Hack
            inherit_hack_class_constants_only(class_, class_params)
        }
    }
}

fn from_class_xhp_attrs_only<R: Reason>(parents: &Parents<R>, ty: &Ty<R>) -> Inherited<R> {
    let (_, pos_id, _class_params) = ty.unwrap_class_type();
    match parents.get(&pos_id.id()) {
        None => {
            // The class lives in PHP, we don't know anything about it
            empty()
        }
        Some(class_) => {
            // The class lives in Hack
            inherit_hack_xhp_attrs_only(class_)
        }
    }
}

pub fn parents_which_provide_members<R: Reason>(c: &ShallowClass<R>) -> Vec<&Ty<R>> {
    // /!\ For soundness, the traversal order below
    // must be consistent with traversal order for ancestors
    // used in decl_folded_class.ml
    // In an abstract class or a trait, we assume the interfaces
    // will be implemented in the future, so we take them as
    // part of the class (as requested by dependency injection implementers)
    match c.kind {
        ClassishKind::Cclass(k) if k.is_abstract() => {
            (c.implements.iter()).chain(c.extends.iter()).collect()
        }
        ClassishKind::Ctrait => (c.implements.iter())
            .chain(c.extends.iter())
            .chain(c.req_implements.iter())
            .collect(),
        ClassishKind::Cclass(_)
        | ClassishKind::Cinterface
        | ClassishKind::Cenum
        | ClassishKind::CenumClass(_) => c.extends.iter().collect(),
    }
}

fn from_parent<R: Reason>(
    c: &ShallowClass<R>,
    parents: &Parents<R>,
    acc: Inherited<R>,
    parent: &Ty<R>,
) -> Inherited<R> {
    let inherited = from_class(c, parents, parent);
    add_inherited(c, inherited, acc)
}

fn from_requirements<R: Reason>(
    c: &ShallowClass<R>,
    parents: &Parents<R>,
    acc: Inherited<R>,
    reqs: &Ty<R>,
) -> Inherited<R> {
    let inherited = from_class(c, parents, reqs);
    let inherited = mark_as_synthesized(inherited);
    add_inherited(c, inherited, acc)
}

fn from_trait<R: Reason>(
    c: &ShallowClass<R>,
    parents: &Parents<R>,
    acc: Inherited<R>,
    uses: &Ty<R>,
) -> Inherited<R> {
    let inherited = from_class(c, parents, uses);
    add_inherited(c, inherited, acc)
}

fn from_xhp_attr_use<R: Reason>(
    c: &ShallowClass<R>,
    parents: &Parents<R>,
    acc: Inherited<R>,
    uses: &Ty<R>,
) -> Inherited<R> {
    let inherited = from_class_xhp_attrs_only(parents, uses);
    add_inherited(c, inherited, acc)
}

/// Inherits constants and type constants from an interface.
fn from_interface_constants<R: Reason>(
    c: &ShallowClass<R>,
    parents: &Parents<R>,
    acc: Inherited<R>,
    impls: &Ty<R>,
) -> Inherited<R> {
    let inherited = from_class_constants_only(parents, impls);
    add_inherited(c, inherited, acc)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParentKind {
    Parent,
    Requirement,
    Trait,
}

/// c.f. `Decl_inherit.OrderedParents` (`get` and `fold`; `rev` and
/// `find_map_first_with_highest_precedence` are only used by
/// `find_overridden_method`, see the module documentation).
pub mod ordered_parents {
    use super::*;

    pub type T<'a, R> = Vec<(ParentKind, Vec<&'a Ty<R>>)>;

    /// This provides the parent traversal order for member folding.
    /// This is appropriate for all members except XHP attributes and constants.
    /// The order is different for those and these are handled elsewhere.
    pub fn get<R: Reason>(c: &ShallowClass<R>) -> T<'_, R> {
        // /!\ For soundness, the traversal order below
        // must be consistent with traversal order for ancestors
        // used in decl_folded_class.ml
        vec![
            (
                ParentKind::Parent,
                parents_which_provide_members(c).into_iter().rev().collect(),
            ),
            (
                ParentKind::Requirement,
                (c.req_constraints.iter())
                    // `Shallow_decl_defs.to_decl_constraint`
                    .map(|dcr| match dcr {
                        DeclConstraintRequirement::DCREqual(ty)
                        | DeclConstraintRequirement::DCRSubtype(ty) => ty,
                    })
                    .chain(c.req_extends.iter())
                    .collect(),
            ),
            (ParentKind::Trait, c.uses.iter().collect()),
        ]
    }

    pub fn fold<'a, R: Reason, Acc>(
        t: T<'a, R>,
        init: Acc,
        mut f: impl FnMut(ParentKind, Acc, &'a Ty<R>) -> Acc,
    ) -> Acc {
        let mut acc = init;
        for (parent_kind, parents) in t {
            for parent in parents {
                acc = f(parent_kind, acc, parent);
            }
        }
        acc
    }
}

/// Builds the [inherited] type by fetching any ancestor from the heap.
/// The [cache] parameter is a map of heap entries we might already have at hand
/// which acts as a cache for the shared heap.
///
/// (The ancestors are those of `parents`, which is the cache.)
pub fn make<R: Reason>(c: &ShallowClass<R>, parents: &Parents<R>) -> Inherited<R> {
    let acc = empty();
    let acc = ordered_parents::fold(ordered_parents::get(c), acc, |parent_kind, acc, parent| {
        match parent_kind {
            ParentKind::Parent => from_parent(c, parents, acc, parent),
            ParentKind::Requirement => from_requirements(c, parents, acc, parent),
            ParentKind::Trait => from_trait(c, parents, acc, parent),
        }
    });
    let acc =
        (c.xhp_attr_uses.iter()).fold(acc, |acc, uses| from_xhp_attr_use(c, parents, acc, uses));
    // todo: what about the same constant defined in different interfaces
    // we implement? We should forbid and say "constant already defined".
    // to julien: where is the logic that check for duplicated things?
    // todo: improve constant handling, see task #2487051
    let acc = (c.req_implements.iter()).fold(acc, |acc, impls| {
        from_interface_constants(c, parents, acc, impls)
    });
    let included_enums: &[Ty<R>] = match &c.enum_type {
        None => &[],
        Some(enum_type) => &enum_type.includes,
    };
    let acc = (included_enums.iter()).fold(acc, |acc, impls| {
        from_interface_constants(c, parents, acc, impls)
    });
    (c.implements.iter()).fold(acc, |acc, impls| {
        from_interface_constants(c, parents, acc, impls)
    })
}

impl<R: Reason> Inherited<R> {
    /// `Decl_inherit.make`
    pub fn make(child: &ShallowClass<R>, parents: &Parents<R>) -> Self {
        make(child, parents)
    }
}
