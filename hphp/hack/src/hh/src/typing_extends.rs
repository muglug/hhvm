// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_extends.ml`. See `hh/PORTING.md`.
//!
//! Checks that a class implements its interfaces, extends its base class and
//! uses its traits correctly (member compatibility only). The public surface
//! is what `typing_extends.mli` exports: [`check_implements_extends_uses`].
//!
//! - The submodules `MemberKind`, `ParentClassElt`, `ParentClassConst` and
//!   `ParentTypeConst` are [`member_kind`], [`parent_class_elt`],
//!   [`parent_class_const`] and [`parent_type_const`]. The sets built on them
//!   (`Stdlib.Set.Make`) are `BTreeSet`s ordered by the modules' `compare`,
//!   which, like `Set.add`, keep the element already there when an equal one
//!   is added. `MemberKindMap` and `MemberNameMap` (`S_map`) are `BTreeMap`s:
//!   the maps are built once and read.
//! - `ParentClassElt.parent` is shared between the elements of one parent
//!   (`Rc<Parent>`), as the OCaml shares the record.
//! - The `on_error` functions of type `Pos.t * string ->
//!   Typing_error.Reasons_callback.t` are `&dyn Fn((Pos, String)) -> ...`.
//! - `Map.merge` (in `merge_member_maps`) calls its function on the keys in
//!   *decreasing* order: it evaluates `concat_or_join (merge f l1 l2) v
//!   (f v d1 d2) (merge f r1 r2)`, whose arguments OCaml evaluates from right
//!   to left. The function reports errors (trait diamonds), so the port
//!   visits the member names in that order.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::rc::Rc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Id;
use oxidized::classish_positions_types;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typing_defs_flags::FunTypeFlags;
use oxidized::typing_reason::Ureason;
use oxidized::xhp_attribute::Tag;
use oxidized::xhp_attribute::XhpAttribute;
use pos::BPos;
use pos::Symbol;
use pos::ToOxidized;
use pos::TypeName;
use ty::decl::Ty_ as DTy_;
use ty::decl::ty::Capability;
use ty::decl::ty::FunImplicitParams;
use ty::reason::Reason as _;
use ty::reason::ReasonImpl;
use ty::reason::WitnessDecl;

use crate::ancestor_route;
use crate::ast_defs;
use crate::ctx::R;
use crate::decl_entry;
use crate::decl_instantiate as inst;
use crate::decl_provider;
use crate::diagnostics_state;
use crate::folded_class as cls;
use crate::folded_class::ClassElt;
use crate::markdown_lite;
use crate::naming_attributes;
use crate::package;
use crate::pos_or_decl;
use crate::pos_or_decl::RawPosOrDeclReference;
use crate::provider_context;
use crate::quickfix;
use crate::trait_reuse_check;
use crate::type_parameter_env;
use crate::typing_const_reifiable;
use crate::typing_defs::ClassConst;
use crate::typing_defs::ClassConstKind;
use crate::typing_defs::PackageRequirement;
use crate::typing_defs::TypeconstType;
use crate::typing_defs::class_elt_is_private_not_lsb;
use crate::typing_defs::get_ce_abstract;
use crate::typing_defs::get_ce_const;
use crate::typing_defs::get_ce_final;
use crate::typing_defs::get_ce_lateinit;
use crate::typing_defs::get_ce_lsb;
use crate::typing_defs::get_ce_readonly_prop_or_needs_concrete;
use crate::typing_defs::get_ce_superfluous_override;
use crate::typing_defs::get_ce_support_dynamic_type;
use crate::typing_defs::get_ce_synthesized;
use crate::typing_defs::get_ce_tests_bypass_visibility;
use crate::typing_defs::get_ce_xhp_attr;
use crate::typing_defs::is_typeconst_type_abstract;
use crate::typing_defs::make_ce_flags;
use crate::typing_defs_core::CeVisibility;
use crate::typing_defs_core::ConsistentKind;
use crate::typing_defs_core::DeclFunType;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::PosString;
use crate::typing_defs_core::compare_decl_ty;
use crate::typing_defs_core::string_of_visibility;
use crate::typing_defs_flags;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_dynamic;
use crate::typing_enforceability;
use crate::typing_enforceable_hint;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_error_utils;
use crate::typing_log;
use crate::typing_make_type;
use crate::typing_modules;
use crate::typing_modules::CanAccessInternalResult;
use crate::typing_ops;
use crate::typing_partial_enforcement;
use crate::typing_pessimisation_deps;
use crate::typing_phase;
use crate::typing_print;
use crate::typing_reason;
use crate::typing_skeleton;
use crate::typing_subtype_method;
use crate::typing_utils;
use crate::typing_warning;
use crate::typing_warning_utils;
use crate::utils;
use crate::worker_cancel;

/// `Typing_reason.t` (of an inferred type)
type Reason = typing_reason::T;

// ~~ Helpers on declared types (`hackrs`) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Typing_reason.localize` of the reason of a declared type.
fn localize_reason(r: &R) -> Reason {
    typing_reason::localize(&r.clone().to_oxidized())
}

/// `Typing_reason.to_pos` of the reason of a declared type.
fn decl_reason_to_pos(r: &R) -> PosOrDecl {
    typing_reason::to_pos(&localize_reason(r))
}

/// `Typing_defs.get_pos` of a declared type.
fn decl_get_pos(ty: &DeclTy) -> PosOrDecl {
    decl_reason_to_pos(ty.reason())
}

/// A declaration position as a `Pos_or_decl.t`.
fn decl_pos(p: &BPos) -> PosOrDecl {
    PosOrDecl::from(p.clone())
}

/// `Typing_defs.get_ft_async` of a declared function type.
fn decl_get_ft_async(ft: &DeclFunType) -> bool {
    ft.flags.contains(FunTypeFlags::ASYNC)
}

/// `Lazy.force` of the position of a class element.
fn ce_pos(ce: &ClassElt) -> PosOrDecl {
    PosOrDecl::clone(&ce.ce_pos)
}

/// `Option.merge e1 e2 ~f:Typing_error.both`
fn merge_errors(
    e1: Option<typing_error::T>,
    e2: Option<typing_error::T>,
) -> Option<typing_error::T> {
    match (e1, e2) {
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    }
}

/// `Option.iter ~f:(Typing_error_utils.add_typing_error ~env)`
fn add_typing_error_opt(env: &Env, ty_err_opt: Option<typing_error::T>) {
    if let Some(err) = ty_err_opt {
        typing_error_utils::add_typing_error(&err, env)
    }
}

/// `lazy (Ancestor_route.describe_route env ~classish ~ancestor)`, as a
/// `Pos_or_decl.t Message.t list` (which is what `(Pos_or_decl.t * string)
/// list` is in OCaml).
fn describe_route_lazily(
    env: &Env,
    classish: String,
    ancestor: String,
) -> typing_error::Lazy<Vec<Message<PosOrDecl>>> {
    let env = env.clone();
    typing_error::Lazy::new(move || {
        (ancestor_route::describe_route(&env, &classish, &ancestor).into_iter())
            .map(|(pos, msg)| Message(pos, msg.into()))
            .collect()
    })
}

// ~~ MemberKind ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `MemberKind`
pub mod member_kind {
    use std::cmp::Ordering;

    /// `[@@deriving eq, ord]`: the derived order is the one of the
    /// constructors, then of their arguments, as in OCaml.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum T {
        Property,
        StaticProperty,
        Method,
        StaticMethod,
        Constructor { is_consistent: bool },
    }

    pub fn equal(t1: &T, t2: &T) -> bool {
        t1 == t2
    }

    pub fn compare(t1: &T, t2: &T) -> Ordering {
        t1.cmp(t2)
    }

    pub fn is_method(t: T) -> bool {
        match t {
            T::Method | T::StaticMethod => true,
            T::Property | T::StaticProperty | T::Constructor { .. } => false,
        }
    }

    pub fn is_property(t: T) -> bool {
        match t {
            T::Property | T::StaticProperty => true,
            T::Method | T::StaticMethod | T::Constructor { .. } => false,
        }
    }

    pub fn is_functional(member_kind: T) -> bool {
        match member_kind {
            T::Method | T::StaticMethod | T::Constructor { .. } => true,
            T::Property | T::StaticProperty => false,
        }
    }

    pub fn is_constructor(t: T) -> bool {
        match t {
            T::Constructor { .. } => true,
            _ => false,
        }
    }

    pub fn is_static(t: T) -> bool {
        match t {
            T::Property | T::Method | T::Constructor { .. } => false,
            T::StaticProperty | T::StaticMethod => true,
        }
    }
}

type MemberKind = member_kind::T;

// ~~ ParentClassElt ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// This is used to merge members from all parents (direct ancestors) of a
/// class. Certain class hierarchies are heavy in diamond patterns so merging
/// members avoids doing the same member subtyping multiple times.
pub mod parent_class_elt {
    use std::cmp::Ordering;
    use std::rc::Rc;

    use oxidized::pos::Pos;

    use crate::folded_class as cls;
    use crate::folded_class::ClassElt;
    use crate::typing_defs_core::DeclTy;
    use crate::typing_defs_core::compare_decl_ty;
    use crate::typing_error;

    pub struct Parent {
        pub parent_pos: Pos,
        pub parent_class: cls::T,
        pub parent_type: DeclTy,
    }

    #[derive(Clone)]
    pub struct T {
        pub class_elt: ClassElt,
        /// The parent this class element is from.
        pub parent: Rc<Parent>,
        /// A list of errors to be added if that class element is not
        /// overridden in the class being checked.
        pub errors_if_not_overriden: Vec<typing_error::Lazy<typing_error::T>>,
    }

    pub fn make(
        errors_if_not_overriden: Option<Vec<typing_error::Lazy<typing_error::T>>>,
        (class_elt, parent): (ClassElt, Rc<Parent>),
    ) -> T {
        T {
            class_elt,
            parent,
            errors_if_not_overriden: errors_if_not_overriden.unwrap_or_default(),
        }
    }

    /// Class elements with the same names and origins should be equal modulo
    /// type instantiations, which is why we also need to compare types. For
    /// example,
    ///
    /// ```text
    ///    interface I<T> {
    ///      public function foo():T;
    ///    }
    ///    interface I1 extends I<string> {}
    ///    interface I2 extends I<int> {}
    ///    class C implements I1, I2 {
    ///      public function foo():int { return 3; }
    ///    }
    /// ```
    ///
    /// When unioning members of I1 and I2, we have two `foo` members with the
    /// same origin (`I`) but with different types.
    pub fn compare(t1: &T, t2: &T) -> Ordering {
        let ClassElt {
            ce_visibility: _,
            ce_type: type1,
            ce_origin: origin1,
            ce_deprecated: _,
            ce_pos: _,
            ce_flags: _,
            ce_sealed_allowlist: _,
            ce_overlapping_tparams: _,
            ce_package_requirement: _,
        } = &t1.class_elt;
        let ClassElt {
            ce_visibility: _,
            ce_type: type2,
            ce_origin: origin2,
            ce_deprecated: _,
            ce_pos: _,
            ce_flags: _,
            ce_sealed_allowlist: _,
            ce_overlapping_tparams: _,
            ce_package_requirement: _,
        } = &t2.class_elt;
        match origin1.as_str().cmp(origin2.as_str()) {
            Ordering::Equal => compare_decl_ty(None, type1, type2),
            x => x,
        }
    }

    impl PartialEq for T {
        fn eq(&self, other: &Self) -> bool {
            compare(self, other) == Ordering::Equal
        }
    }

    impl Eq for T {}

    impl PartialOrd for T {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(compare(self, other))
        }
    }

    impl Ord for T {
        fn cmp(&self, other: &Self) -> Ordering {
            compare(self, other)
        }
    }
}

/// `ParentClassEltSet`
type ParentClassEltSet = BTreeSet<parent_class_elt::T>;

/// `ParentClassElt.parent`
type Parent = parent_class_elt::Parent;

// ~~ ParentClassConst ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub mod parent_class_const {
    use std::cmp::Ordering;
    use std::rc::Rc;

    use super::parent_class_elt::Parent;
    use crate::typing_defs::ClassConst;

    pub struct T {
        pub class_const: ClassConst,
        pub parent: Rc<Parent>,
    }

    pub fn make(class_const: ClassConst, parent: Rc<Parent>) -> T {
        T {
            class_const,
            parent,
        }
    }

    pub fn compare(left: &T, right: &T) -> Ordering {
        (left.class_const.origin.as_str()).cmp(right.class_const.origin.as_str())
    }

    impl PartialEq for T {
        fn eq(&self, other: &Self) -> bool {
            compare(self, other) == Ordering::Equal
        }
    }

    impl Eq for T {}

    impl PartialOrd for T {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(compare(self, other))
        }
    }

    impl Ord for T {
        fn cmp(&self, other: &Self) -> Ordering {
            compare(self, other)
        }
    }
}

/// `ParentClassConstSet`
type ParentClassConstSet = BTreeSet<parent_class_const::T>;

// ~~ ParentTypeConst ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub mod parent_type_const {
    use std::cmp::Ordering;
    use std::rc::Rc;

    use super::parent_class_elt::Parent;
    use crate::typing_defs::TypeconstType;

    pub struct T {
        pub typeconst: TypeconstType,
        pub parent: Rc<Parent>,
    }

    pub fn make(typeconst: TypeconstType, parent: Rc<Parent>) -> T {
        T { typeconst, parent }
    }

    pub fn compare(left: &T, right: &T) -> Ordering {
        (left.typeconst.origin.as_str()).cmp(right.typeconst.origin.as_str())
    }

    impl PartialEq for T {
        fn eq(&self, other: &Self) -> bool {
            compare(self, other) == Ordering::Equal
        }
    }

    impl Eq for T {}

    impl PartialOrd for T {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(compare(self, other))
        }
    }

    impl Ord for T {
        fn cmp(&self, other: &Self) -> Ordering {
            compare(self, other)
        }
    }
}

/// `ParentTypeConstSet`
type ParentTypeConstSet = BTreeSet<parent_type_const::T>;

/// `ParentClassEltSet.t MemberNameMap.t MemberKindMap.t`
type ParentMembers = BTreeMap<MemberKind, BTreeMap<String, ParentClassEltSet>>;

/// `class_elt MemberNameMap.t MemberKindMap.t`
type MemberMap = BTreeMap<MemberKind, BTreeMap<String, ClassElt>>;

/// `(Pos.t * string) * decl_ty * decl_ty list * Cls.t`: a direct ancestor,
/// with the position and name of its hint, its type, its type arguments and
/// its declaration.
type ParentInfo = ((Pos, String), DeclTy, Vec<DeclTy>, cls::T);

/// `Pos.t * string -> Typing_error.Reasons_callback.t`
type OnError<'a> = &'a dyn Fn((Pos, String)) -> reasons_callback::T;

fn constructor_is_consistent(kind: ConsistentKind) -> bool {
    match kind {
        ConsistentKind::ConsistentConstruct | ConsistentKind::FinalClass => true,
        ConsistentKind::Inconsistent => false,
    }
}

// ~~ Given a map of members, check that the overriding is correct. ~~~~~~~~~~~
//
// Please note that 'members' has a very general meaning here.
// It can be class variables, methods, static methods etc ... The same logic
// is applied to verify that the overriding is correct.

/// Rules for visibility
fn check_visibility(
    env: &Env,
    parent_vis: &CeVisibility,
    c_vis: &CeVisibility,
    parent_pos: PosOrDecl,
    pos: PosOrDecl,
    on_error: &reasons_callback::T,
) {
    use CeVisibility::*;
    match (parent_vis, c_vis) {
        (Vprivate(_), _) => {
            // The only time this case should come into play is when the
            // parent_class_elt comes from a trait
        }
        (Vpublic, Vpublic)
        | (Vprotected(_), Vprotected(_))
        | (Vprotected(_), Vpublic)
        | (VprotectedInternal { .. }, Vprotected(_))
        | (VprotectedInternal { .. }, Vpublic)
        | (Vinternal(_), Vpublic) => {}
        (
            VprotectedInternal {
                module__: parent_m, ..
            },
            VprotectedInternal {
                module__: child_m, ..
            },
        )
        | (
            VprotectedInternal {
                module__: parent_m, ..
            },
            Vinternal(child_m),
        )
        | (Vinternal(parent_m), Vinternal(child_m)) => {
            let err_opt = match typing_modules::can_access_internal(
                env,
                Some(child_m.clone()),
                Some(parent_m.clone()),
            ) {
                CanAccessInternalResult::Yes => None,
                CanAccessInternalResult::Disjoint(current, target) => {
                    Some(secondary::T::Visibility_override_internal {
                        pos,
                        module_name: Some(current),
                        parent_pos,
                        parent_module: target,
                    })
                }
                CanAccessInternalResult::Outside(target) => {
                    Some(secondary::T::Visibility_override_internal {
                        pos,
                        module_name: None,
                        parent_pos,
                        parent_module: target,
                    })
                }
                // TODO(T109499403) This case *is* possible, but because it refers to
                // class members in traits, any code that runs afoul of this rule will
                // also violate the nast check requiring that any trait member in a
                // non-internal trait must also be non-internal. I can't even figure out
                // a test case where this also doesn't violate _other_ rules about
                // referencing internal symbols in modules, e.g.:
                //
                //
                // internal trait Quuz {
                //   internal function lol(): void {}
                // }
                //
                // trait Corge {
                //   use Quuz;
                //   internal function lol(): void {}
                // }
                //
                // This code snippet alone raises two errors. One for `use Quuz`,
                // and one for `Corge::lol`.
                CanAccessInternalResult::OutsideViaTrait(_) => None,
            };
            if let Some(err) = err_opt {
                typing_error_utils::add_typing_error(
                    &typing_error::apply_reasons(err, on_error.clone()),
                    env,
                )
            }
        }
        _ => {
            let parent_vis = string_of_visibility(parent_vis).to_string();
            let vis = string_of_visibility(c_vis).to_string();
            let err = secondary::T::Visibility_extends {
                pos,
                vis,
                parent_pos,
                parent_vis,
            };
            typing_error_utils::add_typing_error(
                &typing_error::apply_reasons(err, on_error.clone()),
                env,
            )
        }
    }
}

fn check_class_elt_visibility(
    env: &Env,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    let parent_vis = &parent_class_elt.ce_visibility;
    let c_vis = &class_elt.ce_visibility;
    let parent_pos = ce_pos(parent_class_elt);
    let pos = ce_pos(class_elt);
    check_visibility(env, parent_vis, c_vis, parent_pos, pos, on_error)
}

/// `get_member member_kind class_` is a function of the member name; here the
/// name is its third argument.
fn get_member(member_kind: MemberKind, class_: &cls::T, name: &str) -> Option<ClassElt> {
    match member_kind {
        MemberKind::Property => cls::get_prop(class_, name),
        MemberKind::StaticProperty => cls::get_sprop(class_, name),
        MemberKind::Method => cls::get_method(class_, name),
        MemberKind::StaticMethod => cls::get_smethod(class_, name),
        MemberKind::Constructor { .. } => cls::construct(class_).0,
    }
}

/// `missing_member_info`
#[derive(Clone)]
struct MissingMemberInfo {
    member_name: String,
    member_kind: MemberKind,
    parent_class_elt: ClassElt,
    parent_pos: Pos,
    is_override: bool,
}

fn stub_all_methods_quickfix(
    class_name: &str,
    title: &str,
    methods: &[MissingMemberInfo],
) -> quickfix::Quickfix<Pos> {
    let method_texts: Vec<String> = methods
        .iter()
        .map(
            |MissingMemberInfo {
                 member_name,
                 parent_class_elt,
                 member_kind,
                 is_override,
                 ..
             }| {
                let is_static = member_kind::is_static(*member_kind);
                typing_skeleton::to_string(&typing_skeleton::of_method(
                    member_name,
                    parent_class_elt,
                    is_static,
                    *is_override,
                    false,
                ))
            },
        )
        .collect();
    let classish_end_new_text = method_texts.concat();
    quickfix::make(
        title.to_string(),
        quickfix::Edits::ClassishEnd {
            new_text: classish_end_new_text,
            name: class_name.to_string(),
        },
        vec![quickfix::HintStyle::HintStyleHint(
            classish_positions_types::Pos::ClassishClosingBrace(class_name.to_string()),
        )],
    )
}

/// Emit an error for every missing method or property in this class. Offer a
/// single quickfix for adding all the missing methods.
fn members_missing_error(
    env: &Env,
    class_pos: &Pos,
    class_: &cls::T,
    members: Vec<MissingMemberInfo>,
) {
    let (missing_methods, missing_props): (Vec<MissingMemberInfo>, Vec<MissingMemberInfo>) =
        members
            .into_iter()
            .partition(|MissingMemberInfo { member_kind, .. }| {
                member_kind::is_functional(*member_kind)
            });

    let (class_methods, interface_methods): (Vec<MissingMemberInfo>, Vec<MissingMemberInfo>) =
        missing_methods
            .into_iter()
            .partition(|MissingMemberInfo { is_override, .. }| *is_override);

    for (
        i,
        MissingMemberInfo {
            parent_pos,
            member_name,
            parent_class_elt,
            ..
        },
    ) in interface_methods.iter().enumerate()
    {
        let quickfixes = match i {
            0 => vec![stub_all_methods_quickfix(
                &cls::name(class_),
                "Add stubs for missing interface methods",
                &interface_methods,
            )],
            _ => vec![],
        };
        let defn_pos = ce_pos(parent_class_elt);

        let err = typing_error::primary(primary::T::Member_not_implemented {
            pos: parent_pos.clone(),
            member_name: member_name.clone(),
            decl_pos: defn_pos,
            quickfixes,
        });
        typing_error_utils::add_typing_error(&err, env);
    }

    for (
        i,
        MissingMemberInfo {
            member_name,
            parent_class_elt,
            ..
        },
    ) in class_methods.iter().enumerate()
    {
        let quickfixes = match i {
            0 => vec![stub_all_methods_quickfix(
                &cls::name(class_),
                "Add stubs for missing inherited methods",
                &class_methods,
            )],
            _ => vec![],
        };

        let trace =
            describe_route_lazily(env, cls::name(class_), parent_class_elt.ce_origin.clone());
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Implement_abstract {
                is_final: cls::final_(class_),
                pos: class_pos.clone(),
                decl_pos: ce_pos(parent_class_elt),
                trace,
                kind: primary::ImplementAbstractKind::meth,
                name: member_name.clone(),
                quickfixes,
            }),
            env,
        );
    }

    for MissingMemberInfo {
        member_name,
        parent_class_elt,
        ..
    } in &missing_props
    {
        let trace =
            describe_route_lazily(env, cls::name(class_), parent_class_elt.ce_origin.clone());
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Implement_abstract {
                is_final: cls::final_(class_),
                pos: class_pos.clone(),
                decl_pos: ce_pos(parent_class_elt),
                trace,
                kind: primary::ImplementAbstractKind::prop,
                name: member_name.clone(),
                quickfixes: vec![],
            }),
            env,
        );
    }
}

/// The trailing `()` of the OCaml (this function is used as a thunk) is not a
/// parameter here.
fn check_subtype_methods(
    env: &mut Env,
    check_return: bool,
    on_error: reasons_callback::T,
    (r_ancestor, ft_ancestor): &(Reason, &DeclFunType),
    (r_child, ft_child): &(Reason, &DeclFunType),
) {
    // Add deps here when we override
    typing_subtype_method::subtype_method_decl(
        check_return,
        env,
        r_child,
        ft_child,
        r_ancestor,
        ft_ancestor,
        on_error,
    )
}

/// An abstract member can be declared in multiple ancestors. Sometimes these
/// declarations can be different, but yet compatible depending on which
/// ancestor we inherit the member from. For example:
///
/// ```text
/// interface I1 { abstract public function foo(): int; }
/// interface I2 { abstract public function foo(): mixed; }
///
/// abstract class C implements I1, I2 {}
/// ```
///
/// I1::foo() is compatible with I2::foo(), but not vice versa. Hack chooses
/// the signature for C::foo() arbitrarily and can report an error if we make a
/// "wrong" choice. We check for this case and emit an extra line in the error
/// instructing the programmer to redeclare the member to remove the ambiguity.
///
/// Note: We could detect this case and make the correct choice for the user,
/// but this would require invalidating the current entry we have in the typing
/// heap for this class. We cannot make this choice earlier during typing_decl
/// because a class we depend on during the subtyping may not have been
/// declared yet.
///
/// `f parent child` is the OCaml `f parent child ()`. Both `f child parent`
/// and the error handler see the environment as it was before the attempt,
/// as in OCaml, where `f` closes over it.
// TODO(jjwu): get rid of this for type constants too, and we can delete
fn check_ambiguous_inheritance<X>(
    f: impl Fn(&mut Env, &X, &X),
    parent: &X,
    child: &X,
    pos: PosOrDecl,
    class_: &cls::T,
    origin: &str,
    on_error: &reasons_callback::T,
    env: &mut Env,
) {
    let saved_env = env.clone();
    diagnostics_state::try_when(
        || f(env, parent, child),
        || {
            cls::name(class_) != origin
                && diagnostics_state::try_no_errors(|| f(&mut saved_env.clone(), child, parent))
        },
        |error| {
            typing_error_utils::ambiguous_inheritance(
                pos,
                &cls::name(class_),
                origin,
                error,
                on_error,
                &saved_env,
            )
        },
    )
}

/// Checks that we're not overriding a final method.
fn check_override_final_method(
    env: &Env,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    let is_override_of_final_method =
        get_ce_final(parent_class_elt) && parent_class_elt.ce_origin != class_elt.ce_origin;
    if is_override_of_final_method && !get_ce_synthesized(class_elt) {
        // we have a final method being overridden by a user-declared method
        let parent_pos = ce_pos(parent_class_elt);
        let pos = ce_pos(class_elt);
        typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Override_final { pos, parent_pos },
                on_error.clone(),
            ),
            env,
        )
    }
}

/// Checks that we're not overriding a concrete static property.
fn check_override_concrete_static_prop(
    parent_pos: &Pos,
    env: &Env,
    member_name: &str,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
) {
    if !get_ce_abstract(parent_class_elt) && !get_ce_const(parent_class_elt) {
        let child_prop_pos = ce_pos(class_elt);
        typing_warning_utils::add(
            env,
            (
                parent_pos.clone(),
                typing_warning::Kind::Static_property_override,
                typing_warning::static_property_override::T {
                    prop_name: member_name.to_string(),
                    child_prop_pos,
                },
            ),
        )
    }
}

fn bad_sealed_override_error(
    env: &Env,
    member_name: &str,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    let parent_pos = ce_pos(parent_class_elt);
    let pos = ce_pos(class_elt);
    // OCaml evaluates the components of the tuple from right to left.
    let snd_err2 = secondary::T::Override_sealed {
        pos: pos.clone(),
        parent_pos,
    };
    let snd_err1 = secondary::T::Bad_method_override {
        pos,
        member_name: member_name.to_string(),
    };
    let on_error = reasons_callback::prepend_on_apply(on_error.clone(), snd_err1);
    typing_error_utils::add_typing_error(&typing_error::apply_reasons(snd_err2, on_error), env)
}

fn check_sealed_allowlist(
    env: &Env,
    member_name: &str,
    _parent_class: &cls::T,
    parent_class_elt: &ClassElt,
    class_: &cls::T,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    match &parent_class_elt.ce_sealed_allowlist {
        None => {}
        Some(allowlist) => {
            if !allowlist.contains(&class_elt.ce_origin) {
                // if the origin of class_elt is not in the allowlist we emit an error unless
                // the class itself is in the allowlist and the elt is imported from a trait
                let is_class_elt_origin_trait =
                    match decl_entry::to_option(typing_env::get_class(env, &class_elt.ce_origin)) {
                        Some(origin_class) if ast_defs::is_c_trait(cls::kind(&origin_class)) => {
                            true
                        }
                        _ => false,
                    };
                let is_class_in_allowlist = allowlist.contains(&cls::name(class_));
                if !(is_class_elt_origin_trait && is_class_in_allowlist) {
                    bad_sealed_override_error(
                        env,
                        member_name,
                        parent_class_elt,
                        class_elt,
                        on_error,
                    )
                }
            }
        }
    }
}

/// The rules for overriding methods with __RequirePackage follow by analogy
/// to visibility modifiers -- a method cannot become "less visible" by
/// override. So, if package a includes package b, a method requiring package
/// a may be overridden by one requiring package b.
fn check_require_package(
    env: &Env,
    member_name: &str,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    let pos = ce_pos(class_elt);
    let snd_err = secondary::T::Bad_method_override {
        pos,
        member_name: member_name.to_string(),
    };
    let on_error = reasons_callback::prepend_on_apply(on_error.clone(), snd_err);
    let strengthening_error = |p_super: PosOrDecl,
                               PosString(c_pos, c): &PosString,
                               child_str: &str,
                               parent_str: &str| {
        let reason_sub = {
            let c_pos = c_pos.clone();
            let c = c.clone();
            let child_str = child_str.to_string();
            typing_error::Lazy::new(move || {
                vec![Message(
                    c_pos,
                    format!("This method {} package `{}`", child_str, c).into(),
                )]
            })
        };
        let reason_super = {
            let parent_str = parent_str.to_string();
            typing_error::Lazy::new(move || {
                vec![Message(
                        p_super,
                        format!(
                            "The parent method {} attribute. The override must have a weaker requirement.",
                            parent_str
                        )
                        .into(),
                    )]
            })
        };
        typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Require_package_mismatch {
                    pos: c_pos.clone(),
                    reason_sub,
                    reason_super,
                },
                on_error.clone(),
            ),
            env,
        )
    };
    let mismatch_error = |PosString(p_pos, p): &PosString,
                          PosString(c_pos, c): &PosString,
                          parent_package: &package::T,
                          child_str: &str,
                          parent_str: &str,
                          inclusion_str: &str| {
        let reason_sub = {
            let c_pos = c_pos.clone();
            let c = c.clone();
            let child_str = child_str.to_string();
            typing_error::Lazy::new(move || {
                vec![Message(
                    c_pos,
                    format!("This method {} package `{}`", child_str, c).into(),
                )]
            })
        };
        let reason_super = {
            let p_pos = p_pos.clone();
            let p = p.clone();
            let c = c.clone();
            let parent_str = parent_str.to_string();
            let inclusion_str = inclusion_str.to_string();
            let parent_package = parent_package.clone();
            typing_error::Lazy::new(move || {
                vec![
                    Message(
                        p_pos,
                        format!(
                            "It cannot override a method that {} package `{}`",
                            parent_str, p
                        )
                        .into(),
                    ),
                    Message(
                        pos_or_decl::of_raw_pos(package::get_package_pos(&parent_package)),
                        format!("Because `{}` {} `{}`", p, inclusion_str, c).into(),
                    ),
                ]
            })
        };
        typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Require_package_mismatch {
                    pos: c_pos.clone(),
                    reason_sub,
                    reason_super,
                },
                on_error.clone(),
            ),
            env,
        )
    };

    let check_inclusion = |p: &PosString, c: &PosString, parent_str: &str, child_str: &str| {
        // OCaml evaluates the components of the tuple from right to left.
        let child_package = typing_env::get_package_by_name(env, &c.1);
        let parent_package = typing_env::get_package_by_name(env, &p.1);
        match (parent_package, child_package) {
            (Some(parent_package), Some(child_package)) => {
                match package::relationship(&parent_package, &child_package) {
                    package::PackageRelationship::Includes
                    | package::PackageRelationship::Equal => {}
                    package::PackageRelationship::Unrelated => mismatch_error(
                        p,
                        c,
                        &parent_package,
                        child_str,
                        parent_str,
                        "does not include",
                    ),
                    package::PackageRelationship::SoftIncludes => mismatch_error(
                        p,
                        c,
                        &parent_package,
                        child_str,
                        parent_str,
                        "only soft-includes",
                    ),
                }
            }
            (None, _) | (_, None) => {
                // Required package existence and inclusion of file package checked elsewhere
            }
        }
    };

    match (
        &parent_class_elt.ce_package_requirement,
        &class_elt.ce_package_requirement,
    ) {
        (Some(parent_requirent), Some(child_requirement)) => {
            match (parent_requirent, child_requirement) {
                (PackageRequirement::RPRequire(p), PackageRequirement::RPRequire(c)) => {
                    let parent_str = "requires";
                    let child_str = "requires";
                    check_inclusion(p, c, parent_str, child_str)
                }
                (PackageRequirement::RPSoft(_), PackageRequirement::RPRequire(c)) => {
                    let p_super = ce_pos(parent_class_elt);
                    let child_str = "requires";
                    let parent_str = "has a `__SoftRequirePackage`";
                    strengthening_error(p_super, c, child_str, parent_str)
                }
                (PackageRequirement::RPNormal, PackageRequirement::RPRequire(c)) => {
                    let p_super = ce_pos(parent_class_elt);
                    let child_str = "requires";
                    let parent_str = "does not have a `__RequirePackage`";
                    strengthening_error(p_super, c, child_str, parent_str)
                }
                (PackageRequirement::RPRequire(p), PackageRequirement::RPSoft(c)) => {
                    let parent_str = "requires";
                    let child_str = "soft-requires";
                    check_inclusion(p, c, parent_str, child_str)
                }
                (PackageRequirement::RPSoft(p), PackageRequirement::RPSoft(c)) => {
                    let parent_str = "soft-requires";
                    let child_str = "soft-requires";
                    check_inclusion(p, c, parent_str, child_str)
                }
                (PackageRequirement::RPNormal, PackageRequirement::RPSoft(c)) => {
                    let p_super = ce_pos(parent_class_elt);
                    let child_str = "soft-requires";
                    let parent_str = "does not have a `__SoftRequirePackage`";
                    strengthening_error(p_super, c, child_str, parent_str)
                }
                (PackageRequirement::RPSoft(_), PackageRequirement::RPNormal)
                | (PackageRequirement::RPRequire(_), PackageRequirement::RPNormal) => {
                    // Child is less restrictive than the parent, also covered by extends check
                }
                (PackageRequirement::RPNormal, PackageRequirement::RPNormal) => {
                    // Covered by the existing check of the symbol reference in `extends` clause
                }
            }
        }
        // non-methods
        (None, _) | (_, None) => {}
    }
}

/// Check that we are not overriding an __LSB property
fn check_lsb_overrides(
    env: &Env,
    member_kind: MemberKind,
    member_name: &str,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    let parent_is_lsb = get_ce_lsb(parent_class_elt);
    if member_kind::equal(&MemberKind::StaticProperty, &member_kind) && parent_is_lsb {
        // __LSB attribute is being overridden
        let parent_pos = ce_pos(parent_class_elt);
        let pos = ce_pos(class_elt);
        typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Override_lsb {
                    pos,
                    parent_pos,
                    member_name: member_name.to_string(),
                },
                on_error.clone(),
            ),
            env,
        )
    }
}

/// Check that __LateInit annotation on members are consistent between parents
/// and children.
fn check_lateinit(
    env: &Env,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    let lateinit_diff = get_ce_lateinit(parent_class_elt) != get_ce_lateinit(class_elt);
    if lateinit_diff {
        let parent_pos = ce_pos(parent_class_elt);
        let child_pos = ce_pos(class_elt);
        typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Bad_lateinit_override {
                    pos: child_pos,
                    parent_pos,
                    parent_is_lateinit: get_ce_lateinit(parent_class_elt),
                },
                on_error.clone(),
            ),
            env,
        )
    }
}

fn check_async(
    env: &Env,
    ft_parent: &DeclFunType,
    ft_child: &DeclFunType,
    parent_pos: PosOrDecl,
    pos: PosOrDecl,
    on_error: &reasons_callback::T,
) {
    match (decl_get_ft_async(ft_parent), decl_get_ft_async(ft_child)) {
        (true, false) => typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Override_async { pos, parent_pos },
                on_error.clone(),
            ),
            env,
        ),
        _ => {}
    }
}

fn check_xhp_attr_required(
    env: &Env,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    let is_less_strict = |tags: (Option<Tag>, Option<Tag>)| match tags {
        (Some(Tag::Required), _)
        | (Some(Tag::LateInit), Some(Tag::LateInit))
        | (Some(Tag::LateInit), None)
        | (None, None) => false,
        (_, _) => true,
    };
    let parent_attr = get_ce_xhp_attr(parent_class_elt);
    let attr = get_ce_xhp_attr(class_elt);
    match (parent_attr, attr) {
        (
            Some(XhpAttribute {
                tag: parent_tag, ..
            }),
            Some(XhpAttribute { tag, .. }),
        ) if is_less_strict((tag, parent_tag)) => {
            let parent_pos = ce_pos(parent_class_elt);
            let child_pos = ce_pos(class_elt);
            let lateinit = markdown_lite::md_codify("@lateinit");
            let required = markdown_lite::md_codify("@required");
            let show_tag_opt = |tag: Option<Tag>| match tag {
                None => format!("not {} or {}", required, lateinit),
                Some(Tag::Required) => required.clone(),
                Some(Tag::LateInit) => lateinit.clone(),
            };
            typing_error_utils::add_typing_error(
                &typing_error::apply_reasons(
                    secondary::T::Bad_xhp_attr_required_override {
                        pos: child_pos,
                        tag: show_tag_opt(tag),
                        parent_pos,
                        parent_tag: show_tag_opt(parent_tag),
                    },
                    on_error.clone(),
                ),
                env,
            )
        }
        (_, _) => {}
    }
}

fn add_pessimisation_dependency(
    env: &Env,
    child_cls: &cls::T,
    member_name: &str,
    member_kind: MemberKind,
    parent_cls: &cls::T,
) {
    let result = {
        // For the time being we only care about methods
        // (OCaml evaluates the components of the tuples from right to left.)
        match member_kind {
            MemberKind::Method => {
                let member = Some(typing_pessimisation_deps::DependentMember::Method(
                    member_name.to_string(),
                ));
                let parent_elt = cls::get_method(parent_cls, member_name);
                let child_elt = cls::get_method(child_cls, member_name);
                (child_elt, parent_elt, member)
            }
            MemberKind::StaticMethod => {
                let member = Some(typing_pessimisation_deps::DependentMember::SMethod(
                    member_name.to_string(),
                ));
                let parent_elt = cls::get_smethod(parent_cls, member_name);
                let child_elt = cls::get_smethod(child_cls, member_name);
                (child_elt, parent_elt, member)
            }
            _ => (None, None, None),
        }
    };
    match result {
        (Some(child_elt), Some(parent_elt), Some(member)) => {
            // We resolve both the parent and child to their origin. This allows us
            // to perform hierarchy poisioning for traits correctly: If a class C
            // gets a definition of some method foo by using a trait D, then the
            // following two conditions hold simultaneously:
            // a) If a child of C pessimises foo, then D::foo must be pessimised.
            // b) If the definition of foo in requires it to be pessimised, then
            //    all users of C::foo must be aware of that. Further, if C::foo
            //    overrides P::foo in some parent P of C, then this P::foo must be
            //    poisoned.
            //
            //
            // To resolve this, we effectively unify C:ffoo and D::foo in the
            // (pessimisation) dependency graph:
            // Elsewhere, we make sure that all users of C::foo point to D::foo
            // instead.  Here, we make sure that we mark D::foo as overriding P::foo
            // and any direct overrider of C::foo is marked as overriding D::foo
            // instead.
            let child_name = &child_elt.ce_origin;
            let parent_name = &parent_elt.ce_origin;
            typing_pessimisation_deps::add_override_dep(
                &typing_env::get_deps_mode(env),
                child_name,
                parent_name,
                &member,
            )
        }
        _ => {}
    }
}

fn add_member_dep(
    env: &Env,
    class_: &cls::T,
    parent_class: &cls::T,
    (member_kind, member_name, member_origin): (MemberKind, &str, &str),
) {
    let origin_pos = cls::pos(parent_class);
    if !pos_or_decl::is_hhi(&origin_pos) {
        let dep = match member_kind {
            MemberKind::Method => {
                dep::Variant::Method(member_origin.to_string(), member_name.to_string())
            }
            MemberKind::StaticMethod => {
                dep::Variant::SMethod(member_origin.to_string(), member_name.to_string())
            }
            MemberKind::StaticProperty => {
                dep::Variant::SProp(member_origin.to_string(), member_name.to_string())
            }
            MemberKind::Property => {
                dep::Variant::Prop(member_origin.to_string(), member_name.to_string())
            }
            MemberKind::Constructor { .. } => dep::Variant::Constructor(member_origin.to_string()),
        };
        let class_name = cls::name(class_);
        typing_deps::add_idep(
            &typing_env::get_deps_mode(env),
            &dep::Variant::Type(class_name),
            &dep,
        );
        if typing_env::get_tcopt(env).tco_record_fine_grained_dependencies {
            add_pessimisation_dependency(env, class_, member_name, member_kind, parent_class)
        }
    }
}

fn check_compatible_sound_dynamic_attributes(
    env: &Env,
    member_name: &str,
    member_kind: MemberKind,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    if !member_kind::is_constructor(member_kind)
        && get_ce_support_dynamic_type(parent_class_elt)
        && !get_ce_support_dynamic_type(class_elt)
    {
        let pos = ce_pos(class_elt);
        let parent_pos = ce_pos(parent_class_elt);
        typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Override_method_support_dynamic_type {
                    pos,
                    parent_pos,
                    parent_origin: parent_class_elt.ce_origin.clone(),
                    method_name: member_name.to_string(),
                },
                on_error.clone(),
            ),
            env,
        )
    }
}

fn check_prop_const_mismatch(
    env: &Env,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    if get_ce_const(class_elt) != get_ce_const(parent_class_elt) {
        // OCaml evaluates the fields of the record from right to left.
        let parent_is_const = get_ce_const(parent_class_elt);
        let parent_pos = ce_pos(parent_class_elt);
        let is_const = get_ce_const(class_elt);
        let pos = ce_pos(class_elt);
        typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Overriding_prop_const_mismatch {
                    pos,
                    is_const,
                    parent_pos,
                    parent_is_const,
                },
                on_error.clone(),
            ),
            env,
        )
    }
}

/// Property `readonly`-ness is invariant across overrides: reading a mutable
/// property through a `readonly` view, or writing a `readonly` property through
/// a mutable view, would both be unsound. We only warn (rather than error) for
/// now, following `check_override_concrete_static_prop`.
fn check_readonly_prop_override(
    parent_pos: &Pos,
    env: &Env,
    member_name: &str,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
) {
    if get_ce_readonly_prop_or_needs_concrete(class_elt)
        != get_ce_readonly_prop_or_needs_concrete(parent_class_elt)
    {
        let child_prop_pos = ce_pos(class_elt);
        typing_warning_utils::add(
            env,
            (
                parent_pos.clone(),
                typing_warning::Kind::Readonly_property_override,
                typing_warning::readonly_property_override::T {
                    prop_name: member_name.to_string(),
                    child_prop_pos,
                },
            ),
        )
    }
}

fn check_abstract_overrides_concrete(
    env: &Env,
    member_kind: MemberKind,
    parent_class_elt: &ClassElt,
    class_elt: &ClassElt,
    on_error: &reasons_callback::T,
) {
    if !get_ce_abstract(parent_class_elt) && get_ce_abstract(class_elt) {
        // It is valid for abstract class to extend a concrete class, but it cannot
        // redefine already concrete members as abstract.
        // See override_abstract_concrete.php test case for example.
        typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Abstract_concrete_override {
                    pos: ce_pos(class_elt),
                    parent_pos: ce_pos(parent_class_elt),
                    kind: if member_kind::is_functional(member_kind) {
                        secondary::AbstractConcreteOverrideKind::method_
                    } else {
                        secondary::AbstractConcreteOverrideKind::property
                    },
                },
                on_error.clone(),
            ),
            env,
        )
    }
}

/// Why this check: It would be unsound for a class that needs concrete
/// (`<<__NeedsConcrete>>`) to override one that does not, since a
/// __NeedsConcrete method imposes stricter requirements on its input
/// (`static` must point to a concrete class).
/// A final, concrete class is exempt: its methods only run with `static` bound
/// to the class itself.
fn check_needs_concrete_override(
    env: &Env,
    parent_class_elt: &ClassElt,
    class_: &cls::T,
    class_elt: &ClassElt,
    class_pos: &Pos,
    member_name: &str,
) {
    if !get_ce_readonly_prop_or_needs_concrete(parent_class_elt)
        && get_ce_readonly_prop_or_needs_concrete(class_elt)
        && !(cls::final_(class_) && typing_env::is_concrete_class(env, class_))
    {
        let defined_in_same_class = class_elt.ce_origin == cls::name(class_);
        let (error_pos, method_name_for_method_defined_outside_class) =
            match pos_or_decl::get_raw_pos_or_decl_reference(ce_pos(class_elt)) {
                RawPosOrDeclReference::Raw(pos) if defined_in_same_class => (pos, None),
                RawPosOrDeclReference::Raw(_) | RawPosOrDeclReference::Decl_ref(_) => {
                    (class_pos.clone(), Some(member_name.to_string()))
                }
            };
        let method_pos = ce_pos(class_elt);
        let parent_pos = ce_pos(parent_class_elt);
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Needs_concrete_override {
                pos: error_pos,
                method_pos,
                parent_pos,
                method_name_for_method_defined_outside_class,
            }),
            env,
        )
    }
}

fn detect_multiple_concrete_defs(
    (class_elt, class_): (&ClassElt, &cls::T),
    (parent_class_elt, parent_class): (&ClassElt, &cls::T),
) -> bool {
    // We want to check if there are conflicting trait declarations of a class member.
    // If the parent we are checking is a trait and the member's origin both isn't
    // that parent and isn't the class itself, then it must come from another trait
    // and there is a conflict.
    //
    // We rule out cases where any of the traits' member
    // is synthetic (from a requirement) or abstract.
    match cls::kind(parent_class) {
        ast_defs::ClassishKind::Ctrait => {
            !get_ce_synthesized(class_elt)
                && !get_ce_abstract(class_elt)
                && !get_ce_abstract(parent_class_elt)
                && class_elt.ce_origin != cls::name(class_)
        }
        ast_defs::ClassishKind::Cinterface
        | ast_defs::ClassishKind::Cclass(_)
        | ast_defs::ClassishKind::Cenum
        | ast_defs::ClassishKind::CenumClass(_) => false,
    }
}

fn check_multiple_concrete_definitions(
    env: &Env,
    member_name: &str,
    member_kind: MemberKind,
    (class_elt, class_): (&ClassElt, &cls::T),
    (parent_class_elt, parent_class): (&ClassElt, &cls::T),
    on_error: &reasons_callback::T,
) {
    if (member_kind::is_functional(member_kind) || get_ce_const(class_elt))
        && detect_multiple_concrete_defs((class_elt, class_), (parent_class_elt, parent_class))
    {
        // Multiple concrete trait definitions, error
        typing_error_utils::add_typing_error(
            &typing_error::apply_reasons(
                secondary::T::Multiple_concrete_defs {
                    pos: ce_pos(class_elt),
                    parent_pos: ce_pos(parent_class_elt),
                    origin: class_elt.ce_origin.clone(),
                    parent_origin: parent_class_elt.ce_origin.clone(),
                    name: member_name.to_string(),
                    class_name: cls::name(class_),
                },
                on_error.clone(),
            ),
            env,
        )
    }
}

/// Get the type of the value that is returned: for an async function that has
/// declared return type Awaitable<t>, this is t, otherwise it's just the
/// declared return type
fn get_return_value_type(ft: &DeclFunType) -> DeclTy {
    match (decl_get_ft_async(ft), ft.ret.node_ref()) {
        (true, DTy_::Tapply(id_and_args))
            if id_and_args.1.len() == 1
                && id_and_args.0.id_ref().as_str() == sn::classes::AWAITABLE =>
        {
            id_and_args.1[0].clone()
        }
        _ => ft.ret.clone(),
    }
}

fn maybe_poison_ancestors(
    env: &Env,
    ft_parent: &DeclFunType,
    ft_child: &DeclFunType,
    parent_class: &cls::T,
    child_class: &cls::T,
    origin: &str,
    member_name: &str,
    member_kind: MemberKind,
) {
    if provider_context::get_tcopt(&typing_env::get_ctx(env)).tco_like_casts {
        let parent_return_ty = get_return_value_type(ft_parent);
        let child_return_ty = get_return_value_type(ft_child);
        let (declared_class, declared_return_ty): (cls::T, DeclTy) =
            if cls::name(child_class) == origin {
                (child_class.clone(), child_return_ty)
            } else {
                match typing_env::get_class(env, origin) {
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                        (child_class.clone(), child_return_ty)
                    }
                    decl_entry::T::Found(c) => match typing_env::get_method(env, &c, member_name) {
                        None => (child_class.clone(), child_return_ty),
                        Some(elt) => {
                            let fty: &DeclTy = &elt.ce_type;
                            match fty.node_ref() {
                                DTy_::Tfun(ft) => {
                                    let ty = get_return_value_type(ft);
                                    (c, ty)
                                }
                                _ => (child_class.clone(), child_return_ty),
                            }
                        }
                    },
                }
            };
        // OCaml evaluates the components of the tuple from right to left.
        let declared_enforcement = typing_enforceability::get_enforcement(
            Some(true),
            Some(&declared_class),
            env,
            &declared_return_ty,
        );
        let parent_enforcement = typing_enforceability::get_enforcement(
            Some(true),
            Some(parent_class),
            env,
            &parent_return_ty,
        );
        match (parent_enforcement, declared_enforcement) {
            // If the parent itself overrides a fully-enforced return type
            // then we need to "copy down" any intersection, so record this in the log
            (Enforcement::Unenforced, Enforcement::Unenforced) => {
                let child_pos = pos_or_decl::unsafe_to_raw_pos(decl_get_pos(&ft_child.ret));
                let parent_pos = pos_or_decl::unsafe_to_raw_pos(decl_get_pos(&ft_parent.ret));
                let p = crate::pos::to_absolute(&parent_pos);
                let s = format!("!,{},{}", crate::pos::filename(&p), crate::pos::line(&p));
                typing_log::log_pessimise_return(None, env, &child_pos, Some(&s))
            }
            (Enforcement::Enforced, Enforcement::Unenforced) => match parent_return_ty.node_ref() {
                DTy_::Tmixed => {}
                _ => {
                    let enforced_declared_ty = typing_partial_enforcement::get_enforced_type(
                        env,
                        Some(&declared_class),
                        &declared_return_ty,
                    );
                    let tmp_env = {
                        let self_ty = typing_make_type::class_type(
                            typing_reason::none(),
                            origin.to_string(),
                            (cls::tparams(&declared_class).iter())
                                .map(|tp| {
                                    typing_make_type::generic(
                                        typing_reason::none(),
                                        tp.name.id_ref().as_str().to_string(),
                                    )
                                })
                                .collect(),
                        );
                        let mut tpenv = type_parameter_env::empty();
                        type_parameter_env::add_upper_bound(
                            None,
                            &mut tpenv,
                            sn::typehints::THIS.to_string(),
                            self_ty,
                        );
                        let mut tmp_env = env.clone();
                        typing_env::env_with_tpenv(&mut tmp_env, tpenv);
                        tmp_env
                    };
                    let child_pos = pos_or_decl::unsafe_to_raw_pos(decl_get_pos(&ft_child.ret));
                    let enforced_parent_ty = typing_partial_enforcement::get_enforced_type(
                        env,
                        Some(parent_class),
                        &parent_return_ty,
                    );
                    // We need that the enforced child type is a subtype of the enforced parent type
                    let sub1 = typing_phase::is_sub_type_decl(
                        Some(true),
                        &tmp_env,
                        &enforced_declared_ty,
                        &enforced_parent_ty,
                    );
                    // But also the original child type should be a subtype of the enforced parent type
                    let sub2 = typing_phase::is_sub_type_decl(
                        Some(true),
                        &tmp_env,
                        &declared_return_ty,
                        &enforced_parent_ty,
                    );
                    if sub1 && sub2 {
                        let ty_str = typing_print::full_decl(
                            None,
                            &typing_env::get_tcopt(env),
                            &enforced_parent_ty.clone().to_oxidized(),
                        );
                        // Hack to remove "\\" if XHP type is rendered as "\\:X"
                        // TODO: fix Typing_print so that it renders XHP correctly
                        // (`Str.global_replace (Str.regexp "\\\\:") ":"`)
                        let ty_str = ty_str.replace("\\:", ":");
                        typing_log::log_pessimise_return(None, env, &child_pos, Some(&ty_str))
                    } else {
                        let classes: Vec<cls::T> = (cls::all_ancestor_names(child_class).iter())
                            .map(|c| decl_entry::to_option(typing_env::get_class(env, c)))
                            .collect::<Vec<_>>()
                            .into_iter()
                            .flatten()
                            .collect();
                        for cls in &classes {
                            let elt = match member_kind {
                                MemberKind::StaticMethod => cls::get_smethod(cls, member_name),
                                MemberKind::Method => cls::get_method(cls, member_name),
                                _ => None,
                            };
                            if let Some(elt) = elt {
                                let fty: &DeclTy = &elt.ce_type;
                                match fty.node_ref() {
                                    DTy_::Tfun(ft) => {
                                        let pos =
                                            pos_or_decl::unsafe_to_raw_pos(decl_get_pos(&ft.ret));
                                        // The ^ denotes poisoning
                                        typing_log::log_pessimise_poisoned_return(
                                            None,
                                            env,
                                            &pos,
                                            &format!("{}::{}", cls::name(child_class), member_name),
                                        )
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }
            },
            _ => {}
        }
    }
}

fn bad_member_override_not_subtype(
    env: &Env,
    is_method: bool,
    class_: &cls::T,
    parent_class: &cls::T,
    parent_type: &DeclTy,
    member_name: &str,
    class_elt: &ClassElt,
    parent_class_elt: &ClassElt,
) -> secondary::T {
    let member_pos = ce_pos(class_elt);
    let member_parent_pos = ce_pos(parent_class_elt);

    let member_type: DeclTy = DeclTy::clone(&class_elt.ce_type);
    let member_parent_type: DeclTy = DeclTy::clone(&parent_class_elt.ce_type);
    // The lazy messages print with the environment as it is now.
    let env = Rc::new(env.clone());
    let print_lazily = |ty: DeclTy| -> typing_error::Lazy<String> {
        let env = Rc::clone(&env);
        typing_error::Lazy::new(move || {
            typing_print::full_strip_ns_decl(None, true, &*env, &ty.to_oxidized())
        })
    };
    let get_origin_type = |class_: &cls::T, class_elt: &ClassElt| -> typing_error::Lazy<String> {
        let env = Rc::clone(&env);
        let class_ = class_.clone();
        let origin = class_elt.ce_origin.clone();
        typing_error::Lazy::new(move || match cls::get_ancestor(&class_, &origin) {
            Some(ty) => typing_print::full_strip_ns_decl(None, true, &*env, &ty.to_oxidized()),
            None => utils::strip_ns(&origin).to_string(),
        })
    };
    secondary::T::Bad_member_override_not_subtype {
        is_method,
        class_name: cls::name(class_),
        parent_name: cls::name(parent_class),
        parent_type: print_lazily(parent_type.clone()),
        member_pos,
        member_name: member_name.to_string(),
        member_type: print_lazily(member_type),
        origin_name: class_elt.ce_origin.clone(),
        origin_type: get_origin_type(class_, class_elt),
        member_parent_pos,
        member_parent_type: print_lazily(member_parent_type),
        member_parent_origin: parent_class_elt.ce_origin.clone(),
        member_parent_origin_type: get_origin_type(parent_class, parent_class_elt),
    }
}

/// Check that overriding is correct
fn check_override(
    env: &mut Env,
    check_member_unique: bool,
    member_name: &str,
    member_kind: MemberKind,
    class_: &cls::T,
    parent_class: &cls::T,
    parent_type: &DeclTy,
    parent_pos: &Pos,
    class_pos: &Pos,
    class_elt: &ClassElt,
    parent_class_elt: &ClassElt,
    on_error: reasons_callback::T,
) {
    // If the class element is defined in the class that we're checking, then
    // don't wrap with the extra
    // "Class ... does not correctly implement all required members" message
    let on_error = if class_elt.ce_origin == cls::name(class_) {
        typing_env::unify_error_assert_primary_pos_in_current_decl(env)
    } else {
        on_error
    };

    match member_kind {
        MemberKind::StaticProperty => check_override_concrete_static_prop(
            parent_pos,
            env,
            member_name,
            parent_class_elt,
            class_elt,
        ),
        _ => {}
    }

    if get_ce_tests_bypass_visibility(parent_class_elt) {
        let is_private_parent = match &parent_class_elt.ce_visibility {
            CeVisibility::Vprivate(_) => true,
            _ => false,
        };
        let is_public_child = match &class_elt.ce_visibility {
            CeVisibility::Vpublic => true,
            _ => false,
        };
        // Private members marked `<<__TestsBypassVisibility>>` are kept during
        // inheritance, so they reach normal override checking. A concrete private
        // member with the attribute must remain unique in its hierarchy; otherwise
        // a test-context access through a subclass would be ambiguous between the
        // inherited private member and the subclass member.
        //
        // We do not reject the opposite direction, where the ancestor has an
        // ordinary concrete private member and the child introduces a member with
        // `<<__TestsBypassVisibility>>`. The ordinary ancestor private member is
        // still inaccessible from test contexts, so upcasting cannot expose it.
        if is_private_parent && !get_ce_abstract(parent_class_elt) {
            let pos = ce_pos(class_elt);
            let parent_pos = ce_pos(parent_class_elt);
            typing_error_utils::add_typing_error(
                &typing_error::apply_reasons(
                    secondary::T::Override_tests_bypass_visibility {
                        pos,
                        member_name: member_name.to_string(),
                        parent_pos,
                    },
                    on_error.clone(),
                ),
                env,
            )
        } else if !is_public_child && !get_ce_tests_bypass_visibility(class_elt) {
            // Abstract private methods may be implemented in subclasses, but the
            // implementation must opt in as well so the inherited test-only access
            // contract is preserved.
            let pos = ce_pos(class_elt);
            let parent_pos = ce_pos(parent_class_elt);
            typing_error_utils::add_typing_error(
                &typing_error::apply_reasons(
                    secondary::T::Abstract_tests_bypass_visibility_missing_attr {
                        pos,
                        member_name: member_name.to_string(),
                        parent_pos,
                    },
                    on_error.clone(),
                ),
                env,
            )
        }
    }

    if member_kind::is_method(member_kind) {
        // We first verify that we aren't overriding a final method.  We only check
        // for final overrides on methods, not properties. Constructors have their
        // own code-path with this check, see `check_constructors`
        check_override_final_method(env, parent_class_elt, class_elt, &on_error);
        check_sealed_allowlist(
            env,
            member_name,
            parent_class,
            parent_class_elt,
            class_,
            class_elt,
            &on_error,
        )
    }

    // We check visibility on constructor overrides regardless of consistency,
    // so this enforces the same constraint for package requirements.
    if member_kind::is_functional(member_kind) {
        check_require_package(env, member_name, parent_class_elt, class_elt, &on_error)
    }

    // Verify that we are not overriding an __LSB property
    check_lsb_overrides(
        env,
        member_kind,
        member_name,
        parent_class_elt,
        class_elt,
        &on_error,
    );
    check_lateinit(env, parent_class_elt, class_elt, &on_error);
    check_xhp_attr_required(env, parent_class_elt, class_elt, &on_error);
    check_class_elt_visibility(env, parent_class_elt, class_elt, &on_error);
    check_prop_const_mismatch(env, parent_class_elt, class_elt, &on_error);
    check_abstract_overrides_concrete(env, member_kind, parent_class_elt, class_elt, &on_error);
    // On properties the shared flag means readonly, not __NeedsConcrete
    if member_kind::is_method(member_kind) {
        check_needs_concrete_override(
            env,
            parent_class_elt,
            class_,
            class_elt,
            class_pos,
            member_name,
        );
    } else if member_kind::is_property(member_kind) {
        check_readonly_prop_override(parent_pos, env, member_name, parent_class_elt, class_elt);
    }

    let pos = ce_pos(class_elt);

    let fty_child: &DeclTy = &class_elt.ce_type;
    let fty_parent: &DeclTy = &parent_class_elt.ce_type;
    let snd_err = if member_kind::is_functional(member_kind) {
        secondary::T::Bad_method_override {
            pos: pos.clone(),
            member_name: member_name.to_string(),
        }
    } else {
        secondary::T::Bad_prop_override {
            pos: pos.clone(),
            member_name: member_name.to_string(),
        }
    };
    // Modify the `Typing_error.Reasons_callback.t` so that we always end up
    // with the error code given by `snd_err` and the reasons of whatever
    // error it is applied to are appended to the reasons given by `snd_err`
    let on_error = reasons_callback::prepend_on_apply(on_error, snd_err);

    if check_member_unique {
        check_multiple_concrete_definitions(
            env,
            member_name,
            member_kind,
            (class_elt, class_),
            (parent_class_elt, parent_class),
            &on_error,
        )
    }
    check_compatible_sound_dynamic_attributes(
        env,
        member_name,
        member_kind,
        parent_class_elt,
        class_elt,
        &on_error,
    );

    match (fty_parent.node_ref(), fty_child.node_ref()) {
        (DTy_::Tfun(ft_parent), DTy_::Tfun(ft_child)) => {
            let r_parent = fty_parent.reason();
            let r_child = fty_child.reason();
            match member_kind {
                MemberKind::Constructor {
                    is_consistent: false,
                } => {
                    // we don't check that constructor signatures follow
                    // subtyping rules except with __ConsistentConstruct
                }
                _ => {
                    maybe_poison_ancestors(
                        env,
                        ft_parent,
                        ft_child,
                        parent_class,
                        class_,
                        &class_elt.ce_origin,
                        member_name,
                        member_kind,
                    );
                    check_async(
                        env,
                        ft_parent,
                        ft_child,
                        decl_reason_to_pos(r_parent),
                        decl_reason_to_pos(r_child),
                        &on_error,
                    );
                    let check_subtype_methods_ =
                        |env: &mut Env,
                         on_error: &reasons_callback::T,
                         x: &(Reason, &DeclFunType),
                         y: &(Reason, &DeclFunType)| {
                            let on_error = reasons_callback::prepend_on_apply(
                                on_error.clone(),
                                bad_member_override_not_subtype(
                                    env,
                                    member_kind::is_functional(member_kind),
                                    class_,
                                    parent_class,
                                    parent_type,
                                    member_name,
                                    class_elt,
                                    parent_class_elt,
                                ),
                            );
                            check_subtype_methods(
                                env,
                                !member_kind::is_constructor(member_kind),
                                on_error,
                                x,
                                y,
                            )
                        };
                    check_ambiguous_inheritance(
                        |env: &mut Env, x: &(Reason, &DeclFunType), y: &(Reason, &DeclFunType)| {
                            check_subtype_methods_(env, &on_error, x, y)
                        },
                        &(localize_reason(r_parent), &**ft_parent),
                        &(localize_reason(r_child), &**ft_child),
                        pos,
                        class_,
                        &class_elt.ce_origin,
                        &on_error,
                        env,
                    )
                }
            }
        }
        _ => {
            let ty_err_opt = if get_ce_const(class_elt) {
                typing_phase::sub_type_decl(env, fty_child, fty_parent, Some(on_error))
            } else {
                typing_ops::unify_decl(pos, Ureason::URnone, env, on_error, fty_parent, fty_child)
            };
            add_typing_error_opt(env, ty_err_opt)
        }
    }
}

/// Constants and type constants with declared values in declared interfaces
/// can never be overridden by other inherited constants.
/// @precondition: both constants must not be synthesized
fn constant_conflict_with_declared_interface_or_trait(
    include_traits: Option<bool>,
    env: &Env,
    implements: &[(PosOrDecl, cls::T)],
    parent_class: &cls::T,
    class_: &cls::T,
    parent_origin: &str,
    origin: &str,
    const_name: &str,
) -> bool {
    let include_traits = include_traits.unwrap_or(true);
    let is_inherited_and_conflicts_with_parent =
        origin != cls::name(class_) && origin != parent_origin;
    let child_const_from_used_trait = if include_traits {
        match typing_env::get_class(env, origin) {
            decl_entry::T::Found(cls) => ast_defs::is_c_trait(cls::kind(&cls)),
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
        }
    } else {
        false
    };

    // True if a declared interface on class_ has a concrete constant with
    // the same name and origin as child constant
    let child_const_from_declared_interface = match typing_env::get_class(env, origin) {
        decl_entry::T::Found(cls) => {
            ast_defs::is_c_interface(cls::kind(&cls))
                && if include_traits {
                    true
                } else {
                    implements.iter().fold(false, |acc, (_, iface)| {
                        acc || match cls::get_const(iface, const_name) {
                            None => false,
                            Some(const_) => const_.origin.as_str() == origin,
                        }
                    })
                }
        }
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
    };

    match cls::kind(parent_class) {
        ast_defs::ClassishKind::Cinterface => is_inherited_and_conflicts_with_parent,
        ast_defs::ClassishKind::Cclass(_) => {
            is_inherited_and_conflicts_with_parent
                && (child_const_from_declared_interface || child_const_from_used_trait)
        }
        ast_defs::ClassishKind::Ctrait => {
            is_inherited_and_conflicts_with_parent
                && (child_const_from_declared_interface || child_const_from_used_trait)
                && {
                    // constant must be declared on a trait (or interface if include_traits == true) to conflict
                    match typing_env::get_class(env, parent_origin) {
                        decl_entry::T::Found(cls) => {
                            if include_traits {
                                let k = cls::kind(&cls);
                                ast_defs::is_c_trait(k) || ast_defs::is_c_interface(k)
                            } else {
                                ast_defs::is_c_trait(cls::kind(&cls))
                            }
                        }
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
                    }
                }
        }
        ast_defs::ClassishKind::CenumClass(_) | ast_defs::ClassishKind::Cenum => false,
    }
}

fn check_abstract_const_in_concrete_class(
    env: &Env,
    (class_pos, class_): (&Pos, &cls::T),
    (const_name, class_const): (&str, &ClassConst),
) {
    let is_final = cls::final_(class_);
    if ast_defs::is_c_concrete(cls::kind(class_)) || is_final {
        match class_const.kind {
            ClassConstKind::CCAbstract(_) => {
                let trace =
                    describe_route_lazily(env, cls::name(class_), class_const.origin.to_string());
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Implement_abstract {
                        is_final,
                        pos: class_pos.clone(),
                        decl_pos: decl_pos(&class_const.pos),
                        trace,
                        kind: primary::ImplementAbstractKind::const_,
                        name: const_name.to_string(),
                        quickfixes: vec![],
                    }),
                    env,
                )
            }
            ClassConstKind::CCConcrete => {}
        }
    }
}

fn check_const_override(
    env: &mut Env,
    implements: &[(PosOrDecl, cls::T)],
    const_name: &str,
    parent_class: &cls::T,
    (class_pos, class_): (&Pos, &cls::T),
    parent_class_const: &ClassConst,
    class_const: &ClassConst,
    on_error: reasons_callback::T,
) {
    if parent_class_const.origin.as_str() == class_const.origin.as_str() {
        check_abstract_const_in_concrete_class(env, (class_pos, class_), (const_name, class_const))
    } else {
        let parent_kind = cls::kind(parent_class);
        let class_kind = cls::kind(class_);
        // Shared preconditions for const_interface_member_not_unique and
        // is_bad_interface_const_override
        let is_concrete = |k: &ClassConstKind| match k {
            ClassConstKind::CCConcrete => true,
            ClassConstKind::CCAbstract(_) => false,
        };
        let both_are_non_synthetic_and_concrete =
            // Synthetic
            !class_const.is_synthesized
            // The parent we are checking is synthetic, no point in checking
            && !parent_class_const.is_synthesized
            // Only check if parent and child have concrete definitions
            && is_concrete(&class_const.kind)
            && is_concrete(&parent_class_const.kind);
        let const_interface_or_trait_member_not_unique =
            // Similar to detect_multiple_concrete_defs, we check if there are multiple
            // concrete implementations of class constants with no override.
            constant_conflict_with_declared_interface_or_trait(
                None,
                env,
                implements,
                parent_class,
                class_,
                parent_class_const.origin.as_str(),
                class_const.origin.as_str(),
                const_name,
            ) && both_are_non_synthetic_and_concrete;
        let is_bad_interface_const_override =
            // HHVM does not support one specific case of overriding constants:
            // If the original constant was defined as non-abstract in an interface or trait,
            // it cannot be overridden when implementing or extending that interface or using that trait.
            if ast_defs::is_c_interface(parent_kind) {
                both_are_non_synthetic_and_concrete
                    // Check that the constant is indeed defined in class_
                    && class_const.origin.as_str() == cls::name(class_)
            } else {
                false
            };
        let is_abstract_concrete_override = match (&parent_class_const.kind, &class_const.kind) {
            (ClassConstKind::CCConcrete, ClassConstKind::CCAbstract(_)) => true,
            _ => false,
        };

        let remove_hh_member_of = |dty: &DeclTy| -> DeclTy {
            match dty.node_ref() {
                DTy_::Tapply(id_and_args) if id_and_args.1.len() == 2 => {
                    // `Tapply (_hh_member_of, [_enum; dty])`
                    id_and_args.1[1].clone()
                }
                _ => dty.clone(),
            }
        };
        let class_const_type = if ast_defs::is_c_enum_class(class_kind) {
            remove_hh_member_of(&class_const.ty)
        } else {
            class_const.ty.clone()
        };
        let parent_class_const_type = if ast_defs::is_c_enum_class(parent_kind) {
            remove_hh_member_of(&parent_class_const.ty)
        } else {
            parent_class_const.ty.clone()
        };

        let ty_err_opt1 = if const_interface_or_trait_member_not_unique {
            let snd_err = secondary::T::Interface_or_trait_const_multiple_defs {
                pos: decl_pos(&class_const.pos),
                name: const_name.to_string(),
                origin: class_const.origin.to_string(),
                parent_pos: decl_pos(&parent_class_const.pos),
                parent_origin: parent_class_const.origin.to_string(),
            };
            Some(typing_error::apply_reasons(snd_err, on_error.clone()))
        } else if is_bad_interface_const_override {
            let snd_err = secondary::T::Concrete_const_interface_override {
                pos: decl_pos(&class_const.pos),
                name: const_name.to_string(),
                parent_pos: decl_pos(&parent_class_const.pos),
                parent_origin: parent_class_const.origin.to_string(),
            };
            Some(typing_error::apply_reasons(snd_err, on_error.clone()))
        } else if is_abstract_concrete_override {
            let snd_err = secondary::T::Abstract_concrete_override {
                pos: decl_pos(&class_const.pos),
                parent_pos: decl_pos(&parent_class_const.pos),
                kind: secondary::AbstractConcreteOverrideKind::constant,
            };
            Some(typing_error::assert_in_current_decl(
                snd_err,
                typing_env::get_current_decl_and_file(env),
            ))
        } else {
            None
        };
        add_typing_error_opt(env, ty_err_opt1);
        let ty_err_opt2 = typing_phase::sub_type_decl(
            env,
            &class_const_type,
            &parent_class_const_type,
            Some(reasons_callback::class_constant_type_mismatch(on_error)),
        );
        add_typing_error_opt(env, ty_err_opt2)
    }
}

fn check_inherited_member_is_dynamically_callable(
    env: &Env,
    inheriting_class: (&Pos, &cls::T),
    parent_class: &cls::T,
    (member_kind, member_name, parent_class_elt): (MemberKind, &str, &ClassElt),
) {
    let (inheriting_class_pos, inheriting_class) = inheriting_class;
    if cls::get_support_dynamic_type(inheriting_class)
        && !cls::get_support_dynamic_type(parent_class)
    // TODO: ideally refactor so the last test is not systematically performed on all methods
    {
        match cls::kind(parent_class) {
            ast_defs::ClassishKind::Cclass(_) | ast_defs::ClassishKind::Ctrait => match member_kind
            {
                MemberKind::Method => {
                    if !get_ce_support_dynamic_type(parent_class_elt) {
                        // since the attribute is missing run the inter check
                        let ty: &DeclTy = &parent_class_elt.ce_type;
                        match ty.node_ref() {
                            DTy_::Tfun(fun_ty) => {
                                if !typing_dynamic::sound_dynamic_interface_check_from_fun_ty(
                                    Some(parent_class),
                                    env,
                                    fun_ty,
                                ) {
                                    diagnostics_state::method_is_not_dynamically_callable(
                                        inheriting_class_pos.clone(),
                                        member_name,
                                        &cls::name(inheriting_class),
                                        false,
                                        Some((
                                            ce_pos(parent_class_elt),
                                            parent_class_elt.ce_origin.clone(),
                                        )),
                                        None,
                                    )
                                }
                            }
                            _ => {}
                        }
                    }
                }
                MemberKind::StaticMethod
                | MemberKind::StaticProperty
                | MemberKind::Property
                | MemberKind::Constructor { .. } => {}
            },
            ast_defs::ClassishKind::Cinterface
            | ast_defs::ClassishKind::CenumClass(_)
            | ast_defs::ClassishKind::Cenum => {}
        }
    }
}

fn eager_resolve_member_via_req_class(
    env: &Env,
    parent_class_elt: &ClassElt,
    class_: &cls::T,
    member_kind: MemberKind,
    member_name: &str,
) -> Option<ClassElt> {
    let member_element_opt = get_member(member_kind, class_, member_name);
    let req_class_constraints = cls::all_ancestor_req_class_requirements(class_);
    if req_class_constraints.is_empty() {
        // fast path: if class_ does not have require class constraints then eager resolution cannot apply
        member_element_opt
    } else {
        member_element_opt.map(|member_element| {
            // eager resolution should happen only if one of the matched elements is defined in an interface
            // so check the kind of the classish where the elements are defined
            let origin_is_interface =
                |el: &ClassElt| match typing_env::get_class(env, &el.ce_origin) {
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
                    decl_entry::T::Found(el) => ast_defs::is_c_interface(cls::kind(&el)),
                };
            let parent_element_origin_is_interface = origin_is_interface(parent_class_elt);
            let element_origin_is_interface = origin_is_interface(&member_element);
            if ast_defs::is_c_trait(cls::kind(class_))
                && (parent_element_origin_is_interface || element_origin_is_interface)
            {
                if member_element.ce_origin == cls::name(class_) {
                    member_element
                } else {
                    // Since at least one of the elements is not defined in a trait, and the base trait has a
                    // require class constraint, perform eager fetch of the element via the required class.
                    let member_element_in_req_class =
                        req_class_constraints.iter().find_map(|req| {
                            let (_, cn, _) = typing_utils::unwrap_class_type(&req.ty);
                            decl_entry::to_option(decl_provider::get_class(
                                None,
                                &typing_env::get_ctx(env),
                                cn.id_ref().as_str(),
                            ))
                            .and_then(|cnc| get_member(member_kind, &cnc, member_name))
                        });
                    match member_element_in_req_class {
                        Some(member_element_in_req_class) => ClassElt {
                            ce_flags: typing_defs_flags::class_elt::set_synthesized(
                                member_element_in_req_class.ce_flags,
                            ),
                            ..member_element_in_req_class
                        },
                        None => member_element,
                    }
                }
            } else {
                member_element
            }
        })
    }
}

fn check_class_against_parent_class_elt(
    on_error: OnError<'_>,
    (class_pos, class_): (&Pos, &cls::T),
    member_kind: MemberKind,
    member_name: &str,
    parent_class_elt::T {
        class_elt: parent_class_elt,
        parent,
        errors_if_not_overriden,
    }: &parent_class_elt::T,
    env: &mut Env,
) -> Vec<MissingMemberInfo> {
    let Parent {
        parent_pos,
        parent_class,
        parent_type,
    } = &**parent;
    add_member_dep(
        env,
        class_,
        parent_class,
        (member_kind, member_name, &parent_class_elt.ce_origin),
    );

    let member_element_opt =
        // If a trait does not define the element itself, but will inherit the element from a
        // require class constraint then eagerly compare the element from the required class
        // against the parent class elements.  This is useful to eagerly solve conflicts between
        // interfaces implemented by the trait.
        // However, the eager resolution should not be applied to solve conflicts due to multiple
        // definitions in traits used by the trait, as HHVM does not perform the eager resolution
        // and fatals when flattening the trait methods.
        eager_resolve_member_via_req_class(env, parent_class_elt, class_, member_kind, member_name);
    match member_element_opt {
        Some(class_elt) => {
            if parent_class_elt.ce_origin == class_elt.ce_origin {
                // Case where the child's element comes from the parent being checked.
                // if the child class implements dynamic, all inherited methods should be dynamically callable
                check_inherited_member_is_dynamically_callable(
                    env,
                    (class_pos, class_),
                    parent_class,
                    (member_kind, member_name, parent_class_elt),
                );
                for err in errors_if_not_overriden {
                    typing_error_utils::add_typing_error(err.force(), env)
                }

                let is_final = cls::final_(class_);
                let missing_members = if (ast_defs::is_c_concrete(cls::kind(class_)) || is_final)
                    && typing_defs_flags::class_elt::is_abstract(class_elt.ce_flags)
                {
                    vec![MissingMemberInfo {
                        member_name: member_name.to_string(),
                        parent_class_elt: parent_class_elt.clone(),
                        parent_pos: parent_pos.clone(),
                        member_kind,
                        is_override: true,
                    }]
                } else {
                    vec![]
                };

                missing_members
            } else {
                // We can skip this check if the class elements have the same origin, as we are
                // essentially comparing a method against itself
                check_override(
                    env,
                    true,
                    member_name,
                    member_kind,
                    class_,
                    parent_class,
                    parent_type,
                    parent_pos,
                    class_pos,
                    &class_elt,
                    parent_class_elt,
                    on_error((parent_pos.clone(), cls::name(parent_class))),
                );
                vec![]
            }
        }
        None => {
            // The only case when a member belongs to a parent but not the child is if the parent is an
            // interface and the child is a concrete class. Otherwise, the member would have been inherited.
            // In this case, this is an error because the concrete class fails to implement the parent interface.
            vec![MissingMemberInfo {
                member_name: member_name.to_string(),
                parent_class_elt: parent_class_elt.clone(),
                parent_pos: parent_pos.clone(),
                member_kind,
                is_override: false,
            }]
        }
    }
}

/// [check_static_member_intersection class_ class_pos parent_members] looks
/// for intersections in the static and instance members of [class_] (at
/// [class_pos]) via a precomputed list of class members in [parent_members].
/// We emit an error if there exists a class member that is defined as both
/// static, and instance, as it will unconditionally fatal in HHVM. For
/// example, the following code will fatal:
///
/// ```text
///   abstract class Foo { public int $bar; }
///   trait Baz { public static int $bar; }
///   final class Quxx extends Foo { use Baz; }
/// ```
fn check_static_member_intersection(
    env: &Env,
    class_: &cls::T,
    class_pos: &Pos,
    parent_members: &ParentMembers,
) {
    let check_single_member =
        |member_kind: MemberKind,
         name: &str,
         parent_members: &ParentClassEltSet,
         acc: &mut Vec<(String, ClassElt, ClassElt)>| {
            let name = match member_kind {
                MemberKind::Property => name.strip_prefix('$').unwrap_or(name).to_string(),
                MemberKind::StaticProperty => format!("${}", name),
                MemberKind::StaticMethod | MemberKind::Method | MemberKind::Constructor { .. } => {
                    name.to_string()
                }
            };
            match get_member(member_kind, class_, &name) {
                None => {}
                Some(class_elt) => {
                    // `ParentClassEltSet.choose` is `Set.min_elt`.
                    let chosen = parent_members
                        .iter()
                        .next()
                        .unwrap_or_else(|| panic!("Not_found"));
                    acc.push((name, chosen.class_elt.clone(), class_elt))
                }
            }
        };
    let gather_violations = |parent_member_kind: MemberKind, child_member_kind: MemberKind| {
        // `MemberNameMap.fold` conses onto its accumulator in increasing order of
        // the names: the list is in decreasing order.
        let mut acc = vec![];
        if let Some(map) = parent_members.get(&parent_member_kind) {
            for (name, parent_members) in map {
                check_single_member(child_member_kind, name, parent_members, &mut acc)
            }
        }
        acc.reverse();
        acc
    };
    let on_error = |member_name: String,
                    static_elem: &ClassElt,
                    instance_elem: &ClassElt,
                    kind: primary::StaticInstanceIntersectionKind| {
        let instance_pos = {
            let p = instance_elem.ce_pos.clone();
            typing_error::Lazy::new(move || PosOrDecl::clone(&p))
        };
        let static_pos = {
            let p = static_elem.ce_pos.clone();
            typing_error::Lazy::new(move || PosOrDecl::clone(&p))
        };
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Static_instance_intersection {
                class_pos: class_pos.clone(),
                instance_pos,
                static_pos,
                member_name,
                kind,
            }),
            env,
        )
    };
    let find_intersections =
        |static_member_kind: MemberKind,
         instance_member_kind: MemberKind,
         kind: primary::StaticInstanceIntersectionKind| {
            let violations = gather_violations(static_member_kind, instance_member_kind);
            for (member_name, static_elem, instance_elem) in violations {
                on_error(member_name, &static_elem, &instance_elem, kind)
            }
            let violations = gather_violations(instance_member_kind, static_member_kind);
            for (member_name, instance_elem, static_elem) in violations {
                on_error(member_name, &static_elem, &instance_elem, kind)
            }
        };
    find_intersections(
        MemberKind::StaticMethod,
        MemberKind::Method,
        primary::MethOrProp::meth,
    );
    find_intersections(
        MemberKind::StaticProperty,
        MemberKind::Property,
        primary::MethOrProp::prop,
    );
}

fn check_members_from_all_parents(
    env: &mut Env,
    (class_pos, class_): (&Pos, &cls::T),
    on_error: OnError<'_>,
    parent_members: &ParentMembers,
) {
    let mut missing_members: Vec<MissingMemberInfo> = vec![];
    for (member_kind, member_map) in parent_members {
        for (member_name, class_elts) in member_map {
            worker_cancel::raise_if_stop_requested();
            for elt in class_elts {
                let missing = check_class_against_parent_class_elt(
                    on_error,
                    (class_pos, class_),
                    *member_kind,
                    member_name,
                    elt,
                    env,
                );
                missing_members.extend(missing);
            }
        }
    }

    members_missing_error(env, class_pos, class_, missing_members);
    check_static_member_intersection(env, class_, class_pos, parent_members)
}

fn make_all_members(parent_class: &cls::T) -> Vec<(MemberKind, Vec<(String, ClassElt)>)> {
    let wrap_constructor = |(ctor, kind): (Option<ClassElt>, ConsistentKind)| {
        (
            MemberKind::Constructor {
                is_consistent: constructor_is_consistent(kind),
            },
            ctor.map(|x| (sn::members::__CONSTRUCT.to_string(), x))
                .into_iter()
                .collect(),
        )
    };
    // OCaml evaluates the elements of a list literal from right to left.
    let construct = wrap_constructor(cls::construct(parent_class));
    let smethods = (MemberKind::StaticMethod, cls::smethods(parent_class));
    let methods = (MemberKind::Method, cls::methods(parent_class));
    let sprops = (MemberKind::StaticProperty, cls::sprops(parent_class));
    let props = (MemberKind::Property, cls::props(parent_class));
    vec![props, sprops, methods, smethods, construct]
}

/// The phantom class element that represents the default constructor:
/// `public function __construct()[] {}`
///
/// It isn't added to the tc_construct only because that's used to
/// determine whether a child class needs to call parent::__construct
fn default_constructor_ce(class_: &cls::T) -> ClassElt {
    let (pos, name) = (cls::pos(class_), cls::name(class_));
    let r = R::witness_from_decl(BPos::from(pos.clone()));
    // reason doesn't get used in, e.g. arity checks
    let ft = DeclFunType {
        tparams: Box::new([]),
        where_constraints: Box::new([]),
        params: Box::new([]),
        // `MakeType.mixed r`
        implicit_params: FunImplicitParams {
            capability: Capability::CapTy(DeclTy::new(
                r.clone(),
                DTy_::Toption(DeclTy::new(r.clone(), DTy_::Tnonnull)),
            )),
        },
        // `MakeType.void r`
        ret: DeclTy::void(r.clone()),
        flags: FunTypeFlags::empty(),
        instantiated: true,
    };
    ClassElt {
        ce_visibility: CeVisibility::Vpublic,
        ce_type: cls::lazy(move || DeclTy::new(r, DTy_::Tfun(Box::new(ft)))),
        ce_origin: name,
        ce_deprecated: None,
        ce_pos: cls::lazy(move || pos),
        ce_overlapping_tparams: None,
        ce_package_requirement: Some(PackageRequirement::RPNormal),
        ce_sealed_allowlist: None,
        ce_flags: make_ce_flags(
            None,  // xhp_attr
            false, // abstract
            false, // final
            false, // superfluous_override
            false, // lsb
            true,  // synthesized
            false, // const
            false, // lateinit
            false, // dynamicallycallable
            false, // readonly_prop_or_needs_concrete
            false, // support_dynamic_type
            false, // needs_init
            false, // safe_global_variable
            false, // no_auto_likes
            false, // tests_bypass_visibility
        ),
    }
}

/// When an interface defines a constructor, we check that they are compatible
fn check_constructors(
    parent_pos: &Pos,
    env: &mut Env,
    (parent_class, parent_type): (&cls::T, &DeclTy),
    class_: &cls::T,
    class_pos: &Pos,
    psubst: &crate::decl_subst::DeclSubst,
    on_error: reasons_callback::T,
) {
    let parent_is_interface = ast_defs::is_c_interface(cls::kind(parent_class));
    let parent_is_consistent = constructor_is_consistent(cls::construct(parent_class).1);
    if parent_is_interface || parent_is_consistent {
        // OCaml evaluates the components of the tuple from right to left.
        let cstr_opt = cls::construct(class_).0;
        let parent_cstr_opt = cls::construct(parent_class).0;
        match (parent_cstr_opt, cstr_opt) {
            (Some(parent_cstr), _) if get_ce_synthesized(&parent_cstr) => {}
            (Some(parent_cstr), None) => {
                let pos = ce_pos(&parent_cstr);
                typing_error_utils::add_typing_error(
                    &typing_error::apply_reasons(
                        secondary::T::Missing_constructor(pos),
                        on_error.clone(),
                    ),
                    env,
                )
            }
            (_, Some(cstr)) if get_ce_superfluous_override(&cstr) => {
                // <<__UNSAFE_Construct>>
            }
            (opt_parent_cstr, Some(cstr)) if opt_parent_cstr.is_some() || parent_is_consistent => {
                let parent_cstr = match opt_parent_cstr {
                    Some(parent_cstr) => parent_cstr,
                    None => default_constructor_ce(parent_class),
                };
                if parent_cstr.ce_origin != cstr.ce_origin {
                    let parent_cstr = inst::instantiate_ce(psubst, &parent_cstr);
                    check_override(
                        env,
                        false,
                        sn::members::__CONSTRUCT,
                        MemberKind::Constructor {
                            is_consistent: true,
                        },
                        class_,
                        parent_class,
                        parent_type,
                        parent_pos,
                        class_pos,
                        &cstr,
                        &parent_cstr,
                        on_error.clone(),
                    )
                }
            }
            (_, _) => {}
        }
    }
    // OCaml evaluates the components of the tuple from right to left.
    let cstr_opt = cls::construct(class_).0;
    let parent_cstr_opt = cls::construct(parent_class).0;
    match (parent_cstr_opt, cstr_opt) {
        (Some(parent_cstr), _) if get_ce_synthesized(&parent_cstr) => {}
        (Some(parent_cstr), Some(child_cstr)) => {
            check_override_final_method(env, &parent_cstr, &child_cstr, &on_error)
        }
        (_, _) => {}
    }
}

/// Checks if a child is compatible with the type constant of its parent.
/// This requires the child's constraint and assigned type to be a subtype of
/// the parent's type constant.
fn tconst_subsumption(
    env: &mut Env,
    class_name: &str,
    parent_typeconst: &TypeconstType,
    parent_tconst_enforceable: (PosOrDecl, bool),
    child_typeconst: &TypeconstType,
    on_error: reasons_callback::T,
) {
    use ty::decl::AbstractTypeconst;
    use ty::decl::ConcreteTypeconst;
    use ty::decl::Typeconst::TCAbstract;
    use ty::decl::Typeconst::TCConcrete;

    let pos = decl_pos(child_typeconst.name.pos());
    let name = child_typeconst.name.id_ref().as_str();
    let parent_pos = decl_pos(parent_typeconst.name.pos());
    match (&parent_typeconst.kind, &child_typeconst.kind) {
        (
            TCAbstract(AbstractTypeconst {
                default: Some(_), ..
            }),
            TCAbstract(AbstractTypeconst { default: None, .. }),
        ) => typing_error_utils::add_typing_error(
            &typing_error::assert_in_current_decl(
                secondary::T::Override_no_default_typeconst { pos, parent_pos },
                typing_env::get_current_decl_and_file(env),
            ),
            env,
        ),
        (TCConcrete(_), TCAbstract(_)) => {
            // It is valid for abstract class to extend a concrete class, but it cannot
            // redefine already concrete members as abstract.
            // See typecheck/tconst/subsume_tconst5.php test case for example.
            typing_error_utils::add_typing_error(
                &typing_error::apply_reasons(
                    secondary::T::Abstract_concrete_override {
                        pos,
                        parent_pos,
                        kind: secondary::AbstractConcreteOverrideKind::typeconst,
                    },
                    on_error,
                ),
                env,
            )
        }
        _ => {
            let inherited = child_typeconst.origin.as_str() != class_name;
            // If the class element is inherited from a parent class, we must
            // wrap any error with
            //   "Class [class_name] does not correctly implement all required members"
            // and the primary position should be on [class_name]
            let on_error = if inherited {
                on_error
            } else {
                typing_env::unify_error_assert_primary_pos_in_current_decl(env)
            };

            // Check that the child's constraint is compatible with the parent. If the
            // parent has a constraint then the child must also have a constraint if it
            // is abstract.
            //
            // Check that the child's assigned type satisifies parent constraint
            let default = {
                // `MakeType.generic (Reason.tconst_no_cstr child_typeconst.ttc_name) name`
                let tconst_pos = child_typeconst.name.pos().clone();
                let r = R::mk(|| {
                    ReasonImpl::FromWitnessDecl(WitnessDecl::TconstNoCstr((
                        tconst_pos,
                        Symbol::new(name),
                    )))
                });
                DeclTy::generic(r, TypeName::new(name))
            };
            let is_coeffect = parent_typeconst.is_ctx || child_typeconst.is_ctx;
            let check_cstrs = |reason: Ureason,
                               env: &mut Env,
                               sub: Option<&DeclTy>,
                               super_: Option<&DeclTy>|
             -> Option<typing_error::T> {
                match (sub, super_) {
                    (Some(sub), Some(super_)) => typing_ops::sub_type_decl(
                        Some(is_coeffect),
                        Some(false),
                        on_error.clone(),
                        pos.clone(),
                        reason,
                        env,
                        sub,
                        super_,
                    ),
                    _ => None,
                }
            };
            // TODO(T88552052) This can be greatly simplified by adopting the { A = S..T } representation
            // from DOT and implementing the Typ-<:-Typ rule, Amin 2016
            match &parent_typeconst.kind {
                TCAbstract(AbstractTypeconst {
                    as_constraint: p_as_opt,
                    super_constraint: p_super_opt,
                    ..
                }) => match &child_typeconst.kind {
                    TCAbstract(AbstractTypeconst {
                        as_constraint: c_as_opt,
                        super_constraint: c_super_opt,
                        ..
                    }) => {
                        // TODO(T88552052) this transformation can be done with mixed and nothing
                        let c_as_opt = Some(c_as_opt.as_ref().unwrap_or(&default));
                        let c_super_opt = Some(c_super_opt.as_ref().unwrap_or(&default));

                        let e1 = check_cstrs(
                            Ureason::URsubsumeTconstCstr,
                            env,
                            c_as_opt,
                            p_as_opt.as_ref(),
                        );
                        let e2 = check_cstrs(
                            Ureason::URsubsumeTconstCstr,
                            env,
                            p_super_opt.as_ref(),
                            c_super_opt,
                        );
                        let ty_err_opt = merge_errors(e1, e2);
                        add_typing_error_opt(env, ty_err_opt)
                    }
                    TCConcrete(ConcreteTypeconst { ty: c_t }) => {
                        let e1 = check_cstrs(
                            Ureason::URtypeconstCstr,
                            env,
                            Some(c_t),
                            p_as_opt.as_ref(),
                        );
                        let e2 = check_cstrs(
                            Ureason::URtypeconstCstr,
                            env,
                            p_super_opt.as_ref(),
                            Some(c_t),
                        );
                        let ty_err_opt = merge_errors(e1, e2);
                        add_typing_error_opt(env, ty_err_opt)
                    }
                },
                TCConcrete(_) => match &child_typeconst.kind {
                    TCConcrete(_) => {
                        if typing_env::get_tcopt(env).tco_typeconst_concrete_concrete_error
                            && !inherited
                        {
                            typing_error_utils::add_typing_error(
                                &typing_error::assert_in_current_decl(
                                    secondary::T::Typeconst_concrete_concrete_override {
                                        pos: pos.clone(),
                                        parent_pos: parent_pos.clone(),
                                    },
                                    typing_env::get_current_decl_and_file(env),
                                ),
                                env,
                            )
                        }
                    }
                    _ => {}
                },
            }

            match (&child_typeconst.kind, parent_tconst_enforceable) {
                (
                    TCAbstract(AbstractTypeconst {
                        default: Some(ty), ..
                    }),
                    (tp_pos, true),
                )
                | (TCConcrete(ConcreteTypeconst { ty }), (tp_pos, true)) => {
                    let env: &Env = env;
                    let emit_error = |pos: Pos, ty_info| {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::Invalid_enforceable_type {
                                pos,
                                ty_info,
                                kind: primary::InvalidEnforceableTypeKind::constant,
                                tp_pos: tp_pos.clone(),
                                tp_name: name.to_string(),
                            }),
                            env,
                        )
                    };
                    typing_enforceable_hint::validate_type(
                        env,
                        pos_or_decl::unsafe_to_raw_pos(decl_pos(child_typeconst.name.pos())),
                        ty,
                        emit_error,
                    )
                }
                _ => {
                    if !inherited {
                        match &parent_typeconst.reifiable {
                            None => {}
                            Some(pos) => typing_const_reifiable::check_reifiable(
                                env,
                                child_typeconst,
                                decl_pos(pos),
                            ),
                        }
                    }
                }
            }

            // If the parent cannot be overridden, we unify the types otherwise we ensure
            // the child's assigned type is compatible with the parent's
            //
            // TODO(T88552052) restrict concrete typeconst overriding
            let parent_is_final = match &parent_typeconst.kind {
                TCConcrete(_) => true,
                TCAbstract(_) => false,
            };
            let check = |env: &mut Env, x: &DeclTy, y: &DeclTy| -> Option<typing_error::T> {
                if parent_is_final {
                    typing_ops::unify_decl(
                        pos.clone(),
                        Ureason::URsubsumeTconstAssign,
                        env,
                        on_error.clone(),
                        x,
                        y,
                    )
                } else {
                    typing_ops::sub_type_decl(
                        None,
                        None,
                        on_error.clone(),
                        pos.clone(),
                        Ureason::URsubsumeTconstAssign,
                        env,
                        y,
                        x,
                    )
                }
            };
            // TODO(T88552052) this fetching of types is a temporary hack; this whole check will be eliminated
            #[allow(non_snake_case)]
            let opt_type__LEGACY = |t: &TypeconstType| -> Option<DeclTy> {
                match &t.kind {
                    TCConcrete(ConcreteTypeconst { ty: t }) => Some(t.clone()),
                    TCAbstract(_) => None,
                }
            };
            let ty_err_opt = match (
                opt_type__LEGACY(parent_typeconst),
                opt_type__LEGACY(child_typeconst),
            ) {
                (Some(x), Some(y)) => check(env, &x, &y),
                _ => None,
            };
            add_typing_error_opt(env, ty_err_opt)
        }
    }
}

fn check_abstract_typeconst_in_concrete_class(
    env: &Env,
    (class_pos, class_): (&Pos, &cls::T),
    tconst: &TypeconstType,
) {
    let is_final = cls::final_(class_);
    if ast_defs::is_c_concrete(cls::kind(class_)) || is_final {
        match &tconst.kind {
            ty::decl::Typeconst::TCAbstract(_) => {
                let typeconst_pos = decl_pos(tconst.name.pos());
                let typeconst_name = tconst.name.id_ref().as_str().to_string();
                let trace =
                    describe_route_lazily(env, cls::name(class_), tconst.origin.to_string());
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Implement_abstract {
                        is_final,
                        pos: class_pos.clone(),
                        decl_pos: typeconst_pos,
                        trace,
                        kind: primary::ImplementAbstractKind::ty_const,
                        name: typeconst_name,
                        quickfixes: vec![],
                    }),
                    env,
                )
            }
            ty::decl::Typeconst::TCConcrete(_) => {}
        }
    }
}

fn check_typeconst_override(
    env: &mut Env,
    implements: &[(PosOrDecl, cls::T)],
    (class_pos, class_): (&Pos, &cls::T),
    parent_tconst: &TypeconstType,
    tconst: &TypeconstType,
    parent_class: &cls::T,
    on_error: reasons_callback::T,
) {
    use ty::decl::AbstractTypeconst;
    use ty::decl::Typeconst::TCAbstract;
    use ty::decl::Typeconst::TCConcrete;

    if parent_tconst.origin.as_str() == tconst.origin.as_str() {
        check_abstract_typeconst_in_concrete_class(env, (class_pos, class_), tconst)
    } else {
        // If the class element is defined in the class that we're checking, then
        // don't wrap with the extra
        // "Class ... does not correctly implement all required members" message
        let on_error = if tconst.origin.as_str() == cls::name(class_) {
            typing_env::unify_error_assert_primary_pos_in_current_decl(env)
        } else {
            on_error
        };
        let tconst_check =
            |env: &mut Env, parent_tconst: &TypeconstType, tconst: &TypeconstType| {
                let parent_tconst_enforceable =
                    // We know that this typeconst exists in the parent (else we would not
                    // have successfully looked up [parent_tconst]), so we know that
                    // [get_typeconst_enforceability] will return Some.
                    cls::get_typeconst_enforceability(parent_class, tconst.name.id_ref().as_str())
                        .unwrap_or_else(|| panic!("Option.value_exn: None"));
                tconst_subsumption(
                    env,
                    &cls::name(class_),
                    parent_tconst,
                    parent_tconst_enforceable,
                    tconst,
                    on_error.clone(),
                )
            };
        check_ambiguous_inheritance(
            tconst_check,
            parent_tconst,
            tconst,
            decl_pos(tconst.name.pos()),
            class_,
            tconst.origin.as_str(),
            &on_error,
            env,
        );
        let (pos, name) = (decl_pos(tconst.name.pos()), tconst.name.id_ref().as_str());
        let parent_pos = decl_pos(parent_tconst.name.pos());
        // Temporarily skip checks on context constants
        //
        // TODO(T89366955) elimninate this check
        let is_context_constant = match (&parent_tconst.kind, &tconst.kind) {
            (
                TCAbstract(AbstractTypeconst {
                    default: Some(hint1),
                    ..
                }),
                TCAbstract(AbstractTypeconst {
                    default: Some(hint2),
                    ..
                }),
            ) => match (hint1.node_ref(), hint2.node_ref()) {
                (DTy_::Tintersection(_), _) | (_, DTy_::Tintersection(_)) => true,
                _ => false,
            },
            (
                TCAbstract(AbstractTypeconst {
                    default: Some(hint),
                    ..
                }),
                _,
            )
            | (
                _,
                TCAbstract(AbstractTypeconst {
                    default: Some(hint),
                    ..
                }),
            ) => match hint.node_ref() {
                DTy_::Tintersection(_) => true,
                _ => false,
            },
            _ => false,
        };
        match (&parent_tconst.kind, &tconst.kind) {
            (TCConcrete(_), TCConcrete(_))
            | (
                TCAbstract(AbstractTypeconst {
                    default: Some(_), ..
                }),
                TCAbstract(AbstractTypeconst {
                    default: Some(_), ..
                }),
            ) => {
                if !is_context_constant
                    && !tconst.is_synthesized
                    && !parent_tconst.is_synthesized
                    && constant_conflict_with_declared_interface_or_trait(
                        Some(false),
                        env,
                        implements,
                        parent_class,
                        class_,
                        parent_tconst.origin.as_str(),
                        tconst.origin.as_str(),
                        name,
                    )
                {
                    let child_is_abstract = is_typeconst_type_abstract(tconst);
                    let err = secondary::T::Interface_typeconst_multiple_defs {
                        pos,
                        name: name.to_string(),
                        is_abstract: child_is_abstract,
                        origin: tconst.origin.to_string(),
                        parent_pos,
                        parent_origin: parent_tconst.origin.to_string(),
                    };
                    typing_error_utils::add_typing_error(
                        &typing_error::apply_reasons(err, on_error),
                        env,
                    )
                }
            }
            _ => {}
        }
    }
}

/// Use the [on_error] callback if we need to wrap the basic error with a
///   "Class ... does not correctly implement all required members"
/// message pointing at the class being checked.
fn check_class_extends_parent_constructors(
    parent_pos: &Pos,
    env: &mut Env,
    parent_class: &ParentInfo,
    class_: &cls::T,
    class_pos: &Pos,
    on_error: reasons_callback::T,
) {
    let (_, parent_type, parent_tparaml, parent_class) = parent_class;
    let psubst = inst::make_subst(&cls::tparams(parent_class), parent_tparaml);
    check_constructors(
        parent_pos,
        env,
        (parent_class, parent_type),
        class_,
        class_pos,
        &psubst,
        on_error,
    )
}

/// Eliminate all synthesized members (those from requirements) plus all
/// private members unless they're from traits.
fn filter_privates_and_synthethized<A>(
    is_trait: bool,
    members: Vec<(A, ClassElt)>,
) -> Vec<(A, ClassElt)> {
    let eliminate = |class_elt: &ClassElt| {
        get_ce_synthesized(class_elt) || (!is_trait && class_elt_is_private_not_lsb(class_elt))
    };
    let keep = |class_elt: &ClassElt| !eliminate(class_elt);
    members
        .into_iter()
        .filter(|(_name, class_elt)| keep(class_elt))
        .collect()
}

fn make_parent_member_map(parent: &ParentInfo) -> (Rc<Parent>, MemberMap) {
    let ((parent_pos, _parent_name), parent_type, parent_tparaml, parent_class) = parent;
    let psubst = inst::make_subst(&cls::tparams(parent_class), parent_tparaml);
    // `MemberKindMap.of_list`: a later binding replaces an earlier one.
    let mut of_list: BTreeMap<MemberKind, Vec<(String, ClassElt)>> = BTreeMap::new();
    for (member_kind, members) in make_all_members(parent_class) {
        of_list.insert(member_kind, members);
    }
    let is_trait = ast_defs::is_c_trait(cls::kind(parent_class));
    let member_map: MemberMap = (of_list.into_iter())
        .map(|(member_kind, members)| {
            let members = filter_privates_and_synthethized(is_trait, members);
            // `S_map.of_list`
            let mut map: BTreeMap<String, ClassElt> = BTreeMap::new();
            for (name, elt) in members {
                map.insert(name, elt);
            }
            let map = (map.into_iter())
                .map(|(name, elt)| {
                    let elt = inst::instantiate_ce(&psubst, &elt);
                    (name, elt)
                })
                .collect();
            (member_kind, map)
        })
        .collect();
    (
        Rc::new(Parent {
            parent_pos: parent_pos.clone(),
            parent_class: parent_class.clone(),
            parent_type: parent_type.clone(),
        }),
        member_map,
    )
}

/// Check for multiple kinds of forbidden hierarchy diamonds involving traits:
/// - Any kind of diamond involving final methods is forbidden unless the
///   class has __EnableMethodTraitDiamond and the diamond involves only
///   traits.
/// - Diamonds involving only traits, with the trait at the top of the diamond
///   containing at least one method, are only allowed if the classish has
///   __EnableMethodTraitDiamond attribute.
/// - Any kind of diamond involving properties with a generic type instantiated
///   differently along the two paths of the diamond is forbidden.
///
/// [check_trait_diamonds env ~allow_diamonds ~class_name ~member_name elt elts
/// member_kind] considers [elt] and [elts]. Members from [elt] union [elts]
/// have the same name [member_name]. [elts] represents all the members with
/// this member name that we've seen so far from the parents we are merging.
/// In this function, we'll detect diamonds by checking if [elt] has the same
/// origin as one of the elements in [elts] and produce an error if that
/// diamond is forbidden.
fn check_trait_diamonds(
    env: &Env,
    allow_diamonds: bool,
    class_name: &Id,
    member_name: &str,
    parent_class_elt: (ClassElt, Rc<Parent>),
    elts: ParentClassEltSet,
    member_kind: MemberKind,
) -> (
    (parent_class_elt::T, ParentClassEltSet),
    Option<((String, String), typing_error::T)>,
) {
    let (class_elt, parent) = &parent_class_elt;
    let Parent {
        parent_pos,
        parent_class,
        parent_type: _,
    } = &**parent;
    let default_parent_class_elt = || parent_class_elt::make(None, parent_class_elt.clone());
    if
    // We'll check some of those conditions later but check them first
    // here to avoid an expensive set lookup if we can.
    // Note that we never check that the origin of class_elt is a trait, because that
    // would require a decl heap lookup which is expensive. But that should follow from the
    // following facts: 1) the parent from which class_elt comes from is a trait - 2) the member
    // is not synthetic, i.e. not from a `require extends`, since we've filtered those out earlier -
    // 3) the member is not abstract, so not from a `require implements` either.
    ast_defs::is_c_trait(cls::kind(parent_class))
        && !get_ce_abstract(class_elt)
        && (member_kind::is_method(member_kind) && (!allow_diamonds || get_ce_final(class_elt))
            || member_kind::is_property(member_kind))
    {
        // Let's search for a diamond.
        // We want to find an existing element with the same origin,
        // i.o.w, find a diamond.
        // Set.find_first_opt only works for 'monotonic' `f` which is
        // not the case for the equality test, and Set.find_opt
        // uses the polymorphic equaliy: we only want to test for origin.
        // Set doesn't provide a `find with condition` so we do an iteration
        // and bail at the first occurrence we spot
        //
        // This works in a deterministic way because the set we are working
        // with has the invariant that each element have a unique origin.
        let candidate = (elts.iter())
            .find(
                |parent_class_elt::T {
                     class_elt: prev_class_elt,
                     ..
                 }| class_elt.ce_origin == prev_class_elt.ce_origin,
            )
            .cloned();
        match candidate {
            None => ((default_parent_class_elt(), elts), None),
            Some(prev_parent_class_elt) => {
                let parent_class_elt::T {
                    class_elt: prev_class_elt,
                    parent: prev_parent,
                    errors_if_not_overriden: err,
                } = &prev_parent_class_elt;
                let prev_parent = &prev_parent.parent_class;
                if member_kind::is_method(member_kind)
                    && get_ce_final(class_elt)
                    && (!allow_diamonds || ast_defs::is_c_class(cls::kind(prev_parent)))
                {
                    let error =
                        // We want only one such error per diamond (instead of one per diamond per final method),
                        // so let's return the diamond corners and the error and let the caller aggregate per diamond.
                        Some((
                            (cls::name(prev_parent), class_elt.ce_origin.clone()),
                            trait_reuse_check::trait_reuse_with_final_method_error(
                                env,
                                class_elt,
                                class_name.1.clone(),
                                prev_parent,
                                (parent_pos.clone(), parent_class),
                            ),
                        ));
                    // Let's keep the previous parent class element, whose parent is a class,
                    // to detect additional such errors if there are more diamonds.
                    ((prev_parent_class_elt, elts), error)
                } else if member_kind::is_method(member_kind)
                    && !allow_diamonds
                    && ast_defs::is_c_trait(cls::kind(prev_parent))
                {
                    let method_import_error = {
                        let env = env.clone();
                        let class_name = class_name.clone();
                        let member_name = member_name.to_string();
                        let class_elt = class_elt.clone();
                        let prev_parent = prev_parent.clone();
                        let parent_class = parent_class.clone();
                        typing_error::Lazy::new(move || {
                            let Id(class_name_pos, class_name) = class_name;
                            trait_reuse_check::method_import_via_diamond_error(
                                &env,
                                (class_name_pos, class_name),
                                (member_name, &class_elt),
                                &prev_parent,
                                &parent_class,
                            )
                        })
                    };
                    let mut errors_if_not_overriden = vec![method_import_error];
                    errors_if_not_overriden.extend(err.iter().cloned());
                    let new_parent_class_elt = parent_class_elt::make(
                        Some(errors_if_not_overriden),
                        parent_class_elt.clone(),
                    );
                    let mut elts = elts;
                    elts.remove(&default_parent_class_elt());
                    ((new_parent_class_elt, elts), None)
                } else if member_kind::is_property(member_kind) {
                    if allow_diamonds {
                        // traits with properties cannot be inherited via multiple paths
                        // if the base class has the <<__EnableMethodTraitDiamond>> attribute
                        trait_reuse_check::property_import_via_diamond_error(
                            false,
                            env,
                            (class_name.0.clone(), class_name.1.clone()),
                            (member_name.to_string(), class_elt),
                            prev_parent,
                            parent_class,
                        );
                        ((default_parent_class_elt(), elts), None)
                    } else if compare_decl_ty(None, &class_elt.ce_type, &prev_class_elt.ce_type)
                        != Ordering::Equal
                    {
                        // it is unsound to use a trait that defines a generic property
                        // at different types along multiple paths
                        trait_reuse_check::property_import_via_diamond_error(
                            true,
                            env,
                            (class_name.0.clone(), class_name.1.clone()),
                            (member_name.to_string(), class_elt),
                            prev_parent,
                            parent_class,
                        );
                        ((default_parent_class_elt(), elts), None)
                    } else {
                        ((default_parent_class_elt(), elts), None)
                    }
                } else {
                    // When we have a diamond between a class parent and a used trait
                    // (e.g. D extends C { use TraitA; use TraitB; } where C also uses
                    // TraitA), we need to keep the trait's entry rather than the class
                    // parent's entry.
                    let elts = if ast_defs::is_c_class(cls::kind(prev_parent)) {
                        let mut elts = elts;
                        elts.remove(&default_parent_class_elt());
                        elts
                    } else {
                        elts
                    };
                    ((default_parent_class_elt(), elts), None)
                }
            }
        }
    } else {
        ((default_parent_class_elt(), elts), None)
    }
}

/// Selects the minimum classes out of a list using the partial ordering
/// provided by the subtyping relationship.
fn minimum_classes(env: &Env, classes: Vec<String>) -> Vec<String> {
    let is_sub_type = |x: &str, y: &str| {
        decl_entry::to_option(decl_provider::get_class(None, &typing_env::get_ctx(env), x))
            .and_then(|x| cls::get_ancestor(&x, y))
            .is_some()
    };
    // The lists are OCaml lists: element 0 is the head.
    let add_min = |is_lower: &dyn Fn(&str, &str) -> bool, x: String, mins: Vec<String>| {
        let mut mins: &[String] = &mins;
        let mut result: Vec<String> = vec![];
        loop {
            match mins {
                [] => {
                    // `x :: result`
                    result.insert(0, x);
                    return result;
                }
                [y, ys @ ..] => {
                    if is_lower(&x, y) {
                        mins = ys;
                    } else if is_lower(y, &x) {
                        // `List.rev_append result mins`
                        result.reverse();
                        result.extend(mins.iter().cloned());
                        return result;
                    } else {
                        result.insert(0, y.clone());
                        mins = ys;
                    }
                }
            }
        }
    };
    let mut minimum_classes: Vec<String> = vec![];
    for class_ in classes {
        minimum_classes = add_min(&is_sub_type, class_, minimum_classes);
    }
    minimum_classes
}

fn check_no_conflicting_inherited_concrete_constants(
    env: &Env,
    name: &str,
    constants: &ParentClassConstSet,
    class_pos: &Pos,
) {
    let definitions: Vec<&parent_class_const::T> = (constants.iter())
        .filter(
            |parent_class_const::T { class_const, .. }| match class_const.kind {
                ClassConstKind::CCConcrete => true,
                ClassConstKind::CCAbstract(_) => false,
            },
        )
        .collect();
    if definitions.len() > 1 {
        let err = primary::T::Constant_multiple_concrete_conflict {
            pos: class_pos.clone(),
            name: name.to_string(),
            definitions: (definitions.iter())
                .map(
                    |parent_class_const::T {
                         class_const,
                         parent,
                     }| {
                        let parent_name = cls::name(&parent.parent_class);
                        let via = if parent_name != class_const.origin.as_str() {
                            Some(utils::strip_ns(&parent_name).to_string())
                        } else {
                            None
                        };
                        (decl_pos(&class_const.pos), via)
                    },
                )
                .collect(),
        };
        typing_error_utils::add_typing_error(&typing_error::primary(err), env)
    }
}

/// When a class inherits a concrete type constant from two different points
/// in its hierarchy (e.g. a parent class and an interface) HHVM will fail to
/// load the class, and the flag -vEval.TraitConstantInterfaceBehavior=1
/// extends this behavior to traits. This function reports such cases,
/// pointing to the definitions of the constants and reporting which parent
/// brings them in, e.g. declared in an interface brought in via a trait use.
fn check_no_conflicting_inherited_concrete_typeconsts(
    env: &Env,
    name: &str,
    typeconsts: &ParentTypeConstSet,
    class_pos: &Pos,
) {
    let definitions: Vec<&parent_type_const::T> = (typeconsts.iter())
        .filter(
            |parent_type_const::T { typeconst, .. }| match &typeconst.kind {
                ty::decl::Typeconst::TCConcrete(_) => !typeconst.is_synthesized,
                ty::decl::Typeconst::TCAbstract(_) => false,
            },
        )
        .collect();
    if definitions.len() > 1 {
        let err = primary::T::Constant_multiple_concrete_conflict {
            pos: class_pos.clone(),
            name: name.to_string(),
            definitions: (definitions.iter())
                .map(|parent_type_const::T { typeconst, parent }| {
                    let parent_name = cls::name(&parent.parent_class);
                    let via = if parent_name != typeconst.origin.as_str() {
                        Some(utils::strip_ns(&parent_name).to_string())
                    } else {
                        None
                    };
                    (decl_pos(typeconst.name.pos()), via)
                })
                .collect(),
        };
        typing_error_utils::add_typing_error(&typing_error::primary(err), env)
    }
}

fn union_parent_constants(parents: &[ParentInfo]) -> BTreeMap<String, ParentClassConstSet> {
    let get_declared_consts = |((parent_pos, _), parent_type, parent_tparaml, parent_class): &ParentInfo|
     -> (Rc<Parent>, Vec<(String, ClassConst)>) {
        let psubst = inst::make_subst(&cls::tparams(parent_class), parent_tparaml);
        let consts = (cls::consts(parent_class).into_iter())
            .filter(|(_, cc)| !cc.is_synthesized)
            .map(|(name, cc)| {
                let cc = inst::instantiate_cc(&psubst, &cc);
                (name, cc)
            })
            .collect();
        (
            Rc::new(Parent {
                parent_pos: parent_pos.clone(),
                parent_class: parent_class.clone(),
                parent_type: parent_type.clone(),
            }),
            consts,
        )
    };
    let declared: Vec<(Rc<Parent>, Vec<(String, ClassConst)>)> =
        parents.iter().map(get_declared_consts).collect();
    let mut acc: BTreeMap<String, ParentClassConstSet> = BTreeMap::new();
    for (parent, consts) in declared {
        for (name, const_) in consts {
            let elt = parent_class_const::make(const_, Rc::clone(&parent));
            // `Set.add` keeps the element already there.
            acc.entry(name).or_default().insert(elt);
        }
    }
    acc
}

fn union_parent_typeconsts(parents: &[ParentInfo]) -> BTreeMap<String, ParentTypeConstSet> {
    let get_declared_consts = |((parent_pos, _), parent_type, parent_tparaml, parent_class): &ParentInfo|
     -> (Rc<Parent>, Vec<(String, TypeconstType)>) {
        let psubst = inst::make_subst(&cls::tparams(parent_class), parent_tparaml);
        let typeconsts = (cls::typeconsts(parent_class).into_iter())
            .map(|(name, tc)| {
                let tc = inst::instantiate_typeconst_type(&psubst, &tc);
                (name, tc)
            })
            .collect();
        (
            Rc::new(Parent {
                parent_pos: parent_pos.clone(),
                parent_class: parent_class.clone(),
                parent_type: parent_type.clone(),
            }),
            typeconsts,
        )
    };
    let declared: Vec<(Rc<Parent>, Vec<(String, TypeconstType)>)> =
        parents.iter().map(get_declared_consts).collect();
    let mut acc: BTreeMap<String, ParentTypeConstSet> = BTreeMap::new();
    for (parent, typeconsts) in declared {
        for (name, typeconst) in typeconsts {
            let elt = parent_type_const::make(typeconst, Rc::clone(&parent));
            // `Set.add` keeps the element already there.
            acc.entry(name).or_default().insert(elt);
        }
    }
    acc
}

fn check_class_extends_parents_constants(
    env: &mut Env,
    implements: &[(PosOrDecl, cls::T)],
    (class_ast, class_): (&nast::Class_, &cls::T),
    parents: &[ParentInfo],
    on_error: OnError<'_>,
) {
    let constants: BTreeMap<String, ParentClassConstSet> = union_parent_constants(parents);

    let class_pos = &class_ast.name.0;

    for (const_name, inherited) in &constants {
        check_no_conflicting_inherited_concrete_constants(env, const_name, inherited, class_pos);

        // TODO(vmladenov): factor individual checks out of check_const_override and remove [implements] parameter
        for parent_class_const::T {
            parent,
            class_const: parent_const,
        } in inherited
        {
            let Parent {
                parent_pos,
                parent_class,
                parent_type: _,
            } = &**parent;
            match cls::get_const(class_, const_name) {
                Some(const_) => {
                    // skip checks for typeconst derived class constants
                    match cls::get_typeconst(class_, const_name) {
                        None => check_const_override(
                            env,
                            implements,
                            const_name,
                            parent_class,
                            (class_pos, class_),
                            parent_const,
                            &const_,
                            on_error((parent_pos.clone(), cls::name(parent_class))),
                        ),
                        Some(_) => {}
                    }
                }
                None => {
                    let err = typing_error::primary(primary::T::Member_not_implemented {
                        pos: parent_pos.clone(),
                        member_name: const_name.clone(),
                        decl_pos: decl_pos(&parent_const.pos),
                        quickfixes: vec![],
                    });
                    typing_error_utils::add_typing_error(&err, env)
                }
            }
        }
    }
}

fn check_class_extends_parents_typeconsts(
    env: &mut Env,
    implements: &[(PosOrDecl, cls::T)],
    (class_ast, class_): (&nast::Class_, &cls::T),
    parents: &[ParentInfo],
    on_error: OnError<'_>,
) {
    let typeconsts: BTreeMap<String, ParentTypeConstSet> = union_parent_typeconsts(parents);
    let class_pos = &class_ast.name.0;

    for (tconst_name, inherited) in &typeconsts {
        check_no_conflicting_inherited_concrete_typeconsts(env, tconst_name, inherited, class_pos);

        for parent_type_const::T {
            parent,
            typeconst: parent_tconst,
        } in inherited
        {
            let Parent {
                parent_pos,
                parent_class,
                parent_type: _,
            } = &**parent;
            // If class_ is a trait that has a require class C constraint, and C provides a concrete definition
            // for the type constant, and the parent definition is abstract, then compare the parent type constant
            // against the type constant defined in the required class.
            // Otherwise compare it against the type constant defined in class_, if any.
            // However, if the parent definition is a concrete type constant, then we can skip checking type constants
            // inherited via require class constants, as these must be concrete and a conflict check will be
            // performed on the class itself
            let is_parent_tconst_abstract = is_typeconst_type_abstract(parent_tconst);
            let class_tconst_opt = {
                let tconst_element = cls::get_typeconst(class_, tconst_name);
                if ast_defs::is_c_trait(cls::kind(class_)) && is_parent_tconst_abstract {
                    tconst_element.map(|tconst_element| {
                        if tconst_element.origin.as_str() == cls::name(class_) {
                            tconst_element
                        } else {
                            let tconst_element_in_req_class =
                                (cls::all_ancestor_req_class_requirements(class_).iter()).find_map(
                                    |req| {
                                        let (_, cn, _) = typing_utils::unwrap_class_type(&req.ty);
                                        decl_entry::to_option(decl_provider::get_class(
                                            None,
                                            &typing_env::get_ctx(env),
                                            cn.id_ref().as_str(),
                                        ))
                                        .and_then(|cnc| {
                                            // Since only final classes can satisfy require class constraints, if the type constant is
                                            // found in the require class then it must be concrete.  No need to check that here.
                                            cls::get_typeconst(&cnc, tconst_name)
                                        })
                                    },
                                );
                            match tconst_element_in_req_class {
                                Some(tconst_element_in_req_class) => TypeconstType {
                                    is_synthesized: true,
                                    ..tconst_element_in_req_class
                                },
                                None => tconst_element,
                            }
                        }
                    })
                } else {
                    tconst_element
                }
            };

            match class_tconst_opt {
                Some(tconst) => check_typeconst_override(
                    env,
                    implements,
                    (class_pos, class_),
                    parent_tconst,
                    &tconst,
                    parent_class,
                    on_error((parent_pos.clone(), cls::name(parent_class))),
                ),
                None => {
                    // The only case when a member belongs to a parent but not the child is if the parent is an
                    // interface and the child is a concrete class. Otherwise, the member would have been inherited.
                    let err = typing_error::primary(primary::T::Member_not_implemented {
                        pos: parent_pos.clone(),
                        member_name: tconst_name.clone(),
                        decl_pos: decl_pos(parent_tconst.name.pos()),
                        quickfixes: vec![],
                    });
                    typing_error_utils::add_typing_error(&err, env)
                }
            }
        }
    }
}

fn merge_member_maps(
    env: &Env,
    allow_diamonds: bool,
    class_name: &Id,
    acc_map: ParentMembers,
    (parent, map): (Rc<Parent>, MemberMap),
) -> ParentMembers {
    let mut errors_per_diamond: BTreeMap<String, BTreeMap<String, typing_error::T>> =
        BTreeMap::new();
    let mut acc_map = acc_map;
    for (mem_kind, members) in map {
        let members_for_mem_kind: BTreeMap<String, ParentClassEltSet> =
            match acc_map.remove(&mem_kind) {
                None => (members.into_iter())
                    .map(|(name, elt)| {
                        let mut set = ParentClassEltSet::new();
                        set.insert(parent_class_elt::make(None, (elt, Rc::clone(&parent))));
                        (name, set)
                    })
                    .collect(),
                Some(prev_members) => {
                    // `MemberNameMap.merge`, which calls its function in
                    // decreasing order of the names (see the module
                    // documentation).
                    let mut members = members;
                    let mut prev_members = prev_members;
                    let names: BTreeSet<String> = (members.keys())
                        .chain(prev_members.keys())
                        .cloned()
                        .collect();
                    let mut merged: BTreeMap<String, ParentClassEltSet> = BTreeMap::new();
                    for member_name in names.into_iter().rev() {
                        let elt = members.remove(&member_name);
                        let elts = prev_members.remove(&member_name);
                        let res = match (elt, elts) {
                            (None, None) => None,
                            (Some(elt), None) => {
                                let mut set = ParentClassEltSet::new();
                                set.insert(parent_class_elt::make(None, (elt, Rc::clone(&parent))));
                                Some(set)
                            }
                            (None, elts @ Some(_)) => elts,
                            (Some(elt), Some(elts)) => {
                                let ((elt, mut elts), error) = check_trait_diamonds(
                                    env,
                                    allow_diamonds,
                                    class_name,
                                    &member_name,
                                    (elt, Rc::clone(&parent)),
                                    elts,
                                    mem_kind,
                                );
                                // We want only one error per diamond, so we aggregate errors in
                                // `errors_per_diamond` before adding them later.
                                if let Some(((diamond_parent, origin), error)) = error {
                                    // `S_map.add ~combine:(fun x _ -> x)` keeps the error already there.
                                    (errors_per_diamond.entry(diamond_parent).or_default())
                                        .entry(origin)
                                        .or_insert(error);
                                }
                                // `Set.add` keeps the element already there.
                                elts.insert(elt);
                                Some(elts)
                            }
                        };
                        if let Some(res) = res {
                            merged.insert(member_name, res);
                        }
                    }
                    merged
                }
            };
        acc_map.insert(mem_kind, members_for_mem_kind);
    }
    let members = acc_map;
    for errors_per_origin in errors_per_diamond.values() {
        // `S_map.keys` (`Wrapped_map.keys`) folds with `::`: the keys come in
        // decreasing order, and `minimum_classes` depends on that order.
        let origins: Vec<String> = errors_per_origin.keys().rev().cloned().collect();
        for origin in minimum_classes(env, origins) {
            let error = errors_per_origin
                .get(&origin)
                .unwrap_or_else(|| panic!("Not_found"));
            typing_error_utils::add_typing_error(error, env)
        }
    }
    members
}

fn union_parent_members(
    env: &Env,
    class_ast: &nast::Class_,
    parents: &[ParentInfo],
) -> ParentMembers {
    let allow_diamonds = naming_attributes::mem(
        sn::user_attributes::ENABLE_METHOD_TRAIT_DIAMOND,
        &class_ast.user_attributes.0,
    );
    let class_name = &class_ast.name;
    let parent_member_maps: Vec<(Rc<Parent>, MemberMap)> =
        parents.iter().map(make_parent_member_map).collect();
    let mut acc: ParentMembers = BTreeMap::new();
    for parent_member_map in parent_member_maps {
        acc = merge_member_maps(env, allow_diamonds, class_name, acc, parent_member_map);
    }
    acc
}

fn check_class_extends_parents_members(
    env: &mut Env,
    (class_ast, class_): (&nast::Class_, &cls::T),
    parents: &[ParentInfo],
    on_error: OnError<'_>,
) {
    let members: ParentMembers = union_parent_members(env, class_ast, parents);
    check_members_from_all_parents(env, (&class_ast.name.0, class_), on_error, &members)
}

fn check_consts_are_not_abstract(
    env: &Env,
    is_final: bool,
    class_name_pos: &Pos,
    consts: &[nast::ClassConst],
) {
    for const_ in consts {
        match &const_.kind {
            aast::ClassConstKind::CCAbstract(_) => typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Abstract_member_in_concrete_class {
                    pos: const_.id.0.clone(),
                    class_name_pos: class_name_pos.clone(),
                    is_final,
                    member_kind: primary::AbstractMemberKind::constant,
                    member_name: const_.id.1.clone(),
                }),
                env,
            ),
            aast::ClassConstKind::CCConcrete(_) => {}
        }
    }
}

fn check_typeconsts_are_not_abstract(
    env: &Env,
    is_final: bool,
    class_name_pos: &Pos,
    typeconsts: &[nast::ClassTypeconstDef],
) {
    for tc in typeconsts {
        match &tc.kind {
            aast::ClassTypeconst::TCAbstract(_) => typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Abstract_member_in_concrete_class {
                    pos: tc.name.0.clone(),
                    class_name_pos: class_name_pos.clone(),
                    is_final,
                    member_kind: primary::AbstractMemberKind::type_constant,
                    member_name: tc.name.1.clone(),
                }),
                env,
            ),
            aast::ClassTypeconst::TCConcrete(_) => {}
        }
    }
}

fn check_properties_are_not_abstract(
    env: &Env,
    is_final: bool,
    class_name_pos: &Pos,
    properties: &[nast::ClassVar],
) {
    for property in properties {
        if property.abstract_ {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Abstract_member_in_concrete_class {
                    pos: property.id.0.clone(),
                    class_name_pos: class_name_pos.clone(),
                    is_final,
                    member_kind: primary::AbstractMemberKind::property,
                    member_name: property.id.1.clone(),
                }),
                env,
            )
        }
    }
}

fn check_methods_are_not_abstract(
    env: &Env,
    is_final: bool,
    class_name_pos: &Pos,
    methods: &[nast::Method_],
) {
    for method_ in methods {
        if method_.abstract_ {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Abstract_member_in_concrete_class {
                    pos: method_.name.0.clone(),
                    class_name_pos: class_name_pos.clone(),
                    is_final,
                    member_kind: primary::AbstractMemberKind::method_,
                    member_name: method_.name.1.clone(),
                }),
                env,
            )
        }
    }
}

/// Error if there are abstract members in a concrete class' AST.
fn check_concrete_has_no_abstract_members(env: &Env, class_: &nast::Class_) {
    let nast::Class_ {
        kind: c_kind,
        final_: is_final,
        typeconsts: c_typeconsts,
        consts: c_consts,
        vars: c_vars,
        methods: c_methods,
        name: Id(class_name_pos, _),
        ..
    } = class_;
    let is_final = *is_final;
    if ast_defs::is_c_concrete(*c_kind) || is_final {
        check_consts_are_not_abstract(env, is_final, class_name_pos, c_consts);
        check_typeconsts_are_not_abstract(env, is_final, class_name_pos, c_typeconsts);
        check_properties_are_not_abstract(env, is_final, class_name_pos, c_vars);
        check_methods_are_not_abstract(env, is_final, class_name_pos, c_methods)
    }
    // Checking that a concrete class does not inherit abstract members is checked
    // when checking against a class' parents.
}

// ~~ The externally visible function ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// [check_implements_extends_uses env ~implements ~parents type_] checks that
/// a classish type implements its interfaces, extends its base class, and
/// uses its traits.
///
/// This actually only checks member compatibility. Other hierarchy checks
/// like requirements (e.g. `require extends`) are checked in Typing_class.
///
/// - `implements`: the list of interfaces the classish type directly
///   implements.
/// - `parents`: the list of direct ancestors, including interfaces and
///   traits, the class directly uses.
/// - the last argument: the classish type to check (its AST and its
///   declaration).
///
/// [parents] also contains traits.
/// Here's a simple example showing why we need to check overriding traits:
///
/// ```text
///   trait T {
///     public function foo(): void {}
///     public function bar(): void {
///       $this->foo();
///     }
///   }
///
///   class A {
///     use T;
///     public function foo(int $x): void {}
///   }
/// ```
///
/// Overriding foo this way is unsound due to bar using foo,
/// so A::foo needs to be a subtype of T::foo.
pub fn check_implements_extends_uses(
    env: &mut Env,
    implements: &[DeclTy],
    parents: &[(aast::Hint, DeclTy)],
    (class_ast, class_): (&nast::Class_, &cls::T),
) {
    let Id(name_pos, name) = &class_ast.name;
    let implements: Vec<(PosOrDecl, cls::T)> = {
        let env: &Env = env;
        let decl_ty_to_cls = |x: &DeclTy| {
            let (_, pos_name, _) = typing_utils::unwrap_class_type(x);
            decl_entry::to_option(typing_env::get_class(env, pos_name.id_ref().as_str()))
                .map(|class_| (decl_pos(pos_name.pos()), class_))
        };
        implements.iter().filter_map(decl_ty_to_cls).collect()
    };
    let on_error = |(parent_name_pos, parent_name): (Pos, String)| -> reasons_callback::T {
        // sadly, enum error reporting requires this to keep the error in the file
        // with the enum
        if parent_name == sn::classes::HH_BUILTIN_ENUM {
            reasons_callback::bad_enum_decl(name_pos.clone())
        } else {
            reasons_callback::bad_decl_override(name.clone(), parent_name_pos, parent_name)
        }
    };
    let parents: Vec<ParentInfo> = {
        let env: &Env = env;
        let destructure_type = |(aast::Hint(p, _h), ty): &(aast::Hint, DeclTy)| {
            let (_, pos_name, tparaml) = typing_utils::unwrap_class_type(ty);
            let name = pos_name.id_ref().as_str().to_string();
            decl_entry::to_option(typing_env::get_class(env, &name))
                .map(|class_| ((p.clone(), name), ty.clone(), tparaml, class_))
        };
        parents.iter().filter_map(destructure_type).collect()
    };
    for parent in &parents {
        let (parent_name, _, _, _) = parent;
        check_class_extends_parent_constructors(
            &parent_name.0,
            env,
            parent,
            class_,
            name_pos,
            on_error(parent_name.clone()),
        )
    }
    check_class_extends_parents_constants(
        env,
        &implements,
        (class_ast, class_),
        &parents,
        &on_error,
    );
    check_class_extends_parents_typeconsts(
        env,
        &implements,
        (class_ast, class_),
        &parents,
        &on_error,
    );
    check_class_extends_parents_members(env, (class_ast, class_), &parents, &on_error);
    check_concrete_has_no_abstract_members(env, class_ast)
}

#[cfg(test)]
mod tests {
    use super::member_kind;
    use super::member_kind::T as MK;

    #[test]
    fn member_kind_predicates() {
        let all = [
            MK::Property,
            MK::StaticProperty,
            MK::Method,
            MK::StaticMethod,
            MK::Constructor {
                is_consistent: false,
            },
            MK::Constructor {
                is_consistent: true,
            },
        ];
        let methods: Vec<bool> = all.iter().map(|k| member_kind::is_method(*k)).collect();
        assert_eq!(methods, [false, false, true, true, false, false]);
        let props: Vec<bool> = all.iter().map(|k| member_kind::is_property(*k)).collect();
        assert_eq!(props, [true, true, false, false, false, false]);
        let functional: Vec<bool> = all.iter().map(|k| member_kind::is_functional(*k)).collect();
        assert_eq!(functional, [false, false, true, true, true, true]);
        let ctors: Vec<bool> = all
            .iter()
            .map(|k| member_kind::is_constructor(*k))
            .collect();
        assert_eq!(ctors, [false, false, false, false, true, true]);
        let statics: Vec<bool> = all.iter().map(|k| member_kind::is_static(*k)).collect();
        assert_eq!(statics, [false, true, false, true, false, false]);
    }

    /// `[@@deriving ord]`: constructors in declaration order, then their
    /// arguments (`false < true`).
    #[test]
    fn member_kind_order() {
        let mut kinds = vec![
            MK::Constructor {
                is_consistent: true,
            },
            MK::StaticMethod,
            MK::Constructor {
                is_consistent: false,
            },
            MK::Method,
            MK::StaticProperty,
            MK::Property,
        ];
        kinds.sort_by(member_kind::compare);
        assert_eq!(
            kinds,
            vec![
                MK::Property,
                MK::StaticProperty,
                MK::Method,
                MK::StaticMethod,
                MK::Constructor {
                    is_consistent: false
                },
                MK::Constructor {
                    is_consistent: true
                },
            ]
        );
        assert!(member_kind::equal(&MK::Method, &MK::Method));
        assert!(!member_kind::equal(&MK::Method, &MK::StaticMethod));
    }
}
