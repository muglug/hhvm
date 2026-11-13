// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `shallow_class_diff.ml`. See `hh/PORTING.md`.
//!
//! The diff of two versions of the shallow declaration of a class
//! ([`diff_class`]).
//!
//! Shallow classes are the `hackrs` ones (`ty::decl::ShallowClass<R>`, as
//! `crate::decl_provider::get_shallow_class` returns them). Their equalities
//! are not those of `ty::decl` (whose `PartialEq` compares the reasons of the
//! types): the `[@@deriving eq]` functions of `Shallow_decl_defs` and the ones
//! of `Typing_defs` they are made of, which compare declared types with
//! `equal_decl_ty`, are ported in the private modules [`shallow_decl_defs`]
//! and [`typing_defs`] (neither `crate` module has them). `Poly.( = )`, the
//! structural equality of OCaml, is the `PartialEq` of `ty::decl`.
//!
//! The first-class modules of signature `Member_S` are the implementations of
//! the trait [`MemberS`] (`class_const::Member`, ...), given to
//! [`diff_members`] as a type parameter.

use naming_special_names_rust as sn;
use oxidized::aast_defs::PackageMembership;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::Visibility;
use oxidized::typing_defs_flags::FunTypeFlags;
use ty::decl::EnumType;
use ty::decl::ShallowClass;
use ty::decl::ShallowClassConst;
use ty::decl::ShallowMethod;
use ty::decl::ShallowProp;
use ty::decl::ShallowTypeconst;
use ty::decl::Ty_;
use ty::decl::Typeconst;
use ty::decl::UserAttribute;
use ty::decl::ty::DeclConstraintRequirement;
use ty::decl::ty::UserAttributeParam;

use crate::ast_defs;
use crate::class_diff;
use crate::class_diff::ClassShellChange;
use crate::class_diff::ConstructorChange;
use crate::class_diff::EnumTypeChange;
use crate::class_diff::MemberChange;
use crate::class_diff::MemberDiff;
use crate::class_diff::ParentChanges;
use crate::class_diff::bool_change;
use crate::class_diff::kind_change;
use crate::class_diff::major_change;
use crate::class_diff::member_modification;
use crate::class_diff::named_items_list_change;
use crate::class_diff::value_change;
use crate::class_diff::value_diff;
use crate::ctx::R;
use crate::decl_pos_utils;
use crate::decl_utils;
use crate::s_map;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::xhp_attribute;

type BPos = <R as ty::reason::Reason>::Pos;

/// `List.equal`
fn list_equal<A>(equal: impl Fn(&A, &A) -> bool, l1: &[A], l2: &[A]) -> bool {
    l1.len() == l2.len() && l1.iter().zip(l2.iter()).all(|(x, y)| equal(x, y))
}

/// `Option.equal`
fn option_equal<A>(equal: impl Fn(&A, &A) -> bool, o1: Option<&A>, o2: Option<&A>) -> bool {
    match (o1, o2) {
        (None, None) => true,
        (Some(x), Some(y)) => equal(x, y),
        (None, Some(_)) | (Some(_), None) => false,
    }
}

mod typing_defs {
    //! The functions of `Typing_defs` (and `Typing_defs_core`) on declared
    //! data that `crate::typing_defs` does not have, for the `hackrs` types:
    //! the `[@@deriving eq]` equalities, which compare declared types with
    //! `equal_decl_ty` (reasons ignored) and everything else structurally,
    //! positions included.

    use super::*;
    use crate::typing_defs_core;

    /// `Typing_defs.ty_equal` on declared types (`phys_equal` of the nodes,
    /// or `ty_compare` = 0: the same as `equal_decl_ty`).
    pub fn ty_equal(ty1: &DeclTy, ty2: &DeclTy) -> bool {
        typing_defs_core::equal_decl_ty(ty1, ty2)
    }

    /// `Typing_defs.tyl_equal` (`tyl_compare ~sort:false` = 0)
    pub fn tyl_equal(tyl1: &[DeclTy], tyl2: &[DeclTy]) -> bool {
        typing_defs_core::equal_decl_tyl(tyl1, tyl2)
    }

    pub fn equal_decl_ty(ty1: &DeclTy, ty2: &DeclTy) -> bool {
        typing_defs_core::equal_decl_ty(ty1, ty2)
    }

    /// `equal_user_attribute`: its name (with its position), its parameters
    /// and its raw value, which is the derived equality of `ty::decl`.
    pub fn equal_user_attribute(ua1: &UserAttribute<BPos>, ua2: &UserAttribute<BPos>) -> bool {
        ua1 == ua2
    }

    pub fn equal_user_attribute_param(p1: &UserAttributeParam, p2: &UserAttributeParam) -> bool {
        p1 == p2
    }

    /// `Typing_defs_core.user_attribute_param_to_string`. (A `String` parameter
    /// is bytes: one that is not UTF-8 is converted lossily.)
    pub fn user_attribute_param_to_string(p: &UserAttributeParam) -> String {
        match p {
            UserAttributeParam::Classname(s) => s.as_str().to_string(),
            UserAttributeParam::EnumClassLabel(s) | UserAttributeParam::Int(s) => {
                s.as_str().to_string()
            }
            UserAttributeParam::String(s) => String::from_utf8_lossy(s.as_bytes()).into_owned(),
        }
    }

    /// `equal_decl_tparam`
    pub fn equal_decl_tparam(tp1: &DeclTparam, tp2: &DeclTparam) -> bool {
        tp1.variance == tp2.variance
            && tp1.name == tp2.name
            && list_equal(
                |(ck1, ty1), (ck2, ty2)| ck1 == ck2 && equal_decl_ty(ty1, ty2),
                &tp1.constraints,
                &tp2.constraints,
            )
            && tp1.reified == tp2.reified
            && list_equal(
                equal_user_attribute,
                &tp1.user_attributes,
                &tp2.user_attributes,
            )
    }

    /// `equal_enum_type`
    pub fn equal_enum_type(e1: &EnumType<R>, e2: &EnumType<R>) -> bool {
        equal_decl_ty(&e1.base, &e2.base)
            && option_equal(
                equal_decl_ty,
                e1.constraint.as_ref(),
                e2.constraint.as_ref(),
            )
            && list_equal(equal_decl_ty, &e1.includes, &e2.includes)
    }

    /// `equal_typeconst`
    pub fn equal_typeconst(tc1: &Typeconst<R>, tc2: &Typeconst<R>) -> bool {
        match (tc1, tc2) {
            (Typeconst::TCAbstract(a1), Typeconst::TCAbstract(a2)) => {
                option_equal(
                    equal_decl_ty,
                    a1.as_constraint.as_ref(),
                    a2.as_constraint.as_ref(),
                ) && option_equal(
                    equal_decl_ty,
                    a1.super_constraint.as_ref(),
                    a2.super_constraint.as_ref(),
                ) && option_equal(equal_decl_ty, a1.default.as_ref(), a2.default.as_ref())
            }
            (Typeconst::TCConcrete(c1), Typeconst::TCConcrete(c2)) => equal_decl_ty(&c1.ty, &c2.ty),
            (Typeconst::TCAbstract(_) | Typeconst::TCConcrete(_), _) => false,
        }
    }

    pub fn equal_class_const_kind(
        k1: &ty::decl::ClassConstKind,
        k2: &ty::decl::ClassConstKind,
    ) -> bool {
        k1 == k2
    }

    pub fn equal_consistent_kind(
        k1: &ty::decl::ConsistentKind,
        k2: &ty::decl::ConsistentKind,
    ) -> bool {
        k1 == k2
    }
}

mod shallow_decl_defs {
    //! The functions of `Shallow_decl_defs` that this module uses, for the
    //! `hackrs` types: the accessors of the flags, and the
    //! `[@@deriving eq]` equalities (see [`super::typing_defs`]).

    use super::*;

    pub fn sp_abstract(sp: &ShallowProp<R>) -> bool {
        sp.flags.is_abstract()
    }

    pub fn sp_lsb(sp: &ShallowProp<R>) -> bool {
        sp.flags.is_lsb()
    }

    pub fn sp_tests_bypass_visibility(sp: &ShallowProp<R>) -> bool {
        sp.flags.tests_bypass_visibility()
    }

    pub fn sm_abstract(sm: &ShallowMethod<R>) -> bool {
        sm.flags.is_abstract()
    }

    pub fn sm_tests_bypass_visibility(sm: &ShallowMethod<R>) -> bool {
        sm.flags.tests_bypass_visibility()
    }

    /// `equal_shallow_class_const`: `scc_abstract`, `scc_name`, `scc_type`,
    /// `scc_refs`, `scc_value`, `scc_const_value`.
    pub fn equal_shallow_class_const(c1: &ShallowClassConst<R>, c2: &ShallowClassConst<R>) -> bool {
        let ShallowClassConst {
            kind,
            name,
            ty,
            refs,
            is_shape_key,
            value,
            const_value,
        } = c1;
        typing_defs::equal_class_const_kind(kind, &c2.kind)
            && *name == c2.name
            && typing_defs::equal_decl_ty(ty, &c2.ty)
            && *refs == c2.refs
            && *is_shape_key == c2.is_shape_key
            && *value == c2.value
            && *const_value == c2.const_value
    }

    /// `equal_shallow_typeconst`: `stc_name`, `stc_kind`, `stc_enforceable`,
    /// `stc_reifiable`, `stc_is_ctx`.
    pub fn equal_shallow_typeconst(t1: &ShallowTypeconst<R>, t2: &ShallowTypeconst<R>) -> bool {
        let ShallowTypeconst {
            name,
            kind,
            enforceable,
            reifiable,
            is_ctx,
        } = t1;
        *name == t2.name
            && typing_defs::equal_typeconst(kind, &t2.kind)
            // `Pos_or_decl.t * bool`: `(p, true)` is `Some p`, and `(_, false)`
            // (whose position is always `Pos_or_decl.none`) is `None`.
            && *enforceable == t2.enforceable
            && *reifiable == t2.reifiable
            && *is_ctx == t2.is_ctx
    }

    /// `equal_shallow_prop`: `sp_name`, `sp_xhp_attr`, `sp_type`,
    /// `sp_visibility`, `sp_flags`.
    pub fn equal_shallow_prop(p1: &ShallowProp<R>, p2: &ShallowProp<R>) -> bool {
        let ShallowProp {
            name,
            xhp_attr,
            ty,
            visibility,
            flags,
        } = p1;
        *name == p2.name
            && *xhp_attr == p2.xhp_attr
            && typing_defs::equal_decl_ty(ty, &p2.ty)
            && *visibility == p2.visibility
            && *flags == p2.flags
    }

    /// `equal_shallow_method`: `sm_name`, `sm_type`, `sm_visibility`,
    /// `sm_deprecated`, `sm_flags`, `sm_attributes`, `sm_package_requirement`.
    pub fn equal_shallow_method(m1: &ShallowMethod<R>, m2: &ShallowMethod<R>) -> bool {
        let ShallowMethod {
            name,
            ty,
            visibility,
            deprecated,
            flags,
            attributes,
            package_requirement,
        } = m1;
        *name == m2.name
            && typing_defs::equal_decl_ty(ty, &m2.ty)
            && *visibility == m2.visibility
            && *deprecated == m2.deprecated
            && *flags == m2.flags
            && list_equal(
                typing_defs::equal_user_attribute,
                attributes,
                &m2.attributes,
            )
            && *package_requirement == m2.package_requirement
    }

    /// `equal_xhp_enum_values` (`Ast_defs.xhp_enum_value list S_map.t`)
    pub fn equal_xhp_enum_values(
        v1: &std::collections::BTreeMap<pos::Symbol, Box<[ty::decl::ty::XhpEnumValue]>>,
        v2: &std::collections::BTreeMap<pos::Symbol, Box<[ty::decl::ty::XhpEnumValue]>>,
    ) -> bool {
        v1 == v2
    }

    /// `equal_decl_constraint_requirement`
    pub fn equal_decl_constraint_requirement(
        r1: &DeclConstraintRequirement<R>,
        r2: &DeclConstraintRequirement<R>,
    ) -> bool {
        match (r1, r2) {
            (DeclConstraintRequirement::DCREqual(t1), DeclConstraintRequirement::DCREqual(t2))
            | (
                DeclConstraintRequirement::DCRSubtype(t1),
                DeclConstraintRequirement::DCRSubtype(t2),
            ) => typing_defs::equal_decl_ty(t1, t2),
            (
                DeclConstraintRequirement::DCREqual(_) | DeclConstraintRequirement::DCRSubtype(_),
                _,
            ) => false,
        }
    }

    /// `equal_shallow_class`, field by field.
    pub fn equal_shallow_class(c1: &ShallowClass<R>, c2: &ShallowClass<R>) -> bool {
        let ShallowClass {
            mode,
            is_final,
            is_abstract,
            is_xhp,
            is_internal,
            has_xhp_keyword,
            kind,
            module,
            name,
            tparams,
            extends,
            uses,
            xhp_attr_uses,
            xhp_enum_values,
            xhp_marked_empty,
            req_extends,
            req_implements,
            req_constraints,
            implements,
            support_dynamic_type,
            consts,
            typeconsts,
            props,
            static_props,
            constructor,
            static_methods,
            methods,
            user_attributes,
            enum_type,
            docs_url,
            package,
        } = c1;
        *mode == c2.mode
            && *is_final == c2.is_final
            && *is_abstract == c2.is_abstract
            && *is_xhp == c2.is_xhp
            && *is_internal == c2.is_internal
            && *has_xhp_keyword == c2.has_xhp_keyword
            && *kind == c2.kind
            // `Ast_defs.id option`
            && *module == c2.module
            && *name == c2.name
            && list_equal(typing_defs::equal_decl_tparam, tparams, &c2.tparams)
            && list_equal(typing_defs::equal_decl_ty, extends, &c2.extends)
            && list_equal(typing_defs::equal_decl_ty, uses, &c2.uses)
            && list_equal(typing_defs::equal_decl_ty, xhp_attr_uses, &c2.xhp_attr_uses)
            && equal_xhp_enum_values(xhp_enum_values, &c2.xhp_enum_values)
            && *xhp_marked_empty == c2.xhp_marked_empty
            && list_equal(typing_defs::equal_decl_ty, req_extends, &c2.req_extends)
            && list_equal(typing_defs::equal_decl_ty, req_implements, &c2.req_implements)
            && list_equal(
                equal_decl_constraint_requirement,
                req_constraints,
                &c2.req_constraints,
            )
            && list_equal(typing_defs::equal_decl_ty, implements, &c2.implements)
            && *support_dynamic_type == c2.support_dynamic_type
            && list_equal(equal_shallow_class_const, consts, &c2.consts)
            && list_equal(equal_shallow_typeconst, typeconsts, &c2.typeconsts)
            && list_equal(equal_shallow_prop, props, &c2.props)
            && list_equal(equal_shallow_prop, static_props, &c2.static_props)
            && option_equal(
                equal_shallow_method,
                constructor.as_ref(),
                c2.constructor.as_ref(),
            )
            && list_equal(equal_shallow_method, static_methods, &c2.static_methods)
            && list_equal(equal_shallow_method, methods, &c2.methods)
            && list_equal(
                typing_defs::equal_user_attribute,
                user_attributes,
                &c2.user_attributes,
            )
            && option_equal(
                typing_defs::equal_enum_type,
                enum_type.as_ref(),
                c2.enum_type.as_ref(),
            )
            && *docs_url == c2.docs_url
            && *package == c2.package
    }
}

mod parents {
    //! `Parents`

    use super::*;

    pub struct T<'a> {
        pub extends: &'a [DeclTy],
        pub implements: &'a [DeclTy],
        pub req_extends: &'a [DeclTy],
        pub req_implements: &'a [DeclTy],
        pub req_constraints: &'a [DeclConstraintRequirement<R>],
        pub uses: &'a [DeclTy],
        pub xhp_attr_uses: &'a [DeclTy],
    }

    /// `[@@deriving eq]`
    pub fn equal(c1: &T<'_>, c2: &T<'_>) -> bool {
        list_equal(typing_defs::equal_decl_ty, c1.extends, c2.extends)
            && list_equal(typing_defs::equal_decl_ty, c1.implements, c2.implements)
            && list_equal(typing_defs::equal_decl_ty, c1.req_extends, c2.req_extends)
            && list_equal(
                typing_defs::equal_decl_ty,
                c1.req_implements,
                c2.req_implements,
            )
            && list_equal(
                shallow_decl_defs::equal_decl_constraint_requirement,
                c1.req_constraints,
                c2.req_constraints,
            )
            && list_equal(typing_defs::equal_decl_ty, c1.uses, c2.uses)
            && list_equal(
                typing_defs::equal_decl_ty,
                c1.xhp_attr_uses,
                c2.xhp_attr_uses,
            )
    }

    pub fn of_shallow_class(c: &ShallowClass<R>) -> T<'_> {
        let ShallowClass {
            extends: sc_extends,
            implements: sc_implements,
            req_extends: sc_req_extends,
            req_implements: sc_req_implements,
            req_constraints: sc_req_constraints,
            uses: sc_uses,
            xhp_attr_uses: sc_xhp_attr_uses,
            mode: _,
            is_final: _,
            is_abstract: _,
            is_xhp: _,
            is_internal: _,
            has_xhp_keyword: _,
            kind: _,
            module: _,
            name: _,
            tparams: _,
            xhp_enum_values: _,
            xhp_marked_empty: _,
            support_dynamic_type: _,
            consts: _,
            typeconsts: _,
            props: _,
            static_props: _,
            constructor: _,
            static_methods: _,
            methods: _,
            user_attributes: _,
            enum_type: _,
            docs_url: _,
            package: _,
        } = c;
        T {
            extends: sc_extends,
            implements: sc_implements,
            req_extends: sc_req_extends,
            req_implements: sc_req_implements,
            req_constraints: sc_req_constraints,
            uses: sc_uses,
            xhp_attr_uses: sc_xhp_attr_uses,
        }
    }
}

/// When a member of a given name is declared multiple times, keep the first
/// (as Decl_inheritance does).
fn merge_member_lists<'a, M>(
    get_name: impl Fn(&M) -> String,
    l1: &'a [M],
    l2: &'a [M],
) -> s_map::T<(Option<&'a M>, Option<&'a M>)> {
    let mut map = s_map::T::new();
    for x in l1 {
        let name = get_name(x);
        if !map.contains_key(&name) {
            map.insert(name, (Some(x), None));
        }
    }
    for y in l2 {
        let name = get_name(y);
        match map.get(&name).copied() {
            Some((x, None)) => {
                map.insert(name, (x, Some(y)));
            }
            None => {
                map.insert(name, (None, Some(y)));
            }
            Some((_, Some(_))) => (),
        }
    }
    map
}

/// `module type Member_S`
trait MemberS {
    type T;

    fn diff(m1: &Self::T, m2: &Self::T) -> Option<MemberChange>;

    fn is_private(m: &Self::T) -> bool;

    fn is_internal(m: &Self::T) -> bool;

    /// Whether adding this member implies that the constructor and the
    /// constructor of all descendants should be considered modified.
    /// This is the case for example for required XHP attributes.
    fn constructor_is_changed_inheritance_when_added(m: &Self::T) -> bool;

    /// Whether modifying this member implies that the constructor and the
    /// constructor of all descendants should be considered modified.
    /// This is the case for example for required XHP attributes.
    fn constructor_is_changed_inheritance_when_modified(old: &Self::T, new_: &Self::T) -> bool;
}

/// A module change can alter an internal member's accessibility even if its
/// declaration is unchanged.
fn diff_member<M: MemberS>(module_changed: bool, old: &M::T, new_: &M::T) -> Option<MemberChange> {
    let diff = M::diff(old, new_);
    match diff {
        None if module_changed && M::is_internal(old) && M::is_internal(new_) => {
            Some(MemberChange::Modified(member_modification::T::Other))
        }
        None | Some(_) => diff,
    }
}

/// Returns the diff of two member lists, plus a diff on the constructor if the
/// member changes impact the constructor.
///
/// (The module `Member` of the OCaml is the type parameter.)
fn diff_members<M: MemberS>(
    members_left_right: &s_map::T<(Option<&M::T>, Option<&M::T>)>,
    classish_kind: ClassishKind,
    module_changed: bool,
) -> (s_map::T<MemberChange>, ConstructorChange) {
    let mut diff: s_map::T<MemberChange> = s_map::T::new();
    let mut constructor_change: ConstructorChange = None;
    for (name, old_and_new) in members_left_right.iter() {
        match *old_and_new {
            (None, None) => panic!("merge_member_lists added (None, None)"),
            (Some(member), None) | (None, Some(member))
                if (!ast_defs::is_c_trait(classish_kind)) && M::is_private(member) =>
            {
                diff.insert(name.clone(), MemberChange::PrivateChangeNotInTrait);
            }
            (Some(_), None) => {
                diff.insert(name.clone(), MemberChange::Removed);
            }
            (None, Some(m)) => {
                constructor_change = class_diff::max_constructor_change(
                    constructor_change,
                    if M::constructor_is_changed_inheritance_when_added(m) {
                        Some(MemberChange::ChangedInheritance)
                    } else {
                        None
                    },
                );
                diff.insert(name.clone(), MemberChange::Added);
            }
            (Some(old_member), Some(new_member)) => {
                if let Some(ch) = diff_member::<M>(module_changed, old_member, new_member) {
                    diff.insert(name.clone(), ch);
                }
                constructor_change = class_diff::max_constructor_change(
                    constructor_change,
                    if M::constructor_is_changed_inheritance_when_modified(old_member, new_member) {
                        Some(MemberChange::ChangedInheritance)
                    } else {
                        None
                    },
                );
            }
        }
    }
    (diff, constructor_change)
}

mod class_const {
    //! `ClassConst : Member_S with type t = shallow_class_const`

    use super::*;

    pub fn diff(c1: &ShallowClassConst<R>, c2: &ShallowClassConst<R>) -> Option<MemberChange> {
        let c1 = decl_pos_utils::normalize_sig::shallow_class_const(c1);
        let c2 = decl_pos_utils::normalize_sig::shallow_class_const(c2);
        if shallow_decl_defs::equal_shallow_class_const(&c1, &c2) {
            None
        } else if !typing_defs::equal_class_const_kind(&c1.kind, &c2.kind) {
            Some(MemberChange::ChangedInheritance)
        } else {
            Some(MemberChange::Modified(member_modification::T::Other))
        }
    }

    pub fn is_private(_: &ShallowClassConst<R>) -> bool {
        false
    }

    pub fn is_internal(_: &ShallowClassConst<R>) -> bool {
        false
    }

    pub fn constructor_is_changed_inheritance_when_added(_: &ShallowClassConst<R>) -> bool {
        false
    }

    pub fn constructor_is_changed_inheritance_when_modified(
        _old: &ShallowClassConst<R>,
        _new_: &ShallowClassConst<R>,
    ) -> bool {
        false
    }

    /// The module, as a type: `diff_members::<Member>`.
    pub enum Member {}

    impl MemberS for Member {
        type T = ShallowClassConst<R>;

        fn diff(m1: &Self::T, m2: &Self::T) -> Option<MemberChange> {
            diff(m1, m2)
        }

        fn is_private(m: &Self::T) -> bool {
            is_private(m)
        }

        fn is_internal(m: &Self::T) -> bool {
            is_internal(m)
        }

        fn constructor_is_changed_inheritance_when_added(m: &Self::T) -> bool {
            constructor_is_changed_inheritance_when_added(m)
        }

        fn constructor_is_changed_inheritance_when_modified(old: &Self::T, new_: &Self::T) -> bool {
            constructor_is_changed_inheritance_when_modified(old, new_)
        }
    }
}

mod type_const {
    //! `TypeConst : Member_S with type t = shallow_typeconst`

    use super::*;

    pub fn diff(tc1: &ShallowTypeconst<R>, tc2: &ShallowTypeconst<R>) -> Option<MemberChange> {
        let tc1 = decl_pos_utils::normalize_sig::shallow_typeconst(tc1);
        let tc2 = decl_pos_utils::normalize_sig::shallow_typeconst(tc2);
        if shallow_decl_defs::equal_shallow_typeconst(&tc1, &tc2) {
            None
        } else {
            match (&tc1.kind, &tc2.kind) {
                (Typeconst::TCAbstract(_), Typeconst::TCAbstract(_))
                | (Typeconst::TCConcrete(_), Typeconst::TCConcrete(_)) => {
                    Some(MemberChange::Modified(member_modification::T::Other))
                }
                (_, Typeconst::TCAbstract(_) | Typeconst::TCConcrete(_)) => {
                    Some(MemberChange::ChangedInheritance)
                }
            }
        }
    }

    pub fn is_private(_: &ShallowTypeconst<R>) -> bool {
        false
    }

    pub fn is_internal(_: &ShallowTypeconst<R>) -> bool {
        false
    }

    pub fn constructor_is_changed_inheritance_when_added(_: &ShallowTypeconst<R>) -> bool {
        false
    }

    pub fn constructor_is_changed_inheritance_when_modified(
        _old: &ShallowTypeconst<R>,
        _new_: &ShallowTypeconst<R>,
    ) -> bool {
        false
    }

    /// The module, as a type: `diff_members::<Member>`.
    pub enum Member {}

    impl MemberS for Member {
        type T = ShallowTypeconst<R>;

        fn diff(m1: &Self::T, m2: &Self::T) -> Option<MemberChange> {
            diff(m1, m2)
        }

        fn is_private(m: &Self::T) -> bool {
            is_private(m)
        }

        fn is_internal(m: &Self::T) -> bool {
            is_internal(m)
        }

        fn constructor_is_changed_inheritance_when_added(m: &Self::T) -> bool {
            constructor_is_changed_inheritance_when_added(m)
        }

        fn constructor_is_changed_inheritance_when_modified(old: &Self::T, new_: &Self::T) -> bool {
            constructor_is_changed_inheritance_when_modified(old, new_)
        }
    }
}

mod prop {
    //! `Prop : Member_S with type t = shallow_prop`

    use super::*;

    pub fn diff(p1: &ShallowProp<R>, p2: &ShallowProp<R>) -> Option<MemberChange> {
        let p1 = decl_pos_utils::normalize_sig::shallow_prop(p1);
        let p2 = decl_pos_utils::normalize_sig::shallow_prop(p2);
        if shallow_decl_defs::equal_shallow_prop(&p1, &p2) {
            None
        } else if (p1.visibility != p2.visibility)
            || shallow_decl_defs::sp_abstract(&p1) != shallow_decl_defs::sp_abstract(&p2)
            || shallow_decl_defs::sp_lsb(&p1) != shallow_decl_defs::sp_lsb(&p2)
            || shallow_decl_defs::sp_tests_bypass_visibility(&p1)
                != shallow_decl_defs::sp_tests_bypass_visibility(&p2)
        {
            Some(MemberChange::ChangedInheritance)
        } else {
            Some(MemberChange::Modified(member_modification::T::Other))
        }
    }

    pub fn is_private(p: &ShallowProp<R>) -> bool {
        p.visibility == Visibility::Private
    }

    pub fn is_internal(p: &ShallowProp<R>) -> bool {
        p.visibility == Visibility::Internal || p.visibility == Visibility::ProtectedInternal
    }

    pub fn constructor_is_changed_inheritance_when_added(p: &ShallowProp<R>) -> bool {
        xhp_attribute::opt_is_required(p.xhp_attr)
    }

    pub fn constructor_is_changed_inheritance_when_modified(
        old: &ShallowProp<R>,
        new_: &ShallowProp<R>,
    ) -> bool {
        xhp_attribute::opt_is_required(new_.xhp_attr)
            && (!xhp_attribute::opt_is_required(old.xhp_attr))
    }

    /// The module, as a type: `diff_members::<Member>`.
    pub enum Member {}

    impl MemberS for Member {
        type T = ShallowProp<R>;

        fn diff(m1: &Self::T, m2: &Self::T) -> Option<MemberChange> {
            diff(m1, m2)
        }

        fn is_private(m: &Self::T) -> bool {
            is_private(m)
        }

        fn is_internal(m: &Self::T) -> bool {
            is_internal(m)
        }

        fn constructor_is_changed_inheritance_when_added(m: &Self::T) -> bool {
            constructor_is_changed_inheritance_when_added(m)
        }

        fn constructor_is_changed_inheritance_when_modified(old: &Self::T, new_: &Self::T) -> bool {
            constructor_is_changed_inheritance_when_modified(old, new_)
        }
    }
}

mod method {
    //! `Method : Member_S with type t = shallow_method`

    use super::*;

    pub fn diff(m1: &ShallowMethod<R>, m2: &ShallowMethod<R>) -> Option<MemberChange> {
        let m1 = decl_pos_utils::normalize_sig::shallow_method(m1);
        let m2 = decl_pos_utils::normalize_sig::shallow_method(m2);
        if shallow_decl_defs::equal_shallow_method(&m1, &m2) {
            None
        } else if (m1.visibility != m2.visibility)
            || shallow_decl_defs::sm_abstract(&m1) != shallow_decl_defs::sm_abstract(&m2)
            || shallow_decl_defs::sm_tests_bypass_visibility(&m1)
                != shallow_decl_defs::sm_tests_bypass_visibility(&m2)
        {
            Some(MemberChange::ChangedInheritance)
        } else {
            let member_modification = {
                let is_async = |ty: &DeclTy| -> bool {
                    match ty.node_ref() {
                        // `Typing_defs.Flags.get_ft_async fun_type`
                        Ty_::Tfun(fun_type) => fun_type.flags.contains(FunTypeFlags::ASYNC),
                        _ => false,
                    }
                };
                match (is_async(&m1.ty), is_async(&m2.ty)) {
                    (false, true) => member_modification::T::Asyncified,
                    (true, false) => member_modification::T::Deasyncified,
                    _ => member_modification::T::Other,
                }
            };
            Some(MemberChange::Modified(member_modification))
        }
    }

    pub fn is_private(m: &ShallowMethod<R>) -> bool {
        m.visibility == Visibility::Private
    }

    pub fn is_internal(m: &ShallowMethod<R>) -> bool {
        m.visibility == Visibility::Internal || m.visibility == Visibility::ProtectedInternal
    }

    pub fn constructor_is_changed_inheritance_when_added(_: &ShallowMethod<R>) -> bool {
        false
    }

    pub fn constructor_is_changed_inheritance_when_modified(
        _old: &ShallowMethod<R>,
        _new_: &ShallowMethod<R>,
    ) -> bool {
        false
    }

    /// The module, as a type: `diff_members::<Member>`.
    pub enum Member {}

    impl MemberS for Member {
        type T = ShallowMethod<R>;

        fn diff(m1: &Self::T, m2: &Self::T) -> Option<MemberChange> {
            diff(m1, m2)
        }

        fn is_private(m: &Self::T) -> bool {
            is_private(m)
        }

        fn is_internal(m: &Self::T) -> bool {
            is_internal(m)
        }

        fn constructor_is_changed_inheritance_when_added(m: &Self::T) -> bool {
            constructor_is_changed_inheritance_when_added(m)
        }

        fn constructor_is_changed_inheritance_when_modified(old: &Self::T, new_: &Self::T) -> bool {
            constructor_is_changed_inheritance_when_modified(old, new_)
        }
    }
}

fn diff_constructor(
    old_cls: &ShallowClass<R>,
    new_cls: &ShallowClass<R>,
    module_changed: bool,
    old_cstr: Option<&ShallowMethod<R>>,
    new_cstr: Option<&ShallowMethod<R>>,
) -> Option<MemberChange> {
    let consistent1 = decl_utils::consistent_construct_kind(old_cls);
    let consistent2 = decl_utils::consistent_construct_kind(new_cls);
    if !typing_defs::equal_consistent_kind(&consistent1, &consistent2) {
        Some(MemberChange::ChangedInheritance)
    } else {
        match (old_cstr, new_cstr) {
            (None, None) => None,
            (Some(_), None) => Some(MemberChange::Removed),
            (None, Some(_)) => Some(MemberChange::Added),
            (Some(old_method), Some(new_method)) => {
                diff_member::<method::Member>(module_changed, old_method, new_method)
            }
        }
    }
}

fn diff_class_members(c1: &ShallowClass<R>, c2: &ShallowClass<R>) -> MemberDiff {
    let diff = class_diff::empty_member_diff();
    let kind = c2.kind;
    let module_changed = match (&c1.module, &c2.module) {
        (Some(m1), Some(m2)) if m1.id_ref().as_str() == m2.id_ref().as_str() => false,
        (None, None) => false,
        _ => true,
    };
    let diff = {
        let get_name = |x: &ShallowClassConst<R>| x.name.id_ref().as_str().to_string();
        let consts = merge_member_lists(get_name, &c1.consts, &c2.consts);
        let (consts, constructor_change) =
            diff_members::<class_const::Member>(&consts, kind, module_changed);
        MemberDiff {
            consts,
            constructor: class_diff::max_constructor_change(diff.constructor, constructor_change),
            ..diff
        }
    };
    let diff = {
        let get_name = |x: &ShallowTypeconst<R>| x.name.id_ref().as_str().to_string();
        let typeconsts = merge_member_lists(get_name, &c1.typeconsts, &c2.typeconsts);
        let (typeconsts, constructor_change) =
            diff_members::<type_const::Member>(&typeconsts, kind, module_changed);
        MemberDiff {
            typeconsts,
            constructor: class_diff::max_constructor_change(diff.constructor, constructor_change),
            ..diff
        }
    };
    let diff = {
        let get_name = |x: &ShallowProp<R>| x.name.id_ref().as_str().to_string();
        let props = merge_member_lists(get_name, &c1.props, &c2.props);
        let (props, constructor_change) =
            diff_members::<prop::Member>(&props, kind, module_changed);
        MemberDiff {
            props,
            constructor: class_diff::max_constructor_change(diff.constructor, constructor_change),
            ..diff
        }
    };
    let diff = {
        let get_name = |x: &ShallowProp<R>| x.name.id_ref().as_str().to_string();
        let sprops = merge_member_lists(get_name, &c1.static_props, &c2.static_props);
        let (sprops, constructor_change) =
            diff_members::<prop::Member>(&sprops, kind, module_changed);
        MemberDiff {
            sprops,
            constructor: class_diff::max_constructor_change(diff.constructor, constructor_change),
            ..diff
        }
    };
    let diff = {
        let get_name = |x: &ShallowMethod<R>| x.name.id_ref().as_str().to_string();
        let methods = merge_member_lists(get_name, &c1.methods, &c2.methods);
        let (methods, constructor_change) =
            diff_members::<method::Member>(&methods, kind, module_changed);
        MemberDiff {
            methods,
            constructor: class_diff::max_constructor_change(diff.constructor, constructor_change),
            ..diff
        }
    };
    let diff = {
        let get_name = |x: &ShallowMethod<R>| x.name.id_ref().as_str().to_string();
        let smethods = merge_member_lists(get_name, &c1.static_methods, &c2.static_methods);
        let (smethods, constructor_change) =
            diff_members::<method::Member>(&smethods, kind, module_changed);
        MemberDiff {
            smethods,
            constructor: class_diff::max_constructor_change(diff.constructor, constructor_change),
            ..diff
        }
    };
    let diff = {
        let constructor =
            diff_constructor(
                c1,
                c2,
                module_changed,
                c1.constructor.as_ref(),
                c2.constructor.as_ref(),
            );
        MemberDiff {
            constructor: class_diff::max_constructor_change(diff.constructor, constructor),
            ..diff
        }
    };
    diff
}

/// Return true if the two classes would (shallowly) produce the same member
/// resolution order.
/// NB: It is critical for the correctness of incremental typechecking that every
/// bit of information used to decide the ordering of decl folding is checked here!
fn mro_inputs_equal(c1: &ShallowClass<R>, c2: &ShallowClass<R>) -> bool {
    let is_to_string = |m: &&ShallowMethod<R>| m.name.id_ref().as_str() == sn::members::__TO_STRING;
    let sc_name_equal =
        // compare c1 and c2 sc_name ignoring the position in the file, but not the filename
        c1.name.id_ref().as_str() == c2.name.id_ref().as_str()
            && c1.name.pos().file() == c2.name.pos().file();
    // `List.equal Poly.( = )`: the structural equality of the `hackrs` values.
    sc_name_equal
        && c1.kind == c2.kind
        && option_equal(
            shallow_decl_defs::equal_shallow_method,
            c1.methods.iter().find(is_to_string),
            c2.methods.iter().find(is_to_string),
        )
        && c1.tparams == c2.tparams
        && c1.extends == c2.extends
        && c1.implements == c2.implements
        && c1.uses == c2.uses
        && c1.req_extends == c2.req_extends
        && c1.req_implements == c2.req_implements
        && c1.xhp_attr_uses == c2.xhp_attr_uses
}

/// The ConsistentConstruct attribute is propagated down the inheritance
/// hierarchy, so we can model it with Changed_inheritance on the constructor. To
/// do so, though, we need to remove the attribute while normalizing classes (so
/// that we don't consider it a Major_change).
fn remove_consistent_construct_attribute(sc: ShallowClass<R>) -> ShallowClass<R> {
    ShallowClass {
        user_attributes: sc
            .user_attributes
            .iter()
            .filter(|ua| !(ua.name.id_ref().as_str() == sn::user_attributes::CONSISTENT_CONSTRUCT))
            .cloned()
            .collect(),
        ..sc
    }
}

fn remove_user_defined_attributes(sc: ShallowClass<R>) -> ShallowClass<R> {
    ShallowClass {
        user_attributes: sc
            .user_attributes
            .iter()
            .filter(|ua| sn::user_attributes::is_reserved(ua.name.id_ref().as_str()))
            .cloned()
            .collect(),
        ..sc
    }
}

/// Normalize module if the class is public
fn remove_modules_if_public(sc: ShallowClass<R>) -> ShallowClass<R> {
    if sc.is_internal {
        sc
    } else {
        ShallowClass { module: None, ..sc }
    }
}

fn remove_members_except_to_string(sc: ShallowClass<R>) -> ShallowClass<R> {
    ShallowClass {
        constructor: None,
        consts: Box::new([]),
        typeconsts: Box::new([]),
        props: Box::new([]),
        static_props: Box::new([]),
        static_methods: Box::new([]),
        methods: sc
            .methods
            .iter()
            .filter(|m| m.name.id_ref().as_str() == sn::members::__TO_STRING)
            .cloned()
            .collect(),
        ..sc
    }
}

/// To normalize classes for comparison, we:
///
/// - Remove the ConsistentConstruct attribute
/// - When annotation-agnostic decl diffing is enabled, remove user-defined
///   attributes
/// - Remove module if class itself is public
/// - Remove all members (except for the toString method, which results in the
///   implicit inclusion of the Stringish interface),
/// - Replace all positions with Pos.none
///
/// We consider any difference between normalized classes to be a "Major change".
/// This means only that we have not implemented some means of computing a fanout
/// for that change which is smaller than what would be added by
/// Shallow_class_fanout.add_maximum_fanout (e.g., since we DO have fine-grained
/// dependency tracking for uses of members, and can handle them in a more
/// intelligent way, we remove them during major-change-detection).
///
/// There are certainly opportunities for us to be cleverer about some kinds of
/// changes, but any kind of cleverness in reducing fanout must be implemented
/// with great care.
fn normalize(
    enable_annotation_agnostic_decl_diffing: bool,
    sc: &ShallowClass<R>,
) -> ShallowClass<R> {
    let sc = remove_consistent_construct_attribute(sc.clone());
    let sc = if enable_annotation_agnostic_decl_diffing {
        remove_user_defined_attributes(sc)
    } else {
        sc
    };
    let sc = remove_members_except_to_string(sc);
    let sc = decl_pos_utils::normalize_sig::shallow_class(&sc);
    remove_modules_if_public(sc)
}

fn type_name(ty: &DeclTy) -> (String, Vec<DeclTy>) {
    let (_, name, tparams) = decl_utils::unwrap_class_type(ty);
    (name.id_ref().as_str().to_string(), tparams)
}

mod bag {
    //! `Bag`: A bag of strings.
    //! A bag is a set where elements can appear multiple times

    use super::*;

    #[derive(Clone, Debug)]
    pub struct T(s_map::T<isize>);

    fn empty() -> T {
        T(s_map::T::new())
    }

    fn add(s: &str, t: T) -> T {
        let T(mut t) = t;
        let v = t.get(s).copied().unwrap_or(0);
        t.insert(s.to_string(), v + 1);
        T(t)
    }

    pub fn remove(s: &str, t: T) -> T {
        let T(mut t) = t;
        match t.get(s).copied() {
            None => T(t),
            Some(v) => {
                if v == 1 {
                    t.remove(s);
                } else {
                    t.insert(s.to_string(), v - 1);
                }
                T(t)
            }
        }
    }

    pub fn mem(s: &str, t: &T) -> bool {
        t.0.contains_key(s)
    }

    pub fn of_list(l: &[String]) -> T {
        let mut bag = empty();
        for x in l {
            bag = add(x, bag);
        }
        bag
    }
}

/// `exception Found_swap`
struct FoundSwap;

/// The order has changed if there exists x and y
/// such that x comes before y in [l1],
/// but y comes before x in [l2],
/// i.e. if there exists two elements which are in both lists
/// and have been swapped.
fn order_has_changed(l1: &[String], l2: &[String]) -> bool {
    fn go(l1: &[String], l2: &[String], l1_bag: bag::T, l2_bag: bag::T) -> Result<bool, FoundSwap> {
        match l1 {
            [] => Ok(false),
            [x1, l1 @ ..] => match l2 {
                [] => Ok(false),
                l2 => {
                    let l1_bag = bag::remove(x1, l1_bag);
                    if bag::mem(x1, &l2_bag) {
                        find_swap(l1, l2, l1_bag, l2_bag, x1)
                    } else {
                        go(l1, l2, l1_bag, l2_bag)
                    }
                }
            },
        }
    }
    fn find_swap(
        l1: &[String],
        l2: &[String],
        l1_bag: bag::T,
        l2_bag: bag::T,
        x1: &str,
    ) -> Result<bool, FoundSwap> {
        match l2 {
            [x2, l2 @ ..] => {
                let l2_bag = bag::remove(x2, l2_bag);
                if x2 == x1 {
                    go(l1, l2, l1_bag, l2_bag)
                } else if bag::mem(x2, &l1_bag) {
                    Err(FoundSwap)
                } else {
                    find_swap(l1, l2, l1_bag, l2_bag, x1)
                }
            }
            [] => panic!("We should have found x1 in l2 before this happens."),
        }
    }
    match go(l1, l2, bag::of_list(l1), bag::of_list(l2)) {
        Ok(b) => b,
        Err(FoundSwap) => true,
    }
}

fn diff_value_lists<V, W: Clone, C: Clone>(
    values1: &[V],
    values2: &[V],
    equal: impl Fn(&V, &V) -> bool,
    get_name_value: impl Fn(&V) -> (String, W),
    diff: impl Fn(&W, &W) -> Option<C>,
) -> Option<named_items_list_change::T<C>> {
    if list_equal(&equal, values1, values2) {
        None
    } else {
        let values1: Vec<(String, W)> = values1.iter().map(&get_name_value).collect();
        let values2: Vec<(String, W)> = values2.iter().map(&get_name_value).collect();
        // (The fields of the record are evaluated from right to left.)
        let per_name_changes = s_map::merge(
            |_, value1, value2| match (value1, value2) {
                (None, None) => None,
                (None, Some(_)) => Some(value_change::T::Added),
                (Some(_), None) => Some(value_change::T::Removed),
                (Some(value1), Some(value2)) => diff(value1, value2).map(value_change::T::Modified),
            },
            &s_map::of_list(values1.clone()),
            &s_map::of_list(values2.clone()),
        );
        let order_change = order_has_changed(
            &values1
                .into_iter()
                .map(|(name, _)| name)
                .collect::<Vec<_>>(),
            &values2
                .into_iter()
                .map(|(name, _)| name)
                .collect::<Vec<_>>(),
        );
        Some(named_items_list_change::T {
            order_change,
            per_name_changes,
        })
    }
}

fn diff_of_equal<A>(equal: impl Fn(&A, &A) -> bool, x: &A, y: &A) -> Option<()> {
    if equal(x, y) { None } else { Some(()) }
}

fn diff_type_lists(
    values1: &[DeclTy],
    values2: &[DeclTy],
) -> Option<named_items_list_change::T<named_items_list_change::T<()>>> {
    diff_value_lists(
        values1,
        values2,
        typing_defs::ty_equal,
        type_name,
        |tparams1: &Vec<DeclTy>, tparams2: &Vec<DeclTy>| {
            diff_value_lists(
                tparams1,
                tparams2,
                typing_defs::ty_equal,
                type_name,
                |x: &Vec<DeclTy>, y: &Vec<DeclTy>| {
                    diff_of_equal(|x: &Vec<DeclTy>, y| typing_defs::tyl_equal(x, y), x, y)
                },
            )
        },
    )
}

fn diff_parents(c1: &parents::T<'_>, c2: &parents::T<'_>) -> Option<ParentChanges> {
    if parents::equal(c1, c2) {
        None
    } else {
        fn equal_req_constraints(
            rc1: &[DeclConstraintRequirement<R>],
            rc2: &[DeclConstraintRequirement<R>],
        ) -> bool {
            match (rc1, rc2) {
                (
                    [DeclConstraintRequirement::DCREqual(c1), tl1 @ ..],
                    [DeclConstraintRequirement::DCREqual(c2), tl2 @ ..],
                )
                | (
                    [DeclConstraintRequirement::DCRSubtype(c1), tl1 @ ..],
                    [DeclConstraintRequirement::DCRSubtype(c2), tl2 @ ..],
                ) => typing_defs::ty_equal(c1, c2) && equal_req_constraints(tl1, tl2),
                ([], []) => true,
                _ => false,
            }
        }

        // (The fields of the record are evaluated from right to left.)
        let xhp_attr_changes = diff_type_lists(c1.xhp_attr_uses, c2.xhp_attr_uses);
        let uses_changes = diff_type_lists(c1.uses, c2.uses);
        let req_constraints_changes =
            !equal_req_constraints(c1.req_constraints, c2.req_constraints);
        let req_implements_changes = diff_type_lists(c1.req_implements, c2.req_implements);
        let req_extends_changes = diff_type_lists(c1.req_extends, c2.req_extends);
        let implements_changes = diff_type_lists(c1.implements, c2.implements);
        let extends_changes = diff_type_lists(c1.extends, c2.extends);
        Some(ParentChanges {
            extends_changes,
            implements_changes,
            req_extends_changes,
            req_implements_changes,
            req_constraints_changes,
            uses_changes,
            xhp_attr_changes,
        })
    }
}

fn diff_kinds(kind1: ClassishKind, kind2: ClassishKind) -> Option<kind_change::T> {
    if kind1 == kind2 {
        None
    } else {
        Some(kind_change::T { new_kind: kind2 })
    }
}

fn diff_bools(b1: bool, b2: bool) -> Option<bool_change::T> {
    match (b1, b2) {
        (true, true) | (false, false) => None,
        (false, true) => Some(bool_change::T::Became),
        (true, false) => Some(bool_change::T::NoMore),
    }
}

fn diff_options<A, C>(
    option1: Option<&A>,
    option2: Option<&A>,
    diff: impl Fn(&A, &A) -> Option<C>,
) -> Option<value_change::T<C>> {
    match (option1, option2) {
        (None, None) => None,
        (None, Some(_)) => Some(value_change::T::Added),
        (Some(_), None) => Some(value_change::T::Removed),
        (Some(value1), Some(value2)) => match diff(value1, value2) {
            None => None,
            Some(diff) => Some(value_change::T::Modified(diff)),
        },
    }
}

/// `diff_options ~diff:(diff_of_equal Ast_defs.equal_id)`: the name and its
/// position.
fn diff_modules(
    option1: Option<&pos::Positioned<pos::ModuleName, BPos>>,
    option2: Option<&pos::Positioned<pos::ModuleName, BPos>>,
) -> Option<value_change::T<()>> {
    diff_options(option1, option2, |m1, m2| {
        diff_of_equal(|m1, m2| m1 == m2, m1, m2)
    })
}

fn diff_packages(
    option1: Option<&PackageMembership>,
    option2: Option<&PackageMembership>,
) -> Option<value_change::T<()>> {
    diff_options(option1, option2, |pm1, pm2| match (pm1, pm2) {
        (PackageMembership::PackageOverride(_, p1), PackageMembership::PackageOverride(_, p2))
        | (
            PackageMembership::PackageConfigAssignment(p1),
            PackageMembership::PackageOverride(_, p2),
        )
        | (
            PackageMembership::PackageOverride(_, p1),
            PackageMembership::PackageConfigAssignment(p2),
        )
        | (
            PackageMembership::PackageConfigAssignment(p1),
            PackageMembership::PackageConfigAssignment(p2),
        ) => diff_of_equal(|p1: &String, p2| p1 == p2, p1, p2),
    })
}

fn diff<V: Clone>(
    equal: impl Fn(&V, &V) -> bool,
    old_value: &V,
    new_value: &V,
) -> Option<value_diff::T<V>> {
    if equal(old_value, new_value) {
        None
    } else {
        Some(value_diff::T {
            old_value: old_value.clone(),
            new_value: new_value.clone(),
        })
    }
}

fn diff_types(old_value: &DeclTy, new_value: &DeclTy) -> Option<value_diff::T<DeclTy>> {
    diff(typing_defs::ty_equal, old_value, new_value)
}

fn diff_enum_types(enum_type1: &EnumType<R>, enum_type2: &EnumType<R>) -> Option<EnumTypeChange> {
    if typing_defs::equal_enum_type(enum_type1, enum_type2) {
        None
    } else {
        let EnumType {
            base: base1,
            constraint: constraint1,
            includes: includes1,
        } = enum_type1;
        let EnumType {
            base: base2,
            constraint: constraint2,
            includes: includes2,
        } = enum_type2;

        // (The fields of the record are evaluated from right to left.)
        let includes_change = diff_type_lists(includes1, includes2);
        let constraint_change =
            diff_options(constraint1.as_ref(), constraint2.as_ref(), diff_types);
        let base_change = diff_types(base1, base2);
        Some(EnumTypeChange {
            base_change,
            constraint_change,
            includes_change,
        })
    }
}

fn diff_enum_type_options(
    option1: Option<&EnumType<R>>,
    option2: Option<&EnumType<R>>,
) -> Option<value_change::T<EnumTypeChange>> {
    diff_options(option1, option2, diff_enum_types)
}

fn user_attribute_name_value(ua: &UserAttribute<BPos>) -> (String, Vec<UserAttributeParam>) {
    (ua.name.id_ref().as_str().to_string(), ua.params.to_vec())
}

fn diff_user_attribute_params(
    attrs1: &[UserAttributeParam],
    attrs2: &[UserAttributeParam],
) -> Option<named_items_list_change::T<()>> {
    diff_value_lists(
        attrs1,
        attrs2,
        typing_defs::equal_user_attribute_param,
        |param| {
            (
                typing_defs::user_attribute_param_to_string(param),
                param.clone(),
            )
        },
        |x, y| diff_of_equal(typing_defs::equal_user_attribute_param, x, y),
    )
}

fn diff_class_shells(c1: &ShallowClass<R>, c2: &ShallowClass<R>) -> ClassShellChange {
    // (The fields of the record are evaluated from right to left.)
    let enum_type_change = diff_enum_type_options(c1.enum_type.as_ref(), c2.enum_type.as_ref());
    let user_attributes_changes = diff_value_lists(
        &c1.user_attributes,
        &c2.user_attributes,
        typing_defs::equal_user_attribute,
        user_attribute_name_value,
        |attrs1: &Vec<UserAttributeParam>, attrs2: &Vec<UserAttributeParam>| {
            diff_user_attribute_params(attrs1, attrs2)
        },
    );
    let xhp_enum_values_change =
        !shallow_decl_defs::equal_xhp_enum_values(&c1.xhp_enum_values, &c2.xhp_enum_values);
    let package_change = diff_packages(c1.package.as_ref(), c2.package.as_ref());
    let module_change = diff_modules(c1.module.as_ref(), c2.module.as_ref());
    let support_dynamic_type_change = diff_bools(c1.support_dynamic_type, c2.support_dynamic_type);
    let has_xhp_keyword_change = diff_bools(c1.has_xhp_keyword, c2.has_xhp_keyword);
    let internal_change = diff_bools(c1.is_internal, c2.is_internal);
    let is_xhp_change = diff_bools(c1.is_xhp, c2.is_xhp);
    let abstract_change = diff_bools(c1.is_abstract, c2.is_abstract);
    let final_change = diff_bools(c1.is_final, c2.is_final);
    let kind_change = diff_kinds(c1.kind, c2.kind);
    // (The new type parameters come first: OCaml diffs `c2.sc_tparams` against
    // `c1.sc_tparams`.)
    let type_parameters_change = diff_value_lists(
        &c2.tparams,
        &c1.tparams,
        typing_defs::equal_decl_tparam,
        |tparam: &DeclTparam| (tparam.name.id_ref().as_str().to_string(), tparam.clone()),
        |x, y| diff_of_equal(typing_defs::equal_decl_tparam, x, y),
    );
    let parent_changes = diff_parents(
        &parents::of_shallow_class(c1),
        &parents::of_shallow_class(c2),
    );
    ClassShellChange {
        old_classish_kind: c1.kind,
        parent_changes,
        type_parameters_change,
        kind_change,
        final_change,
        abstract_change,
        is_xhp_change,
        internal_change,
        has_xhp_keyword_change,
        support_dynamic_type_change,
        module_change,
        package_change,
        xhp_enum_values_change,
        user_attributes_changes,
        enum_type_change,
    }
}

pub fn diff_class(
    enable_annotation_agnostic_decl_diffing: bool,
    c1: &ShallowClass<R>,
    c2: &ShallowClass<R>,
) -> Option<class_diff::T> {
    let class_shell1 = normalize(enable_annotation_agnostic_decl_diffing, c1);
    let class_shell2 = normalize(enable_annotation_agnostic_decl_diffing, c2);
    let member_diff = diff_class_members(c1, c2);
    if !shallow_decl_defs::equal_shallow_class(&class_shell1, &class_shell2) {
        Some(class_diff::T::MajorChange(major_change::T::Modified(
            diff_class_shells(&class_shell1, &class_shell2),
            member_diff,
        )))
    } else {
        let mro_inputs_equal = mro_inputs_equal(c1, c2);
        if mro_inputs_equal && class_diff::is_empty_member_diff(&member_diff) {
            None
        } else {
            Some(class_diff::T::MinorChange(member_diff))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;
    use crate::decl_provider;
    use crate::decl_provider::testing::ctx_of;

    fn strings(l: &[&str]) -> Vec<String> {
        l.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn order_changes() {
        let changed = |l1: &[&str], l2: &[&str]| order_has_changed(&strings(l1), &strings(l2));
        assert!(!changed(&[], &[]));
        assert!(!changed(&["a", "b"], &["a", "b"]));
        assert!(changed(&["a", "b"], &["b", "a"]));
        // Adding or removing elements is not a change of order.
        assert!(!changed(&["a", "b"], &["b"]));
        assert!(!changed(&["a", "b"], &["a", "c", "b"]));
        assert!(!changed(&["a"], &["c", "a", "d"]));
        assert!(changed(&["a", "c", "b"], &["b", "a"]));
        // Duplicates.
        assert!(!changed(&["a", "a", "b"], &["a", "b"]));
        assert!(changed(&["a", "b", "a"], &["b", "a", "a"]));
    }

    #[test]
    fn bags() {
        let b = bag::of_list(&strings(&["a", "a", "b"]));
        assert!(bag::mem("a", &b) && bag::mem("b", &b) && !bag::mem("c", &b));
        let b = bag::remove("a", b);
        assert!(bag::mem("a", &b));
        let b = bag::remove("a", b);
        assert!(!bag::mem("a", &b));
        let b = bag::remove("c", b);
        assert!(bag::mem("b", &b));
    }

    #[test]
    fn merging_member_lists_keeps_the_first_of_a_name() {
        let get_name = |x: &(&str, usize)| x.0.to_string();
        let l1 = [("a", 1), ("b", 2), ("a", 3)];
        let l2 = [("b", 4), ("c", 5), ("b", 6), ("c", 7)];
        let merged = merge_member_lists(get_name, &l1, &l2);
        let merged: Vec<(String, Option<usize>, Option<usize>)> = merged
            .iter()
            .map(|(k, (x, y))| (k.clone(), x.map(|x| x.1), y.map(|y| y.1)))
            .collect();
        assert_eq!(
            merged,
            vec![
                ("a".to_string(), Some(1), None),
                ("b".to_string(), Some(2), Some(4)),
                ("c".to_string(), None, Some(5)),
            ]
        );
    }

    #[test]
    fn simple_diffs() {
        assert_eq!(diff_bools(true, true), None);
        assert_eq!(diff_bools(false, true), Some(bool_change::T::Became));
        assert_eq!(diff_bools(true, false), Some(bool_change::T::NoMore));
        assert_eq!(
            diff_kinds(ClassishKind::Ctrait, ClassishKind::Cinterface),
            Some(kind_change::T {
                new_kind: ClassishKind::Cinterface
            })
        );
        assert_eq!(diff_kinds(ClassishKind::Cenum, ClassishKind::Cenum), None);
        let eq = |a: &isize, b: &isize| diff_of_equal(|a: &isize, b| a == b, a, b);
        assert_eq!(diff_options(None, None, eq), None);
        assert_eq!(
            diff_options(None, Some(&1), eq),
            Some(value_change::T::Added)
        );
        assert_eq!(
            diff_options(Some(&1), None, eq),
            Some(value_change::T::Removed)
        );
        assert_eq!(diff_options(Some(&1), Some(&1), eq), None);
        assert_eq!(
            diff_options(Some(&1), Some(&2), eq),
            Some(value_change::T::Modified(()))
        );
        // A package is compared by its name only.
        let over =
            |p: &str| PackageMembership::PackageOverride(oxidized::pos::Pos::NONE, p.to_string());
        let conf = |p: &str| PackageMembership::PackageConfigAssignment(p.to_string());
        assert_eq!(diff_packages(Some(&over("p")), Some(&conf("p"))), None);
        assert_eq!(
            diff_packages(Some(&over("p")), Some(&conf("q"))),
            Some(value_change::T::Modified(()))
        );
    }

    #[test]
    fn value_lists() {
        let get = |x: &(&str, isize)| (x.0.to_string(), x.1);
        let eq = |x: &(&str, isize), y: &(&str, isize)| x == y;
        let modified = |x: &isize, y: &isize| if x == y { None } else { Some(*y) };
        assert_eq!(
            diff_value_lists(&[("a", 1)], &[("a", 1)], eq, get, modified),
            None
        );
        let change = diff_value_lists(
            &[("a", 1), ("b", 2), ("c", 3)],
            &[("c", 4), ("a", 1), ("d", 5)],
            eq,
            get,
            modified,
        )
        .unwrap();
        assert!(change.order_change);
        assert_eq!(
            change.per_name_changes.into_iter().collect::<Vec<_>>(),
            vec![
                ("b".to_string(), value_change::T::Removed),
                ("c".to_string(), value_change::T::Modified(4)),
                ("d".to_string(), value_change::T::Added),
            ]
        );
    }

    /// The shallow class `name` of the file `src`.
    fn shallow_class(src: &str, name: &str) -> Arc<ShallowClass<R>> {
        let ctx = ctx_of(src, TypecheckerOptions::default());
        decl_provider::get_shallow_class(&ctx, name).unwrap()
    }

    fn diff_of(before: &str, after: &str, name: &str) -> Option<class_diff::T> {
        diff_class(
            false,
            &shallow_class(before, name),
            &shallow_class(after, name),
        )
    }

    fn members(bindings: &[(&str, MemberChange)]) -> s_map::T<MemberChange> {
        bindings
            .iter()
            .map(|(name, change)| (name.to_string(), *change))
            .collect()
    }

    #[test]
    fn unchanged_class() {
        let src = "<?hh\nclass Foo { public function f(): void {} }\n";
        assert_eq!(diff_of(src, src, "\\Foo"), None);
    }

    /// `test/integration_ml/test_remove_method.ml`: removing a method is a
    /// minor change, whose fanout reaches the descendants.
    #[test]
    fn remove_method() {
        let before = "<?hh // strict

class Foo {
  public function f() : void {}
}
";
        let after = "<?hh // strict

class Foo {}
";
        let diff = diff_of(before, after, "\\Foo");
        assert_eq!(
            diff,
            Some(class_diff::T::MinorChange(MemberDiff {
                methods: members(&[("f", MemberChange::Removed)]),
                ..class_diff::empty_member_diff()
            }))
        );
        assert!(class_diff::method_or_property_change_affects_descendants(
            &MemberChange::Removed
        ));
    }

    /// A method whose return type changes (the class of
    /// `test/integration_ml/test_added_parent.ml`, against an earlier version
    /// whose `f` returned `int`; in that test itself `Foo`'s file was empty
    /// before, so `Foo` is `Major_change Added`, which `compute_class_diffs`
    /// gives: see `shallow_decl_compare`'s tests) is a minor change that does
    /// not reach the descendants through inheritance.
    #[test]
    fn modified_method() {
        let before = "<?hh // strict

class Foo {
  public function f() : int {
  }
}
";
        let after = "<?hh // strict

class Foo {
  /* HH_FIXME[4336] */
  public function f() : string {
  }
}
";
        assert_eq!(
            diff_of(before, after, "\\Foo"),
            Some(class_diff::T::MinorChange(MemberDiff {
                methods: members(&[("f", MemberChange::Modified(member_modification::T::Other))]),
                ..class_diff::empty_member_diff()
            }))
        );
        assert!(!class_diff::method_or_property_change_affects_descendants(
            &MemberChange::Modified(member_modification::T::Other)
        ));
    }

    /// `mro_inputs_equal` compares the parents with `Poly.( = )`, positions
    /// included, but the name of the class only by its file: a class with a
    /// parent that moves in its file is a minor change with no member
    /// changed; one without parents that moves is unchanged.
    #[test]
    fn moved_classes() {
        let before = "<?hh\nclass B {}\nclass A extends B {}\n";
        let after = "<?hh\n\nclass B {}\n\nclass A extends B {}\n";
        assert_eq!(
            diff_of(before, after, "\\A"),
            Some(class_diff::T::MinorChange(class_diff::empty_member_diff()))
        );
        assert_eq!(diff_of(before, after, "\\B"), None);
    }

    /// The module of a public class is not compared, but when it changes,
    /// the internal members that did not change are `Modified Other`. The
    /// module of an internal class is part of its shell.
    #[test]
    fn module_changes() {
        let class = |module: &str, visibility: &str| {
            format!(
                "<?hh\nmodule {};\n{} class C {{\n  internal function f(): void {{}}\n  public function g(): void {{}}\n}}\n",
                module, visibility
            )
        };
        assert_eq!(
            diff_of(&class("M", "public"), &class("N", "public"), "\\C"),
            Some(class_diff::T::MinorChange(MemberDiff {
                methods: members(&[("f", MemberChange::Modified(member_modification::T::Other))]),
                ..class_diff::empty_member_diff()
            }))
        );
        assert_eq!(
            diff_of(&class("M", "public"), &class("M", "public"), "\\C"),
            None
        );
        match diff_of(&class("M", "internal"), &class("N", "internal"), "\\C") {
            Some(class_diff::T::MajorChange(major_change::T::Modified(shell, member_diff))) => {
                assert_eq!(shell.module_change, Some(value_change::T::Modified(())));
                assert_eq!(shell.internal_change, None);
                assert_eq!(
                    member_diff,
                    MemberDiff {
                        methods: members(&[(
                            "f",
                            MemberChange::Modified(member_modification::T::Other)
                        )]),
                        ..class_diff::empty_member_diff()
                    }
                );
            }
            diff => panic!("{:?}", diff),
        }
    }

    /// `test/integration_ml/test_remove_enum_variant.ml`: removing an enum
    /// constant is a minor change on the constants.
    #[test]
    fn remove_enum_variant() {
        let before = "<?hh

enum E: int {
  A = 1;
  B = 2;
}
";
        let after = "<?hh

enum E: int {
  A = 1;
}
";
        assert_eq!(
            diff_of(before, after, "\\E"),
            Some(class_diff::T::MinorChange(MemberDiff {
                consts: members(&[("B", MemberChange::Removed)]),
                ..class_diff::empty_member_diff()
            }))
        );
    }

    #[test]
    fn member_changes() {
        let diff = diff_of(
            "<?hh\nabstract class C {\n  public function f(): void {}\n  public function g(): void {}\n  private function p(): void {}\n  public int $x = 1;\n}\n",
            "<?hh\nabstract class C {\n  public abstract function f(): void;\n  public async function g(): Awaitable<void> {}\n  public int $x = 2;\n  public string $y = '';\n}\n",
            "\\C",
        );
        assert_eq!(
            diff,
            Some(class_diff::T::MinorChange(MemberDiff {
                methods: members(&[
                    ("f", MemberChange::ChangedInheritance),
                    (
                        "g",
                        MemberChange::Modified(member_modification::T::Asyncified)
                    ),
                    ("p", MemberChange::PrivateChangeNotInTrait),
                ]),
                props: members(&[("y", MemberChange::Added)]),
                ..class_diff::empty_member_diff()
            }))
        );
    }

    #[test]
    fn constructor_changes() {
        // `__ConsistentConstruct` is not a major change: it changes the
        // constructor in a way that affects the descendants.
        let diff = diff_of(
            "<?hh\nclass C {}\n",
            "<?hh\n<<__ConsistentConstruct>>\nclass C {}\n",
            "\\C",
        );
        assert_eq!(
            diff,
            Some(class_diff::T::MinorChange(MemberDiff {
                constructor: Some(MemberChange::ChangedInheritance),
                ..class_diff::empty_member_diff()
            }))
        );
        let diff = diff_of(
            "<?hh\nclass C {}\n",
            "<?hh\nclass C { public function __construct() {} }\n",
            "\\C",
        );
        assert_eq!(
            diff,
            Some(class_diff::T::MinorChange(MemberDiff {
                constructor: Some(MemberChange::Added),
                ..class_diff::empty_member_diff()
            }))
        );
    }

    #[test]
    fn major_changes() {
        match diff_of("<?hh\nclass C {}\n", "<?hh\nfinal class C {}\n", "\\C") {
            Some(class_diff::T::MajorChange(major_change::T::Modified(shell, members))) => {
                assert_eq!(shell.final_change, Some(bool_change::T::Became));
                assert_eq!(shell.kind_change, None);
                assert_eq!(shell.parent_changes, None);
                // A final class has a consistent constructor (`FinalClass`).
                assert_eq!(
                    members,
                    MemberDiff {
                        constructor: Some(MemberChange::ChangedInheritance),
                        ..class_diff::empty_member_diff()
                    }
                );
            }
            diff => panic!("{:?}", diff),
        }
        match diff_of(
            "<?hh\ninterface I {}\ninterface J {}\nclass C implements I, J {}\n",
            "<?hh\ninterface I {}\ninterface J {}\nclass C implements J, I {}\n",
            "\\C",
        ) {
            Some(class_diff::T::MajorChange(major_change::T::Modified(shell, _))) => {
                let parent_changes = shell.parent_changes.unwrap();
                let implements_changes = parent_changes.implements_changes.unwrap();
                assert!(implements_changes.order_change);
                assert!(implements_changes.per_name_changes.is_empty());
                assert_eq!(parent_changes.extends_changes, None);
                assert!(!parent_changes.req_constraints_changes);
            }
            diff => panic!("{:?}", diff),
        }
        // The new type parameters are diffed against the old ones: a new one
        // shows as removed.
        match diff_of("<?hh\nclass C {}\n", "<?hh\nclass C<T> {}\n", "\\C") {
            Some(class_diff::T::MajorChange(major_change::T::Modified(shell, _))) => {
                let type_parameters_change = shell.type_parameters_change.unwrap();
                assert_eq!(
                    type_parameters_change
                        .per_name_changes
                        .into_iter()
                        .collect::<Vec<_>>(),
                    vec![("T".to_string(), value_change::T::Removed)]
                );
            }
            diff => panic!("{:?}", diff),
        }
    }
}
