// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_defs_constraints.ml`. See `hh/PORTING.md`.
//!
//! `oxidized` has none of these types. They are named the way `oxidized` names
//! types (see `typing_defs_core.rs`): constructors in camel case
//! (`Thas_member` is `ThasMember`), and the common prefix of the fields of a
//! record removed (`hm_name` is `name`, `ci_key` is `key`).

use std::rc::Rc;
use std::cmp::Ordering;

use oxidized::aast_defs::Sid;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::typing_defs_core::Ty;
use crate::typing_defs_core::TypePredicate;
use crate::typing_defs_core::chain_compare;
use crate::typing_defs_core::class_id_compare;
use crate::typing_defs_core::compare_type_predicate;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::ty_compare;
use crate::typing_defs_core::ty_equal;
use crate::typing_defs_core::tyl_compare;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DestructureKind {
    ListDestructure,
    SplatUnpack,
}

/// Constraint type for `list()` destructuring and splat unpacking.
/// Shape and tuple destructuring (e.g., `shape('x' => $x) = $s`) uses
/// Can_index under the hood, see `Typing_destructure`.
#[derive(Clone, Debug)]
pub struct Destructure {
    /// This represents the standard parameters of a function or the fields in a list
    /// destructuring assignment. Example:
    ///
    /// function take(bool $b, float $f = 3.14, arraykey ...$aks): void {}
    /// function f((bool, float, int, string) $tup): void {
    ///   take(...$tup);
    /// }
    ///
    /// corresponds to the subtyping assertion
    ///
    /// (bool, float, int, string) <: splat([#1], [opt#2], ...#3)
    pub required: Vec<Ty>,
    /// Represents the optional parameters in a function, only used for splats
    pub optional: Vec<Ty>,
    /// Represents a function's variadic parameter, also only used for splats
    pub variadic: Option<Ty>,
    /// list() destructuring allows for partial matches on lists, even when the operation
    /// might throw i.e. list($a) = vec[];
    pub kind: DestructureKind,
}

#[derive(Clone, Debug)]
pub struct HasMemberMethod {
    /// The list of explicit type arguments provided to the method call
    pub explicit_targs: Vec<nast::Targ>,
    /// A list of the primary positions of the arguments, for error messages
    pub args_pos: Vec<Pos>,
}

#[derive(Clone, Debug)]
pub struct HasMember {
    pub name: Sid,
    pub type_: Ty,
    /// This is required to check ambiguous object access, where sometimes
    /// HHVM would access the private member of a parent class instead of the
    /// one from the current class.
    pub class_id: nast::ClassId_,
    /// - For a "has-property" constraint, this is `None`
    /// - For a "has-method" constraint, this is `Some hmm`
    pub method: Option<HasMemberMethod>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CiAccessKind {
    /// Standard array/shape/tuple index access.
    CiNormal,
    /// Access on the left side of `??`, e.g. `$x['k'] ?? $default`. Suppresses errors for missing/optional fields and nullable containers.
    CiLhsOfNullCoalesce,
    /// Access of an `optional` tuple entry in a destructuring pattern. Suppresses OOB errors for optional entries but does NOT suppress nullable-container errors.
    CiDestructureOptional,
}

/// A can_index constraint represents the ability to do an array index operation.
/// We should have t <: { ci_key; ci_val; _ } when t is a type that supports
/// being index with a value of type ci_key, and will return a value of ci_val.
#[derive(Clone, Debug)]
pub struct CanIndex {
    pub key: Ty,
    pub val: Ty,
    pub index_expr: nast::Expr,
    pub access_kind: CiAccessKind,
    pub expr_pos: Pos,
    pub array_pos: Pos,
    pub index_pos: Pos,
}

/// `$source[key] = write` update source to type val
#[derive(Clone, Debug)]
pub struct CanIndexAssign {
    pub key: Ty,
    pub write: Ty,
    pub val: Ty,
    pub index_expr: nast::Expr,
    pub expr_pos: Pos,
    pub array_pos: Pos,
    pub index_pos: Pos,
    pub write_pos: Pos,
}

/// A can_traverse represents the ability to do a foreach over a certain type.
/// We should have t <: {ct_key; ct_val; ct_is_await} when type t supports foreach
/// and doing the foreack will bind values of type ct_val, and optionally bind keys of
/// type ct_key.
#[derive(Clone, Debug)]
pub struct CanTraverse {
    pub key: Option<Ty>,
    pub val: Ty,
    pub is_await: bool,
    pub reason: Reason,
}

#[derive(Clone, Debug)]
pub struct HasTypeMember {
    pub id: String,
    pub lower: Ty,
    pub upper: Ty,
}

#[derive(Clone, Debug)]
pub enum ConstraintType_ {
    ThasMember(HasMember),
    /// [Thas_type_member('T',lo,hi)] is a supertype of all concrete class
    /// types that have a type member [::T] satisfying [lo <: T <: hi]
    ThasTypeMember(HasTypeMember),
    /// Check if the given type has a class constant that is compatible with [ty]
    ThasConst {
        name: String,
        ty: Ty,
    },
    TcanIndex(CanIndex),
    TcanIndexAssign(CanIndexAssign),
    TcanTraverse(CanTraverse),
    /// The type of container destructuring via list() or splat `...`
    /// Implements valid destructuring operations via subtyping.
    Tdestructure(Destructure),
    /// The type of a value we want to decompose based on a runtime type test.
    /// In the expression:
    /// ```
    /// if ($x is P) { ... } else { ... }
    /// ```
    ///
    /// The term `$x` must satisfy the constraint type_switch(P, T_true, T_false), where
    /// T_true is the type of `$x` if the predicate is true and T_false is the
    /// type of `$x` if the predicate is false
    TtypeSwitch {
        predicate: TypePredicate,
        ty_true: Ty,
        ty_false: Ty,
    },
}

/// `constraint_type = Reason.t * constraint_type_`
///
/// The OCaml's pair is a heap block whose identity `phys_equal` tests; here
/// the node is reference-counted, like that of [`Ty`] (see
/// [`crate::typing_defs_core::Ty`]), so that clones share it and
/// [`phys_equal_constraint_type`] can compare pointers.
#[derive(Clone, Debug)]
pub struct ConstraintType(pub Reason, pub Rc<ConstraintType_>);

#[derive(Clone, Debug)]
pub enum InternalType {
    LoclType(Ty),
    ConstraintType(ConstraintType),
}

pub fn mk_constraint_type(p: (Reason, ConstraintType_)) -> ConstraintType {
    let (r, ty_) = p;
    ConstraintType(r, Rc::new(ty_))
}

/// OCaml's `phys_equal` on constraint types (see
/// [`crate::typing_defs_core::phys_equal`]).
pub fn phys_equal_constraint_type(t1: &ConstraintType, t2: &ConstraintType) -> bool {
    Rc::ptr_eq(&t1.1, &t2.1) && t1.0 == t2.0
}

/// OCaml's `phys_equal` on internal types.
pub fn phys_equal_internal_type(t1: &InternalType, t2: &InternalType) -> bool {
    match (t1, t2) {
        (InternalType::LoclType(a), InternalType::LoclType(b)) => {
            crate::typing_defs_core::phys_equal(a, b)
        }
        (InternalType::ConstraintType(a), InternalType::ConstraintType(b)) => {
            phys_equal_constraint_type(a, b)
        }
        _ => false,
    }
}

/// The reason and the node, copied (as `Typing_defs_core.deref`).
pub fn deref_constraint_type(p: &ConstraintType) -> (Reason, ConstraintType_) {
    let ConstraintType(r, ty_) = p;
    (r.clone(), (**ty_).clone())
}

pub fn get_reason_i(t: &InternalType) -> &Reason {
    match t {
        InternalType::LoclType(lty) => get_reason(lty),
        InternalType::ConstraintType(ConstraintType(r, _)) => r,
    }
}

/// `Option.compare`
fn option_compare<T>(
    cmp: impl FnOnce(&T, &T) -> Ordering,
    o1: Option<&T>,
    o2: Option<&T>,
) -> Ordering {
    match (o1, o2) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => cmp(a, b),
    }
}

fn has_member_compare(normalize_lists: bool, hm1: &HasMember, hm2: &HasMember) -> Ordering {
    let ty_compare = |ty1: &Ty, ty2: &Ty| ty_compare(Some(normalize_lists), ty1, ty2);
    let HasMember {
        name: oxidized::ast_defs::Id(_, m1),
        type_: ty1,
        class_id: cid1,
        method: method1,
    } = hm1;
    let HasMember {
        name: oxidized::ast_defs::Id(_, m2),
        type_: ty2,
        class_id: cid2,
        method: method2,
    } = hm2;
    let method_compare = |method1: &HasMemberMethod, method2: &HasMemberMethod| {
        let HasMemberMethod {
            explicit_targs: targs1,
            args_pos: _,
        } = method1;
        let HasMemberMethod {
            explicit_targs: targs2,
            args_pos: _,
        } = method2;
        // Aast_defs.compare_hint (snd a1) (snd a2)
        crate::rt::ocaml_list::compare(|a1, a2| a1.1.cmp(&a2.1), targs1, targs2)
    };
    chain_compare(m1.cmp(m2), || {
        chain_compare(ty_compare(ty1, ty2), || {
            chain_compare(class_id_compare(cid1, cid2), || {
                option_compare(method_compare, method1.as_ref(), method2.as_ref())
            })
        })
    })
}

fn can_index_compare(normalize_lists: bool, ci1: &CanIndex, ci2: &CanIndex) -> Ordering {
    chain_compare(
        ty_compare(Some(normalize_lists), &ci1.key, &ci2.key),
        || {
            chain_compare(
                ty_compare(Some(normalize_lists), &ci1.val, &ci2.val),
                || {
                    chain_compare(ci1.access_kind.cmp(&ci2.access_kind), || {
                        // Aast.compare_expr (fun _ _ -> 0) (fun _ _ -> 0)
                        ci1.index_expr.cmp(&ci2.index_expr)
                    })
                },
            )
        },
    )
}

fn can_index_assign_compare(
    normalize_lists: bool,
    cia1: &CanIndexAssign,
    cia2: &CanIndexAssign,
) -> Ordering {
    chain_compare(
        ty_compare(Some(normalize_lists), &cia1.key, &cia2.key),
        || {
            chain_compare(
                ty_compare(Some(normalize_lists), &cia1.write, &cia2.write),
                || ty_compare(Some(normalize_lists), &cia1.val, &cia2.val),
            )
        },
    )
}

fn can_traverse_compare(normalize_lists: bool, ct1: &CanTraverse, ct2: &CanTraverse) -> Ordering {
    chain_compare(
        option_compare(
            |a, b| ty_compare(Some(normalize_lists), a, b),
            ct1.key.as_ref(),
            ct2.key.as_ref(),
        ),
        || {
            chain_compare(
                ty_compare(Some(normalize_lists), &ct1.val, &ct2.val),
                || ct1.is_await.cmp(&ct2.is_await),
            )
        },
    )
}

fn destructure_compare(normalize_lists: bool, d1: &Destructure, d2: &Destructure) -> Ordering {
    let Destructure {
        required: tyl1,
        optional: tyl_opt1,
        variadic: ty_opt1,
        kind: e1,
    } = d1;
    let Destructure {
        required: tyl2,
        optional: tyl_opt2,
        variadic: ty_opt2,
        kind: e2,
    } = d2;
    chain_compare(
        tyl_compare(false, Some(normalize_lists), tyl1, tyl2),
        || {
            chain_compare(
                tyl_compare(false, Some(normalize_lists), tyl_opt1, tyl_opt2),
                || {
                    chain_compare(
                        // (without ~normalize_lists, as in OCaml)
                        option_compare(
                            |a, b| ty_compare(None, a, b),
                            ty_opt1.as_ref(),
                            ty_opt2.as_ref(),
                        ),
                        || e1.cmp(e2),
                    )
                },
            )
        },
    )
}

fn constraint_ty_con_ordinal(cty: &ConstraintType_) -> isize {
    match cty {
        ConstraintType_::ThasMember(_) => 0,
        ConstraintType_::Tdestructure(_) => 1,
        ConstraintType_::TcanIndex(_) => 2,
        ConstraintType_::TcanIndexAssign(_) => 3,
        ConstraintType_::TcanTraverse(_) => 4,
        ConstraintType_::ThasTypeMember(_) => 5,
        ConstraintType_::TtypeSwitch { .. } => 6,
        ConstraintType_::ThasConst { .. } => 7,
    }
}

pub fn constraint_ty_compare(
    normalize_lists: Option<bool>,
    ty1: &ConstraintType,
    ty2: &ConstraintType,
) -> Ordering {
    let normalize_lists = normalize_lists.unwrap_or(false);
    let ConstraintType(_, ty1) = ty1;
    let ConstraintType(_, ty2) = ty2;
    let ty1: &ConstraintType_ = ty1;
    let ty2: &ConstraintType_ = ty2;
    match (ty1, ty2) {
        (ConstraintType_::ThasMember(hm1), ConstraintType_::ThasMember(hm2)) => {
            has_member_compare(normalize_lists, hm1, hm2)
        }
        (ConstraintType_::ThasTypeMember(htm1), ConstraintType_::ThasTypeMember(htm2)) => {
            let HasTypeMember {
                id: id1,
                lower: lower1,
                upper: upper1,
            } = htm1;
            let HasTypeMember {
                id: id2,
                lower: lower2,
                upper: upper2,
            } = htm2;
            // (without ~normalize_lists, as in OCaml)
            chain_compare(id1.cmp(id2), || {
                chain_compare(ty_compare(None, lower1, lower2), || {
                    ty_compare(None, upper1, upper2)
                })
            })
        }
        (ConstraintType_::TcanIndex(ci1), ConstraintType_::TcanIndex(ci2)) => {
            can_index_compare(normalize_lists, ci1, ci2)
        }
        (ConstraintType_::TcanIndexAssign(cia1), ConstraintType_::TcanIndexAssign(cia2)) => {
            can_index_assign_compare(normalize_lists, cia1, cia2)
        }
        (ConstraintType_::TcanTraverse(ct1), ConstraintType_::TcanTraverse(ct2)) => {
            can_traverse_compare(normalize_lists, ct1, ct2)
        }
        (ConstraintType_::Tdestructure(d1), ConstraintType_::Tdestructure(d2)) => {
            destructure_compare(normalize_lists, d1, d2)
        }
        (
            ConstraintType_::TtypeSwitch {
                predicate: predicate1,
                ty_true: ty_true1,
                ty_false: ty_false1,
            },
            ConstraintType_::TtypeSwitch {
                predicate: predicate2,
                ty_true: ty_true2,
                ty_false: ty_false2,
            },
        ) => chain_compare(compare_type_predicate(predicate1, predicate2), || {
            chain_compare(
                ty_compare(Some(normalize_lists), ty_true1, ty_true2),
                || ty_compare(Some(normalize_lists), ty_false1, ty_false2),
            )
        }),
        (
            ConstraintType_::ThasConst {
                name: name1,
                ty: ty1,
            },
            ConstraintType_::ThasConst {
                name: name2,
                ty: ty2,
            },
        ) => chain_compare(name1.cmp(name2), || {
            ty_compare(Some(normalize_lists), ty1, ty2)
        }),
        (
            _,
            ConstraintType_::ThasMember(_)
            | ConstraintType_::TcanIndex(_)
            | ConstraintType_::TcanIndexAssign(_)
            | ConstraintType_::TcanTraverse(_)
            | ConstraintType_::Tdestructure(_)
            | ConstraintType_::ThasTypeMember(_)
            | ConstraintType_::TtypeSwitch { .. }
            | ConstraintType_::ThasConst { .. },
        ) => {
            // (ty2 first, as in OCaml)
            constraint_ty_con_ordinal(ty2).cmp(&constraint_ty_con_ordinal(ty1))
        }
    }
}

/// (Not in the `.mli`.)
pub fn constraint_ty_equal(
    normalize_lists: Option<bool>,
    ty1: &ConstraintType,
    ty2: &ConstraintType,
) -> bool {
    let normalize_lists = normalize_lists.unwrap_or(false);
    constraint_ty_compare(Some(normalize_lists), ty1, ty2) == Ordering::Equal
}

/// Ignore position and reason info.
///
/// (Not in the `.mli`.)
pub fn equal_internal_type(ty1: &InternalType, ty2: &InternalType) -> bool {
    match (ty1, ty2) {
        (InternalType::LoclType(ty1), InternalType::LoclType(ty2)) => {
            ty_equal(Some(true), ty1, ty2)
        }
        (InternalType::ConstraintType(ty1), InternalType::ConstraintType(ty2)) => {
            constraint_ty_equal(Some(true), ty1, ty2)
        }
        (_, InternalType::LoclType(_) | InternalType::ConstraintType(_)) => false,
    }
}

pub fn get_var_i(t: &InternalType) -> Option<isize> {
    match t {
        InternalType::LoclType(t) => crate::typing_defs_core::get_var(t),
        InternalType::ConstraintType(_) => None,
    }
}

pub fn is_tyvar_i(t: &InternalType) -> bool {
    get_var_i(t).is_some()
}

pub fn is_has_member(t: &ConstraintType) -> bool {
    let ConstraintType(_, ty_) = t;
    match &**ty_ {
        ConstraintType_::ThasMember(_) => true,
        _ => false,
    }
}

pub fn is_locl_type(t: &InternalType) -> bool {
    match t {
        InternalType::LoclType(_) => true,
        _ => false,
    }
}

pub fn reason(t: &InternalType) -> &Reason {
    match t {
        InternalType::LoclType(t) => get_reason(t),
        InternalType::ConstraintType(ConstraintType(r, _)) => r,
    }
}

pub fn is_constraint_type(t: &InternalType) -> bool {
    match t {
        InternalType::ConstraintType(_) => true,
        InternalType::LoclType(_) => false,
    }
}

/// `module InternalType`
pub mod internal_type {
    use super::InternalType;

    pub fn get_var(t: &InternalType) -> Option<isize> {
        match t {
            InternalType::LoclType(t) => crate::typing_defs_core::get_var(t),
            InternalType::ConstraintType(_) => None,
        }
    }

    pub fn is_var_v(t: &InternalType, v: isize) -> bool {
        match t {
            InternalType::LoclType(t) => crate::typing_defs_core::is_var_v(t, v),
            InternalType::ConstraintType(_) => false,
        }
    }

    pub fn is_not_var_v(t: &InternalType, v: isize) -> bool {
        !is_var_v(t, v)
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs;
    use oxidized::ast_defs::Tprim;

    use super::*;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::mk;

    fn r() -> Reason {
        crate::typing_reason::none()
    }

    fn prim(p: Tprim) -> Ty {
        mk((r(), Ty_::Tprim(p)))
    }

    fn union(tyl: Vec<Ty>) -> Ty {
        mk((r(), Ty_::Tunion(tyl)))
    }

    fn cty(ty_: ConstraintType_) -> ConstraintType {
        mk_constraint_type((r(), ty_))
    }

    fn destructure(required: Vec<Ty>, variadic: Option<Ty>) -> ConstraintType {
        cty(ConstraintType_::Tdestructure(Destructure {
            required,
            optional: vec![],
            variadic,
            kind: DestructureKind::ListDestructure,
        }))
    }

    fn has_const(name: &str, ty: Ty) -> ConstraintType {
        cty(ConstraintType_::ThasConst {
            name: name.to_string(),
            ty,
        })
    }

    fn has_member(name: &str, ty: Ty, class_id: nast::ClassId_) -> ConstraintType {
        cty(ConstraintType_::ThasMember(HasMember {
            name: ast_defs::Id(Pos::NONE, name.to_string()),
            type_: ty,
            class_id,
            method: None,
        }))
    }

    #[test]
    fn mk_and_deref() {
        let c = has_const("C", prim(Tprim::Tint));
        assert!(!is_has_member(&c));
        let (_, ty_) = deref_constraint_type(&c);
        assert!(matches!(ty_, ConstraintType_::ThasConst { .. }));
        let m = has_member("m", prim(Tprim::Tint), nast::ClassId_::CIself);
        assert!(is_has_member(&m));
    }

    #[test]
    fn compare_different_constructors_is_reversed() {
        // has_member (0), destructure (1), has_const (7): the OCaml subtracts
        // the ordinal of the first from the ordinal of the second.
        let m = has_member("m", prim(Tprim::Tint), nast::ClassId_::CIself);
        let d = destructure(vec![], None);
        let c = has_const("C", prim(Tprim::Tint));
        assert_eq!(constraint_ty_compare(None, &m, &d), Ordering::Greater);
        assert_eq!(constraint_ty_compare(None, &d, &m), Ordering::Less);
        assert_eq!(constraint_ty_compare(None, &d, &c), Ordering::Greater);
        assert_eq!(constraint_ty_compare(None, &c, &c), Ordering::Equal);
    }

    #[test]
    fn compare_has_member() {
        let a = has_member("a", prim(Tprim::Tint), nast::ClassId_::CIself);
        let b = has_member("b", prim(Tprim::Tint), nast::ClassId_::CIself);
        assert_eq!(constraint_ty_compare(None, &a, &b), Ordering::Less);
        let a_float = has_member("a", prim(Tprim::Tfloat), nast::ClassId_::CIself);
        assert_ne!(constraint_ty_compare(None, &a, &a_float), Ordering::Equal);
        // class_id_compare: CIparent (0) against CIself (1) is "greater"
        let a_parent = has_member("a", prim(Tprim::Tint), nast::ClassId_::CIparent);
        assert_eq!(
            constraint_ty_compare(None, &a_parent, &a),
            Ordering::Greater
        );
        assert!(constraint_ty_equal(None, &a, &a));
    }

    #[test]
    fn normalize_lists() {
        let u1 = || union(vec![prim(Tprim::Tint), prim(Tprim::Tfloat)]);
        let u2 = || union(vec![prim(Tprim::Tfloat), prim(Tprim::Tint)]);
        let c1 = has_const("C", u1());
        let c2 = has_const("C", u2());
        assert!(!constraint_ty_equal(None, &c1, &c2));
        assert!(constraint_ty_equal(Some(true), &c1, &c2));
        // the variadic type of a destructure is compared without normalize_lists
        let d1 = destructure(vec![u1()], None);
        let d2 = destructure(vec![u2()], None);
        assert!(constraint_ty_equal(Some(true), &d1, &d2));
        let d1 = destructure(vec![], Some(u1()));
        let d2 = destructure(vec![], Some(u2()));
        assert!(!constraint_ty_equal(Some(true), &d1, &d2));
        // equal_internal_type normalizes lists
        assert!(equal_internal_type(
            &InternalType::LoclType(u1()),
            &InternalType::LoclType(u2())
        ));
        assert!(equal_internal_type(
            &InternalType::ConstraintType(c1),
            &InternalType::ConstraintType(c2)
        ));
        assert!(!equal_internal_type(
            &InternalType::LoclType(u1()),
            &InternalType::ConstraintType(d1)
        ));
    }

    #[test]
    fn internal_types() {
        let v = InternalType::LoclType(mk((r(), Ty_::Tvar(3))));
        let c = InternalType::ConstraintType(has_const("C", prim(Tprim::Tint)));
        assert_eq!(get_var_i(&v), Some(3));
        assert_eq!(get_var_i(&c), None);
        assert!(is_tyvar_i(&v) && !is_tyvar_i(&c));
        assert!(is_locl_type(&v) && !is_locl_type(&c));
        assert!(is_constraint_type(&c) && !is_constraint_type(&v));
        assert_eq!(internal_type::get_var(&v), Some(3));
        assert!(internal_type::is_var_v(&v, 3));
        assert!(internal_type::is_not_var_v(&v, 4));
        assert!(internal_type::is_not_var_v(&c, 3));
        assert!(matches!(&**get_reason_i(&c), crate::typing_reason::T_::NoReason));
        assert!(matches!(&**reason(&v), crate::typing_reason::T_::NoReason));
    }
}
