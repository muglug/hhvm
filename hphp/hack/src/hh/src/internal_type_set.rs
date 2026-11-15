// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/internal_type_set.ml`. See `hh/PORTING.md`.
//!
//! An implementation of a set of types, using compare_locl_ty for a total
//! order. Typing-rule-equivalent types may get duplicated, as the equality
//! induced by compare_locl_ty does not expand Tvars and type aliases.
//!
//! The set is `Stdlib.Set.Make (Ty_)`: see `crate::typing_set` for why it is
//! `crate::typing_set::stdlib_set` (the trees of `set.ml`), and for the
//! functions and methods that [`T`] has.

use std::cmp::Ordering;

use crate::type_force_lazy_values;
use crate::typing_defs_constraints::InternalType;
use crate::typing_set::stdlib_set;
pub use crate::typing_set::stdlib_set::add;
pub use crate::typing_set::stdlib_set::cardinal;
pub use crate::typing_set::stdlib_set::choose_opt;
pub use crate::typing_set::stdlib_set::diff;
pub use crate::typing_set::stdlib_set::elements;
pub use crate::typing_set::stdlib_set::empty;
pub use crate::typing_set::stdlib_set::equal;
pub use crate::typing_set::stdlib_set::exists;
pub use crate::typing_set::stdlib_set::filter;
pub use crate::typing_set::stdlib_set::find_first_opt;
pub use crate::typing_set::stdlib_set::fold;
pub use crate::typing_set::stdlib_set::for_all;
pub use crate::typing_set::stdlib_set::inter;
pub use crate::typing_set::stdlib_set::is_empty;
pub use crate::typing_set::stdlib_set::iter;
pub use crate::typing_set::stdlib_set::map;
pub use crate::typing_set::stdlib_set::map_phys;
pub use crate::typing_set::stdlib_set::max_elt_opt;
pub use crate::typing_set::stdlib_set::mem;
pub use crate::typing_set::stdlib_set::min_elt_opt;
pub use crate::typing_set::stdlib_set::of_list;
pub use crate::typing_set::stdlib_set::partition;
pub use crate::typing_set::stdlib_set::remove;
pub use crate::typing_set::stdlib_set::singleton;
pub use crate::typing_set::stdlib_set::subset;
pub use crate::typing_set::stdlib_set::to_list;
pub use crate::typing_set::stdlib_set::union;

pub mod ty_ {
    use std::cmp::Ordering;

    use crate::typing_defs_constraints::InternalType;
    use crate::typing_defs_constraints::constraint_ty_compare;
    use crate::typing_defs_core::compare_locl_ty;

    /// `Internal_type_set.Ty_.t`
    pub type T = InternalType;

    pub fn compare(ty1: &InternalType, ty2: &InternalType) -> Ordering {
        match (ty1, ty2) {
            (InternalType::LoclType(ty1), InternalType::LoclType(ty2)) => {
                compare_locl_ty(None, ty1, ty2)
            }
            (InternalType::ConstraintType(ty1), InternalType::ConstraintType(ty2)) => {
                constraint_ty_compare(None, ty1, ty2)
            }
            (InternalType::LoclType(_), InternalType::ConstraintType(_)) => Ordering::Greater,
            (InternalType::ConstraintType(_), InternalType::LoclType(_)) => Ordering::Less,
        }
    }
}

/// `Ty_.compare`
impl stdlib_set::OrderedType for InternalType {
    fn compare(a: &Self, b: &Self) -> Ordering {
        ty_::compare(a, b)
    }
}

/// `Internal_type_set.elt`
pub type Elt = InternalType;

/// `Internal_type_set.t`
pub type T = stdlib_set::Set<InternalType>;

/// `Set.compare` (the module has no `compare` of its own: `Ty_.compare` is
/// [`ty_::compare`]).
pub fn compare(s1: &T, s2: &T) -> Ordering {
    stdlib_set::compare(s1, s2)
}

/// `f` is applied to the elements in increasing order, and its results are
/// added one by one to the empty set.
pub fn fold_map<Acc>(
    set: &T,
    init: Acc,
    mut f: impl FnMut(Acc, InternalType) -> (Acc, InternalType),
) -> (Acc, T) {
    let acc = init;
    fold(
        |x, (acc, res): (Acc, T)| {
            let (acc, x) = f(acc, x.clone());
            let res = add(x, &res);
            (acc, res)
        },
        set,
        (acc, empty()),
    )
}

/// The elements are printed by `Typing_defs_constraints.pp_internal_type`,
/// in `Format` boxes (`pp`, which takes a `Format.formatter`, is not here:
/// see `crate::typing_defs_core::pp`).
pub fn show(_t: &T) -> String {
    todo!(
        "Internal_type_set.show: needs a port of OCaml's Format (boxes and break hints) and Typing_defs_constraints.pp_internal_type"
    )
}

pub fn force_lazy_values(t: T) -> T {
    map(|ty| type_force_lazy_values::internal_type(ty.clone()), &t)
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;
    use oxidized::pos::Pos;

    use super::*;
    use crate::typing_defs_constraints::ConstraintType_;
    use crate::typing_defs_constraints::HasTypeMember;
    use crate::typing_defs_constraints::constraint_ty_compare;
    use crate::typing_defs_constraints::mk_constraint_type;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::compare_locl_ty;
    use crate::typing_defs_core::get_node;
    use crate::typing_defs_core::get_reason;
    use crate::typing_defs_core::mk;
    use crate::typing_reason;

    fn prim(p: Tprim) -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(p)))
    }

    fn var(n: isize) -> Ty {
        mk((typing_reason::none(), Ty_::Tvar(n)))
    }

    fn locl(ty: Ty) -> InternalType {
        InternalType::LoclType(ty)
    }

    fn has_type_member(id: &str, ty: Ty) -> InternalType {
        InternalType::ConstraintType(mk_constraint_type((
            typing_reason::none(),
            ConstraintType_::ThasTypeMember(HasTypeMember {
                id: id.to_string(),
                lower: ty.clone(),
                upper: ty,
            }),
        )))
    }

    fn has_const(name: &str, ty: Ty) -> InternalType {
        InternalType::ConstraintType(mk_constraint_type((
            typing_reason::none(),
            ConstraintType_::ThasConst {
                name: name.to_string(),
                ty,
            },
        )))
    }

    /// The same locl type with a reason that can be told from the others.
    fn marked(ty: &InternalType) -> InternalType {
        match ty {
            InternalType::LoclType(ty) => locl(mk((
                typing_reason::type_variable(Pos::NONE, 42),
                get_node(ty).clone(),
            ))),
            InternalType::ConstraintType(_) => panic!("locl types only"),
        }
    }

    fn is_marked(ty: &InternalType) -> bool {
        match ty {
            InternalType::LoclType(ty) => !matches!(&**get_reason(ty), crate::typing_reason::T_::NoReason),
            InternalType::ConstraintType(_) => false,
        }
    }

    fn eq(a: &InternalType, b: &InternalType) -> bool {
        ty_::compare(a, b) == Ordering::Equal
    }

    fn sample() -> Vec<InternalType> {
        vec![
            locl(prim(Tprim::Tfloat)),
            has_type_member("T", prim(Tprim::Tint)),
            locl(var(2)),
            has_const("C", prim(Tprim::Tint)),
            locl(prim(Tprim::Tint)),
            has_type_member("A", prim(Tprim::Tint)),
            locl(var(1)),
            has_const("B", prim(Tprim::Tfloat)),
        ]
    }

    #[test]
    fn the_order_is_ty_compare() {
        let tys = sample();
        for a in &tys {
            for b in &tys {
                let c = ty_::compare(a, b);
                let expected = match (a, b) {
                    (InternalType::LoclType(a), InternalType::LoclType(b)) => {
                        compare_locl_ty(None, a, b)
                    }
                    (InternalType::ConstraintType(a), InternalType::ConstraintType(b)) => {
                        constraint_ty_compare(None, a, b)
                    }
                    // Constraint types come before locl types.
                    (InternalType::LoclType(_), InternalType::ConstraintType(_)) => {
                        Ordering::Greater
                    }
                    (InternalType::ConstraintType(_), InternalType::LoclType(_)) => Ordering::Less,
                };
                assert_eq!(c, expected);
                assert_eq!(c.reverse(), ty_::compare(b, a));
                assert_eq!(
                    c,
                    <InternalType as stdlib_set::OrderedType>::compare(a, b)
                );
            }
        }
        assert_eq!(
            ty_::compare(&locl(var(1)), &has_const("C", var(1))),
            Ordering::Greater
        );
        assert_eq!(
            ty_::compare(&has_const("C", var(1)), &locl(var(1))),
            Ordering::Less
        );
        assert_eq!(
            ty_::compare(&locl(var(1)), &marked(&locl(var(1)))),
            Ordering::Equal
        );
        assert_eq!(ty_::compare(&locl(var(1)), &locl(var(2))), Ordering::Less);
    }

    #[test]
    fn iteration_is_ascending_constraint_types_first() {
        let tys = sample();
        let mut sorted = tys.clone();
        sorted.sort_by(ty_::compare);
        // The four constraint types, then the four locl types.
        assert!(
            sorted[..4]
                .iter()
                .all(|ty| matches!(ty, InternalType::ConstraintType(_)))
        );
        assert!(
            sorted[4..]
                .iter()
                .all(|ty| matches!(ty, InternalType::LoclType(_)))
        );

        let mut set = T::default();
        assert!(set.is_empty());
        for ty in &tys {
            assert!(set.insert(ty.clone()));
            stdlib_set::check_invariants(&set);
        }
        assert!(!set.is_empty());
        assert_eq!(set.len(), 8);
        let iterated: Vec<&InternalType> = set.iter().collect();
        assert_eq!(iterated.len(), sorted.len());
        for (a, b) in iterated.iter().zip(sorted.iter()) {
            assert!(eq(a, b));
        }
        // From the reversed list: the same elements in the same order.
        let set2: T = tys.iter().rev().cloned().collect();
        assert!(equal(&set, &set2));
        for (a, b) in elements(&set2).iter().zip(sorted.iter()) {
            assert!(eq(a, b));
        }
        // `Debug`
        assert!(format!("{:?}", T::default()) == "{}");
        assert!(format!("{:?}", set).starts_with('{'));
    }

    #[test]
    fn insert_keeps_the_element_that_is_there_and_union_follows_ocaml() {
        let int = locl(prim(Tprim::Tint));
        let float = locl(prim(Tprim::Tfloat));
        let mut set: T = std::iter::once(int.clone()).collect();
        assert!(!set.insert(marked(&int)));
        assert_eq!(set.len(), 1);
        assert!(!set.iter().any(is_marked));

        // A singleton and a singleton: the element of the first set.
        let u = union(&set, &singleton(marked(&int)));
        assert_eq!(u.len(), 1);
        assert!(!u.iter().any(is_marked));
        let u = union(&singleton(marked(&int)), &set);
        assert!(u.iter().all(is_marked));
        // A singleton and a larger set: the element of the larger set.
        let larger: T = [int.clone(), float.clone()].into_iter().collect();
        let u = union(&singleton(marked(&int)), &larger);
        assert_eq!(u.len(), 2);
        assert!(!u.iter().any(is_marked));
        let u = union(&larger, &singleton(marked(&int)));
        assert!(!u.iter().any(is_marked));
        // The arguments are untouched.
        assert_eq!(larger.len(), 2);
    }

    #[test]
    fn fold_map_goes_in_increasing_order() {
        let set: T = sample().into_iter().collect();
        let (seen, mapped) = fold_map(&set, vec![], |mut acc: Vec<InternalType>, ty| {
            acc.push(ty.clone());
            let ty = match ty {
                InternalType::LoclType(ty) => match get_node(&ty) {
                    Ty_::Tvar(n) => locl(var(n + 10)),
                    _ => locl(ty),
                },
                ty => ty,
            };
            (acc, ty)
        });
        for (a, b) in seen.iter().zip(set.iter()) {
            assert!(eq(a, b));
        }
        assert_eq!(seen.len(), 8);
        stdlib_set::check_invariants(&mapped);
        assert_eq!(mapped.len(), 8);
        assert!(mapped.contains(&locl(var(11))));
        assert!(mapped.contains(&locl(var(12))));
        assert!(!mapped.contains(&locl(var(1))));
        assert!(mem(&has_const("C", prim(Tprim::Tint)), &mapped));
    }

    #[test]
    fn force_lazy_values_keeps_the_set() {
        let set: T = sample().into_iter().collect();
        let forced = force_lazy_values(set.clone());
        assert!(equal(&set, &forced));
        assert_eq!(forced.len(), 8);
    }
}
