// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_logic.ml`. See `hh/PORTING.md`.
//!
//! `valid` is a value in OCaml and a function here: [`valid`]`()`.
//!
//! The functions that build a proposition out of others take them by value
//! (they store them); the ones that inspect a proposition take a reference.

use crate::tvid;
use crate::type_force_lazy_values;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::equal_internal_type;
use crate::typing_error;

/// Logical proposition about types
#[derive(Clone, Debug)]
pub enum SubtypeProp {
    /// IsSubtype(Some cd, ty1, ty2), if ty1 is a subtype of ty2 while potentially
    /// coercing to or from dynamic (depending on cd), written ty1 ~> ty2.
    /// IsSubtype(None, ty1, ty2) if ty1 is a subtype of ty2, written ty1 <: ty2
    IsSubtype(bool, InternalType, InternalType),
    /// Conjunction. Conj [] means "true"
    Conj(Vec<SubtypeProp>),
    /// Disjunction. Disj f [] means "false".  The error message function f
    /// wraps the error that should be produced in this case.
    Disj(Option<typing_error::T>, Vec<SubtypeProp>),
    /// A shape-splat relation that the expected-type subtyping entry point
    /// must defer. This is kept in the proposition so discarded disjuncts
    /// do not affect the selected subtype branch.
    AmbiguousShapeSplat(Vec<tvid::T>),
}

/// `[@@deriving show]`: `Format` boxes, as `crate::typing_defs_core::pp`
/// (`pp_subtype_prop`, which takes a `Format.formatter`, is not here).
pub fn show_subtype_prop(_x: &SubtypeProp) -> String {
    todo!(
        "Typing_logic.show_subtype_prop: needs a port of OCaml's Format (boxes and break hints), Typing_defs_constraints.pp_internal_type and Typing_error.pp"
    )
}

pub fn print(print_ty: impl Fn(&InternalType) -> String, prop: &SubtypeProp) -> String {
    fn print(print_ty: &dyn Fn(&InternalType) -> String, prop: &SubtypeProp) -> String {
        match prop {
            SubtypeProp::IsSubtype(_is_dynamic_aware, sub, super_) => {
                format!("{} <: {}", print_ty(sub), print_ty(super_))
            }
            SubtypeProp::Conj(l) if l.is_empty() => "true".to_string(),
            SubtypeProp::Conj(l) => l
                .iter()
                .map(|p| print(print_ty, p))
                .collect::<Vec<String>>()
                .join(" & "),
            SubtypeProp::Disj(_, l) if l.is_empty() => "false".to_string(),
            SubtypeProp::Disj(_, l) => l
                .iter()
                .map(|p| print(print_ty, p))
                .collect::<Vec<String>>()
                .join(" | "),
            SubtypeProp::AmbiguousShapeSplat(vars) => format!(
                "ambiguous_shape_splat({})",
                vars.iter()
                    .map(|v| tvid::show(*v))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        }
    }
    print(&print_ty, prop)
}

pub fn equal_subtype_prop(p1: &SubtypeProp, p2: &SubtypeProp) -> bool {
    match (p1, p2) {
        (SubtypeProp::IsSubtype(da1, ty1, ty1_), SubtypeProp::IsSubtype(da2, ty2, ty2_)) => {
            da1 == da2 && equal_internal_type(ty1, ty2) && equal_internal_type(ty1_, ty2_)
        }
        (SubtypeProp::Conj(ps1), SubtypeProp::Conj(ps2))
        | (SubtypeProp::Disj(_, ps1), SubtypeProp::Disj(_, ps2)) => {
            ps1.len() == ps2.len()
                && ps1
                    .iter()
                    .zip(ps2.iter())
                    .all(|(p1, p2)| equal_subtype_prop(p1, p2))
        }
        (SubtypeProp::AmbiguousShapeSplat(vars1), SubtypeProp::AmbiguousShapeSplat(vars2)) => {
            vars1.len() == vars2.len()
                && vars1
                    .iter()
                    .zip(vars2.iter())
                    .all(|(v1, v2)| tvid::equal(*v1, *v2))
        }
        (
            _,
            SubtypeProp::IsSubtype(..)
            | SubtypeProp::Conj(_)
            | SubtypeProp::Disj(..)
            | SubtypeProp::AmbiguousShapeSplat(_),
        ) => false,
    }
}

pub fn size(p: &SubtypeProp) -> isize {
    match p {
        SubtypeProp::IsSubtype(..) | SubtypeProp::AmbiguousShapeSplat(_) => 1,
        SubtypeProp::Conj(l) | SubtypeProp::Disj(_, l) => {
            let sizes = l.iter().map(size);
            sizes.fold(0, |a, b| a + b)
        }
    }
}

/// Sum of the sizes of the disjunctions.
pub fn n_disj(p: &SubtypeProp) -> isize {
    match p {
        SubtypeProp::IsSubtype(..) | SubtypeProp::AmbiguousShapeSplat(_) => 0,
        SubtypeProp::Conj(l) => {
            let n_disjs = l.iter().map(n_disj);
            n_disjs.fold(0, |a, b| a + b)
        }
        SubtypeProp::Disj(_, l) => {
            let n_disjs = l.iter().map(n_disj);
            l.len() as isize + n_disjs.fold(0, |a, b| a + b)
        }
    }
}

/// Sum of the sizes of the conjunctions.
pub fn n_conj(p: &SubtypeProp) -> isize {
    match p {
        SubtypeProp::IsSubtype(..) | SubtypeProp::AmbiguousShapeSplat(_) => 0,
        SubtypeProp::Disj(_, l) => {
            let n_conjs = l.iter().map(n_conj);
            n_conjs.fold(0, |a, b| a + b)
        }
        SubtypeProp::Conj(l) => {
            let n_conjs = l.iter().map(n_conj);
            l.len() as isize + n_conjs.fold(0, |a, b| a + b)
        }
    }
}

pub fn valid() -> SubtypeProp {
    SubtypeProp::Conj(vec![])
}

pub fn invalid(fail: Option<typing_error::T>) -> SubtypeProp {
    SubtypeProp::Disj(fail, vec![])
}

/// Is this proposition always true? (e.g. Conj [] but also Disj [Conj []; Disj (_, [])]
/// if not simplified
pub fn is_valid(p: &SubtypeProp) -> bool {
    match p {
        SubtypeProp::Conj(ps) => ps.iter().all(is_valid),
        SubtypeProp::Disj(_, ps) => ps.iter().any(is_valid),
        SubtypeProp::IsSubtype(..) | SubtypeProp::AmbiguousShapeSplat(_) => false,
    }
}

/// Is this proposition always false? e.g. Unsat _ but also Conj [Conj []; Disj (_, [])]
/// if not simplified
pub fn is_unsat(p: &SubtypeProp) -> bool {
    match p {
        SubtypeProp::Conj(ps) => ps.iter().any(is_unsat),
        SubtypeProp::Disj(_, ps) => ps.iter().all(is_unsat),
        SubtypeProp::IsSubtype(..) | SubtypeProp::AmbiguousShapeSplat(_) => false,
    }
}

/// `Some err` (a copy of the error of the disjunction, which may be `None`)
/// if the proposition is unsatisfiable.
pub fn get_error_if_unsat(p: &SubtypeProp) -> Option<Option<typing_error::T>> {
    match p {
        SubtypeProp::Disj(err, ps) => {
            if ps.iter().all(is_unsat) {
                Some(err.clone())
            } else {
                None
            }
        }
        SubtypeProp::Conj(ps) => ps.iter().find_map(get_error_if_unsat),
        SubtypeProp::IsSubtype(..) | SubtypeProp::AmbiguousShapeSplat(_) => None,
    }
}

/// `Conj []` ("true", as [`valid`] builds it).
#[inline]
pub fn is_conj_nil(p: &SubtypeProp) -> bool {
    matches!(p, SubtypeProp::Conj(ps) if ps.is_empty())
}

/// `intersect_opt (List.filter_opt errs)` without building the lists when
/// at most one error is present.
fn intersect_opt3(
    e1: Option<typing_error::T>,
    e2: Option<typing_error::T>,
    e3: Option<typing_error::T>,
) -> Option<typing_error::T> {
    match (e1, e2, e3) {
        (None, None, None) => None,
        (Some(e), None, None) | (None, Some(e), None) | (None, None, Some(e)) => Some(e),
        (e1, e2, e3) => typing_error::intersect_opt(filter_opt(vec![e1, e2, e3])),
    }
}

/// Smart constructor for binary conjunction
pub fn conj(p1: SubtypeProp, p2: SubtypeProp) -> SubtypeProp {
    // Not in the OCaml (typing_logic.ml, `conj`), which compares the two
    // propositions first: with `true` on either side, the result is the other
    // side (which the comparison below gives as well when both are `true`),
    // without the structural `equal_subtype_prop` walk of the other side.
    // `conj` runs at every `&&&` step of subtyping, mostly with `valid` on one
    // side.
    if is_conj_nil(&p1) {
        return p2;
    }
    if is_conj_nil(&p2) {
        return p1;
    }
    if equal_subtype_prop(&p1, &p2) {
        p1
    } else {
        match (p1, p2) {
            (SubtypeProp::Conj(ps), p) if ps.is_empty() => p,
            (p, SubtypeProp::Conj(ps)) if ps.is_empty() => p,
            (SubtypeProp::Conj(mut ps1), SubtypeProp::Conj(ps2)) => {
                ps1.extend(ps2);
                SubtypeProp::Conj(ps1)
            }
            // Preserve the order to maintain legacy behaviour. If two errors share the
            // same position then the first one to be emitted wins.
            // TODO: consider relaxing this behaviour
            (SubtypeProp::Conj(mut ps), p2) => {
                ps.push(p2);
                SubtypeProp::Conj(ps)
            }
            (p1, SubtypeProp::Conj(mut ps)) => {
                ps.insert(0, p1);
                SubtypeProp::Conj(ps)
            }
            (p1, p2) => SubtypeProp::Conj(vec![p1, p2]),
        }
    }
}

pub fn conj_list(ps: Vec<SubtypeProp>) -> SubtypeProp {
    ps.into_iter().fold(SubtypeProp::Conj(vec![]), conj)
}

fn add_prop(p: SubtypeProp, mut ps: Vec<SubtypeProp>) -> Vec<SubtypeProp> {
    if ps.iter().any(|p_| equal_subtype_prop(&p, p_)) {
        ps
    } else {
        ps.insert(0, p);
        ps
    }
}

fn append_prop(mut ps: Vec<SubtypeProp>, p: SubtypeProp) -> Vec<SubtypeProp> {
    if ps.iter().any(|p_| equal_subtype_prop(&p, p_)) {
        ps
    } else {
        ps.push(p);
        ps
    }
}

enum PropResult {
    Valid,
    Invalid(Option<typing_error::T>),
    Unknown,
}

fn to_prop_result(prop: &SubtypeProp) -> PropResult {
    if is_valid(prop) {
        PropResult::Valid
    } else {
        match get_error_if_unsat(prop) {
            Some(err) => PropResult::Invalid(err),
            _ => PropResult::Unknown,
        }
    }
}

/// `List.filter_opt`
fn filter_opt(errs: Vec<Option<typing_error::T>>) -> Vec<typing_error::T> {
    errs.into_iter().flatten().collect()
}

fn append_disj(fail: Option<typing_error::T>, p1: SubtypeProp, p2: SubtypeProp) -> SubtypeProp {
    match (p1, p2) {
        (SubtypeProp::Disj(err1, ps1), SubtypeProp::Disj(err2, ps2)) => {
            let disj_err = intersect_opt3(fail, err1, err2);
            SubtypeProp::Disj(
                disj_err,
                ps2.into_iter().fold(ps1, append_prop),
            )
        }
        (p, SubtypeProp::Disj(err, ps)) => {
            let disj_err = intersect_opt3(fail, err, None);
            SubtypeProp::Disj(disj_err, add_prop(p, ps))
        }
        (SubtypeProp::Disj(err, ps), p) => {
            let disj_err = intersect_opt3(fail, err, None);
            SubtypeProp::Disj(disj_err, append_prop(ps, p))
        }
        (p1, p2) => SubtypeProp::Disj(fail, vec![p1, p2]),
    }
}

/// Smart constructor for binary disjunction
pub fn disj(fail: Option<typing_error::T>, p1: SubtypeProp, p2: SubtypeProp) -> SubtypeProp {
    if equal_subtype_prop(&p1, &p2) {
        p1
    } else {
        match (to_prop_result(&p1), to_prop_result(&p2)) {
            (PropResult::Valid, _) | (_, PropResult::Valid) => valid(),
            (PropResult::Invalid(err1), PropResult::Invalid(err2)) => {
                let disj_err = intersect_opt3(fail, err1, err2);
                invalid(disj_err)
            }
            (PropResult::Invalid(err), PropResult::Unknown) => {
                let disj_err = intersect_opt3(fail, err, None);
                SubtypeProp::Disj(disj_err, vec![p2])
            }
            (PropResult::Unknown, PropResult::Invalid(err)) => {
                let disj_err = intersect_opt3(fail, err, None);
                SubtypeProp::Disj(disj_err, vec![p1])
            }
            (PropResult::Unknown, PropResult::Unknown) => append_disj(fail, p1, p2),
        }
    }
}

pub fn force_lazy_values(prop: SubtypeProp) -> SubtypeProp {
    match prop {
        SubtypeProp::IsSubtype(dir, ty1, ty2) => SubtypeProp::IsSubtype(
            dir,
            type_force_lazy_values::internal_type(ty1),
            type_force_lazy_values::internal_type(ty2),
        ),
        SubtypeProp::Conj(props) => {
            SubtypeProp::Conj(props.into_iter().map(force_lazy_values).collect())
        }
        SubtypeProp::Disj(_err, props) => SubtypeProp::Disj(
            // TODO force lazy values in error
            None,
            props.into_iter().map(force_lazy_values).collect(),
        ),
        SubtypeProp::AmbiguousShapeSplat(_) => prop,
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::SubtypeProp::*;
    use super::*;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::mk;
    use crate::typing_reason;

    fn prim(p: Tprim) -> InternalType {
        InternalType::LoclType(mk((typing_reason::none(), Ty_::Tprim(p))))
    }

    fn var(n: isize) -> InternalType {
        InternalType::LoclType(mk((typing_reason::none(), Ty_::Tvar(n))))
    }

    /// `#n <: int`
    fn sub(n: isize) -> SubtypeProp {
        IsSubtype(false, var(n), prim(Tprim::Tint))
    }

    fn show(p: &SubtypeProp) -> String {
        print(
            |ty| match ty {
                InternalType::LoclType(ty) => match crate::typing_defs_core::get_node(ty) {
                    Ty_::Tvar(n) => format!("#{}", n),
                    Ty_::Tprim(Tprim::Tint) => "int".to_string(),
                    _ => "?".to_string(),
                },
                InternalType::ConstraintType(_) => "?".to_string(),
            },
            p,
        )
    }

    /// The structure, with the error of a disjunction as `!` when it has one.
    fn structure(p: &SubtypeProp) -> String {
        match p {
            IsSubtype(..) | AmbiguousShapeSplat(_) => show(p),
            Conj(ps) => format!(
                "Conj[{}]",
                ps.iter().map(structure).collect::<Vec<_>>().join("; ")
            ),
            Disj(err, ps) => format!(
                "Disj{}[{}]",
                if err.is_some() { "!" } else { "" },
                ps.iter().map(structure).collect::<Vec<_>>().join("; ")
            ),
        }
    }

    fn some_error() -> typing_error::T {
        typing_error::T::Multiple(vec![])
    }

    #[test]
    fn print_() {
        assert_eq!(show(&valid()), "true");
        assert_eq!(show(&invalid(None)), "false");
        assert_eq!(show(&sub(1)), "#1 <: int");
        assert_eq!(show(&Conj(vec![sub(1), sub(2)])), "#1 <: int & #2 <: int");
        assert_eq!(
            show(&Disj(None, vec![sub(1), Conj(vec![])])),
            "#1 <: int | true"
        );
        assert_eq!(
            show(&AmbiguousShapeSplat(vec![3, 14])),
            "ambiguous_shape_splat(3, 14)"
        );
        assert_eq!(show(&AmbiguousShapeSplat(vec![])), "ambiguous_shape_splat()");
    }

    #[test]
    fn equal() {
        assert!(equal_subtype_prop(&sub(1), &sub(1)));
        assert!(!equal_subtype_prop(&sub(1), &sub(2)));
        // The flag counts.
        assert!(!equal_subtype_prop(
            &IsSubtype(true, var(1), var(2)),
            &IsSubtype(false, var(1), var(2))
        ));
        // The error of a disjunction does not.
        assert!(equal_subtype_prop(
            &Disj(Some(some_error()), vec![sub(1)]),
            &Disj(None, vec![sub(1)])
        ));
        assert!(!equal_subtype_prop(
            &Disj(None, vec![sub(1)]),
            &Conj(vec![sub(1)])
        ));
        assert!(!equal_subtype_prop(
            &Conj(vec![sub(1)]),
            &Conj(vec![sub(1), sub(2)])
        ));
        assert!(equal_subtype_prop(
            &AmbiguousShapeSplat(vec![1, 2]),
            &AmbiguousShapeSplat(vec![1, 2])
        ));
        assert!(!equal_subtype_prop(
            &AmbiguousShapeSplat(vec![1, 2]),
            &AmbiguousShapeSplat(vec![2, 1])
        ));
        assert!(!equal_subtype_prop(&AmbiguousShapeSplat(vec![]), &valid()));
    }

    #[test]
    fn sizes() {
        let p = Conj(vec![
            sub(1),
            Disj(None, vec![sub(2), sub(3), Conj(vec![sub(4), sub(5)])]),
            AmbiguousShapeSplat(vec![1]),
        ]);
        assert_eq!(size(&p), 6);
        assert_eq!(n_disj(&p), 3);
        assert_eq!(n_conj(&p), 5);
        assert_eq!(size(&valid()), 0);
    }

    #[test]
    fn valid_and_unsat() {
        assert!(is_valid(&valid()));
        assert!(!is_unsat(&valid()));
        assert!(is_unsat(&invalid(None)));
        assert!(!is_valid(&invalid(None)));
        assert!(!is_valid(&sub(1)));
        assert!(!is_unsat(&sub(1)));
        assert!(is_valid(&Disj(None, vec![sub(1), Conj(vec![])])));
        assert!(is_unsat(&Conj(vec![Conj(vec![]), Disj(None, vec![])])));
        assert!(!is_unsat(&AmbiguousShapeSplat(vec![1])));

        assert!(get_error_if_unsat(&valid()).is_none());
        assert!(get_error_if_unsat(&sub(1)).is_none());
        // Unsatisfiable without an error, and with one.
        assert!(matches!(get_error_if_unsat(&invalid(None)), Some(None)));
        assert!(matches!(
            get_error_if_unsat(&invalid(Some(some_error()))),
            Some(Some(_))
        ));
        // The first unsatisfiable conjunct.
        assert!(matches!(
            get_error_if_unsat(&Conj(vec![
                sub(1),
                invalid(None),
                invalid(Some(some_error()))
            ])),
            Some(None)
        ));
        // A disjunction is unsatisfiable when all its disjuncts are.
        assert!(matches!(
            get_error_if_unsat(&Disj(Some(some_error()), vec![invalid(None)])),
            Some(Some(_))
        ));
        assert!(get_error_if_unsat(&Disj(Some(some_error()), vec![sub(1)])).is_none());
    }

    #[test]
    fn conj_() {
        assert_eq!(structure(&conj(sub(1), sub(1))), "#1 <: int");
        assert_eq!(structure(&conj(valid(), sub(1))), "#1 <: int");
        assert_eq!(structure(&conj(sub(1), valid())), "#1 <: int");
        assert_eq!(structure(&conj(valid(), valid())), "Conj[]");
        assert_eq!(
            structure(&conj(Conj(vec![sub(1), sub(2)]), Conj(vec![sub(3)]))),
            "Conj[#1 <: int; #2 <: int; #3 <: int]"
        );
        assert_eq!(
            structure(&conj(Conj(vec![sub(1), sub(2)]), sub(3))),
            "Conj[#1 <: int; #2 <: int; #3 <: int]"
        );
        assert_eq!(
            structure(&conj(sub(3), Conj(vec![sub(1), sub(2)]))),
            "Conj[#3 <: int; #1 <: int; #2 <: int]"
        );
        assert_eq!(
            structure(&conj(sub(1), sub(2))),
            "Conj[#1 <: int; #2 <: int]"
        );
        assert_eq!(
            structure(&conj(sub(1), invalid(None))),
            "Conj[#1 <: int; Disj[]]"
        );
        assert_eq!(
            structure(&conj_list(vec![sub(1), valid(), sub(2), sub(1), sub(3)])),
            // `sub(1)` again is not equal to the conjunction so far.
            "Conj[#1 <: int; #2 <: int; #1 <: int; #3 <: int]"
        );
        assert_eq!(structure(&conj_list(vec![])), "Conj[]");
    }

    #[test]
    fn disj_() {
        assert_eq!(structure(&disj(None, sub(1), sub(1))), "#1 <: int");
        assert_eq!(structure(&disj(None, valid(), sub(1))), "Conj[]");
        assert_eq!(
            structure(&disj(Some(some_error()), sub(1), valid())),
            "Conj[]"
        );
        // Two empty disjunctions are equal whatever their errors: the first.
        assert_eq!(
            structure(&disj(None, invalid(None), invalid(Some(some_error())))),
            "Disj[]"
        );
        // Both unsatisfiable: the errors are intersected.
        assert_eq!(
            structure(&disj(
                None,
                Conj(vec![invalid(None)]),
                invalid(Some(some_error()))
            )),
            "Disj![]"
        );
        assert_eq!(
            structure(&disj(None, Conj(vec![invalid(None)]), invalid(None))),
            "Disj[]"
        );
        match disj(
            Some(some_error()),
            invalid(Some(some_error())),
            Conj(vec![invalid(Some(some_error()))]),
        ) {
            Disj(Some(typing_error::T::Intersection(errs)), ps) => {
                assert_eq!(errs.len(), 3);
                assert!(ps.is_empty());
            }
            p => panic!("unexpected {:?}", p),
        }
        // One unsatisfiable: the other one alone, in a disjunction.
        assert_eq!(
            structure(&disj(None, invalid(Some(some_error())), sub(1))),
            "Disj![#1 <: int]"
        );
        assert_eq!(
            structure(&disj(None, sub(1), invalid(None))),
            "Disj[#1 <: int]"
        );
        // Neither.
        assert_eq!(
            structure(&disj(None, sub(1), sub(2))),
            "Disj[#1 <: int; #2 <: int]"
        );
        // `add_prop` puts a disjunct on the left first, `append_prop` one on
        // the right last, and both drop it if it is already there.
        assert_eq!(
            structure(&disj(
                None,
                sub(3),
                Disj(Some(some_error()), vec![sub(1), sub(2)])
            )),
            "Disj![#3 <: int; #1 <: int; #2 <: int]"
        );
        assert_eq!(
            structure(&disj(None, Disj(None, vec![sub(1), sub(2)]), sub(3))),
            "Disj[#1 <: int; #2 <: int; #3 <: int]"
        );
        assert_eq!(
            structure(&disj(None, Disj(None, vec![sub(1), sub(2)]), sub(2))),
            "Disj[#1 <: int; #2 <: int]"
        );
        assert_eq!(
            structure(&disj(
                None,
                Disj(None, vec![sub(1), sub(2)]),
                Disj(None, vec![sub(2), sub(3), sub(4)])
            )),
            "Disj[#1 <: int; #2 <: int; #3 <: int; #4 <: int]"
        );
    }

    #[test]
    fn force_lazy_values_drops_the_errors() {
        let p = Conj(vec![
            sub(1),
            Disj(Some(some_error()), vec![sub(2), AmbiguousShapeSplat(vec![7])]),
        ]);
        let forced = force_lazy_values(p.clone());
        assert!(equal_subtype_prop(&p, &forced));
        assert_eq!(
            structure(&forced),
            "Conj[#1 <: int; Disj[#2 <: int; ambiguous_shape_splat(7)]]"
        );
    }
}
