// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `class_refinement.ml`. See `hh/PORTING.md`.
//!
//! The OCaml functions are polymorphic in the phase. As in
//! `crate::typing_defs_core`, the functions with the OCaml names are for the
//! localized phase ([`ClassRefinement`], whose `cr_consts` is a `BTreeMap`
//! keyed by the name, as `S_map`), and those for the declared phase
//! (`ty::decl::ClassRefinement`, whose `consts` is a `BTreeMap` keyed by
//! `TypeConstName`, ordered by the string as `S_map` is) have `_decl`
//! appended. `fold_map` exists only for the declared phase, as in the `.mli`;
//! `map` is from a phase to the same phase (the OCaml callers map decl types
//! to decl types).

use crate::typing_defs_core::ClassRefinement;
use crate::typing_defs_core::DeclClassRefinement;
use crate::typing_defs_core::DeclRefinedConst;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::RefinedConst;
use crate::typing_defs_core::RefinedConstBound;
use crate::typing_defs_core::RefinedConstBounds;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::refined_const_kind_str;

pub fn is_empty(cr: &ClassRefinement) -> bool {
    cr.cr_consts.is_empty()
}

pub fn has_refined_const<P>(pos_id: &(P, String), cr: &ClassRefinement) -> bool {
    cr.cr_consts.contains_key(&pos_id.1)
}

pub fn get_refined_const<P>(pos_id: &(P, String), cr: &ClassRefinement) -> Option<RefinedConst> {
    let (_, id) = pos_id;
    cr.cr_consts.get(id).cloned()
}

pub fn fold_refined_consts<Acc>(
    cr: &ClassRefinement,
    init: Acc,
    mut f: impl FnMut(&str, &RefinedConst, Acc) -> Acc,
) -> Acc {
    // `S_map.fold f cr.cr_consts acc`: in increasing order of the names.
    let mut acc = init;
    for (name, rc) in cr.cr_consts.iter() {
        acc = f(name, rc, acc);
    }
    acc
}

pub fn add_refined_const(id: String, tr: RefinedConst, cr: ClassRefinement) -> ClassRefinement {
    fn combine(r1: RefinedConst, r2: RefinedConst) -> RefinedConst {
        // Note: previous stages ensure that is_ctx are compatible
        let rc_bound = match (r1.bound, r2.bound) {
            (exact @ RefinedConstBound::TRexact(_), _)
            | (_, exact @ RefinedConstBound::TRexact(_)) => exact,
            (
                RefinedConstBound::TRloose(RefinedConstBounds {
                    lower: ls1,
                    upper: us1,
                }),
                RefinedConstBound::TRloose(RefinedConstBounds {
                    lower: ls2,
                    upper: us2,
                }),
            ) => RefinedConstBound::TRloose(RefinedConstBounds {
                lower: ls1.into_iter().chain(ls2).collect(),
                upper: us1.into_iter().chain(us2).collect(),
            }),
        };
        RefinedConst {
            bound: rc_bound,
            is_ctx: r1.is_ctx,
        }
    }
    // `S_map.add ~combine id tr cr.cr_consts`: `combine old_value new_value`
    // when the name is already there.
    let mut cr_consts = cr.cr_consts;
    let rc = match cr_consts.remove(&id) {
        None => tr,
        Some(old_value) => combine(old_value, tr),
    };
    cr_consts.insert(id, rc);
    ClassRefinement { cr_consts }
}

fn map_refined_const(
    f: &mut impl FnMut(Ty) -> Ty,
    RefinedConst {
        bound: rc_bound,
        is_ctx: rc_is_ctx,
    }: RefinedConst,
) -> RefinedConst {
    let rc_bound = match rc_bound {
        RefinedConstBound::TRexact(ty) => RefinedConstBound::TRexact(f(ty)),
        RefinedConstBound::TRloose(RefinedConstBounds {
            lower: ls,
            upper: us,
        }) => {
            // `TRloose { tr_lower = List.map ls ~f; tr_upper = List.map us ~f }`:
            // OCaml evaluates the fields of a record from right to left, so
            // the upper bounds are mapped first (each list from left to
            // right).
            let upper: Vec<Ty> = us.into_iter().map(&mut *f).collect();
            let lower: Vec<Ty> = ls.into_iter().map(&mut *f).collect();
            RefinedConstBound::TRloose(RefinedConstBounds { lower, upper })
        }
    };
    RefinedConst {
        bound: rc_bound,
        is_ctx: rc_is_ctx,
    }
}

pub fn map(mut f: impl FnMut(Ty) -> Ty, cr: ClassRefinement) -> ClassRefinement {
    // `S_map.map`: in increasing order of the names.
    let ClassRefinement { cr_consts: rcs } = cr;
    ClassRefinement {
        cr_consts: rcs
            .into_iter()
            .map(|(name, rc)| (name, map_refined_const(&mut f, rc)))
            .collect(),
    }
}

fn fold_map_refined_const<Acc>(
    f: &mut impl FnMut(Acc, DeclTy) -> (Acc, DeclTy),
    acc: Acc,
    _name: &str,
    rc: DeclRefinedConst,
) -> (Acc, DeclRefinedConst) {
    use ty::decl::RefinedConstBound as B;
    let ty::decl::RefinedConst {
        bound: rc_bound,
        is_ctx: rc_is_ctx,
    } = rc;
    let (acc, rc_bound) = match rc_bound {
        B::Exact(ty) => {
            let (acc, ty) = f(acc, ty);
            (acc, B::Exact(ty))
        }
        B::Loose(ty::decl::RefinedConstBounds {
            lower: ls,
            upper: us,
        }) => {
            // `List.fold_map ~f ~init:acc ls`, then `us`
            let mut acc = acc;
            let mut lower = Vec::with_capacity(ls.len());
            for ty in ls.into_vec() {
                let (acc_, ty) = f(acc, ty);
                acc = acc_;
                lower.push(ty);
            }
            let mut upper = Vec::with_capacity(us.len());
            for ty in us.into_vec() {
                let (acc_, ty) = f(acc, ty);
                acc = acc_;
                upper.push(ty);
            }
            (
                acc,
                B::Loose(ty::decl::RefinedConstBounds {
                    lower: lower.into_boxed_slice(),
                    upper: upper.into_boxed_slice(),
                }),
            )
        }
    };
    (
        acc,
        ty::decl::RefinedConst {
            bound: rc_bound,
            is_ctx: rc_is_ctx,
        },
    )
}

/// (Declared phase only, as in the `.mli`.)
pub fn fold_map<Acc>(
    mut f: impl FnMut(Acc, DeclTy) -> (Acc, DeclTy),
    acc: Acc,
    cr: DeclClassRefinement,
) -> (Acc, DeclClassRefinement) {
    // `S_map.map_env (fold_map_refined_const f) acc rcs`: in increasing order
    // of the names.
    let ty::decl::ClassRefinement { consts: rcs } = cr;
    let mut acc = acc;
    let mut consts = std::collections::BTreeMap::new();
    for (name, rc) in rcs {
        let (acc_, rc) = fold_map_refined_const(&mut f, acc, name.as_str(), rc);
        acc = acc_;
        consts.insert(name, rc);
    }
    (acc, ty::decl::ClassRefinement { consts })
}

fn fold_refined_const<Acc>(
    RefinedConst {
        bound: rc_bound,
        is_ctx: _,
    }: &RefinedConst,
    init: Acc,
    f: &mut impl FnMut(Acc, &Ty) -> Acc,
) -> Acc {
    match rc_bound {
        RefinedConstBound::TRexact(ty) => f(init, ty),
        RefinedConstBound::TRloose(RefinedConstBounds {
            lower: ls,
            upper: us,
        }) => {
            let mut acc = init;
            for ty in ls {
                acc = f(acc, ty);
            }
            for ty in us {
                acc = f(acc, ty);
            }
            acc
        }
    }
}

pub fn fold<Acc>(cr: &ClassRefinement, init: Acc, mut f: impl FnMut(Acc, &Ty) -> Acc) -> Acc {
    let ClassRefinement { cr_consts: rcs } = cr;
    let mut acc = init;
    for (_, rc) in rcs.iter() {
        acc = fold_refined_const(rc, acc, &mut f);
    }
    acc
}

pub fn iter(mut f: impl FnMut(&Ty), r: &ClassRefinement) {
    fold(r, (), |(), ty| f(ty))
}

pub fn to_string(ty_to_string: impl Fn(&Ty) -> String, cr: &ClassRefinement) -> String {
    let rc_to_string = |rc: &RefinedConst| match &rc.bound {
        RefinedConstBound::TRexact(ty) => "= ".to_string() + &ty_to_string(ty),
        RefinedConstBound::TRloose(RefinedConstBounds {
            lower: ls,
            upper: us,
        }) => {
            let l1 = ls.iter().map(|ty| "as ".to_string() + &ty_to_string(ty));
            let l2 = us.iter().map(|ty| "super ".to_string() + &ty_to_string(ty));
            l1.chain(l2).collect::<Vec<String>>().join(" ")
        }
    };
    // `S_map.fold f cr.cr_consts []` with `f` consing: in decreasing order of
    // the names.
    let mut members_list: Vec<String> = vec![];
    for (name, rc) in cr.cr_consts.iter() {
        let kind = refined_const_kind_str(rc);
        members_list.insert(0, format!("{} {} {}", kind, name, rc_to_string(rc)));
    }
    "{".to_string() + &members_list.join("; ") + "}"
}

// ---------------------------------------------------------------------------
// The declared phase
// ---------------------------------------------------------------------------

/// `is_empty` on a decl refinement.
pub fn is_empty_decl(cr: &DeclClassRefinement) -> bool {
    cr.consts.is_empty()
}

/// `has_refined_const` on a decl refinement.
pub fn has_refined_const_decl<P>(pos_id: &(P, String), cr: &DeclClassRefinement) -> bool {
    cr.consts.contains_key(&pos::TypeConstName::new(&pos_id.1))
}

/// `get_refined_const` on a decl refinement.
pub fn get_refined_const_decl<P>(
    pos_id: &(P, String),
    cr: &DeclClassRefinement,
) -> Option<DeclRefinedConst> {
    let (_, id) = pos_id;
    cr.consts.get(&pos::TypeConstName::new(id)).cloned()
}

/// `fold_refined_consts` on a decl refinement.
pub fn fold_refined_consts_decl<Acc>(
    cr: &DeclClassRefinement,
    init: Acc,
    mut f: impl FnMut(&str, &DeclRefinedConst, Acc) -> Acc,
) -> Acc {
    let mut acc = init;
    for (name, rc) in cr.consts.iter() {
        acc = f(name.as_str(), rc, acc);
    }
    acc
}

/// `add_refined_const` on a decl refinement.
pub fn add_refined_const_decl(
    id: String,
    tr: DeclRefinedConst,
    cr: DeclClassRefinement,
) -> DeclClassRefinement {
    use ty::decl::RefinedConstBound as B;
    fn combine(r1: DeclRefinedConst, r2: DeclRefinedConst) -> DeclRefinedConst {
        // Note: previous stages ensure that is_ctx are compatible
        let rc_bound = match (r1.bound, r2.bound) {
            (exact @ B::Exact(_), _) | (_, exact @ B::Exact(_)) => exact,
            (
                B::Loose(ty::decl::RefinedConstBounds {
                    lower: ls1,
                    upper: us1,
                }),
                B::Loose(ty::decl::RefinedConstBounds {
                    lower: ls2,
                    upper: us2,
                }),
            ) => B::Loose(ty::decl::RefinedConstBounds {
                lower: ls1.into_vec().into_iter().chain(ls2.into_vec()).collect(),
                upper: us1.into_vec().into_iter().chain(us2.into_vec()).collect(),
            }),
        };
        ty::decl::RefinedConst {
            bound: rc_bound,
            is_ctx: r1.is_ctx,
        }
    }
    let mut consts = cr.consts;
    let key = pos::TypeConstName::new(&id);
    let rc = match consts.remove(&key) {
        None => tr,
        Some(old_value) => combine(old_value, tr),
    };
    consts.insert(key, rc);
    ty::decl::ClassRefinement { consts }
}

fn map_refined_const_decl(
    f: &mut impl FnMut(DeclTy) -> DeclTy,
    rc: DeclRefinedConst,
) -> DeclRefinedConst {
    use ty::decl::RefinedConstBound as B;
    let ty::decl::RefinedConst {
        bound: rc_bound,
        is_ctx: rc_is_ctx,
    } = rc;
    let rc_bound = match rc_bound {
        B::Exact(ty) => B::Exact(f(ty)),
        B::Loose(ty::decl::RefinedConstBounds {
            lower: ls,
            upper: us,
        }) => {
            // As in `map_refined_const`: the upper bounds first.
            let upper: Box<[DeclTy]> = us.into_vec().into_iter().map(&mut *f).collect();
            let lower: Box<[DeclTy]> = ls.into_vec().into_iter().map(&mut *f).collect();
            B::Loose(ty::decl::RefinedConstBounds { lower, upper })
        }
    };
    ty::decl::RefinedConst {
        bound: rc_bound,
        is_ctx: rc_is_ctx,
    }
}

/// `map` on a decl refinement.
pub fn map_decl(
    mut f: impl FnMut(DeclTy) -> DeclTy,
    cr: DeclClassRefinement,
) -> DeclClassRefinement {
    let ty::decl::ClassRefinement { consts: rcs } = cr;
    ty::decl::ClassRefinement {
        consts: rcs
            .into_iter()
            .map(|(name, rc)| (name, map_refined_const_decl(&mut f, rc)))
            .collect(),
    }
}

fn fold_refined_const_decl<Acc>(
    rc: &DeclRefinedConst,
    init: Acc,
    f: &mut impl FnMut(Acc, &DeclTy) -> Acc,
) -> Acc {
    use ty::decl::RefinedConstBound as B;
    match &rc.bound {
        B::Exact(ty) => f(init, ty),
        B::Loose(ty::decl::RefinedConstBounds {
            lower: ls,
            upper: us,
        }) => {
            let mut acc = init;
            for ty in ls.iter() {
                acc = f(acc, ty);
            }
            for ty in us.iter() {
                acc = f(acc, ty);
            }
            acc
        }
    }
}

/// `fold` on a decl refinement.
pub fn fold_decl<Acc>(
    cr: &DeclClassRefinement,
    init: Acc,
    mut f: impl FnMut(Acc, &DeclTy) -> Acc,
) -> Acc {
    let mut acc = init;
    for (_, rc) in cr.consts.iter() {
        acc = fold_refined_const_decl(rc, acc, &mut f);
    }
    acc
}

/// `iter` on a decl refinement.
pub fn iter_decl(mut f: impl FnMut(&DeclTy), r: &DeclClassRefinement) {
    fold_decl(r, (), |(), ty| f(ty))
}

/// `to_string` on a decl refinement.
pub fn to_string_decl(
    ty_to_string: impl Fn(&DeclTy) -> String,
    cr: &DeclClassRefinement,
) -> String {
    use ty::decl::RefinedConstBound as B;
    let rc_to_string = |rc: &DeclRefinedConst| match &rc.bound {
        B::Exact(ty) => "= ".to_string() + &ty_to_string(ty),
        B::Loose(ty::decl::RefinedConstBounds {
            lower: ls,
            upper: us,
        }) => {
            let l1 = ls.iter().map(|ty| "as ".to_string() + &ty_to_string(ty));
            let l2 = us.iter().map(|ty| "super ".to_string() + &ty_to_string(ty));
            l1.chain(l2).collect::<Vec<String>>().join(" ")
        }
    };
    let mut members_list: Vec<String> = vec![];
    for (name, rc) in cr.consts.iter() {
        // `refined_const_kind_str`
        let kind = if rc.is_ctx { "ctx" } else { "type" };
        members_list.insert(
            0,
            format!("{} {} {}", kind, name.as_str(), rc_to_string(rc)),
        );
    }
    "{".to_string() + &members_list.join("; ") + "}"
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;
    use oxidized::s_map::SMap;

    use super::*;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::mk;
    use crate::typing_reason;

    fn prim(p: Tprim) -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(p)))
    }

    fn loose(lower: Vec<Ty>, upper: Vec<Ty>) -> RefinedConst {
        RefinedConst {
            bound: RefinedConstBound::TRloose(RefinedConstBounds { lower, upper }),
            is_ctx: false,
        }
    }

    fn show(ty: &Ty) -> String {
        match crate::typing_defs_core::get_node(ty) {
            Ty_::Tprim(Tprim::Tint) => "int".to_string(),
            Ty_::Tprim(Tprim::Tfloat) => "float".to_string(),
            Ty_::Tprim(Tprim::Tbool) => "bool".to_string(),
            _ => "?".to_string(),
        }
    }

    #[test]
    fn add_combines_bounds() {
        let cr = ClassRefinement {
            cr_consts: SMap::new().into(),
        };
        assert!(is_empty(&cr));
        let cr = add_refined_const("T".to_string(), loose(vec![prim(Tprim::Tint)], vec![]), cr);
        let cr = add_refined_const(
            "T".to_string(),
            loose(vec![prim(Tprim::Tfloat)], vec![prim(Tprim::Tbool)]),
            cr,
        );
        assert!(has_refined_const(&((), "T".to_string()), &cr));
        assert!(!has_refined_const(&((), "U".to_string()), &cr));
        match get_refined_const(&((), "T".to_string()), &cr).map(|rc| rc.bound) {
            Some(RefinedConstBound::TRloose(RefinedConstBounds { lower, upper })) => {
                assert_eq!(
                    lower.iter().map(show).collect::<Vec<_>>(),
                    vec!["int", "float"]
                );
                assert_eq!(upper.iter().map(show).collect::<Vec<_>>(), vec!["bool"]);
            }
            _ => panic!("expected loose bounds"),
        }
        // An exact bound wins.
        let cr = add_refined_const(
            "T".to_string(),
            RefinedConst {
                bound: RefinedConstBound::TRexact(prim(Tprim::Tint)),
                is_ctx: false,
            },
            cr,
        );
        assert!(matches!(
            get_refined_const(&((), "T".to_string()), &cr).map(|rc| rc.bound),
            Some(RefinedConstBound::TRexact(_))
        ));
    }

    #[test]
    fn to_string_lists_the_names_in_decreasing_order() {
        let mut cr_consts = SMap::new();
        cr_consts.insert(
            "A".to_string(),
            RefinedConst {
                bound: RefinedConstBound::TRexact(prim(Tprim::Tint)),
                is_ctx: false,
            },
        );
        cr_consts.insert(
            "B".to_string(),
            loose(vec![prim(Tprim::Tint)], vec![prim(Tprim::Tfloat)]),
        );
        let cr = ClassRefinement {
            cr_consts: cr_consts.into(),
        };
        assert_eq!(
            to_string(show, &cr),
            "{type B as int super float; type A = int}"
        );
        let mut n = 0;
        iter(|_| n += 1, &cr);
        assert_eq!(n, 3);
        let names = fold_refined_consts(&cr, vec![], |name, _, mut acc| {
            acc.push(name.to_string());
            acc
        });
        assert_eq!(names, vec!["A", "B"]);
    }
}
