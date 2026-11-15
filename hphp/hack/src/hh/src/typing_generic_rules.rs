// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_generic_rules.ml`. See `hh/PORTING.md`.
//!
//! The callbacks take the environment, `~supportdyn` and the type, and return
//! the type and the `(locl_ty, locl_ty * locl_ty) result`s
//! ([`TyMismatchRes`]) of the `.mli`; the functions return the type and the
//! mismatches as options.

use std::collections::VecDeque;

use crate::naming_special_names as sn;
use crate::s_set;
use crate::tast;
use crate::typing_defs::is_arraykey;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error_utils;
use crate::typing_intersection;
use crate::typing_make_type as make_type;
use crate::typing_reason as reason;
use crate::typing_set as ty_set;
use crate::typing_solver;
use crate::typing_union;
use crate::typing_utils;

/// `(locl_ty, locl_ty * locl_ty) result`
pub type TyMismatchRes = Result<Ty, (Ty, Ty)>;

/// Return upper bounds of a generic parameter, transitively following bounds
/// that are themselves parameters. Detect cycles.
fn get_transitive_upper_bounds(env: &mut Env, ty: &Ty) -> Vec<Ty> {
    let mut seen = s_set::T::new();
    let mut acc = ty_set::empty();
    let mut tyl: VecDeque<Ty> = VecDeque::from([ty.clone()]);
    while let Some(ty) = tyl.pop_front() {
        let ety = env::expand_type(env, ty.clone());
        match get_node(&ety) {
            Ty_::Tgeneric(n) => {
                if seen.contains(n) {
                } else {
                    seen.insert(n.clone());
                    // `TySet.elements (Env.get_upper_bounds env n) @ tyl`
                    let bounds = ty_set::elements(&env::get_upper_bounds(env, n));
                    for bound in bounds.into_iter().rev() {
                        tyl.push_front(bound)
                    }
                }
            }
            _ => acc = ty_set::add(ty, &acc),
        }
    }
    ty_set::elements(&acc)
}

// Apply generic typing rules. Here, assume E[e:t] is some expression with a
// subexpression e of type t. For example, E[x:C] is `x->method(e1,..,en)` (method
// invocation on object of class C) or E[x:vec<int>] is `x[e1] = e2` (array
// assignment on a vec<int>).
// 1. Lift unions: if e:t1|t2 and E[e:t1] : u1 and E[e:t2] : u2
//    then E[e:t1|t2] : u1|u2. (Note: both sides of union must succeed.)
// 2. Lift intersections: if e:t1&t2 and E[e:t1] : u1 and E[e:t2] : u2
//    then E[e:t1&t2] : u1&u2. If E[e:t1] : u1 but E[e:t2] does not type,
//    then E[e:t1&t2] : u1 (and similar for the other way round).
// 3. Apply subsumption wrt upper bounds on generics and abstract types:
//    If e:T and generic parameter T has upper bound t and E[e:t] : u,
//    then E[e:T] : u.
// For the implementation below, ty is the type of the subexpression e,
// and f is the checker for the context E[e:ty].
// We iterate the rule through intersections, unions, and bounds.

fn is_shape(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tshape(ShapeType::ShapeSimple(_)) => true,
        Ty_::Tshape(ShapeType::ShapeSplat(_)) => true,
        _ => false,
    }
}

/// `fold_errs`: the folding over the reversed list, consing, puts the
/// results in the order of `errs`.
fn fold_errs(errs: Vec<TyMismatchRes>) -> Result<Vec<Ty>, (Vec<Ty>, Vec<Ty>)> {
    // The lists are built backwards (by pushing) and reversed at the end.
    let mut acc: Result<Vec<Ty>, (Vec<Ty>, Vec<Ty>)> = Ok(vec![]);
    for res in errs.into_iter().rev() {
        acc = match (acc, res) {
            (Ok(mut xs), Ok(x)) => {
                xs.push(x);
                Ok(xs)
            }
            (Ok(xs), Err((ty_actual, ty_expect))) => {
                let mut actuals = xs.clone();
                actuals.push(ty_actual);
                let mut expects = xs;
                expects.push(ty_expect);
                Err((actuals, expects))
            }
            (Err((mut xs, mut ys)), Ok(x)) => {
                xs.push(x.clone());
                ys.push(x);
                Err((xs, ys))
            }
            (Err((mut xs, mut ys)), Err((ty_actual, ty_expect))) => {
                xs.push(ty_actual);
                ys.push(ty_expect);
                Err((xs, ys))
            }
        }
    }
    match acc {
        Ok(mut xs) => {
            xs.reverse();
            Ok(xs)
        }
        Err((mut xs, mut ys)) => {
            xs.reverse();
            ys.reverse();
            Err((xs, ys))
        }
    }
}

fn intersect_errs(env: &mut Env, errs: Vec<TyMismatchRes>) -> TyMismatchRes {
    match fold_errs(errs) {
        Ok(tys) => {
            let ty = typing_intersection::intersect_list(env, reason::none(), &tys);
            Ok(ty)
        }
        Err((actuals, expects)) => {
            let ty_actual = typing_intersection::intersect_list(env, reason::none(), &actuals);
            let ty_expect = typing_intersection::intersect_list(env, reason::none(), &expects);
            Err((ty_actual, ty_expect))
        }
    }
}

fn union_errs(env: &mut Env, errs: Vec<TyMismatchRes>) -> TyMismatchRes {
    match fold_errs(errs) {
        Ok(tys) => {
            let ty = typing_union::union_list(env, None, reason::none(), &tys);
            Ok(ty)
        }
        Err((actuals, expects)) => {
            let ty_actual = typing_union::union_list(env, None, reason::none(), &actuals);
            let ty_expect = typing_union::union_list(env, None, reason::none(), &expects);
            Err((ty_actual, ty_expect))
        }
    }
}

type ArrayCallback<'a> =
    dyn FnMut(&mut Env, bool, Ty) -> (Ty, TyMismatchRes, TyMismatchRes, TyMismatchRes) + 'a;

/// `iter ~supportdyn ~is_nonnull env ty` of
/// `apply_rules_with_array_index_value_ty_mismatches`.
fn iter(
    ignore_type_structure: bool,
    preserve_supportdyn: bool,
    f: &mut ArrayCallback<'_>,
    supportdyn: bool,
    is_nonnull: bool,
    env: &mut Env,
    ty: Ty,
) -> (Ty, TyMismatchRes, TyMismatchRes, TyMismatchRes) {
    let ety = env::expand_type(env, ty.clone());
    // This is the base case: not a union or intersection or bounded abstract type
    // (The OCaml closure captures the environment returned by `expand_type`:
    // the branches that change `env` before calling it restore it first.)
    let default = |f: &mut ArrayCallback<'_>, env: &mut Env, ty: Ty| f(env, supportdyn, ty);

    let r = get_reason(&ety).clone();
    match get_node(&ety) {
        // For intersections, collect up all successful applications and compute
        // the intersection of the types and intersection of errors
        Ty_::Tintersection(tyl) => {
            let (is_nonnull, ty_err_opt) =
                typing_solver::is_sub_type(env, &ty, &make_type::nonnull(reason::none()));
            if let Some(err) = &ty_err_opt {
                typing_error_utils::add_typing_error(err, env)
            }
            let res = typing_utils::run_on_intersection(
                env,
                |env: &mut Env, ty: &Ty| {
                    iter(
                        ignore_type_structure,
                        preserve_supportdyn,
                        f,
                        supportdyn,
                        is_nonnull,
                        env,
                        ty.clone(),
                    )
                },
                tyl,
            );
            let mut tys = vec![];
            let mut arr_errs = vec![];
            let mut key_errs = vec![];
            let mut val_errs = vec![];
            for (ty, arr_err, key_err, val_err) in res {
                tys.push(ty);
                arr_errs.push(arr_err);
                key_errs.push(key_err);
                val_errs.push(val_err);
            }
            let arr_ty_mismatch = intersect_errs(env, arr_errs);
            let key_ty_mismatch = intersect_errs(env, key_errs);
            let val_ty_mismatch = intersect_errs(env, val_errs);
            let ty = typing_intersection::intersect_list(env, r, &tys);
            (ty, arr_ty_mismatch, key_ty_mismatch, val_ty_mismatch)
        }
        Ty_::Tnewtype(cid, _, _)
            if cid == sn::classes::SUPPORT_DYN
                && tast::is_under_dynamic_assumptions(env.checked) =>
        {
            // If we are under_dynamic_assumptions, we might want to take advantage of
            // the dynamic in supportdyn<t>, so don't break it apart as in the next case.
            default(f, env, ty)
        }
        // Preserve supportdyn<_> across operation
        Ty_::Tnewtype(cid, tyl, _) if tyl.len() == 1 && cid == sn::classes::SUPPORT_DYN => {
            let (ty, arr_errs, key_errs, val_errs) = iter(
                ignore_type_structure,
                preserve_supportdyn,
                f,
                true,
                is_nonnull,
                env,
                tyl[0].clone(),
            );
            let ty = if preserve_supportdyn {
                typing_utils::make_supportdyn(r, env, ty)
            } else {
                ty
            };
            (ty, arr_errs, key_errs, val_errs)
        }
        // For unions, just apply rule of components and compute union of result
        Ty_::Tunion(tyl) => {
            // `List.fold_left` conses each result: the lists are in the
            // reverse order of `tyl`.
            let mut tys = vec![];
            let mut arr_errs = vec![];
            let mut key_errs = vec![];
            let mut val_errs = vec![];
            for ty in tyl.iter() {
                let (ty, arr_err, key_err, val_err) = iter(
                    ignore_type_structure,
                    preserve_supportdyn,
                    f,
                    supportdyn,
                    is_nonnull,
                    env,
                    ty.clone(),
                );
                tys.push(ty);
                arr_errs.push(arr_err);
                key_errs.push(key_err);
                val_errs.push(val_err);
            }
            tys.reverse();
            arr_errs.reverse();
            key_errs.reverse();
            val_errs.reverse();
            let arr_ty_mismatch = union_errs(env, arr_errs);
            let key_ty_mismatch = union_errs(env, key_errs);
            let val_ty_mismatch = union_errs(env, val_errs);
            let ty = typing_union::union_list(env, None, r, &tys);
            (ty, arr_ty_mismatch, key_ty_mismatch, val_ty_mismatch)
        }
        // Special case for `TypeStructure<_> as shape { ... }`, because some clients care about the
        // fact that we have the special type TypeStructure
        Ty_::Tnewtype(cid, tyl, _) => {
            // `default ()` runs `f` with the environment it closed over (the
            // one before `get_newtype_super`), dropping the newer one.
            let env_before_bound = env.clone();
            let bound = typing_utils::get_newtype_super(env, r, cid, tyl);
            if cid == sn::fb::TYPE_STRUCTURE && is_shape(&bound) && ignore_type_structure {
                *env = env_before_bound;
                default(f, env, ty)
            }
            // Enums with arraykey upper bound are treated as "abstract"
            else if env::is_enum(env, cid) && is_arraykey(&bound) {
                *env = env_before_bound;
                default(f, env, ty)
            } else {
                iter(
                    ignore_type_structure,
                    preserve_supportdyn,
                    f,
                    supportdyn,
                    is_nonnull,
                    env,
                    bound,
                )
            }
        }
        // If there is an explicit upper bound, delegate to it
        Ty_::Tdependent(_, ty) => iter(
            ignore_type_structure,
            preserve_supportdyn,
            f,
            supportdyn,
            is_nonnull,
            env,
            ty.clone(),
        ),
        // For type parameters with upper bounds, delegate to intersection of the upper bounds
        Ty_::Tgeneric(_) => {
            // `default ()` runs `f` with the environment it closed over (the
            // one before `get_transitive_upper_bounds`).
            let env_before_bounds = env.clone();
            let tyl = get_transitive_upper_bounds(env, &ty);
            if tyl.is_empty() {
                *env = env_before_bounds;
                default(f, env, ty)
            } else {
                let ty = typing_intersection::intersect_list(env, r, &tyl);
                let ty = if is_nonnull {
                    let pos = get_pos(&ty);
                    typing_intersection::intersect_with_nonnull(env, pos, ty)
                } else {
                    ty
                };
                iter(
                    ignore_type_structure,
                    preserve_supportdyn,
                    f,
                    supportdyn,
                    is_nonnull,
                    env,
                    ty,
                )
            }
        }
        _ => default(f, env, ty),
    }
}

fn opt_of_res(res: TyMismatchRes) -> Option<(Ty, Ty)> {
    match res {
        Ok(_) => None,
        Err(tys) => Some(tys),
    }
}

/// Here we have a function returns the updated environment, a local type
/// and results indicating type errors for both and index expression and
/// the rhs expression of an assignment
pub fn apply_rules_with_array_index_value_ty_mismatches(
    ignore_type_structure: Option<bool>,
    preserve_supportdyn: Option<bool>,
    env: &mut Env,
    ty: Ty,
    mut f: impl FnMut(&mut Env, bool, Ty) -> (Ty, TyMismatchRes, TyMismatchRes, TyMismatchRes),
) -> (Ty, Option<(Ty, Ty)>, Option<(Ty, Ty)>, Option<(Ty, Ty)>) {
    let ignore_type_structure = ignore_type_structure.unwrap_or(false);
    let preserve_supportdyn = preserve_supportdyn.unwrap_or(true);
    let (ty, arr_ty_mismatch, key_ty_mismatch, val_ty_mismatch) = iter(
        ignore_type_structure,
        preserve_supportdyn,
        &mut f,
        false,
        false,
        env,
        ty,
    );
    let arr_err_opt = opt_of_res(arr_ty_mismatch);
    let key_err_opt = opt_of_res(key_ty_mismatch);
    let val_err_opt = opt_of_res(val_ty_mismatch);
    (ty, arr_err_opt, key_err_opt, val_err_opt)
}

pub fn apply_rules_with_index_value_ty_mismatches(
    ignore_type_structure: Option<bool>,
    preserve_supportdyn: bool,
    env: &mut Env,
    ty: Ty,
    mut f: impl FnMut(&mut Env, bool, Ty) -> (Ty, TyMismatchRes, TyMismatchRes),
) -> (Ty, Option<(Ty, Ty)>, Option<(Ty, Ty)>) {
    let g = |env: &mut Env, supportdyn: bool, ty: Ty| {
        let (ty, idx_ty_mismatch, val_ty_mismatch) = f(env, supportdyn, ty);
        (ty.clone(), Ok(ty), idx_ty_mismatch, val_ty_mismatch)
    };
    let (ty, _, idx_ty_mismatch, val_ty_mismatch) =
        apply_rules_with_array_index_value_ty_mismatches(
            ignore_type_structure,
            Some(preserve_supportdyn),
            env,
            ty,
            g,
        );
    (ty, idx_ty_mismatch, val_ty_mismatch)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typing_reason as reason;

    #[test]
    fn fold_errs_order() {
        let a = make_type::int(reason::none());
        let b = make_type::string(reason::none());
        let c = make_type::float(reason::none());
        let d = make_type::bool(reason::none());
        match fold_errs(vec![
            Ok(a.clone()),
            Err((b.clone(), c.clone())),
            Ok(d.clone()),
        ]) {
            Err((xs, ys)) => {
                assert!(xs.len() == 3 && ys.len() == 3);
                assert!(crate::typing_defs_core::phys_equal(&xs[1], &b));
                assert!(crate::typing_defs_core::phys_equal(&ys[1], &c));
                assert!(crate::typing_defs_core::phys_equal(&xs[0], &a));
                assert!(crate::typing_defs_core::phys_equal(&ys[2], &d));
            }
            Ok(_) => panic!("expected an error"),
        }
    }
}
