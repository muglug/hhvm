// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_async.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;
use oxidized::pos::Pos;

use crate::typing_defs;
use crate::typing_defs::t_shape_map;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::mk;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Type = Typing_ops`
use crate::typing_ops as type_;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
use crate::typing_solver;
use crate::typing_union;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `Option.merge e1 e2 ~f:Typing_error.both`
fn merge(e1: Option<typing_error::T>, e2: Option<typing_error::T>) -> Option<typing_error::T> {
    match (e1, e2) {
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    }
}

/// If an expression e is of type `opt_ty_maybe`, then this function
/// returns the type of `await e`.
///
/// There is the special case that
///   e : ?Awaitable<T> |- await e : ?T
fn overload_extract_from_awaitable_with_ty_err(
    env: &mut Env,
    p: Pos,
    opt_ty_maybe: Ty,
) -> (Option<typing_error::T>, Ty) {
    let r = reason::witness(p.clone());
    fn extract_inner(
        env: &mut Env,
        p: &Pos,
        r: &Reason,
        opt_ty_maybe: Ty,
    ) -> (Option<typing_error::T>, Ty) {
        let (e1, e_opt_ty): (Option<typing_error::T>, Ty) = typing_solver::expand_type_and_solve(
            env,
            None,
            "an Awaitable",
            p.clone(),
            opt_ty_maybe.clone(),
        );
        match get_node(&e_opt_ty) {
            Ty_::Tunion(tyl) => {
                // `List.fold_map ~init:(env, Option.to_list e1)`: the errors
                // are prepended to the list, so the OCaml list is the reverse
                // of the order in which they are found.
                let mut ty_errs: Vec<typing_error::T> = e1.into_iter().collect();
                let mut rtyl = Vec::with_capacity(tyl.len());
                for ty in tyl {
                    match extract_inner(env, p, r, ty.clone()) {
                        (Some(ty_err), ty) => {
                            ty_errs.push(ty_err);
                            rtyl.push(ty)
                        }
                        (_, ty) => rtyl.push(ty),
                    }
                }
                ty_errs.reverse();
                let ty = t_utils::union_list(env, None, r.clone(), &rtyl);
                (typing_error::multiple_opt(ty_errs), ty)
            }
            Ty_::Toption(ty) => {
                // We want to try to avoid easy double nullables here, so we handle Toption
                // with some special logic.
                let (e2, ty) = extract_inner(env, p, r, ty.clone());
                let ty = t_utils::union(env, None, None, make_type::null(r.clone()), ty);
                (merge(e1, e2), ty)
            }
            Ty_::Tnewtype(n, tyl, _) if tyl.len() == 1 && n == sn::classes::SUPPORT_DYN => {
                let (e2, ty) = extract_inner(env, p, r, tyl[0].clone());
                let ty = t_utils::make_supportdyn(r.clone(), env, ty);
                (merge(e1, e2), ty)
            }
            Ty_::Tintersection(tyl) => {
                let (e2, rtyl) = t_utils::run_on_intersection_with_ty_err(
                    env,
                    |env: &mut Env, ty: &Ty| extract_inner(env, p, r, ty.clone()),
                    tyl,
                );
                (merge(e1, e2), make_type::intersection(r.clone(), rtyl))
            }
            Ty_::Tprim(Tprim::Tnull) => (e1, e_opt_ty.clone()),
            Ty_::Tdynamic(shadow_v_opt) => {
                // Dynamic inference: awaiting a dynamic with a shadow type variable.
                // Create a fresh shadow for the result, and record Awaitable<dynamic#v>
                // as an upper bound on the input shadow. This tracks that the value was
                // used as an Awaitable.
                let result_shadow = match shadow_v_opt {
                    Some(shadow_v) => {
                        let v_result = env::fresh_shadow_tyvar(env, p.clone());
                        let awaitable_ty = make_type::awaitable(
                            r.clone(),
                            mk((r.clone(), Ty_::Tdynamic(Some(v_result)))),
                        );
                        env::add_tyvar_upper_bound(
                            None,
                            env,
                            *shadow_v,
                            InternalType::LoclType(awaitable_ty),
                        );
                        Some(v_result)
                    }
                    None => None,
                };
                (e1, mk((r.clone(), Ty_::Tdynamic(result_shadow))))
            }
            Ty_::Tany(_)
            | Ty_::TvecOrDict(_, _)
            | Ty_::Tnonnull
            | Ty_::Tprim(_)
            | Ty_::Tvar(_)
            | Ty_::Tfun(_)
            | Ty_::Tgeneric(_)
            | Ty_::Tnewtype(_, _, _)
            | Ty_::Tdependent(_, _)
            | Ty_::Tclass(_, _, _)
            | Ty_::Ttuple(_)
            | Ty_::Tshape(ShapeType::ShapeSimple(_) | ShapeType::ShapeSplat(_))
            | Ty_::Taccess(_)
            | Ty_::Tlabel(_)
            | Ty_::Tneg(_)
            | Ty_::TclassPtr(_) => {
                let type_var = if t_utils::is_tyvar_error(env, &e_opt_ty) {
                    env::fresh_type_error(env, p.clone())
                } else {
                    env::fresh_type(env, p.clone())
                };
                let expected_type = make_type::awaitable(r.clone(), type_var.clone());
                let return_type = match get_node(&e_opt_ty) {
                    Ty_::Tany(_) => mk((r.clone(), typing_defs::make_tany())),
                    Ty_::Tdynamic(_)
                    | Ty_::Tnonnull
                    | Ty_::TvecOrDict(_, _)
                    | Ty_::Tprim(_)
                    | Ty_::Tvar(_)
                    | Ty_::Tfun(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tnewtype(_, _, _)
                    | Ty_::Tdependent(_, _)
                    | Ty_::Tclass(_, _, _)
                    | Ty_::Ttuple(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Toption(_)
                    | Ty_::Tunion(_)
                    | Ty_::Tshape(ShapeType::ShapeSimple(_) | ShapeType::ShapeSplat(_))
                    | Ty_::Taccess(_)
                    | Ty_::Tlabel(_)
                    | Ty_::Tneg(_)
                    | Ty_::TclassPtr(_) => type_var,
                };
                let e2 = type_::sub_type(None, 
                    p.clone(),
                    Ureason::URawait,
                    env,
                    opt_ty_maybe,
                    expected_type,
                    typing_error::callback::unify_error(),
                );
                (merge(e1, e2), return_type)
            }
        }
    }
    env::open_tyvars(env, p.clone());
    let (ty_err_opt, ty) = extract_inner(env, &p, &r, opt_ty_maybe);
    let err = typing_solver::close_tyvars_and_solve(env);
    if let Some(ty_err) = &ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    let ty = typing_union::simplify_unions(env, None, None, ty);
    (err, ty)
}

pub fn overload_extract_from_awaitable(env: &mut Env, p: Pos, opt_ty_maybe: Ty) -> Ty {
    let (ty_err_opt, res) = overload_extract_from_awaitable_with_ty_err(env, p, opt_ty_maybe);
    if let Some(ty_err) = &ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    res
}

fn overload_extract_from_awaitable_list_with_ty_err(
    env: &mut Env,
    p: Pos,
    tyl: &[Ty],
) -> (Option<typing_error::T>, Vec<Ty>) {
    // `List.fold_right`: the last type first. Each result and each error is
    // prepended, so both lists end up in the order of `tyl`.
    let mut ty_errs = vec![];
    let mut rtyl = Vec::with_capacity(tyl.len());
    for ty in tyl.iter().rev() {
        let (ty_err_opt, rty) = overload_extract_from_awaitable_with_ty_err(env, p.clone(), ty.clone());
        if let Some(e) = ty_err_opt {
            ty_errs.push(e)
        }
        rtyl.push(rty)
    }
    ty_errs.reverse();
    rtyl.reverse();
    (typing_error::multiple_opt(ty_errs), rtyl)
}

pub fn overload_extract_from_awaitable_list(env: &mut Env, p: Pos, tyl: &[Ty]) -> Vec<Ty> {
    let (ty_err_opt, res) = overload_extract_from_awaitable_list_with_ty_err(env, p, tyl);
    if let Some(ty_err) = &ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    res
}

fn overload_extract_from_awaitable_shape_with_ty_err<A>(
    env: &mut Env,
    p: Pos,
    fdm: t_shape_map::T<(A, Ty)>,
) -> (Option<typing_error::T>, t_shape_map::T<(A, Ty)>) {
    t_shape_map::map_env_ty_err_opt(
        |env: &mut Env, _key, (tk, tv): (A, Ty)| {
            let (ty_err_opt, rtv) = overload_extract_from_awaitable_with_ty_err(env, p.clone(), tv);
            (ty_err_opt, (tk, rtv))
        },
        env,
        fdm,
        typing_error::multiple_opt,
    )
}

pub fn overload_extract_from_awaitable_shape<A>(
    env: &mut Env,
    p: Pos,
    fdm: t_shape_map::T<(A, Ty)>,
) -> t_shape_map::T<(A, Ty)> {
    let (ty_err_opt, res) = overload_extract_from_awaitable_shape_with_ty_err(env, p, fdm);
    if let Some(ty_err) = &ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    res
}
