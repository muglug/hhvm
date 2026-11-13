// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 11320-11450): module `Subtype_simplify`.
//! See `hh/PORTING.md`.
//!
//! The functions return a list and no environment: they take `&Env`, and
//! expand types in a copy of it, which they pass on as the OCaml passes the
//! environment the expansions returned. Their shape is that of the
//! `intersect`/`union` callbacks of `typing_env::add_upper_bound`,
//! `add_lower_bound`, `add_tyvar_upper_bound_and_update_variances` and
//! `add_tyvar_lower_bound_and_update_variances`
//! (`(ty, &[ty]) -> Vec<ty>`), with the environment as the first argument
//! after the optional ones.

use oxidized::ast_defs::Tprim;

use crate::typing_defs::is_prim;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::is_tyvar_i;
use crate::typing_defs_constraints::reason;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_make_type as make_type;
use crate::typing_subtype::subtype_ask;

/// Attempt to compute the intersection of a type with an existing list intersection.
/// If try_intersect env t [t1;...;tn] = [u1; ...; um]
/// then u1&...&um must be the greatest lower bound of t and t1&...&tn wrt subtyping.
/// For example:
///   try_intersect nonnull [?C] = [C]
///   try_intersect t1 [t2] = [t1]  if t1 <: t2
/// Note: it's acceptable to return [t;t1;...;tn] but the intention is that
/// we simplify (as above) wherever practical.
/// It can be assumed that the original list contains no redundancy.
pub fn try_intersect_i(
    ignore_tyvars: Option<bool>,
    env: &Env,
    ty: InternalType,
    tyl: &[InternalType],
) -> Vec<InternalType> {
    let ignore_tyvars = ignore_tyvars.unwrap_or(false);
    match tyl {
        [] => vec![ty],
        [ty_, tyl_ @ ..] => {
            let mut env = env.clone();
            let ty = env::expand_internal_type(&mut env, ty);
            let ty_ = env::expand_internal_type(&mut env, ty_.clone());
            let env = &env;
            let default = |env: &Env| {
                let rest = try_intersect_i(Some(ignore_tyvars), env, ty.clone(), tyl_);
                let mut res = vec![ty_.clone()];
                res.extend(rest);
                res
            };
            // Do not attempt to simplify intersection of type variables, as we use
            // intersection simplification when transitively closing through type variable
            // upper bounds and this would result in a type failing to be added.
            if ignore_tyvars && (is_tyvar_i(&ty) || is_tyvar_i(&ty_)) {
                default(env)
            } else if subtype_ask::is_sub_type_ignore_generic_params_i(env, &ty, &ty_) {
                try_intersect_i(Some(ignore_tyvars), env, ty.clone(), tyl_)
            } else if subtype_ask::is_sub_type_ignore_generic_params_i(env, &ty_, &ty) {
                tyl.to_vec()
            } else {
                let nonnull_ty = InternalType::LoclType(make_type::nonnull(reason(&ty).clone()));
                match (&ty, &ty_) {
                    (InternalType::LoclType(lty), _)
                        if subtype_ask::is_sub_type_ignore_generic_params_i(
                            env,
                            &ty_,
                            &nonnull_ty,
                        ) =>
                    {
                        match get_node(lty) {
                            Ty_::Toption(t) => {
                                let mut tyl = vec![ty_.clone()];
                                tyl.extend_from_slice(tyl_);
                                try_intersect_i(
                                    Some(ignore_tyvars),
                                    env,
                                    InternalType::LoclType(t.clone()),
                                    &tyl,
                                )
                            }
                            _ => default(env),
                        }
                    }
                    (_, InternalType::LoclType(lty))
                        if subtype_ask::is_sub_type_ignore_generic_params_i(
                            env,
                            &ty,
                            &nonnull_ty,
                        ) =>
                    {
                        match get_node(lty) {
                            Ty_::Toption(t) => {
                                let mut tyl = vec![ty.clone()];
                                tyl.extend_from_slice(tyl_);
                                try_intersect_i(
                                    Some(ignore_tyvars),
                                    env,
                                    InternalType::LoclType(t.clone()),
                                    &tyl,
                                )
                            }
                            _ => default(env),
                        }
                    }
                    (_, _) => default(env),
                }
            }
        }
    }
}

pub fn try_intersect(ignore_tyvars: Option<bool>, env: &Env, ty: Ty, tyl: &[Ty]) -> Vec<Ty> {
    let ignore_tyvars = ignore_tyvars.unwrap_or(false);
    let tyl: Vec<InternalType> = tyl
        .iter()
        .map(|ty| InternalType::LoclType(ty.clone()))
        .collect();
    try_intersect_i(Some(ignore_tyvars), env, InternalType::LoclType(ty), &tyl)
        .into_iter()
        .map(|ty| match ty {
            InternalType::LoclType(ty) => ty,
            _ => panic!("The intersection of two locl type should always be a locl type."),
        })
        .collect()
}

/// Attempt to compute the union of a type with an existing list union.
/// If try_union env t [t1;...;tn] = [u1;...;um]
/// then u1|...|um must be the least upper bound of t and t1|...|tn wrt subtyping.
/// For example:
///   try_union int [float] = [num]
///   try_union t1 [t2] = [t1] if t2 <: t1
///
/// Notes:
/// 1. It's acceptable to return [t;t1;...;tn] but the intention is that
///    we simplify (as above) wherever practical.
/// 2. Do not use Tunion for a syntactic union - the caller can do that.
/// 3. It can be assumed that the original list contains no redundancy.
/// TODO: there are many more unions to implement yet.
pub fn try_union_i(env: &Env, ty: InternalType, tyl: &[InternalType]) -> Vec<InternalType> {
    // The OCaml recursion, as a loop: the recursive call on the tail is the
    // next iteration, and what the OCaml conses in front of its result is
    // pushed onto `res`, which the result of the last call ends.
    // `expanded_env` is the environment the expansions returned, which the
    // OCaml passes to the recursive call (`None`: still `env`).
    let mut res: Vec<InternalType> = Vec::new();
    let mut expanded_env: Option<Env> = None;
    let mut ty = ty;
    for (i, ty_) in tyl.iter().enumerate() {
        let env_: &Env = expanded_env.as_ref().unwrap_or(env);
        if subtype_ask::is_sub_type_for_union_i(env_, None, &ty, ty_) {
            res.extend_from_slice(&tyl[i..]);
            return res;
        } else if subtype_ask::is_sub_type_for_union_i(env_, None, ty_, &ty) {
            // `try_union env ty tyl`
        } else {
            let mut env_ = env_.clone();
            let ety = env::expand_internal_type(&mut env_, ty);
            let ety_ = env::expand_internal_type(&mut env_, ty_.clone());
            match (&ety, &ety_) {
                (InternalType::LoclType(t1), InternalType::LoclType(t2))
                    if (is_prim(Tprim::Tfloat, t1) && is_prim(Tprim::Tint, t2))
                        || (is_prim(Tprim::Tint, t1) && is_prim(Tprim::Tfloat, t2)) =>
                {
                    ty = InternalType::LoclType(make_type::num(reason(&ety).clone()));
                }
                (_, _) => {
                    ty = ety;
                    res.push(ety_);
                }
            }
            expanded_env = Some(env_);
        }
    }
    // `[] -> [ty]`
    res.push(ty);
    res
}

pub fn try_union(env: &Env, ty: Ty, tyl: &[Ty]) -> Vec<Ty> {
    let tyl: Vec<InternalType> = tyl
        .iter()
        .map(|ty| InternalType::LoclType(ty.clone()))
        .collect();
    try_union_i(env, InternalType::LoclType(ty), &tyl)
        .into_iter()
        .map(|ty| match ty {
            InternalType::LoclType(ty) => ty,
            _ => panic!("The union of two locl type should always be a locl type."),
        })
        .collect()
}
