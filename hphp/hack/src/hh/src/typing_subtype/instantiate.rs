// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 12470-12680): module `Instantiate`.
//! See `hh/PORTING.md`.
//!
//! - The environment is the labelled `~env` that comes last in OCaml: it is
//!   the last parameter here too.
//! - `bind_tparams` threads a `Type_parameter_env.t` as well as the
//!   environment: it is `&mut type_parameter_env::T`, like the environment.
//! - The accumulated `(env, err_opts)` of `add_constraint` is the environment
//!   and a vector of the errors in the order they are produced (the OCaml
//!   list has the last one first, and is reversed where it is read).

use naming_special_names_rust as sn;
use oxidized::ast_defs;
use oxidized::pos::Pos;

use crate::type_parameter_env;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::Tparam;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::WhereConstraint;
use crate::typing_defs_core::locl_subst;
use crate::typing_defs_core::mk;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_intersection;
use crate::typing_kinding_defs;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_set;
use crate::typing_subtype::subtype_tell;
use crate::typing_union;
use crate::typing_utils;

pub(crate) fn freshen_fun_ty(fun_ty: FunType, env: &mut Env, rank: isize) -> FunType {
    // The OCaml conses the new type parameters onto `ft_tparams_rev` and
    // reverses the list at the end: here they are pushed in order.
    let mut ft_tparams: Vec<Tparam> = Vec::with_capacity(fun_ty.tparams.len());
    let mut subst: locl_subst::T = locl_subst::T::new();
    for tparam in &fun_ty.tparams {
        let (pos, old_name) = &tparam.name;
        let new_name = env::fresh_param_name(env, old_name);
        let tparam = Tparam {
            name: (pos.clone(), new_name.clone()),
            ..tparam.clone()
        };
        let ty = mk((
            typing_reason::polymorphic_type_param((
                pos.clone(),
                new_name.clone(),
                old_name.clone(),
                rank,
            )),
            Ty_::Tgeneric(new_name),
        ));
        ft_tparams.push(tparam);
        subst.insert(old_name.clone(), ty);
    }
    let combine_reasons = |_src: Reason, dest: Reason| dest;
    locl_subst::apply_fun(
        FunType {
            tparams: ft_tparams,
            ..fun_ty
        },
        &subst,
        &combine_reasons,
    )
}

pub fn bind_tparams(
    r: Reason,
    tparams: &[Tparam],
    rank: isize,
    env: &mut Env,
    tp_env: &mut type_parameter_env::T,
) {
    for tparam in tparams {
        let Tparam {
            name: (def_pos, name),
            constraints: tp_constraints,
            reified,
            user_attributes: tp_user_attributes,
            ..
        } = tparam;
        let (lower_bounds, upper_bounds) = {
            let mut lower = typing_set::empty();
            let mut upper = typing_set::empty();
            for (kind, ty) in tp_constraints {
                // The components of the tuple are evaluated right to left
                // (and both run subtyping): `is_nothing` first.
                let is_nothing = typing_utils::is_nothing(env, ty);
                let is_mixed = typing_utils::is_mixed(env, ty);
                match kind {
                    ast_defs::ConstraintKind::ConstraintAs if is_mixed => {}
                    ast_defs::ConstraintKind::ConstraintAs => {
                        upper = typing_set::add(ty.clone(), &upper);
                    }
                    ast_defs::ConstraintKind::ConstraintSuper if is_nothing => {}
                    ast_defs::ConstraintKind::ConstraintSuper => {
                        lower = typing_set::add(ty.clone(), &lower);
                    }
                    ast_defs::ConstraintKind::ConstraintEq => {
                        lower = typing_set::add(ty.clone(), &lower);
                        upper = typing_set::add(ty.clone(), &upper);
                    }
                }
            }
            (lower, upper)
        };
        let (enforceable, newable, require_dynamic) = {
            let mut acc = (false, false, false);
            for ua in tp_user_attributes {
                let (_, name) = &ua.name;
                let (enforceable, newable, require_dynamic) = acc;
                acc = if name == sn::user_attributes::ENFORCEABLE {
                    (true, newable, require_dynamic)
                } else if name == sn::user_attributes::NEWABLE {
                    (enforceable, true, require_dynamic)
                } else if name == sn::user_attributes::REQUIRE_DYNAMIC {
                    (enforceable, newable, true)
                } else {
                    acc
                };
            }
            acc
        };
        let lower_bounds = {
            let lower_bound = typing_union::union_list(
                env,
                None,
                r.clone(),
                &typing_set::elements(&lower_bounds),
            );
            if typing_utils::is_nothing(env, &lower_bound) {
                typing_set::empty()
            } else {
                typing_set::singleton(lower_bound)
            }
        };
        let upper_bounds = {
            let upper_bound = typing_intersection::intersect_list(
                env,
                r.clone(),
                &typing_set::elements(&upper_bounds),
            );
            if typing_utils::is_mixed(env, &upper_bound) {
                typing_set::empty()
            } else {
                typing_set::singleton(upper_bound)
            }
        };
        let info = typing_kinding_defs::Kind {
            lower_bounds,
            upper_bounds,
            reified: *reified,
            enforceable,
            newable,
            require_dynamic,
            rank,
        };
        type_parameter_env::add(def_pos.clone(), name.clone(), info, tp_env);
    }
}

pub fn freshen_and_bind_fun_type_quantifiers(
    reason: Reason,
    fun_ty: FunType,
    rank: isize,
    env: &mut Env,
) -> FunType {
    let fun_ty = freshen_fun_ty(fun_ty, env, rank);
    let fun_ty = FunType {
        instantiated: true,
        ..fun_ty
    };
    {
        let FunType {
            tparams: ft_tparams,
            ..
        } = &fun_ty;
        // `env.tpenv` is read before `bind_tparams` runs, and the result is
        // put back in the environment that `bind_tparams` returns.
        let mut tpenv = env.tpenv.clone();
        bind_tparams(reason, ft_tparams, rank, env, &mut tpenv);
        env.tpenv = tpenv;
    }
    fun_ty
}

pub(crate) fn add_constraint(
    on_error: &Option<reasons_callback::T>,
    env: &mut Env,
    err_opts: &mut Vec<Option<typing_error::T>>,
    pos: &Pos,
    (ty_subj, constraint_kind, ty_cstr): (Ty, ast_defs::ConstraintKind, Ty),
) {
    // Prefer the use-site callback (e.g. the subtyping goal that triggered this
    // instantiation) so that an unsatisfiable-bounds error is anchored at the
    // use site rather than at the decl position of [pos], which may live in a
    // different definition and produce an "incomplete position" error.
    let callback = match on_error {
        Some(_) => on_error.clone(),
        None => Some(reasons_callback::unify_error_at(pos.clone())),
    };
    match constraint_kind {
        ast_defs::ConstraintKind::ConstraintAs => {
            let err =
                subtype_tell::sub_type(env, None, None, None, None, ty_subj, ty_cstr, callback);
            err_opts.push(err);
        }
        ast_defs::ConstraintKind::ConstraintSuper => {
            let err =
                subtype_tell::sub_type(env, None, None, None, None, ty_cstr, ty_subj, callback);
            err_opts.push(err);
        }
        ast_defs::ConstraintKind::ConstraintEq => {
            let err_cov = subtype_tell::sub_type(
                env,
                None,
                None,
                None,
                None,
                ty_subj.clone(),
                ty_cstr.clone(),
                callback.clone(),
            );
            let err_contrav =
                subtype_tell::sub_type(env, None, None, None, None, ty_cstr, ty_subj, callback);
            // `Option.merge err_cov err_contrav ~f:Typing_error.both`
            let err = match (err_cov, err_contrav) {
                (Some(err_cov), Some(err_contrav)) => {
                    Some(typing_error::both(err_cov, err_contrav))
                }
                (Some(err), None) | (None, Some(err)) => Some(err),
                (None, None) => None,
            };
            err_opts.push(err);
        }
    }
}

/// Instantiate a polymorphic function type with fresh type variables and
/// assert subtype constraints from type parameter bounds and where constraints
pub fn instantiate_fun_type(
    on_error: Option<reasons_callback::T>,
    pos: Pos,
    fun_ty: FunType,
    rank: isize,
    env: &mut Env,
) -> (Option<typing_error::T>, FunType) {
    // We need to build the substitution before generating constraints because
    // type parameters may appear as upper / lower bounds of other type
    // parameters, e.g.
    // function foo<T1 as T2,T2>(...)
    let subst: locl_subst::T = {
        let mut name_tys: Vec<(String, Ty)> = Vec::with_capacity(fun_ty.tparams.len());
        for Tparam { name: tp_name, .. } in &fun_ty.tparams {
            let (_, name) = tp_name;
            // We don't want to solve these type variable so we create them as
            // invariant
            let ty = env::fresh_type_invariant_with_rank(env, rank, pos.clone());
            name_tys.push((name.clone(), ty));
        }
        // `S_map.of_list` on the OCaml list, which has the last type
        // parameter first: the binding added last (that of the first type
        // parameter of a name) wins.
        let mut subst = locl_subst::T::new();
        for (name, ty) in name_tys.into_iter().rev() {
            subst.insert(name, ty);
        }
        subst
    };
    // TODO(mjt) add flow for polymorphic instantiation
    let combine_reasons = |src: Reason, _dest: Reason| src;
    let fun_ty = locl_subst::apply_fun(fun_ty, &subst, &combine_reasons);
    // Accumulate constraints
    let mut err_opts: Vec<Option<typing_error::T>> = vec![];
    for Tparam {
        name: (_, id),
        constraints: tp_constraints,
        ..
    } in &fun_ty.tparams
    {
        // We know the substituion contains the name so use the unsafe [find]
        let ty_subj = match subst.get(id) {
            Some(ty) => ty.clone(),
            None => panic!("Not_found"),
        };
        for (cstr_kind, ty_cstr) in tp_constraints {
            add_constraint(
                &on_error,
                env,
                &mut err_opts,
                &pos,
                (ty_subj.clone(), *cstr_kind, ty_cstr.clone()),
            );
        }
    }
    for WhereConstraint(ty1, cstr_kind, ty2) in &fun_ty.where_constraints {
        add_constraint(
            &on_error,
            env,
            &mut err_opts,
            &pos,
            (ty1.clone(), *cstr_kind, ty2.clone()),
        );
    }
    // `Typing_error.multiple_opt @@ List.filter_opt err_opts`, on the OCaml
    // list (the last error first).
    let err_opt = typing_error::multiple_opt(err_opts.into_iter().rev().flatten().collect());
    (
        err_opt,
        FunType {
            instantiated: true,
            ..fun_ty
        },
    )
}
