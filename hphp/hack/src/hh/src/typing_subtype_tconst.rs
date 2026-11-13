// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_subtype_tconst.ml`. See `hh/PORTING.md`.
//!
//! As in `crate::typing_taccess`, the `((env, ty_err_opt, cycles), x)` of
//! OCaml is `(ty_err_opt, cycles, x)`.

use oxidized::pos::Pos;

use crate::tvid;
use crate::type_expansions::CycleReporter;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::HasTypeMember;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::deref_constraint_type;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::Ty;
/// `module Env = Typing_env`
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_log;
use crate::typing_reason;
/// `module Utils = Typing_utils`
use crate::typing_utils as utils;

/// `Option.merge a b ~f`
fn option_merge<A>(a: Option<A>, b: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (a, b) {
        (None, x) | (x, None) => x,
        (Some(a), Some(b)) => Some(f(a, b)),
    }
}

/// Make `tvar` equal to `ty::tconstid`. The locl type `tvar` is a
/// type variable that represents the the type constant ::tconstid of
/// another variable v. See get_tyvar_type_const below, where such type
/// variables are created.
fn make_type_const_equal(
    env: &mut Env,
    tvar: &Ty,
    ty: &InternalType,
    tconstid: &PosId,
    on_error: Option<reasons_callback::T>,
    as_tyvar_with_cnstr: Option<Pos>,
) -> (Option<typing_error::T>, Vec<CycleReporter>) {
    let subtype_error = on_error.clone().map(reasons_callback::type_constant_mismatch);
    let make_equal = |env: &mut Env, ty: &InternalType| match ty {
        InternalType::LoclType(ty) => {
            let ety_env = empty_expand_env();
            let ignore_errors = as_tyvar_with_cnstr.is_some();
            let (e1, cycles, tytconst) = utils::expand_typeconst(
                &ety_env,
                env,
                Some(ignore_errors),
                Some(as_tyvar_with_cnstr.clone()),
                ty.clone(),
                tconstid.clone(),
                true, // allow_abstract_tconst
            );
            let e2 = utils::sub_type(
                env,
                None,
                None,
                None,
                None,
                tytconst.clone(),
                tvar.clone(),
                subtype_error.clone(),
            );
            let e3 = utils::sub_type(
                env,
                None,
                None,
                None,
                None,
                tvar.clone(),
                tytconst,
                subtype_error.clone(),
            );
            (
                typing_error::multiple_opt([e1, e2, e3].into_iter().flatten().collect()),
                cycles,
            )
        }
        InternalType::ConstraintType(ty) => match deref_constraint_type(ty) {
            (
                r,
                ConstraintType_::ThasTypeMember(HasTypeMember {
                    id: htm_id,
                    upper: up_ty,
                    lower: lo_ty,
                }),
            ) if htm_id == tconstid.1 => {
                let e = utils::sub_type(
                    env,
                    None,
                    None,
                    None,
                    None,
                    up_ty.clone(),
                    lo_ty.clone(),
                    on_error.clone(),
                );
                match e {
                    Some(_) => {
                        let err_opt = on_error.clone().map(|on_error| {
                            typing_error::apply_reasons(
                                secondary::T::Inexact_tconst_access(
                                    typing_reason::to_pos(&r),
                                    tconstid.clone(),
                                ),
                                on_error,
                            )
                        });
                        (err_opt, vec![])
                    }
                    None => {
                        // We constrain the upper and lower bounds to be equal
                        // between themselves and with the type variable.
                        let e1 = utils::sub_type(
                            env,
                            None,
                            None,
                            None,
                            None,
                            up_ty,
                            tvar.clone(),
                            subtype_error.clone(),
                        );
                        let e2 = utils::sub_type(
                            env,
                            None,
                            None,
                            None,
                            None,
                            tvar.clone(),
                            lo_ty,
                            subtype_error.clone(),
                        );
                        (option_merge(e1, e2, typing_error::both), vec![])
                    }
                }
            }
            (_, ConstraintType_::ThasTypeMember(_))
            | (_, ConstraintType_::ThasMember(_))
            | (_, ConstraintType_::TcanIndex(_))
            | (_, ConstraintType_::TcanIndexAssign(_))
            | (_, ConstraintType_::TcanTraverse(_))
            | (_, ConstraintType_::TtypeSwitch { .. })
            | (_, ConstraintType_::ThasConst { .. })
            | (_, ConstraintType_::Tdestructure(_)) => (None, vec![]),
        },
    };
    make_equal(env, ty)
}

/// Add a type constant with id `tyconstid` and type `ty` to a type variable,
/// and propagate constraints to all type constants `tyconstid` of upper bounds and
/// lower bounds.
fn add_tyvar_type_const(
    env: &mut Env,
    var: tvid::T,
    tconstid: &PosId,
    ty: &Ty,
    on_error: Option<reasons_callback::T>,
) -> (Option<typing_error::T>, Vec<CycleReporter>) {
    typing_env::set_tyvar_type_const(env, var, tconstid.clone(), ty.clone());
    let var_pos = typing_env::get_tyvar_pos(env, var);
    let upper_bounds = typing_env::get_tyvar_upper_bounds(env, var);
    // `ty_errs` is the OCaml list of errors, reversed. The OCaml prepends the
    // cycles of each bound to those of the bounds before it: here they are
    // kept bound by bound, in the order of the bounds.
    let mut ty_errs: Vec<typing_error::T> = vec![];
    let mut cycles_upper: Vec<Vec<CycleReporter>> = vec![];
    for bound in upper_bounds.iter() {
        // Skip upper bounds like mixed and supportdyn<mixed> that don't
        // have type constants. Expanding type constants on these types
        // returns Missing, leading to unsound Tany.
        let bound_is_mixed = match bound {
            InternalType::LoclType(lty) => {
                // The environment of `strip_supportdyn` is dropped.
                let mut env = env.clone();
                let (_is_supportdyn, lty) = utils::strip_supportdyn(&mut env, lty.clone());
                utils::is_mixed(&env, &lty)
            }
            _ => false,
        };
        if bound_is_mixed {
        } else {
            let (err, cycles) = make_type_const_equal(
                env,
                ty,
                bound,
                tconstid,
                on_error.clone(),
                Some(var_pos.clone()),
            );
            ty_errs.extend(err);
            cycles_upper.push(cycles);
        }
    }
    let lower_bounds = typing_env::get_tyvar_lower_bounds(env, var);
    let mut cycles_lower: Vec<Vec<CycleReporter>> = vec![];
    for bound in lower_bounds.iter() {
        let (err, cycles) =
            make_type_const_equal(env, ty, bound, tconstid, on_error.clone(), None);
        ty_errs.extend(err);
        cycles_lower.push(cycles);
    }
    ty_errs.reverse();
    // `cycles_lower @ cycles_upper`, each the cycles of the last bound first.
    let cycles: Vec<CycleReporter> = cycles_lower
        .into_iter()
        .rev()
        .flatten()
        .chain(cycles_upper.into_iter().rev().flatten())
        .collect();
    (typing_error::multiple_opt(ty_errs), cycles)
}

/// [make_all_type_consts_equal env v ty] makes the types of
/// all type constants T of type variable v equal to `ty`::T
pub fn make_all_type_consts_equal(
    env: &mut Env,
    var: tvid::T,
    ty: &InternalType,
    on_error: Option<reasons_callback::T>,
    as_tyvar_with_cnstr: bool,
) -> Option<typing_error::T> {
    // Not in the OCaml: without type constants on `var` (the usual case) the
    // fold below does nothing whatever `is_mixed` says, and `is_mixed` has no
    // effect (it asks in copies of the environment, about `mixed <: t` for a
    // localized `t`, which makes no type variable): skip it, unless the
    // dependency edges are recorded (`is_mixed` looks classes up, and the
    // lookups record edges).
    let tconsts = typing_env::get_tyvar_type_consts(env, var);
    if tconsts.is_empty() && !typing_env::deps::records_dependency_edges(env) {
        return None;
    }
    let is_mixed = match ty {
        InternalType::LoclType(lty) => {
            // The environment of `strip_supportdyn` is dropped.
            let mut env = env.clone();
            let (_is_supportdyn, lty) = utils::strip_supportdyn(&mut env, lty.clone());
            utils::is_mixed(&env, &lty)
        }
        _ => false,
    };
    if is_mixed {
        None
    } else {
        let var_pos = typing_env::get_tyvar_pos(env, var);
        let as_tyvar_with_cnstr = if as_tyvar_with_cnstr {
            Some(var_pos)
        } else {
            None
        };
        // The OCaml list of errors, reversed.
        let mut ty_errs: Vec<typing_error::T> = vec![];
        for (_, (tconstid, tconstty)) in tconsts.iter() {
            let (err, _cycles) = make_type_const_equal(
                env,
                tconstty,
                ty,
                tconstid,
                on_error.clone(),
                as_tyvar_with_cnstr.clone(),
            );
            ty_errs.extend(err);
        }
        ty_errs.reverse();
        typing_error::multiple_opt(ty_errs)
    }
}

/// Get the type of a type constant of a type variable by looking it up in the
/// environment.
/// If that type constant is not present, make a fresh invariant
/// type variable and add it as the type of the type constant in the environment.
///
/// `p` is the position where var::tconstid was encountered.
pub fn get_tyvar_type_const(
    env: &mut Env,
    var: tvid::T,
    tconstid: &PosId,
    on_error: Option<reasons_callback::T>,
) -> (Option<typing_error::T>, Vec<CycleReporter>, Ty) {
    match typing_env::get_tyvar_type_const(env, var, tconstid) {
        Some((_pos, ty)) => (None, vec![], ty),
        None => {
            let var_pos = typing_env::get_tyvar_pos(env, var);
            let tvar = typing_env::fresh_type_invariant(env, var_pos.clone());
            typing_log::log_new_tvar_for_tconst(env, (&var_pos, var), tconstid, &tvar);
            let (err, cycles) = add_tyvar_type_const(env, var, tconstid, &tvar, on_error);
            (err, cycles, tvar)
        }
    }
}
