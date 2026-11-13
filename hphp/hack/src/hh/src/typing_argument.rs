// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_argument.ml`. See `hh/PORTING.md`.

use oxidized::pos::Pos;

use crate::pos_or_decl;
use crate::typing_coercion;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::get_reason;
use crate::typing_dynamic_utils;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_log;
use crate::typing_make_type;
use crate::typing_reason::Ureason;
use crate::typing_utils;

/// `type dyn_func_kind`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DynFuncKind {
    SupportdynFunction,
    LikeFunction,
}

fn mk_ty_mismatch_opt<E>(ty_have: Ty, ty_expect: Ty, e: Option<&E>) -> Option<(Ty, Ty)> {
    match e {
        Some(_) => Some((ty_have, ty_expect)),
        _ => None,
    }
}

fn check_argument_type_against_parameter_type_helper(
    dynamic_func: Option<DynFuncKind>,
    ignore_readonly: bool,
    ureason: Ureason,
    env: &mut Env,
    pos: Pos,
    param_ty: Ty,
    arg_ty: Ty,
) -> Option<typing_error::T> {
    {
        let env: &Env = env;
        typing_log::log_with_level(env, "typing", 2, || {
            typing_log::log_types(
                &pos_or_decl::of_raw_pos(pos.clone()),
                env,
                &[typing_log::LogStructure::LogHead(
                    "Typing.check_argument_type_against_parameter_type_helper ".to_string()
                        + match dynamic_func {
                            None => "None",
                            Some(DynFuncKind::SupportdynFunction) => "sd",
                            Some(DynFuncKind::LikeFunction) => "~",
                        },
                    vec![
                        typing_log::LogStructure::LogType("param_ty".to_string(), param_ty.clone()),
                        typing_log::LogStructure::LogType("arg_ty".to_string(), arg_ty.clone()),
                    ],
                )],
            )
        })
    }
    let param_ty = match dynamic_func {
        Some(dyn_func_kind) => {
            // It is only sound to add like types to the parameters of supportdyn functions, since
            // in this case we are semantically just using the &dynamic part of the type to call them.
            // For like functions, they have to check both sides.
            match dyn_func_kind {
                DynFuncKind::SupportdynFunction => {
                    typing_make_type::locl_like(get_reason(&param_ty).clone(), param_ty)
                }
                DynFuncKind::LikeFunction => param_ty,
            }
        }
        None => param_ty,
    };
    typing_coercion::coerce_type(
        None,
        Some(false),
        Some(ignore_readonly),
        pos,
        ureason,
        env,
        arg_ty,
        param_ty,
        Enforcement::Enforced,
        typing_error::callback::unify_error(),
    )
}

/// Check a single argument type arg_ty against the function parameter type param_ty.
///
/// For functions marked SupportDynamicType (if dynamic_func != None)
/// we attempt a static check, and if that fails, we check against a like-type of param_ty.
///
/// In the case that the argument type is already a like-type,
/// and the parameter type is not, we just skip straight to this dynamic check, in order
/// to avoid the situation where we make poor choices with generic parameters e.g. we
/// attempt ~t <: T to get T:=~t rather than ~t <: ~T to get T := t.
pub fn check_argument_type_against_parameter_type(
    is_single_argument: Option<bool>,
    ureason: Option<Ureason>,
    dynamic_func: Option<DynFuncKind>,
    ignore_readonly: bool,
    env: &mut Env,
    param_ty: Ty,
    arg_pos: Pos,
    arg_ty: Ty,
) -> (Option<(Ty, Ty)>, bool) {
    let is_single_argument = is_single_argument.unwrap_or(false);
    let ureason = ureason.unwrap_or(Ureason::URparam);
    let (opt_e, used_dynamic) = if dynamic_func.is_none() {
        let opt_e = check_argument_type_against_parameter_type_helper(
            None,
            ignore_readonly,
            ureason,
            env,
            arg_pos,
            param_ty.clone(),
            arg_ty.clone(),
        );
        (opt_e, false)
    } else {
        // The environments that `try_strip_dynamic` returns are dropped.
        let check_dynamic_only = !is_single_argument
            && !typing_utils::is_dynamic(env, &param_ty)
            && typing_dynamic_utils::try_strip_dynamic(Some(true), None, &mut env.clone(), &arg_ty)
                .is_some()
            && typing_dynamic_utils::try_strip_dynamic(None, None, &mut env.clone(), &param_ty)
                .is_none();
        if check_dynamic_only {
            // Only try dynamically
            let opt_e = check_argument_type_against_parameter_type_helper(
                dynamic_func,
                ignore_readonly,
                ureason,
                env,
                arg_pos,
                param_ty.clone(),
                arg_ty.clone(),
            );
            (opt_e, true)
        } else {
            let (opt_e, used_dynamic_info) = {
                // Both attempts start from the environment as it is now: `env`
                // becomes `env1`, `env2` starts from this copy.
                let saved_env = env.clone();
                // First try statically
                let e1opt = check_argument_type_against_parameter_type_helper(
                    None,
                    ignore_readonly,
                    ureason.clone(),
                    env,
                    arg_pos.clone(),
                    param_ty.clone(),
                    arg_ty.clone(),
                );
                match e1opt {
                    None => (None, false),
                    Some(e1) => {
                        let mut env2 = saved_env;
                        let e2opt = check_argument_type_against_parameter_type_helper(
                            dynamic_func,
                            ignore_readonly,
                            ureason,
                            &mut env2,
                            arg_pos,
                            param_ty.clone(),
                            arg_ty.clone(),
                        );
                        match e2opt {
                            // We used dynamic calling to get a successful check
                            None => {
                                *env = env2;
                                (None, true)
                            }
                            // We failed on both, pick the one with fewest errors! (preferring static on a tie)
                            Some(e2) => {
                                if typing_error::count(&e1) <= typing_error::count(&e2) {
                                    (Some(e1), false)
                                } else {
                                    *env = env2;
                                    (Some(e2), true)
                                }
                            }
                        }
                    }
                }
            };
            (opt_e, used_dynamic_info)
        }
    };
    if let Some(e) = &opt_e {
        typing_error_utils::add_typing_error(e, env)
    }
    (
        mk_ty_mismatch_opt(arg_ty, param_ty, opt_e.as_ref()),
        used_dynamic,
    )
}
