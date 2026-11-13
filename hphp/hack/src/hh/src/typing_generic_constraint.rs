// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_generic_constraint.ml`. See `hh/PORTING.md`.

use oxidized::ast_defs::ConstraintKind;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::typing_defs::*;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_log;
use crate::typing_utils as t_utils;

/// `Option.merge e1 e2 ~f:Typing_error.both`
fn merge_errs(
    e1: Option<typing_error::T>,
    e2: Option<typing_error::T>,
) -> Option<typing_error::T> {
    match (e1, e2) {
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    }
}

/// Add a constraint to the environment.
/// Raise an error if any inconsistency is detected.
pub fn check_constraint(
    env: &mut Env,
    ck: ConstraintKind,
    ty: Ty,
    cstr_ty: Ty,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    {
        let env: &Env = env;
        typing_log::log_with_level(env, "sub", 1, || {
            typing_log::log_types(
                &get_pos(&ty),
                env,
                &[typing_log::LogStructure::LogHead(
                    "Typing_generic_constraint.check_constraint".to_string(),
                    vec![
                        typing_log::LogStructure::LogType("ty".to_string(), ty.clone()),
                        typing_log::LogStructure::LogType("cstr_ty".to_string(), cstr_ty.clone()),
                    ],
                )],
            )
        })
    }
    if !env::is_consistent(env) {
        None
    } else {
        let ety = env::expand_type(env, ty.clone());
        let ecstr_ty = env::expand_type(env, cstr_ty.clone());
        match ck {
            ConstraintKind::ConstraintAs => {
                t_utils::sub_type(env, None, None, None, Some(false), ety, cstr_ty, on_error)
            }
            ConstraintKind::ConstraintEq => {
                // An equality constraint is the same as two commuting `as`
                // constraints, i.e. X=Y is { X as Y, Y as X }. Thus, add
                // add both expansions to the environment. We don't expand
                // both sides of the equation simultaniously, to preserve an
                // easier convergence indication.
                let e1 = t_utils::sub_type(
                    env,
                    None,
                    None,
                    None,
                    Some(false),
                    ecstr_ty,
                    ty,
                    on_error.clone(),
                );
                let e2 =
                    t_utils::sub_type(env, None, None, None, Some(false), ety, cstr_ty, on_error);
                merge_errs(e1, e2)
            }
            ConstraintKind::ConstraintSuper => {
                t_utils::sub_type(env, None, None, None, Some(false), ecstr_ty, ty, on_error)
            }
        }
    }
}

/// Add an [as] or [super] constraint to the environment.
/// Raise an error if any inconsistency is detected.
pub fn check_tparams_constraint(
    env: &mut Env,
    use_pos: Pos,
    ck: ConstraintKind,
    cstr_ty: Ty,
    ty: Ty,
) -> Option<typing_error::T> {
    check_constraint(
        env,
        ck,
        ty,
        cstr_ty,
        Some(reasons_callback::explain_constraint(use_pos)),
    )
}

/// Add a [where] constraint to the environment.
/// Raise an error if any inconsistency is detected.
pub fn check_where_constraint(
    in_class: bool,
    env: &mut Env,
    use_pos: Pos,
    definition_pos: PosOrDecl,
    ck: ConstraintKind,
    cstr_ty: Ty,
    ty: Ty,
) -> Option<typing_error::T> {
    check_constraint(
        env,
        ck,
        ty,
        cstr_ty,
        Some(reasons_callback::explain_where_constraint(
            use_pos,
            in_class,
            definition_pos,
        )),
    )
}
