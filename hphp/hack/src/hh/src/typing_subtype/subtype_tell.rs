// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 12237-12468): module `Subtype_tell`.
//! See `hh/PORTING.md`.
//!
//! - `sub_type_inner_with_ambiguity` is defined twice in OCaml: the second
//!   definition (logging) shadows the first. Here the first is a function of
//!   the same name nested in the second, so that, as in OCaml, nothing else
//!   can call it.
//! - The entry points return the environment they were given when subtyping
//!   fails (`old_env`): they save it before and restore it.
//! - `sub_type_against_expected_type` returns `TUtils.Ambiguous_shape_splat`
//!   without an environment: the caller goes on with the one it had, so the
//!   environment is restored on that path too. `TUtils.Subtyping_result`
//!   carries the environment in OCaml; here it is the environment updated in
//!   place, and the variant (`typing_utils::ExpectedSubtypingResult::
//!   SubtypingResult`) has the error only.

use crate::tvid;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::reason;
use crate::typing_defs_core::Ty;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_log;
use crate::typing_logic as tl;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype_trans;
use crate::typing_utils as t_utils;

pub(crate) fn sub_type_inner_with_ambiguity(
    env: &mut Env,
    subtype_env: subtype_env::T,
    sub_supportdyn: Option<Reason>,
    this_ty: Option<&Ty>,
    ity_sub: InternalType,
    ity_super: InternalType,
) -> (Option<typing_error::T>, tvid::set::T) {
    /// The first OCaml definition, which the logging one shadows.
    fn sub_type_inner_with_ambiguity(
        env: &mut Env,
        subtype_env: subtype_env::T,
        sub_supportdyn: Option<Reason>,
        this_ty: Option<&Ty>,
        ity_sub: InternalType,
        ity_super: InternalType,
    ) -> (Option<typing_error::T>, tvid::set::T) {
        let prop = common::dispatch_constraint(
            &subtype_env,
            this_ty,
            sub_supportdyn,
            ity_sub.clone(),
            ity_super.clone(),
            env,
        );
        if !tl::is_valid(&prop) {
            typing_log::log_prop(
                1,
                &typing_reason::to_pos(reason(&ity_sub)),
                "sub_type_inner",
                env,
                &prop,
            );
        }
        subtype_trans::prop_to_env_against_expected_type(
            &ity_sub,
            &ity_super,
            env,
            prop,
            subtype_env.on_error,
        )
    }

    if logging::should_log_subtype_i(env, 1, &ity_sub, &ity_super) {
        let function_name = "Typing_subtype.Subtype_tell.sub_type_inner".to_string()
            + match subtype_env.is_dynamic_aware {
                true => " (dynamic aware)",
                false => "",
            };
        // `log_subtype_i` prints with the environment before the call, which
        // the continuation changes: a copy.
        let log_env = env.clone();
        let (log_ity_sub, log_ity_super) = (ity_sub.clone(), ity_super.clone());
        logging::log_subtype_i(
            this_ty,
            &function_name,
            &log_env,
            &log_ity_sub,
            &log_ity_super,
            || {
                sub_type_inner_with_ambiguity(
                    env,
                    subtype_env,
                    sub_supportdyn,
                    this_ty,
                    ity_sub,
                    ity_super,
                )
            },
        )
    } else {
        sub_type_inner_with_ambiguity(
            env,
            subtype_env,
            sub_supportdyn,
            this_ty,
            ity_sub,
            ity_super,
        )
    }
}

pub(crate) fn sub_type_inner(
    env: &mut Env,
    subtype_env: subtype_env::T,
    sub_supportdyn: Option<Reason>,
    this_ty: Option<&Ty>,
    ity_sub: InternalType,
    ity_super: InternalType,
) -> Option<typing_error::T> {
    let (ty_err_opt, _) = sub_type_inner_with_ambiguity(
        env,
        subtype_env,
        sub_supportdyn,
        this_ty,
        ity_sub,
        ity_super,
    );
    ty_err_opt
}

pub(crate) fn sub_type_inner_against_expected_type(
    env: &mut Env,
    subtype_env: subtype_env::T,
    sub_supportdyn: Option<Reason>,
    this_ty: Option<&Ty>,
    ity_sub: InternalType,
    ity_super: InternalType,
) -> (Option<typing_error::T>, tvid::set::T) {
    sub_type_inner_with_ambiguity(
        env,
        subtype_env,
        sub_supportdyn,
        this_ty,
        ity_sub,
        ity_super,
    )
}

/// The outcomes of the entry points below that are remembered: not in the
/// OCaml, it only saves work. For two localized types that the memo of
/// `Subtype_ask` accepts (see `subtype_ask::memo` for the types, the context
/// and why an outcome cannot depend on anything else), a query that reported
/// no error and left the environment as it was (no write at all: `old_env`
/// still shares its fields) and made no type variable or expression id has
/// the same outcome when it is asked again, with the same fields of the
/// subtype environment (`subtype_ask::memo::tell_flags`): it is then not
/// simplified again.
mod tell_memo {
    use super::*;
    use crate::typing_subtype::subtype_ask::memo;

    pub(super) enum Query {
        /// Asked before: no error, no change.
        Known,
        Unsupported,
        /// Known, but checked against the simplifier (`HH_ASK_MEMO_VERIFY`).
        Verify(Ty, Ty),
        Miss {
            sub: Ty,
            sup: Ty,
            flags: u16,
            miss: memo::Miss,
            ids: (isize, isize),
        },
    }

    pub(super) fn lookup(
        env: &Env,
        subtype_env: &subtype_env::T,
        ity_sub: &InternalType,
        ity_super: &InternalType,
    ) -> Query {
        match (ity_sub, ity_super) {
            (InternalType::LoclType(sub), InternalType::LoclType(sup))
                if env.log_levels.is_empty()
                    && subtype_env.has_member_arg_posl.is_none()
                    && subtype_env.visited.is_empty()
                    && subtype_env.visited_internal.is_empty() =>
            {
                let flags = memo::tell_flags(subtype_env);
                match memo::lookup(env, sub, sup, flags) {
                    memo::Lookup::Hit(_) if !memo::verify() => Query::Known,
                    memo::Lookup::Hit(_) => Query::Verify(sub.clone(), sup.clone()),
                    memo::Lookup::Miss(miss) => Query::Miss {
                        sub: sub.clone(),
                        sup: sup.clone(),
                        flags,
                        miss,
                        ids: memo::ids(env),
                    },
                    memo::Lookup::Unsupported => Query::Unsupported,
                }
            }
            _ => Query::Unsupported,
        }
    }

    /// After the query: `ok` is no error (and no ambiguity).
    pub(super) fn record(query: Query, old_env: &Env, env: &Env, ok: bool) {
        match query {
            Query::Miss {
                sub,
                sup,
                flags,
                miss,
                ids,
            } => {
                if ok && Env::ptr_eq(old_env, env) && memo::ids(env) == ids {
                    memo::record(miss, &sub, &sup, flags, Some(true))
                }
            }
            Query::Verify(sub, sup) if !(ok && Env::ptr_eq(old_env, env)) => {
                eprintln!(
                    "HH_ASK_MEMO_VERIFY: tell remembered as valid, but not: {} <: {}",
                    crate::typing_print::debug(env, &sub),
                    crate::typing_print::debug(env, &sup)
                );
            }
            Query::Known | Query::Unsupported | Query::Verify(..) => {}
        }
    }
}

// == Tell API ============================================================

// -- sub_type_i entry point ----------------------------------------------

pub fn sub_type_i(
    env: &mut Env,
    is_coeffect: Option<bool>,
    ty_sub: InternalType,
    ty_super: InternalType,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    let is_coeffect = is_coeffect.unwrap_or(false);
    let subtype_env = subtype_env::create(
        None,                   // require_soundness
        None,                   // require_completeness
        None,                   // ignore_readonly
        None,                   // no_top_bottom
        Some(false),            // is_dynamic_aware
        Some(is_coeffect),      // is_coeffect
        None,                   // in_transitive_closure
        None,                   // ignore_likes
        None,                   // has_member_arg_posl
        None,                   // report_ambiguous_shape_splat
        should_cls_sub_cn(env), // class_sub_classname
        2,                      // log_level
        on_error,
    );
    let old_env = env.clone();
    let query = tell_memo::lookup(env, &subtype_env, &ty_sub, &ty_super);
    let ty_err_opt = if let tell_memo::Query::Known = query {
        None
    } else {
        sub_type_inner(
            env,
            subtype_env,
            None, // sub_supportdyn
            None, // this_ty
            ty_sub,
            ty_super,
        )
    };
    tell_memo::record(query, &old_env, env, ty_err_opt.is_none());
    // `Env.log_env_change "sub_type" old_env @@ if ... then env else old_env`
    if ty_err_opt.is_none() {
        env::log_env_change("sub_type", None, &old_env, env);
    } else {
        env::log_env_change("sub_type", None, &old_env, &old_env);
        *env = old_env;
    }
    ty_err_opt
}

// -- sub_type entry point --------------------------------------------------

/// Entry point asserting top-level subtype constraints and all implied constraints
pub fn sub_type(
    env: &mut Env,
    is_dynamic_aware: Option<bool>,
    is_coeffect: Option<bool>,
    ignore_readonly: Option<bool>,
    class_sub_classname: Option<bool>,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    let is_dynamic_aware = is_dynamic_aware.unwrap_or(false);
    let is_coeffect = is_coeffect.unwrap_or(false);
    let ignore_readonly = ignore_readonly.unwrap_or(false);
    let class_sub_classname = class_sub_classname.unwrap_or_else(|| should_cls_sub_cn(env));
    let subtype_env = subtype_env::create(
        None,                   // require_soundness
        None,                   // require_completeness
        None,                   // ignore_readonly
        None,                   // no_top_bottom
        Some(is_dynamic_aware), // is_dynamic_aware
        Some(is_coeffect),      // is_coeffect
        None,                   // in_transitive_closure
        None,                   // ignore_likes
        None,                   // has_member_arg_posl
        None,                   // report_ambiguous_shape_splat
        class_sub_classname,    // class_sub_classname
        2,                      // log_level
        on_error,
    );
    let subtype_env = subtype_env::T {
        ignore_readonly,
        ..subtype_env
    };
    let old_env = env.clone();
    let (ity_sub, ity_super) = (InternalType::LoclType(ty_sub), InternalType::LoclType(ty_super));
    let query = tell_memo::lookup(env, &subtype_env, &ity_sub, &ity_super);
    let ty_err_opt = if let tell_memo::Query::Known = query {
        None
    } else {
        sub_type_inner(
            env,
            subtype_env,
            None, // sub_supportdyn
            None, // this_ty
            ity_sub,
            ity_super,
        )
    };
    tell_memo::record(query, &old_env, env, ty_err_opt.is_none());
    // `Env.log_env_change "sub_type" old_env @@ if ... then env else old_env`
    if ty_err_opt.is_none() {
        env::log_env_change("sub_type", None, &old_env, env);
    } else {
        env::log_env_change("sub_type", None, &old_env, &old_env);
        *env = old_env;
    }
    ty_err_opt
}

/// Like [`sub_type`], but reports an ambiguous multi-spread shape relation
/// without retaining speculative subtype constraints.
pub fn sub_type_against_expected_type(
    env: &mut Env,
    is_dynamic_aware: Option<bool>,
    ignore_readonly: Option<bool>,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) -> t_utils::ExpectedSubtypingResult {
    let is_dynamic_aware = is_dynamic_aware.unwrap_or(false);
    let ignore_readonly = ignore_readonly.unwrap_or(false);
    let subtype_env = subtype_env::create(
        None,                   // require_soundness
        None,                   // require_completeness
        None,                   // ignore_readonly
        None,                   // no_top_bottom
        Some(is_dynamic_aware), // is_dynamic_aware
        None,                   // is_coeffect
        None,                   // in_transitive_closure
        None,                   // ignore_likes
        None,                   // has_member_arg_posl
        Some(true),             // report_ambiguous_shape_splat
        should_cls_sub_cn(env), // class_sub_classname
        2,                      // log_level
        on_error,
    );
    let subtype_env = subtype_env::T {
        ignore_readonly,
        ..subtype_env
    };
    let old_env = env.clone();
    let (ity_sub, ity_super) = (InternalType::LoclType(ty_sub), InternalType::LoclType(ty_super));
    let query = tell_memo::lookup(env, &subtype_env, &ity_sub, &ity_super);
    let (ty_err_opt, ambiguous_shape_splat_vars) = if let tell_memo::Query::Known = query {
        (None, tvid::set::T::new())
    } else {
        sub_type_inner_against_expected_type(
            env,
            subtype_env,
            None, // sub_supportdyn
            None, // this_ty
            ity_sub,
            ity_super,
        )
    };
    tell_memo::record(
        query,
        &old_env,
        env,
        ty_err_opt.is_none() && ambiguous_shape_splat_vars.is_empty(),
    );
    if ty_err_opt.is_some() {
        env::log_env_change("sub_type", None, &old_env, &old_env);
        *env = old_env;
        t_utils::ExpectedSubtypingResult::SubtypingResult(ty_err_opt)
    } else if ambiguous_shape_splat_vars.is_empty() {
        env::log_env_change("sub_type", None, &old_env, env);
        t_utils::ExpectedSubtypingResult::SubtypingResult(None)
    } else {
        // No environment is returned: the caller goes on with `old_env`.
        *env = old_env;
        t_utils::ExpectedSubtypingResult::AmbiguousShapeSplat(ambiguous_shape_splat_vars)
    }
}

/// As [`sub_type`], but with a simpler error handler that doesn't make use of
/// the code and message list provided by subtyping.
/// Entry point
pub fn sub_type_or_fail(
    env: &mut Env,
    ty1: Ty,
    ty2: Ty,
    err_opt: Option<typing_error::error::T>,
) -> Option<typing_error::T> {
    sub_type(
        env,
        None, // is_dynamic_aware
        None, // is_coeffect
        None, // ignore_readonly
        None, // class_sub_classname
        ty1,
        ty2,
        err_opt.map(reasons_callback::always),
    )
}
