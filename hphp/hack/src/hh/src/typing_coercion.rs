// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_coercion.ml`. See `hh/PORTING.md`.
//!
//! These are the main coercion functions. Roughly, coercion should be used over
//! subtyping in places where a particular type that could be dynamic is
//! required, like parameters and returns.
//!
//! The old dynamic uses the following ideas:
//!
//! There are only a few coercion (~>) rules, documented in hphp/hack/doc/type_system/hack_typing.ott.
//!
//! 1. |- t ~> dynamic
//!    (you can coerce t to dynamic)
//! 2. t is enforceable |- dynamic ~> t
//!    (coercion from dynamic to enforceable types is permitted)
//! 3. T1 ~> T and T2 ~> T |- T1|T2 ~> T
//!    (coercion from a union is valid if coercion from each element is valid)
//! 4. t1 <: t2 |- t1 ~> t2
//!    (you can coerce t1 to any of its supertypes)
//!
//! This boils down to running the normal sub_type procedure whenever possible,
//! and catching the remaining cases. The normal sub_type procedure is important
//! for resolving/inferring various types (e.g. array's union types), as well as
//! useful to the user for error messages. In the cases where we do not want to
//! sub_type, it suffices to do nothing.
//!
//! # Notes on the port
//!
//! - `coerce_type` is defined twice in OCaml: the second definition (with the
//!   optional arguments and the logging) shadows the first, which only it
//!   calls. Here the first is a function of the same name nested in the
//!   second.
//! - The `'a` that `Typing_log.log_function` gets is the environment with the
//!   result, as in `typing_subtype/prelude.rs`.
//! - `coerce_type_like_strip` tries twice from the same environment and keeps
//!   one of the two environments: the one it starts from is saved, and the
//!   one it returns ends up in `*env`.

use bstr::BString;
use oxidized::message::Message;
use oxidized::pos::Pos;

use crate::diagnostics_state;
use crate::pos_or_decl;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_log;
use crate::typing_make_type;
use crate::typing_print;
/// `module Reason = Typing_reason` (through `Typing_defs`)
use crate::typing_reason as reason;
use crate::typing_reason::Ureason;
use crate::typing_utils;

/// `module Log`
mod log {
    use super::*;

    pub fn should_log_coerce_type(env: &Env) -> bool {
        typing_log::should_log(env, "typing", 2)
    }

    /// `log_coerce_type env p ~ty_have ~ty_expect f`
    pub fn log_coerce_type(
        env: &mut Env,
        p: &Pos,
        ty_have: &Ty,
        ty_expect: &Ty,
        f: impl FnOnce(&mut Env) -> Option<typing_error::T>,
    ) -> Option<typing_error::T> {
        let arguments = vec![
            ("ty_expect".to_string(), typing_print::debug(env, ty_expect)),
            ("ty_have".to_string(), typing_print::debug(env, ty_have)),
        ];
        let (_env, err_opt) = typing_log::log_function(
            &pos_or_decl::of_raw_pos(p.clone()),
            "Typing_coercion.coerce_type",
            &arguments,
            |(_env, err_opt): &(&mut Env, Option<typing_error::T>)| {
                Some(
                    match err_opt {
                        None => "ok",
                        Some(_) => "error",
                    }
                    .to_string(),
                )
            },
            move || {
                let err_opt = f(env);
                (env, err_opt)
            },
        );
        err_opt
    }

    /// `log_coerce_type_against_expected_type env p ~ty_have ~ty_expect f`
    pub fn log_coerce_type_against_expected_type(
        env: &mut Env,
        p: &Pos,
        ty_have: &Ty,
        ty_expect: &Ty,
        f: impl FnOnce(&mut Env) -> typing_utils::ExpectedSubtypingResult,
    ) -> typing_utils::ExpectedSubtypingResult {
        let arguments = vec![
            ("ty_expect".to_string(), typing_print::debug(env, ty_expect)),
            ("ty_have".to_string(), typing_print::debug(env, ty_have)),
        ];
        typing_log::log_function(
            &pos_or_decl::of_raw_pos(p.clone()),
            "Typing_coercion.coerce_type_against_expected_type",
            &arguments,
            |result: &typing_utils::ExpectedSubtypingResult| {
                Some(
                    match result {
                        typing_utils::ExpectedSubtypingResult::SubtypingResult(None) => "ok",
                        typing_utils::ExpectedSubtypingResult::SubtypingResult(Some(_)) => "error",
                        typing_utils::ExpectedSubtypingResult::AmbiguousShapeSplat(_) => {
                            "ambiguous_shape_splat"
                        }
                    }
                    .to_string(),
                )
            },
            move || f(env),
        )
    }
}

/// `lazy (p, Reason.string_of_ureason ur)`, the claim of the coercion errors.
fn claim(p: &Pos, ur: &Ureason) -> Lazy<Message<Pos>> {
    let p = p.clone();
    let ur = ur.clone();
    Lazy::new(move || Message(p, BString::from(reason::string_of_ureason(&ur))))
}

/// does coercion, including subtyping
///
/// `sub_type ~is_dynamic_aware ~ignore_readonly env ty_have ty_expect
/// on_error` is `sub_type(is_dynamic_aware, ignore_readonly, env, ty_have,
/// ty_expect, on_error)`.
fn coerce_type_impl_with_sub_type<A>(
    sub_type: impl FnOnce(bool, bool, &mut Env, Ty, Ty, Option<reasons_callback::T>) -> A,
    coerce_for_op: bool,
    is_dynamic_aware: bool,
    ignore_readonly: bool,
    env: &mut Env,
    ty_have: Ty,
    ty_expect: Ty,
    ty_expect_enforced: Enforcement,
    on_error: Option<reasons_callback::T>,
) -> A {
    let is_expected_enforced = matches!(ty_expect_enforced, Enforcement::Enforced);
    if coerce_for_op && is_expected_enforced {
        // If the coercion is for a built-in operation, then we want to allow it to apply to
        // dynamic
        let tunion = typing_make_type::locl_like(
            reason::dynamic_coercion(get_reason(&ty_expect).clone()),
            ty_expect,
        );
        sub_type(
            false, // is_dynamic_aware
            ignore_readonly,
            env,
            ty_have,
            tunion,
            on_error,
        )
    } else {
        let ety_expect = typing_env::expand_type(env, ty_expect.clone());
        match get_node(&ety_expect) {
            Ty_::Tdynamic(_) => sub_type(
                true, // is_dynamic_aware
                ignore_readonly,
                env,
                ty_have,
                ty_expect,
                on_error,
            ),
            _ => sub_type(
                is_dynamic_aware,
                ignore_readonly,
                env,
                ty_have,
                ty_expect,
                on_error,
            ),
        }
    }
}

fn coerce_type_impl(
    coerce_for_op: bool,
    is_dynamic_aware: bool,
    ignore_readonly: bool,
    env: &mut Env,
    ty_have: Ty,
    ty_expect: Ty,
    ty_expect_enforced: Enforcement,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    coerce_type_impl_with_sub_type(
        |is_dynamic_aware, ignore_readonly, env, ty_have, ty_expect, on_error| {
            typing_utils::sub_type(
                env,
                Some(is_dynamic_aware),
                None, // is_coeffect
                Some(ignore_readonly),
                None, // class_sub_classname
                ty_have,
                ty_expect,
                on_error,
            )
        },
        coerce_for_op,
        is_dynamic_aware,
        ignore_readonly,
        env,
        ty_have,
        ty_expect,
        ty_expect_enforced,
        on_error,
    )
}

pub fn coerce_type(
    coerce_for_op: Option<bool>,
    is_dynamic_aware: Option<bool>,
    ignore_readonly: Option<bool>,
    p: Pos,
    ur: Ureason,
    env: &mut Env,
    ty_have: Ty,
    ty_expect: Ty,
    ty_expect_enforced: Enforcement,
    on_error: callback::T,
) -> Option<typing_error::T> {
    /// The first OCaml definition, which the second one shadows.
    fn coerce_type(
        coerce_for_op: bool,
        is_dynamic_aware: bool,
        ignore_readonly: bool,
        p: Pos,
        ur: Ureason,
        env: &mut Env,
        ty_have: Ty,
        ty_expect: Ty,
        ty_expect_enforced: Enforcement,
        on_error: callback::T,
    ) -> Option<typing_error::T> {
        coerce_type_impl(
            coerce_for_op,
            is_dynamic_aware,
            ignore_readonly,
            env,
            ty_have,
            ty_expect,
            ty_expect_enforced,
            Some(reasons_callback::with_claim(on_error, claim(&p, &ur))),
        )
    }
    let coerce_for_op = coerce_for_op.unwrap_or(false);
    let is_dynamic_aware = is_dynamic_aware.unwrap_or(false);
    let ignore_readonly = ignore_readonly.unwrap_or(false);
    if log::should_log_coerce_type(env) {
        let (ty_have_, ty_expect_) = (ty_have.clone(), ty_expect.clone());
        log::log_coerce_type(env, &p.clone(), &ty_have_, &ty_expect_, move |env| {
            coerce_type(
                coerce_for_op,
                is_dynamic_aware,
                ignore_readonly,
                p,
                ur,
                env,
                ty_have,
                ty_expect,
                ty_expect_enforced,
                on_error,
            )
        })
    } else {
        coerce_type(
            coerce_for_op,
            is_dynamic_aware,
            ignore_readonly,
            p,
            ur,
            env,
            ty_have,
            ty_expect,
            ty_expect_enforced,
            on_error,
        )
    }
}

pub fn coerce_type_against_expected_type(
    coerce_for_op: Option<bool>,
    is_dynamic_aware: Option<bool>,
    ignore_readonly: Option<bool>,
    p: Pos,
    ur: Ureason,
    env: &mut Env,
    ty_have: Ty,
    ty_expect: Ty,
    ty_expect_enforced: Enforcement,
    on_error: callback::T,
) -> typing_utils::ExpectedSubtypingResult {
    let coerce_for_op = coerce_for_op.unwrap_or(false);
    let is_dynamic_aware = is_dynamic_aware.unwrap_or(false);
    let ignore_readonly = ignore_readonly.unwrap_or(false);
    let (ty_have_, ty_expect_) = (ty_have.clone(), ty_expect.clone());
    let p_ = p.clone();
    let check = move |env: &mut Env| {
        coerce_type_impl_with_sub_type(
            |is_dynamic_aware, ignore_readonly, env, ty_have, ty_expect, on_error| {
                typing_utils::sub_type_against_expected_type(
                    env,
                    Some(is_dynamic_aware),
                    Some(ignore_readonly),
                    ty_have,
                    ty_expect,
                    on_error,
                )
            },
            coerce_for_op,
            is_dynamic_aware,
            ignore_readonly,
            env,
            ty_have,
            ty_expect,
            ty_expect_enforced,
            Some(reasons_callback::with_claim(on_error, claim(&p, &ur))),
        )
    };
    if log::should_log_coerce_type(env) {
        log::log_coerce_type_against_expected_type(env, &p_, &ty_have_, &ty_expect_, check)
    } else {
        check(env)
    }
}

/// The OCaml returns `(env, ty_mismatch, used_dynamic, ty)`.
pub fn coerce_type_like_strip(
    p: Pos,
    ur: Ureason,
    env: &mut Env,
    ty_have: Ty,
    ty_expect: Ty,
    on_error: callback::T,
) -> (Option<(Ty, Ty)>, bool, Ty) {
    // The second attempt starts from `env`, as it was before the first.
    let env0 = env.clone();
    // `env1`: `*env` after this call.
    let ty_err_opt = coerce_type_impl(
        false, // coerce_for_op
        false, // is_dynamic_aware
        false, // ignore_readonly
        env,
        ty_have.clone(),
        ty_expect.clone(),
        Enforcement::Unenforced,
        Some(reasons_callback::with_claim(on_error, claim(&p, &ur))),
    );
    match ty_err_opt {
        None => (None, false, ty_have),
        Some(_) => {
            let env1 = std::mem::replace(env, env0);
            // `env2`: `*env` from here on.
            let fresh_ty = typing_env::fresh_type(env, p.clone());
            let like_ty = typing_utils::union(
                env,
                None,
                None,
                fresh_ty.clone(),
                typing_make_type::dynamic(get_reason(&fresh_ty).clone()),
            );
            let cb = reasons_callback::unify_error_at(p.clone());
            let impossible_error = typing_utils::sub_type(
                env,
                None,
                None,
                None,
                None,
                fresh_ty.clone(),
                ty_expect.clone(),
                Some(cb),
            );
            // Enforce the invariant - this call should never give us an error
            if impossible_error.is_some() {
                diagnostics_state::internal_error(p.clone(), "Subtype of fresh type variable");
            }
            let ty_err_opt_like = coerce_type(
                None,
                None,
                None,
                p,
                Ureason::URnone,
                env,
                ty_have.clone(),
                like_ty,
                Enforcement::Unenforced,
                callback::unify_error(),
            );
            match ty_err_opt_like {
                None => (None, true, fresh_ty),
                Some(_) => {
                    *env = env1;
                    if let Some(ty_err) = &ty_err_opt {
                        typing_error_utils::add_typing_error(ty_err, env);
                    }
                    let ty_mismatch = ty_err_opt.map(|_| (ty_have.clone(), ty_expect));
                    (ty_mismatch, false, ty_have)
                }
            }
        }
    }
}
