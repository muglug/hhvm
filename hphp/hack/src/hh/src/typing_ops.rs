// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_ops.ml`. See `hh/PORTING.md`.

use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::pos_or_decl;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Ty;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_log;
/// `module Reason = Typing_reason`
use crate::typing_reason;
use crate::typing_reason::Ureason;
use crate::typing_utils;

// ---------------------------------------------------------------------------
// Exporting.
// ---------------------------------------------------------------------------

fn log_sub_type(env: &Env, p: &Pos, ty_sub: &InternalType, ty_super: &InternalType) {
    let level = if !(typing_utils::is_capability_i(ty_sub) || typing_utils::is_capability_i(ty_super))
    {
        1
    } else {
        3
    };
    typing_log::log_with_level(env, "sub", level, || {
        typing_log::log_types(
            &pos_or_decl::of_raw_pos(p.clone()),
            env,
            &[typing_log::LogStructure::LogHead(
                "Typing_ops.sub_type".to_string(),
                vec![
                    typing_log::LogStructure::LogTypeI("ty_sub".to_string(), ty_sub.clone()),
                    typing_log::LogStructure::LogTypeI("ty_super".to_string(), ty_super.clone()),
                ],
            )],
        )
    })
}

fn sub_type_i_apply_reason_callback(
    is_coeffect: Option<bool>,
    class_sub_classname: Option<bool>,
    p: &Pos,
    env: &mut Env,
    ty_sub: InternalType,
    ty_super: InternalType,
    callback: reasons_callback::T,
) -> Option<typing_error::T> {
    let is_coeffect = is_coeffect.unwrap_or(false);
    log_sub_type(env, p, &ty_sub, &ty_super);
    typing_utils::sub_type_i(
        env,
        Some(is_coeffect),
        class_sub_classname,
        ty_sub,
        ty_super,
        Some(callback),
    )
}

/// Add constraint or check that ty_sub is subtype of ty_super in envs
pub fn sub_type_i(
    is_coeffect: Option<bool>,
    class_sub_classname: Option<bool>,
    p: Pos,
    ur: Ureason,
    env: &mut Env,
    ty_sub: InternalType,
    ty_super: InternalType,
    on_error: callback::T,
) -> Option<typing_error::T> {
    let is_coeffect = is_coeffect.unwrap_or(false);
    let claim = {
        let p = p.clone();
        Lazy::new(move || Message(p, typing_reason::string_of_ureason(&ur).into()))
    };
    sub_type_i_apply_reason_callback(
        Some(is_coeffect),
        class_sub_classname,
        &p,
        env,
        ty_sub,
        ty_super,
        reasons_callback::with_claim(on_error, claim),
    )
}

/// Tries to add constraint that ty_sub is subtype of ty_super in envs
fn sub_type_i_w_err_prefix(
    is_coeffect: Option<bool>,
    p: &Pos,
    env: &mut Env,
    ty_sub: InternalType,
    ty_super: InternalType,
    err_prefix: primary::T,
) -> Option<typing_error::T> {
    let is_coeffect = is_coeffect.unwrap_or(false);
    sub_type_i_apply_reason_callback(
        Some(is_coeffect),
        None,
        p,
        env,
        ty_sub,
        ty_super,
        reasons_callback::T::Prefix(std::rc::Rc::new(err_prefix)),
    )
}

pub fn sub_type(
    class_sub_classname: Option<bool>,
    p: Pos,
    ur: Ureason,
    env: &mut Env,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: callback::T,
) -> Option<typing_error::T> {
    sub_type_i(
        None,
        class_sub_classname,
        p,
        ur,
        env,
        InternalType::LoclType(ty_sub),
        InternalType::LoclType(ty_super),
        on_error,
    )
}

/// Assert a type is a sub-type of another.
/// If assertion fails, add error prefix to sub-typing error.
pub fn sub_type_w_err_prefix(
    is_coeffect: Option<bool>,
    p: &Pos,
    env: &mut Env,
    ty_sub: Ty,
    ty_super: Ty,
    err_prefix: primary::T,
) -> Option<typing_error::T> {
    let is_coeffect = is_coeffect.unwrap_or(false);
    sub_type_i_w_err_prefix(
        Some(is_coeffect),
        p,
        env,
        InternalType::LoclType(ty_sub),
        InternalType::LoclType(ty_super),
        err_prefix,
    )
}

pub fn sub_type_decl(
    is_coeffect: Option<bool>,
    class_sub_classname: Option<bool>,
    on_error: reasons_callback::T,
    p: PosOrDecl,
    ur: Ureason,
    env: &mut Env,
    ty_sub: &DeclTy,
    ty_super: &DeclTy,
) -> Option<typing_error::T> {
    let is_coeffect = is_coeffect.unwrap_or(false);
    let localize_no_subst =
        |env: &mut Env, ty: &DeclTy| typing_utils::localize_no_subst(env, true, ty);
    let (ty_err1, ty_super) = localize_no_subst(env, ty_super);
    let (ty_err2, ty_sub) = localize_no_subst(env, ty_sub);
    let ty_err3 = typing_utils::sub_type(
        env,
        None,
        Some(is_coeffect),
        None,
        class_sub_classname,
        ty_sub,
        ty_super,
        Some(reasons_callback::prepend_reason(
            on_error,
            Lazy::new(move || Message(p, typing_reason::string_of_ureason(&ur).into())),
        )),
    );
    typing_error::multiple_opt([ty_err1, ty_err2, ty_err3].into_iter().flatten().collect())
}

/// Ensure that types are equivalent i.e. subtypes of each other
pub fn unify_decl(
    p: PosOrDecl,
    ur: Ureason,
    env: &mut Env,
    on_error: reasons_callback::T,
    ty1: &DeclTy,
    ty2: &DeclTy,
) -> Option<typing_error::T> {
    let localize_no_subst =
        |env: &mut Env, ty: &DeclTy| typing_utils::localize_no_subst(env, true, ty);
    let (ty_err1, ty1) = localize_no_subst(env, ty1);
    let (ty_err2, ty2) = localize_no_subst(env, ty2);
    let reason: Lazy<Message<PosOrDecl>> =
        Lazy::new(move || Message(p, typing_reason::string_of_ureason(&ur).into()));
    let ty_err3 = typing_utils::sub_type(
        env,
        None,
        None,
        None,
        None,
        ty2.clone(),
        ty1.clone(),
        Some(reasons_callback::prepend_reason(on_error.clone(), reason.clone())),
    );
    let ty_err4 = typing_utils::sub_type(
        env,
        None,
        None,
        None,
        None,
        ty1,
        ty2,
        Some(reasons_callback::prepend_reason(on_error, reason)),
    );
    typing_error::multiple_opt(
        [ty_err1, ty_err2, ty_err3, ty_err4]
            .into_iter()
            .flatten()
            .collect(),
    )
}
