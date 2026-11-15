// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing.ml` (lines 14234-14294): the top-level functions after the recursive group.
//! See `hh/PORTING.md`.
//!
//! External API (`typing.mli`), re-exported at `crate::typing::*`. The
//! modules of the group are named by their full path here
//! (`crate::typing::expr::expr`), since this module defines functions of the
//! same names.

use oxidized::aast;
use oxidized::ast_defs;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::decl_counters;
use crate::folded_class as cls;
use crate::tast;
use crate::typing::file_attribute;
use crate::typing::lambda;
use crate::typing::tparam;
use crate::typing::user_attribute;
use crate::typing_argument::DynFuncKind;
use crate::typing_defs::DeclTy;
use crate::typing_defs::Ty;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_return_info;
use crate::typing_env_types::Env;
// module ExpectedTy = Typing_helpers.ExpectedTy
use crate::typing_helpers::expected_ty;
use crate::typing_reason::T as Reason;

pub fn bind_params(
    env: &mut Env,
    can_read_globals: Option<bool>,
    no_auto_likes: bool,
    ctxts_opt: Option<&aast::Contexts>,
    tys: &[Option<Ty>],
    params: &[nast::FunParam],
) -> Vec<tast::FunParam> {
    lambda::bind_params(env, can_read_globals, no_auto_likes, ctxts_opt, tys, params)
}

pub fn fun_(
    abstract_: Option<bool>,
    native: Option<bool>,
    disable: Option<bool>,
    env: &mut Env,
    return_info: typing_env_return_info::T,
    pos: &Pos,
    func_body: &nast::FuncBody,
    fun_kind: ast_defs::FunKind,
) -> Vec<tast::Stmt> {
    lambda::fun_(
        abstract_,
        native,
        disable,
        env,
        return_info,
        pos,
        func_body,
        fun_kind,
    )
}

pub fn attributes_check_def(
    env: &mut Env,
    name: &str,
    user_attrs: &[nast::UserAttribute],
) -> Vec<tast::UserAttribute> {
    user_attribute::attributes_check_def(env, name, user_attrs)
}

/// Typechecks a call.
/// Returns in this order the typed expressions for the arguments, for the
/// variadic arguments, the return type, and a boolean indicating whether fake
/// members should be forgotten. If dynamic_func is not None, then we are trying
/// to call the function with dynamic arguments using the fact that is is a SDT
/// function. That is, we have already ruled out trying to call it with just its
/// declared type.
///
/// `?nullsafe:Pos.t option` is `Option<Option<Pos>>`, passed on as it is.
pub fn call(
    expected: Option<&expected_ty::T>,
    nullsafe: Option<Option<Pos>>,
    in_await: Option<Reason>,
    dynamic_func: Option<DynFuncKind>,
    expr_pos: &Pos,
    recv_pos: &Pos,
    id_pos: &Pos,
    env: &mut Env,
    fty: Ty,
    params: &[nast::Argument],
    unpacked_element: Option<&nast::Expr>,
) -> (Vec<tast::Argument>, Option<tast::Expr>, Ty, bool) {
    crate::typing::expr::call(
        expected,
        nullsafe,
        None,
        in_await,
        dynamic_func,
        expr_pos,
        recv_pos,
        id_pos,
        env,
        fty,
        params,
        unpacked_element,
    )
}

pub fn check_function_dynamically_callable(
    this_class: Option<&cls::T>,
    env: &mut Env,
    f_name: Option<&aast::Sid>,
    f: &nast::Fun_,
    params_decl_ty: &[Option<DeclTy>],
    ret_locl_ty: &Ty,
) -> (Vec<tast::FunParam>, Vec<tast::Stmt>, Ty) {
    lambda::check_function_dynamically_callable(
        this_class,
        env,
        f_name,
        f,
        params_decl_ty,
        ret_locl_ty,
    )
}

pub fn type_param(env: &mut Env, tparam: &nast::Tparam) -> tast::Tparam {
    tparam::type_param(env, tparam)
}

pub fn file_attributes(env: &mut Env, file_attrs: &[nast::FileAttribute]) -> Vec<tast::FileAttribute> {
    file_attribute::file_attributes(env, file_attrs)
}

pub fn expr(expected: Option<&expected_ty::T>, env: &mut Env, e: &nast::Expr) -> (tast::Expr, Ty) {
    env::with_origin2(env, decl_counters::Origin::Body, |env| {
        crate::typing::expr::expr(
            expected,
            &crate::typing::expr::context::default(),
            env,
            e,
        )
    })
}

pub fn expr_with_pure_coeffects(
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    e: &nast::Expr,
) -> (tast::Expr, Ty) {
    env::with_origin2(env, decl_counters::Origin::Body, |env| {
        crate::typing::expr::expr_with_pure_coeffects(expected, env, e)
    })
}

pub fn stmt(env: &mut Env, st: &nast::Stmt) -> tast::Stmt {
    env::with_origin(env, decl_counters::Origin::Body, |env| {
        crate::typing::stmt::stmt(env, st)
    })
}
