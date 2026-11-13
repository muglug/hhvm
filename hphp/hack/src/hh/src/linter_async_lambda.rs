// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_async_lambda.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).
//!
//! This lint advises users to use
//!   `async params ==> await ...`
//! instead of
//!   `params ==> ...`
//! when `...` is an `Awaitable`.
//!
//! The reason is the former produces better stack traces and gets optimised
//! more aggressively.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::FunKind;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
/// `module T = Typing_defs`
use crate::typing_defs as t;

fn is_awaitable(env: &Env, ty: &tast::Ty) -> bool {
    let ty = tast_env::expand_type(&mut env.clone(), ty.clone());
    match t::get_node(&ty) {
        t::Ty_::Tclass(id, _, _) => id.1 == sn::classes::AWAITABLE,
        _ => false,
    }
}

fn is_awaitable_awaitable(env: &Env, ty: &tast::Ty) -> bool {
    let ty = tast_env::strip_dynamic(env, ty.clone());
    let mut env = env.clone();
    let ty = tast_env::expand_type(&mut env, ty);
    match t::get_node(&ty) {
        t::Ty_::Tclass(id, _, tyl) if tyl.len() == 1 && id.1 == sn::classes::AWAITABLE => {
            let ty = tast_env::strip_dynamic(&env, tyl[0].clone());
            let ty = tast_env::expand_type(&mut env.clone(), ty);
            match t::get_node(&ty) {
                t::Ty_::Tclass(id, _, _) => id.1 == sn::classes::AWAITABLE,
                _ => false,
            }
        }
        _ => false,
    }
}

fn is_fsync(k: FunKind) -> bool {
    match k {
        FunKind::FSync => true,
        _ => false,
    }
}

fn is_await(e: &tast::Expr_) -> bool {
    match e {
        aast::Expr_::Await(_) => true,
        _ => false,
    }
}

fn simple_body(b: &[tast::Stmt]) -> Option<(&tast::Ty, &tast::Expr_)> {
    match b {
        [aast::Stmt(_, aast::Stmt_::Return(r))] => match &**r {
            Some(aast::Expr(ty, _, e)) => Some((ty, e)),
            None => None,
        },
        _ => None,
    }
}

fn async_lambda_cond(env: &Env, ty: &tast::Ty, e: &tast::Expr_, f_fun_kind: FunKind) -> bool {
    is_awaitable(env, ty) && !is_await(e) && is_fsync(f_fun_kind)
}

fn awaitable_awaitable_cond(env: &Env, ret: &aast::TypeHint<tast::Ty>) -> bool {
    match ret {
        aast::TypeHint(ty, None) => is_awaitable_awaitable(env, ty),
        _ => false,
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, aast::Expr(_, pos, e): &'a tast::Expr) {
        let f = match e {
            aast::Expr_::Lfun(lf) => Some(&lf.0),
            aast::Expr_::Efun(ef) => Some(&ef.fun),
            _ => None,
        };
        match f {
            Some(f) => {
                let (f_fun_kind, f_ret, fb_ast) = (f.fun_kind, &f.ret, &f.body.fb_ast.0);
                match simple_body(fb_ast) {
                    Some((ty, e)) => {
                        if async_lambda_cond(env, ty, e, f_fun_kind) {
                            crate::lints_diagnostics::async_lambda(*pos)
                        } else if awaitable_awaitable_cond(env, f_ret) {
                            crate::lints_diagnostics::awaitable_awaitable(*pos)
                        }
                    }
                    None => {
                        if awaitable_awaitable_cond(env, f_ret) {
                            crate::lints_diagnostics::awaitable_awaitable(*pos)
                        }
                    }
                }
            }
            None => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
