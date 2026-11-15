// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/naming_coroutine_check.ml`.

use oxidized::ast_defs::FunKind;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

fn is_sync(env: &Env<'_>) -> bool {
    matches!(
        env.function_kind,
        Some(FunKind::FGenerator) | Some(FunKind::FSync)
    )
}

pub struct NamingCoroutineCheck;

impl<'a> Handler<'a> for NamingCoroutineCheck {
    fn at_expr(&mut self, env: &Env<'a>, e: &'a nast::Expr, errors: &mut Errors) {
        let nast::Expr(_, p, e) = e;
        let keyword = match e {
            nast::Expr_::Await(_) if is_sync(env) => "await",
            nast::Expr_::Delay(_) if is_sync(env) => "delay",
            _ => return,
        };
        errors.add(NastCheckError::AwaitInSyncFunction {
            pos: p.clone(),
            func_pos: env.function_name.map(|sid| sid.0.clone()),
            keyword: keyword.to_string(),
        });
    }

    fn at_stmt(&mut self, env: &Env<'a>, s: &'a nast::Stmt, errors: &mut Errors) {
        let pos = match &s.1 {
            nast::Stmt_::Using(using) if using.has_await && is_sync(env) => &using.exprs.0,
            nast::Stmt_::Foreach(foreach) if is_sync(env) => match &foreach.1 {
                nast::AsExpr::AwaitAsV(p, _) | nast::AsExpr::AwaitAsKv(p, _, _) => p,
                nast::AsExpr::AsV(_) | nast::AsExpr::AsKv(_, _) => return,
            },
            nast::Stmt_::Awaitall(_) if is_sync(env) => &s.0,
            _ => return,
        };
        errors.add(NastCheckError::AwaitInSyncFunction {
            pos: pos.clone(),
            func_pos: None,
            keyword: "await".to_string(),
        });
    }
}
