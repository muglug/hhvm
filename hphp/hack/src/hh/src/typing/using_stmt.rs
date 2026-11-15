// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing.ml` (lines 13000-13099): module `Using_stmt`.
//! See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::local_id::LocalId;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::tast;
use crate::typing::expr;
use crate::typing::prelude::*;
use crate::typing_defs::Ty;
use crate::typing_env_types::Env;
use crate::typing_error::callback;
use crate::typing_error_utils;
use crate::typing_helpers;
// module TOG = Typing_object_get
use crate::typing_object_get as tog;

/// Ensure that `ty` is a subtype of IDisposable (for `using`) or
/// IAsyncDisposable (for `await using`)
pub(crate) fn has_dispose_method(
    env: &mut Env,
    has_await: bool,
    p: &Pos,
    e: &nast::Expr,
    ty: Ty,
) {
    let meth = if has_await {
        sn::members::__DISPOSE_ASYNC
    } else {
        sn::members::__DISPOSE
    };
    let aast::Expr(_, obj_pos, _) = e;
    let (ty_err_opt, (tfty, _tal)) = tog::obj_get(
        obj_pos.clone(),
        true,
        None,
        None,
        &[],
        &aast::ClassId_::CIexpr(e.clone()),
        &ast_defs::Id(p.clone(), meth.to_string()),
        callback::using_error(p.clone(), has_await),
        None,
        env,
        ty,
    );
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    let (_tel, _typed_unpack_element, _ty, _should_forget_fakes) = expr::call(
        None,
        None,
        None,
        None,
        None,
        p,
        obj_pos,
        p,
        env,
        tfty,
        &[],
        None,
    );
}

/// Check an individual component in the expression `e` in the
/// `using (e) { ... }` statement.
/// This consists of either
///   a simple assignment `$x = e`, in which `$x` is the using variable, or
///   an arbitrary expression `e`, in which case a temporary is the using
///      variable, inaccessible in the source.
/// Return the typed expression and its type, and any variables that must
/// be designated as "using variables" for avoiding escapes.
pub(crate) fn check_using_expr(
    has_await: bool,
    env: &mut Env,
    using_clause: &nast::Expr,
) -> (tast::Expr, Vec<LocalId>) {
    let aast::Expr(_, pos, content) = using_clause;
    // Simple assignment to local of form `$lvar = e`
    let simple_assignment = match content {
        aast::Expr_::Assign(assign) => match &**assign {
            (aast::Expr(_, lvar_pos, aast::Expr_::Lvar(lvar)), None, e) => {
                Some((lvar_pos, &**lvar, e))
            }
            _ => None,
        },
        _ => None,
    };
    match simple_assignment {
        Some((lvar_pos, lvar, e)) => {
            let (te, ty) = expr::expr(
                None,
                &expr::context::T {
                    is_using_clause: true,
                    ..expr::context::default()
                },
                env,
                e,
            );
            has_dispose_method(env, has_await, pos, e, ty.clone());
            set_valid_rvalue(
                Some(true),
                lvar.0.clone(),
                env,
                lvar.1.clone(),
                None,
                ty.clone(),
            );
            let inner_tast = typing_helpers::make_simplify_typed_expr(
                env,
                lvar_pos.clone(),
                ty.clone(),
                aast::Expr_::Lvar(Box::new(lvar.clone())),
            );
            let tast = typing_helpers::make_simplify_typed_expr(
                env,
                pos.clone(),
                ty,
                aast::Expr_::Assign(Box::new((inner_tast, None, te))),
            );
            (tast, vec![lvar.1.clone()])
        }
        // Arbitrary expression. This will be assigned to a temporary
        None => {
            let (typed_using_clause, ty) = expr::expr(
                None,
                &expr::context::T {
                    is_using_clause: true,
                    ..expr::context::default()
                },
                env,
                using_clause,
            );
            has_dispose_method(env, has_await, pos, using_clause, ty);
            (typed_using_clause, vec![])
        }
    }
}

pub fn check_using_clause(
    env: &mut Env,
    has_await: bool,
    using_clauses: &[nast::Expr],
) -> (Vec<tast::Expr>, Vec<LocalId>) {
    let pairs: Vec<(tast::Expr, Vec<LocalId>)> = using_clauses
        .iter()
        .map(|using_clause| check_using_expr(has_await, env, using_clause))
        .collect();
    let (typed_using_clauses, vars): (Vec<tast::Expr>, Vec<Vec<LocalId>>) =
        pairs.into_iter().unzip();
    (typed_using_clauses, vars.into_iter().flatten().collect())
}
