// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 12801-12823): module `Expression_tree`.
//! See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::tast;
use crate::typing::expr;
use crate::typing::prelude::*;
use crate::typing_defs::Ty;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_types::Env;

pub fn expression_tree(env: &mut Env, p: &Pos, et: &nast::ExpressionTree) -> (tast::Expr, Ty) {
    let aast::ExpressionTree {
        class: et_class,
        runtime_expr: et_runtime_expr,
        free_vars: et_free_vars,
    } = et;

    let (t_runtime_expr, ty_runtime_expr) =
        env::with_inside_expr_tree(env, et_class.clone(), |env| {
            expr::expr(None, &expr::context::default(), env, et_runtime_expr)
        });

    make_result(
        env,
        p.clone(),
        aast::Expr_::ExpressionTree(Box::new(aast::ExpressionTree {
            class: et_class.clone(),
            runtime_expr: t_runtime_expr,
            free_vars: et_free_vars.clone(),
        })),
        ty_runtime_expr,
    )
}
