// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/expression_tree_check.ml`. See `hh/PORTING.md`.

use oxidized::aast::Expr;
use oxidized::aast::Expr_;
use oxidized::ast_defs::Id;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_error;
use crate::typing_error::primary::expr_tree::T as ExprTree;
use crate::typing_error_utils;

/// `handler`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, Expr(_, pos, e): &'a tast::Expr) {
        match e {
            Expr_::ExpressionTree(et) => {
                let tcopt = tast_env::get_tcopt(env);
                // Unstable features file attribute ignores all restrictions
                // (`Typechecker_options.expression_trees_enabled`)
                if tcopt.tco_enable_expression_trees {
                } else {
                    // Otherwise, only allow those visitors in hhconfig
                    // (`Typechecker_options.allowed_expression_tree_visitors`)
                    let allowed_expression_tree_visitors =
                        &tcopt.tco_allowed_expression_tree_visitors;
                    let Id(_pos, id) = &et.class;
                    let err_opt = if allowed_expression_tree_visitors.iter().any(|s| s == id) {
                        None
                    } else {
                        Some(typing_error::expr_tree(
                            ExprTree::ExperimentalExpressionTrees(pos.clone()),
                        ))
                    };
                    if let Some(err) = err_opt {
                        typing_error_utils::add_typing_error(&err, env)
                    }
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
