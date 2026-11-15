// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_comparing_booleans.ml`. See `hh/PORTING.md`.
//!
//! Check for expression like `$mybool == true` and suggests simplification.

use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Tprim;

use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;

fn as_lvar_and_literal(
    aast::Expr(_, _, lhs): &tast::Expr,
    aast::Expr(_, _, rhs): &tast::Expr,
) -> Option<(String, bool)> {
    match (lhs, rhs) {
        (aast::Expr_::Lvar(lid), aast::Expr_::True) => {
            Some((crate::local_id::get_name(&lid.1).to_string(), true))
        }
        (aast::Expr_::Lvar(lid), aast::Expr_::False) => {
            Some((crate::local_id::get_name(&lid.1).to_string(), false))
        }
        _ => None,
    }
}

fn is_boolean_variable(aast::Expr(ty, _pos, _expr_): &tast::Expr) -> bool {
    crate::typing_defs::is_prim(Tprim::Tbool, ty)
}

fn checking_the_expression(exp1: &tast::Expr, exp2: &tast::Expr) -> Option<(String, bool)> {
    if is_boolean_variable(exp1) {
        as_lvar_and_literal(exp1, exp2)
    } else {
        None
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, _env: &Env, aast::Expr(_, pos, expr_): &'a tast::Expr) {
        match expr_ {
            aast::Expr_::Binop(binop) => {
                let aast::Binop { bop, lhs, rhs } = &**binop;
                match bop {
                    Bop::Eqeq | Bop::Eqeqeq => match checking_the_expression(lhs, rhs) {
                        Some((name, boolean_var)) => {
                            let pos_exp1 = &lhs.1;
                            crate::lints_diagnostics::comparing_booleans(
                                *pos,
                                pos_exp1,
                                &name,
                                boolean_var,
                            )
                        }
                        None => match checking_the_expression(rhs, lhs) {
                            Some((name, boolean_var)) => {
                                let pos_exp2 = &rhs.1;
                                crate::lints_diagnostics::comparing_booleans(
                                    *pos,
                                    pos_exp2,
                                    &name,
                                    boolean_var,
                                )
                            }
                            None => {}
                        },
                    },
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
