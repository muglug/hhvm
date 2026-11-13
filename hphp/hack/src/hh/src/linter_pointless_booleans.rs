// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_pointless_booleans.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).
//!
//! Checks for always true/false boolean expressions like
//! `expr || true` and `expr && false`,
//! or pointless booleans like `expr || false` and `expr && true`.

use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Tprim;
use oxidized::pos::Pos;

use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;

/// `Aast.True` or `Aast.False`
#[derive(Clone, Copy)]
enum BooleanLiteral {
    True,
    False,
}

fn which_boolean_literal(aast::Expr(_ty, _pos, expr_): &tast::Expr) -> Option<BooleanLiteral> {
    match expr_ {
        aast::Expr_::True => Some(BooleanLiteral::True),
        aast::Expr_::False => Some(BooleanLiteral::False),
        _ => None,
    }
}

fn is_boolean_expression(aast::Expr(ty, _pos, _expr_): &tast::Expr) -> bool {
    crate::typing_defs::is_prim(Tprim::Tbool, ty)
}

fn checking_the_expression(exp1: &tast::Expr, exp2: &tast::Expr) -> Option<BooleanLiteral> {
    match which_boolean_literal(exp1) {
        Some(x) if is_boolean_expression(exp2) => Some(x),
        _ => None,
    }
}

fn check_the_error(
    logical_op: &Bop,
    boolean_literal: BooleanLiteral,
) -> Option<(&'static str, Option<&'static str>)> {
    match logical_op {
        Bop::Ampamp => match boolean_literal {
            BooleanLiteral::True => Some(("The boolean expression is pointless", None)),
            BooleanLiteral::False => {
                Some(("The boolean expression is always false", Some("false")))
            }
        },
        Bop::Barbar => match boolean_literal {
            BooleanLiteral::True => Some(("The boolean expression is always true", Some("true"))),
            BooleanLiteral::False => Some(("The boolean expression is pointless", None)),
        },
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn send_to_lint_error(
    pos: Pos,
    str: &str,
    line1: usize,
    line2: usize,
    bol1: usize,
    bol2: usize,
    col1: usize,
    col2: usize,
) {
    let pos_quickfix = Pos::from_lnum_bol_offset(
        pos.filename_rc(),
        (line1, bol1, col1),
        (line2, bol2, col2),
    );
    crate::lints_diagnostics::calling_pointless_boolean(
        pos,
        pos_quickfix,
        String::new(),
        str.to_string(),
    )
}

/// `Pos.line_beg_offset`
fn line_beg_offset(p: &Pos) -> (usize, usize, usize) {
    p.to_start_and_end_lnum_bol_offset().0
}

/// `Pos.end_line_beg_offset`
fn end_line_beg_offset(p: &Pos) -> (usize, usize, usize) {
    p.to_start_and_end_lnum_bol_offset().1
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, _env: &Env, aast::Expr(_, pos, expr_): &'a tast::Expr) {
        let pos = *pos;
        match expr_ {
            aast::Expr_::Binop(binop) => {
                let aast::Binop { bop, lhs, rhs } = &**binop;
                match bop {
                    Bop::Ampamp | Bop::Barbar => {
                        // exp1 is the boolean literal (it is of the type true ||, false && etc)
                        // The original string for quickfix starts from the
                        // start of exp1 and ends at the start of exp2
                        match checking_the_expression(lhs, rhs) {
                            Some(x) => match check_the_error(bop, x) {
                                Some((str, None)) => {
                                    // exp1 is the boolean literal, expression is pointless
                                    // Remove from start of exp1 to start of exp2
                                    let (pos_exp1, pos_exp2) = (&lhs.1, &rhs.1);
                                    let (line1, bol1, start_col1) = line_beg_offset(pos_exp1);
                                    let (line2, bol2, start_col2) = line_beg_offset(pos_exp2);
                                    send_to_lint_error(
                                        pos, str, line1, line2, bol1, bol2, start_col1, start_col2,
                                    )
                                }
                                Some((str, Some(replacement))) => {
                                    // exp1 is the boolean literal, expression is always true/false
                                    // Replace entire expression with the literal
                                    crate::lints_diagnostics::calling_pointless_boolean(
                                        pos,
                                        pos,
                                        replacement.to_string(),
                                        str.to_string(),
                                    )
                                }
                                None => {}
                            },
                            None => {
                                // exp2 is the boolean literal (it is of the type && true, || false etc)
                                match checking_the_expression(rhs, lhs) {
                                    Some(x) => match check_the_error(bop, x) {
                                        Some((str, None)) => {
                                            // exp2 is the boolean literal, expression is pointless
                                            // Remove from end of exp1 to end of exp2
                                            let (pos_exp1, pos_exp2) = (&lhs.1, &rhs.1);
                                            let (line1, bol1, end_col1) =
                                                end_line_beg_offset(pos_exp1);
                                            let (line2, bol2, end_col2) =
                                                end_line_beg_offset(pos_exp2);
                                            send_to_lint_error(
                                                pos, str, line1, line2, bol1, bol2, end_col1,
                                                end_col2,
                                            )
                                        }
                                        Some((str, Some(replacement))) => {
                                            // exp2 is the boolean literal, expression is always true/false
                                            // Replace entire expression with the literal
                                            crate::lints_diagnostics::calling_pointless_boolean(
                                                pos,
                                                pos,
                                                replacement.to_string(),
                                                str.to_string(),
                                            )
                                        }
                                        None => {}
                                    },
                                    None => {}
                                }
                            }
                        }
                    }
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
