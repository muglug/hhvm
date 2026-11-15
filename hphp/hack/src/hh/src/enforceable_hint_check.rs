// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/enforceable_hint_check.ml`. See `hh/PORTING.md`.

use oxidized::aast;

use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_enforceable_hint;
use crate::typing_error;
use crate::typing_error::primary::InvalidIsAsExpressionHintOp;
use crate::typing_error_utils;

/// The object `handler`.
struct EnforceableHintCheck;

impl<'a> tast_visitor::Handler<'a> for EnforceableHintCheck {
    fn at_expr(&mut self, env: &tast_env::Env, e: &'a tast::Expr) {
        let aast::Expr(_, _, e) = e;
        let validate = |hint: &aast::Hint, op: InvalidIsAsExpressionHintOp| {
            typing_enforceable_hint::validate_hint(env, hint, |pos, reasons| {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(typing_error::primary::T::InvalidIsAsExpressionHint {
                        op,
                        pos,
                        reasons,
                    }),
                    env,
                )
            })
        };
        match e {
            aast::Expr_::Is(is) => {
                let (_, hint) = &**is;
                validate(hint, InvalidIsAsExpressionHintOp::Is)
            }
            aast::Expr_::As(as_) => validate(&as_.hint, InvalidIsAsExpressionHintOp::As),
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(EnforceableHintCheck)
}
