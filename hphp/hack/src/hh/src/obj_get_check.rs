// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `obj_get_check.ml`. See `hh/PORTING.md`.

use oxidized::aast;

use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;

/// `let handler = object inherit Tast_visitor.handler_base ... end`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        match &e.2 {
            aast::Expr_::ObjGet(x) => match &x.1 {
                aast::Expr(_, p, aast::Expr_::This) => typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Nonsense_member_selection {
                        pos: p.clone(),
                        kind: "$this".to_string(),
                    }),
                    env,
                ),
                aast::Expr(_, p, aast::Expr_::Lplaceholder(_)) => {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Nonsense_member_selection {
                            pos: p.clone(),
                            kind: "$_".to_string(),
                        }),
                        env,
                    )
                }
                _ => {}
            },
            _ => {}
        }
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}
