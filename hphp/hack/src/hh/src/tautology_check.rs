// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tautology_check.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::ast_defs::Bop;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        match e {
            aast::Expr(_, p, aast::Expr_::Binop(binop))
                if matches!(binop.bop, Bop::Eqeqeq | Bop::Diff2) =>
            {
                let aast::Binop { bop, lhs, rhs } = &**binop;
                tast_env::assert_nontrivial(
                    p.clone(),
                    bop.clone(),
                    env,
                    tast::get_type(lhs).clone(),
                    tast::get_type(rhs).clone(),
                )
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
