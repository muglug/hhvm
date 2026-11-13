// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `unresolved_type_variable_check.ml`. See `hh/PORTING.md`.

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_expand;
use crate::tast_visitor;

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        let tast::Expr(ty, p, _) = e;
        if tast_env::get_tcopt(env).tco_disallow_unresolved_type_variables {
            let _ = tast_expand::expand_ty(None, Some(p), env, ty.clone());
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
