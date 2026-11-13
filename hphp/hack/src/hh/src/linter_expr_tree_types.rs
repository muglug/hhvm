// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_expr_tree_types.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).

use oxidized::aast;
use oxidized::ast_defs::Tprim;

use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    /// Require that methods named __bool should return a bool.
    fn at_method_(&mut self, _env: &Env, m: &'a tast::Method_) {
        let name = &m.name.1;
        if name == "__bool" {
            let hint = &m.ret.1;
            match hint {
                Some(aast::Hint(_, h)) if matches!(**h, aast::Hint_::Hprim(Tprim::Tbool)) => {}
                Some(aast::Hint(p, _)) => crate::lints_diagnostics::bad_virtualized_method(*p),
                None => {}
            }
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
