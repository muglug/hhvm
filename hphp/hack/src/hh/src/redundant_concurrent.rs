// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `redundant_concurrent.ml`. See `hh/PORTING.md`.

use oxidized::aast;

use crate::error_codes;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_warning;
use crate::typing_warning::redundant_concurrent;
use crate::typing_warning_utils;

/// `val error_codes : Error_codes.Warning.t list`
pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&typing_warning::Kind::REDUNDANT_CONCURRENT)
}

/// `handler ~as_lint` (`as_lint` is unused, as in OCaml)
struct Handler {
    #[allow(dead_code)]
    as_lint: bool,
}

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_stmt(&mut self, env: &Env, stmt: &'a tast::Stmt) {
        match stmt {
            aast::Stmt(pos, aast::Stmt_::Concurrent(block)) if block.len() == 1 => {
                tast_env::add_warning(
                    env,
                    (
                        pos.clone(),
                        typing_warning::Kind::REDUNDANT_CONCURRENT,
                        redundant_concurrent::T,
                    ),
                )
            }
            _ => {}
        }
    }
}

/// `val handler : as_lint:bool -> Tast_visitor.handler`
pub fn handler(as_lint: bool) -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler { as_lint })
}
