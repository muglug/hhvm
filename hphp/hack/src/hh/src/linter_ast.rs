// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_ast.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).

use oxidized::aast;
use oxidized::nast;

pub fn go(ast: &nast::Program) {
    for def in &ast.0 {
        match def {
            aast::Def::Stmt(stmt) => match &stmt.1 {
                aast::Stmt_::Expr(e) => match &e.2 {
                    aast::Expr_::Import(import)
                        if matches!(
                            import.0,
                            aast::ImportFlavor::Include | aast::ImportFlavor::IncludeOnce
                        ) =>
                    {
                        crate::lints_diagnostics::include_use(
                            e.1,
                            "Prefer `require` and `require_once` to `include` and `include_once`."
                                .to_string(),
                        )
                    }
                    _ => {}
                },
                _ => {}
            },
            _ => {}
        }
    }
}
