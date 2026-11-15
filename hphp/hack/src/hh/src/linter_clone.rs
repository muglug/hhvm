// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_clone.ml`. See `hh/PORTING.md`.

use std::rc::Rc;
use std::sync::Arc;

use oxidized::nast;

use crate::ctx::Ctx;
use crate::linting_visitors::BodyVisitor;
use crate::linting_visitors::BodyVisitorModule;
use crate::linting_visitors::LintEnv;
use crate::linting_visitors::lint_all_bodies;
use crate::parser_return;
use crate::relative_path::RelativePath;

/// `class visitor env` of `VisitorFunctor`
struct Visitor;

impl BodyVisitorModule for Visitor {
    fn on_clone(&self, this: &mut BodyVisitor<'_>, depth: usize, e: &nast::Expr) {
        let oxidized::aast::Expr(_, p, _) = e;
        crate::lints_diagnostics::clone_use(*p);
        this.on_clone_at(depth, e)
    }
}

/// `module VisitorFunctor`
fn visitor_functor(_env: &LintEnv<'_>) -> Rc<dyn BodyVisitorModule> {
    Rc::new(Visitor)
}

pub fn go(ctx: &Arc<Ctx>, fn_: &RelativePath, pr: &parser_return::T) {
    lint_all_bodies(visitor_functor, ctx, fn_, pr)
}
