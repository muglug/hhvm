// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_foreach_shadow.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).
//!
//! Lint on loop or catch variables that shadow local variables.
//!
//! ```hack
//! function foo(): void {
//!   $x = 99;
//!
//!   // Lint on this $x:
//!   foreach (vec[1, 2] as $x) {
//!   }
//!
//!   // $x is 2 here.
//!   $x;
//! }
//! ```
//!
//! The OCaml lists (`lid list`, `lid list list`) are `Vec`s with the head of
//! the list first.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use oxidized::aast;
use oxidized::nast;

use crate::ctx::Ctx;
use crate::linting_visitors::BodyVisitor;
use crate::linting_visitors::BodyVisitorLayer;
use crate::linting_visitors::LintEnv;
use crate::linting_visitors::lint_all_bodies;
use crate::nast::visitor_deprecated;
use crate::nast::visitor_deprecated::Visitor as _;
use crate::parser_return;
use crate::relative_path::RelativePath;

/// `lvar_visitor`: the accumulator is the OCaml list, head last (`id :: ids`
/// pushes `id`).
struct LvarVisitor;

impl visitor_deprecated::Visitor<Vec<nast::Lid>> for LvarVisitor {
    fn on_lvar(&mut self, mut ids: Vec<nast::Lid>, id: &visitor_deprecated::Id) -> Vec<nast::Lid> {
        ids.push(id.clone());
        ids
    }
}

/// The list, head first.
fn head_first(mut ids: Vec<nast::Lid>) -> Vec<nast::Lid> {
    ids.reverse();
    ids
}

fn expr_lvars(e: &nast::Expr) -> Vec<nast::Lid> {
    head_first(LvarVisitor.on_expr(vec![], e))
}

fn as_expr_lvars(ae: &nast::AsExpr) -> Vec<nast::Lid> {
    head_first(LvarVisitor.on_as_expr(vec![], ae))
}

/// `class visitor env` of `VisitorFunctor`
struct Visitor {
    /// `val mutable frames : lid list list = [[]]`
    frames: RefCell<Vec<Vec<nast::Lid>>>,
}

impl Visitor {
    fn env(&self) -> Vec<nast::Lid> {
        self.frames.borrow().concat()
    }

    fn extend_env(&self, vars: Vec<nast::Lid>) {
        let mut frames = self.frames.borrow_mut();
        // `List.rev_append vars (List.hd frames) :: List.tl frames`
        let hd = &mut frames[0];
        let mut new_hd: Vec<nast::Lid> = vars.into_iter().rev().collect();
        new_hd.append(hd);
        *hd = new_hd;
    }

    fn push_empty_frame(&self) {
        self.frames.borrow_mut().insert(0, vec![])
    }

    fn pop_frame(&self) {
        // `List.tl frames`
        let mut frames = self.frames.borrow_mut();
        if frames.is_empty() {
            panic!("Failure tl");
        }
        frames.remove(0);
    }

    fn on_block_with_local_vars(
        &self,
        this: &mut BodyVisitor<'_>,
        depth: usize,
        vars: Vec<nast::Lid>,
        block: &[nast::Stmt],
    ) {
        self.push_empty_frame();
        self.extend_env(vars);
        // `parent#on_block () block`
        this.on_block_at(depth, block);
        self.pop_frame()
    }
}

impl BodyVisitorLayer for Visitor {
    fn on_block(&self, this: &mut BodyVisitor<'_>, depth: usize, b: &[nast::Stmt]) {
        self.on_block_with_local_vars(this, depth, vec![], b)
    }

    fn on_stmt(&self, this: &mut BodyVisitor<'_>, depth: usize, stmt: &nast::Stmt) {
        match &stmt.1 {
            aast::Stmt_::Expr(e) => match &e.2 {
                aast::Expr_::Assign(assign) => self.extend_env(expr_lvars(&assign.0)),
                _ => {}
            },
            _ => {}
        }
        this.on_stmt_at(depth, stmt)
    }

    fn on_foreach(
        &self,
        this: &mut BodyVisitor<'_>,
        depth: usize,
        expr: &nast::Expr,
        as_expr: &nast::AsExpr,
        block: &[nast::Stmt],
    ) {
        visitor_deprecated::Visitor::on_expr(this, (), expr);
        visitor_deprecated::Visitor::on_as_expr(this, (), as_expr);
        self.on_block_with_local_vars(this, depth, as_expr_lvars(as_expr), block)
    }

    fn on_as_expr(&self, this: &mut BodyVisitor<'_>, depth: usize, as_expr: &nast::AsExpr) {
        let env = self.env();
        for aast::Lid(p1, id1) in as_expr_lvars(as_expr) {
            if crate::local_id::get_name(&id1) == "$_" {
            } else {
                match env.iter().find(|aast::Lid(_, id2)| id1 == *id2) {
                    None => {}
                    Some(aast::Lid(p2, _)) => {
                        crate::lints_diagnostics::loop_variable_shadows_local_variable(
                            p1, &id1, p2,
                        )
                    }
                }
            }
        }
        this.on_as_expr_at(depth, as_expr)
    }

    fn on_catch(&self, this: &mut BodyVisitor<'_>, depth: usize, c: &nast::Catch) {
        let aast::Catch(_, var, block) = c;
        // `this#on_block_with_local_vars`: its `parent#on_block` is this
        // class's parent's.
        self.on_block_with_local_vars(this, depth, vec![var.clone()], &block.0)
    }

    fn on_expr(&self, this: &mut BodyVisitor<'_>, depth: usize, e: &nast::Expr) {
        match &e.2 {
            aast::Expr_::Efun(_) | aast::Expr_::Lfun(_) => {
                let old_frames = self.frames.replace(vec![vec![]]);
                this.on_expr_at(depth, e);
                *self.frames.borrow_mut() = old_frames;
            }
            _ => this.on_expr_at(depth, e),
        }
    }
}

/// `module VisitorFunctor`
fn visitor_functor(_env: &LintEnv<'_>) -> Rc<dyn BodyVisitorLayer> {
    Rc::new(Visitor {
        frames: RefCell::new(vec![vec![]]),
    })
}

pub fn go(ctx: &Arc<Ctx>, fn_: &RelativePath, pr: &parser_return::T) {
    lint_all_bodies(visitor_functor, ctx, fn_, pr)
}
