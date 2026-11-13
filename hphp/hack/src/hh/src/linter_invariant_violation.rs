// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_invariant_violation.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).

use std::rc::Rc;
use std::sync::Arc;

use oxidized::aast;
use oxidized::ast_defs;
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

/// `type conditionKind`
#[derive(Clone, Copy)]
#[allow(clippy::enum_variant_names)]
enum ConditionKind {
    CKString,
    CKLiteral(bool),
    CKUnaryNot(bool),
    CKUnknown,
}

/// `class condition_visitor`: checks if condition consists only of literal
/// values and unary not operator
struct ConditionVisitor;

impl visitor_deprecated::Visitor<ConditionKind> for ConditionVisitor {
    fn on_expr_(&mut self, acc: ConditionKind, e: &nast::Expr_) -> ConditionKind {
        match e {
            aast::Expr_::String(_) => ConditionKind::CKString,
            aast::Expr_::True => ConditionKind::CKLiteral(true),
            aast::Expr_::False => ConditionKind::CKLiteral(false),
            aast::Expr_::Unop(unop) if matches!(unop.0, ast_defs::Uop::Unot) => {
                match self.on_expr(acc, &unop.1) {
                    ConditionKind::CKLiteral(v) => ConditionKind::CKUnaryNot(v),
                    ConditionKind::CKUnaryNot(v) => ConditionKind::CKUnaryNot(!v),
                    e => e,
                }
            }
            _ => ConditionKind::CKUnknown,
        }
    }
}

/// `class visitor lint_env` of `VisitorFunctor`
struct Visitor;

impl BodyVisitorLayer for Visitor {
    fn on_if(
        &self,
        this: &mut BodyVisitor<'_>,
        depth: usize,
        e: &nast::Expr,
        b1: &[nast::Stmt],
        b2: &[nast::Stmt],
    ) {
        let aast::Expr(_, p, _) = e;
        // invariant() is not actually a function - both the typechecker and
        // the runtime transform it into an if statement with a call to
        // invariant_violation() inside.
        let is_invariant_violation_call = match b1 {
            [aast::Stmt(_, aast::Stmt_::Expr(e))] => match &e.2 {
                aast::Expr_::Call(call) => {
                    matches!(&call.func.2, aast::Expr_::Id(id) if id.1 == "\\HH\\invariant_violation")
                }
                _ => false,
            },
            _ => false,
        };
        let err_msg = match ConditionVisitor.on_expr(ConditionKind::CKUnknown, e) {
            ConditionKind::CKUnknown => None,
            ConditionKind::CKString => {
                let err_msg = if is_invariant_violation_call {
                    "invariant('error message') will never or always crash. Did you mean invariant_violation()?"
                } else {
                    "Putting a string literal in the condition of an `if` statement guarantees it will always or never trigger."
                };
                Some(err_msg)
            }
            ConditionKind::CKUnaryNot(true) if is_invariant_violation_call => Some(
                "Your expression always evaluates to true. Because of this, invariant() will never throw an exception here. If this is the behavior you want simply remove or comment out the line.",
            ),
            ConditionKind::CKUnaryNot(false) if is_invariant_violation_call => Some(
                "Your expression always evaluates to false. Because of this, invariant() will always throw an exception here. If this is the behavior you want, please use invariant_violation() explicitly instead.",
            ),
            _ => None,
        };
        match err_msg {
            Some(err_msg) => crate::lints_diagnostics::if_literal(*p, err_msg.to_string()),
            None => {}
        }
        this.on_if_at(depth, e, b1, b2)
    }
}

/// `module VisitorFunctor`
fn visitor_functor(_env: &LintEnv<'_>) -> Rc<dyn BodyVisitorLayer> {
    Rc::new(Visitor)
}

pub fn go(ctx: &Arc<Ctx>, fn_: &RelativePath, pr: &parser_return::T) {
    lint_all_bodies(visitor_functor, ctx, fn_, pr)
}
