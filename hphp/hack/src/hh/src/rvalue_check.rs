// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/rvalue_check.ml`. See `hh/PORTING.md`.
//!
//! `visitor` is an object of OCaml's module (one for the process), whose
//! `non_returning_allowed` is a `ref` that every method restores once it
//! returns: between two calls of the handler it is always `true`, its initial
//! value. So [`visitor`] makes a new one for each call of the handler.
//!
//! The handler runs the visitor on every statement, and the visitor walks
//! the statements nested in it again, so the OCaml visits a statement once
//! for each statement it is nested in (quadratic in the nesting depth). The
//! visitor here does not enter a block reached from the root statement
//! through statements only (no expression in between, so no lambda): the
//! TAST visitor calls the handler on each statement of such a block with the
//! same environment, and the visitor starts that walk in the same state
//! (`non_returning_allowed` is `true` at the start of a block and of a
//! handler call), so the errors the skipped walk would add are added then,
//! identical; diagnostics are deduplicated (`diagnostics::sort`).

use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor as _;
use oxidized::ast_defs;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::*;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;

fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, msg.into()))
        .collect()
}

fn check_valid_rvalue(pos: &Pos, env: &Env, ty: &Ty) {
    // `iter_over_types env tyl`: `tyl` is the list, its head first.
    fn iter_over_types(pos: &Pos, env: &mut Env, mut tyl: Vec<Ty>) {
        tyl.reverse();
        while let Some(ty) = tyl.pop() {
            let (_, ty) = tast_env::strip_supportdyn(env, ty);
            let ety = tast_env::expand_type(env, ty);
            match get_node(&ety) {
                Ty_::Tprim(ast_defs::Tprim::Tnoreturn) => {
                    let r = get_reason(&ety).clone();
                    typing_error_utils::add_typing_error(
                        &typing_error::wellformedness(primary::wellformedness::T::NoreturnUsage {
                            pos: pos.clone(),
                            reason: typing_error::Lazy::new(move || {
                                messages(reason::to_string(
                                    "A `noreturn` function always throws or exits.",
                                    &r,
                                ))
                            }),
                        }),
                        env,
                    );
                    return;
                }
                Ty_::Tprim(ast_defs::Tprim::Tvoid) => {
                    let r = get_reason(&ety).clone();
                    typing_error_utils::add_typing_error(
                        &typing_error::wellformedness(primary::wellformedness::T::VoidUsage {
                            pos: pos.clone(),
                            reason: typing_error::Lazy::new(move || {
                                messages(reason::to_string(
                                    "A `void` function doesn't return a value.",
                                    &r,
                                ))
                            }),
                        }),
                        env,
                    );
                    return;
                }
                // iter_over_types env (tyl2 @ tyl)
                Ty_::Tunion(tyl2) => tyl.extend(tyl2.iter().rev().cloned()),
                _ => {}
            }
        }
    }
    // A type that is not a type variable, a newtype (`supportdyn`), a union,
    // `void` or `noreturn` is left as it is by `strip_supportdyn` and
    // `expand_type` and reports nothing; nor does a union of such types (the
    // like types of most expressions): skip the copy of the environment.
    fn may_report(ty: &Ty) -> bool {
        match get_node(ty) {
            Ty_::Tvar(_)
            | Ty_::Tnewtype(..)
            | Ty_::Tprim(ast_defs::Tprim::Tvoid | ast_defs::Tprim::Tnoreturn) => true,
            Ty_::Tunion(tyl) => tyl.iter().any(may_report),
            _ => false,
        }
    }
    if !may_report(ty) {
        return;
    }
    iter_over_types(pos, &mut env.clone(), vec![ty.clone()])
}

/// The class of the object `visitor` (which inherits `Aast.iter`).
struct RvalueVisitor {
    non_returning_allowed: bool,
    /// How many expressions enclose the node being visited (0 between the
    /// root statement and the blocks it has through statements alone).
    expr_depth: u32,
}

/// `let visitor = object (this) inherit [_] Aast.iter as super ... end`
fn visitor() -> RvalueVisitor {
    RvalueVisitor {
        non_returning_allowed: true,
        expr_depth: 0,
    }
}

type Res = Result<(), ()>;

impl RvalueVisitor {
    fn allow_non_returning(&mut self, f: impl FnOnce(&mut Self) -> Res) -> Res {
        let is_non_returning_allowed = self.non_returning_allowed;
        self.non_returning_allowed = true;
        let res = f(self);
        self.non_returning_allowed = is_non_returning_allowed;
        res
    }

    fn disallow_non_returning(&mut self, f: impl FnOnce(&mut Self) -> Res) -> Res {
        let is_non_returning_allowed = self.non_returning_allowed;
        self.non_returning_allowed = false;
        let res = f(self);
        self.non_returning_allowed = is_non_returning_allowed;
        res
    }
}

impl<'a> oxidized::aast_visitor::Visitor<'a> for RvalueVisitor {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn oxidized::aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    fn visit_expr(&mut self, env: &mut Env, te: &'a tast::Expr) -> Res {
        self.expr_depth += 1;
        let res = self.on_expr(env, te);
        self.expr_depth -= 1;
        res
    }

    fn visit_stmt(&mut self, env: &mut Env, stmt: &'a tast::Stmt) -> Res {
        self.on_stmt(env, stmt)
    }

    fn visit_block(&mut self, env: &mut Env, block: &'a tast::Block) -> Res {
        if self.expr_depth == 0 {
            // Its statements are checked by their own calls of the handler
            // (see the module doc).
            return Ok(());
        }
        self.allow_non_returning(|this| block.recurse(env, this))
    }
}

impl RvalueVisitor {
    /// `method! on_expr`
    fn on_expr<'a>(&mut self, env: &mut Env, te: &'a tast::Expr) -> Res {
        let aast::Expr(ty, p, e) = te;
        match e {
            aast::Expr_::Assign(a) if a.1.is_none() => {
                let (lhs, _, rhs) = &**a;
                self.allow_non_returning(|this| this.visit_expr(env, lhs))?;
                self.disallow_non_returning(|this| this.visit_expr(env, rhs))
            }
            aast::Expr_::Eif(a) => {
                let (e1, e2, e3) = &**a;
                self.disallow_non_returning(|this| this.visit_expr(env, e1))?;
                if let Some(e2) = e2 {
                    self.visit_expr(env, e2)?;
                }
                self.visit_expr(env, e3)
            }
            aast::Expr_::Pipe(a) => {
                let (_, e1, e2, _) = &**a;
                self.disallow_non_returning(|this| this.visit_expr(env, e1))?;
                self.visit_expr(env, e2)
            }
            aast::Expr_::List(el) => {
                for e in el {
                    self.visit_expr(env, e)?;
                }
                Ok(())
            }
            aast::Expr_::ReadonlyExpr(r) => {
                // ReadonlyExprs can be immediately surrounding a void thing,
                // but the thing inside the expression should be checked for void
                // (`super#on_expr env r`: the children of `r`, not `this#on_expr`
                // on `r`, which `Box`'s `recurse` would call.)
                let r: &'a tast::Expr = r;
                self.disallow_non_returning(|this| r.recurse(env, this))
            }
            aast::Expr_::ExpressionTree(et) => {
                let aast::ExpressionTree {
                    class: et_class,
                    runtime_expr: et_runtime_expr,
                    free_vars: _,
                } = &**et;
                self.visit_id(env, et_class)?;

                // Allow calls to void functions at the top level:
                //
                //   Code`void_func()`
                //
                // but not in subexpressions:
                //
                //   Code`() ==> { $x = void_func(); }`
                self.visit_expr(env, et_runtime_expr)
            }
            _ => {
                if !self.non_returning_allowed {
                    check_valid_rvalue(p, env, ty)
                }
                self.disallow_non_returning(|this| te.recurse(env, this))
            }
        }
    }

    /// `method! on_stmt`
    fn on_stmt<'a>(&mut self, env: &mut Env, stmt: &'a tast::Stmt) -> Res {
        match &stmt.1 {
            aast::Stmt_::Expr(e) => self.allow_non_returning(|this| this.visit_expr(env, e)),
            aast::Stmt_::Return(e) if e.is_some() => {
                let e = match (**e).as_ref().unwrap() {
                    aast::Expr(_, _, aast::Expr_::Hole(h)) => &h.0,
                    e => e,
                };
                self.allow_non_returning(|this| this.visit_expr(env, e))
            }
            aast::Stmt_::For(a) => {
                let (e1, e2, aast::LoopIter(_, _, e3), b) = &**a;
                self.allow_non_returning(|this| {
                    for e in e1 {
                        this.visit_expr(env, e)?;
                    }
                    Ok(())
                })?;
                self.disallow_non_returning(|this| match e2 {
                    Some(aast::LoopCond(_, _, e)) => this.visit_expr(env, e),
                    None => Ok(()),
                })?;
                self.allow_non_returning(|this| {
                    for e in e3 {
                        this.visit_expr(env, e)?;
                    }
                    Ok(())
                })?;
                self.visit_block(env, b)
            }
            aast::Stmt_::Foreach(a) => {
                let (e1, e2, b) = &**a;
                self.disallow_non_returning(|this| this.visit_expr(env, e1))?;
                self.allow_non_returning(|this| this.visit_as_expr(env, e2))?;
                self.visit_block(env, b)
            }
            aast::Stmt_::Awaitall(_) => self.allow_non_returning(|this| stmt.recurse(env, this)),
            _ => self.disallow_non_returning(|this| stmt.recurse(env, this)),
        }
    }
}

/// `let handler = object inherit Tast_visitor.handler_base ... end`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    /// `method! at_stmt = visitor#on_stmt`
    fn at_stmt(&mut self, env: &Env, stmt: &'a tast::Stmt) {
        let _ = visitor().visit_stmt(&mut env.clone(), stmt);
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}
