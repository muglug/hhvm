// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_branches_return_same_value.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).
//!
//! Lint on functions/methods that always return the same value. This
//! is usually a copy-paste error.
//!
//! ```hack
//! function some_predicate(Whatever $value): bool {
//!   if ($value->foo()) {
//!     return false;
//!   }
//!
//!   if ($value->bar()) {
//!     return false;
//!   }
//!
//!   return false; // oops!
//! }
//! ```

use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;

use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;

fn is_expr_same(aast::Expr(_, _, expr1): &tast::Expr, aast::Expr(_, _, expr2): &tast::Expr) -> bool {
    match (expr1, expr2) {
        (aast::Expr_::True, aast::Expr_::True) | (aast::Expr_::False, aast::Expr_::False) => true,
        (aast::Expr_::Int(s1), aast::Expr_::Int(s2)) if s1 == s2 => true,
        (aast::Expr_::Float(s1), aast::Expr_::Float(s2)) if s1 == s2 => true,
        (aast::Expr_::String(s1), aast::Expr_::String(s2)) if s1 == s2 => true,
        (aast::Expr_::Id(id1), aast::Expr_::Id(id2)) if id1.1 == id2.1 => true,
        (aast::Expr_::ClassConst(cc1), aast::Expr_::ClassConst(cc2)) => {
            match (&**cc1, &**cc2) {
                (
                    (aast::ClassId(_, _, aast::ClassId_::CI(enum1)), (_, name1)),
                    (aast::ClassId(_, _, aast::ClassId_::CI(enum2)), (_, name2)),
                ) if enum1.1 == enum2.1 && name1 == name2 => true,
                _ => false,
            }
        }
        _ => false,
    }
}

/// Does this value look like a success exit code? We don't want to
/// lint on code like this:
///
/// ```hack
/// function my_main(): int {
///   if (quick_check()) { return 0; }
///
///   normal_work();
///   return 0;
/// }
/// ```
fn is_success_ish(aast::Expr(_, _, e_): &tast::Expr) -> bool {
    match e_ {
        aast::Expr_::Int(s) if s == "0" => true,
        aast::Expr_::ClassConst(cc) if cc.1.1 == "SUCCESS" => true,
        _ => false,
    }
}

fn are_return_expressions_same(ret_list: &[&tast::Expr]) -> bool {
    match ret_list {
        [expr1, expr2, ..] => {
            if is_expr_same(expr1, expr2) {
                are_return_expressions_same(&ret_list[1..])
            } else {
                false
            }
        }
        [_] => true,
        [] => true,
    }
}

/// `type return_or_throw`
enum ReturnOrThrow<'a> {
    ReturnExpr(&'a tast::Expr),
    ThrowStmt,
}

/// `get_return_or_throw_visitor`: `Aast.reduce` with `zero = []` and
/// `plus = (@)`; the accumulator is the result, in the order of the
/// traversal.
struct GetReturnOrThrowVisitor<'a> {
    acc: Vec<ReturnOrThrow<'a>>,
}

impl<'a> Visitor<'a> for GetReturnOrThrowVisitor<'a> {
    type Params = tast_visitor::Params<()>;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    fn visit_stmt(&mut self, env: &mut (), s: &'a tast::Stmt) -> Result<(), ()> {
        match &s.1 {
            aast::Stmt_::Return(e) if e.is_some() => {
                let Some(expr) = &**e else { unreachable!() };
                self.acc.push(ReturnOrThrow::ReturnExpr(expr));
                Ok(())
            }
            aast::Stmt_::Throw(_) => {
                self.acc.push(ReturnOrThrow::ThrowStmt);
                Ok(())
            }
            _ => s.recurse(env, self.object()),
        }
    }

    /// We ignore return expressions and throw statements within lambdas.
    fn visit_expr_(&mut self, env: &mut (), e: &'a tast::Expr_) -> Result<(), ()> {
        match e {
            aast::Expr_::Efun(_) => Ok(()),
            aast::Expr_::Lfun(_) => Ok(()),
            _ => e.recurse(env, self.object()),
        }
    }
}

/// This function returns all return expressions and throw statements in a
/// block.
fn get_return_or_throw(stmts: &[tast::Stmt]) -> Vec<ReturnOrThrow<'_>> {
    let mut v = GetReturnOrThrowVisitor { acc: vec![] };
    for s in stmts {
        let _ = v.visit_stmt(&mut (), s);
    }
    v.acc
}

fn check_block(block: &[tast::Stmt]) {
    let return_or_throw = get_return_or_throw(block);
    let has_throw = return_or_throw.iter().any(|x| match x {
        ReturnOrThrow::ThrowStmt => true,
        ReturnOrThrow::ReturnExpr(_) => false,
    });
    let ret_list: Vec<&tast::Expr> = return_or_throw
        .iter()
        .filter_map(|x| match x {
            ReturnOrThrow::ReturnExpr(expr) => Some(*expr),
            ReturnOrThrow::ThrowStmt => None,
        })
        .collect();
    match ret_list.as_slice() {
        [expr1, _, ..] => {
            if !has_throw && are_return_expressions_same(&ret_list) && !is_success_ish(expr1) {
                for aast::Expr(_, pos, _) in &ret_list {
                    crate::lints_diagnostics::branches_return_same_value(*pos)
                }
            }
        }
        _ => {}
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_fun_def(&mut self, _env: &Env, f: &'a tast::FunDef) {
        check_block(&f.fun.body.fb_ast.0)
    }

    fn at_method_(&mut self, _env: &Env, m: &'a tast::Method_) {
        check_block(&m.body.fb_ast.0)
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
