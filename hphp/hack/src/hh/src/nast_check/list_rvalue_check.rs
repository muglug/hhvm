// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/list_rvalue_check.ml`.

use oxidized::aast_visitor;
use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor as _;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::nast_check_env;
use super::nast_visitor::Handler;

/// `env`: the OCaml's record `{ in_lvalue: bool }`.
type Env = bool;

/// The handler runs the visitor on every function and lambda, and the
/// OCaml visitor walks the lambdas nested in it again (quadratic in the
/// nesting, the errors are the same each time and deduplicated). Here the
/// visitor does not enter a nested lambda reached with `in_lvalue` false:
/// the NAST visitor calls the handler on it (`at_fun_`), which walks it in
/// the same state, so the same errors are added then.
struct Visitor<'e> {
    errors: &'e mut Errors,
    /// Whether the node the handler was called on is being walked (its
    /// `Fun_` is not skipped).
    in_root: bool,
}

impl<'e> Visitor<'e> {
    fn with<'a>(
        &mut self,
        state: &mut Env,
        in_lvalue: bool,
        f: impl FnOnce(&mut Self, &mut Env) -> Result<(), ()>,
    ) -> Result<(), ()> {
        let saved = std::mem::replace(state, in_lvalue);
        let result = f(self, state);
        *state = saved;
        result
    }
}

impl<'a, 'e> aast_visitor::Visitor<'a> for Visitor<'e> {
    type Params = AstParams<Env, ()>;

    fn object(&mut self) -> &mut dyn aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    fn visit_expr(&mut self, in_lvalue: &mut Env, e: &'a nast::Expr) -> Result<(), ()> {
        match &e.2 {
            nast::Expr_::Assign(assign) if assign.1.is_none() => {
                // Allow list($foo) = $bar;
                let (e1, _, e2) = &**assign;
                self.with(in_lvalue, true, |this, state| this.visit_expr(state, e1))?;
                self.visit_expr(in_lvalue, e2)
            }
            nast::Expr_::List(_) => {
                if *in_lvalue {
                    // list() can nest, so allow list(list($x)) = $foo;
                    e.recurse(in_lvalue, self)
                } else {
                    // Ban list() in rvalue positions, e.g. foo(list($bar))
                    self.errors.add(NastCheckError::ListRvalue(e.1.clone()));
                    Ok(())
                }
            }
            _ => self.with(in_lvalue, false, |this, state| e.recurse(state, this)),
        }
    }

    fn visit_fun_(&mut self, in_lvalue: &mut Env, f: &'a nast::Fun_) -> Result<(), ()> {
        if self.in_root && !*in_lvalue {
            return Ok(());
        }
        let in_root = std::mem::replace(&mut self.in_root, true);
        let res = f.recurse(in_lvalue, self);
        self.in_root = in_root;
        res
    }

    fn visit_stmt(&mut self, in_lvalue: &mut Env, s: &'a nast::Stmt) -> Result<(), ()> {
        match &s.1 {
            nast::Stmt_::Foreach(foreach) => {
                let (val_expr, as_expr, body) = &**foreach;
                self.visit_expr(in_lvalue, val_expr)?;
                // Allow foreach($foo as list($x, $y)) { ... }
                self.with(in_lvalue, true, |this, state| {
                    this.visit_as_expr(state, as_expr)
                })?;
                self.visit_block(in_lvalue, body)
            }
            _ => s.recurse(in_lvalue, self),
        }
    }
}

pub struct ListRvalueCheck;

impl<'a> Handler<'a> for ListRvalueCheck {
    fn at_fun_(&mut self, _env: &nast_check_env::Env<'a>, f: &'a nast::Fun_, errors: &mut Errors) {
        let _ = Visitor {
            errors,
            in_root: false,
        }
        .visit_fun_(&mut false, f);
    }

    fn at_method_(
        &mut self,
        _env: &nast_check_env::Env<'a>,
        m: &'a nast::Method_,
        errors: &mut Errors,
    ) {
        let _ = Visitor {
            errors,
            in_root: true,
        }
        .visit_method_(&mut false, m);
    }
}
