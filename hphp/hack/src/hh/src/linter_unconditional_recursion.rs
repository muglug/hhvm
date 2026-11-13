// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_unconditional_recursion.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).

use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs::PropOrMethod;
use oxidized::pos::Pos;

use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;

/// `type method_prop`
struct MethodProp<'a> {
    method_name: &'a str,
    class_name: &'a str,
    pos: Pos,
}

/// `type fun_prop`
struct FunProp<'a> {
    fun_name: &'a str,
    pos: Pos,
}

/// `type is_fun_or_method`
enum IsFunOrMethod<'a> {
    IsFun(FunProp<'a>),
    IsMethod(MethodProp<'a>),
}

fn same_name_ignoring_ns(name1: &str, name2: &str) -> bool {
    crate::utils::strip_ns(name1) == crate::utils::strip_ns(name2)
}

fn check_expr(expr_: &tast::Expr_, is_fun_or_method: &IsFunOrMethod<'_>) -> bool {
    match is_fun_or_method {
        IsFunOrMethod::IsFun(f_prop) => match expr_ {
            aast::Expr_::Call(call) => match &call.func.2 {
                aast::Expr_::Id(id) => same_name_ignoring_ns(&id.1, f_prop.fun_name),
                _ => false,
            },
            _ => false,
        },
        IsFunOrMethod::IsMethod(m_prop) => match expr_ {
            aast::Expr_::Call(call) => match &call.func.2 {
                aast::Expr_::ObjGet(og)
                    if matches!(og.0.2, aast::Expr_::This)
                        && matches!(og.1.2, aast::Expr_::Id(_))
                        && matches!(og.3, PropOrMethod::IsMethod) =>
                {
                    let aast::Expr_::Id(id) = &og.1.2 else {
                        unreachable!()
                    };
                    same_name_ignoring_ns(&id.1, m_prop.method_name)
                }
                aast::Expr_::ClassConst(cc) => {
                    let (aast::ClassId(_, _, cid), (_, name)) = &**cc;
                    match cid {
                        aast::ClassId_::CI(name_of_class)
                            if same_name_ignoring_ns(&name_of_class.1, m_prop.class_name) =>
                        {
                            same_name_ignoring_ns(name, m_prop.method_name)
                        }
                        aast::ClassId_::CIstatic => same_name_ignoring_ns(name, m_prop.method_name),
                        aast::ClassId_::CIself => same_name_ignoring_ns(name, m_prop.method_name),
                        _ => false,
                    }
                }
                _ => false,
            },
            _ => false,
        },
    }
}

fn is_recursive_call(aast::Stmt(_, stmt_): &tast::Stmt, is_fun_or_method: &IsFunOrMethod<'_>) -> bool {
    match stmt_ {
        aast::Stmt_::Return(e) => match &**e {
            Some(aast::Expr(_, _, aast::Expr_::Await(await_exp))) => {
                check_expr(&await_exp.2, is_fun_or_method)
            }
            Some(aast::Expr(_, _, e)) => check_expr(e, is_fun_or_method),
            None => false,
        },
        aast::Stmt_::Throw(e) => check_expr(&e.2, is_fun_or_method),
        aast::Stmt_::Expr(e) => match &e.2 {
            aast::Expr_::Await(await_exp) => check_expr(&await_exp.2, is_fun_or_method),
            expr_ => check_expr(expr_, is_fun_or_method),
        },
        _ => false,
    }
}

/// `can_terminate_visitor`: `Aast.reduce` with `zero = false` and
/// `plus = (||)`; the accumulator is the result.
struct CanTerminateVisitor<'p, 'a> {
    is_fun_or_method: &'p IsFunOrMethod<'a>,
    acc: bool,
}

impl<'n, 'p, 'a> Visitor<'n> for CanTerminateVisitor<'p, 'a> {
    type Params = tast_visitor::Params<()>;

    fn object(&mut self) -> &mut dyn Visitor<'n, Params = Self::Params> {
        self
    }

    fn visit_stmt(&mut self, env: &mut (), s: &'n tast::Stmt) -> Result<(), ()> {
        match &s.1 {
            aast::Stmt_::Return(_) | aast::Stmt_::Throw(_) => {
                let r = !is_recursive_call(s, self.is_fun_or_method);
                self.acc = self.acc || r;
                Ok(())
            }
            _ => s.recurse(env, self.object()),
        }
    }
}

/// This function returns true if the recursion can be terminated. This
/// occurs when we find at least one return or throw statment that is
/// followed by any expression other than a recursive call
fn can_terminate(s: &tast::Stmt, is_fun_or_method: &IsFunOrMethod<'_>) -> bool {
    let mut v = CanTerminateVisitor {
        is_fun_or_method,
        acc: false,
    };
    let _ = v.visit_stmt(&mut (), s);
    v.acc
}

fn check_unconditional_recursion(stmt_list: &[tast::Stmt], is_fun_or_method: &IsFunOrMethod<'_>) {
    match stmt_list {
        [head, tail @ ..] => {
            if can_terminate(head, is_fun_or_method) {
            } else if is_recursive_call(head, is_fun_or_method) {
                match is_fun_or_method {
                    IsFunOrMethod::IsFun(f_prop) => {
                        crate::lints_diagnostics::unconditional_recursion(f_prop.pos)
                    }
                    IsFunOrMethod::IsMethod(m_prop) => {
                        crate::lints_diagnostics::unconditional_recursion(m_prop.pos)
                    }
                }
            } else {
                check_unconditional_recursion(tail, is_fun_or_method)
            }
        }
        [] => {}
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_fun_def(&mut self, _env: &Env, f: &'a tast::FunDef) {
        let f_properties = FunProp {
            fun_name: &f.name.1,
            pos: f.fun.span,
        };
        let is_f_or_m = IsFunOrMethod::IsFun(f_properties);
        check_unconditional_recursion(&f.fun.body.fb_ast.0, &is_f_or_m)
    }

    fn at_class_(&mut self, _env: &Env, c: &'a tast::Class_) {
        for c_method in &c.methods {
            let m_properties = MethodProp {
                method_name: &c_method.name.1,
                class_name: &c.name.1,
                pos: c_method.span,
            };
            let is_f_or_m = IsFunOrMethod::IsMethod(m_properties);
            check_unconditional_recursion(&c_method.body.fb_ast.0, &is_f_or_m)
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
