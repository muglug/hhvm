// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_visitor.ml`: one traversal of a definition, shared by
//! the checks (`Handler`s), which maintains the `Env` they are given.

use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::nast;

use super::Errors;
use super::nast_check_env::ControlContext;
use super::nast_check_env::Env;

/// `Nast_visitor.handler`. A check overrides the methods of the nodes it
/// looks at.
///
/// As in OCaml, a handler is given the environment *before* it is updated
/// for the node itself: `at_method_` does not see the method as
/// `function_name`, `at_fun_` of a lambda sees the kind of the enclosing
/// function, and so on. (Top-level definitions are the exception: `def_env`
/// has already been applied to them.)
#[allow(unused_variables)]
pub trait Handler<'a> {
    fn at_fun_def(&mut self, env: &Env<'a>, fd: &'a nast::FunDef, errors: &mut Errors) {}
    fn at_fun_(&mut self, env: &Env<'a>, f: &'a nast::Fun_, errors: &mut Errors) {}
    fn at_class_(&mut self, env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {}
    fn at_method_(&mut self, env: &Env<'a>, m: &'a nast::Method_, errors: &mut Errors) {}
    fn at_expr(&mut self, env: &Env<'a>, e: &'a nast::Expr, errors: &mut Errors) {}
    fn at_stmt(&mut self, env: &Env<'a>, s: &'a nast::Stmt, errors: &mut Errors) {}
    fn at_hint(&mut self, env: &Env<'a>, h: &'a nast::Hint, errors: &mut Errors) {}
    fn at_contexts(&mut self, env: &Env<'a>, c: &'a nast::Contexts, errors: &mut Errors) {}
    fn at_typedef(&mut self, env: &Env<'a>, t: &'a nast::Typedef, errors: &mut Errors) {}
    fn at_gconst(&mut self, env: &Env<'a>, c: &'a nast::Gconst, errors: &mut Errors) {}
    fn at_file_attribute(
        &mut self,
        env: &Env<'a>,
        fa: &'a nast::FileAttribute,
        errors: &mut Errors,
    ) {
    }
    fn at_user_attribute(
        &mut self,
        env: &Env<'a>,
        ua: &'a nast::UserAttribute,
        errors: &mut Errors,
    ) {
    }
}

type P<'a> = AstParams<Env<'a>, ()>;

/// `Nast_visitor.iter_with handlers` (which inherits from `Nast_visitor.iter`).
pub struct IterWith<'a, 'e> {
    pub handlers: Vec<Box<dyn Handler<'a> + 'a>>,
    pub errors: &'e mut Errors,
}

impl<'a, 'e> IterWith<'a, 'e> {
    /// `go_def`
    pub fn go_def(&mut self, ctx: &'a crate::ctx::Ctx, def: &'a nast::Def) {
        let mut env = Env::def_env(ctx, def);
        let _ = self.visit_def(&mut env, def);
    }

    /// Run `f` with a modified environment, and restore the environment.
    fn with_env(
        &mut self,
        env: &mut Env<'a>,
        new_env: Env<'a>,
        f: impl FnOnce(&mut Self, &mut Env<'a>) -> Result<(), ()>,
    ) -> Result<(), ()> {
        let saved = std::mem::replace(env, new_env);
        let result = f(self, env);
        *env = saved;
        result
    }
}

macro_rules! handlers {
    ($self:ident, $method:ident, $env:expr, $node:expr) => {
        for handler in $self.handlers.iter_mut() {
            handler.$method($env, $node, $self.errors);
        }
    };
}

impl<'a, 'e> Visitor<'a> for IterWith<'a, 'e> {
    type Params = P<'a>;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    fn visit_file_attribute(
        &mut self,
        env: &mut Env<'a>,
        x: &'a nast::FileAttribute,
    ) -> Result<(), ()> {
        handlers!(self, at_file_attribute, env, x);
        x.recurse(env, self)
    }

    fn visit_fun_def(&mut self, env: &mut Env<'a>, x: &'a nast::FunDef) -> Result<(), ()> {
        handlers!(self, at_fun_def, env, x);
        let new_env = env.fun_def_env(x);
        self.with_env(env, new_env, |this, env| x.recurse(env, this))
    }

    fn visit_fun_(&mut self, env: &mut Env<'a>, x: &'a nast::Fun_) -> Result<(), ()> {
        handlers!(self, at_fun_, env, x);
        let new_env = env.fun_env(x);
        self.with_env(env, new_env, |this, env| x.recurse(env, this))
    }

    fn visit_class_(&mut self, env: &mut Env<'a>, x: &'a nast::Class_) -> Result<(), ()> {
        handlers!(self, at_class_, env, x);
        let new_env = env.class_env(x);
        self.with_env(env, new_env, |this, env| x.recurse(env, this))
    }

    fn visit_method_(&mut self, env: &mut Env<'a>, x: &'a nast::Method_) -> Result<(), ()> {
        handlers!(self, at_method_, env, x);
        let new_env = env.method_env(x);
        self.with_env(env, new_env, |this, env| x.recurse(env, this))
    }

    fn visit_expr(&mut self, env: &mut Env<'a>, x: &'a nast::Expr) -> Result<(), ()> {
        handlers!(self, at_expr, env, x);
        match &x.2 {
            // `on_Efun`, `on_Lfun`
            nast::Expr_::Efun(_) | nast::Expr_::Lfun(_) => {
                let new_env = Env {
                    is_finally: false,
                    control_context: ControlContext::Toplevel,
                    ..*env
                };
                self.with_env(env, new_env, |this, env| x.recurse(env, this))
            }
            // `on_Obj_get`, `on_Array_get`
            nast::Expr_::ObjGet(_) | nast::Expr_::ArrayGet(_) => {
                let new_env = Env {
                    array_append_allowed: false,
                    ..*env
                };
                self.with_env(env, new_env, |this, env| x.recurse(env, this))
            }
            // `on_Assign`
            nast::Expr_::Assign(assign) if assign.1.is_none() => {
                let (lhs, _, rhs) = &**assign;
                let new_env = Env {
                    array_append_allowed: true,
                    ..*env
                };
                self.with_env(env, new_env, |this, env| this.visit_expr(env, lhs))?;
                self.visit_expr(env, rhs)
            }
            _ => x.recurse(env, self),
        }
    }

    fn visit_stmt(&mut self, env: &mut Env<'a>, x: &'a nast::Stmt) -> Result<(), ()> {
        handlers!(self, at_stmt, env, x);
        match &x.1 {
            // `on_Try`
            nast::Stmt_::Try(try_) => {
                let (block, catches, finally) = &**try_;
                self.visit_block(env, block)?;
                for catch in catches {
                    self.visit_catch(env, catch)?;
                }
                let new_env = Env {
                    is_finally: true,
                    ..*env
                };
                self.with_env(env, new_env, |this, env| {
                    for stmt in &finally.0 {
                        this.visit_stmt(env, stmt)?;
                    }
                    Ok(())
                })
            }
            // `on_Do`, `on_While`, `on_For`, `on_Foreach`
            nast::Stmt_::Do(_)
            | nast::Stmt_::While(_)
            | nast::Stmt_::For(_)
            | nast::Stmt_::Foreach(_) => {
                let new_env = Env {
                    control_context: ControlContext::LoopContext,
                    ..*env
                };
                self.with_env(env, new_env, |this, env| x.recurse(env, this))
            }
            // `on_Switch`
            nast::Stmt_::Switch(_) => {
                let new_env = Env {
                    control_context: ControlContext::SwitchContext,
                    ..*env
                };
                self.with_env(env, new_env, |this, env| x.recurse(env, this))
            }
            _ => x.recurse(env, self),
        }
    }

    fn visit_func_body(&mut self, env: &mut Env<'a>, x: &'a nast::FuncBody) -> Result<(), ()> {
        match x.fb_ast.0.as_slice() {
            // A body that is a single `if (SOME_CONSTANT) { ... } else { ... }`:
            // neither the `if` nor its condition are shown to the handlers
            // (`super#on_expr env id` is the plain iterator, and an `Id` has
            // nothing to iterate on).
            [nast::Stmt(_, nast::Stmt_::If(if_))]
                if matches!(&if_.0, nast::Expr(_, _, nast::Expr_::Id(_))) =>
            {
                let (_, then_block, else_block) = &**if_;
                self.visit_block(env, then_block)?;
                self.visit_block(env, else_block)
            }
            _ => x.recurse(env, self),
        }
    }

    fn visit_hint(&mut self, env: &mut Env<'a>, x: &'a nast::Hint) -> Result<(), ()> {
        handlers!(self, at_hint, env, x);
        x.recurse(env, self)
    }

    fn visit_contexts(&mut self, env: &mut Env<'a>, x: &'a nast::Contexts) -> Result<(), ()> {
        handlers!(self, at_contexts, env, x);
        x.recurse(env, self)
    }

    fn visit_typedef(&mut self, env: &mut Env<'a>, x: &'a nast::Typedef) -> Result<(), ()> {
        handlers!(self, at_typedef, env, x);
        x.recurse(env, self)
    }

    fn visit_gconst(&mut self, env: &mut Env<'a>, x: &'a nast::Gconst) -> Result<(), ()> {
        handlers!(self, at_gconst, env, x);
        x.recurse(env, self)
    }

    fn visit_user_attribute(
        &mut self,
        env: &mut Env<'a>,
        x: &'a nast::UserAttribute,
    ) -> Result<(), ()> {
        handlers!(self, at_user_attribute, env, x);
        x.recurse(env, self)
    }
}
