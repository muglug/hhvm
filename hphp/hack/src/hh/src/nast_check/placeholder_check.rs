// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/placeholder_check.ml`.

use naming_special_names_rust as sn;
use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

/// `env`
#[derive(Clone)]
struct State {
    in_lvalue: bool,
    inout_param_pos: Option<Pos>,
}

struct PlaceholderVisitor<'e> {
    errors: &'e mut Errors,
}

fn is_placeholder(id: &nast::LocalId) -> bool {
    id.1 == sn::special_idents::PLACEHOLDER
}

impl<'e> PlaceholderVisitor<'e> {
    fn check_placeholder(&mut self, env: &State, pos: &Pos) {
        if !env.in_lvalue {
            self.errors.add(NastCheckError::PlaceholderRead(pos.clone()))
        } else if let Some(param_pos) = &env.inout_param_pos {
            self.errors.add(NastCheckError::PlaceholderInoutWrite {
                pos: pos.clone(),
                param_pos: param_pos.clone(),
            })
        }
    }

    fn check_binding(&mut self, env: &State, lid: &nast::Lid) {
        let nast::Lid(pos, id) = lid;
        if is_placeholder(id) {
            let env = State {
                in_lvalue: true,
                ..env.clone()
            };
            self.check_placeholder(&env, pos)
        }
    }

    /// Runs `f` with `in_lvalue` set to the given value, and restores it.
    fn with(
        &mut self,
        state: &mut State,
        in_lvalue: bool,
        f: impl FnOnce(&mut Self, &mut State) -> Result<(), ()>,
    ) -> Result<(), ()> {
        let saved = std::mem::replace(&mut state.in_lvalue, in_lvalue);
        let result = f(self, state);
        state.in_lvalue = saved;
        result
    }
}

impl<'a, 'e> Visitor<'a> for PlaceholderVisitor<'e> {
    type Params = AstParams<State, ()>;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    /// Each callable body is checked by its own handler invocation.
    fn visit_fun_(&mut self, _env: &mut State, _f: &'a nast::Fun_) -> Result<(), ()> {
        Ok(())
    }

    fn visit_expr(&mut self, env: &mut State, e: &'a nast::Expr) -> Result<(), ()> {
        match &e.2 {
            nast::Expr_::Lplaceholder(_) => {
                self.check_placeholder(env, &e.1);
                Ok(())
            }
            nast::Expr_::Assign(assign) if assign.1.is_none() => {
                let (lhs, _, rhs) = &**assign;
                self.with(env, true, |this, env| this.visit_expr(env, lhs))?;
                self.with(env, false, |this, env| this.visit_expr(env, rhs))
            }
            nast::Expr_::List(_) => e.recurse(env, self),
            _ => self.with(env, false, |this, env| e.recurse(env, this)),
        }
    }

    fn visit_stmt(&mut self, env: &mut State, s: &'a nast::Stmt) -> Result<(), ()> {
        match &s.1 {
            nast::Stmt_::Foreach(foreach) => {
                let (collection, binding, body) = &**foreach;
                self.with(env, false, |this, env| this.visit_expr(env, collection))?;
                self.with(env, true, |this, env| this.visit_as_expr(env, binding))?;
                self.with(env, false, |this, env| this.visit_block(env, body))
            }
            _ => s.recurse(env, self),
        }
    }

    fn visit_catch(&mut self, env: &mut State, catch: &'a nast::Catch) -> Result<(), ()> {
        let nast::Catch(_, id, _) = catch;
        self.check_binding(env, id);
        catch.recurse(env, self)
    }

    fn visit_destructure_target_(
        &mut self,
        env: &mut State,
        target: &'a nast::DestructureTarget_,
    ) -> Result<(), ()> {
        match target {
            nast::DestructureTarget_::DtLvar(id) => {
                self.check_binding(env, id);
                Ok(())
            }
            _ => target.recurse(env, self),
        }
    }

    fn visit_capture_lid(
        &mut self,
        env: &mut State,
        capture: &'a nast::CaptureLid,
    ) -> Result<(), ()> {
        let nast::CaptureLid(_, nast::Lid(pos, id)) = capture;
        if is_placeholder(id) {
            let env = State {
                in_lvalue: false,
                ..env.clone()
            };
            self.check_placeholder(&env, pos)
        }
        Ok(())
    }
}

fn check_body<'a>(params: &'a [nast::FunParam], body: &'a nast::FuncBody, errors: &mut Errors) {
    let inout_param_pos = params.iter().find_map(|param| match &param.callconv {
        ast_defs::ParamKind::Pinout(_) if param.name == sn::special_idents::PLACEHOLDER => {
            Some(param.pos.clone())
        }
        _ => None,
    });
    let mut state = State {
        in_lvalue: false,
        inout_param_pos,
    };
    let _ = PlaceholderVisitor { errors }.visit_func_body(&mut state, body);
}

pub struct PlaceholderCheck;

impl<'a> Handler<'a> for PlaceholderCheck {
    fn at_fun_(&mut self, _env: &Env<'a>, f: &'a nast::Fun_, errors: &mut Errors) {
        check_body(&f.params, &f.body, errors)
    }

    fn at_method_(&mut self, _env: &Env<'a>, m: &'a nast::Method_, errors: &mut Errors) {
        check_body(&m.params, &m.body, errors)
    }
}
