// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `dynamic_return_check.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::ast_defs;
use pos::ToOxidized;
use ty::decl::ty as d;

use crate::decl_entry;
use crate::error_codes;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Enforcement;
use crate::typing_enforceability;
use crate::typing_partial_enforcement;
use crate::typing_phase;
use crate::typing_warning;
use crate::typing_warning::Warn;
use crate::typing_warning::dynamic_return;
use crate::typing_warning_utils;

const warning_kind: typing_warning::Kind<dynamic_return::T, Warn> =
    typing_warning::Kind::Dynamic_return;

/// `val error_codes : Error_codes.Warning.t list`
pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&warning_kind)
}

fn awaitable_inner(ty: &DeclTy) -> Option<DeclTy> {
    match ty.node_ref() {
        d::Ty_::Tapply(apply)
            if apply.0.id_ref().as_str() == sn::classes::AWAITABLE && apply.1.len() == 1 =>
        {
            Some(apply.1[0].clone())
        }
        _ => None,
    }
}

fn return_value_type(fun_kind: ast_defs::FunKind, ty: DeclTy) -> DeclTy {
    match (fun_kind, ty.node_ref()) {
        (ast_defs::FunKind::FAsync, d::Ty_::Tapply(_)) => match awaitable_inner(&ty) {
            Some(inner_ty) => inner_ty,
            None => ty,
        },
        (ast_defs::FunKind::FAsync, d::Ty_::Tlike(ty_)) => match awaitable_inner(ty_) {
            Some(inner_ty) => DeclTy::new(ty_.reason().clone(), d::Ty_::Tlike(inner_ty)),
            None => ty_.clone(),
        },
        _ => ty,
    }
}

fn check_return(env: &Env, return_type: &DeclTy, expr: &tast::Expr) {
    let aast::Expr(expr_ty, expr_pos, _) = expr;
    // `let (_env, expr_ty) = Tast_env.expand_type env expr_ty`
    let expr_ty = tast_env::expand_type(&mut env.clone(), expr_ty.clone());
    match get_node(&expr_ty) {
        Ty_::Tdynamic(_) => {
            let return_type_pos = return_type.pos().clone().to_oxidized();
            let return_type = tast_env::print_decl_ty(None, env, return_type);
            tast_env::add_warning(
                env,
                (
                    expr_pos.clone(),
                    typing_warning::Kind::Dynamic_return,
                    dynamic_return::T {
                        return_type,
                        return_type_pos,
                    },
                ),
            )
        }
        _ => {}
    }
}

/// The visitor of `check_callable`: it does not go into functions or methods.
struct ReturnVisitor<'r> {
    return_type: &'r DeclTy,
}

impl<'a> oxidized::aast_visitor::Visitor<'a> for ReturnVisitor<'_> {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn oxidized::aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    fn visit_stmt(&mut self, env: &mut Env, stmt: &'a tast::Stmt) -> tast_visitor::Res {
        match stmt {
            aast::Stmt(_, aast::Stmt_::Return(e)) => match &**e {
                Some(expr) => check_return(env, self.return_type, expr),
                None => {}
            },
            _ => {}
        }
        stmt.recurse(env, self)
    }

    fn visit_fun_(&mut self, _env: &mut Env, _: &'a tast::Fun_) -> tast_visitor::Res {
        Ok(())
    }

    fn visit_method_(&mut self, _env: &mut Env, _: &'a tast::Method_) -> tast_visitor::Res {
        Ok(())
    }
}

fn check_callable(
    env: &mut Env,
    fun_kind: ast_defs::FunKind,
    type_hint: &tast::TypeHint,
    body: &tast::FuncBody,
) {
    match crate::aast::hint_of_type_hint(type_hint) {
        None => {}
        Some(hint) => {
            let return_type = return_value_type(fun_kind, tast_env::hint_to_ty(env, hint));
            if !matches!(return_type.node_ref(), d::Ty_::Tdynamic) {
                let this_class = decl_entry::to_option(tast_env::get_self_class(env));
                let is_enforced = match typing_enforceability::get_enforcement(
                    Some(true),
                    this_class.as_ref(),
                    env,
                    &return_type,
                ) {
                    Enforcement::Enforced => true,
                    Enforcement::Unenforced => {
                        let enforced_type = typing_partial_enforcement::get_enforced_type(
                            env,
                            this_class.as_ref(),
                            &return_type,
                        );
                        typing_phase::is_sub_type_decl(
                            Some(true),
                            env,
                            &enforced_type,
                            &return_type,
                        )
                    }
                };
                if !is_enforced {
                    let mut visitor = ReturnVisitor {
                        return_type: &return_type,
                    };
                    let _ = oxidized::aast_visitor::Visitor::visit_block(
                        &mut visitor,
                        env,
                        &body.fb_ast,
                    );
                }
            }
        }
    }
}

/// `handler ~as_lint` (`as_lint` is unused, as in OCaml)
struct Handler {
    #[allow(dead_code)]
    as_lint: bool,
}

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_fun_(&mut self, env: &Env, fun_: &'a tast::Fun_) {
        let mut env = env.clone();
        tast_env::restore_fun_env(&mut env, fun_);
        check_callable(&mut env, fun_.fun_kind, &fun_.ret, &fun_.body)
    }

    fn at_method_(&mut self, env: &Env, method_: &'a tast::Method_) {
        let mut env = env.clone();
        tast_env::restore_method_env(&mut env, method_);
        check_callable(&mut env, method_.fun_kind, &method_.ret, &method_.body)
    }
}

/// `val handler : as_lint:bool -> Tast_visitor.handler`
pub fn handler(as_lint: bool) -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler { as_lint })
}
