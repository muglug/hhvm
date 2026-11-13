// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tany_logger.ml`. See `hh/PORTING.md`.
//!
//! A bad type is a Tany. (`_extract_bad_type_indicator`, unused in the
//! OCaml, is not here.)

use std::sync::Arc;

use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs;
use oxidized::pos::Pos;

use crate::ctx::Ctx;
use crate::relative_path;
use crate::tany_logger_file::log_info_to_file;
use crate::tany_logger_types::*;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::tast_visitor::Reduce;
use crate::tast_visitor::Res;
use crate::tast_visitor::reduce;
use crate::typing_defs;
use crate::typing_defs::Ty;

fn log_info(env: &Env, infos: &[Info]) {
    for info in infos {
        log_info_to_file(env, info)
    }
}

fn mk_common_info(context_id: &ContextId, pos: Pos) -> CommonInfo {
    let path = relative_path::suffix(pos.filename());
    let is_generated = path.contains("generated");
    let is_test = path.contains("test");
    CommonInfo {
        context_id: context_id.clone(),
        is_generated,
        is_test,
        pos,
    }
}

fn mk_ret_decl_info_internal(context_id: &ContextId, env: &Env, ty: &Ty) -> Info {
    let pos = crate::pos_or_decl::fill_in_filename(
        &tast_env::get_file(env),
        typing_defs::get_pos(ty),
    );
    let common_info = mk_common_info(context_id, pos);
    let position = Position::Return;
    let context = Context::Declaration(DeclarationInfo { position });
    Info {
        common_info,
        context,
    }
}

fn mk_ret_decl_info(context_id: &ContextId, env: &Env, ret: &tast::TypeHint) -> Option<Info> {
    let aast::TypeHint(ty, _hint) = ret;
    let bad_type = typing_defs::is_any(ty);
    if bad_type {
        Some(mk_ret_decl_info_internal(context_id, env, ty))
    } else {
        None
    }
}

fn mk_param_decl_info_internal(
    context_id: &ContextId,
    is_variadic: bool,
    pos: &Pos,
    callconv: &ast_defs::ParamKind,
) -> Info {
    let common_info = mk_common_info(context_id, pos.clone());
    let is_inout = match callconv {
        ast_defs::ParamKind::Pinout(_) => true,
        ast_defs::ParamKind::Pnormal => false,
    };
    let position = Position::Parameter(ParameterInfo {
        is_inout,
        is_variadic,
    });
    let context = Context::Declaration(DeclarationInfo { position });
    Info {
        common_info,
        context,
    }
}

fn mk_param_decl_info(context_id: &ContextId, par: &tast::FunParam) -> Option<Info> {
    let aast::TypeHint(ty, _) = &par.type_hint;
    let bad_type = typing_defs::is_any(ty);
    if bad_type {
        Some(mk_param_decl_info_internal(
            context_id,
            crate::aast_utils::is_param_variadic(par),
            &par.pos,
            &par.callconv,
        ))
    } else {
        None
    }
}

fn mk_callable_decl_infos(
    context_id: &ContextId,
    env: &Env,
    params: &[tast::FunParam],
    ret: &tast::TypeHint,
) -> Vec<Info> {
    // The arguments of `::` are evaluated from the right (no effects here).
    let param_infos = params.iter().map(|p| mk_param_decl_info(context_id, p));
    std::iter::once(mk_ret_decl_info(context_id, env, ret))
        .chain(param_infos)
        .flatten()
        .collect()
}

fn mk_expr_info_internal(context_id: &ContextId, pos: &Pos, ty: &Ty, exp: &tast::Expr_) -> Info {
    let common_info = mk_common_info(context_id, pos.clone());
    let producer_id = |e: &tast::Expr_| match e {
        aast::Expr_::Id(id) => Some(id.1.clone()),
        aast::Expr_::ClassConst(cc) => match &**cc {
            (aast::ClassId(_, _, aast::ClassId_::CI(ast_defs::Id(_, class_id))), (_, id)) => {
                Some(format!("{}::{}", class_id, id))
            }
            _ => None,
        },
        _ => None,
    };
    let exp_info = match exp {
        aast::Expr_::Call(call) => {
            let aast::Expr(_, _, receiver) = &call.func;
            let producer = match producer_id(receiver) {
                Some(id) => Some(id),
                None => Some("-".to_string()),
            };
            ExpressionInfo {
                producer,
                declaration_usage: false,
            }
        }
        aast::Expr_::Id(_) | aast::Expr_::ClassConst(_) => {
            let declaration_usage = matches!(typing_defs::get_node(ty), typing_defs::Ty_::Tfun(_));
            ExpressionInfo {
                producer: None,
                declaration_usage,
            }
        }
        _ => ExpressionInfo {
            producer: None,
            declaration_usage: false,
        },
    };
    let context = Context::Expression(exp_info);
    Info {
        common_info,
        context,
    }
}

fn mk_expr_info(context_id: &ContextId, e: &tast::Expr) -> Option<Info> {
    let aast::Expr(ty, pos, exp) = e;
    let bad_type = typing_defs::is_any(ty);
    if bad_type {
        Some(mk_expr_info_internal(context_id, pos, ty, exp))
    } else {
        None
    }
}

/// Reduction to collect all Tany/Terr information below methods and
/// functions (`collect_infos_methods_functions context_id`).
struct CollectInfosMethodsFunctions {
    context_id: ContextId,
    acc: Vec<Info>,
}

impl<'a> Reduce<'a> for CollectInfosMethodsFunctions {
    type Acc = Vec<Info>;

    fn zero(&self) -> Vec<Info> {
        vec![]
    }

    fn plus(&self, mut a: Vec<Info>, b: Vec<Info>) -> Vec<Info> {
        a.extend(b);
        a
    }

    fn acc(&mut self) -> &mut Vec<Info> {
        &mut self.acc
    }
}

impl<'a> Visitor<'a> for CollectInfosMethodsFunctions {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a; expr_, class_var, expression_tree);

    /// `infos @ super#on_method_ env m`
    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> Res {
        let infos = mk_callable_decl_infos(&self.context_id, env, &m.params, &m.ret);
        reduce::add(self, infos);
        reduce::on_method_(self, env, m)
    }

    /// `infos @ super#on_fun_ env f`
    fn visit_fun_(&mut self, env: &mut Env, f: &'a tast::Fun_) -> Res {
        let infos = mk_callable_decl_infos(&self.context_id, env, &f.params, &f.ret);
        reduce::add(self, infos);
        reduce::on_fun_(self, env, f)
    }

    /// `infos @ super#on_expr env exp`
    fn visit_expr(&mut self, env: &mut Env, exp: &'a tast::Expr) -> Res {
        let infos = match mk_expr_info(&self.context_id, exp) {
            Some(info) => vec![info],
            None => vec![],
        };
        reduce::add(self, infos);
        exp.recurse(env, self)
    }
}

fn collect_infos_methods_functions(context_id: ContextId) -> CollectInfosMethodsFunctions {
    CollectInfosMethodsFunctions {
        context_id,
        acc: vec![],
    }
}

/// Reduction to collect all Tany/Terr information. It calls the reduction
/// for functions and methods with the context information attached
/// (`collect_infos`).
struct CollectInfos {
    acc: Vec<Info>,
}

impl<'a> Reduce<'a> for CollectInfos {
    type Acc = Vec<Info>;

    fn zero(&self) -> Vec<Info> {
        vec![]
    }

    fn plus(&self, mut a: Vec<Info>, b: Vec<Info>) -> Vec<Info> {
        a.extend(b);
        a
    }

    fn acc(&mut self) -> &mut Vec<Info> {
        &mut self.acc
    }
}

impl<'a> Visitor<'a> for CollectInfos {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a; expr_, fun_, class_var, expression_tree);

    fn visit_fun_def(&mut self, env: &mut Env, fd: &'a tast::FunDef) -> Res {
        let context_id = ContextId::Function(fd.name.1.clone());
        let mut v = collect_infos_methods_functions(context_id);
        let (res, infos) = reduce::result(&mut v, |v| v.visit_fun_def(env, fd));
        reduce::add(self, infos);
        res
    }

    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> Res {
        let context_id = match tast_env::get_self_id(env) {
            Some(c_name) => ContextId::Method(c_name, m.name.1.clone()),
            None => panic!("method does not have an enclosing class"),
        };
        let mut v = collect_infos_methods_functions(context_id);
        let (res, infos) = reduce::result(&mut v, |v| v.visit_method_(env, m));
        reduce::add(self, infos);
        res
    }
}

fn collect_infos() -> CollectInfos {
    CollectInfos { acc: vec![] }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_fun_def(&mut self, env: &Env, f: &'a tast::FunDef) {
        let mut v = collect_infos();
        let (_, infos) = reduce::result(&mut v, |v| v.visit_fun_def(&mut env.clone(), f));
        log_info(env, &infos)
    }

    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        let mut v = collect_infos();
        let (_, infos) = reduce::result(&mut v, |v| v.visit_class_(&mut env.clone(), c));
        log_info(env, &infos)
    }
}

pub fn create_handler<'a>(_ctx: &Arc<Ctx>) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
