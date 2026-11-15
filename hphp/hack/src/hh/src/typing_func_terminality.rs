// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_func_terminality.ml`. See `hh/PORTING.md`.
//!
//! The function types looked up here are declared types
//! (`ty::decl::FunType`); `Typing_defs.is_prim` on them is [`is_prim_decl`],
//! since `crate::typing_defs::is_prim` is the inferred-phase function.

use oxidized::aast;
use oxidized::ast_defs::Pstring;
use oxidized::ast_defs::Tprim;
use ty::decl;

use crate::decl_entry;
use crate::tast;
use crate::typing_defs;
use crate::typing_defs_core::DeclFunType;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;

/// `Typing_defs.is_prim` at the declared phase.
fn is_prim_decl(p: Tprim, t: &DeclTy) -> bool {
    match t.node_ref() {
        decl::Ty_::Tprim(p_) if *p_ == p => true,
        _ => false,
    }
}

/// Not adding a Typing_dep here because it will be added when the
/// Nast is fully processed (by the caller of this code)
fn get_fun(env: &Env, name: &str) -> Option<DeclFunType> {
    match decl_entry::to_option(env::get_fun(env, name)) {
        Some(fe) => match fe.ty.node_ref() {
            decl::Ty_::Tfun(ft) => Some((**ft).clone()),
            _ => None,
        },
        _ => None,
    }
}

fn get_static_meth(env: &Env, cls_name: &str, meth_name: &str) -> Option<DeclFunType> {
    match env::get_class(env, cls_name) {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
        decl_entry::T::Found(cls) => match env::get_static_member(true, env, &cls, meth_name) {
            None => None,
            Some(ce) => {
                // `{ Typing_defs.ce_type = (lazy ty); _ }`
                let ty: &DeclTy = &ce.ce_type;
                match ty.node_ref() {
                    decl::Ty_::Tfun(fty) => Some((**fty).clone()),
                    _ => None,
                }
            }
        },
    }
}

fn funopt_is_noreturn(fo: Option<&DeclFunType>) -> bool {
    match fo {
        Some(ft) => is_prim_decl(Tprim::Tnoreturn, &ft.ret),
        _ => false,
    }
}

fn static_meth_is_noreturn<Ex, En>(
    env: &Env,
    ci: &aast::ClassId_<Ex, En>,
    meth_id: &Pstring,
) -> bool {
    let class_name = match ci {
        aast::ClassId_::CI(cls_id) => Some(cls_id.1.clone()),
        aast::ClassId_::CIself | aast::ClassId_::CIstatic => env::get_self_id(env),
        aast::ClassId_::CIparent => env::get_parent_id(env),
        aast::ClassId_::CIexpr(_) => None,
        // we declared the types, but didn't check the bodies yet
        // so can't tell anything here
        aast::ClassId_::CIreified(_) => None,
    };
    match class_name {
        Some(class_name) => {
            funopt_is_noreturn(get_static_meth(env, &class_name, &meth_id.1).as_ref())
        }
        None => false,
    }
}

pub fn typed_expression_exits(e: &tast::Expr) -> bool {
    let aast::Expr(ty, _, _e) = e;
    typing_defs::is_type_no_return(get_node(ty))
}

pub fn expression_exits<Ex, En>(env: &Env, e: &aast::Expr<Ex, En>) -> bool {
    let aast::Expr(_, _, e) = e;
    match e {
        aast::Expr_::Call(call) => match &call.func {
            aast::Expr(_, _, aast::Expr_::Id(id)) => {
                let fun_name = &id.1;
                funopt_is_noreturn(get_fun(env, fun_name).as_ref())
            }
            aast::Expr(_, _, aast::Expr_::ClassConst(cc)) => {
                let (aast::ClassId(_, _, ci), meth_id) = &**cc;
                static_meth_is_noreturn(env, ci, meth_id)
            }
            _ => false,
        },
        _ => false,
    }
}

pub fn is_noreturn(env: &Env) -> bool {
    // `let (_env, ret_ty) = Env.expand_type env ...`: the new environment is
    // dropped. (`expand_type` writes only for a type variable, so that is
    // the only case expanded in a copy.)
    let ret_ty = env::get_return(env).return_type;
    let ret_ty = match get_node(&ret_ty) {
        Ty_::Tvar(_) => env::expand_type(&mut env.clone(), ret_ty),
        _ => ret_ty,
    };
    typing_defs::is_prim(Tprim::Tnoreturn, &ret_ty)
}
