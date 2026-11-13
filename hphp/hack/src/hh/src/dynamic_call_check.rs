// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `dynamic_call_check.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::pos::Pos;

use crate::error_codes;
use crate::pos_or_decl;
use crate::relative_path;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs::get_reason;
use crate::typing_reason;
use crate::typing_warning;
use crate::typing_warning::dynamic_call::Kind;
use crate::typing_warning_utils;

pub const warning_kind: typing_warning::Kind<
    typing_warning::dynamic_call::T,
    typing_warning::Warn,
> = typing_warning::Kind::Dynamic_call;

pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&warning_kind)
}

/// The environment is threaded inside the option (`(env * ty) option`): the
/// result has the environment of the attempt that found `dynamic`, and the
/// attempts that find nothing leave `env` as it was.
pub fn is_dynamic_or_intersects_dynamic(env: &Env, ty: &Ty) -> Option<(Env, Ty)> {
    let mut env = env.clone();
    let ty = tast_env::expand_type(&mut env, ty.clone());
    match get_node(&ty) {
        Ty_::Tdynamic(_) => Some((env, ty)),
        Ty_::Tintersection(tyl) => tyl
            .iter()
            .find_map(|ty| is_dynamic_or_intersects_dynamic(&env, ty)),
        Ty_::Tnewtype(name, tyargs, _) if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN => {
            is_dynamic_or_intersects_dynamic(&env, &tyargs[0])
        }
        _ => None,
    }
}

pub fn strip_supportdyn(env: &mut Env, ty: &Ty) -> Ty {
    let ty = tast_env::expand_type(env, ty.clone());
    match get_node(&ty) {
        Ty_::Tnewtype(name, tyargs, _) if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN => {
            strip_supportdyn(env, &tyargs[0])
        }
        _ => ty,
    }
}

pub fn check_dynamic_call(env: &Env, pos: &Pos, kind: Kind, ty: &Ty) {
    match is_dynamic_or_intersects_dynamic(env, ty) {
        Some((_env, dynamic_ty)) => {
            let file = tast_env::get_file(env);
            let path = relative_path::suffix(&file);
            // Don't bother with tests as dynamic is too prolific there
            if !path.contains("/__tests__/") {
                let ty_for_print = strip_supportdyn(&mut env.clone(), ty);
                let actual_type = tast_env::print_ty(env, &ty_for_print);
                let r = get_reason(&dynamic_ty);
                let (dynamic_reason_pos, dynamic_reason_msg) =
                    match typing_reason::to_string("This expression has type `dynamic`", r)
                        .into_iter()
                        .next()
                    {
                        Some((p, msg)) => (p, msg),
                        None => (
                            pos_or_decl::of_raw_pos(pos.clone()),
                            "This expression has type `dynamic`".to_string(),
                        ),
                    };
                tast_env::add_warning(
                    env,
                    (
                        pos.clone(),
                        typing_warning::Kind::Dynamic_call,
                        typing_warning::dynamic_call::T {
                            kind,
                            actual_type,
                            dynamic_reason_pos,
                            dynamic_reason_msg,
                        },
                    ),
                )
            }
        }
        None => {}
    }
}

/// The object `handler ~as_lint:_`.
struct DynamicCallCheck;

impl<'a> tast_visitor::Handler<'a> for DynamicCallCheck {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        let aast::Expr(_, _, expr_) = e;
        match expr_ {
            aast::Expr_::Call(call)
                if matches!(
                    &call.func.2,
                    aast::Expr_::ObjGet(og) if matches!(og.3, aast::PropOrMethod::IsMethod)
                ) =>
            {
                let og = match &call.func.2 {
                    aast::Expr_::ObjGet(og) => og,
                    _ => unreachable!(),
                };
                let (aast::Expr(receiver_ty, _, _), aast::Expr(_, method_pos, _), _, _) = &**og;
                check_dynamic_call(env, method_pos, Kind::Method_invocation, receiver_ty)
            }
            aast::Expr_::ObjGet(og) if matches!(og.3, aast::PropOrMethod::IsProp) => {
                let (aast::Expr(receiver_ty, _, _), aast::Expr(_, prop_pos, _), _, _) = &**og;
                check_dynamic_call(env, prop_pos, Kind::Property_access, receiver_ty)
            }
            aast::Expr_::Call(call) => {
                let aast::Expr(fty, fpos, _) = &call.func;
                check_dynamic_call(env, fpos, Kind::Function_call, fty)
            }
            aast::Expr_::ArrayGet(ag) if ag.1.is_none() => {
                let aast::Expr(base_ty, base_pos, _) = &ag.0;
                check_dynamic_call(env, base_pos, Kind::Array_append, base_ty)
            }
            aast::Expr_::ArrayGet(ag) => {
                let aast::Expr(base_ty, base_pos, _) = &ag.0;
                check_dynamic_call(env, base_pos, Kind::Array_index, base_ty)
            }
            _ => {}
        }
    }
}

pub fn handler<'a>(_as_lint: bool) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(DynamicCallCheck)
}
