// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `meth_caller_check.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::pos::Pos;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::*;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_reason;

fn check_inout_parameters(env: &Env, pos: &Pos, (_, ftype): &(typing_reason::T, std::rc::Rc<FunType>)) {
    match ftype
        .params
        .iter()
        .find(|ft_param| match get_fp_mode(ft_param) {
            ParamMode::FPnormal => false,
            ParamMode::FPinout => true,
        }) {
        Some(fparam) => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Invalid_meth_caller_inout_parameter {
                pos: pos.clone(),
                decl_pos: fparam.pos.clone(),
            }),
            env,
        ),
        None => {}
    }
}

/// `Naming_special_names.UnstableFeatures.named_parameters_meth_caller`
/// (`naming_special_names_rust` does not have it).
const NAMED_PARAMETERS_METH_CALLER: &str = "named_parameters_meth_caller";

fn check_named_parameters(env: &Env, pos: &Pos, (_, ftype): &(typing_reason::T, std::rc::Rc<FunType>)) {
    if !crate::typechecker_options::is_unstable_feature_enabled(
        &crate::tast_env::get_tcopt(env),
        NAMED_PARAMETERS_METH_CALLER,
    ) {
        match ftype.params.iter().find(|fp| get_fp_is_named(fp)) {
            Some(fparam) => typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Invalid_meth_caller_named_parameter {
                    pos: pos.clone(),
                    decl_pos: fparam.pos.clone(),
                }),
                env,
            ),
            None => {}
        }
    }
}

fn check_readonly_return(env: &Env, pos: &Pos, (r, ftype): &(typing_reason::T, std::rc::Rc<FunType>)) {
    if get_ft_returns_readonly(ftype) {
        let rpos = typing_reason::to_pos(r);
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Invalid_meth_caller_readonly_return {
                pos: pos.clone(),
                decl_pos: rpos,
            }),
            env,
        )
    }
}

/// `let handler = object inherit Tast_visitor.handler_base ... end`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        match e {
            aast::Expr(ty, pos, aast::Expr_::MethodCaller(_)) => {
                match tast_env::get_underlying_function_type(env, ty.clone()) {
                    None => {}
                    Some(ft) => {
                        check_inout_parameters(env, pos, &ft);
                        check_named_parameters(env, pos, &ft);
                        check_readonly_return(env, pos, &ft)
                    }
                }
            }
            _ => {}
        }
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}
