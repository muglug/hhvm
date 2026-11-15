// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/pseudofunctions_check.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::pos::Pos;

use crate::aast_utils;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;

fn disallow_isset_inout_args_check(env: &Env, p: &Pos, x: &tast::Expr_) {
    match x {
        aast::Expr_::Call(call)
            if matches!(&call.func.2, aast::Expr_::Id(id) if id.1 == sn::pseudo_functions::ISSET)
                && call.args.iter().any(|arg| match arg {
                    aast::Argument::Ainout(_, _) => true,
                    aast::Argument::Anormal(_) => false,
                    aast::Argument::Anamed(_, _) => false,
                }) =>
        {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::IssetInoutArg(p.clone())),
                env,
            )
        }
        _ => {}
    }
}

fn well_formed_isset_argument_check(env: &Env, p: &Pos, x: &tast::Expr_) {
    match x {
        aast::Expr_::Call(call) => match (&call.func.2, call.args.as_slice()) {
            (aast::Expr_::Id(id), [arg]) => {
                let pseudo_func = &id.1;
                match aast_utils::arg_to_expr(arg) {
                    aast::Expr(_, _, aast::Expr_::Lvar(_))
                        if pseudo_func == sn::pseudo_functions::ISSET =>
                    {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::IssetInStrict(p.clone())),
                            env,
                        )
                    }
                    // isset($var->thing) but not isset($foo->$bar)
                    aast::Expr(_, _, aast::Expr_::ObjGet(og))
                        if matches!(&og.1.2, aast::Expr_::Id(_))
                            && matches!(og.3, aast::PropOrMethod::IsProp)
                            && pseudo_func == sn::pseudo_functions::ISSET =>
                    {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::IssetInStrict(p.clone())),
                            env,
                        )
                    }
                    _ => {}
                }
            }
            _ => {}
        },
        _ => {}
    }
}

/// `let handler = object inherit Tast_visitor.handler_base ... end`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, aast::Expr(_, p, x): &'a tast::Expr) {
        disallow_isset_inout_args_check(env, p, x);
        well_formed_isset_argument_check(env, p, x)
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}
