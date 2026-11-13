// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `method_type_param_check.ml`. See `hh/PORTING.md`.

use oxidized::ast_defs;

use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;

fn check_tparams(env: &Env, tps: &[tast::Tparam]) {
    let check_tparam = |tp: &tast::Tparam| match tp.variance {
        ast_defs::Variance::Invariant => {}
        _ => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Method_variance(tp.name.0.clone())),
            env,
        ),
    };
    tps.iter().for_each(check_tparam)
}

/// `let handler = object inherit Tast_visitor.handler_base ... end`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_method_(&mut self, env: &Env, m: &'a tast::Method_) {
        check_tparams(env, &m.tparams)
    }

    fn at_fun_def(&mut self, env: &Env, f: &'a tast::FunDef) {
        check_tparams(env, &f.tparams)
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}
