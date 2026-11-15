// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/inout_check.ml`.

use oxidized::ast_defs::ParamKind;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;

use super::Errors;
use super::attrs;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;

fn check_param(
    params: &[nast::FunParam],
    p: &Pos,
    user_attributes: &nast::UserAttributes,
    name: &str,
    errors: &mut Errors,
) {
    for param in params {
        match &param.callconv {
            ParamKind::Pinout(_) => {
                if sn::members::AS_SET.contains(name) {
                    errors.add(NastCheckError::InoutParamsSpecial(param.pos.clone()));
                }
            }
            ParamKind::Pnormal => {}
        }
    }
    let inout = params
        .iter()
        .find(|param| matches!(param.callconv, ParamKind::Pinout(_)));
    if let Some(param) = inout {
        if attrs::mem2(
            sn::user_attributes::MEMOIZE,
            sn::user_attributes::MEMOIZE_LSB,
            user_attributes,
        ) {
            errors.add(NastCheckError::InoutParamsMemoize {
                pos: p.clone(),
                param_pos: param.pos.clone(),
            });
        }
    }
}

pub struct InoutCheck;

impl<'a> Handler<'a> for InoutCheck {
    fn at_fun_def(&mut self, _env: &Env<'a>, fd: &'a nast::FunDef, errors: &mut Errors) {
        let f = &fd.fun;
        let nast::Id(p, name) = &fd.name;
        check_param(&f.params, p, &f.user_attributes, name, errors);
    }

    fn at_method_(&mut self, _env: &Env<'a>, m: &'a nast::Method_, errors: &mut Errors) {
        let nast::Id(p, name) = &m.name;
        check_param(&m.params, p, &m.user_attributes, name, errors);
    }
}
