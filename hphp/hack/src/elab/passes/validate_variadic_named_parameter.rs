// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Fun_;
use nast::FunParam;
use nast::FunParamInfo;
use nast::Method_;
use nast::ParamNamed;

use crate::prelude::*;

/// Port of `Naming_validate_variadic_named_parameter`: reject variadic named
/// parameters on function definitions (e.g. `named int...`) unless
/// `tco_variadic_named_parameters` is enabled.
#[derive(Clone, Copy, Default)]
pub struct ValidateVariadicNamedParameterPass;

fn check_params(env: &Env, params: &[FunParam]) {
    if env.variadic_named_parameters() {
        return;
    }
    for param in params {
        if let FunParam {
            info: FunParamInfo::ParamVariadic,
            named: Some(ParamNamed::ParamNamed),
            pos,
            ..
        } = param
        {
            env.emit_error(NamingError::VariadicNamedParameterDisallowed(pos.clone()))
        }
    }
}

impl Pass for ValidateVariadicNamedParameterPass {
    fn on_ty_method__top_down(&mut self, env: &Env, elem: &mut Method_) -> ControlFlow<()> {
        check_params(env, &elem.params);
        Continue(())
    }

    fn on_ty_fun__top_down(&mut self, env: &Env, elem: &mut Fun_) -> ControlFlow<()> {
        check_params(env, &elem.params);
        Continue(())
    }
}
