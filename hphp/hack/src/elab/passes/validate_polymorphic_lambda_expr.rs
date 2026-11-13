// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Fun_;
use nast::FunParam;
use nast::FuncBody;
use nast::Hint;
use nast::Hint_;
use nast::TypeHint;

use crate::prelude::*;

/// Port of `Naming_validate_polymorphic_lambda_expr`: validate polymorphic
/// lambda expressions, ensuring return hint and all parameter hints are
/// provided.
#[derive(Clone, Copy, Default)]
pub struct ValidatePolymorphicLambdaExprPass {
    in_poly_lambda: bool,
}

impl Pass for ValidatePolymorphicLambdaExprPass {
    fn on_ty_fun__top_down(&mut self, env: &Env, elem: &mut Fun_) -> ControlFlow<()> {
        let in_poly_lambda = !elem.tparams.is_empty();
        if in_poly_lambda {
            if let TypeHint(_, None) = &elem.ret {
                env.emit_error(NamingError::PolymorphicLambdaMissingReturnHint(
                    elem.span.clone(),
                ))
            }
            for param in elem.params.iter() {
                if let FunParam {
                    pos,
                    name,
                    type_hint: TypeHint(_, None),
                    ..
                } = param
                {
                    env.emit_error(NamingError::PolymorphicLambdaMissingParamHint {
                        pos: pos.clone(),
                        name: name.clone(),
                    })
                }
            }
        }
        self.in_poly_lambda = in_poly_lambda;
        Continue(())
    }

    fn on_ty_func_body_top_down(&mut self, _: &Env, _: &mut FuncBody) -> ControlFlow<()> {
        // We only want to disallow wildcards in hints appearing the signature,
        // not the body
        self.in_poly_lambda = false;
        Continue(())
    }

    fn on_ty_hint_top_down(&mut self, env: &Env, elem: &mut Hint) -> ControlFlow<()> {
        if self.in_poly_lambda {
            if let Hint(pos, box Hint_::Hwildcard) = elem {
                env.emit_error(NamingError::WildcardHintDisallowed(pos.clone()))
            }
        }
        Continue(())
    }
}
