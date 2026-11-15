// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Hint;
use nast::Hint_;
use nast::HintFun;

use crate::prelude::*;

/// Port of `Naming_validate_named_variadic_type`: reject named variadic
/// parameters in function type hints unless `tco_named_variadic_type` is
/// enabled.
#[derive(Clone, Copy, Default)]
pub struct ValidateNamedVariadicTypePass;

impl Pass for ValidateNamedVariadicTypePass {
    fn on_ty_hint_top_down(&mut self, env: &Env, elem: &mut Hint) -> ControlFlow<()> {
        if !env.named_variadic_type() {
            if let Hint(
                _,
                box Hint_::Hfun(HintFun {
                    named_variadic_ty: Some(Hint(pos, _)),
                    ..
                }),
            ) = elem
            {
                env.emit_error(NamingError::NamedVariadicTypeDisallowed(pos.clone()))
            }
        }
        Continue(())
    }
}
