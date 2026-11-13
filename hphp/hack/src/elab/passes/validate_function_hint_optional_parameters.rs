// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::HfParamInfo;
use nast::Hint;
use nast::Hint_;
use nast::OptionalKind;
use nast::SplatKind;

use crate::prelude::*;

/// Port of `Naming_validate_function_hint_optional_parameters`.
#[derive(Clone, Copy, Default)]
pub struct ValidateFunctionHintOptionalParametersPass;

impl Pass for ValidateFunctionHintOptionalParametersPass {
    // Reject optional parameter preceding non-optional parameter
    // e.g. (function(int,optional bool,string):void)
    fn on_ty_hint_top_down(&mut self, env: &Env, hint: &mut Hint) -> ControlFlow<()> {
        if let Hint(pos, box Hint_::Hfun(hint_fun)) = hint {
            let mut seen_optional_positional = false;
            let mut optional_precedes_required_positional = false;
            for pi in &hint_fun.param_info {
                match pi {
                    Some(HfParamInfo {
                        splat: Some(SplatKind::Splat),
                        ..
                    }) => (),
                    Some(HfParamInfo { named: Some(_), .. }) => (),
                    Some(HfParamInfo {
                        optional: Some(OptionalKind::Optional),
                        ..
                    }) => seen_optional_positional = true,
                    _ => {
                        optional_precedes_required_positional =
                            optional_precedes_required_positional || seen_optional_positional
                    }
                }
            }
            if optional_precedes_required_positional {
                env.emit_error(NamingPhaseError::Parsing(ParsingError::ParsingError {
                    pos: pos.clone(),
                    msg: "Optional parameter cannot precede non-optional parameter".to_string(),
                    quickfixes: vec![],
                }));
            }
        }
        Continue(())
    }
}

