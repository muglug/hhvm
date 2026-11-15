// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/this_hint_check.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::NamingPhaseError;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_hint(&mut self, env: &Env, h: &'a tast::Hint) {
        let aast::Hint(pos, hint) = h;
        let report_error_if_outside_class = |env: &Env| match tast_env::get_self_id(env) {
            Some(_) => {}
            None => {
                // `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic
                // (Naming_error.This_hint_outside_class pos) custom_err_config)`,
                // where `custom_err_config` is
                // `Typechecker_options.custom_error_config (Tast_env.get_tcopt env)`:
                // the renderer of naming errors of this crate does not take the
                // custom error configuration.
                let diagnostic = crate::naming_phase_error::to_user_diagnostic(
                    NamingPhaseError::Naming(NamingError::ThisHintOutsideClass(pos.clone())),
                );
                crate::diagnostics::add_diagnostic(diagnostic);
            }
        };
        match &**hint {
            aast::Hint_::Hthis => report_error_if_outside_class(env),
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
