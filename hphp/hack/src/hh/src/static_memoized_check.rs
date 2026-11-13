// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `static_memoized_check.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::custom_error_config::CustomErrorConfig;
use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::NamingPhaseError;

use crate::aast::split_methods;
use crate::naming_attributes;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typechecker_options;

pub fn unnecessary_memoize_lsb(
    c: &tast::Class_,
    m: &tast::Method_,
    _custom_err_config: &CustomErrorConfig,
) {
    let attr = sn::user_attributes::MEMOIZE_LSB;
    match naming_attributes::mem_pos(attr, &m.user_attributes.0) {
        None => {}
        Some(pos) => {
            let oxidized::ast_defs::Id(class_pos, class_name) = &c.name;
            let suggestion = Some(format!(
                "Try using the attribute `{}` instead",
                sn::user_attributes::MEMOIZE
            ));
            // `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic
            // error custom_err_config)`: the renderer of naming errors of this
            // crate does not take the custom error configuration.
            if let Some(diagnostic) =
                crate::naming_errors::to_diagnostic(NamingPhaseError::Naming(
                    NamingError::UnnecessaryAttribute {
                        pos,
                        attr: attr.to_string(),
                        class_pos: class_pos.clone(),
                        class_name: class_name.clone(),
                        suggestion,
                    },
                ))
            {
                crate::diagnostics_state::add_diagnostic(diagnostic)
            }
        }
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        let custom_err_config = {
            let tcopt = tast_env::get_tcopt(env);
            typechecker_options::custom_error_config(&tcopt)
        };
        let (_, static_methods, _) = split_methods(&c.methods);
        if c.final_ {
            for m in static_methods {
                unnecessary_memoize_lsb(c, m, &custom_err_config)
            }
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
