// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/private_final_check.ml`.
//!
//! Ban `private final` on classes, but not traits.

use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::Visibility;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

pub struct PrivateFinalCheck;

impl<'a> Handler<'a> for PrivateFinalCheck {
    fn at_method_(&mut self, env: &Env<'a>, m: &'a nast::Method_, errors: &mut Errors) {
        match (env.classish_kind, m.visibility, m.final_) {
            (Some(ClassishKind::Ctrait), _, _) => {}
            (_, Visibility::Private, true) => {
                errors.add(NastCheckError::PrivateAndFinal(m.name.0.clone()));
            }
            _ => {}
        }
    }
}
