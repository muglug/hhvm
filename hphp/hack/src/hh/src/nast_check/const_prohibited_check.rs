// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/const_prohibited_check.ml`.

use oxidized::naming_phase_error::ExperimentalFeature;
use oxidized::nast;
use oxidized::pos::Pos;

use super::Errors;
use super::attrs;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;
use super::tcopt;

fn error_if_const(pos: &Pos, attrs: &nast::UserAttributes, errors: &mut Errors) {
    if attrs::mem(sn::user_attributes::CONST, attrs) {
        // `Diagnostics.experimental_feature pos "The __Const attribute is not supported."`
        errors.add(ExperimentalFeature::ConstAttr(pos.clone()));
    }
}

pub struct ConstProhibitedCheck;

impl<'a> Handler<'a> for ConstProhibitedCheck {
    fn at_class_(&mut self, env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        // Const handling: disallow the __Const attribute unless the
        // typechecker option is enabled. (Nothing is reported while the
        // option is not known: see `tcopt`.)
        let pos = &c.name.0;
        if tcopt::const_attribute(env.ctx) == Some(false) {
            error_if_const(pos, &c.user_attributes, errors);
            for cv in &c.vars {
                error_if_const(pos, &cv.user_attributes, errors);
            }
        }
    }
}
