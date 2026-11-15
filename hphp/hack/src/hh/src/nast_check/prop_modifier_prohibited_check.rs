// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/prop_modifier_prohibited_check.ml`.

use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::ExperimentalFeature;
use oxidized::nast;

use super::Errors;
use super::attrs;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;
use super::tcopt;

fn error_if_static_prop_is_const(env: &Env<'_>, cv: &nast::ClassVar, errors: &mut Errors) {
    if cv.is_static
        && !tcopt::const_static_props(env.ctx)
        && attrs::mem(sn::user_attributes::CONST, &cv.user_attributes)
    {
        // `Diagnostics.experimental_feature pos "Const properties cannot be static."`
        errors.add(ExperimentalFeature::ConstStaticProp(cv.id.0.clone()));
    }
}

/// Non-static properties cannot have attribute `__LSB`.
fn error_if_nonstatic_prop_with_lsb(cv: &nast::ClassVar, errors: &mut Errors) {
    if !cv.is_static {
        if let Some(pos) = attrs::mem_pos(sn::user_attributes::LSB, &cv.user_attributes) {
            errors.add(NamingError::NonstaticPropertyWithLsb(pos.clone()));
        }
    }
}

fn unnecessary_lsb(c: &nast::Class_, cv: &nast::ClassVar, errors: &mut Errors) {
    let attr = sn::user_attributes::LSB;
    if let Some(pos) = attrs::mem_pos(attr, &cv.user_attributes) {
        errors.add(NamingError::UnnecessaryAttribute {
            pos: pos.clone(),
            attr: attr.to_string(),
            class_pos: c.name.0.clone(),
            class_name: c.name.1.clone(),
            suggestion: None,
        });
    }
}

pub struct PropModifierProhibitedCheck;

impl<'a> Handler<'a> for PropModifierProhibitedCheck {
    fn at_class_(&mut self, env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        for cv in &c.vars {
            error_if_static_prop_is_const(env, cv, errors);
            error_if_nonstatic_prop_with_lsb(cv, errors);
        }
        if c.final_ {
            for cv in &c.vars {
                unnecessary_lsb(c, cv, errors);
            }
        }
    }
}
