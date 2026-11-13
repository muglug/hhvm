// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/interface_check.ml`.

use oxidized::ast_defs::ClassishKind;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

fn enforce_no_body(m: &nast::Method_, errors: &mut Errors) {
    if !m.body.fb_ast.0.is_empty() {
        errors.add(NastCheckError::AbstractBody(m.name.0.clone()));
    }
}

fn check_interface(c: &nast::Class_, errors: &mut Errors) {
    for nast::Hint(p, _) in &c.uses {
        errors.add(NastCheckError::InterfaceUsesTrait(p.clone()));
    }

    // `split_vars`
    let mut statics = c.vars.iter().filter(|cv| cv.is_static);
    let mut vars = c.vars.iter().filter(|cv| !cv.is_static);
    if let Some(hd) = vars.next() {
        errors.add(NastCheckError::InterfaceWithMemberVariable(hd.id.0.clone()));
    }
    if let Some(hd) = statics.next() {
        errors.add(NastCheckError::InterfaceWithStaticMemberVariable(
            hd.id.0.clone(),
        ));
    }

    // make sure that interfaces only have empty public methods
    for m in &c.methods {
        enforce_no_body(m, errors);
    }
}

pub struct InterfaceCheck;

impl<'a> Handler<'a> for InterfaceCheck {
    fn at_class_(&mut self, _env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        if matches!(c.kind, ClassishKind::Cinterface) {
            check_interface(c, errors);
        }
    }
}
