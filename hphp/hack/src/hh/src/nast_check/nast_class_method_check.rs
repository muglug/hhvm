// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/nast_class_method_check.ml`.

use std::collections::BTreeSet;

use oxidized::naming_error::NamingError;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::attrs;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;

fn is_memoizable(user_attributes: &nast::UserAttributes) -> bool {
    attrs::mem2(
        sn::user_attributes::MEMOIZE,
        sn::user_attributes::MEMOIZE_LSB,
        user_attributes,
    )
}

fn error_if_duplicate_method_names(methods: &[nast::Method_], errors: &mut Errors) {
    let mut seen_methods = BTreeSet::new();
    for m in methods {
        let nast::Id(pos, meth_name) = &m.name;
        if !seen_methods.insert(meth_name.as_str()) {
            errors.add(NamingError::MethodNameAlreadyBound {
                pos: pos.clone(),
                meth_name: meth_name.clone(),
            });
        }
    }
}

fn error_if_abstract_method_is_memoized(method: &nast::Method_, errors: &mut Errors) {
    if method.abstract_ && is_memoizable(&method.user_attributes) {
        errors.add(NastCheckError::AbstractMethodMemoize(method.name.0.clone()));
    }
}

pub struct NastClassMethodCheck;

impl<'a> Handler<'a> for NastClassMethodCheck {
    fn at_class_(&mut self, _env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        error_if_duplicate_method_names(&c.methods, errors);
    }

    fn at_method_(&mut self, _env: &Env<'a>, m: &'a nast::Method_, errors: &mut Errors) {
        error_if_abstract_method_is_memoized(m, errors);
    }
}
