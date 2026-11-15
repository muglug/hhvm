// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/duplicate_class_member_check.ml`.

use std::collections::HashMap;

use oxidized::naming_error::NamingError;
use oxidized::nast;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

/// Type constants use the same namespace as the constants of the class, so we
/// cannot have a const and a type const with the same name.
fn error_if_repeated_name<'a>(
    member_or_const: impl Iterator<Item = &'a nast::Id>,
    errors: &mut Errors,
) {
    let mut seen: HashMap<&str, &nast::Pos> = HashMap::new();
    for nast::Id(pos, name) in member_or_const {
        match seen.get(name.as_str()) {
            Some(prev_pos) => errors.add(NamingError::ErrorNameAlreadyBound {
                pos: pos.clone(),
                name: name.clone(),
                prev_pos: (*prev_pos).clone(),
            }),
            None => {
                seen.insert(name.as_str(), pos);
            }
        }
    }
}

pub struct DuplicateClassMemberCheck;

impl<'a> Handler<'a> for DuplicateClassMemberCheck {
    fn at_class_(&mut self, _env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        let typeconst_names = c.typeconsts.iter().map(|tc| &tc.name);
        let const_names = c.consts.iter().map(|cc| &cc.id);
        error_if_repeated_name(typeconst_names.chain(const_names), errors);
    }
}
