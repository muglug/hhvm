// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/nast_generics_check.ml`.

use std::collections::BTreeMap;

use oxidized::naming_error::NamingError;
use oxidized::nast;
use oxidized::pos::Pos;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;

/// Positions of type parameters that are in scope.
type TparamInfo<'a> = BTreeMap<&'a str, &'a Pos>;

fn error_if_is_this(nast::Id(pos, name): &nast::Id, errors: &mut Errors) {
    if name.to_lowercase() == "this" {
        errors.add(NamingError::ThisReserved(pos.clone()));
    }
}

fn error_if_invalid_tparam_name(nast::Id(pos, name): &nast::Id, errors: &mut Errors) {
    if !name.starts_with('T') {
        errors.add(NamingError::StartWithT(pos.clone()));
    }
}

/// See the note on `Naming.type_param` about the scoping of type parameters.
fn check_tparams<'a>(
    mut seen: TparamInfo<'a>,
    tparams: &'a [nast::Tparam],
    errors: &mut Errors,
) -> TparamInfo<'a> {
    for tparam in tparams {
        error_if_is_this(&tparam.name, errors);
        error_if_invalid_tparam_name(&tparam.name, errors);
        let nast::Id(pos, name) = &tparam.name;
        if name == sn::typehints::WILDCARD {
            errors.add(NamingError::WildcardTparamDisallowed(pos.clone()));
        } else {
            if let Some(prev_pos) = seen.get(name.as_str()) {
                errors.add(NamingError::ShadowedTparam {
                    pos: pos.clone(),
                    prev_pos: (*prev_pos).clone(),
                    tparam_name: name.clone(),
                });
            }
            seen.insert(name, pos);
        }
    }
    seen
}

fn check_class(class: &nast::Class_, errors: &mut Errors) {
    let seen_class_tparams = check_tparams(BTreeMap::new(), &class.tparams, errors);
    // Note that the class tparams are still marked as in scope.
    for m in &class.methods {
        check_tparams(seen_class_tparams.clone(), &m.tparams, errors);
    }
}

pub struct NastGenericsCheck;

impl<'a> Handler<'a> for NastGenericsCheck {
    fn at_fun_def(&mut self, _env: &Env<'a>, fd: &'a nast::FunDef, errors: &mut Errors) {
        check_tparams(BTreeMap::new(), &fd.tparams, errors);
    }

    fn at_class_(&mut self, _env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        check_class(c, errors);
    }

    fn at_typedef(&mut self, _env: &Env<'a>, t: &'a nast::Typedef, errors: &mut Errors) {
        check_tparams(BTreeMap::new(), &t.tparams, errors);
    }
}
