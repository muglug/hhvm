// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/global_const_check.ml`.

use oxidized::file_info::Mode;
use oxidized::naming_error::NamingError;
use oxidized::nast;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;

fn error_if_no_typehint(gconst: &nast::Gconst, errors: &mut Errors) {
    if !matches!(gconst.mode, Mode::Mhhi) && gconst.type_.is_none() {
        let nast::Id(pos, const_name) = &gconst.name;
        let ty_name = match &gconst.value.2 {
            nast::Expr_::String(_) => "string",
            nast::Expr_::Int(_) => "int",
            nast::Expr_::Float(_) => "float",
            _ => "mixed",
        };
        errors.add(NamingError::ConstWithoutTypehint {
            pos: pos.clone(),
            const_name: const_name.clone(),
            ty_name: ty_name.to_string(),
        });
    }
}

fn error_if_pseudo_constant(gconst: &nast::Gconst, errors: &mut Errors) {
    if gconst.namespace.name.is_some() {
        let nast::Id(pos, name) = &gconst.name;
        // `Utils.strip_all_ns`
        let name = match name.rfind('\\') {
            Some(i) => &name[i + 1..],
            None => name,
        };
        // `Utils.add_ns`
        if sn::pseudo_consts::is_pseudo_const(&format!("\\{}", name)) {
            errors.add(NamingError::NameIsReserved {
                pos: pos.clone(),
                name: name.to_string(),
            });
        }
    }
}

pub struct GlobalConstCheck;

impl<'a> Handler<'a> for GlobalConstCheck {
    fn at_gconst(&mut self, _env: &Env<'a>, gconst: &'a nast::Gconst, errors: &mut Errors) {
        error_if_no_typehint(gconst, errors);
        error_if_pseudo_constant(gconst, errors);
    }
}
