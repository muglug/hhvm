// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/dynamically_callable_attr_check.ml`.

use oxidized::ast_defs::ReifyKind;
use oxidized::ast_defs::Visibility;
use oxidized::naming_error;
use oxidized::naming_error::NamingError;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::attrs;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;

fn has_reified_generics(tparams: &[nast::Tparam]) -> bool {
    tparams.iter().any(|tparam| match tparam.reified {
        ReifyKind::Erased => false,
        ReifyKind::SoftReified | ReifyKind::Reified => true,
    })
}

pub struct DynamicallyCallableAttrCheck;

impl<'a> Handler<'a> for DynamicallyCallableAttrCheck {
    fn at_method_(&mut self, _env: &Env<'a>, m: &'a nast::Method_, errors: &mut Errors) {
        let pos = &m.name.0;
        let vis = m.visibility;
        let Some(p) = attrs::mem_pos(
            sn::user_attributes::DYNAMICALLY_CALLABLE,
            &m.user_attributes,
        ) else {
            return;
        };
        match vis {
            Visibility::Public | Visibility::Internal => {}
            _ => {
                let vis = match vis {
                    Visibility::Public => naming_error::Visibility::Vpublic,
                    Visibility::Private => naming_error::Visibility::Vprivate,
                    Visibility::Protected => naming_error::Visibility::Vprotected,
                    Visibility::Internal => naming_error::Visibility::Vinternal,
                    Visibility::ProtectedInternal => naming_error::Visibility::VprotectedInternal,
                };
                errors.add(NamingError::IllegalUseOfDynamicallyCallable {
                    attr_pos: p.clone(),
                    meth_pos: pos.clone(),
                    vis,
                });
            }
        }
        if has_reified_generics(&m.tparams) {
            errors.add(NastCheckError::DynamicallyCallableReified(p.clone()));
        }
    }

    fn at_fun_def(&mut self, _env: &Env<'a>, fd: &'a nast::FunDef, errors: &mut Errors) {
        if let Some(p) = attrs::mem_pos(
            sn::user_attributes::DYNAMICALLY_CALLABLE,
            &fd.fun.user_attributes,
        ) {
            if has_reified_generics(&fd.tparams) {
                errors.add(NastCheckError::DynamicallyCallableReified(p.clone()));
            }
        }
    }
}
