// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/well_formed_internal_trait.ml`.

use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::Visibility;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::attrs;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;

pub struct WellFormedInternalTrait;

impl<'a> Handler<'a> for WellFormedInternalTrait {
    fn at_class_(&mut self, env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        if env.module.is_none() {
            return;
        }
        match c.kind {
            ClassishKind::Ctrait if !c.internal => {
                let trait_pos = &c.name.0;
                for meth in &c.methods {
                    if meth.visibility == Visibility::Internal
                        && !attrs::mem(sn::user_attributes::MODULE_LEVEL_TRAIT, &c.user_attributes)
                    {
                        errors.add(NastCheckError::InternalMemberInsidePublicTrait {
                            member_pos: meth.span.clone(),
                            trait_pos: trait_pos.clone(),
                            is_method: true,
                        });
                    }
                }
                for cv in &c.vars {
                    if cv.visibility == Visibility::Internal {
                        errors.add(NastCheckError::InternalMemberInsidePublicTrait {
                            member_pos: cv.span.clone(),
                            trait_pos: trait_pos.clone(),
                            is_method: false,
                        });
                    }
                }
            }
            ClassishKind::Ctrait
            | ClassishKind::Cclass(_)
            | ClassishKind::Cinterface
            | ClassishKind::Cenum
            | ClassishKind::CenumClass(_) => {}
        }
    }
}
