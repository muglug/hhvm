// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_const_reifiable.ml`. See `hh/PORTING.md`.

use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::pos_or_decl;
use crate::type_validator::Reification;
use crate::type_validator::TypeValidator;
use crate::typing_defs::*;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_reified_check;

pub fn check_reifiable(env: &Env, tc: &TypeconstType, attr_pos: PosOrDecl) {
    let check_impl = |kind: primary::ReifiableAttrKind, ty: &DeclTy| {
        let emit_err = |pos: Pos, ty_info: typing_error::Lazy<Vec<Message<PosOrDecl>>>| {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::ReifiableAttr {
                    pos,
                    ty_info,
                    attr_pos: attr_pos.clone(),
                    kind,
                }),
                env,
            )
        };
        typing_reified_check::validator().validate_type(
            env,
            pos_or_decl::unsafe_to_raw_pos(tc.name.pos().clone().to_oxidized()),
            ty,
            Some(Reification::Unresolved),
            emit_err,
        )
    };
    match &tc.kind {
        Typeconst::TCConcrete(ConcreteTypeconst { ty: tc_type }) => {
            check_impl(primary::ReifiableAttrKind::Ty, tc_type)
        }
        Typeconst::TCAbstract(AbstractTypeconst {
            as_constraint: _,
            super_constraint: _,
            default: atc_default,
        }) => {
            if let Some(ty) = atc_default {
                check_impl(primary::ReifiableAttrKind::Ty, ty)
            }
        }
    }
}
