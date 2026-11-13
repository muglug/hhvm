// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 11789-11869): module `User_attribute`.
//! See `hh/PORTING.md`.
//!
//! OCaml defines `user_attribute` twice, the second definition calling the
//! first: the first is a function nested in the second, as in
//! `typing_coercion.rs`.
//!
//! `attributes_check_def` takes `Nast.user_attribute list` as a slice (the
//! `.0` of an `aast::UserAttributes`) and returns the typed attributes.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::ast_defs;
use crate::naming_attributes;
use crate::pos_or_decl;
use crate::tast;
use crate::typing::expr;
use crate::typing_defs::PosString;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_types::Env;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;

pub(crate) fn user_attribute(env: &mut Env, attr: &nast::UserAttribute) -> tast::UserAttribute {
    /// The first OCaml definition of `user_attribute`, which the second one
    /// shadows.
    fn user_attribute(env: &mut Env, ua: &nast::UserAttribute) -> tast::UserAttribute {
        let aast::UserAttribute {
            name: ua_name,
            params: ua_params,
        } = ua;
        // `List.map_env`: from left to right.
        let typed_ua_params: Vec<tast::Expr> = ua_params
            .iter()
            .map(|e| {
                let (te, _) = expr::expr(
                    None,
                    &expr::context::T {
                        attribute_check_policy: expr::AttributeCheckPolicy::SkipAllAccess,
                        ..expr::context::default()
                    },
                    env,
                    e,
                );
                te
            })
            .collect();

        aast::UserAttribute {
            name: ua_name.clone(),
            params: typed_ua_params,
        }
    }

    let ast_defs::Id(pos, name) = &attr.name;
    // For SimpliHack we allow arbitrary expressions including function calls.
    // In that case it is important to set the capabilities
    if name == sn::user_attributes::SIMPLIHACK {
        // For now use the default capability set, though ideally we would
        // introduce one that is specific to SimpliHack.
        let defaults = make_type::default_capability(pos_or_decl::of_raw_pos(pos.clone()));
        let conts = env::all_continuations(env);
        crate::typing_lenv::stash_and_do(env, &conts, |env| {
            let _ = crate::typing_coeffects::register_capabilities(env, defaults.clone(), defaults);
            user_attribute(env, attr)
        })
    } else {
        user_attribute(env, attr)
    }
}

pub(crate) fn attributes_check_def(
    env: &mut Env,
    kind: &str,
    attrs: &[nast::UserAttribute],
) -> Vec<tast::UserAttribute> {
    let emit_string_coercion_error = env.emit_string_coercion_error;
    env.emit_string_coercion_error = false;
    let new_object =
        |attr_pos: &Pos, env: &mut Env, attr_cid: &PosString, params: &[nast::Argument]| {
            // We'd like the class id's position here to be the use position of the attribute
            // instead of the decl position of the class
            let PosString(_decl_pos, cid_) = attr_cid;
            let _ = expr::new_object(
                None,
                false,
                false,
                true,
                attr_pos,
                env,
                &aast::ClassId(
                    (),
                    attr_pos.clone(),
                    aast::ClassId_::CI(ast_defs::Id(attr_pos.clone(), cid_.clone())),
                ),
                &[],
                // list of attr parameter literals
                params,
                // no variadic arguments
                None,
            );
        };
    crate::typing_attributes::check_def(env, &new_object, kind, attrs);
    // `List.map_env`: from left to right.
    let user_attrs: Vec<tast::UserAttribute> =
        attrs.iter().map(|attr| user_attribute(env, attr)).collect();
    env.emit_string_coercion_error = emit_string_coercion_error;
    // If NoAutoDynamic is set, disable everything_sdt
    if naming_attributes::mem(sn::user_attributes::NO_AUTO_DYNAMIC, &user_attrs) {
        env::set_everything_sdt(env, false)
    }
    user_attrs
}
