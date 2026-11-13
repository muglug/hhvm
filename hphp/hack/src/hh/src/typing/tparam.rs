// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 14213-14232): module `Tparam`.
//! See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::nast;

use crate::tast;
use crate::typing::user_attribute;
use crate::typing_env_types::Env;
// open Typing_helpers
use crate::typing_helpers::reify_kind;

pub fn type_param(env: &mut Env, t: &nast::Tparam) -> tast::Tparam {
    let user_attributes = user_attribute::attributes_check_def(
        env,
        sn::attribute_kinds::TYPE_PARAM,
        &t.user_attributes.0,
    );
    aast::Tparam {
        variance: t.variance,
        name: t.name.clone(),
        constraints: t.constraints.clone(),
        reified: reify_kind(t.reified),
        user_attributes: aast::UserAttributes(user_attributes),
    }
}
