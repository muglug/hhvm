// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 14189-14211): module `File_attribute`.
//! See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::diagnostics_state;
use crate::tast;
use crate::typing::user_attribute;
use crate::typing_env_types::Env;

pub fn file_attributes(env: &mut Env, file_attrs: &[nast::FileAttribute]) -> Vec<tast::FileAttribute> {
    // Disable checking of error positions, as file attributes have spans that
    // aren't subspans of the class or function into which they are copied
    diagnostics_state::run_with_span(Pos::NONE, || {
        file_attrs
            .iter()
            .map(|fa| {
                let user_attributes = user_attribute::attributes_check_def(
                    env,
                    sn::attribute_kinds::FILE,
                    &fa.user_attributes.0,
                );
                aast::FileAttribute {
                    user_attributes: aast::UserAttributes(user_attributes),
                    namespace: fa.namespace.clone(),
                }
            })
            .collect()
    })
}
