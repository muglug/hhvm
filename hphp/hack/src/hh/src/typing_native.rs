// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_native.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;

use crate::naming_attributes;
use crate::provider_context;
use crate::typing_env;
use crate::typing_env_types::Env;

pub fn is_native_fun<Ex, En>(env: &Env, f: &aast::Fun_<Ex, En>) -> bool {
    // `Typechecker_options.is_systemlib`
    provider_context::get_tcopt(&typing_env::get_ctx(env))
        .po
        .is_systemlib
        && naming_attributes::mem(sn::user_attributes::NATIVE, &f.user_attributes.0)
}

pub fn is_native_meth<Ex, En>(env: &Env, m: &aast::Method_<Ex, En>) -> bool {
    // `Typechecker_options.is_systemlib`
    provider_context::get_tcopt(&typing_env::get_ctx(env))
        .po
        .is_systemlib
        && naming_attributes::mem(sn::user_attributes::NATIVE, &m.user_attributes.0)
}
