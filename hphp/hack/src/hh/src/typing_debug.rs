// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_debug.ml`. See `hh/PORTING.md`.

use oxidized::pos::Pos;

use crate::typing_env as env_;
use crate::typing_env_types::Env;
use crate::typing_inference_env::size::inference_env_size;
use crate::typing_inference_env::size::ty_size;
use crate::typing_per_cont_env;

fn local_env_size(env: &Env) -> isize {
    match env_::next_cont_opt(env) {
        None => 0,
        Some(typing_per_cont_env::PerContEntry { local_types, .. }) => {
            let mut size = 0;
            for (_, local) in local_types.iter() {
                size = size + ty_size(&env.inference_env, &local.ty);
            }
            size
        }
    }
}

fn env_size(env: &Env) -> isize {
    local_env_size(env) + inference_env_size(&env.inference_env)
}

/// `env.big_envs` is shared by the copies of the environment (a `ref` in
/// OCaml): the environment is only read.
///
/// (It is also where the deadline of `Typing_helpers.with_timeout` is
/// checked: see `crate::timeout::check_timeout`.)
pub fn log_env_if_too_big(pos: &Pos, env: &Env) {
    if env_::get_tcopt(env).tco_timeout > 0 {
        crate::timeout::check_timeout()
    }
    if env_::get_tcopt(env).tco_timeout > 0
        && env.big_envs.borrow().len() < 1
        && env_size(env) >= 1000
    {
        // `env.big_envs := (pos, env) :: !(env.big_envs)`: the head of the
        // OCaml list is the last element.
        env.big_envs.borrow_mut().push((pos.clone(), env.clone()))
    }
}
