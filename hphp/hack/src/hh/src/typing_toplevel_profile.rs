// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_toplevel_profile.ml`. See `hh/PORTING.md`.
//!
//! `id` is a `'a * string` in OCaml; every caller passes the name of a
//! definition (`Ast_defs.id`), so it is an `ast_defs::Id` here.

use oxidized::ast_defs;

use crate::typechecker_options::TypecheckerOptions;
use crate::typing_env as env;
use crate::typing_env_types::Env;

/// `Unix.gettimeofday ()`
fn gettimeofday() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0.0, |d| d.as_secs_f64())
}

/// Measure the time it takes to evaluate the last argument and write the
/// result to console along with the given identifier.
pub fn measure_elapsed_time_and_report<B>(
    tcopt: &TypecheckerOptions,
    env_opt: Option<&Env>,
    id: &ast_defs::Id,
    f: impl FnOnce() -> B,
) -> B {
    // `Typechecker_options.profile_top_level_definitions`
    if tcopt.tco_profile_top_level_definitions {
        let start_time = gettimeofday();
        let result = f();
        let end_time = gettimeofday();
        let elapsed_time_ms = (end_time - start_time) * 1000.;
        let id = match env_opt.and_then(env::get_self_id) {
            Some(class_name) => class_name + "::" + &id.1,
            None => id.1.clone(),
        };
        // `Printf.printf "%s: %0.2fms\n" id elapsed_time_ms`
        print!("{}: {:.2}ms\n", id, elapsed_time_ms);
        result
    } else {
        f()
    }
}
