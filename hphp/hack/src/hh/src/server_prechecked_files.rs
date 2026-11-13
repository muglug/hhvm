// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_prechecked_files.ml`.
//!
//! Owned by **SS3** (plan §7.3). Created empty by W0b.
//!
//! S1 ported the two hooks that `Server_type_check` calls, for the only
//! status there is until saved states land (`Prechecked_files_disabled`:
//! after a full init the OCaml never enables prechecked files,
//! `server_env_build.ml:62`). SS3 completes them with the other statuses.

use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_env::PrecheckedFilesStatus;
use crate::telemetry;
use crate::typing_deps::dep_set;

type RPSet = crate::relative_path::set::T;

/// `update_rechecked_files env rechecked`: adds `rechecked` to the
/// `rechecked_files` of the status (nothing to add to while disabled).
fn update_rechecked_files(env: Env, rechecked: &RPSet) -> Env {
    let _ = rechecked;
    let prechecked_files = match env.prechecked_files {
        PrecheckedFilesStatus::PrecheckedFilesDisabled => {
            PrecheckedFilesStatus::PrecheckedFilesDisabled
        }
    };
    // (`Hack_event_logger.prechecked_update_rechecked`: a no-op in the
    // open-source build.)
    Env {
        prechecked_files,
        ..env
    }
}

/// `update_after_recheck genv env rechecked ~start_time`
pub fn update_after_recheck(
    genv: &Genv,
    env: Env,
    rechecked: &RPSet,
    start_time: f64,
) -> (Env, telemetry::T) {
    let _ = genv;
    let telemetry = telemetry::create();
    let telemetry = telemetry::duration(Some("start"), start_time, None, telemetry);
    let telemetry = telemetry::int_("rechecked", rechecked.len() as isize, telemetry);
    let env = update_rechecked_files(env, rechecked);
    let telemetry = telemetry::duration(Some("end"), start_time, None, telemetry);
    match (env.full_check_status, env.prechecked_files) {
        // (`Full_check_done, Initial_typechecking ...`: SS3.)
        (_, PrecheckedFilesStatus::PrecheckedFilesDisabled) => (env, telemetry),
    }
}

/// `update_after_local_changes genv env changes ~start_time`
pub fn update_after_local_changes(
    genv: &Genv,
    env: Env,
    changes: &dep_set::T,
    start_time: f64,
) -> (Env, telemetry::T) {
    let _ = genv;
    let telemetry = telemetry::create();
    let telemetry = telemetry::duration(Some("start"), start_time, None, telemetry);
    let telemetry = telemetry::int_("changes", changes.len() as isize, telemetry);
    let (env, telemetry) = match env.prechecked_files {
        PrecheckedFilesStatus::PrecheckedFilesDisabled => {
            let telemetry = telemetry::string_(None, "mode", "disabled", telemetry);
            (env, telemetry)
        }
    };
    let telemetry = telemetry::duration(Some("end"), start_time, None, telemetry);
    (env, telemetry)
}
