// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_global_state.ml`: the globals that a
//! server child (and a worker) gets from the process that starts it.

use serde::Deserialize;
use serde::Serialize;

use crate::hh_logger;
use crate::relative_path;

/// `t`: what the server child gets of the monitor's globals.
/// (`logging_init` is `fun () -> ()` for the server; `no_load` is in the
/// options, there being no `Server_load_flag` here.)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct T {
    pub saved_root: Option<String>,
    pub saved_hhi: Option<String>,
    pub saved_tmp: Option<String>,
    pub trace: bool,
    pub allowed_fixme_codes_strict: Vec<isize>,
    pub code_agnostic_fixme: bool,
    /// The sources of the regular expressions.
    pub paths_to_ignore: Vec<String>,
    pub cgroup_initial_reading: crate::cgroup_profiler::InitialReading,
}

/// `save ~logging_init`
pub fn save() -> T {
    let prefix = |p| relative_path::path_of_prefix(p).ok();
    T {
        saved_root: prefix(relative_path::Prefix::Root),
        saved_hhi: prefix(relative_path::Prefix::Hhi),
        saved_tmp: prefix(relative_path::Prefix::Tmp),
        trace: crate::typing_deps::TRACE.load(std::sync::atomic::Ordering::Relaxed),
        allowed_fixme_codes_strict: crate::diagnostics::allowed_fixme_codes_strict()
            .iter()
            .copied()
            .collect(),
        code_agnostic_fixme: crate::diagnostics::code_agnostic_fixme(),
        paths_to_ignore: crate::files_to_ignore::get_paths_to_ignore()
            .iter()
            .map(|r| r.as_str().to_string())
            .collect(),
        cgroup_initial_reading: crate::cgroup_profiler::get_initial_reading(),
    }
}

/// `worker_id_str`
fn worker_id_str(worker_id: isize) -> String {
    if worker_id == 0 {
        "master".to_string()
    } else {
        format!("worker-{}", worker_id)
    }
}

/// `restore state ~worker_id`
pub fn restore(state: &T, worker_id: isize) {
    hh_logger::set_id(&worker_id_str(worker_id));
    let set = |p, v: &Option<String>| {
        if let Some(v) = v {
            relative_path::set_path_prefix(p, std::path::Path::new(v));
        }
    };
    set(relative_path::Prefix::Root, &state.saved_root);
    set(relative_path::Prefix::Hhi, &state.saved_hhi);
    set(relative_path::Prefix::Tmp, &state.saved_tmp);
    crate::typing_deps::TRACE.store(state.trace, std::sync::atomic::Ordering::Relaxed);
    crate::diagnostics::set_allowed_fixme_codes_strict(
        state.allowed_fixme_codes_strict.iter().copied().collect(),
    );
    crate::diagnostics::set_code_agnostic_fixme(state.code_agnostic_fixme);
    crate::files_to_ignore::set_paths_to_ignore(
        state
            .paths_to_ignore
            .iter()
            .filter_map(|s| regex::Regex::new(s).ok())
            .collect(),
    );
    crate::diagnostics::set_allow_errors_in_default_path(false);
    crate::cgroup_profiler::use_initial_reading(state.cgroup_initial_reading.clone());
}
