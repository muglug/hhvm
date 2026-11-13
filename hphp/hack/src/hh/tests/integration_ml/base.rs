// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/integration_test_base.ml` (+ `.mli`,
//! `integration_test_base_types.ml`): an in-process server driven one loop
//! iteration at a time (`Server_main.serve_one_iteration` with a
//! `TestProvider`).
//!
//! Owned by **T1** (plan §3.1). Interfaces by W0 (plan §3.2).

use hh::diagnostics_state;
use hh::server_command_types;
use hh::server_config;
use hh::server_env::Env;

type Diag = diagnostics_state::T;

/// `disk_changes_type`: (path, contents).
pub type DiskChanges<'a> = &'a [(&'a str, &'a str)];

/// `'a loop_inputs` (`new_client = Some (RequestResponse cmd)`).
#[derive(Default)]
pub struct LoopInputs {
    pub disk_changes: Vec<(String, String)>,
    pub new_client: Option<server_command_types::T>,
}

/// `'a loop_outputs`
#[derive(Default)]
pub struct LoopOutputs {
    pub did_read_disk_changes: bool,
    pub total_changed_files_count: isize,
    pub total_rechecked_count: isize,
    pub last_actual_total_rechecked_count: Option<isize>,
    pub new_client_response: Option<server_command_types::CommandResult>,
}

pub fn setup_server(
    custom_config: Option<server_config::T>,
    hhi_files: &[(&str, &str)],
    edges_dir: Option<&str>,
) -> Env {
    let _ = (custom_config, hhi_files, edges_dir);
    todo!("Integration_test_base.setup_server: T1 in progress")
}

pub fn setup_disk(env: Env, disk_changes: DiskChanges) -> Env {
    let _ = (env, disk_changes);
    todo!("Integration_test_base.setup_disk: T1 in progress")
}

pub fn change_files(env: Env, disk_changes: DiskChanges) -> (Env, LoopOutputs) {
    let _ = (env, disk_changes);
    todo!("Integration_test_base.change_files: T1 in progress")
}

pub fn run_loop_once(env: Env, inputs: LoopInputs) -> (Env, LoopOutputs) {
    let _ = (env, inputs);
    todo!("Integration_test_base.run_loop_once: T1 in progress")
}

pub fn assert_no_diagnostics(env: &Env) {
    let _ = env;
    todo!("Integration_test_base.assert_no_diagnostics: T1 in progress")
}

pub fn assert_env_diagnostics(env: &Env, expected: &str) {
    let _ = (env, expected);
    todo!("Integration_test_base.assert_env_diagnostics: T1 in progress")
}

pub fn assert_diagnostics(diagnostics: &Diag, expected: &str) {
    let _ = (diagnostics, expected);
    todo!("Integration_test_base.assert_diagnostics: T1 in progress")
}

/// `assertSingleDiagnostic expected diagnostics`
pub fn assert_single_diagnostic(expected: &str, diagnostics: &[diagnostics_state::Diagnostic]) {
    let _ = (expected, diagnostics);
    todo!("Integration_test_base.assertSingleDiagnostic: T1 in progress")
}

pub fn assert_needs_recheck(env: &Env, path: &str) {
    let _ = (env, path);
    todo!("Integration_test_base.assert_needs_recheck: T1 in progress")
}

/// Removes the root prefix from `s`.
pub fn relativize(s: &str) -> String {
    let _ = s;
    todo!("Integration_test_base.relativize: T1 in progress")
}
