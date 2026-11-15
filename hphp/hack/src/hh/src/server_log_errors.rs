// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_log_errors.ml`. See `hh/PORTING.md`.

use crate::diagnostics;
use crate::filter_diagnostics;
use crate::markdown_lite;
use crate::pos;
use crate::provider_utils;
use crate::relative_path;
use crate::server_command_types::FileInput;
use crate::server_env;
use crate::server_status_single;
use crate::tast_provider;
use crate::telemetry;
use crate::user_diagnostic;
use crate::yojson::safe as yojson;

/// Type check files and generate Telemetry with error diagnostics
pub fn go(
    num_workers: isize,
    env: &server_env::Env,
    files: &[String],
    error_filter: filter_diagnostics::filter::T,
    preexisting_warnings: bool,
) -> telemetry::T {
    let file_names: Vec<FileInput> = files.iter().map(|f| FileInput::FileName(f.clone())).collect();
    let ctx = provider_utils::ctx_from_server_env(env);
    let tast_error_filter = tast_provider::ErrorFilter {
        error_filter,
        // (`init_env.mergebase_warning_hashes`: only with saved states.)
        warnings_saved_state: None,
    };
    let _ = preexisting_warnings;
    let (errors, _tasts) = server_status_single::go(num_workers, &file_names, &ctx, false, &tast_error_filter);
    // Define error JSON serialization function.
    // This differs from `hh --json` to align with the information sent to VSCode
    // (similar structure, though not identical). The `hh --json` format includes
    // unnecessary extra fields that aren't needed for this use case.
    let error_to_json = |err: &diagnostics::Diagnostic| -> yojson::T {
        let d = user_diagnostic::to_absolute(err);
        let msg_to_json = |msg: &[u8]| {
            yojson::T::String(markdown_lite::render(Some(false), None, &String::from_utf8_lossy(msg)))
        };
        let reasons = d
            .reasons
            .iter()
            .map(|r| {
                yojson::T::Assoc(vec![
                    ("location".to_string(), pos::multiline_json(&r.0)),
                    ("message".to_string(), msg_to_json(&r.1)),
                ])
            })
            .collect();
        yojson::T::Assoc(vec![
            (
                "severity".to_string(),
                yojson::T::String(user_diagnostic::severity::to_all_caps_string(&d.severity)),
            ),
            ("range".to_string(), pos::multiline_json_no_filename(&d.claim.0)),
            ("message".to_string(), msg_to_json(&d.claim.1)),
            ("relatedInformation".to_string(), yojson::T::List(reasons)),
            (
                "customErrors".to_string(),
                yojson::T::List(d.custom_msgs.iter().map(|m| msg_to_json(m.as_bytes())).collect()),
            ),
            (
                "lineAgnosticHash".to_string(),
                yojson::T::String(format!("{:x}", user_diagnostic::hash_diagnostic_for_saved_state(err))),
            ),
        ])
    };
    let errors = diagnostics::drop_fixmed_errors_in_files(errors);
    let file_to_errors = diagnostics::as_map(errors);
    let compute_file_telemetry = |fn_: &String| {
        let relpath = relative_path::create_detect_prefix(fn_);
        let diagnostics: Vec<yojson::T> = file_to_errors
            .get(&relpath)
            .map(|l| l.iter().map(error_to_json).collect())
            .unwrap_or_default();
        let t = telemetry::string_(None, "filename", &relative_path::to_absolute(&relpath), telemetry::create());
        telemetry::json("diagnostics", yojson::T::List(diagnostics), t)
    };
    let l: Vec<telemetry::T> = files.iter().map(compute_file_telemetry).collect();
    telemetry::object_list("errors", &l, telemetry::create())
}
