// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_log_errors.ml`. See `hh/PORTING.md`.

use crate::diagnostics_state;
use crate::filter_diagnostics;
use crate::relative_path;
use crate::server_command_types::FileInput;
use crate::server_env;
use crate::tast_provider;
use crate::telemetry;
use crate::user_diagnostic;
use crate::yojson::safe as yojson;

pub fn go(
    env: &server_env::Env,
    files: &[String],
    error_filter: filter_diagnostics::filter::T,
    preexisting_warnings: bool,
) -> telemetry::T {
    let file_names: Vec<FileInput> = files.iter().map(|filename| FileInput::FileName(filename.clone())).collect();
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    // (`env.init_env.mergebase_warning_hashes`: the port's init env has none.)
    let _ = preexisting_warnings;
    let tast_error_filter = tast_provider::ErrorFilter {
        error_filter,
        warnings_saved_state: None,
    };
    let (errors, _tasts) = crate::server_status_single::go(&file_names, &ctx, false, &tast_error_filter);
    // Define error JSON serialization function.
    // This differs from `hh --json` to align with the information sent to VSCode
    // (similar structure, though not identical). The `hh --json` format includes
    // unnecessary extra fields that aren't needed for this use case.
    let error_to_json = |err: &oxidized::diagnostics::Diagnostic| -> yojson::T {
        let user_diagnostic::UserDiagnostic {
            severity,
            claim: oxidized::message::Message(pos, claim_msg),
            reasons,
            custom_msgs,
            ..
        } = user_diagnostic::to_absolute(err);
        let msg_to_json = |msg: &[u8]| {
            yojson::T::String(crate::markdown_lite::render(
                Some(false),
                None,
                &String::from_utf8_lossy(msg),
            ))
        };
        let reason_to_json = |oxidized::message::Message(pos, msg): &oxidized::message::Message<crate::pos::Absolute>| {
            yojson::T::Assoc(vec![
                ("location".to_string(), crate::pos::multiline_json(pos)),
                ("message".to_string(), msg_to_json(msg)),
            ])
        };
        yojson::T::Assoc(vec![
            (
                "severity".to_string(),
                yojson::T::String(user_diagnostic::severity::to_all_caps_string(&severity)),
            ),
            ("range".to_string(), crate::pos::multiline_json_no_filename(&pos)),
            ("message".to_string(), msg_to_json(&claim_msg)),
            (
                "relatedInformation".to_string(),
                yojson::T::List(reasons.iter().map(reason_to_json).collect()),
            ),
            (
                "customErrors".to_string(),
                yojson::T::List(custom_msgs.iter().map(|m| msg_to_json(m.as_bytes())).collect()),
            ),
            (
                "lineAgnosticHash".to_string(),
                yojson::T::String(format!("{:x}", user_diagnostic::hash_diagnostic_for_saved_state(err))),
            ),
        ])
    };
    let errors = diagnostics_state::drop_fixmed_errors_in_files(errors);
    let file_to_errors = diagnostics_state::as_map(errors);
    let compute_file_telemetry = |fn_: &String| {
        let relpath = relative_path::create_detect_prefix(fn_);
        let diagnostics: Vec<yojson::T> = file_to_errors
            .get(&relpath)
            .map(|errs| errs.iter().map(error_to_json).collect())
            .unwrap_or_default();
        let t = telemetry::create();
        let t = telemetry::string_(None, "filename", &relative_path::to_absolute(&relpath), t);
        telemetry::json("diagnostics", yojson::T::List(diagnostics), t)
    };
    let per_file: Vec<telemetry::T> = files.iter().map(compute_file_telemetry).collect();
    telemetry::object_list("errors", &per_file, telemetry::create())
}
