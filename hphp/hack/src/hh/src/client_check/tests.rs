// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The tests of `client_check`.

use super::*;

/// A `ClientCheckEnv` for `mode` on a root that has no server (and cannot
/// have one: connecting would fail).
fn args(mode: ClientMode) -> client_env::ClientCheckEnv {
    client_env::ClientCheckEnv {
        autostart: false,
        config: vec![],
        custom_hhi_path: None,
        custom_telemetry_data: vec![],
        error_format: None,
        force_dormant_start: false,
        from: "test".to_string(),
        show_spinner: false,
        ignore_hh_version: false,
        saved_state_ignore_hhconfig: false,
        paths: vec![],
        max_errors: None,
        preexisting_warnings: false,
        reason: None,
        mode,
        no_load: false,
        save_64bit: None,
        save_human_readable_64bit_dep_map: None,
        output_json: false,
        output_jsonl: false,
        prechecked: None,
        mini_state: None,
        root: "/nonexistent/hh_client_check_test".to_string(),
        sort_results: false,
        stdin_name: None,
        deadline: None,
        watchman_debug_logging: false,
        allow_non_opt_build: false,
        desc: "check".to_string(),
        is_interactive: false,
        warning_switches: vec![],
        dump_config: false,
    }
}

/// The modes that are not ported yet stop with `Exit_with Input_error`
/// before connecting (plan §3.4).
#[test]
fn a_mode_that_is_not_ported_exits_10_before_connecting() {
    let config = server_config::default_config();
    let local_config = crate::server_local_config_load::default();
    let partial: PartialTelemetryRef = Arc::new(Mutex::new(None));
    for mode in [
        ClientMode::MODETYPEATPOS("a.php:1:1".to_string()),
        ClientMode::MODELINT,
        ClientMode::MODEFINDREFS("f".to_string()),
        ClientMode::MODEOUTLINE,
    ] {
        match main_internal(&args(mode), &config, &local_config, &partial) {
            Err(Exn::ExitWith(es)) => {
                assert!(matches!(es, exit_status::T::InputError));
                assert_eq!(exit_status::exit_code(&es), 10);
            }
            _ => panic!("expected Exit_with Input_error"),
        }
    }
}

/// `Filter.make` gets the generated-file patterns of `.hhconfig` and the
/// `-W` switches of the command line.
#[test]
fn the_error_filter_of_the_status() {
    let config = server_config::default_config();
    let local_config = crate::server_local_config_load::default();
    let mut a = args(ClientMode::MODESTATUS);
    a.warning_switches = vec![filter_diagnostics::Switch::WAll];
    let f = error_filter(&config, &local_config, &a);
    assert_eq!(
        format!("{:?}", f),
        format!(
            "{:?}",
            filter_diagnostics::filter::make(
                local_config.warnings_default_all,
                server_config::warnings_generated_files(&config)
                    .iter()
                    .map(|s| ocaml_str::regexp(s).unwrap())
                    .collect(),
                vec![filter_diagnostics::Switch::WAll]
            )
        )
    );
}
