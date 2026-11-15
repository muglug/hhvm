// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: the tests of `client_check`.

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

/// `Filter.make` gets the generated-file patterns of `.hhconfig` and the
/// `-W` switches of the command line.
#[test]
fn the_error_filter_of_the_status() {
    let config = server_config::default_config();
    let local_config = crate::server_local_config_load::default();
    let mut a = args(ClientMode::ModeStatus);
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

/// The argument errors of the position modes, before connecting.
#[test]
fn position_argument_errors() {
    assert!(matches!(
        parse_position_string(":", "12"),
        Err(Exn::ExitWith(exit_status::T::InputError))
    ));
    assert!(matches!(parse_position_string(":", "0x10:2"), Ok((16, 2))));
    let config = server_config::default_config();
    let local_config = crate::server_local_config_load::default();
    let partial: PartialTelemetryRef = Arc::new(Mutex::new(None));
    for mode in [
        // `--identify` needs `--json`
        ClientMode::ModeIdentifySymbol("C".to_string()),
        // a position of one field
        ClientMode::ModeTypeAtPosBatch(vec!["a.php".to_string()]),
    ] {
        match main_internal(&args(mode), &config, &local_config, &partial) {
            Err(Exn::ExitWith(es)) => assert!(matches!(es, exit_status::T::InputError)),
            _ => panic!("expected Exit_with Input_error"),
        }
    }
}

fn isolation_result() -> server_isolation_types::Result {
    server_isolation_types::Result {
        refused: None,
        movability: None,
        grown: false,
        total_seeds: 1,
        total_isolatable_files: 1,
        total_clusters: 1,
        total_truncated: 0,
        total_refused: 0,
        largest_cluster: 1,
    }
}

fn isolation_text(result: &server_isolation_types::Result, output_json: bool) -> String {
    let mut out = vec![];
    write_isolation_result(&mut out, result, output_json).unwrap();
    String::from_utf8(out).unwrap()
}

#[test]
fn truncated_clusters_sentences() {
    assert_eq!(
        truncated_clusters_sentence(1, 1),
        "It stopped at the size cap and is not complete.\n"
    );
    assert_eq!(
        truncated_clusters_sentence(5, 1),
        "1 of them stopped at the size cap and is not complete.\n"
    );
    assert_eq!(
        truncated_clusters_sentence(5, 3),
        "3 of them stopped at the size cap and are not complete.\n"
    );
}

#[test]
fn isolation_results_as_text() {
    use server_isolation_types::Movability;
    let r = isolation_result();
    assert_eq!(
        isolation_text(&r, false),
        "Started from 1 file.\nFound 1 isolatable cluster without growing, covering 1 file.\n"
    );
    let r = server_isolation_types::Result {
        total_seeds: 7,
        total_isolatable_files: 9,
        total_clusters: 3,
        largest_cluster: 4,
        total_refused: 2,
        ..isolation_result()
    };
    assert_eq!(
        isolation_text(&r, false),
        "Started from 7 files.\n\
         Found 3 isolatable clusters without growing, covering 9 files in all; the largest has 4 files.\n\
         Not in any cluster: 2 starting files (for example, more files depend on one than --isolation-max-dependents allows, or it declares nothing).\n"
    );
    let r = server_isolation_types::Result {
        grown: true,
        total_seeds: 7,
        total_isolatable_files: 9,
        total_clusters: 3,
        total_truncated: 2,
        largest_cluster: 4,
        ..isolation_result()
    };
    assert_eq!(
        isolation_text(&r, false),
        "Started from 7 files.\nGrew 3 clusters covering 9 files (largest: 4).\n\
         2 of them stopped at the size cap and are not complete.\n"
    );
    let r = server_isolation_types::Result {
        grown: true,
        total_truncated: 1,
        ..isolation_result()
    };
    assert_eq!(
        isolation_text(&r, false),
        "Started from 1 file.\nGrew 1 cluster covering 1 file.\n\
         It stopped at the size cap and is not complete.\n"
    );
    let r = server_isolation_types::Result {
        movability: Some(Movability::Movable),
        total_isolatable_files: 2,
        ..isolation_result()
    };
    assert_eq!(isolation_text(&r, false), "Movable: 2 files, nothing outside references in.\n");
    let r = server_isolation_types::Result {
        movability: Some(Movability::Blocked(vec![
            server_isolation_types::Blocker {
                file: "a.php".to_string(),
                references: vec!["x.php".to_string()],
            },
            server_isolation_types::Blocker {
                file: "b.php".to_string(),
                references: vec!["x.php".to_string(), "y.php".to_string()],
            },
        ])),
        ..isolation_result()
    };
    assert_eq!(
        isolation_text(&r, false),
        "Blocked: referenced from 2 files outside.\n  a.php\n  b.php\n"
    );
    assert_eq!(
        isolation_text(&r, true),
        "{\"refused\":null,\"movability\":\"blocked\",\"blockers\":[\"a.php\",\"b.php\"],\"blocked_by\":[{\"file\":\"a.php\",\"references\":[\"x.php\"]},{\"file\":\"b.php\",\"references\":[\"x.php\",\"y.php\"]}],\"summary\":{\"grown\":false,\"total_seeds\":1,\"total_isolatable_files\":1,\"total_clusters\":1,\"total_truncated\":0,\"total_refused\":0,\"largest_cluster\":1}}\n"
    );
    let r = server_isolation_types::Result {
        refused: Some("too many".to_string()),
        movability: Some(Movability::Movable),
        ..isolation_result()
    };
    assert_eq!(isolation_text(&r, false), "Did not run: too many\n");
    assert!(matches!(isolation_status(&r), exit_status::T::InputError));
    assert!(matches!(isolation_status(&isolation_result()), exit_status::T::NoError));
}

/// Telemetry keeps the old name of the files mode.
#[test]
fn telemetry_mode_names() {
    assert_eq!(
        telemetry_mode_name(&ClientMode::ModeStatusFiles(client_env::StatusFiles {
            filenames: vec![],
            show_tast: false,
            preexisting_warnings: false,
        })),
        "MODE_STATUS_SINGLE"
    );
    assert_eq!(
        telemetry_mode_name(&ClientMode::ModeValidateIsolation(String::new())),
        "MODE_VALIDATE_ISOLATION"
    );
}

#[test]
fn split_lines_as_base() {
    assert_eq!(split_lines(""), Vec::<&str>::new());
    assert_eq!(split_lines("\n"), vec![""]);
    assert_eq!(split_lines("a\r\nb\n\nc"), vec!["a", "b", "", "c"]);
    assert_eq!(split_lines("a\n"), vec!["a"]);
}

/// `--validate-isolation` reads its list before connecting.
#[test]
fn validate_isolation_input_errors() {
    let config = server_config::default_config();
    let local_config = crate::server_local_config_load::default();
    let partial: PartialTelemetryRef = Arc::new(Mutex::new(None));
    let empty = std::env::temp_dir().join(format!("hh_validate_isolation_{}", std::process::id()));
    std::fs::write(&empty, " \n\t\n").unwrap();
    for list in ["/nonexistent/hh_validate_isolation_list", empty.to_str().unwrap()] {
        let mode = ClientMode::ModeValidateIsolation(list.to_string());
        match main_internal(&args(mode), &config, &local_config, &partial) {
            Err(Exn::ExitWith(es)) => assert!(matches!(es, exit_status::T::InputError)),
            _ => panic!("expected Exit_with Input_error"),
        }
    }
    let _ = std::fs::remove_file(&empty);
}
