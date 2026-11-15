// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/module_fanout_after_interrupt_tests.ml`
//! (group D): a process test (real `hh_client`, monitor and server, see
//! `server_interrupt_test_harness.rs`), not an in-process one. Each of its
//! three tests is an entry of the runner's table.

use crate::server_interrupt_test_harness as harness;

fn consumer_baseline() -> (String, String) {
    ("a_consumer.php".into(), "<?hh\nfinal class ModuleConsumer {}\n".into())
}

fn consumer_with_missing_module() -> (String, String) {
    (
        "a_consumer.php".into(),
        "<?hh\nmodule foo.bar;\nfinal class ModuleConsumer {}\n".into(),
    )
}

fn blocker_baseline() -> (String, String) {
    ("z_blocker.php".into(), "<?hh\nfunction test_blocker(): void {}\n".into())
}

fn blocker_infinite() -> (String, String) {
    (
        "z_blocker.php".into(),
        "<?hh\nfunction test_blocker(): void { hh_loop_forever(); }\n".into(),
    )
}

fn module_definition() -> (String, String) {
    ("module.php".into(), "<?hh\nnew module foo.bar {}\n".into())
}

fn second_wave(changed_file_count: usize) -> Vec<(String, String)> {
    // Every file defines a symbol, so this count is also the number of entries in
    // [redo_type_decl]'s defs map: fewer than 10 run on the master, while 10 or
    // more use workers.
    let filler_count = changed_file_count - 2;
    let fillers = (0..filler_count).map(|index| {
        (
            format!("filler_{:02}.php", index),
            format!("<?hh\nfunction module_fanout_filler_{:02}(): void {{}}\n", index),
        )
    });
    [module_definition(), blocker_baseline()]
        .into_iter()
        .chain(fillers)
        .collect()
}

fn start_server(env: &harness::T) -> String {
    harness::hh(
        env,
        &[
            "--no-load",
            "--config",
            "max_workers=4",
            "--config",
            "produce_streaming_errors=true",
            "--config",
            "interrupt_on_client=true",
            "--custom-hhi-path",
            &env.hhi,
        ],
    )
}

fn assert_contains(text: &str, substring: &str) {
    if !text.contains(substring) {
        panic!("Expected to find {:?} in:\n{}", substring, text)
    }
}

fn assert_interruption_shape(env: &harness::T, log_offset: u64, changed_file_count: usize) {
    let log = harness::server_log_since(env, log_offset);
    assert_contains(&log, "Begin typechecking 2 files.");
    assert_contains(&log, "Typechecked 1 files [1 errors]");
    assert_contains(
        &log,
        &format!(
            "Interrupted by file watcher sync query: {} files changed",
            changed_file_count
        ),
    );
    assert_contains(&log, "Processing deferred typechecking for 1 file(s)");
    assert_contains(
        &log,
        &format!("Processing changes to {} files", changed_file_count),
    );
}

fn files_to_recheck_from_log(log: &str) -> Vec<String> {
    let headers = ["Files to recheck:", "First 10 files to recheck:"];
    let lines: Vec<&str> = log.lines().collect();
    let mut latest: Option<Vec<String>> = None;
    for (i, line) in lines.iter().enumerate() {
        if headers.iter().any(|header| line.ends_with(header)) {
            let files = lines[i + 1..]
                .iter()
                .take_while(|l| l.ends_with(".php"))
                .map(|l| l.to_string())
                .collect();
            latest = Some(files);
        }
    }
    // `Option.value_exn latest`
    latest.expect("Option.value_exn")
}

/// `test_files_to_recheck_uses_latest_section`
pub fn test_files_to_recheck_uses_latest_section() {
    let log = "[old] Files to recheck:\nold.php\n[new] First 10 files to recheck:\na_consumer.php\nfiller.php\n";
    // `Bool_asserter.assert_equals true (...) msg`
    assert!(
        files_to_recheck_from_log(log) == ["a_consumer.php", "filler.php"],
        "the latest timestamp-prefixed recheck section should be selected"
    );
}

fn assert_consumer_fanout(env: &harness::T, log_offset: u64, expect_consumer: bool) {
    let files = files_to_recheck_from_log(&harness::server_log_since(env, log_offset));
    let got = files.iter().any(|f| f == "a_consumer.php");
    assert!(
        expect_consumer == got,
        "unexpected second-wave files-to-recheck set: [{}]",
        files.join(", ")
    );
}

fn run_case(changed_file_count: usize) {
    harness::with_server(
        "allowed_files_for_module_declarations = *\n",
        &[consumer_baseline(), blocker_baseline()],
        |env| {
            let initial = start_server(env);
            // `String_asserter.assert_equals expected got msg`
            assert_eq!(
                "No errors!\n", initial,
                "the server should finish its baseline check before the first wave"
            );
            let log_offset = harness::server_log_offset(env);
            harness::write_files(env, &[consumer_with_missing_module(), blocker_infinite()]);
            harness::with_hh_process(
                env,
                &["check", "--search", "this_is_just_to_check_liveness_of_hh_server"],
                |_first_priority_query| {
                    harness::wait_for_server_log(
                        None,
                        env,
                        log_offset,
                        "the first-wave two-file typecheck",
                        |log| log.contains("Begin typechecking 2 files."),
                    );
                    harness::with_current_errors_stream(env, |current_errors| {
                        harness::wait_for_event(
                            None,
                            current_errors,
                            "consumer.php's missing-module diagnostic",
                            |s| s == "Errors [a_consumer.php=1]",
                        );
                        // The diagnostic is streamed before the worker's dependency edges are
                        // registered. A fresh priority query can only complete after the server has
                        // returned from that merge callback, so awaiting it establishes the barrier
                        // before the second wave without relying on timing.
                        let _ = harness::hh(
                            env,
                            &["check", "--search", "this_is_just_to_check_liveness_of_hh_server"],
                        );
                        let second_wave_log_offset = harness::server_log_offset(env);
                        harness::write_files(env, &second_wave(changed_file_count));
                        let _ = harness::hh(
                            env,
                            &["check", "--search", "this_is_just_to_check_liveness_of_hh_server"],
                        );
                        harness::wait_for_event(
                            None,
                            current_errors,
                            "the interrupted typecheck restart",
                            |s| s.contains("typecheck restarted"),
                        );
                        let final_ = harness::hh(env, &["check", "--error-format", "plain"]);
                        assert_interruption_shape(env, log_offset, changed_file_count);
                        assert_eq!(
                            "No errors!\n", final_,
                            "adding the module should clear the unbound-module diagnostic"
                        );
                        assert_consumer_fanout(env, second_wave_log_offset, true);
                    })
                },
            )
        },
    )
}

/// `test_nine_changed_files`
pub fn test_nine_changed_files() {
    run_case(9)
}

/// `test_ten_changed_files`
pub fn test_ten_changed_files() {
    run_case(10)
}
