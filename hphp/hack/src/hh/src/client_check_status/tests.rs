// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The tests of `Client_check_status`.
//!
//! What `go` and the streaming consumer print goes to stdout: each test runs
//! its body again in a child process (this test binary, running that one
//! test), whose stdout is a file ([`in_child`]); the parent compares it with
//! what the OCaml prints (its format strings; the byte-exact comparison of
//! whole runs with the OCaml `hh_client` is in the report of STATUS, against
//! `/tmp/hh-incr/status/fixtures`).

use std::os::fd::AsRawFd;
use std::sync::mpsc;

use super::*;
use crate::rt::diagnostic_fixtures as fx;

/// Set in the child: the file its stdout goes to.
const OUT_VAR: &str = "HH_CLIENT_CHECK_STATUS_TEST_OUT";

/// In the parent, runs the test `test` of this module again in a child
/// process and returns `Some((stdout, what body returned))`; in the child,
/// runs `body` with its stdout in the file and returns `None`.
fn in_child(test: &str, body: impl FnOnce() -> String) -> Option<(String, String)> {
    if let Some(out_file) = std::env::var_os(OUT_VAR) {
        let out = std::fs::File::create(&out_file).unwrap();
        let _ = std::io::stdout().flush();
        let saved = unsafe { libc::dup(1) };
        unsafe {
            libc::dup2(out.as_raw_fd(), 1);
        }
        let res = body();
        let _ = std::io::stdout().flush();
        // (What the test harness prints next goes to the real stdout.)
        unsafe {
            libc::dup2(saved, 1);
            libc::close(saved);
        }
        std::fs::write(format!("{}.res", out_file.to_str().unwrap()), res).unwrap();
        return None;
    }
    let out_file = std::env::temp_dir().join(format!(
        "hh_ccs_test_{}_{}",
        std::process::id(),
        test
    ));
    let name = format!("client_check_status::tests::{}", test);
    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .args([&name, "--exact", "--nocapture", "--test-threads=1", "-q"])
        .env(OUT_VAR, &out_file)
        .env("TERM", "dumb")
        .env_remove("FORCE_ERROR_COLOR")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::piped())
        .output()
        .unwrap();
    assert!(
        status.status.success(),
        "the child of {} failed: {}",
        name,
        String::from_utf8_lossy(&status.stderr)
    );
    let out = std::fs::read_to_string(&out_file).unwrap();
    let res = std::fs::read_to_string(format!("{}.res", out_file.to_str().unwrap())).unwrap();
    let _ = std::fs::remove_file(&out_file);
    let _ = std::fs::remove_file(format!("{}.res", out_file.to_str().unwrap()));
    Some((out, res))
}

/// A file with ten lines `line N`, so that every formatter finds its
/// positions.
fn file(name: &str) -> String {
    let dir = std::env::temp_dir().join(format!("hh_ccs_files_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    let contents: String = (1..=10).map(|n| format!("line {}\n", n)).collect();
    std::fs::write(&path, contents).unwrap();
    path.to_str().unwrap().to_string()
}

fn err(file: &str, line: usize, text: &str) -> FinalizedDiagnostic {
    fx::diagnostic(
        Severity::Err,
        4110,
        fx::msg(fx::pos(file, (line, 0), (line, 4)), text),
        vec![],
    )
}

fn warn(file: &str, line: usize, text: &str) -> FinalizedDiagnostic {
    fx::diagnostic(
        Severity::Warning { is_trusted: true },
        12007,
        fx::msg(fx::pos(file, (line, 0), (line, 4)), text),
        vec![],
    )
}

fn status(error_list: Vec<FinalizedDiagnostic>, dropped_count: isize) -> server_status::T {
    server_status::T {
        liveness: StatusLiveness::LiveStatus,
        error_list,
        dropped_count,
        last_recheck_stats: None,
        file_watcher_clock: None,
    }
}

fn texts(format: Format, ds: &[FinalizedDiagnostic]) -> String {
    ds.iter().map(|d| diagnostic_string(format, d)).collect()
}

fn set_prefixes() {
    crate::relative_path::set_path_prefix(
        relative_path::Prefix::Root,
        std::path::Path::new("/"),
    );
}

#[test]
fn go_no_errors() {
    let Some((out, res)) = in_child("go_no_errors", || {
        exit_status::show(&go(status(vec![], 0), None, false, false, false, None))
    }) else {
        return;
    };
    assert_eq!(out, "No errors!\n");
    assert_eq!(res, "Exit_status.No_error");
}

/// Without an error format and not interactive, `Server_error.print_error_list`
/// prints the errors and the exit code is 0.
#[test]
fn go_errors_not_interactive() {
    let Some((out, res)) = in_child("go_errors_not_interactive", || {
        set_prefixes();
        let a = file("a.php");
        let ds = vec![err(&a, 3, "three"), err(&a, 1, "one")];
        let mut expected = vec![];
        server_error::print_error_list(&mut expected, None, false, None, &ds, None);
        let es = go(status(ds, 0), None, false, false, false, None);
        format!(
            "{}|{}",
            exit_status::show(&es),
            String::from_utf8(expected).unwrap()
        )
    }) else {
        return;
    };
    let (es, expected) = res.split_once('|').unwrap();
    assert_eq!(es, "Exit_status.No_error");
    assert_eq!(out, expected);
    assert!(out.starts_with("ERROR: File \""));
}

/// Interactive, or with an error format: each diagnostic in the format,
/// then the summary of the format, then the stale message.
#[test]
fn go_errors_with_a_format() {
    let Some((out, res)) = in_child("go_errors_with_a_format", || {
        set_prefixes();
        let a = file("a.php");
        let ds = vec![warn(&a, 2, "w"), err(&a, 3, "e")];
        let mut st = status(ds.clone(), 3);
        st.liveness = StatusLiveness::StaleStatus;
        let es = go(st, Some(Format::Context), false, false, false, Some(2));
        format!(
            "{}|{}",
            exit_status::show(&es),
            texts(Format::Context, &ds)
        )
    }) else {
        return;
    };
    let (es, diagnostics) = res.split_once('|').unwrap();
    assert_eq!(es, "Exit_status.Type_error");
    assert_eq!(
        out,
        format!(
            "{}1 error, 1 warning found (only showing first 2, dropped 3)\n(but this may be stale, probably due to file watcher being unresponsive)\n",
            diagnostics
        )
    );
}

/// Warnings only: the exit code is 0 (`test_warning_exit_code.py`).
#[test]
fn go_warnings_only_interactive() {
    let Some((out, res)) = in_child("go_warnings_only_interactive", || {
        set_prefixes();
        let a = file("a.php");
        let ds = vec![warn(&a, 2, "w")];
        let es = go(status(ds.clone(), 0), Some(Format::Raw), true, false, false, None);
        format!("{}|{}", exit_status::show(&es), texts(Format::Raw, &ds))
    }) else {
        return;
    };
    let (es, diagnostics) = res.split_once('|').unwrap();
    assert_eq!(es, "Exit_status.No_error");
    // (No summary for `Raw` when there is something to show.)
    assert_eq!(out, diagnostics);
}

/// `--json`: always exit 0.
#[test]
fn go_json() {
    let Some((out, res)) = in_child("go_json", || {
        set_prefixes();
        let a = file("a.php");
        let ds = vec![err(&a, 3, "e")];
        let mut expected = vec![];
        server_error::print_error_list(&mut expected, None, true, Some(Format::Raw), &ds, None);
        let es = go(status(ds, 0), Some(Format::Raw), true, true, false, None);
        format!(
            "{}|{}",
            exit_status::show(&es),
            String::from_utf8(expected).unwrap()
        )
    }) else {
        return;
    };
    let (es, expected) = res.split_once('|').unwrap();
    assert_eq!(es, "Exit_status.No_error");
    assert_eq!(out, expected);
    assert!(out.contains("\"passed\":false"));
}

/// `--jsonl`: one line per diagnostic, then the summary; 2 when there is an
/// error.
#[test]
fn go_jsonl() {
    let Some((out, res)) = in_child("go_jsonl", || {
        set_prefixes();
        let a = file("a.php");
        let ds = vec![warn(&a, 2, "w"), err(&a, 3, "e")];
        let es = go(status(ds, 0), None, false, false, true, None);
        exit_status::show(&es)
    }) else {
        return;
    };
    assert_eq!(res, "Exit_status.Type_error");
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), 3);
    assert!(lines[0].starts_with("{\"kind\":\"diagnostic\",\"severity\":\"warning\""));
    assert!(lines[1].starts_with("{\"kind\":\"diagnostic\",\"severity\":\"error\""));
    assert!(lines[2].starts_with("{\"kind\":\"summary\",\"passed\":false,\"version\":"));
    assert!(lines[2].ends_with(",\"error_count\":1,\"warning_count\":1}"));
}

// ~~ Streaming ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn check_env(max_errors: Option<isize>, output_jsonl: bool) -> client_env::ClientCheckEnv {
    client_env::ClientCheckEnv {
        autostart: true,
        config: vec![],
        custom_hhi_path: None,
        custom_telemetry_data: vec![],
        error_format: Some(Format::Raw),
        force_dormant_start: false,
        from: "test".to_string(),
        show_spinner: false,
        ignore_hh_version: false,
        saved_state_ignore_hhconfig: false,
        paths: vec![],
        max_errors,
        preexisting_warnings: false,
        reason: None,
        mode: client_env::ClientMode::MODESTATUS,
        no_load: false,
        save_64bit: None,
        save_human_readable_64bit_dep_map: None,
        output_json: false,
        output_jsonl,
        prechecked: None,
        mini_state: None,
        root: "/".to_string(),
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

fn errors_item(ds: Vec<FinalizedDiagnostic>) -> Result<ReadResult, WatchError> {
    let mut errors = relative_path::map::T::new();
    errors.insert(
        relative_path::RelativePath::make(relative_path::Prefix::Root, "a.php".into()),
        ds.into_iter().map(|d| (d, 0)).collect(),
    );
    Ok(ReadResult::RItem(ErrorsFileItem::Errors {
        errors,
        timestamp: 0.,
    }))
}

/// Runs the streaming consumer on `items`; returns the exit status it ends
/// with (`Ok` or `Exit_with`).
fn stream(
    items: Vec<Result<ReadResult, WatchError>>,
    max_errors: Option<isize>,
    output_jsonl: bool,
    default_all: bool,
) -> String {
    let (tx, rx) = mpsc::channel();
    for item in items {
        tx.send(item).unwrap();
    }
    drop(tx);
    let partial: PartialTelemetryRef = Arc::new(Mutex::new(None));
    let cb: ProgressCallback = Arc::new(|_| {});
    let res = go_streaming_on_errors_stream(
        "inode#1:2",
        rx,
        &check_env(max_errors, output_jsonl),
        &filter_diagnostics::filter::make(default_all, vec![], vec![]),
        &partial,
        telemetry::create(),
        &cb,
    );
    match res {
        Ok((es, _)) => format!("Ok {}", exit_status::show(&es)),
        Err(Exn::ExitWith(es)) => format!("Exit_with {}", exit_status::show(&es)),
        Err(Exn::Other(_)) => "other".to_string(),
    }
}

#[test]
fn streaming_complete() {
    let Some((out, res)) = in_child("streaming_complete", || {
        set_prefixes();
        let a = file("a.php");
        let res = stream(
            vec![
                errors_item(vec![err(&a, 1, "one")]),
                Ok(ReadResult::RItem(ErrorsFileItem::Telemetry(telemetry::create()))),
                errors_item(vec![warn(&a, 2, "w"), err(&a, 3, "three")]),
                Ok(ReadResult::RCompleted(
                    CompletionReason::Complete(telemetry::create()),
                    "complete".to_string(),
                )),
            ],
            None,
            false,
            true,
        );
        format!(
            "{}|{}",
            res,
            texts(
                Format::Raw,
                &[err(&a, 1, "one"), warn(&a, 2, "w"), err(&a, 3, "three")]
            )
        )
    }) else {
        return;
    };
    let (res, diagnostics) = res.split_once('|').unwrap();
    assert_eq!(res, "Ok Exit_status.Type_error");
    // (`Raw` has no summary when there is something to show.)
    assert_eq!(out, diagnostics);
}

#[test]
fn streaming_filters_warnings_and_completes_without_errors() {
    let Some((out, res)) = in_child("streaming_filters_warnings_and_completes_without_errors", || {
        set_prefixes();
        let a = file("a.php");
        stream(
            vec![
                errors_item(vec![warn(&a, 2, "w")]),
                Ok(ReadResult::RCompleted(
                    CompletionReason::Complete(telemetry::create()),
                    "complete".to_string(),
                )),
            ],
            None,
            false,
            false,
        )
    }) else {
        return;
    };
    assert_eq!(res, "Ok Exit_status.No_error");
    assert_eq!(out, "No errors!\n");
}

#[test]
fn streaming_max_errors_counts_the_rest() {
    let Some((out, res)) = in_child("streaming_max_errors_counts_the_rest", || {
        set_prefixes();
        let a = file("a.php");
        let res = stream(
            vec![
                errors_item(vec![err(&a, 1, "one"), err(&a, 2, "two")]),
                errors_item(vec![warn(&a, 3, "w"), err(&a, 4, "four")]),
                Ok(ReadResult::RCompleted(
                    CompletionReason::Complete(telemetry::create()),
                    "complete".to_string(),
                )),
            ],
            Some(1),
            false,
            true,
        );
        format!("{}|{}", res, texts(Format::Raw, &[err(&a, 1, "one")]))
    }) else {
        return;
    };
    let (res, first) = res.split_once('|').unwrap();
    assert_eq!(res, "Ok Exit_status.Type_error");
    assert_eq!(
        out,
        format!(
            "{}1 errors found (not showing all due to --max-errors 1)\n\x1b[1B\x1b[1A\r\x1b[0K2 errors, 1 warnings found (not showing all due to --max-errors 1)\n\x1b[1B",
            first
        )
    );
}

#[test]
fn streaming_restarted() {
    let Some((out, res)) = in_child("streaming_restarted", || {
        stream(
            vec![Ok(ReadResult::RCompleted(
                CompletionReason::Restarted {
                    user_message: "Typecheck restarted".to_string(),
                    log_message: "log".to_string(),
                },
                "new_empty_file".to_string(),
            ))],
            None,
            false,
            true,
        )
    }) else {
        return;
    };
    assert_eq!(res, "Exit_with Exit_status.Typecheck_restarted");
    assert_eq!(out, "\nTypecheck restarted\nPlease re-run hh.\n");
}

#[test]
fn streaming_stopped_and_killed() {
    let Some((out, res)) = in_child("streaming_stopped_and_killed", || {
        let stopped = stream(
            vec![Ok(ReadResult::RCompleted(
                CompletionReason::Stopped,
                "unlink".to_string(),
            ))],
            None,
            false,
            true,
        );
        let killed = stream(vec![Err(WatchError::Killed(None))], None, false, true);
        format!("{} {}", stopped, killed)
    }) else {
        return;
    };
    assert_eq!(
        res,
        "Exit_with Exit_status.Typecheck_abandoned Exit_with Exit_status.Typecheck_abandoned"
    );
    assert_eq!(
        out,
        "hh_server has terminated. [Stopped]\nhh_server has terminated. [Killed]\n"
    );
}

#[test]
fn streaming_jsonl() {
    let Some((out, res)) = in_child("streaming_jsonl", || {
        set_prefixes();
        let a = file("a.php");
        let complete = stream(
            vec![
                errors_item(vec![err(&a, 1, "one")]),
                Ok(ReadResult::RCompleted(
                    CompletionReason::Complete(telemetry::create()),
                    "complete".to_string(),
                )),
            ],
            None,
            true,
            true,
        );
        let stopped = stream(
            vec![Ok(ReadResult::RCompleted(
                CompletionReason::Stopped,
                "unlink".to_string(),
            ))],
            None,
            true,
            true,
        );
        let restarted = stream(
            vec![Ok(ReadResult::RCompleted(
                CompletionReason::Restarted {
                    user_message: "again".to_string(),
                    log_message: "log".to_string(),
                },
                "x".to_string(),
            ))],
            None,
            true,
            true,
        );
        format!("{} {} {}", complete, stopped, restarted)
    }) else {
        return;
    };
    assert_eq!(
        res,
        "Ok Exit_status.Type_error Exit_with Exit_status.Typecheck_abandoned Exit_with Exit_status.Typecheck_restarted"
    );
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), 4);
    assert!(lines[0].starts_with("{\"kind\":\"diagnostic\",\"severity\":\"error\""));
    assert!(lines[1].starts_with("{\"kind\":\"summary\",\"passed\":false"));
    assert_eq!(
        lines[2],
        "{\"kind\":\"stopped\",\"message\":\"hh_server has terminated. [Stopped]\"}"
    );
    assert_eq!(lines[3], "{\"kind\":\"restarted\",\"message\":\"again\"}");
}

#[test]
fn end_sentinel_printers() {
    assert_eq!(
        show_end_sentinel(&EndSentinel::Completed(CompletionReason::Stopped)),
        "(Client_check_status.Completed Stopped)"
    );
    assert_eq!(
        end_sentinel_short_string(&EndSentinel::WatchError(WatchError::Killed(None))),
        "Killed"
    );
    assert_eq!(
        show_end_sentinel(&EndSentinel::WatchError(WatchError::Killed(None))),
        "(Client_check_status.Watch_error (Server_progress_lwt.Killed None))"
    );
}
