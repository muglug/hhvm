// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The tests of `Server_rpc.handle`, on a hand-built environment, and
//! [`fake_server`]: a stand-in daemon (ignored in a normal run) that answers
//! the real `hh_client` with `handle`, on the diagnostics of a full check of
//! a root, for comparisons of the real `hh_client` with the OCaml's.

use std::sync::Arc;

use bstr::BString;
use oxidized::explanation::Explanation;
use oxidized::message::Message;
use oxidized::pos::Pos;
use relative_path::Prefix;
use relative_path::RelativePath;

use super::*;
use crate::diagnostics::Diagnostic;
use crate::diagnostics;
use crate::server_env::FullCheckStatus;
use crate::server_env::InitEnv;
use crate::server_env::PrecheckedFilesStatus;
use crate::server_env::RecheckLoopStats;
use crate::user_diagnostic::Severity;

/// The prefixes of `Relative_path`, as the formatter tests set them (the
/// root is `/`), so that tests running together agree.
fn set_prefixes() {
    crate::relative_path::set_path_prefix(Prefix::Root, std::path::Path::new("/"));
}

fn path(name: &str) -> RelativePath {
    RelativePath::make(Prefix::Root, name.into())
}

fn pos_in(file: &str, line: usize, cols: std::ops::Range<usize>) -> Pos {
    let bol = line * 100;
    Pos::from_lnum_bol_offset(
        Arc::new(path(file)),
        (line, bol, bol + cols.start),
        (line, bol, bol + cols.end),
    )
}

fn diag(severity: Severity, code: isize, file: &str, line: usize, text: &str) -> Diagnostic {
    Diagnostic {
        severity,
        code,
        claim: Message(pos_in(file, line, 0..3), BString::from(text)),
        reasons: vec![],
        explanation: Explanation::Empty,
        quickfixes: vec![],
        custom_msgs: vec![],
        is_fixmed: false,
        function_pos: None,
    }
}

fn err(file: &str, line: usize, text: &str) -> Diagnostic {
    diag(Severity::Err, 4110, file, line, text)
}

/// Warn[12007] (`SketchyNullCheck`'s neighbour, a code that is a warning).
fn warn(file: &str, line: usize, text: &str) -> Diagnostic {
    diag(Severity::Warning { is_trusted: true }, 12007, file, line, text)
}

fn diagnostics(ds: Vec<Diagnostic>) -> diagnostics::T {
    let mut t = diagnostics::T::new();
    for d in ds {
        t.entry(d.claim.0.filename().clone()).or_default().push(d);
    }
    t
}

fn genv() -> Genv {
    Genv {
        options: crate::server_args::default_options("/"),
        config: crate::server_config::default_config(),
        local_config: crate::server_local_config_load::default(),
        notifier: crate::server_notifier::init_null(),
        num_workers: 1,
    }
}

/// An environment whose diagnostics are `ds`, and nothing else.
fn env_with(ds: Vec<Diagnostic>) -> Env {
    Env {
        ctx: Arc::new(
            crate::ctx::Ctx::new(
                std::path::Path::new("/"),
                oxidized::typechecker_options::TypecheckerOptions::default(),
            )
            .unwrap(),
        ),
        naming_table: crate::naming_table::empty(),
        deps_mode: crate::typing_deps_mode::T::InMemoryMode(None),
        diagnostics: diagnostics(ds),
        failed_naming: Default::default(),
        last_command_time: 0.,
        last_notifier_check_time: 0.,
        last_idle_job_time: 0.,
        disk_needs_parsing: Default::default(),
        clock: None,
        needs_phase2_redecl: Default::default(),
        needs_recheck: Default::default(),
        why_needs_server_type_check: (String::new(), String::new()),
        init_env: InitEnv {
            approach_name: String::new(),
            init_error: None,
            init_id: "INITID".to_string(),
            init_start_t: 0.,
            init_type: String::new(),
            why_needed_full_check: None,
            recheck_id: None,
            saved_state_revs_info: None,
            mergebase_warning_hashes: None,
            naming_table_manifold_path: None,
        },
        full_check_status: FullCheckStatus::FullCheckDone,
        prechecked_files: PrecheckedFilesStatus::PrecheckedFilesDisabled,
        changed_files: Default::default(),
        interrupt_handlers: std::sync::Arc::new(|_, _| vec![]),
        type_check_testing_hooks: None,
        nonpersistent_client_pending_command_needs_full_check: None,
        last_recheck_loop_stats: RecheckLoopStats::default(),
        last_recheck_loop_stats_for_actual_work: None,
    }
}

fn metadata() -> CmdMetadata {
    CmdMetadata {
        from: "test".to_string(),
        desc: "test".to_string(),
    }
}

fn filter(default_all: bool) -> filter_diagnostics::filter::T {
    filter_diagnostics::filter::make(default_all, vec![], vec![])
}

fn status(
    env: Env,
    is_stale: bool,
    max_errors: Option<isize>,
    error_filter: filter_diagnostics::filter::T,
) -> server_status::T {
    let (_env, res) = handle(
        &genv(),
        env,
        is_stale,
        &metadata(),
        T::Status {
            max_errors,
            error_filter,
        },
    );
    match res {
        CommandResult::Status(s) => s,
        _ => panic!("not a STATUS result"),
    }
}

fn claims(s: &server_status::T) -> Vec<String> {
    s.error_list
        .iter()
        .map(|d| {
            format!(
                "{}:{} {}",
                crate::pos::filename(&d.claim.0),
                crate::pos::line(&d.claim.0),
                d.claim.1
            )
        })
        .collect()
}

fn sample() -> Vec<Diagnostic> {
    vec![
        err("b.php", 3, "b3"),
        warn("a.php", 2, "a2w"),
        err("a.php", 5, "a5"),
        err("a.php", 1, "a1"),
        // A duplicate, which `sort_and_finalize` removes.
        err("a.php", 1, "a1"),
    ]
}

#[test]
fn status_sorts_dedups_and_filters_warnings_out_by_default() {
    set_prefixes();
    let s = status(env_with(sample()), false, None, filter(false));
    assert_eq!(claims(&s), vec!["/a.php:1 a1", "/a.php:5 a5", "/b.php:3 b3"]);
    assert_eq!(s.dropped_count, 0);
    assert_eq!(s.liveness, StatusLiveness::LiveStatus);
    assert_eq!(s.last_recheck_stats, None);
    assert_eq!(s.file_watcher_clock, None);
}

#[test]
fn status_with_all_warnings() {
    set_prefixes();
    let s = status(env_with(sample()), true, None, filter(true));
    // (`Diagnostics.compare_internal` orders by severity first: warnings
    // before errors.)
    assert_eq!(
        claims(&s),
        vec!["/a.php:2 a2w", "/a.php:1 a1", "/a.php:5 a5", "/b.php:3 b3"]
    );
    assert_eq!(s.liveness, StatusLiveness::StaleStatus);
}

#[test]
fn status_takes_max_errors_after_filtering() {
    set_prefixes();
    let s = status(env_with(sample()), false, Some(2), filter(true));
    assert_eq!(claims(&s), vec!["/a.php:2 a2w", "/a.php:1 a1"]);
    assert_eq!(s.dropped_count, 2);
    let s = status(env_with(sample()), false, Some(0), filter(false));
    assert_eq!(claims(&s), Vec::<String>::new());
    assert_eq!(s.dropped_count, 3);
    let s = status(env_with(sample()), false, Some(-1), filter(false));
    assert_eq!(s.dropped_count, 3);
    let s = status(env_with(sample()), false, Some(10), filter(false));
    assert_eq!(s.dropped_count, 0);
}

#[test]
fn status_drops_fixmed_diagnostics() {
    set_prefixes();
    let fixmed = Diagnostic {
        is_fixmed: true,
        ..err("c.php", 1, "c1")
    };
    let s = status(env_with(vec![fixmed, err("c.php", 2, "c2")]), false, None, filter(false));
    assert_eq!(claims(&s), vec!["/c.php:2 c2"]);
}

#[test]
fn status_reports_the_last_recheck_with_the_init_id() {
    set_prefixes();
    let mut env = env_with(vec![]);
    env.last_recheck_loop_stats_for_actual_work = Some(RecheckLoopStats {
        updates_stale: false,
        per_batch_telemetry: vec![
            telemetry::int_("b", 2, telemetry::create()),
            telemetry::int_("a", 1, telemetry::create()),
        ],
        total_changed_files_count: 3,
        total_rechecked_count: 4,
        last_iteration_start_time: 10.,
        duration: 1.5,
        rust_disk_provider_read: Default::default(),
        time_first_result: Some(10.25),
        recheck_id: "RID".to_string(),
        any_full_checks: true,
    });
    env.clock = Some(crate::server_notifier_types::Clock::Watchman("c:1".to_string()));
    let s = status(env, false, None, filter(false));
    assert_eq!(
        telemetry::to_string(None, s.last_recheck_stats.as_ref().unwrap()),
        r#"{"id":"RID","time":1.5,"rust_disk_provider_read":{"count":0,"duration_ms":0.0},"count":4,"total_changed_files_count":3,"per_batch":[{"a":1},{"b":2}],"updates_stale":false,"any_full_checks":true,"time_to_first_result_ms":250,"init_id":"INITID"}"#
    );
    assert_eq!(
        s.file_watcher_clock,
        Some(crate::server_notifier_types::Clock::Watchman("c:1".to_string()))
    );
}

#[test]
fn list_files_with_errors_lists_the_files_of_errors_once_in_order() {
    set_prefixes();
    let (_env, res) = handle(
        &genv(),
        env_with(vec![warn("w.php", 1, "w")].into_iter().chain(sample()).collect()),
        false,
        &metadata(),
        T::ListFilesWithErrors,
    );
    match res {
        CommandResult::ListFilesWithErrors(files) => {
            assert_eq!(files, vec!["/a.php".to_string(), "/b.php".to_string()])
        }
        _ => panic!("not a LIST_FILES_WITH_ERRORS result"),
    }
}

#[test]
fn check_liveness_stats_no_prechecked_and_dep_table_size() {
    set_prefixes();
    let (env, res) = handle(&genv(), env_with(sample()), false, &metadata(), T::CheckLiveness);
    assert!(matches!(res, CommandResult::CheckLiveness(())));
    let (env, res) = handle(&genv(), env, false, &metadata(), T::Stats);
    match res {
        CommandResult::Stats(stats) => assert_eq!(stats.gc_stat.heap_words, 0),
        _ => panic!("not a STATS result"),
    }
    let (env, res) = handle(&genv(), env, false, &metadata(), T::NoPrecheckedFiles);
    assert!(matches!(res, CommandResult::NoPrecheckedFiles(())));
    assert!(env.needs_recheck.is_empty());
    assert_eq!(env.full_check_status, FullCheckStatus::FullCheckDone);
    let (_env, res) = handle(&genv(), env, false, &metadata(), T::InMemoryDepTableSize);
    assert!(matches!(res, CommandResult::InMemoryDepTableSize(Ok(0))));
}

#[test]
fn pause_sets_full_check_paused() {
    set_prefixes();
    let (env, res) = handle(&genv(), env_with(vec![]), false, &metadata(), T::Pause);
    assert!(matches!(res, CommandResult::Pause(())));
    assert_eq!(env.full_check_status, FullCheckStatus::FullCheckPaused);
}

/// `Server_rage.go`: one item, the pids and the files that need parsing.
#[test]
fn rage() {
    set_prefixes();
    let (_, r) = handle(&genv(), env_with(vec![]), false, &metadata(), T::Rage);
    let CommandResult::Rage(items) = r else { panic!("RAGE") };
    assert_eq!(items.len(), 1);
    assert_eq!(items[0].title, "status");
    assert_eq!(
        items[0].data,
        format!(
            "hh_server pid={} ppid={}\ndisk_needs_parsing: \n",
            std::process::id(),
            std::os::unix::process::parent_id()
        )
    );
}

#[test]
fn the_filter_crosses_the_socket() {
    set_prefixes();
    let re = crate::rt::ocaml_str::regexp("sub/").unwrap();
    let f = filter_diagnostics::filter::make(
        false,
        vec![re],
        vec![
            filter_diagnostics::Switch::CodeOn(crate::error_codes::warning::T::SketchyEquality),
            filter_diagnostics::Switch::GeneratedFilesOn,
        ],
    );
    let cmd = T::Status {
        max_errors: Some(3),
        error_filter: f,
    };
    let bytes = crate::rt::protocol::wire::encode(&cmd);
    let back: T = crate::rt::protocol::wire::decode(&bytes).unwrap();
    assert_eq!(format!("{:?}", back), format!("{:?}", cmd));
}

// ~~ The stand-in daemon ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// A stand-in for the daemon, for comparing the real `hh_client` with the
/// OCaml's without the monitor and the server loop:
/// with `HH_STATUS_FAKE_ROOT=<root>` (and the client's `HH_TMPDIR`), checks
/// the root as `hh_server --check` does, takes its lock, binds its socket,
/// and answers every client with [`handle`] until one asks it to shut down.
/// Run with
/// `cargo test -p hh_wip8 --features server --lib server_rpc::tests::fake_server -- --ignored --exact`.
#[test]
#[ignore]
fn fake_server() {
    use crate::server_client_provider::server_end;
    let Ok(root) = std::env::var("HH_STATUS_FAKE_ROOT") else {
        return;
    };
    let root = std::fs::canonicalize(&root).unwrap();
    let root_s = root.to_str().unwrap().to_string();
    crate::server_progress::set_root(root_s.clone());
    let hhi_root = std::env::temp_dir().join("hh_status_fake_hhi");
    let found = crate::check::discover_root(&root, &[]).unwrap();
    // `check::check_root`, keeping the context (the position commands type
    // files with it).
    let crate::check::Root {
        root: found_root,
        ctx,
        paths,
        hhi_count,
        ..
    } = found;
    let mut stats = crate::check::Stats::default();
    crate::check::declare_files(&ctx, &paths, &mut stats);
    // (As the daemon after its init: the reverse naming table.)
    ctx.build_reverse_naming_table();
    crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, &found_root);
    crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Hhi, &hhi_root);
    crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Tmp, std::path::Path::new("/tmp"));
    let ctx = Arc::new(ctx);
    crate::hh_single_type_check::install(&ctx);
    let by_file = crate::check::check_files_typed_by_file(&ctx, &paths[hhi_count..], &mut stats, None);
    let diagnostics = crate::server_main::full_init_diagnostics(by_file);
    // (A command that panics consumes the environment: each command gets a
    // new one, with the diagnostics of the check.)
    let env = || Env {
        diagnostics: diagnostics.clone(),
        ctx: Arc::clone(&ctx),
        deps_mode: ctx.deps_mode.clone(),
        ..env_with(vec![])
    };
    let genv = Genv {
        options: crate::server_args::default_options(&root_s),
        // (As the daemon: `max 1 (nbr_procs / 2)`.)
        num_workers: std::cmp::max(
            1,
            std::thread::available_parallelism().map_or(1, |n| n.get()) as isize / 2,
        ),
        ..genv()
    };
    assert!(crate::lock::grab(&crate::server_files::lock_file(&root_s)));
    let listener = server_end::bind(&root_s);
    let server_specific_files = server_command_types::ServerSpecificFiles {
        server_finale_file: crate::server_files::server_finale_file(std::process::id() as isize),
    };
    crate::server_progress::write(None, Some(crate::server_progress::Disposition::DReady), "ready");
    // `HH_FAKE_STREAM=step,step,...`: the streaming errors that the daemon
    // writes (`errors.bin`, `Server_progress.ErrorsWrite`), step by step, on
    // a thread: `new` (`new_empty_file`, as at the start of a check, which
    // ends a file already there with `Restarted`), `report` (the diagnostics
    // of the check, as one batch), `complete`, `stop`
    // (`unlink_at_server_stop`), `sleep:<seconds>`, `wait:<file>` (until
    // the file exists). `HH_FAKE_CLOCK`: the clock of `new`.
    let streaming = std::env::var("HH_FAKE_STREAM").ok();
    if let Some(script) = streaming.clone() {
        use crate::server_progress::errors_write;
        crate::server_progress::enable_error_production(true);
        let diagnostics = diagnostics.clone();
        std::thread::spawn(move || {
            for step in script.split(',') {
                match step {
                    // (`HH_FAKE_CLOCK`: the watchman clock of the check, which
                    // the client compares with watchman's.)
                    "new" => errors_write::new_empty_file(
                        std::env::var("HH_FAKE_CLOCK")
                            .ok()
                            .map(crate::server_notifier_types::Clock::Watchman),
                        false,
                        (String::new(), String::new()),
                    ),
                    "report" => errors_write::report(&diagnostics),
                    "complete" => errors_write::complete(&crate::telemetry::create()),
                    "stop" => errors_write::unlink_at_server_stop(),
                    s if s.starts_with("sleep:") => {
                        std::thread::sleep(std::time::Duration::from_secs_f64(s[6..].parse().unwrap()))
                    }
                    s if s.starts_with("wait:") => {
                        while !std::path::Path::new(&s[5..]).exists() {
                            std::thread::sleep(std::time::Duration::from_millis(50))
                        }
                    }
                    s => panic!("HH_FAKE_STREAM: unknown step {}", s),
                }
                eprintln!("fake_server: stream step {} done", step);
            }
        });
    }
    eprintln!("fake_server: ready on {}", root_s);
    for conn in listener.incoming() {
        let Ok(conn) = conn else { continue };
        match server_end::ack_and_handoff_client(conn, false, &server_specific_files) {
            Ok(server_end::Handshake::Handoff(mut client)) => {
                if server_end::read_connection_type(&mut client).is_err() {
                    continue;
                }
                let Ok((metadata, cmd)) = server_end::read_client_msg(&mut client) else {
                    continue;
                };
                let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    handle(&genv, env(), false, &metadata, cmd)
                }));
                match res {
                    Ok((_env, response)) => {
                        let _ = server_end::send_response_to_client(&mut client, response);
                    }
                    // (The server loop drops the connection.)
                    Err(_) => {}
                }
            }
            Ok(server_end::Handshake::ShutDown(..)) => break,
            // (The monitor exits when it said it would.)
            Ok(server_end::Handshake::VersionMismatch {
                monitor_will_terminate: true,
                ..
            }) => break,
            Ok(server_end::Handshake::VersionMismatch { .. }) | Err(_) => {}
        }
    }
    if streaming.is_some() {
        crate::server_progress::errors_write::unlink_at_server_stop();
    }
    let _ = std::fs::remove_file(crate::server_files::socket_file(&root_s));
    crate::server_progress::try_delete();
}
