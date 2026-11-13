// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_main.ml`, as far as `hh_server --check` needs it.
//! See `hh/PORTING.md`.
//!
//! Only check mode is ported: [`run_once`] (`Server_main.run_once`), with
//! what it calls of `setup_server` ([`num_workers`], the log lines,
//! [`warn_on_non_opt_build`]), and `Program.run_once_and_exit`
//! ([`run_once_and_exit`]); and the daemon (SRV, plan §3.1): the recheck
//! loop ([`query_notifier`], [`recheck_until_no_changes_left`],
//! [`serve_one_iteration`]), the interrupt handlers, [`serve`], the
//! daemon's [`program_init`], [`setup_server`] and [`daemon_main`].
//!
//! `program_init` (the full initialisation: indexing, parsing, naming, then
//! `Server_init_common.defer_or_do_type_check`) is redesigned: the check is
//! the one of `hh check` (`crate::check`: declare every file, then
//! `Typing_check_service.process_file` on each file, with threads instead of
//! worker processes). What the OCaml decides is kept: which files are
//! checked, and the diagnostics of the environment in the order its merges
//! give them ([`full_init_diagnostics`]).

use std::time::Instant;

use crate::check;
use crate::check::FileDiagnostics;
use crate::diagnostics_state;
use crate::diagnostics_state::Format;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::hh_version;
use crate::path;
use crate::server_args;
use crate::server_config;
use crate::server_error;
use crate::server_local_config;
use crate::user_diagnostic;

/// `Sys_utils.nbr_procs`: the number of processors online.
fn nbr_procs() -> isize {
    // (`nproc ()` of `sys_utils_stubs.c`: `sysconf(_SC_NPROCESSORS_ONLN)`.)
    let n = unsafe { libc::sysconf(libc::_SC_NPROCESSORS_ONLN) };
    if n < 1 { 1 } else { n as isize }
}

/// `num_workers options local_config`: the number of threads that check.
///
/// The number of workers is set both in hh.conf and as an optional server
/// argument. If the two numbers given in argument and in hh.conf are
/// different, we always take the minimum of the two.
///
/// Without either: `max 1 (nbr_procs / 2)` ("the hardware we are running on
/// has only 1/2 actual CPUs, the rest are hyperthreads").
pub fn num_workers(
    options: &server_args::Options,
    local_config: &server_local_config::T,
) -> isize {
    let max_procs_opt = match (server_args::max_procs(options), local_config.max_workers) {
        (Some(a), Some(b)) => Some(if a == b {
            a
        } else {
            hh_logger::warn(
                None,
                None,
                "Warning: both an argument --max-procs and a local config for max workers are given. Choosing minimum of the two.",
            );
            a.min(b)
        }),
        (a, b) => a.or(b),
    };
    let nbr_procs = nbr_procs();
    match max_procs_opt {
        None => (nbr_procs / 2).max(1),
        Some(max_procs) => {
            if max_procs <= nbr_procs {
                // (`Server_worker.make ~nbr_procs:0` makes no workers, and
                // the master does the work: one thread.)
                max_procs.max(1)
            } else {
                hh_logger::warn(
                    None,
                    None,
                    "Warning: max workers is higher than the number of processors. Capping.",
                );
                nbr_procs
            }
        }
    }
}

/// `warn_on_non_opt_build options config`
fn warn_on_non_opt_build(options: &server_args::Options, config: &server_config::T) {
    if server_config::warn_on_non_opt_build(config) && !crate::build_id::is_build_optimized() {
        let msg = format!(
            "hh_server binary was built in \"{}\" mode, ",
            crate::build_id::build_mode()
        ) + "is running with Rust version of parser enabled, "
            + "and this repository's .hhconfig specifies warn_on_non_opt_build option. "
            + "Parsing with non-opt build will take significantly longer";
        if server_args::allow_non_opt_build(options) {
            hh_logger::log(&format!(
                "Warning: {}. Initializing anyway due to --allow-non-opt-build option.",
                msg
            ))
        } else {
            let msg = format!(
                "Error: {}. Recompile the server in opt or dbgo mode, or pass --allow-non-opt-build to continue anyway.",
                msg
            );
            hh_logger::log(&msg);
            exit::exit(
                Some(msg),
                None,
                None,
                exit_status::T::ServerNonOptBuildMode,
            )
        }
    }
}

/// `Unix.gethostname ()`
fn gethostname() -> String {
    let mut buf = [0u8; 256];
    let r = unsafe { libc::gethostname(buf.as_mut_ptr() as *mut libc::c_char, buf.len()) };
    if r != 0 {
        return "".to_string();
    }
    let len = buf.iter().position(|&c| c == 0).unwrap_or(buf.len());
    String::from_utf8_lossy(&buf[..len]).into_owned()
}

/// `Unix.gettimeofday ()`
fn gettimeofday() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0.0, |d| d.as_secs_f64())
}

/// The diagnostics of the environment after the full initialisation of
/// check mode, from those of each file checked (in the order of the files):
/// what the merges of the OCaml make of them.
///
/// - Each worker merges the diagnostics of each file it checks onto those it
///   has (`Typing_check_service.process_one_workitem`:
///   `Diagnostics.merge file_diagnostics diagnostics`);
/// - the master merges the result of each batch onto what it has
///   (`Typing_service_types.accumulate_job_output`), after
///   `Diagnostics.filter_out_mergebase_warnings` (the identity: there are
///   no mergebase warnings without a saved state);
/// - `Server_init_common.defer_or_do_type_check` merges the result onto the
///   diagnostics of the environment, which are empty
///   (`Server_init_common.validate_no_errors`).
///
/// `Diagnostics.merge` reverses the list of each file it merges, so the
/// diagnostics of a file come out in the reverse of the order they were
/// reported in. Here the files are merged as if one worker had checked them
/// all, in order, in one batch: for a file whose diagnostics come from the
/// check of one file only (the file itself), which is the case of every
/// diagnostic on Slack's code, that is what the OCaml gives whatever the
/// batches; when the checks of several files report diagnostics in a third
/// file, the OCaml's order depends on how the files were spread over the
/// workers, which nothing here can reproduce.
pub fn full_init_diagnostics(by_file: Vec<FileDiagnostics>) -> diagnostics_state::T {
    let mut worker = diagnostics_state::T::new();
    for file_diagnostics in by_file {
        worker = diagnostics_state::merge(file_diagnostics, worker);
    }
    let typing = diagnostics_state::merge(worker, diagnostics_state::T::new());
    diagnostics_state::merge(typing, diagnostics_state::T::new())
}

/// What the check-mode initialisation leaves: `env.diagnostics`.
pub struct Env {
    pub diagnostics: diagnostics_state::T,
}

/// `program_init genv env` in check mode, redesigned (see the module's
/// documentation): finds the files of the root, checks them on `num_workers`
/// threads, and logs each phase.
fn program_init_check_mode(
    options: &server_args::Options,
    config: &server_config::T,
    num_workers: isize,
    start: Instant,
    hhi_root: &str,
) -> Env {
    let fail = |e: anyhow::Error| -> ! {
        hh_logger::log(&format!("{:#}", e));
        exit::exit(
            None,
            None,
            None,
            exit_status::T::UncaughtException(crate::exception::wrap(format!("{:#}", e))),
        )
    };
    hh_logger::log(&format!("Checking with {} threads", num_workers));
    if let Err(e) = check::build_thread_pool(Some(num_workers as usize)) {
        fail(e)
    }
    let root = std::path::PathBuf::from(path::to_string(&server_args::root(options)));
    let t = gettimeofday();
    hh_logger::log("[progress] indexing");
    let root = match check::discover_files(
        root,
        start,
        server_config::typechecker_options(config),
        server_config::ignored_path_patterns(config),
    ) {
        Ok(root) => root,
        Err(e) => fail(e),
    };
    let files = root.paths.len() - root.hhi_count;
    let t = hh_logger::log_duration(
        None,
        None,
        &format!("indexing {} files ({} hhi files)", files, root.hhi_count),
        t,
    );
    hh_logger::log(&format!("Begin parsing, naming and type-checking {} files", files));
    let checked = match check::check_root(root, None, std::path::Path::new(hhi_root)) {
        Ok(checked) => checked,
        Err(e) => fail(e),
    };
    let stats = &checked.stats;
    hh_logger::log(&format!(
        "parsing declarations of {} files ({:.1} MB): {:.6}",
        files,
        stats.bytes as f64 / 1e6,
        stats.decl_time.as_secs_f64()
    ));
    hh_logger::log(&format!(
        "type-check {} files: {:.6}",
        stats.files,
        stats.check_time.as_secs_f64()
    ));
    let diagnostics = full_init_diagnostics(checked.diagnostics);
    let (mut errors, mut warnings) = (0, 0);
    for d in diagnostics.values().flatten() {
        match d.severity {
            user_diagnostic::Severity::Err => errors += 1,
            user_diagnostic::Severity::Warning { .. } => warnings += 1,
        }
    }
    hh_logger::log(&format!(
        "{} errors and {} warnings (before deduplication)",
        errors, warnings
    ));
    hh_logger::log_duration(None, None, "full init", t);
    Env { diagnostics }
}

/// `run_once options config local_config`
///
/// `hhi_root` is the directory of `Hhi.get_hhi_root ()`.
pub fn run_once(
    options: &server_args::Options,
    config: &server_config::T,
    local_config: &server_local_config::T,
    start: Instant,
    hhi_root: &str,
) -> ! {
    assert!(server_args::check_mode(options));
    hh_logger::log("Server_main.run_once starting");
    // `setup_server`
    let num_workers = num_workers(options, local_config);
    hh_logger::log(&format!("Version: {}", hh_version::version()));
    hh_logger::log(&format!("Hostname: {}", gethostname()));
    warn_on_non_opt_build(options, config);
    if local_config.use_saved_state {
        // (`resolve_init_approach` would load a saved state; the port has
        // none and does the full check, which gives the same diagnostics.)
        hh_logger::log("hh.conf asks for a saved state: not ported, doing a full init");
    }
    // The type-checking happens here
    let env = program_init_check_mode(options, config, num_workers, start, hhi_root);
    // Finish up by generating the output and the exit code
    hh_logger::log("Running in check mode");
    run_once_and_exit(options, env)
}

/// What `Program.run_once_and_exit` prints on `oc` of the diagnostics
/// `error_list`: the JSON with `output_json` (`--json`), the deduplicated
/// and sorted list otherwise.
pub fn print_error_list(
    oc: &mut dyn std::io::Write,
    output_json: bool,
    error_list: &[user_diagnostic::T<crate::pos::Absolute, crate::pos::Absolute>],
) {
    server_error::print_error_list(oc, None, output_json, Some(Format::Raw), error_list, None)
}

/// The status `Program.run_once_and_exit` exits with: 1 if there is an
/// error (a warning is not one), 32 instead with `--write-symbol-info`, 0
/// otherwise.
pub fn exit_code(options: &server_args::Options, has_errors: bool) -> i32 {
    if has_errors {
        if server_args::write_symbol_info(options).is_some() {
            32
        } else {
            1
        }
    } else {
        0
    }
}

/// `Program.run_once_and_exit genv env`
pub fn run_once_and_exit(options: &server_args::Options, env: Env) -> ! {
    // (`env.last_recheck_loop_stats_for_actual_work` is `None` after the
    // initialisation.)
    let has_errors = diagnostics_state::has_errors(None, &env.diagnostics);
    let error_list: Vec<_> = diagnostics_state::get_diagnostic_list(None, env.diagnostics)
        .iter()
        .map(user_diagnostic::to_absolute)
        .collect();
    {
        let stdout = std::io::stdout();
        let mut out = std::io::BufWriter::new(stdout.lock());
        print_error_list(&mut out, server_args::json_mode(options), &error_list);
    }
    // (`Worker_controller.force_quit_all ()`: there are no workers.)
    let error_code = exit_code(options, has_errors);
    // `exit` (`Stdlib.exit`: the standard channels are flushed).
    {
        use std::io::Write;
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
    }
    std::process::exit(error_code)
}

// ~~ The daemon (SRV, plan §3.1) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

use std::os::fd::RawFd;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use crate::client_command_handler;
use crate::connection_tracker::Key;
use crate::deferral_tracker;
use crate::hhi_root;
use crate::periodical;
use crate::pid_log;
use crate::random_id;
use crate::relative_path;
use crate::rt::client_provider;
use crate::rt::client_provider::Client;
use crate::rt::client_provider::ClientKind;
use crate::rt::client_provider::ClientProvider;
use crate::rt::client_provider::Handoff;
use crate::rt::client_provider::InFds;
use crate::rt::client_provider::SelectOutcome;
use crate::rt::notifier_watchman as watchman;
use crate::rt::ocaml_sys;
use crate::rt::ocaml_unix;
use crate::s_set;
use crate::server_env;
use crate::server_env::FullCheckStatus;
use crate::server_env::Genv;
use crate::server_env::RecheckLoopStats;
use crate::server_env::init_telemetry;
use crate::server_env::recheck_loop_stats;
use crate::server_env_build;
use crate::server_files;
use crate::server_idle;
use crate::server_init;
use crate::server_init_types::InitApproach;
use crate::server_notifier;
use crate::server_progress;
use crate::server_type_check;
use crate::server_utils;
use crate::server_utils::HandleCommandResult;
use crate::telemetry;
use crate::typing_check_service::InterruptResult;
use crate::typing_deps;

type RPSet = crate::relative_path::set::T;

/// `force_break_recheck_loop_for_test_ref`
#[allow(non_upper_case_globals)]
static force_break_recheck_loop_for_test_ref: AtomicBool = AtomicBool::new(false);

/// `force_break_recheck_loop_for_test`
pub fn force_break_recheck_loop_for_test(b: bool) {
    force_break_recheck_loop_for_test_ref.store(b, Ordering::SeqCst)
}

/// `Program` (the daemon's part: `run_once_and_exit` is the check mode's
/// [`run_once_and_exit`]).
pub mod program {
    use super::*;

    /// `Program.set_signals ()`
    pub fn set_signals() {
        // `Typing.debug_print_last_pos`: the position is per thread here;
        // each thread of the pool prints its own (after the file it is
        // checking), from a thread of its own so that the signal
        // dispatcher does not wait.
        ocaml_sys::set_signal(
            libc::SIGUSR1,
            ocaml_sys::SignalBehavior::SignalHandle(Arc::new(|_| {
                std::thread::spawn(|| {
                    rayon::broadcast(|_| crate::typing::prelude::debug_print_last_pos(()));
                });
            })),
        );
        ocaml_sys::set_signal(
            libc::SIGUSR2,
            ocaml_sys::SignalBehavior::SignalHandle(Arc::new(|_| {
                hh_logger::log("Got sigusr2 signal. Going to shut down.");
                exit::exit(
                    Some(
                        "Hh_server received a stop signal. This can happen from a large rebase/update"
                            .to_string(),
                    ),
                    None,
                    None,
                    exit_status::T::ServerShuttingDownDueToSigusr2,
                )
            })),
        );
        // this is to transform SIGPIPE in an exception. A SIGPIPE can happen when
        // someone C-c the client.
        ocaml_sys::set_signal(libc::SIGPIPE, ocaml_sys::SignalBehavior::SignalIgnore);
    }

    /// filter and relativize updated file paths
    /// (`exit_if_critical_update genv ~raw_updates`)
    pub fn exit_if_critical_update(genv: &Genv, raw_updates: &s_set::T) {
        let hhconfig_in_updates =
            raw_updates.contains(&relative_path::to_absolute(&server_config::repo_config_path));
        if hhconfig_in_updates {
            let (new_config, _) = match server_config::load(
                false,
                &server_args::from(&genv.options),
                &server_args::config(&genv.options),
            ) {
                Ok(configs) => configs,
                Err(e) => std::panic::panic_any(e),
            };
            if !server_config::is_compatible(&genv.config, &new_config) {
                hh_logger::log(&format!(
                    "{} changed in an incompatible way; please restart {}.\n",
                    relative_path::suffix(&server_config::repo_config_path),
                    crate::global_config::program_name
                ));
                // TODO: Notify the server monitor directly about this.
                exit::exit(None, None, None, exit_status::T::HhconfigChanged)
            }
        }
        let package_config_in_updates = raw_updates
            .contains(&relative_path::to_absolute(&crate::package_config::repo_config_path));
        if package_config_in_updates {
            hh_logger::log(&format!(
                "{} changed; please restart {}.\n",
                relative_path::suffix(&crate::package_config::repo_config_path),
                crate::global_config::program_name
            ));
            exit::exit(None, None, None, exit_status::T::PackageConfigChanged)
        }
    }
}

/// `finalize_init init_env typecheck_telemetry init_telemetry`
fn finalize_init(
    init_env: &server_env::InitEnv,
    typecheck_telemetry: telemetry::T,
    init_telemetry: &server_env::InitTelemetry,
) {
    // rest is just logging/telemetry
    let t_ = gettimeofday();
    let hash_telemetry = server_utils::log_and_get_sharedmem_load_telemetry();
    let t = telemetry::create();
    let t = telemetry::duration(None, init_env.init_start_t, None, t);
    let t = telemetry::object_("init", init_telemetry::get(init_telemetry), t);
    let t = telemetry::object_("typecheck", typecheck_telemetry, t);
    let t = telemetry::object_("hash", hash_telemetry, t);
    // (`Shared_mem.SMTelemetry.heap_size ()`: there is no shared heap.)
    let telemetry = telemetry::int_("heap_size", 0, t);
    hh_logger::log(&format!(
        "SERVER_IS_READY. Took {:.6} seconds to init. Telemetry:\n{}",
        t_ - init_env.init_start_t,
        telemetry::to_string(None, &telemetry)
    ));
}

/// The query kinds of [`query_notifier`] (`` [> `Async | `Skip | `Sync ] ``).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QueryKind {
    Async,
    Skip,
    Sync,
}

/// What the notifier raised that the OCaml does not catch: raised again
/// (a panic with the `Watchman` exception, which
/// `Server_utils.exit_on_exception` handles).
fn raise_watchman(e: watchman::Exn) -> ! {
    std::panic::panic_any(e)
}

/// [let (env, changes, new_clock, may_be_stale, telemetry) = query_notifier genv env query_kind start_time].
///
/// Query for changed files.
/// * [`Sync] -- a Watchman/Edenfs_watcher sync query, i.e. guarantees to have picked up all updates
///   up to the moment it was invoked.
/// * [`Async] -- picks up changes that  Watchman/Edenfs_watcher has pushed so far, but we don't
///   do a sync, so therefore there might be changes on disk that the file watcher will tell us about
///   in future.
/// * [`Skip] -- CARE! Despite its name, this also behaves much like [`Async].
///
/// The return value [may_be_stale] indicates whether the most recently returned result was not "sync".
pub fn query_notifier(
    genv: &Genv,
    env: server_env::Env,
    query_kind: QueryKind,
    start_time: f64,
) -> (
    server_env::Env,
    RPSet,
    Option<server_notifier::Clock>,
    bool,
    telemetry::T,
) {
    let telemetry = telemetry::duration(Some("start"), start_time, None, telemetry::create());
    let (env, (raw_updates, clock, telemetry)) = match query_kind {
        QueryKind::Sync => (
            env,
            match server_notifier::get_changes_sync(&genv.notifier, telemetry.clone()) {
                Ok((changes, clock, telemetry)) => {
                    (server_notifier::Changes::SyncChanges(changes), clock, telemetry)
                }
                Err(watchman::Exn::Timeout) => {
                    (server_notifier::Changes::Unavailable, None, telemetry)
                }
                Err(e) => raise_watchman(e),
            },
        ),
        QueryKind::Async => (
            server_env::Env {
                last_notifier_check_time: start_time,
                ..env
            },
            match server_notifier::get_changes_async(&genv.notifier, telemetry) {
                Ok(r) => r,
                Err(e) => raise_watchman(e),
            },
        ),
        QueryKind::Skip => (
            env,
            (
                server_notifier::Changes::AsyncChanges(s_set::T::new()),
                None,
                telemetry,
            ),
        ),
    };
    let telemetry = telemetry::duration(Some("notified"), start_time, None, telemetry);
    let unpack_updates = |changes: server_notifier::Changes| match changes {
        server_notifier::Changes::Unavailable => (true, s_set::T::new()),
        server_notifier::Changes::AsyncChanges(updates) => (true, updates),
        // We get SyncChanges either
        // a) due to a call to to  ServerNotifier.get_changes_sync  (see match on query_kind above) or
        // b) if we used ServerNotifier.get_changes_async, but the latter actually received
        //    changes in a synchronous fashion,
        // In any case, the updates are up to date, meaning that the staleness flag is set to false
        server_notifier::Changes::SyncChanges(updates) => (false, updates),
    };
    let (updates_stale, raw_updates) = unpack_updates(raw_updates);
    // TODO(T226505256) When using Edenfs_watcher, we allow terminating
    // pump_async_updates if we get an empty raw_updates set from
    // ServerNotifier.get_changes_async.
    let stop_pumping_on_empty_updates = genv.local_config.edenfs_file_watcher.enabled;
    let (raw_updates, clock, pump_iterations, telemetry) = {
        let mut acc = raw_updates;
        let mut acc_clock = clock;
        let mut iteration = 0isize;
        let mut telemetry = telemetry;
        loop {
            match server_notifier::maybe_changes_available(&genv.notifier) {
                Some(true) => {
                    let (changes, clock, t) =
                        match server_notifier::get_changes_async(&genv.notifier, telemetry) {
                            Ok(r) => r,
                            Err(e) => raise_watchman(e),
                        };
                    telemetry = t;
                    let (_, raw_updates) = unpack_updates(changes);
                    if stop_pumping_on_empty_updates && raw_updates.is_empty() {
                        break (acc, clock, iteration + 1, telemetry);
                    }
                    acc = acc.union(raw_updates);
                    acc_clock = clock;
                    iteration += 1;
                }
                _ => break (acc, acc_clock, iteration, telemetry),
            }
        }
    };
    let telemetry = telemetry::duration(Some("pumped"), start_time, None, telemetry);
    let telemetry = telemetry::int_("pump_iterations", pump_iterations, telemetry);
    program::exit_if_critical_update(genv, &raw_updates);
    let updates = crate::find_utils::post_file_watcher_filter_from_fully_qualified_raw_updates(
        &server_args::root(&genv.options),
        &raw_updates,
    );
    // CARE! For streaming-errors to work in clientCheckStatus.ml, the test
    // which hh_server uses to determine "is there a non-empty set of changes which prompt me
    // to start a new check" must be at least as strict as the one in clientCheckStatus.
    let telemetry = telemetry::duration(Some("processed"), start_time, None, telemetry);
    let telemetry = telemetry::int_("raw_updates", raw_updates.len() as isize, telemetry);
    let telemetry = telemetry::int_("updates", updates.len() as isize, telemetry);
    // (`Hack_event_logger.notifier_returned`: a no-op.)
    (env, updates, clock, updates_stale, telemetry)
}

/// `update_stats_after_recheck stats check_stats ~telemetry ~start_time`
fn update_stats_after_recheck(
    stats: RecheckLoopStats,
    check_stats: &server_type_check::CheckStats,
    telemetry: telemetry::T,
    start_time: f64,
) -> RecheckLoopStats {
    let RecheckLoopStats {
        total_changed_files_count,
        mut per_batch_telemetry,
        total_rechecked_count,
        updates_stale,
        recheck_id,
        last_iteration_start_time: _,
        duration,
        time_first_result: _,
        any_full_checks: _,
    } = stats;
    per_batch_telemetry.insert(0, telemetry);
    RecheckLoopStats {
        total_changed_files_count: total_changed_files_count + check_stats.reparse_count,
        per_batch_telemetry,
        total_rechecked_count: total_rechecked_count + check_stats.total_rechecked_count,
        updates_stale,
        recheck_id,
        last_iteration_start_time: start_time,
        duration: duration + (gettimeofday() - start_time),
        time_first_result: check_stats.time_first_result,
        any_full_checks: true,
    }
}

fn is_select_new(s: &SelectOutcome) -> bool {
    matches!(s, SelectOutcome::SelectNew(_))
}

/// This function loops until it has processed all outstanding changes.
///
/// One reason for doing this is so that, if a client makes a request,
/// then we can process all outstanding changes prior to handling that request.
/// That way the client will get an up-to-date answer.
///
/// Another reason is to get meaningful logging in case of file watcher events.
/// When a rebase occurs, Watchman/dfind/Edenfs_watcher takes a while to give us the full list
/// of updates, and it often comes in batches. To get an accurate measurement
/// of rebase time, we use the heuristic that any changes that come in
/// right after one rechecking round finishes to be part of the same
/// rebase, and we don't log the recheck_end event until the update list
/// is no longer getting populated.
///
/// The above doesn't apply in presence of interruptions / cancellations -
/// it's possible for client to request current recheck to be stopped.
/// (`recheck_until_no_changes_left stats genv env select_outcome`; the
/// provider is that of the pending client, which may be pinged.)
pub fn recheck_until_no_changes_left(
    stats: RecheckLoopStats,
    genv: &Genv,
    env: server_env::Env,
    select_outcome: &SelectOutcome,
    cp: &mut dyn ClientProvider,
) -> (RecheckLoopStats, server_env::Env) {
    let mut stats = stats;
    let mut env = env;
    loop {
        let start_time = gettimeofday();
        // this is telemetry for the current batch, i.e. iteration:
        let telemetry = telemetry::float_("start_time", start_time, telemetry::create());
        // When a new client connects, we use the synchronous notifier.
        // This is to get synchronous file system changes when invoking
        // hh_client in terminal.
        //
        // CARE! The [`Skip] option doesn't in fact skip. It will still
        // retrieve queued-up file watcher updates.
        let query_kind = if is_select_new(select_outcome) {
            QueryKind::Sync
        } else if start_time - env.last_notifier_check_time > 0.5 {
            QueryKind::Async
        } else {
            QueryKind::Skip
        };
        let (env_, updates, clock, updates_stale, query_telemetry) =
            query_notifier(genv, env, query_kind, start_time);
        env = env_;
        let telemetry = telemetry::object_("query", query_telemetry, telemetry);
        let telemetry = telemetry::duration(Some("query_done"), start_time, None, telemetry);
        stats.updates_stale = updates_stale;
        // saving any file is our trigger to start full recheck
        if clock.is_some() && clock != env.clock {
            hh_logger::log(&format!(
                "Recheck at watchclock {}",
                server_env::show_clock(clock.as_ref())
            ));
            env.clock = clock;
        }
        // We need to union with the existing env.disk_needs_parsing here and use that to decide whether
        // to start another type-check: After a complete type-check (i.e., env.needs_recheck is empty,
        // and env.full_check_status is Full_check_done), we may have that env.disk_needs_parsing is
        // non-empty due to the interrupt handlers adding files there.
        // (Read below, after `updates` is consumed.)
        let updates_is_empty = updates.is_empty();
        let disk_needs_parsing = updates.union(env.disk_needs_parsing.clone());
        if !disk_needs_parsing.is_empty() {
            let full_check_status = match env.full_check_status {
                FullCheckStatus::FullCheckPaused => FullCheckStatus::FullCheckPaused,
                FullCheckStatus::FullCheckNeeded
                | FullCheckStatus::FullCheckStarted
                | FullCheckStatus::FullCheckDone => FullCheckStatus::FullCheckStarted,
            };
            env.disk_needs_parsing = disk_needs_parsing;
            env.full_check_status = full_check_status;
        }
        let telemetry = telemetry::duration(Some("got_updates"), start_time, None, telemetry);
        // If the client went away (e.g. user pressed Ctrl+C while waiting for the typecheck),
        // let's clean up now.
        if server_env::is_full_check_needed(env.full_check_status)
            && start_time - env.last_command_time > 5.0
        {
            if let Some((_command, _reason, client)) =
                env.nonpersistent_client_pending_command_needs_full_check.as_mut()
            {
                if cp.ping(client).is_err() {
                    cp.shutdown_client(client);
                    env.nonpersistent_client_pending_command_needs_full_check = None;
                }
            }
        }
        if server_env::is_full_check_needed(env.full_check_status)
            && start_time > env.last_command_time + 5.0
        {
            hh_logger::log("Restarting full check after 5.0s");
            env.full_check_status = FullCheckStatus::FullCheckStarted;
        }
        // Same as above, but for persistent clients
        let telemetry = telemetry::duration(Some("sorted_out_client"), start_time, None, telemetry);
        match env.full_check_status {
            FullCheckStatus::FullCheckPaused => {
                if !updates_is_empty {
                    hh_logger::log_with(
                        Some(hh_logger::level::T::Debug),
                        None,
                        &format!(
                            "Queued file changes while paused: {} files awaiting parsing",
                            env.disk_needs_parsing.len()
                        ),
                    )
                }
            }
            FullCheckStatus::FullCheckNeeded
            | FullCheckStatus::FullCheckStarted
            | FullCheckStatus::FullCheckDone => {}
        }
        // We have some new, or previously un-processed updates
        let full_check = server_env::is_full_check_started(env.full_check_status);
        let telemetry = telemetry::bool_("full_check", full_check, telemetry);
        let telemetry =
            telemetry::duration(Some("figured_check_kind"), start_time, None, telemetry);
        if !full_check {
            let telemetry = telemetry::string_(None, "check_kind", "None", telemetry);
            stats.per_batch_telemetry.insert(0, telemetry);
            return (stats, env);
        }
        let check_kind_str = "Full_check";
        let needed_full_init = env.init_env.why_needed_full_check.clone();
        // HERE'S WHERE WE DO THE HEAVY WORK! **
        let telemetry = telemetry::string_(None, "check_kind", check_kind_str, telemetry);
        let telemetry =
            telemetry::duration(Some("type_check_start"), start_time, None, telemetry);
        // (`Cgroup_profiler.step_group check_kind_str ~log:true`: no cgroup
        // profiling.)
        let (env_, check_stats, type_check_telemetry) = type_check(genv, env, start_time);
        env = env_;
        let telemetry = telemetry::object_("type_check", type_check_telemetry, telemetry);
        let telemetry = telemetry::duration(Some("type_check_end"), start_time, None, telemetry);
        // END OF HEAVY WORK
        // Final telemetry and cleanup...
        if let (Some(needed_full_init), None) =
            (&needed_full_init, &env.init_env.why_needed_full_check)
        {
            finalize_init(&env.init_env, telemetry.clone(), needed_full_init)
        }
        let telemetry =
            telemetry::duration(Some("finalized_and_touched"), start_time, None, telemetry);
        stats = update_stats_after_recheck(stats, &check_stats, telemetry, start_time);
        // Tests have ability to opt-out of batching completely.
        if force_break_recheck_loop_for_test_ref.load(Ordering::SeqCst) {
            return (stats, env);
        }
    }
}

#[cfg(test)]
type TypeCheckHook = Box<
    dyn FnMut(&Genv, server_env::Env, f64) -> (server_env::Env, server_type_check::CheckStats, telemetry::T),
>;

#[cfg(test)]
thread_local! {
    /// What the tests of this module put instead of `Server_type_check.type_check`.
    static TYPE_CHECK_FOR_TEST: std::cell::RefCell<Option<TypeCheckHook>> =
        const { std::cell::RefCell::new(None) };
}

/// `Server_type_check.type_check genv env start_time`
fn type_check(
    genv: &Genv,
    env: server_env::Env,
    start_time: f64,
) -> (server_env::Env, server_type_check::CheckStats, telemetry::T) {
    #[cfg(test)]
    {
        if let Some(mut f) = TYPE_CHECK_FOR_TEST.with(|h| h.borrow_mut().take()) {
            let r = f(genv, env, start_time);
            TYPE_CHECK_FOR_TEST.with(|h| *h.borrow_mut() = Some(f));
            return r;
        }
    }
    server_type_check::type_check(genv, env, start_time)
}

/// `new_serve_iteration_id ()`
fn new_serve_iteration_id() -> String {
    random_id::short_string()
}

/// This is safe to run only in the main loop, when workers are not doing
/// anything. (`main_loop_command_handler client result`)
fn main_loop_command_handler(client: Client, result: HandleCommandResult) -> server_env::Env {
    match result {
        HandleCommandResult::Done(env) => env,
        HandleCommandResult::NeedsFullRecheck {
            mut env,
            finish_command_handling,
            reason,
        } => {
            // We should not accept any new clients until this is cleared
            assert!(env.nonpersistent_client_pending_command_needs_full_check.is_none());
            env.nonpersistent_client_pending_command_needs_full_check =
                Some((finish_command_handling, reason, client));
            env
        }
    }
}

/// `generate_and_update_recheck_id env`
fn generate_and_update_recheck_id(mut env: server_env::Env) -> (server_env::Env, String) {
    let recheck_id = new_serve_iteration_id();
    env.init_env.recheck_id = Some(recheck_id.clone());
    (env, recheck_id)
}

/// `idle_if_no_client env waiting_client`
fn idle_if_no_client(env: server_env::Env, waiting_client: &SelectOutcome) -> server_env::Env {
    match waiting_client {
        SelectOutcome::SelectNothing
        | SelectOutcome::SelectException(_)
        | SelectOutcome::NotSelectingDeferring(_) => {
            // (`Shared_mem.GC.collect `aggressive`, with the rechecked
            // stats for its logging: there is no shared memory.)
            let t = gettimeofday();
            if t - env.last_idle_job_time > 0.5 {
                let mut env = server_idle::go(env);
                env.last_idle_job_time = t;
                env
            } else {
                env
            }
        }
        SelectOutcome::SelectNew(_) => env,
    }
}

/// `Diagnostics.as_telemetry_summary`
fn diagnostics_as_telemetry_summary(diagnostics: &diagnostics_state::T) -> telemetry::T {
    let mut count = 0;
    let mut warning_count = 0;
    let mut codes = std::collections::BTreeSet::new();
    let mut codes_done = false;
    for d in diagnostics.values().flatten().filter(|d| !d.is_fixmed) {
        count += 1;
        match d.severity {
            user_diagnostic::Severity::Warning { .. } => warning_count += 1,
            user_diagnostic::Severity::Err => {
                // This ignores warnings (`first_n_distinct_error_codes ~n:5`).
                if !codes_done {
                    codes.insert(d.code);
                    if codes.len() >= 5 {
                        codes_done = true;
                    }
                }
            }
        }
    }
    let t = telemetry::create();
    let t = telemetry::int_("count", count, t);
    let t = telemetry::int_("warning_count", warning_count, t);
    let codes: Vec<isize> = codes.into_iter().collect();
    telemetry::int_list(None, "first_5_distinct_error_codes", &codes, t)
}

/// `log_recheck_end stats ~diagnostics`
fn log_recheck_end(stats: &RecheckLoopStats, diagnostics: &diagnostics_state::T) {
    let telemetry = telemetry::object_(
        "errors",
        diagnostics_as_telemetry_summary(diagnostics),
        recheck_loop_stats::to_user_telemetry(stats),
    );
    // (`Hack_event_logger.recheck_end`: a no-op.)
    hh_logger::log(&format!(
        "RECHECK_END (recheck_id {}):\n{}",
        stats.recheck_id,
        telemetry::to_string(None, &telemetry)
    ));
}

/// `exit_if_parent_dead ()`
fn exit_if_parent_dead() {
    // Cross-platform compatible way; parent PID becomes 1 when parent dies.
    // SAFETY: `getppid` has no preconditions.
    if unsafe { libc::getppid() } == 1 {
        hh_logger::log("Server's parent has died; exiting.\n");
        exit::exit(None, None, None, exit_status::T::LostParentMonitor)
    }
}

/// `serve_one_iteration genv env client_provider`
pub fn serve_one_iteration(
    genv: &Genv,
    env: server_env::Env,
    cp: &mut dyn ClientProvider,
) -> server_env::Env {
    let (env, recheck_id) = generate_and_update_recheck_id(env);
    exit_if_parent_dead();
    let admission_decision =
        deferral_tracker::should_accept_client_connection(&genv.local_config, &genv.notifier);
    let acceptable_new_client_kind = {
        let has_default_client_pending = env
            .nonpersistent_client_pending_command_needs_full_check
            .is_some();
        match (&admission_decision, has_default_client_pending) {
            // If we are already blocked on some client, do not accept more of them.
            // Other clients (that connect through priority pipe, or persistent clients)
            // can still be handled - unless deferral blocks admission, where we want to
            // stop accepting any new clients, with the exception of forced ones.
            (deferral_tracker::Decision::Ok, true) => Some(ClientKind::Priority),
            (deferral_tracker::Decision::Ok, false) => Some(ClientKind::Any),
            (deferral_tracker::Decision::DeferredBy(_), true) => None,
            (deferral_tracker::Decision::DeferredBy(_), false) => {
                Some(ClientKind::ForceDormantStartOnly)
            }
        }
    };
    let selected_client = match acceptable_new_client_kind {
        None => SelectOutcome::SelectNothing,
        Some(client_kind) => cp.sleep_and_check(genv.local_config.idle_gc_slice, client_kind),
    };
    let selected_client = match (admission_decision, selected_client) {
        (deferral_tracker::Decision::DeferredBy(states), SelectOutcome::SelectNothing) => {
            SelectOutcome::NotSelectingDeferring(states)
        }
        (_, selected_client) => selected_client,
    };
    let mut env = env;
    match &selected_client {
        SelectOutcome::SelectNew(_) => match env.full_check_status {
            FullCheckStatus::FullCheckPaused => {
                // We can unconditionally switch to [Full_check_done] here: The invariant for
                // [Full_check_paused] tells us that [env.needs_recheck] is empty.
                // [recheck_until_no_changes_left] will switch to [Full_check_started] later if
                // [env.disk_needs_parsing] is non-empty.
                env.full_check_status = FullCheckStatus::FullCheckDone
            }
            FullCheckStatus::FullCheckNeeded
            | FullCheckStatus::FullCheckStarted
            | FullCheckStatus::FullCheckDone => {}
        },
        SelectOutcome::SelectNothing
        | SelectOutcome::SelectException(_)
        | SelectOutcome::NotSelectingDeferring(_) => {}
    }

    // Server_progress: By updating status now at the start of the serve_one_iteration,
    // it means there's no obligation on the "doing work" part of the previous
    // iteration to clean up its own status-reporting once done.
    //
    // By the same token, we will be writing "ready" once every 0.1s to the status file.
    // Think of it as a heartbeat!
    match &selected_client {
        SelectOutcome::SelectNothing | SelectOutcome::SelectException(_) => {
            // There's some subtle IDE behavior, described in [ServerCommand.handle]
            // and [Server_main.recheck_until_no_changes_left]... If an EDIT was received
            // over the persistent connection, then we won't resume typechecking
            // until either a file-save comes in or 5.0s has elapsed.
            let (disposition, msg) = match env.full_check_status {
                FullCheckStatus::FullCheckNeeded => {
                    (server_progress::Disposition::DWorking, "will resume")
                }
                FullCheckStatus::FullCheckStarted => {
                    (server_progress::Disposition::DWorking, "typechecking")
                }
                FullCheckStatus::FullCheckDone => (server_progress::Disposition::DReady, "ready"),
                FullCheckStatus::FullCheckPaused => (
                    server_progress::Disposition::DReady,
                    "paused until the next client request (e.g., hh --stats)",
                ),
            };
            server_progress::write(Some(false), Some(disposition), msg)
        }
        SelectOutcome::NotSelectingDeferring(states) => server_progress::write(
            Some(false),
            None,
            &format!("waiting for {}", states.join(", ")),
        ),
        SelectOutcome::SelectNew(_) => server_progress::write(Some(false), None, "working"),
    }
    let env = idle_if_no_client(env, &selected_client);
    // (`Hack_event_logger.with_id ~stage recheck_id`: a no-op.)
    let _ = &recheck_id;
    // We'll first do "recheck_until_no_changes_left" to handle all outstanding changes, so that
    // after that we'll be able to give an up-to-date answer to the client.
    // Except: this might be stopped early in some cases, e.g. IDE checks.
    let t_start_recheck = gettimeofday();
    let (stats, env) = recheck_until_no_changes_left(
        recheck_loop_stats::empty(&recheck_id),
        genv,
        env,
        &selected_client,
        cp,
    );
    let t_done_recheck = gettimeofday();
    let t_sent_diagnostics = gettimeofday();
    let stats = recheck_loop_stats::record_result_sent_ts(stats, Some(t_sent_diagnostics));
    let did_work = stats.total_rechecked_count > 0;
    let mut env = env;
    if did_work {
        env.last_recheck_loop_stats_for_actual_work = Some(stats.clone());
    }
    env.last_recheck_loop_stats = stats;
    if did_work {
        log_recheck_end(&env.last_recheck_loop_stats, &env.diagnostics);
    }
    let env = match selected_client {
        SelectOutcome::SelectNothing
        | SelectOutcome::SelectException(_)
        | SelectOutcome::NotSelectingDeferring(_) => env,
        SelectOutcome::SelectNew(Handoff {
            mut client,
            m2s_sequence_number,
        }) => {
            hh_logger::log(&format!(
                "Serving new client obtained from monitor handoff #{}",
                m2s_sequence_number
            ));
            // client here is the new client (not the existing persistent client)
            // whose request we're going to handle.
            cp.track(
                &mut client,
                Key::ServerStartRecheck,
                Some(t_start_recheck),
                None,
                None,
                None,
            );
            cp.track(
                &mut client,
                Key::ServerDoneRecheck,
                Some(t_done_recheck),
                None,
                None,
                None,
            );
            cp.track(
                &mut client,
                Key::ServerSentDiagnostics,
                Some(t_sent_diagnostics),
                None,
                None,
                None,
            );
            // (The OCaml catches any exception here, "HANDLE_CONNECTION_EXCEPTION(outer)
            // [ignoring request]": the errors of the client are handled inside
            // `Client_command_handler`; a panic here is a bug, which ends the
            // server.)
            let result = client_command_handler::handle_client_command_or_persistent_connection(
                genv,
                env,
                cp,
                &mut client,
            );
            // (`Hack_event_logger.handled_connection`: a no-op.)
            main_loop_command_handler(client, result)
        }
    };
    let mut env = env;
    if server_env::is_full_check_done(env.full_check_status) {
        if let Some((f, _reason, mut client)) = env
            .nonpersistent_client_pending_command_needs_full_check
            .take()
        {
            env = f(genv, cp, &mut client, env);
            env.nonpersistent_client_pending_command_needs_full_check = None;
        }
    }
    env
}

/// `Unix.localtime timestamp`: (hour, minute, second).
fn localtime_hms(timestamp: f64) -> (i32, i32, i32) {
    let t = timestamp as libc::time_t;
    // SAFETY: `tm` is written by `localtime_r` before it is read.
    unsafe {
        let mut tm: libc::tm = std::mem::zeroed();
        libc::localtime_r(&t, &mut tm);
        (tm.tm_hour, tm.tm_min, tm.tm_sec)
    }
}

/// This synthesizes a [Multi_threaded_call.Cancel] in the event that we want
/// a typecheck cancelled due to files changing on disk. It constructs the
/// human-readable [user_message] and also [log_message] appropriately.
pub fn cancel_due_to_file_changes(
    updates: &RPSet,
    clock: Option<&server_notifier::Clock>,
) -> InterruptResult {
    assert!(!updates.is_empty());
    let size = updates.len();
    let mut examples: Vec<String> = updates.iter().take(5).map(relative_path::suffix).collect();
    if size > 5 {
        examples.push("...".to_string());
    }
    let timestamp = gettimeofday();
    let (h, m, s) = localtime_hms(timestamp);
    InterruptResult::Cancel {
        user_message: format!(
            "Files have changed on disk! [{:02}:{:02}:{:02}] {}",
            h, m, s, examples[0]
        ),
        log_message: format!(
            "file change interrupt handler at clock {}. {} files changed. [{}]",
            server_env::show_clock(clock),
            updates.len(),
            examples.join(",")
        ),
        timestamp,
    }
}

/// `file_changes_interrupt_handler genv`
pub fn file_changes_interrupt_handler<'a>(genv: &'a Genv) -> server_env::InterruptHandler<'a> {
    Box::new(move |env: server_env::Env| {
        let start_time = gettimeofday();
        let (env, updates, clock, updates_stale, _telemetry) =
            query_notifier(genv, env, QueryKind::Async, start_time);
        // Async updates can always be stale, so we don't care
        let _ = updates_stale;
        let size = updates.len();
        if size > 0 {
            hh_logger::log(&format!(
                "Interrupted by file watcher message: {} files changed at watchclock {}",
                size,
                server_env::show_clock(clock.as_ref())
            ));
            let cancel = cancel_due_to_file_changes(&updates, clock.as_ref());
            (
                server_env::Env {
                    disk_needs_parsing: env.disk_needs_parsing.clone().union(updates),
                    clock,
                    ..env
                },
                cancel,
            )
        } else {
            (env, InterruptResult::Continue)
        }
    })
}

/// The provider the priority interrupt handler uses (the OCaml's closure
/// shares the server's).
pub type SharedProvider = Arc<Mutex<Box<dyn ClientProvider + Send>>>;

/// Handler for events on the priority socket, which is used for priority commands which
/// must be served immediately. (`priority_client_interrupt_handler genv
/// client_provider`)
pub fn priority_client_interrupt_handler<'a>(
    genv: &'a Genv,
    client_provider: SharedProvider,
) -> server_env::InterruptHandler<'a> {
    Box::new(move |env: server_env::Env| {
        let t = gettimeofday();
        hh_logger::log("Handling message on priority socket.");
        match deferral_tracker::should_accept_client_connection(&genv.local_config, &genv.notifier)
        {
            deferral_tracker::Decision::DeferredBy(states) => {
                hh_logger::log(&format!(
                    "Won't handle client message: waiting for {}.",
                    states.join(", ")
                ));
                (env, InterruptResult::Continue)
            }
            deferral_tracker::Decision::Ok => {
                // For non-persistent clients that don't synchronize file contents, users
                // expect that a query they do immediately after saving a file will reflect
                // this file contents. Async notifications are not always fast enough to
                // guarantee it, so we need an additional sync query before accepting such
                // client
                let (env, updates, clock, _updates_stale, _telemetry) =
                    query_notifier(genv, env, QueryKind::Sync, t);
                let n_updates = updates.len();
                if n_updates > 0 {
                    hh_logger::log(&format!(
                        "Interrupted by file watcher sync query: {} files changed at watchclock {}",
                        n_updates,
                        server_env::show_clock(clock.as_ref())
                    ));
                    let cancel = cancel_due_to_file_changes(&updates, clock.as_ref());
                    (
                        server_env::Env {
                            disk_needs_parsing: env.disk_needs_parsing.clone().union(updates),
                            clock,
                            ..env
                        },
                        cancel,
                    )
                } else {
                    let idle_gc_slice = genv.local_config.idle_gc_slice;
                    let mut guard = client_provider.lock().unwrap_or_else(|e| e.into_inner());
                    let cp: &mut dyn ClientProvider = &mut **guard;
                    let select_outcome = cp.sleep_and_check(idle_gc_slice, ClientKind::Priority);
                    let env = match select_outcome {
                        SelectOutcome::SelectNothing => {
                            // This is possible because client might have gone away during
                            // sleep_and_check.
                            hh_logger::log("Client went away.");
                            env
                        }
                        SelectOutcome::SelectException(e) => {
                            hh_logger::log(&format!(
                                "Exception during client FD select: {}",
                                crate::exception::get_ctor_string(&e)
                            ));
                            env
                        }
                        SelectOutcome::NotSelectingDeferring(_) => env,
                        SelectOutcome::SelectNew(Handoff {
                            mut client,
                            m2s_sequence_number,
                        }) => {
                            hh_logger::log(&format!(
                                "Serving new client obtained from monitor handoff #{}",
                                m2s_sequence_number
                            ));
                            match client_command_handler::handle_client_command_or_persistent_connection(
                                genv,
                                env,
                                cp,
                                &mut client,
                            ) {
                                HandleCommandResult::NeedsFullRecheck { reason, .. } => panic!(
                                    "unexpected command needing full recheck in priority channel: {}",
                                    reason
                                ),
                                HandleCommandResult::Done(env) => env,
                            }
                        }
                    };
                    (env, InterruptResult::Continue)
                }
            }
        }
    })
}

/// `setup_interrupts env client_provider`
pub fn setup_interrupts(
    mut env: server_env::Env,
    client_provider: &dyn ClientProvider,
) -> server_env::Env {
    let priority_fd = client_provider.priority_fd();
    let shared: SharedProvider = Arc::new(Mutex::new(client_provider.clone_provider()));
    env.interrupt_handlers = Arc::new(move |genv: &Genv, _env: &server_env::Env| {
        let server_local_config::T {
            interrupt_on_file_changes,
            interrupt_on_client,
            ..
        } = genv.local_config;
        let mut handlers: Vec<(RawFd, server_env::InterruptHandler<'_>)> = vec![];
        match server_notifier::notification_fd(&genv.notifier) {
            Some(fd) if interrupt_on_file_changes => {
                handlers.insert(0, (fd, file_changes_interrupt_handler(genv)))
            }
            _ => {}
        }
        match priority_fd {
            Some(fd) if interrupt_on_client => handlers.insert(
                0,
                (
                    fd,
                    priority_client_interrupt_handler(genv, Arc::clone(&shared)),
                ),
            ),
            _ => {}
        }
        handlers
    });
    env
}

/// `serve genv env in_fds`
pub fn serve(genv: Genv, env: server_env::Env, in_fds: InFds) -> ! {
    if genv.local_config.ide_parser_cache {
        crate::ide_parser_cache::enable();
    }
    // During server lifetime dependency table can be not up-to-date. Because of
    // that, we ban access to it be default, forcing the code trying to read it to
    // take it into account, either by explcitely enabling reads (and being fine
    // with stale results), or declaring (in ServerCommand) that it requires full
    // check to be completed before being executed.
    let _: bool = typing_deps::allow_dependency_table_reads(&env.deps_mode, false);
    diagnostics_state::set_allow_errors_in_default_path(false);
    // (`Multi_threaded_call.on_exception Server_utils.exit_on_exception`: a
    // panic of the typing service goes up to `with_exit_on_exception`.)
    let mut client_provider = client_provider::provider_from_file_descriptors(in_fds);
    // This is needed when typecheck_after_init option is disabled.
    // We're just filling it with placeholder telemetry values since
    // we don't much care about this scenario.
    let init_telemetry = init_telemetry::make(
        server_env::InitTelemetryReason::InitTypecheckDisabledAfterInit,
        telemetry::string_(
            None,
            "mode",
            "serve_due_to_disabled_typecheck_after_init",
            telemetry::create(),
        ),
    );
    let typecheck_telemetry = telemetry::create();
    if env.init_env.why_needed_full_check.is_none() {
        finalize_init(&env.init_env, typecheck_telemetry, &init_telemetry);
    }
    let mut env = setup_interrupts(env, &client_provider);
    loop {
        env = serve_one_iteration(&genv, env, &mut client_provider);
    }
}

/// `program_init genv env` (the daemon's).
pub fn program_init(genv: &Genv, env: server_env::Env) -> server_env::Env {
    hh_logger::log(&format!("Init id: {}", env.init_env.init_id));
    server_progress::with_message(None, None, "initializing...", || {
        server_progress::enable_error_production(genv.local_config.produce_streaming_errors);
        add_errors_unlink_hook();
        // (`ci_info`: `Ci_util.begin_get_info` is a no-op in the open-source
        // build.)
        let (init_approach, approach_name) = server_init::resolve_init_approach(genv);
        hh_logger::log(&format!("Initing with approach: {}", approach_name));
        let (env, init_type, init_error, init_error_telemetry, saved_state_revs_info) = {
            let (env, init_result) = server_init::init(genv, env, init_approach.clone());
            match init_approach {
                InitApproach::WriteSymbolInfo | InitApproach::FullInit => {
                    (env, "fresh".to_string(), None, None, None)
                }
                InitApproach::ParseOnlyInit => (env, "parse-only".to_string(), None, None, None),
                InitApproach::WriteSymbolInfoWithState(_) | InitApproach::SavedStateInit(_) => {
                    match init_result {
                        server_init::InitResult::LoadStateSucceeded(saved_state_revs_info) => {
                            // (`Naming_table.get_forward_naming_fallback_path`:
                            // the naming table is never backed by SQLite yet.)
                            let init_type = "state_load_blob".to_string();
                            (env, init_type, None, None, Some(saved_state_revs_info))
                        }
                        server_init::InitResult::LoadStateFailed(err, telemetry) => (
                            env,
                            "state_load_failed".to_string(),
                            Some(err),
                            Some(telemetry),
                            None,
                        ),
                        server_init::InitResult::LoadStateDeclined(reason) => (
                            env,
                            "state_load_declined".to_string(),
                            Some(reason),
                            None,
                            None,
                        ),
                    }
                }
            }
        };
        let mut env = env;
        env.init_env.saved_state_revs_info = saved_state_revs_info;
        env.init_env.approach_name = approach_name;
        env.init_env.init_error = init_error;
        env.init_env.init_type = init_type;
        hh_logger::log("Waiting for daemon(s) to be ready...");
        server_progress::write(None, None, "wrapping up init...");
        server_notifier::wait_until_ready(&genv.notifier);
        // (`Event_logger.set_init_type`, `Hack_event_logger.init_lazy_end`
        // with this telemetry: no-ops.)
        let _telemetry = telemetry::json(
            "deps_mode",
            typing_deps::mode::to_opaque_json(&env.deps_mode),
            telemetry::object_opt(
                "init_error",
                init_error_telemetry,
                server_utils::log_and_get_sharedmem_load_telemetry(),
            ),
        );
        env
    })
}

/// `Exit.add_hook_upon_clean_exit (fun _finale_data ->
/// Server_progress.ErrorsWrite.unlink_at_server_stop ())`
fn add_errors_unlink_hook() {
    exit::add_hook_upon_clean_exit(|_finale_data| {
        server_progress::errors_write::unlink_at_server_stop()
    });
}

/// Setup files for IPC. These are used to transmit status messages and
/// errors. (`setup_ipc root`)
fn setup_ipc(root: &path::T) {
    // There are three files which are used for IPC.
    // 1. server_finale_file - we unlink it now upon startup,
    //    and upon clean exit we'll write finale-date to it.
    // 2. server_receipt_to_monitor_file - we'll unlink it now upon startup,
    //    and upon clean exit we'll unlink it.
    // 3. server_progress_file - we write "starting up" to it now upon startup,
    //    and upon clean exit we'll write "shutting down" to it.
    // In both case of clean exit and abrupt exit there'll be leftover files.
    // We'll rely upon tmpclean to eventually clean them up.
    let pid = ocaml_unix::getpid();
    server_progress::set_root(root.clone());
    let server_finale_file = server_files::server_finale_file(pid);
    let server_receipt_to_monitor_file = server_files::server_receipt_to_monitor_file(pid);
    let _ = std::fs::remove_file(&server_finale_file);
    let _ = std::fs::remove_file(&server_receipt_to_monitor_file);
    exit::add_hook_upon_clean_exit(move |finale_data| {
        let _ = std::fs::remove_file(&server_receipt_to_monitor_file);
        // (`Sys_utils.with_umask 0o000`: `rt::finale::write` makes the file
        // readable by all.)
        let _ = crate::rt::finale::write(&server_finale_file, finale_data);
        server_progress::write(None, None, "shutting down");
    });
}

/// `initialize_logging ~is_worker:false ...`: the levels and categories of
/// the logs (`Hack_event_logger.init` is a no-op).
fn initialize_logging(local_config: &server_local_config::T) {
    hh_logger::level::set_min_level(local_config.min_log_level);
    let categories: Vec<&str> = local_config.log_categories.iter().map(|s| s.as_str()).collect();
    hh_logger::level::set_categories(&categories);
}

/// `Sys_utils.is_nfs`: whether `path` is on NFS (or SMB/CIFS).
fn is_nfs(path: &str) -> bool {
    let Ok(c) = std::ffi::CString::new(path) else {
        return false;
    };
    // SAFETY: `buf` is written by `statfs` before it is read.
    unsafe {
        let mut buf: libc::statfs = std::mem::zeroed();
        if libc::statfs(c.as_ptr(), &mut buf) != 0 {
            panic!("Failure: statfs failed");
        }
        #[cfg(target_os = "linux")]
        {
            const NFS_SUPER_MAGIC: i64 = 0x6969;
            const SMB_SUPER_MAGIC: i64 = 0x517B;
            const CIFS_MAGIC_NUMBER: i64 = 0xFF534D42;
            matches!(
                buf.f_type as i64,
                NFS_SUPER_MAGIC | SMB_SUPER_MAGIC | CIFS_MAGIC_NUMBER
            )
        }
        #[cfg(not(target_os = "linux"))]
        {
            let name = std::ffi::CStr::from_ptr(buf.f_fstypename.as_ptr()).to_string_lossy();
            matches!(&*name, "nfs" | "smbfs" | "cifs")
        }
    }
}

/// `check_nfs ~root options local_config`
fn check_nfs(root: &path::T, options: &server_args::Options, local_config: &server_local_config::T) {
    let root_s = path::to_string(root);
    let check_mode = server_args::check_mode(options);
    if !check_mode && is_nfs(&root_s) && !local_config.enable_on_nfs {
        hh_logger::log(&format!("Refusing to run on {}: root is on NFS!", root_s));
        exit::exit(None, None, None, exit_status::T::NfsRoot)
    }
}

/// `Sys_utils.set_priorities ~cpu_priority ~io_priority`
fn set_priorities(cpu_priority: isize, io_priority: isize) {
    // No need to check the return value, if we failed then whatever.
    #[cfg(target_os = "linux")]
    // SAFETY: `ioprio_set` takes three integers.
    unsafe {
        const IOPRIO_WHO_PROCESS: libc::c_long = 1;
        const IOPRIO_CLASS_BE: libc::c_long = 2;
        const IOPRIO_CLASS_SHIFT: libc::c_long = 13;
        libc::syscall(
            libc::SYS_ioprio_set,
            IOPRIO_WHO_PROCESS,
            libc::getpid() as libc::c_long,
            (IOPRIO_CLASS_BE << IOPRIO_CLASS_SHIFT) | io_priority as libc::c_long,
        );
    }
    #[cfg(not(target_os = "linux"))]
    let _ = io_priority;
    // SAFETY: `nice` takes an integer.
    unsafe {
        libc::nice(cpu_priority as libc::c_int);
    }
}

/// `get_deps_mode options`
pub fn get_deps_mode(options: &server_args::Options) -> typing_deps::mode::T {
    match server_args::save_64bit(options) {
        Some(new_edges_dir) => {
            let human_readable_dep_map_dir =
                server_args::save_human_readable_64bit_dep_map(options);
            typing_deps::mode::T::SaveToDiskMode {
                graph: None,
                new_edges_dir,
                human_readable_dep_map_dir,
            }
        }
        None => typing_deps::mode::T::InMemoryMode(None),
    }
}

/// `log_pids root ~monitor_pid`
fn log_pids(root: &path::T, monitor_pid: Option<i32>) {
    pid_log::init(&server_files::pids_file(root));
    if let Some(monitor_pid) = monitor_pid {
        pid_log::log(Some("monitor"), None, monitor_pid as isize);
    }
    pid_log::log(Some("main"), None, ocaml_unix::getpid());
}

/// Does a bunch of operations to get the server up and running, among other things:
/// - Create a unique init ID
/// - Creates a bunch of files for IPC, e.g. for errors and status transmission.
/// - initialize logging
/// - initialize workers (the threads of the pool)
///
/// (`setup_server ~informant_managed ~monitor_pid options config
/// local_config`: the number of workers instead of the workers.)
pub fn setup_server(
    monitor_pid: Option<i32>,
    options: &server_args::Options,
    config: &server_config::T,
    local_config: &server_local_config::T,
) -> (isize, server_env::Env) {
    let num_workers = num_workers(options, local_config);
    // (`Shared_mem.init`: there is no shared memory.)
    let init_id = random_id::short_string();
    let root = server_args::root(options);
    setup_ipc(&root);
    server_progress::write(None, None, "starting up");
    hh_logger::log(&format!("Version: {}", hh_version::version()));
    hh_logger::log(&format!("Hostname: {}", gethostname()));
    // (`configure_gc ()`: there is no OCaml GC.)
    match crate::files::ignored_path_regexes(server_config::ignored_path_patterns(config)) {
        Ok(regexes) => {
            for re in regexes {
                crate::files_to_ignore::ignore_path(re)
            }
        }
        Err(e) => panic!("{:#}", e),
    }
    initialize_logging(local_config);
    // (`Hack_event_logger.init_start`: a no-op.)
    check_nfs(&root, options, local_config);
    warn_on_non_opt_build(options, config);
    program::set_signals();
    set_priorities(local_config.cpu_priority, local_config.io_priority);
    log_pids(&root, monitor_pid);
    // `make_workers`: the threads of the pool.
    if let Err(e) = check::build_thread_pool(Some(num_workers as usize)) {
        panic!("{:#}", e)
    }
    let env = server_env_build::make_env(
        &init_id,
        get_deps_mode(options),
        None,
        config,
        std::path::Path::new(&path::to_string(&root)),
    );
    (num_workers, env)
}

/// `log_pid_cgroup ()`
fn log_pid_cgroup() {
    // `Proc_fs.first_cgroup_for_pid pid`: the first line of
    // `/proc/<pid>/cgroup`, without its `<id>:<controllers>:` (an error
    // where there is no procfs).
    let pid = ocaml_unix::getpid();
    if let Ok(contents) = std::fs::read_to_string(format!("/proc/{}/cgroup", pid)) {
        if let Some(line) = contents.lines().next() {
            if let Some(cgroup) = line.splitn(3, ':').nth(2) {
                hh_logger::log(&format!("Server Pid: {}", pid));
                hh_logger::log(&format!("Server cGroup: {}", cgroup));
            }
        }
    }
}

/// `log_server_ready ()`
fn log_server_ready() {
    hh_logger::log("Server is partially ready");
}

/// `time f`
fn time<A>(f: impl FnOnce() -> A) -> A {
    let t = gettimeofday();
    let res = f();
    let t_ = gettimeofday();
    hh_logger::log(&format!("Took {:.6} seconds.", t_ - t));
    res
}

/// The server monitor will pass client connections to this process
/// via ic. (`daemon_main_exn ~informant_managed options monitor_pid
/// in_fds`)
fn daemon_main_exn(options: server_args::Options, monitor_pid: Option<i32>, in_fds: InFds) -> ! {
    assert!(!server_args::check_mode(&options));
    // (The values of the OCaml modules evaluated at the start of the
    // program: the clocks of `Server_idle`.)
    periodical::init_last_call();
    server_idle::init_last_client_connect();
    hh_logger::log("Server_main daemon starting.");
    let (config, local_config) = match server_config::load(
        false,
        &server_args::from(&options),
        &server_args::config(&options),
    ) {
        Ok(configs) => configs,
        Err(e) => std::panic::panic_any(e),
    };
    // (`memtrace_dir`: no memtrace.)
    let (num_workers, env) = setup_server(monitor_pid, &options, &config, &local_config);
    let root = server_args::root(&options);
    let genv = server_env_build::make_genv(options, config, local_config, num_workers);
    // (`Hack_event_logger.with_id ~stage:`Init`: a no-op.)
    log_pid_cgroup();
    hh_logger::log("Initializing Server (This might take some time)");
    let env = time(|| program_init(&genv, env));
    server_idle::init(&genv, &root);
    log_server_ready();
    serve(genv, env, in_fds)
}

/// `daemon_main_exn ~informant_managed options monitor_pid in_fds` under
/// `Server_utils.with_exit_on_exception`: the entry of the typechecker
/// server (plan §8 item 2). MON's entry wrapper
/// (`server_controller::server_daemon_entry`, the first part of the
/// OCaml's `Server_main.daemon_main`) has set close-on-exec on the pipes,
/// restored the global state (`Server_global_state.restore`) and run
/// `setup_hhi_root` (`monitor_start::setup_hhi_root`) before: the hhi
/// root it chose is recorded here (`Hhi.root`, which the daily
/// `Hhi.touch` uses). `in_fds` = (default, priority,
/// force_dormant_start_only). (`informant_managed` is always false: the
/// informant is the `Resigned` one; it only goes to `Hack_event_logger`.)
pub fn daemon_main(
    options: server_args::Options,
    monitor_pid: Option<i32>,
    in_fds: (RawFd, RawFd, RawFd),
) -> ! {
    if let Ok(hhi) = relative_path::path_of_prefix(relative_path::Prefix::Hhi) {
        if !hhi.is_empty() {
            hhi_root::record_root(path::make(&hhi));
        }
    }
    let (default, priority, force_dormant_start_only) = in_fds;
    let in_fds = InFds {
        default,
        priority,
        force_dormant_start_only,
    };
    server_utils::with_exit_on_exception(|| daemon_main_exn(options, monitor_pid, in_fds))
}

#[cfg(test)]
mod daemon_tests;

#[cfg(test)]
mod tests {
    use ::relative_path::Prefix;
    use ::relative_path::RelativePath;
    use oxidized::message::Message;

    use super::*;

    fn diag(file: &str, line: usize) -> oxidized::diagnostics::Diagnostic {
        let path = RelativePath::make(Prefix::Root, file.into());
        let pos = oxidized::pos::Pos::from_lnum_bol_offset(
            std::sync::Arc::new(path),
            (line, 0, 0),
            (line, 0, 1),
        );
        crate::diagnostics::error(4110, pos, format!("{file}:{line}"))
    }

    fn file(l: &[(&str, &[usize])]) -> FileDiagnostics {
        l.iter()
            .map(|(file, lines)| {
                (
                    RelativePath::make(Prefix::Root, (*file).into()),
                    lines.iter().map(|&line| diag(file, line)).collect(),
                )
            })
            .collect()
    }

    fn lines(t: &diagnostics_state::T) -> Vec<String> {
        t.values()
            .flatten()
            .map(|d| {
                let Message(_, msg) = &d.claim;
                msg.to_string()
            })
            .collect()
    }

    /// The diagnostics of each file in the reverse of the order they were
    /// reported in (as the OCaml gives them: see `full_init_diagnostics`),
    /// the files in the order of `Relative_path`, without deduplication.
    use crate::rt::diagnostic_fixtures as fx;

    fn printed(json: bool, l: &[fx::FinalizedDiagnostic]) -> String {
        let mut out = vec![];
        print_error_list(&mut out, json, l);
        String::from_utf8(out).unwrap()
    }

    /// The version object of the OCaml's outputs below is replaced by this
    /// build's.
    fn with_version(ocaml: &str) -> String {
        let version = crate::yojson::safe::to_string(&hh_version::version_json());
        ocaml.replace(
            r#"{"commit":"7c6928b554a959a2f139efbcd4a20bffc4d30717","commit_time":1794434757,"build_mode":"","api_version":5}"#,
            &version,
        )
    }

    /// The diagnostics of `hh_server --check` on a root with one file,
    /// `a.php`:
    ///
    /// ```text
    /// <?hh
    ///
    /// function f(int $x): string {
    ///   return $x;
    /// }
    ///
    /// function g(string $s): void {
    ///   if ($s is string) {
    ///   }
    /// }
    /// ```
    ///
    /// in the order of the environment (`full_init_diagnostics`).
    fn err_root() -> Vec<fx::FinalizedDiagnostic> {
        let f = "/private/tmp/hh-srv/err/a.php";
        let mut error = fx::err(
            4110,
            fx::msg(fx::chars(f, 4, 10, 11), "Invalid return type"),
            vec![
                fx::msg(fx::chars(f, 3, 21, 26), "Expected `string`"),
                fx::msg(fx::chars(f, 3, 12, 14), "But got `int`"),
            ],
        );
        error.function_pos = Some(fx::chars(f, 3, 1, 43));
        vec![
            fx::warning(
                12009,
                fx::msg(
                    fx::chars(f, 8, 7, 18),
                    "This `is` check is always `true`. The expression on the left has type `string` which is a subtype of `string`.",
                ),
                vec![],
            ),
            error,
        ]
    }

    /// The outputs of the OCaml's `hh_server --check [--json]` on that root,
    /// on the same root without `f` (a warning only), and on a root without
    /// errors.
    #[test]
    fn output_is_the_ocamls() {
        assert_eq!(
            printed(true, &err_root()),
            with_version(
                r#"{"passed":false,"errors":[{"severity":"warning","is_trusted":true,"message":[{"descr":"This `is` check is always `true`. The expression on the left has type `string` which is a subtype of `string`.","path":"/private/tmp/hh-srv/err/a.php","line":8,"start":7,"end":18,"code":12009}],"custom_messages":[]},{"severity":"error","is_trusted":true,"message":[{"descr":"Invalid return type","path":"/private/tmp/hh-srv/err/a.php","line":4,"start":10,"end":11,"code":4110},{"descr":"Expected `string`","path":"/private/tmp/hh-srv/err/a.php","line":3,"start":21,"end":26,"code":4110},{"descr":"But got `int`","path":"/private/tmp/hh-srv/err/a.php","line":3,"start":12,"end":14,"code":4110}],"custom_messages":[],"function_pos":{"path":"/private/tmp/hh-srv/err/a.php","line":3,"start":1,"end":43,"code":4110}}],"version":{"commit":"7c6928b554a959a2f139efbcd4a20bffc4d30717","commit_time":1794434757,"build_mode":"","api_version":5}}"#
            )
        );
        assert_eq!(
            printed(false, &err_root()),
            r#"ERROR: File "/private/tmp/hh-srv/err/a.php", line 4, characters 10-11:
Invalid return type (Typing[4110])
  File "/private/tmp/hh-srv/err/a.php", line 3, characters 21-26:
  Expected `string`
  File "/private/tmp/hh-srv/err/a.php", line 3, characters 12-14:
  But got `int`

WARN: File "/private/tmp/hh-srv/err/a.php", line 8, characters 7-18:
This `is` check is always `true`. The expression on the left has type `string` which is a subtype of `string`. (Warn[12009])

"#
        );
        let warning = &err_root()[..1];
        assert_eq!(
            printed(true, warning),
            with_version(
                r#"{"passed":true,"errors":[{"severity":"warning","is_trusted":true,"message":[{"descr":"This `is` check is always `true`. The expression on the left has type `string` which is a subtype of `string`.","path":"/private/tmp/hh-srv/err/a.php","line":8,"start":7,"end":18,"code":12009}],"custom_messages":[]}],"version":{"commit":"7c6928b554a959a2f139efbcd4a20bffc4d30717","commit_time":1794434757,"build_mode":"","api_version":5}}"#
            )
        );
        assert_eq!(
            printed(true, &[]),
            with_version(
                r#"{"passed":true,"errors":[],"version":{"commit":"7c6928b554a959a2f139efbcd4a20bffc4d30717","commit_time":1794434757,"build_mode":"","api_version":5}}"#
            )
        );
        assert_eq!(printed(false, &[]), "No errors!\n");
    }

    /// The exit status: errors only count, and `--write-symbol-info` has its
    /// own (`--json` does not change it).
    #[test]
    fn exit_codes() {
        let options = server_args::default_options_with_check_mode("/");
        assert_eq!(exit_code(&options, false), 0);
        assert_eq!(exit_code(&options, true), 1);
    }

    #[test]
    fn full_init_diagnostics_are_reversed_per_file() {
        let by_file = vec![
            file(&[("b.php", &[4, 8, 8])]),
            file(&[("a/x.php", &[1, 2])]),
            file(&[]),
            file(&[("a.php", &[3])]),
        ];
        assert_eq!(
            lines(&full_init_diagnostics(by_file)),
            ["a.php:3", "a/x.php:2", "a/x.php:1", "b.php:8", "b.php:8", "b.php:4"]
        );
        // A file whose diagnostics come from the checks of several files:
        // the last file's first.
        let by_file = vec![
            file(&[("c.php", &[1, 2])]),
            file(&[("d.php", &[5]), ("c.php", &[3, 4])]),
        ];
        assert_eq!(
            lines(&full_init_diagnostics(by_file)),
            ["c.php:4", "c.php:3", "c.php:2", "c.php:1", "d.php:5"]
        );
    }
}
