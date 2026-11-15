// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_env.ml`: the environment of the
//! daemon (`genv`, `env`) and the recheck loop types.
//!
//! The OCaml fields of `server_env.ml` that are in scope, plus `ctx` (no
//! `popt`, `tcopt`, `gleanopt`, `swriteopt`: the options are those of `ctx`; no
//! `workers`, `indexer`, `debug_channels` in `genv`: the workers are the
//! threads of the rayon pool, the indexer is `server_notifier::indexer`).
//!
//! `nonpersistent_client_pending_command_needs_full_check` holds the client
//! and the continuation that finishes handling its command; the
//! continuation takes the `genv` and the client provider, which the OCaml's
//! closure captures. `interrupt_handlers` is the OCaml's function of `genv`
//! and `env`, as `Server_main.setup_interrupts` sets it.

use std::os::fd::RawFd;
use std::sync::Arc;

use crate::ctx::Ctx;
use crate::diagnostics;
use crate::naming_table;
use crate::server_args;
use crate::client_provider_sig::Client;
use crate::client_provider_sig;
use crate::server_config;
use crate::server_local_config;
use crate::server_notifier;
use crate::telemetry;
use crate::typing_deps;

type RPSet = crate::relative_path::set::T;

/// `seconds`
pub type Seconds = f64;

/// `seconds_since_epoch`
pub type SecondsSinceEpoch = f64;

/// Telemetry for calls to Rust [DiskProvider::read], including failed attempts.
/// File reads performed through other APIs are not included.
/// (`Rust_disk_provider_read_telemetry.t`.) The port reads files through its
/// own `crate::ctx::Files`, never through `file_provider::DiskProvider`, so
/// the totals stay at zero; the telemetry keeps the OCaml's shape.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct RustDiskProviderReadTelemetry {
    pub count: isize,
    pub seconds: f64,
}

/// `Rust_disk_provider_read_telemetry`
pub mod rust_disk_provider_read_telemetry {
    use super::RustDiskProviderReadTelemetry as T;
    use crate::measure;
    use crate::telemetry;

    /// Cumulative read count and elapsed time from the main process and
    /// collected worker results. Cancelled jobs whose results are discarded are not
    /// included. Retrieving totals does not reset the measurements.
    pub fn get_totals() -> T {
        let record = measure::peek_global();
        let count = measure::get_count(Some(&record), "rust_disk_provider_read_seconds")
            .unwrap_or(0.) as isize;
        let seconds =
            measure::get_sum(Some(&record), "rust_disk_provider_read_seconds").unwrap_or(0.);
        T { count, seconds }
    }

    /// Subtract [start] from [finish].
    pub fn delta(start: &T, finish: &T) -> T {
        T {
            count: finish.count - start.count,
            seconds: finish.seconds - start.seconds,
        }
    }

    /// Encode read attempts and summed elapsed milliseconds.
    pub fn to_telemetry(t: &T) -> telemetry::T {
        let telemetry = telemetry::create();
        let telemetry = telemetry::int_("count", t.count, telemetry);
        telemetry::float_("duration_ms", t.seconds * 1000., telemetry)
    }

    /// Read current totals and encode the delta from [start].
    pub fn get_delta_telemetry(start: &T) -> telemetry::T {
        to_telemetry(&delta(start, &get_totals()))
    }
}

/// `RecheckLoopStats.t`
#[derive(Clone, Debug, Default)]
pub struct RecheckLoopStats {
    /// File watcher subscription has gone down, so state of the world after
    /// the recheck loop may not reflect what is actually on disk.
    pub updates_stale: bool,
    /// An OCaml list: element 0 is the head (the last batch).
    pub per_batch_telemetry: Vec<telemetry::T>,
    /// Count of files changed on disk and potentially also in the IDE.
    pub total_changed_files_count: isize,
    pub total_rechecked_count: isize,
    pub last_iteration_start_time: SecondsSinceEpoch,
    pub duration: Seconds,
    /// Read count and elapsed time across the whole recheck loop.
    pub rust_disk_provider_read: RustDiskProviderReadTelemetry,
    pub time_first_result: Option<SecondsSinceEpoch>,
    pub recheck_id: String,
    pub any_full_checks: bool,
}

/// `RecheckLoopStats`
pub mod recheck_loop_stats {
    use super::RecheckLoopStats;
    use super::SecondsSinceEpoch;
    use crate::telemetry;

    /// `empty ~recheck_id`
    pub fn empty(recheck_id: &str) -> RecheckLoopStats {
        RecheckLoopStats {
            updates_stale: false,
            per_batch_telemetry: vec![],
            total_changed_files_count: 0,
            total_rechecked_count: 0,
            last_iteration_start_time: 0.,
            duration: 0.,
            rust_disk_provider_read: super::RustDiskProviderReadTelemetry {
                count: 0,
                seconds: 0.,
            },
            time_first_result: None,
            recheck_id: recheck_id.to_string(),
            any_full_checks: false,
        }
    }

    /// The format of this json is user-facing, returned from 'hh check --json'
    /// in field `last_recheck`.
    pub fn to_user_telemetry(stats: &RecheckLoopStats) -> telemetry::T {
        let RecheckLoopStats {
            updates_stale,
            per_batch_telemetry,
            total_changed_files_count,
            total_rechecked_count,
            last_iteration_start_time,
            duration,
            rust_disk_provider_read,
            time_first_result,
            recheck_id,
            any_full_checks,
        } = stats;
        let t = telemetry::create();
        let t = telemetry::string_(None, "id", recheck_id, t);
        let t = telemetry::float_("time", *duration, t);
        let t = telemetry::object_(
            "rust_disk_provider_read",
            super::rust_disk_provider_read_telemetry::to_telemetry(rust_disk_provider_read),
            t,
        );
        let t = telemetry::int_("count", *total_rechecked_count, t);
        let t = telemetry::int_("total_changed_files_count", *total_changed_files_count, t);
        let per_batch: Vec<telemetry::T> = per_batch_telemetry.iter().rev().cloned().collect();
        let t = telemetry::object_list("per_batch", &per_batch, t);
        let t = telemetry::bool_("updates_stale", *updates_stale, t);
        let t = telemetry::bool_("any_full_checks", *any_full_checks, t);
        telemetry::int_opt(
            "time_to_first_result_ms",
            time_first_result
                .map(|time| ((time - last_iteration_start_time) * 1000.) as isize),
            t,
        )
    }

    /// Update field [time_first_result] if given timestamp is the
    /// first sent result.
    pub fn record_result_sent_ts(
        stats: RecheckLoopStats,
        new_result_sent_ts: Option<SecondsSinceEpoch>,
    ) -> RecheckLoopStats {
        RecheckLoopStats {
            time_first_result: stats.time_first_result.or(new_result_sent_ts),
            ..stats
        }
    }
}

/// The "static" environment, initialized first and then doesn't change
/// (`genv`; no `workers`, `indexer`, `debug_channels`).
pub struct Genv {
    pub options: server_args::Options,
    pub config: server_config::T,
    pub local_config: server_local_config::T,
    pub notifier: server_notifier::T,
    /// The threads of the rayon pool (`Server_main.num_workers`; the OCaml
    /// has `List.length workers`).
    pub num_workers: isize,
}

/// `full_check_status`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FullCheckStatus {
    /// Some updates have not been fully processed. We get into this state every
    /// time file contents change (on disk, or through IDE notifications).
    /// Operations that depend on global state (like taking full error list, or
    /// looking up things in dependency table) will have stale results.
    FullCheckNeeded,
    /// Same as above, except server will actively try to process outstanding
    /// changes (by going into Server_type_check from main loop - this might need to
    /// be repeated several times before progressing to Full_check_done, due to
    /// ability to interrupt typecheck jobs).
    /// Server starts in this state, and we also enter it from Full_check_needed
    /// whenever there is a command requiring full check pending, or when user
    /// saves a file.
    FullCheckStarted,
    /// All the changes have been fully processed.
    FullCheckDone,
    /// Automatic checks are paused by [hh --pause] until the next accepted client connection.
    /// Invariants:
    ///   - When transitioning to this state, [disk_needs_parsing] and [needs_recheck] are empty.
    ///   - While paused, [needs_recheck] remains empty, but new file changes
    ///     accumulate in [disk_needs_parsing].
    FullCheckPaused,
}

/// `show_full_check_status` (`[@@deriving show]`)
pub fn show_full_check_status(s: FullCheckStatus) -> &'static str {
    match s {
        FullCheckStatus::FullCheckNeeded => "Server_env.Full_check_needed",
        FullCheckStatus::FullCheckStarted => "Server_env.Full_check_started",
        FullCheckStatus::FullCheckDone => "Server_env.Full_check_done",
        FullCheckStatus::FullCheckPaused => "Server_env.Full_check_paused",
    }
}

pub fn is_full_check_done(s: FullCheckStatus) -> bool {
    matches!(s, FullCheckStatus::FullCheckDone)
}

pub fn is_full_check_needed(s: FullCheckStatus) -> bool {
    matches!(s, FullCheckStatus::FullCheckNeeded)
}

pub fn is_full_check_started(s: FullCheckStatus) -> bool {
    matches!(s, FullCheckStatus::FullCheckStarted)
}

/// `Init_telemetry`
pub mod init_telemetry {
    use crate::telemetry;

    /// `reason`
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Reason {
        InitLazyDirty,
        InitTypecheckDisabledAfterInit,
        InitLazyFull,
        InitPrecheckedFanout,
    }

    /// `t`
    #[derive(Clone, Debug)]
    pub struct T {
        pub reason: Reason,
        pub telemetry: telemetry::T,
    }

    /// `show_reason` (`[@@deriving show { with_path = false }]`)
    pub fn show_reason(reason: Reason) -> &'static str {
        match reason {
            Reason::InitLazyDirty => "Init_lazy_dirty",
            Reason::InitTypecheckDisabledAfterInit => {
                "Init_typecheck_disabled_after_init"
            }
            Reason::InitLazyFull => "Init_lazy_full",
            Reason::InitPrecheckedFanout => "Init_prechecked_fanout",
        }
    }

    pub fn make(reason: Reason, telemetry: telemetry::T) -> T {
        T { reason, telemetry }
    }

    pub fn get(t: &T) -> telemetry::T {
        telemetry::string_(None, "reason", show_reason(t.reason), t.telemetry.clone())
    }

    pub fn get_reason(t: &T) -> String {
        show_reason(t.reason).to_string()
    }
}

/// How "old" a given saved state is relative to the working revision.
/// That is, a saved state has some corresponding revision X, and `hh` is
/// invoked on a commit of mergebase Y.
///
/// Distance tracks the number of revisions between X and Y, using globalrev.
/// Age tracks the time elapsed between X and Y in seconds, according to hg
/// log data. (The revisions are strings here.)
#[derive(Clone, Debug, PartialEq)]
pub struct SavedStateRevsInfo {
    pub distance: Option<isize>,
    pub age: Option<isize>,
    pub saved_state_rev: String,
    pub saved_state_globalrev: Option<isize>,
    pub saved_state_rev_timestamp: Option<isize>,
    pub mergebase_rev: Option<String>,
    pub mergebase_globalrev: Option<isize>,
    pub mergebase_rev_timestamp: Option<isize>,
}

pub fn mergebase_has_saved_state(info: &SavedStateRevsInfo) -> Option<bool> {
    info.mergebase_rev
        .as_ref()
        .map(|mergebase_rev| *mergebase_rev == info.saved_state_rev)
}

/// `SavedStateRevsInfo`
pub mod saved_state_revs_info {
    use super::SavedStateRevsInfo;
    use crate::telemetry;

    pub fn default(saved_state_rev: String) -> SavedStateRevsInfo {
        SavedStateRevsInfo {
            distance: None,
            age: None,
            saved_state_rev,
            saved_state_globalrev: None,
            saved_state_rev_timestamp: None,
            mergebase_rev: None,
            mergebase_globalrev: None,
            mergebase_rev_timestamp: None,
        }
    }

    pub fn to_telemetry(info: &SavedStateRevsInfo) -> telemetry::T {
        let t = telemetry::create();
        let t = telemetry::int_opt("distance", info.distance, t);
        let t = telemetry::int_opt("age_seconds", info.age, t);
        let t = telemetry::string_(None, "saved_state_rev", &info.saved_state_rev, t);
        let t = telemetry::int_opt("saved_state_globalrev", info.saved_state_globalrev, t);
        let t = telemetry::int_opt(
            "saved_state_rev_timestamp",
            info.saved_state_rev_timestamp,
            t,
        );
        let t = telemetry::string_opt(None, "mergebase_rev", info.mergebase_rev.as_deref(), t);
        let t = telemetry::int_opt("mergebase_globalrev", info.mergebase_globalrev, t);
        telemetry::int_opt("mergebase_rev_timestamp", info.mergebase_rev_timestamp, t)
    }
}

/// `dirty_deps`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirtyDeps {
    /// We are rechecking dirty files to bootstrap the dependency graph.
    /// After this is done we need to also recheck full fan-out (in this updated
    /// graph) of provided set.
    pub dirty_local_deps: crate::typing_deps::dep_set::T,
    /// The fan-outs of those nodes were not expanded yet.
    pub dirty_master_deps: crate::typing_deps::dep_set::T,
    /// Files that have been rechecked since server startup
    pub rechecked_files: RPSet,
    /// Those deps have already been checked against their interaction with
    /// dirty_master_deps. Storing them here to avoid checking it over and over
    pub clean_local_deps: crate::typing_deps::dep_set::T,
}

/// `prechecked_files_status`: when using prechecked files we split initial
/// typechecking in two phases (dirty files and a subset of their fan-out).
/// Other init types compute the full fan-out up-front. (Only a saved-state
/// load enables them.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrecheckedFilesStatus {
    PrecheckedFilesDisabled,
    InitialTypechecking(DirtyDeps),
    PrecheckedFilesReady(DirtyDeps),
}

/// `init_env` (no `ci_info`, `mergebase_warning_hashes`,
/// `naming_table_manifold_path`).
#[derive(Clone, Debug)]
pub struct InitEnv {
    pub approach_name: String,
    pub init_error: Option<String>,
    pub init_id: String,
    pub init_start_t: f64,
    pub init_type: String,
    /// This is about the first full check (if any) which was deferred after init.
    /// It gets reset after that first full check is completed.
    pub why_needed_full_check: Option<init_telemetry::T>,
    pub recheck_id: Option<String>,
    /// Additional data associated with init that we want to log when a first full
    /// check completes.
    pub saved_state_revs_info: Option<SavedStateRevsInfo>,
    /// The hashes of the warnings of the saved state, which are not reported
    /// (`mergebase_warning_hashes`).
    pub mergebase_warning_hashes: Option<oxidized::warnings_saved_state_impl::WarningsSavedState>,
    /// The manifold path for naming table saved state, to be used by remote type checker
    /// for downloading the naming table in the case of a saved-state init
    /// (`naming_table_manifold_path`).
    pub naming_table_manifold_path: Option<String>,
}

/// Only to be used for testing. The functions in this record are called at predefined stages of
/// type-checking, allowing to communicate with a test environment. The idea is to observe what the
/// type-checker is doing and trigger actions (e.g., changing files on disk).
/// (`type_check_testing_hooks`.) `Send + Sync`: the files are checked on
/// the threads of the pool (see `Typing_check_service.go_with_interrupt`).
pub struct TypeCheckTestingHooks {
    /// Called from [Server_type_check.type_check_core] after [indexing]
    pub after_indexing: Box<dyn Fn() + Send + Sync>,
    /// Called at entry to [Server_type_check.do_redecl] with its old and new
    /// names per file, before oldification.
    pub before_redecl: Box<
        dyn Fn(&crate::relative_path::map::T<crate::decl_compare::versioned_names::T>)
            + Send
            + Sync,
    >,
    /// Called from [Decl_redecl_service.redeclare_files] after a file's declarations are parsed
    /// and its classes folded, before the next file or declaration comparison. Only called
    /// when redeclaration runs in-process rather than in workers.
    pub after_file_redecl: Box<dyn Fn(&crate::relative_path::T) + Send + Sync>,
    /// Called at entry to [Typing_check_service.go_with_interrupt] with its input file list in
    /// order.
    pub before_file_checks: Box<dyn Fn(&[crate::relative_path::T]) + Send + Sync>,
    /// Called from [Typing_check_service.process_one_workitem] after a [Check] completes.
    pub after_file_check: Box<dyn Fn(&crate::relative_path::T) + Send + Sync>,
}

/// What finishes handling a command that waits for a full check: the
/// continuation of `Server_command.handle`, given what its OCaml closure
/// captures (`genv`, the client and its provider).
pub type FinishCommandHandling =
    Box<dyn FnOnce(&Genv, &mut dyn client_provider_sig::S, &mut Client, Env) -> Env + Send>;

/// `nonpersistent_client_pending_command_needs_full_check`: the
/// continuation, the reason why this command needs full recheck (for
/// logging/debugging purposes), and the client.
pub type PendingCommand = (FinishCommandHandling, String, Client);

/// `env Multi_threaded_call.interrupt_handler`
pub type InterruptHandler<'a> = crate::typing_check_service::InterruptHandler<'a, Env>;

/// `interrupt_handlers: genv -> env -> (Unix.file_descr * env
/// Multi_threaded_call.interrupt_handler) list`
pub type InterruptHandlers =
    Arc<dyn for<'a> Fn(&'a Genv, &Env) -> Vec<(RawFd, InterruptHandler<'a>)> + Send + Sync>;

/// The environment constantly maintained by the server (`env`).
///
/// In addition to this environment, many functions are storing and updating
/// ASTs, NASTs, and types in a shared space (see respectively Parser_heap,
/// Naming_table, Typing_env). (Here: the stores of `ctx`.)
pub struct Env {
    /// Not in the OCaml record: the context every phase works on (the
    /// OCaml's is global, `Provider_utils.ctx_from_server_env`).
    pub ctx: Arc<Ctx>,
    pub naming_table: naming_table::T,
    pub deps_mode: typing_deps::mode::T,
    /// Diagnostics are indexed by files that were known to GENERATE diagnostics in
    /// corresponding phases. Note that this is different from HAVING diagnostics -
    /// it's possible for checking of A to generate a diagnostic in B - in this case
    /// Diagnostics.get_failed_files Typing should contain A, not B.
    pub diagnostics: diagnostics::T,
    /// failed_naming is used as kind of a dependency tracking mechanism:
    /// if files A.php and B.php both define class C, then those files are
    /// mutually depending on each other (edit to one might resolve naming
    /// ambiguity and change the interpretation of the other).
    pub failed_naming: RPSet,
    /// Timestamp of last IDE file synchronization command
    pub last_command_time: f64,
    /// Timestamp of last query for disk changes
    pub last_notifier_check_time: f64,
    /// Timestamp of last Server_idle.go run
    pub last_idle_job_time: f64,
    /// Files which parse trees were invalidated (because they changed on
    /// disk) and need to be re-parsed
    pub disk_needs_parsing: RPSet,
    /// This is the clock as of when disk_needs_parsing was last updated.
    /// None if not using Watchman or Edenfs_watcher.
    pub clock: Option<server_notifier::Clock>,
    /// Declarations that became invalidated and moved to "old" part of the heap.
    pub needs_phase2_redecl: RPSet,
    /// Files that need to be typechecked before commands that depend on global
    /// state (like full list of errors, build, or find all references) can be
    /// executed.
    pub needs_recheck: RPSet,
    pub why_needs_server_type_check: (String, String),
    pub init_env: InitEnv,
    pub full_check_status: FullCheckStatus,
    pub prechecked_files: PrecheckedFilesStatus,
    pub changed_files: RPSet,
    pub interrupt_handlers: InterruptHandlers,
    /// Should be [None] unless running tests. See [type_check_testing_hooks].
    pub type_check_testing_hooks: Option<Arc<TypeCheckTestingHooks>>,
    /// When a non-persistent client sends a command that cannot be immediately handled
    /// (due to needing full check) we put the continuation that finishes handling
    /// it here.
    pub nonpersistent_client_pending_command_needs_full_check: Option<PendingCommand>,
    pub last_recheck_loop_stats: RecheckLoopStats,
    pub last_recheck_loop_stats_for_actual_work: Option<RecheckLoopStats>,
}

/// A copy of `env` without its pending command (which cannot be copied):
/// what `Server_command.Nonfatal_rpc_exception` gives back (the env from
/// before the command) when handling a command panics. The OCaml's values
/// are immutable, so the copy is free there; here the sets and maps are
/// persistent (cheap), the diagnostics are copied.
pub fn copy_without_pending_command(env: &Env) -> Env {
    Env {
        ctx: Arc::clone(&env.ctx),
        naming_table: env.naming_table.clone(),
        deps_mode: env.deps_mode.clone(),
        diagnostics: env.diagnostics.clone(),
        failed_naming: env.failed_naming.clone(),
        last_command_time: env.last_command_time,
        last_notifier_check_time: env.last_notifier_check_time,
        last_idle_job_time: env.last_idle_job_time,
        disk_needs_parsing: env.disk_needs_parsing.clone(),
        clock: env.clock.clone(),
        needs_phase2_redecl: env.needs_phase2_redecl.clone(),
        needs_recheck: env.needs_recheck.clone(),
        why_needs_server_type_check: env.why_needs_server_type_check.clone(),
        init_env: env.init_env.clone(),
        full_check_status: env.full_check_status,
        prechecked_files: env.prechecked_files.clone(),
        changed_files: env.changed_files.clone(),
        interrupt_handlers: Arc::clone(&env.interrupt_handlers),
        type_check_testing_hooks: env.type_check_testing_hooks.clone(),
        nonpersistent_client_pending_command_needs_full_check: None,
        last_recheck_loop_stats: env.last_recheck_loop_stats.clone(),
        last_recheck_loop_stats_for_actual_work: env
            .last_recheck_loop_stats_for_actual_work
            .clone(),
    }
}

/// `discard_warnings env`
pub fn discard_warnings(env: &Env) -> bool {
    // `Sandcastle.is_sandcastle ()` is false in the open-source build
    // (`stubs/sandcastle.ml`).
    env.init_env
        .saved_state_revs_info
        .as_ref()
        .and_then(mergebase_has_saved_state)
        .unwrap_or(false)
}

/// `list_files_with_errors env`: the absolute paths of the files with
/// errors (not warnings), sorted.
pub fn list_files_with_errors(env: &Env) -> Vec<String> {
    // The fold over the list adds the file of each error to a set of strings;
    // `S_set.elements` gives them in `String.compare` order.
    let mut acc: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for d in crate::diagnostics::get_diagnostic_list(None, env.diagnostics.clone()).iter().rev() {
        match d.severity {
            crate::user_diagnostic::Severity::Err => {
                acc.insert(crate::relative_path::to_absolute(d.claim.0.filename()));
            }
            crate::user_diagnostic::Severity::Warning { .. } => {}
        }
    }
    acc.into_iter().collect()
}

pub fn prechecked_files_ready_for_diagnostics(s: &PrecheckedFilesStatus) -> bool {
    match s {
        PrecheckedFilesStatus::PrecheckedFilesDisabled => true,
        PrecheckedFilesStatus::InitialTypechecking(_) => false,
        PrecheckedFilesStatus::PrecheckedFilesReady(dirty_deps) => dirty_deps.dirty_master_deps.is_empty(),
    }
}

/// True when [env.diagnostics] is complete enough for callers to filter and
/// serve without recomputing diagnostics.
pub fn are_diagnostics_complete(env: &Env, uses_partial_typecheck: bool) -> bool {
    !uses_partial_typecheck
        && is_full_check_done(env.full_check_status)
        && env.disk_needs_parsing.is_empty()
        && env.needs_phase2_redecl.is_empty()
        && env.needs_recheck.is_empty()
        && prechecked_files_ready_for_diagnostics(&env.prechecked_files)
}

pub fn add_changed_files(env: Env, changed_files: &RPSet) -> Env {
    Env {
        changed_files: env.changed_files.clone().union(changed_files.clone()),
        ..env
    }
}

pub fn show_clock(clock: Option<&server_notifier::Clock>) -> String {
    match clock {
        None => "[noclock]".to_string(),
        Some(clock) => server_notifier::show_clock(clock),
    }
}
