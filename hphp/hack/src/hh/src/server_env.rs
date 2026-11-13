// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_env.ml`: the environment of the
//! daemon (`genv`, `env`) and the recheck loop types.
//!
//! Owned by **SRV** (plan §3.1). The OCaml fields of `server_env.ml` that are
//! in scope, plus `ctx` (no `popt`, `tcopt`, `gleanopt`, `swriteopt`: the
//! options are those of `ctx`; no `workers`, `indexer`, `debug_channels` in
//! `genv`: the workers are the threads of the rayon pool, the indexer is
//! `server_notifier::indexer`).
//!
//! `nonpersistent_client_pending_command_needs_full_check` holds the client
//! and the continuation that finishes handling its command; the
//! continuation takes the `genv` and the client provider, which the OCaml's
//! closure captures. `interrupt_handlers` is the OCaml's function of `genv`
//! and `env`, as `Server_main.setup_interrupts` sets it.

use std::os::fd::RawFd;
use std::sync::Arc;

use crate::ctx::Ctx;
use crate::diagnostics_state;
use crate::naming_table;
use crate::rt::client_provider::Client;
use crate::rt::client_provider::ClientProvider;
use crate::server_args;
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
            time_first_result,
            recheck_id,
            any_full_checks,
        } = stats;
        let t = telemetry::create();
        let t = telemetry::string_(None, "id", recheck_id, t);
        let t = telemetry::float_("time", *duration, t);
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
}

/// `show_full_check_status` (`[@@deriving show]`)
pub fn show_full_check_status(s: FullCheckStatus) -> &'static str {
    match s {
        FullCheckStatus::FullCheckNeeded => "Server_env.Full_check_needed",
        FullCheckStatus::FullCheckStarted => "Server_env.Full_check_started",
        FullCheckStatus::FullCheckDone => "Server_env.Full_check_done",
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

/// `Init_telemetry.reason`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InitTelemetryReason {
    InitLazyDirty,
    InitTypecheckDisabledAfterInit,
    InitLazyFull,
    InitPrecheckedFanout,
}

/// `Init_telemetry.t`
#[derive(Clone, Debug)]
pub struct InitTelemetry {
    pub reason: InitTelemetryReason,
    pub telemetry: telemetry::T,
}

/// `Init_telemetry`
pub mod init_telemetry {
    use super::InitTelemetry;
    use super::InitTelemetryReason;
    use crate::telemetry;

    /// `show_reason` (`[@@deriving show { with_path = false }]`)
    pub fn show_reason(reason: InitTelemetryReason) -> &'static str {
        match reason {
            InitTelemetryReason::InitLazyDirty => "Init_lazy_dirty",
            InitTelemetryReason::InitTypecheckDisabledAfterInit => {
                "Init_typecheck_disabled_after_init"
            }
            InitTelemetryReason::InitLazyFull => "Init_lazy_full",
            InitTelemetryReason::InitPrecheckedFanout => "Init_prechecked_fanout",
        }
    }

    pub fn make(reason: InitTelemetryReason, telemetry: telemetry::T) -> InitTelemetry {
        InitTelemetry { reason, telemetry }
    }

    pub fn get(t: &InitTelemetry) -> telemetry::T {
        telemetry::string_(None, "reason", show_reason(t.reason), t.telemetry.clone())
    }

    pub fn get_reason(t: &InitTelemetry) -> String {
        show_reason(t.reason).to_string()
    }
}

/// How "old" a given saved state is relative to the working revision (saved
/// states are out of scope: the revisions are strings).
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

/// `prechecked_files_status`: prechecked files are only active after a
/// saved-state load (`Server_env_build`, plan §3.4), so only
/// `Prechecked_files_disabled` until SS3.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrecheckedFilesStatus {
    PrecheckedFilesDisabled,
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
    pub why_needed_full_check: Option<InitTelemetry>,
    pub recheck_id: Option<String>,
    /// Additional data associated with init that we want to log when a first full
    /// check completes.
    pub saved_state_revs_info: Option<SavedStateRevsInfo>,
}

/// What finishes handling a command that waits for a full check: the
/// continuation of `Server_command.handle`, given what its OCaml closure
/// captures (`genv`, the client and its provider).
pub type FinishCommandHandling =
    Box<dyn FnOnce(&Genv, &mut dyn ClientProvider, &mut Client, Env) -> Env + Send>;

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
    pub diagnostics: diagnostics_state::T,
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
        prechecked_files: env.prechecked_files,
        changed_files: env.changed_files.clone(),
        interrupt_handlers: Arc::clone(&env.interrupt_handlers),
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
    // (Ported by STATUS, for `LIST_FILES_WITH_ERRORS`.) The fold over the
    // list adds the file of each error to a set of strings; `S_set.elements`
    // gives them in `String.compare` order.
    let mut acc: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for d in crate::diagnostics_state::get_diagnostic_list(None, env.diagnostics.clone()).iter().rev() {
        match d.severity {
            crate::user_diagnostic::Severity::Err => {
                acc.insert(crate::relative_path::to_absolute(d.claim.0.filename()));
            }
            crate::user_diagnostic::Severity::Warning { .. } => {}
        }
    }
    acc.into_iter().collect()
}

pub fn prechecked_files_ready_for_diagnostics(s: PrecheckedFilesStatus) -> bool {
    match s {
        PrecheckedFilesStatus::PrecheckedFilesDisabled => true,
    }
}

pub fn are_diagnostics_complete(env: &Env, uses_partial_typecheck: bool) -> bool {
    !uses_partial_typecheck
        && is_full_check_done(env.full_check_status)
        && env.disk_needs_parsing.is_empty()
        && env.needs_phase2_redecl.is_empty()
        && env.needs_recheck.is_empty()
        && prechecked_files_ready_for_diagnostics(env.prechecked_files)
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
