// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/exit_status.ml`. See `hh/PORTING.md`.
//!
//! [`T`] has every constructor of `Exit_status.t`, in the OCaml order, named
//! as `hh_oxidize` names constructors (`No_error` is `NoError`,
//! `IDE_malformed_request` is `IDEMalformedRequest`); [`show`] prints the
//! OCaml names (`Exit_status.No_error`). `exception Exit_with of t` is
//! [`ExitWith`], the error of the functions that raise it
//! (`Result<_, ExitWith>`, or a variant of their module's error enum),
//! passed on with `?` up to where OCaml catches it (PORTING.md,
//! "Exceptions"; for `hh_client`, `crate::hh_client::Exn`); its `Debug` is
//! what the printer that this module registers with
//! `Exception.register_printer` prints, so `exception::wrap(ExitWith(t))` has
//! the OCaml constructor string
//! `Exit_status.Exit_with(Exit_status.Input_error)`.
//!
//! # The finale file
//!
//! OCaml marshals the `finale_data` into `<tmp>/<pid>.fin`
//! (`Server_main.setup_ipc`) and [`get_finale_data`] unmarshals it. So does
//! the port, with the same bytes: `crate::rt::finale::write` writes it and
//! [`get_finale_data`] reads it with `crate::rt::finale::read` (the encoding
//! is described there).
//!
//! Not ported: the derived `equal`-less polymorphic comparisons (match on the
//! constructors instead).

use std::fmt;

use crate::exception;
use crate::format;
use crate::format::Formatter;
use crate::rt::ocaml_printf::sprintf_s;
use crate::rt::finale;
use crate::rt::ocaml_unix;
use crate::telemetry;
use crate::utils;
use crate::yojson::safe as yojson;

/// `Exit_status.t`
pub enum T {
    NoError,
    InputError,
    KillError,
    NoServerRunningShouldRetry,
    ServerHungUpShouldRetry(Option<Box<FinaleData>>),
    ServerHungUpShouldAbort(Option<Box<FinaleData>>),
    OutOfTime,
    OutOfRetries,
    ServerAlreadyExists,
    TypeError,
    BuildIdMismatch,
    MonitorConnectionFailure,
    UnusedServer,
    LockStolen,
    LostParentMonitor,
    ServerGotEofFromMonitor,
    /// hh_client installs a SIGINT handler which raises [Exit_with Interrupted].
    /// Also, MonitorMain installs SIGINT, SIGQUIT, SIGTERM, SIGHUP handlers which
    /// call [Exit.exit Interrupted].
    Interrupted,
    /// hh_client code tried to write to stdout, but was thwarted by Sys_error("Broken pipe")
    ClientBrokenPipe,
    WorkerOomed,
    WorkerBusy,
    /// An uncaught Not_found exception in the worker.
    WorkerNotFoundException,
    WorkerFailedToSendJob,
    SocketError,
    MissingHhi,
    DfindDied,
    DfindUnresponsive,
    EventLoggerTimeout,
    EventLoggerRestartOutOfRetries,
    EventLoggerBrokenPipe,
    CantRunAI,
    /// Watchman_failed is used both as an exit status from hh_client because this
    /// means it can't safely compute streaming errors,
    /// and also as an exit status from server/monitor because it'ss faster to exit the server
    /// (and have the Monitor restart the server) on a Watchman fresh instance than to compute
    /// the files that have been deleted and do an incremental check.
    WatchmanFailed,
    WatchmanFreshInstance,
    WatchmanInvalidResult,
    /// The EdenFS watcher failed in a way that we cannot recover from
    EdenfsWatcherFailed,
    /// Eden reported that it is intentionally shutting down.
    EdenfsWatcherEdenShuttingDown,
    /// Similar to Watchman_fresh_instance (and some instances of Watchman_failed):
    /// Eden told us that it may have lost track of changes (e.g., due to an Eden restart),
    /// so we cannot be sure what files need to be re-checked.
    EdenfsWatcherLostChanges,
    /// hh_distc (the distributed type checker) failed in a way we cannot
    /// recover from. Common causes: Remote Execution RESOURCE_EXHAUSTED
    /// quota throttling, RE network errors, decl/typecheck phase failures.
    /// Sub-classify by string-matching the logged error message in Scuba.
    /// The log data is prefixed with [spawn] or [runtime] to identify
    /// which phase of the distc run failed.
    DistcFailed,
    FileProviderStale,
    DepgraphUnavailable,
    HhconfigDeleted,
    HhconfigChanged,
    PackageConfigChanged,
    /// an exit status of hh_client check, e.g. because files-on-disk changed
    TypecheckRestarted,
    /// an exit status of hh_client check, e.g. because the server was killed mid-check
    TypecheckAbandoned,
    ServerShuttingDownDueToSigusr2,
    IDEMalformedRequest,
    IDENoServer,
    IDEOutOfRetries,
    NfsRoot,
    IDEInitFailure,
    IDETypecheckerDied,
    RedeclHeapOverflow,
    OutOfSharedMemory,
    SharedMemAssertionFailure,
    HashTableFull,
    IDENewClientConnected,
    LazyDeclBug,
    DeclHeapElemsBug,
    ParserHeapBuildError,
    HeapFull,
    SqlAssertionFailure,
    LocalTypeEnvStale,
    SqlCantopen,
    SqlCorrupt,
    SqlMisuse,
    UncaughtException(exception::T),
    DeclNotFound,
    BigRebaseDetected,
    FailedToLoadShouldRetry,
    FailedToLoadShouldAbort,
    ServerNonOptBuildMode,
    NotRestartingServerWithPrecomputedSavedState,
    ConfigError,
    /// hh_client command-line arguments could not be parsed or its root was invalid.
    ClientBadArgs,
}

/// `Exit_status.finale_data`
pub struct FinaleData {
    /// exit_status is shown to the user in CLI and LSP,
    /// just so they have an error code they can quote back at
    /// developers. It's also used by hh_client to decide, on the
    /// basis of that hh_server exit_status, whether to auto-restart
    /// hh_server or not. And it appears in logs and telemetry.
    pub exit_status: T,
    /// msg is a human-readable message for the end-user to explain why
    /// hh_server stopped. It appears in the CLI, and in LSP in a
    /// hover tooltip. It also is copied into the logs.
    pub msg: Option<String>,
    pub stack: utils::Callstack,
    /// telemetry is unstructured data, for logging, not shown to users
    pub telemetry: Option<telemetry::T>,
}

/// `exception Exit_with of t`
pub struct ExitWith(pub T);

impl fmt::Debug for ExitWith {
    /// The printer registered with `Exception.register_printer`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Exit_status.Exit_with({})", show(&self.0))
    }
}

impl fmt::Debug for T {
    /// `show`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&show(self))
    }
}

impl fmt::Debug for FinaleData {
    /// `show_finale_data`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&show_finale_data(self))
    }
}

/// The OCaml name of the constructor of `t`.
pub(crate) fn constructor_name(t: &T) -> &'static str {
    match t {
        T::NoError => "No_error",
        T::InputError => "Input_error",
        T::KillError => "Kill_error",
        T::NoServerRunningShouldRetry => "No_server_running_should_retry",
        T::ServerHungUpShouldRetry(_) => "Server_hung_up_should_retry",
        T::ServerHungUpShouldAbort(_) => "Server_hung_up_should_abort",
        T::OutOfTime => "Out_of_time",
        T::OutOfRetries => "Out_of_retries",
        T::ServerAlreadyExists => "Server_already_exists",
        T::TypeError => "Type_error",
        T::BuildIdMismatch => "Build_id_mismatch",
        T::MonitorConnectionFailure => "Monitor_connection_failure",
        T::UnusedServer => "Unused_server",
        T::LockStolen => "Lock_stolen",
        T::LostParentMonitor => "Lost_parent_monitor",
        T::ServerGotEofFromMonitor => "Server_got_eof_from_monitor",
        T::Interrupted => "Interrupted",
        T::ClientBrokenPipe => "Client_broken_pipe",
        T::WorkerOomed => "Worker_oomed",
        T::WorkerBusy => "Worker_busy",
        T::WorkerNotFoundException => "Worker_not_found_exception",
        T::WorkerFailedToSendJob => "Worker_failed_to_send_job",
        T::SocketError => "Socket_error",
        T::MissingHhi => "Missing_hhi",
        T::DfindDied => "Dfind_died",
        T::DfindUnresponsive => "Dfind_unresponsive",
        T::EventLoggerTimeout => "EventLogger_Timeout",
        T::EventLoggerRestartOutOfRetries => "EventLogger_restart_out_of_retries",
        T::EventLoggerBrokenPipe => "EventLogger_broken_pipe",
        T::CantRunAI => "CantRunAI",
        T::WatchmanFailed => "Watchman_failed",
        T::WatchmanFreshInstance => "Watchman_fresh_instance",
        T::WatchmanInvalidResult => "Watchman_invalid_result",
        T::EdenfsWatcherFailed => "Edenfs_watcher_failed",
        T::EdenfsWatcherEdenShuttingDown => "Edenfs_watcher_eden_shutting_down",
        T::EdenfsWatcherLostChanges => "Edenfs_watcher_lost_changes",
        T::DistcFailed => "Distc_failed",
        T::FileProviderStale => "File_provider_stale",
        T::DepgraphUnavailable => "Depgraph_unavailable",
        T::HhconfigDeleted => "Hhconfig_deleted",
        T::HhconfigChanged => "Hhconfig_changed",
        T::PackageConfigChanged => "Package_config_changed",
        T::TypecheckRestarted => "Typecheck_restarted",
        T::TypecheckAbandoned => "Typecheck_abandoned",
        T::ServerShuttingDownDueToSigusr2 => "Server_shutting_down_due_to_sigusr2",
        T::IDEMalformedRequest => "IDE_malformed_request",
        T::IDENoServer => "IDE_no_server",
        T::IDEOutOfRetries => "IDE_out_of_retries",
        T::NfsRoot => "Nfs_root",
        T::IDEInitFailure => "IDE_init_failure",
        T::IDETypecheckerDied => "IDE_typechecker_died",
        T::RedeclHeapOverflow => "Redecl_heap_overflow",
        T::OutOfSharedMemory => "Out_of_shared_memory",
        T::SharedMemAssertionFailure => "Shared_mem_assertion_failure",
        T::HashTableFull => "Hash_table_full",
        T::IDENewClientConnected => "IDE_new_client_connected",
        T::LazyDeclBug => "Lazy_decl_bug",
        T::DeclHeapElemsBug => "Decl_heap_elems_bug",
        T::ParserHeapBuildError => "Parser_heap_build_error",
        T::HeapFull => "Heap_full",
        T::SqlAssertionFailure => "Sql_assertion_failure",
        T::LocalTypeEnvStale => "Local_type_env_stale",
        T::SqlCantopen => "Sql_cantopen",
        T::SqlCorrupt => "Sql_corrupt",
        T::SqlMisuse => "Sql_misuse",
        T::UncaughtException(_) => "Uncaught_exception",
        T::DeclNotFound => "Decl_not_found",
        T::BigRebaseDetected => "Big_rebase_detected",
        T::FailedToLoadShouldRetry => "Failed_to_load_should_retry",
        T::FailedToLoadShouldAbort => "Failed_to_load_should_abort",
        T::ServerNonOptBuildMode => "Server_non_opt_build_mode",
        T::NotRestartingServerWithPrecomputedSavedState => {
            "Not_restarting_server_with_precomputed_saved_state"
        }
        T::ConfigError => "Config_error",
        T::ClientBadArgs => "Client_bad_args",
    }
}

/// The constructor without arguments whose OCaml name is `name`.
pub(crate) fn constant_constructor_of_name(name: &str) -> Option<T> {
    Some(match name {
        "No_error" => T::NoError,
        "Input_error" => T::InputError,
        "Kill_error" => T::KillError,
        "No_server_running_should_retry" => T::NoServerRunningShouldRetry,
        "Out_of_time" => T::OutOfTime,
        "Out_of_retries" => T::OutOfRetries,
        "Server_already_exists" => T::ServerAlreadyExists,
        "Type_error" => T::TypeError,
        "Build_id_mismatch" => T::BuildIdMismatch,
        "Monitor_connection_failure" => T::MonitorConnectionFailure,
        "Unused_server" => T::UnusedServer,
        "Lock_stolen" => T::LockStolen,
        "Lost_parent_monitor" => T::LostParentMonitor,
        "Server_got_eof_from_monitor" => T::ServerGotEofFromMonitor,
        "Interrupted" => T::Interrupted,
        "Client_broken_pipe" => T::ClientBrokenPipe,
        "Worker_oomed" => T::WorkerOomed,
        "Worker_busy" => T::WorkerBusy,
        "Worker_not_found_exception" => T::WorkerNotFoundException,
        "Worker_failed_to_send_job" => T::WorkerFailedToSendJob,
        "Socket_error" => T::SocketError,
        "Missing_hhi" => T::MissingHhi,
        "Dfind_died" => T::DfindDied,
        "Dfind_unresponsive" => T::DfindUnresponsive,
        "EventLogger_Timeout" => T::EventLoggerTimeout,
        "EventLogger_restart_out_of_retries" => T::EventLoggerRestartOutOfRetries,
        "EventLogger_broken_pipe" => T::EventLoggerBrokenPipe,
        "CantRunAI" => T::CantRunAI,
        "Watchman_failed" => T::WatchmanFailed,
        "Watchman_fresh_instance" => T::WatchmanFreshInstance,
        "Watchman_invalid_result" => T::WatchmanInvalidResult,
        "Edenfs_watcher_failed" => T::EdenfsWatcherFailed,
        "Edenfs_watcher_eden_shutting_down" => T::EdenfsWatcherEdenShuttingDown,
        "Edenfs_watcher_lost_changes" => T::EdenfsWatcherLostChanges,
        "Distc_failed" => T::DistcFailed,
        "File_provider_stale" => T::FileProviderStale,
        "Depgraph_unavailable" => T::DepgraphUnavailable,
        "Hhconfig_deleted" => T::HhconfigDeleted,
        "Hhconfig_changed" => T::HhconfigChanged,
        "Package_config_changed" => T::PackageConfigChanged,
        "Typecheck_restarted" => T::TypecheckRestarted,
        "Typecheck_abandoned" => T::TypecheckAbandoned,
        "Server_shutting_down_due_to_sigusr2" => T::ServerShuttingDownDueToSigusr2,
        "IDE_malformed_request" => T::IDEMalformedRequest,
        "IDE_no_server" => T::IDENoServer,
        "IDE_out_of_retries" => T::IDEOutOfRetries,
        "Nfs_root" => T::NfsRoot,
        "IDE_init_failure" => T::IDEInitFailure,
        "IDE_typechecker_died" => T::IDETypecheckerDied,
        "Redecl_heap_overflow" => T::RedeclHeapOverflow,
        "Out_of_shared_memory" => T::OutOfSharedMemory,
        "Shared_mem_assertion_failure" => T::SharedMemAssertionFailure,
        "Hash_table_full" => T::HashTableFull,
        "IDE_new_client_connected" => T::IDENewClientConnected,
        "Lazy_decl_bug" => T::LazyDeclBug,
        "Decl_heap_elems_bug" => T::DeclHeapElemsBug,
        "Parser_heap_build_error" => T::ParserHeapBuildError,
        "Heap_full" => T::HeapFull,
        "Sql_assertion_failure" => T::SqlAssertionFailure,
        "Local_type_env_stale" => T::LocalTypeEnvStale,
        "Sql_cantopen" => T::SqlCantopen,
        "Sql_corrupt" => T::SqlCorrupt,
        "Sql_misuse" => T::SqlMisuse,
        "Decl_not_found" => T::DeclNotFound,
        "Big_rebase_detected" => T::BigRebaseDetected,
        "Failed_to_load_should_retry" => T::FailedToLoadShouldRetry,
        "Failed_to_load_should_abort" => T::FailedToLoadShouldAbort,
        "Server_non_opt_build_mode" => T::ServerNonOptBuildMode,
        "Not_restarting_server_with_precomputed_saved_state" => {
            T::NotRestartingServerWithPrecomputedSavedState
        }
        "Config_error" => T::ConfigError,
        "Client_bad_args" => T::ClientBadArgs,
        _ => return None,
    })
}

/// `pp` (`[@@deriving show]`): `Exit_status.<constructor>`. The printers of
/// `Server_hung_up_should_retry`, `Server_hung_up_should_abort` and
/// `Uncaught_exception` print the constructor alone too.
pub fn pp(fmt: &mut Formatter, t: &T) {
    format::pp_print_string(fmt, &show(t))
}

/// `show`
pub fn show(t: &T) -> String {
    format!("Exit_status.{}", constructor_name(t))
}

/// `Utils.pp_callstack` (`type callstack = Callstack of string [@@deriving
/// show]`), which `crate::utils` does not have.
fn pp_callstack(fmt: &mut Formatter, utils::Callstack(a0): &utils::Callstack) {
    // "(@[<2>Utils.Callstack@ " ... "%S" ... "@])"
    format::pp_print_string(fmt, "(");
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "Utils.Callstack");
    format::pp_print_space(fmt);
    format::pp_print_string(fmt, &sprintf_s(a0));
    format::pp_close_box(fmt);
    format::pp_print_string(fmt, ")");
}

/// `Telemetry.pp` (`type t = key_value_pair list [@@deriving show]`, the
/// list being most recent first, each value printed with
/// `Yojson.Safe.to_string`), which `crate::telemetry` does not have.
fn pp_telemetry(fmt: &mut Formatter, telemetry: &telemetry::T) {
    let pairs = match telemetry::to_yojson(telemetry) {
        yojson::T::Assoc(pairs) => pairs,
        _ => vec![],
    };
    // "@[<2>[" ... ";@ " ... "@,]@]"
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "[");
    for (i, (key, value)) in pairs.iter().rev().enumerate() {
        if i > 0 {
            format::pp_print_string(fmt, ";");
            format::pp_print_space(fmt);
        }
        // "(@[" "%S" ",@ " pp_yojson "@])"
        format::pp_print_string(fmt, "(");
        format::pp_open_box(fmt, 0);
        format::pp_print_string(fmt, &sprintf_s(key));
        format::pp_print_string(fmt, ",");
        format::pp_print_space(fmt);
        format::pp_print_string(fmt, &yojson::to_string(value));
        format::pp_close_box(fmt);
        format::pp_print_string(fmt, ")");
    }
    format::pp_print_cut(fmt);
    format::pp_print_string(fmt, "]");
    format::pp_close_box(fmt);
}

/// `pp_finale_data` (`[@@deriving show]` on the record).
pub fn pp_finale_data(fmt: &mut Formatter, x: &FinaleData) {
    // "@[%s =@ " name, the value, "@]"
    fn field(fmt: &mut Formatter, name: &str, value: impl FnOnce(&mut Formatter)) {
        format::pp_open_box(fmt, 0);
        format::pp_print_string(fmt, name);
        format::pp_print_string(fmt, " =");
        format::pp_print_space(fmt);
        value(fmt);
        format::pp_close_box(fmt);
    }
    fn sep(fmt: &mut Formatter) {
        format::pp_print_string(fmt, ";");
        format::pp_print_space(fmt);
    }
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "{ ");
    field(fmt, "Exit_status.exit_status", |fmt| pp(fmt, &x.exit_status));
    sep(fmt);
    field(fmt, "msg", |fmt| match &x.msg {
        None => format::pp_print_string(fmt, "None"),
        Some(msg) => {
            format::pp_print_string(fmt, "(Some ");
            format::pp_print_string(fmt, &sprintf_s(msg));
            format::pp_print_string(fmt, ")");
        }
    });
    sep(fmt);
    field(fmt, "stack", |fmt| pp_callstack(fmt, &x.stack));
    sep(fmt);
    field(fmt, "telemetry", |fmt| match &x.telemetry {
        None => format::pp_print_string(fmt, "None"),
        Some(telemetry) => {
            format::pp_print_string(fmt, "(Some ");
            pp_telemetry(fmt, telemetry);
            format::pp_print_string(fmt, ")");
        }
    });
    format::pp_print_space(fmt);
    format::pp_print_string(fmt, "}");
    format::pp_close_box(fmt);
}

/// `show_finale_data`
pub fn show_finale_data(x: &FinaleData) -> String {
    format::asprintf(|fmt| pp_finale_data(fmt, x))
}

/// Please note that AI(zoncolan) calls hack and might exit with these codes,
/// and also uses own defined codes from ai_exit_status.ml.
/// When adding a new code here, ensure not to overlap with ai_exit_status
pub fn exit_code(t: &T) -> isize {
    match t {
        // standard unix exit code for SIGINT, generated by hh_client.
        // Also generated by MonitorMain for a SIGINT, SIGTERM, SIGHUP, SIGQUIT.
        T::Interrupted => 130,
        // standard unix code for SIGPIPE, generated by hh_client
        T::ClientBrokenPipe => 141,
        T::NoError => 0,
        // used in clientStop/Start/Restart
        T::KillError => 1,
        // used in server
        T::ServerShuttingDownDueToSigusr2 => 1,
        // CARE! exit code 2 is also used when an ocaml binary exits
        // with an unhandled exception. It's a shame that we can't distinguish
        // such exits from the following two codes.
        // used in clientCheck
        T::TypeError => 2,
        T::UncaughtException(_) => 221,
        T::HhconfigChanged => 4,
        T::PackageConfigChanged => 4,
        // gen by clientCheck/clientCheckStatus, read by find_hh.sh
        T::TypecheckRestarted => 19,
        // gen by clientCheck/clientCheckStatus, read by find_hh.sh
        T::TypecheckAbandoned => 20,
        T::UnusedServer => 5,
        // gen by clientConnect, read by find_hh.sh
        T::NoServerRunningShouldRetry => 6,
        // gen by clientConnect, read by find_hh.sh
        T::ServerHungUpShouldRetry(_) => 6,
        T::OutOfTime => 7,
        T::OutOfRetries => 7,
        T::BuildIdMismatch => 9,
        T::MonitorConnectionFailure => 9,
        T::InputError => 10,
        T::LockStolen => 11,
        T::LostParentMonitor => 12,
        T::ServerGotEofFromMonitor => 18,
        T::SharedMemAssertionFailure => 14,
        T::OutOfSharedMemory => 15,
        T::HashTableFull => 16,
        T::HeapFull => 17,
        T::WorkerOomed => 30,
        T::WorkerBusy => 31,
        T::WorkerNotFoundException => 32,
        T::WorkerFailedToSendJob => 33,
        T::ServerAlreadyExists => 77,
        T::MissingHhi => 97,
        T::SocketError => 98,
        T::DfindDied => 99,
        T::DfindUnresponsive => 100,
        T::EventLoggerTimeout => 101,
        T::CantRunAI => 102,
        T::WatchmanFailed => 103,
        T::HhconfigDeleted => 104,
        T::EventLoggerBrokenPipe => 106,
        T::RedeclHeapOverflow => 107,
        T::EventLoggerRestartOutOfRetries => 108,
        T::WatchmanFreshInstance => 109,
        T::WatchmanInvalidResult => 110,
        T::BigRebaseDetected => 111,
        T::IDEMalformedRequest => 201,
        T::IDENoServer => 202,
        T::IDEOutOfRetries => 203,
        T::NfsRoot => 204,
        T::IDEInitFailure => 205,
        T::IDETypecheckerDied => 206,
        T::IDENewClientConnected => 207,
        T::LazyDeclBug => 208,
        T::DeclHeapElemsBug => 209,
        T::ParserHeapBuildError => 210,
        T::FileProviderStale => 211,
        T::SqlAssertionFailure => 212,
        T::LocalTypeEnvStale => 213,
        T::SqlCantopen => 214,
        T::SqlCorrupt => 215,
        T::SqlMisuse => 216,
        T::DeclNotFound => 217,
        // gen by serverInit, read by serverMonitor+clientConnect
        T::FailedToLoadShouldRetry => 218,
        // gen by serverInit, read by serverMonitor+clientConnect
        T::FailedToLoadShouldAbort => 219,
        // generated by clientConnect, read by find_hh.sh
        T::ServerHungUpShouldAbort(_) => 220,
        T::ServerNonOptBuildMode => 222,
        T::NotRestartingServerWithPrecomputedSavedState => 223,
        T::ConfigError => 224,
        T::EdenfsWatcherFailed => 225,
        // Zoncolan uses 231.
        T::EdenfsWatcherEdenShuttingDown => 232,
        // Zoncolan uses 226 and 227, skipping
        T::EdenfsWatcherLostChanges => 228,
        T::DistcFailed => 229,
        // EX_USAGE from sysexits.h
        T::ClientBadArgs => 64,
        T::DepgraphUnavailable => 230,
    }
}

/// `Failure "dummy"`, as `Printexc.to_string` shows it.
#[derive(Debug)]
#[allow(dead_code)]
struct Failure(String);

pub fn exit_code_to_string(code: isize) -> String {
    // We will return the string "See Exit_status.ml for meaning of this code".
    // But, let's hard-code a few of the more common ones just as a convenience
    // to the reader.
    let common_codes = [
        T::Interrupted,
        T::ClientBrokenPipe,
        T::NoError,
        T::KillError,
        T::TypeError,
        T::UncaughtException(exception::wrap(Failure("dummy".to_string()))),
        T::HhconfigChanged,
        T::PackageConfigChanged,
        T::TypecheckRestarted,
        T::TypecheckAbandoned,
        T::NoServerRunningShouldRetry,
        T::ServerHungUpShouldRetry(None),
        T::OutOfTime,
        T::OutOfRetries,
        T::BuildIdMismatch,
        T::MonitorConnectionFailure,
        T::FailedToLoadShouldRetry,
        T::FailedToLoadShouldAbort,
        T::ServerHungUpShouldAbort(None),
        T::WatchmanFailed,
        T::EdenfsWatcherFailed,
        T::EdenfsWatcherEdenShuttingDown,
        T::ServerNonOptBuildMode,
        T::DistcFailed,
        T::ClientBadArgs,
        T::DepgraphUnavailable,
    ];
    let mut matches: Vec<String> = common_codes
        .iter()
        .filter_map(|exit_status| {
            if exit_code(exit_status) == code {
                Some(show(exit_status))
            } else {
                None
            }
        })
        .collect();
    // If an ocaml binary exits with an uncaught exception, it produces exit code 2.
    // We'll reconstruct that fact here. However our binaries should avoid exiting
    // in this manner, since exit code 2 also means "hh_check completed successfully"!
    if code == 2 {
        matches.insert(0, "Uncaught_exception_ocaml".to_string());
    }
    if matches.is_empty() {
        format!("(see Exit_status.exit_code for meaning of code {})", code)
    } else {
        matches.join("/")
    }
}

/// `unpack : Unix.process_status -> string * int`, on the status of a child
/// process. The signal numbers are OCaml's (negative for the signals OCaml
/// knows; see `caml_convert_signal_number` in the OCaml runtime), as in
/// `Unix.WSIGNALED` and `Unix.WSTOPPED`.
pub fn unpack(status: ocaml_unix::ProcessStatus) -> (String, isize) {
    match status {
        ocaml_unix::ProcessStatus::WExited(n) => ("exit".to_string(), n),
        ocaml_unix::ProcessStatus::WSignaled(n) => ("signaled".to_string(), n),
        ocaml_unix::ProcessStatus::WStopped(n) => ("stopped".to_string(), n),
    }
}

/// If the server dies through a controlled exit, it leaves behind a "finale file" <pid>.fin
/// with json-formatted data describing the detailed nature of the exit including callstack.
/// This method retrieves that file, if it exists.
///
/// (The file is OCaml's marshalled data: see `crate::rt::finale`.)
pub fn get_finale_data(server_finale_file: &str) -> Option<FinaleData> {
    finale::read(server_finale_file)
}

/// like [show], but prints a lot more information including callstacks
pub fn show_expanded(t: &T) -> String {
    match t {
        T::ServerHungUpShouldAbort(Some(finale_data))
        | T::ServerHungUpShouldRetry(Some(finale_data)) => {
            let FinaleData {
                exit_status,
                msg,
                stack: utils::Callstack(stack),
                telemetry,
            } = &**finale_data;
            let telemetry = telemetry
                .as_ref()
                .map(|telemetry| telemetry::to_string(None, telemetry))
                .unwrap_or_default();
            format!(
                "{} exit_code={} [{}] {} {}\n{}",
                show(t),
                exit_code(t),
                show(exit_status),
                msg.as_deref().unwrap_or(""),
                telemetry,
                exception::clean_stack(stack)
            )
        }
        T::UncaughtException(e) => format!(
            "{} exit_code={} [{}]\n{}",
            show(t),
            exit_code(t),
            exception::get_ctor_string(e),
            exception::clean_stack(&exception::get_backtrace_string(e))
        ),
        _ => format!("{} exit_code={}", show(t), exit_code(t)),
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// Every constructor without arguments, in the OCaml order.
    fn constant_constructors() -> Vec<T> {
        vec![
            T::NoError,
            T::InputError,
            T::KillError,
            T::NoServerRunningShouldRetry,
            T::OutOfTime,
            T::OutOfRetries,
            T::ServerAlreadyExists,
            T::TypeError,
            T::BuildIdMismatch,
            T::MonitorConnectionFailure,
            T::UnusedServer,
            T::LockStolen,
            T::LostParentMonitor,
            T::ServerGotEofFromMonitor,
            T::Interrupted,
            T::ClientBrokenPipe,
            T::WorkerOomed,
            T::WorkerBusy,
            T::WorkerNotFoundException,
            T::WorkerFailedToSendJob,
            T::SocketError,
            T::MissingHhi,
            T::DfindDied,
            T::DfindUnresponsive,
            T::EventLoggerTimeout,
            T::EventLoggerRestartOutOfRetries,
            T::EventLoggerBrokenPipe,
            T::CantRunAI,
            T::WatchmanFailed,
            T::WatchmanFreshInstance,
            T::WatchmanInvalidResult,
            T::EdenfsWatcherFailed,
            T::EdenfsWatcherEdenShuttingDown,
            T::EdenfsWatcherLostChanges,
            T::DistcFailed,
            T::FileProviderStale,
            T::DepgraphUnavailable,
            T::HhconfigDeleted,
            T::HhconfigChanged,
            T::PackageConfigChanged,
            T::TypecheckRestarted,
            T::TypecheckAbandoned,
            T::ServerShuttingDownDueToSigusr2,
            T::IDEMalformedRequest,
            T::IDENoServer,
            T::IDEOutOfRetries,
            T::NfsRoot,
            T::IDEInitFailure,
            T::IDETypecheckerDied,
            T::RedeclHeapOverflow,
            T::OutOfSharedMemory,
            T::SharedMemAssertionFailure,
            T::HashTableFull,
            T::IDENewClientConnected,
            T::LazyDeclBug,
            T::DeclHeapElemsBug,
            T::ParserHeapBuildError,
            T::HeapFull,
            T::SqlAssertionFailure,
            T::LocalTypeEnvStale,
            T::SqlCantopen,
            T::SqlCorrupt,
            T::SqlMisuse,
            T::DeclNotFound,
            T::BigRebaseDetected,
            T::FailedToLoadShouldRetry,
            T::FailedToLoadShouldAbort,
            T::ServerNonOptBuildMode,
            T::NotRestartingServerWithPrecomputedSavedState,
            T::ConfigError,
            T::ClientBadArgs,
        ]
    }

    #[test]
    fn constructors_round_trip_through_their_names() {
        let all = constant_constructors();
        // 74 constructors, 3 of them with an argument.
        assert_eq!(all.len(), 71);
        for t in &all {
            let name = constructor_name(t);
            let back = constant_constructor_of_name(name).unwrap();
            assert_eq!(show(&back), show(t));
            assert_eq!(exit_code(&back), exit_code(t));
            let json = finale::yojson_of_t(t);
            assert_eq!(show(&finale::t_of_yojson(&json).unwrap()), show(t));
            let v = finale::t_to_ocaml(t);
            assert_eq!(show(&finale::t_of_ocaml(&v).unwrap()), show(t));
        }
    }

    #[test]
    fn show_as_the_tests_expect() {
        // test/client_args_telemetry/*.json.exp, test/integration_ml.
        assert_eq!(show(&T::ClientBadArgs), "Exit_status.Client_bad_args");
        assert_eq!(show(&T::InputError), "Exit_status.Input_error");
        assert_eq!(show(&T::TypecheckRestarted), "Exit_status.Typecheck_restarted");
        assert_eq!(show(&T::TypeError), "Exit_status.Type_error");
        assert_eq!(
            show(&T::FailedToLoadShouldAbort),
            "Exit_status.Failed_to_load_should_abort"
        );
        assert_eq!(
            show(&T::ServerHungUpShouldRetry(None)),
            "Exit_status.Server_hung_up_should_retry"
        );
        assert_eq!(
            show(&T::ServerHungUpShouldAbort(Some(Box::new(sample_finale_data())))),
            "Exit_status.Server_hung_up_should_abort"
        );
        assert_eq!(
            show(&T::UncaughtException(exception::wrap(Failure("x".into())))),
            "Exit_status.Uncaught_exception"
        );
        assert_eq!(
            format!("{:?}", ExitWith(T::InputError)),
            "Exit_status.Exit_with(Exit_status.Input_error)"
        );
        let e = exception::wrap(ExitWith(T::InputError));
        assert_eq!(
            exception::get_ctor_string(&e),
            "Exit_status.Exit_with(Exit_status.Input_error)"
        );
    }

    #[test]
    fn exit_codes() {
        // design 4.5
        for (t, code) in [
            (T::NoError, 0),
            (T::KillError, 1),
            (T::TypeError, 2),
            (T::HhconfigChanged, 4),
            (T::NoServerRunningShouldRetry, 6),
            (T::ServerHungUpShouldRetry(None), 6),
            (T::OutOfTime, 7),
            (T::BuildIdMismatch, 9),
            (T::InputError, 10),
            (T::TypecheckRestarted, 19),
            (T::TypecheckAbandoned, 20),
            (T::ClientBadArgs, 64),
            (T::Interrupted, 130),
            (T::ClientBrokenPipe, 141),
            (T::FailedToLoadShouldRetry, 218),
            (T::FailedToLoadShouldAbort, 219),
            (T::ServerHungUpShouldAbort(None), 220),
            (T::UncaughtException(exception::wrap(Failure("x".into()))), 221),
            (T::DistcFailed, 229),
            (T::DepgraphUnavailable, 230),
        ] {
            assert_eq!(exit_code(&t), code, "{}", show(&t));
        }
    }

    #[test]
    fn exit_code_to_string_joins_the_common_codes() {
        assert_eq!(exit_code_to_string(0), "Exit_status.No_error");
        assert_eq!(
            exit_code_to_string(2),
            "Uncaught_exception_ocaml/Exit_status.Type_error"
        );
        assert_eq!(
            exit_code_to_string(6),
            "Exit_status.No_server_running_should_retry/Exit_status.Server_hung_up_should_retry"
        );
        assert_eq!(
            exit_code_to_string(4),
            "Exit_status.Hhconfig_changed/Exit_status.Package_config_changed"
        );
        assert_eq!(exit_code_to_string(221), "Exit_status.Uncaught_exception");
        assert_eq!(
            exit_code_to_string(42),
            "(see Exit_status.exit_code for meaning of code 42)"
        );
        // Not among the common codes.
        assert_eq!(
            exit_code_to_string(204),
            "(see Exit_status.exit_code for meaning of code 204)"
        );
    }

    #[test]
    fn unpack_statuses() {
        let status = std::process::Command::new("sh")
            .args(["-c", "exit 3"])
            .status()
            .unwrap();
        let status = ocaml_unix::ProcessStatus::of_raw(std::os::unix::process::ExitStatusExt::into_raw(status));
        assert_eq!(unpack(status), ("exit".to_string(), 3));
        let status = std::process::Command::new("sh")
            .args(["-c", "kill -KILL $$"])
            .status()
            .unwrap();
        let status = ocaml_unix::ProcessStatus::of_raw(std::os::unix::process::ExitStatusExt::into_raw(status));
        assert_eq!(unpack(status), ("signaled".to_string(), -7));
    }

    pub(crate) fn sample_finale_data() -> FinaleData {
        let telemetry = telemetry::int_(
            "b",
            2,
            telemetry::string_(None, "a", "x", telemetry::create()),
        );
        FinaleData {
            exit_status: T::HhconfigChanged,
            msg: Some("hh.conf changed".to_string()),
            stack: utils::Callstack("Raised at a.ml".to_string()),
            telemetry: Some(telemetry),
        }
    }

    #[test]
    fn show_expanded_formats() {
        assert_eq!(show_expanded(&T::TypeError), "Exit_status.Type_error exit_code=2");
        let t = T::ServerHungUpShouldRetry(Some(Box::new(sample_finale_data())));
        assert_eq!(
            show_expanded(&t),
            "Exit_status.Server_hung_up_should_retry exit_code=6 [Exit_status.Hhconfig_changed] hh.conf changed {\"a\":\"x\",\"b\":2}\nRaised at a.ml"
        );
        // Without finale data: the last case.
        assert_eq!(
            show_expanded(&T::ServerHungUpShouldAbort(None)),
            "Exit_status.Server_hung_up_should_abort exit_code=220"
        );
        // No message and no telemetry: `"%s %s\n"` of two empty strings.
        let t = T::ServerHungUpShouldAbort(Some(Box::new(FinaleData {
            exit_status: T::NoError,
            msg: None,
            stack: utils::Callstack("x".to_string()),
            telemetry: None,
        })));
        assert_eq!(
            show_expanded(&t),
            "Exit_status.Server_hung_up_should_abort exit_code=220 [Exit_status.No_error]  \nx"
        );
        let e = T::UncaughtException(exception::wrap(Failure("boom".into())));
        assert!(
            show_expanded(&e)
                .starts_with("Exit_status.Uncaught_exception exit_code=221 [Failure(\"boom\")]\n")
        );
    }

    #[test]
    fn show_finale_data_as_ppx_deriving() {
        let d = FinaleData {
            exit_status: T::NoError,
            msg: None,
            stack: utils::Callstack("x".to_string()),
            telemetry: None,
        };
        assert_eq!(
            show_finale_data(&d),
            "{ Exit_status.exit_status = Exit_status.No_error; msg = None;\n  stack = (Utils.Callstack \"x\"); telemetry = None }"
        );
        let d = FinaleData {
            exit_status: T::NoError,
            msg: Some("m".to_string()),
            stack: utils::Callstack(String::new()),
            telemetry: Some(telemetry::int_("k", 1, telemetry::create())),
        };
        assert_eq!(
            show_finale_data(&d),
            "{ Exit_status.exit_status = Exit_status.No_error; msg = (Some \"m\");\n  stack = (Utils.Callstack \"\"); telemetry = (Some [(\"k\", 1)]) }"
        );
    }
}
