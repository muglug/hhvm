// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`. See `hh/PORTING.md`.
//!
//! All hack-specific code relating to LSP goes in here.
//!
//! The module is split: the per-request handlers are in `client_lsp/`, one
//! file per OCaml handler (or group of functions that only serve one
//! request), with the OCaml's function names.
//!
//! # One OCaml thread of Lwt, several Rust threads
//!
//! The OCaml is a single-threaded Lwt program: the main loop, the
//! once-a-second `background_status_refresher`, the continuation of
//! `run_ide_service`, the cancellation watcher of `respect_cancellation` and
//! the shell-outs are promises, and only one of them runs at a time; they
//! switch at the points where a promise waits (an `ide_rpc`, the wait for
//! the next event, a sleep). Here they are threads, and [`lwt`] is the
//! one OCaml thread: a lock that the main loop holds except while it waits
//! at one of those points ([`lwt::yield_during`]), and that the other
//! threads take for what they do between their own waits
//! ([`lwt::with_lock`]). So the messages on stdout come in an order the
//! OCaml can produce, and the global state below is never seen half-done.
//!
//! The IDE daemon is a thread of this process, with the same
//! log files (`.client_lsp_log`, `.client_ide_log`).
//!
//! `Hack_event_logger` and `Event_logger` calls are no-ops in the
//! open-source build: omitted (`log_response_if_necessary` and the
//! telemetry half of `hack_log_error` are only those calls).
//!
//! OCaml exceptions are the [`Exn`] of a `Result`, or panics (the
//! `failwith`s, and the exceptions of other modules); the main loop catches
//! both, as its `try%lwt ... with` does.

use std::cell::Cell;
use std::io::Write;
use std::os::unix::fs::MetadataExt;
use std::panic::AssertUnwindSafe;
use std::sync::Arc;
use std::sync::LazyLock;
use std::sync::Mutex;
use std::sync::RwLock;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::Instant;

use crossbeam_channel::Receiver;
use crossbeam_channel::Select;
use crossbeam_channel::Sender;

use crate::client_ide_message;
use crate::client_ide_message::Diagnostic;
use crate::client_ide_message::IdeResult;
use crate::client_ide_message::Notification;
use crate::client_ide_message::RichError;
use crate::client_ide_service;
use crate::client_start;
use crate::client_stop;
use crate::exception;
use crate::file_content;
use crate::filter_diagnostics;
use crate::find_refs_wire_format;
use crate::find_refs_wire_format::HalfOpenOneBased;
use crate::find_utils;
use crate::hh_json_helpers::jget;
use crate::hh_logger;
use crate::http_lite;
use crate::ide_api_types;
use crate::jsonrpc;
use crate::lsp;
use crate::lsp::DocumentUri;
use crate::lsp::LspId;
use crate::lsp::LspMessage;
use crate::lsp::LspNotification;
use crate::lsp::LspRequest;
use crate::lsp::LspResult;
use crate::lsp::error;
use crate::lsp::initialize;
use crate::lsp::message_type;
use crate::lsp::publish_diagnostics;
use crate::lsp::show_status_fb;
use crate::lsp::text_document_item;
use crate::lsp::uri_map;
use crate::lsp::uri_set;
use crate::lsp_fmt;
use crate::lsp_helpers;
use crate::markdown_lite;
use crate::marshal_tools::RemoteExceptionData;
use crate::path;
use crate::pos;
use crate::random_id;
use crate::relative_path;
use crate::rt::ocaml_unix;
use crate::search_types;
use crate::server_command_types;
use crate::server_config;
use crate::server_files;
use crate::server_local_config;
use crate::server_progress;
use crate::server_progress::CompletionReason;
use crate::server_progress::Disposition;
use crate::server_progress::errors_read;
use crate::server_progress::errors_read::ReadResult;
use crate::server_progress_lwt;
use crate::server_progress_lwt::WatchError;
use crate::server_rename_types;
use crate::symbol_definition;
use crate::telemetry;
use crate::user_diagnostic;
use crate::utils;
use crate::worker_cancel;
use crate::wwwroot;
use crate::yojson::safe as yojson;

// The request handlers, one file per OCaml function (or group of
// functions that only serve one request).
pub(crate) mod do_autoclose;
pub(crate) mod do_code_action;
pub(crate) mod do_completion;
pub(crate) mod do_definition;
pub(crate) mod do_document_rename;
pub(crate) mod do_document_symbol;
pub(crate) mod do_find_references;
pub(crate) mod do_formatting;
pub(crate) mod do_go_to_implementation;
pub(crate) mod do_highlight;
pub(crate) mod do_hover;
pub(crate) mod do_resolve;
pub(crate) mod do_signature_help;
pub(crate) mod do_top_level_def_name_at_pos;
pub(crate) mod do_type_definition;
pub(crate) mod do_workspace_symbol;
#[cfg(test)]
mod tests;

/// `Client_lsp.args`
#[derive(Clone, Debug, PartialEq)]
pub struct Args {
    /// The source where the client was spawned from, i.e. nuclide, vim, emacs, etc.
    pub from: String,
    /// --config overrides at the command-line
    pub config: Vec<(String, String)>,
    pub disable_format_on_save: bool,
    pub ignore_hh_version: bool,
    pub naming_table: Option<String>,
    pub warnings_saved_state_path: Option<path::T>,
    /// Notebook mode. The *only* thing this does is filter out error messages that are not relevant for notebooks.
    /// Important:
    /// 1. The *key* difference between notebooks and IDEs is that top-level statements are allowed
    /// 2. To preserve (1) and keep our testing surface area small: do not propagate this option outside of Client_lsp:
    ///    parsing, elab, type-checking, etc. should not know about notebooks.
    pub notebook_mode: bool,
    /// Extra logging, including logs per LSP message (voluminous!)
    pub verbose: bool,
    /// clientLsp only ever uses the root path provided to us in the initialize request.
    /// This field here isn't that! it's a record of what root was derived upon launch
    /// (well before the initialize request), either from an argument if supplied, or
    /// otherwise by searching from the CWD. We use this field solely to validate
    /// whether there's a mismatch between the project root implied by how we launched,
    /// and the project root supplied by initialize, in case we want to warn about
    /// any difference.
    pub root_from_cli: path::T,
}

/// `env`
#[derive(Clone, Debug)]
pub(crate) struct Env {
    pub args: Args,
    pub root: path::T,
    pub hhconfig_version_and_switch: String,
    pub local_config: server_local_config::T,
}

/// We're storing [env] as global state. It gets initialized right at the start of [main].
/// But we have to fill it with some kind of dummy default, for sake of the type system.
static ENV: LazyLock<RwLock<Arc<Env>>> = LazyLock::new(|| {
    RwLock::new(Arc::new(Env {
        args: Args {
            from: "[init]".to_string(),
            config: vec![],
            disable_format_on_save: false,
            ignore_hh_version: false,
            naming_table: None,
            warnings_saved_state_path: None,
            notebook_mode: false,
            verbose: false,
            root_from_cli: path::dummy_path(),
        },
        root: path::dummy_path(),
        hhconfig_version_and_switch: "[init]".to_string(),
        local_config: crate::server_local_config_load::default(),
    }))
});

/// `!env`
pub(crate) fn env() -> Arc<Env> {
    Arc::clone(&ENV.read().unwrap_or_else(|e| e.into_inner()))
}

fn set_env(e: Env) {
    *ENV.write().unwrap_or_else(|e| e.into_inner()) = Arc::new(e);
}

/// When did this binary start?
static BINARY_START_TIME: LazyLock<f64> = LazyLock::new(ocaml_unix::gettimeofday);

// ~~ Protocol orchestration & helpers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub(crate) const SEE_OUTPUT_HACK: &str = " See Output\u{203A}Hack for details."; // chevron

pub(crate) const FIX_BY_RUNNING_HH: &str = "Try running `hh` at the command-line.";

/// Metadata of an incoming LSP message
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct IncomingMetadata {
    /// time this message arrived at stdin
    pub timestamp: f64,
    /// comes from VSCode for the user-initiated action, which might include several LSP requests. Might
    /// be "_" for LSP requests/notifications that weren't initiated by VSCode-tracked actions.
    pub activity_id: String,
    /// additional unique key, since [activity_id] might be shared between several LSP messages, or empty.
    pub tracking_suffix: String,
    /// This is just [activity_id].[tracking_suffix]. Is handy to keep it in one place.
    pub tracking_id: String,
}

/// The origin of a diagnostic
#[derive(Clone, Debug)]
pub(crate) enum DiagnosticsFrom {
    /// TEMPORARY, FOR VALIDATION ONLY. The validated flag says whether we've validated that
    /// errors-file contained the exact same errors as this list. Once we've done validation,
    /// we'll need neither.
    DiagnosticsFromClientIdeDaemon {
        diagnostics: Vec<Diagnostic>,
        validated: bool,
    },
    DiagnosticsFromErrorsFile,
}

/// `show_diagnostics_from` (`[@@deriving show { with_path = false }]`):
/// `Format.asprintf "%a" pp_diagnostics_from`.
fn show_diagnostics_from(d: &DiagnosticsFrom) -> String {
    use crate::format;
    format::asprintf(|f| match d {
        DiagnosticsFrom::DiagnosticsFromClientIdeDaemon {
            diagnostics,
            validated,
        } => {
            format::pp_open_box(f, 2);
            format::pp_print_string(f, "Diagnostics_from_clientIdeDaemon {");
            format::pp_print_cut(f);
            format::pp_open_box(f, 0);
            format::pp_print_string(f, "diagnostics =");
            format::pp_print_space(f);
            client_ide_message::show::pp_diagnostic_list(f, diagnostics);
            format::pp_close_box(f);
            format::pp_print_string(f, ";");
            format::pp_print_space(f);
            format::pp_open_box(f, 0);
            format::pp_print_string(f, "validated =");
            format::pp_print_space(f);
            format::pp_print_string(f, if *validated { "true" } else { "false" });
            format::pp_close_box(f);
            format::pp_close_box(f);
            format::pp_print_string(f, "}");
        }
        DiagnosticsFrom::DiagnosticsFromErrorsFile => {
            format::pp_print_string(f, "Diagnostics_from_errors_file")
        }
    })
}

/// The state of the errors file seeking state machine.
#[derive(Clone, Debug)]
pub(crate) enum SeekReason {
    Init,
    UnexpectedEndOfStream,
    WatchError(Shared<WatchError>),
    /// (The log message: the OCaml stores it and never reads it.)
    Completed(CompletionReason, #[allow(dead_code)] String),
    AbsentErrorsFile,
    /// (The exception, as `Printexc.to_string` prints it.)
    ErrorFileOpenExn(String),
    ErrorFileOpenError(Shared<errors_read::OpenError>, String),
}

/// A value that several states share (`WatchError` and `OpenError` hold an
/// `Exit_status.t`, which is not `Sync`).
pub(crate) struct Shared<A>(Arc<Mutex<A>>);

impl<A> Clone for Shared<A> {
    fn clone(&self) -> Self {
        Shared(Arc::clone(&self.0))
    }
}

impl<A> Shared<A> {
    fn new(a: A) -> Self {
        Shared(Arc::new(Mutex::new(a)))
    }

    fn with<R>(&self, f: impl FnOnce(&A) -> R) -> R {
        f(&self.0.lock().unwrap_or_else(|e| e.into_inner()))
    }
}

impl<A: std::fmt::Debug> std::fmt::Debug for Shared<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.with(|a| a.fmt(f))
    }
}

fn seek_reason_short_description(r: &SeekReason) -> String {
    match r {
        SeekReason::Init => "init".to_string(),
        SeekReason::UnexpectedEndOfStream => "unexpected end of stream".to_string(),
        SeekReason::AbsentErrorsFile => "errors file is absent".to_string(),
        SeekReason::WatchError(err) => {
            err.with(|err| server_progress_lwt::watch_error_short_description(err).to_string())
        }
        SeekReason::ErrorFileOpenError(err, _msg) => {
            err.with(errors_read::open_error_short_description)
        }
        SeekReason::Completed(completion, _) => {
            server_progress::completion_reason_short_description(completion)
        }
        SeekReason::ErrorFileOpenExn(_exn) => "exception opening errors file".to_string(),
    }
}

/// What the errors-file watcher puts on its stream (`(read_result,
/// watch_error) result`).
pub(crate) type ErrorsItem = Result<ReadResult, WatchError>;

/// This type describes our connection to the errors.bin file, where hh_server writes
/// errors discovered during its current typecheck.
///
/// Here's an overview of how errors_conn works:
/// 1. [handle_tick] attempts to update the global mutable [errors_conn] from [SeekingErrors] to [TailingErrors]
///    every (idle) second, by trying to open the errors file.
/// 2. If the global [errors_conn] is [TailingErrors q], when getting next event for any state,
///    an [Errors_file of read_result] event may be produced if there were new errors (read_result) in q
///    (and not other higher pri events).
/// 3. handling the [Errors_file] event consists in calling [handle_errors_file_item].
/// 4. [handle_errors_file_item] takes a [read_result] and updates the diagnostic map [Run_env.uris_with_standalone_diagnostics],
///    or switches the global mutable [error_conn] from [TrailingErrors] to [SeekingErrors] in case of error or end of file.
pub(crate) enum ErrorsConn {
    /// Haven't yet found a suitable errors.bin, but looking!
    SeekingErrors {
        /// The inode of the last errors.bin file we have dealt with, if any --
        /// we'll only attempt another seek (hence, update [seek_reason] or switch to [TailingErrors])
        /// once we find a new, different errors.bin file.
        prev_st_ino: Option<u64>,
        /// This contains the latest explanation of why we entered or remain in [SeekingErrors] state.
        seek_reason: SeekReason,
    },
    /// We are tailing this errors.bin file
    TailingErrors {
        start_time: f64,
        fd: std::fs::File,
        /// The `Lwt_stream.t`: disconnected once the watcher has ended (the
        /// stream is closed).
        q: Receiver<ErrorsItem>,
    },
}

/// What triggered the errors that we're sending right now?
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum ErrorsTrigger {
    /// After initialization is done, we send errors for all open files
    InitializeTrigger,
    /// In receipt of didOpen/didChange and similar, we update live errors
    MessageTrigger {
        message: LspMessage,
        metadata: IncomingMetadata,
    },
}

pub(crate) mod run_env {
    use super::*;

    /// A file use to stream the output of a shelled out command
    pub struct StreamFile {
        pub file: path::T,
        /// The `Lwt_stream.t`: disconnected once the watcher has ended.
        pub q: Receiver<Vec<HalfOpenOneBased>>,
        pub partial_result_token: lsp::PartialResultToken,
    }

    pub struct ShelloutStandardResponse {
        pub symbol: String,
        pub find_refs_action: server_command_types::find_refs::Action,
        /// These are results calculated by clientIdeDaemon from its open files, one entry for each open file
        pub ide_calculated_positions: uri_map::T<Vec<pos::Absolute>>,
        /// If we want streaming results out of a shellout, go here
        pub stream_file: Option<StreamFile>,
        /// We got this list of hints from clientIdeDaemon, and pass it on to our shellout
        pub hint_suffixes: Vec<String>,
    }

    /// This identifies an LSP *request* that triggered something (typically a shellout).
    /// It's strongly typed to be bound to a request, i.e. something that has an lsp_id,
    /// so we know that an LSP response is needed, and know how to respond.
    #[derive(Clone, Debug)]
    pub struct TriggeringRequest {
        pub id: LspId,
        pub metadata: IncomingMetadata,
        pub start_time_local_handle: f64,
        pub request: LspRequest,
    }

    pub enum ShellableType {
        FindRefs(ShelloutStandardResponse),
        GoToImpl(ShelloutStandardResponse),
        Rename {
            symbol_definition: symbol_definition::T<pos::Pos>,
            find_refs_action: server_command_types::find_refs::Action,
            new_name: String,
            ide_calculated_patches: Vec<server_rename_types::Patch>,
        },
    }

    /// `show_shellable_type` (`[@@deriving show]`, with the `[@opaque]`
    /// fields printed `<opaque>`).
    pub fn show_shellable_type(s: &ShellableType) -> String {
        let standard = |ctor: &str, r: &ShelloutStandardResponse| {
            format!(
                "(Client_lsp.Run_env.{}\n   {{ Client_lsp.Run_env.symbol = {:?}; find_refs_action = <opaque>;\n     ide_calculated_positions = <opaque>; stream_file = <opaque>;\n     hint_suffixes = <opaque> }})",
                ctor, r.symbol
            )
        };
        match s {
            ShellableType::FindRefs(r) => standard("FindRefs", r),
            ShellableType::GoToImpl(r) => standard("GoToImpl", r),
            ShellableType::Rename { new_name, .. } => format!(
                "Client_lsp.Run_env.Rename {{symbol_definition = <opaque>;\n  find_refs_action = <opaque>; new_name = {:?};\n  ide_calculated_patches = <opaque>}}",
                new_name
            ),
        }
    }

    pub struct CurrentHhShell {
        pub process: super::shell_out::Process,
        /// `unit Lwt.u`: resolved by dropping it ([`super::ensure_cancelled`]).
        pub cancellation_token: Option<Sender<()>>,
        pub triggering_request: TriggeringRequest,
        pub shellable_type: ShellableType,
    }

    pub struct T {
        pub editor_open_files: uri_map::T<text_document_item::T>,
        /// files which we believe should have their errors rechecked, maybe
        /// because they had a didOpen/didChange, maybe because a file on disk
        /// changed. We'll recheck them once the queue is empty. Most recent
        /// triggering request goes at the front of the list.
        pub uris_that_need_check: uri_map::T<ErrorsTrigger>,
        /// files which have received didOpen but not didClose.
        /// This isn't needed for correctness; only for validation...
        /// validation that error squiggles from clientIdeDaemon are the
        /// same *for unmodified files* as what hh_server's errors.bin says.
        pub uris_with_unsaved_changes: uri_set::T,
        /// these are diagnostics which arrived from serverless-ide or by tailing hh_server's
        /// errors.bin file, each with a timestamp of when they were discovered.
        /// THis isnt needed for correctness; only for validation...
        /// It's used during validating error squiggles from clientIdeDaemon vs errors.bin,
        /// using the timestamp to let us calculate whether a diagnostic discovered by
        /// clientIdeDaemon is more recent than one read from errors.bin.
        /// (It's also used if we fail to read a new errors.bin file to at least clean up
        /// after ourselves by deleting all the diagnostics we read from the previous one.
        /// And similarly to clean up if we get a shutdown request. We'd be fine without
        /// these two forms of clean up.
        pub uris_with_standalone_diagnostics: uri_map::T<(f64, DiagnosticsFrom)>,
        /// If a shell-out to "hh --ide-find-refs" or similar is currently underway.
        /// Invariant: if this is Some, then...
        /// (1) an LSP response will be delivered for it; when it is turned to None,
        /// either the LSP response has just been sent, or the obligation has been handed
        /// off to a method that will assuredly respond.
        /// (2) the streaming-find-refs file exists; whoever turns it to None they must
        /// also delete the file, which they can assume exists.
        pub current_hh_shell: Option<CurrentHhShell>,
    }
}

pub(crate) enum State {
    /// Pre_init: we haven't yet received the initialize request.
    PreInit,
    /// Running : this is the main state that we'll be in (after initialize request,
    /// before shutdown request) under ide_standalone.
    Running(run_env::T),
    /// Post_shutdown: we received a shutdown request from the client, and
    /// therefore shut down our connection to the server. We can't handle
    /// any more requests from the client and will close as soon as it
    /// notifies us that we can exit.
    PostShutdown,
}

fn is_post_shutdown(state: &State) -> bool {
    match state {
        State::PostShutdown => true,
        State::PreInit | State::Running(_) => false,
    }
}

/// A handler for the result of an LSP request
type ResultHandler = Arc<dyn Fn(&LspResult, &mut State) + Send + Sync>;

/// (The OCaml reads the fields only in `log_response_if_necessary`, for
/// `Hack_event_logger.client_lsp_method_handled`, which has no counterpart.)
pub(crate) struct ResultTelemetry {
    /// how many results did we send back to the user?
    #[allow(dead_code)]
    pub result_count: isize,
    /// other message-specific data
    #[allow(dead_code)]
    pub result_extra_data: Option<telemetry::T>,
    /// Should we log telemetry about this response to an LSP action immediately?
    /// (default true, in case result_telemetry isn't provided.)
    /// Or should we defer logging until some later time, e.g. [handle_shell_out_complete]?
    #[allow(dead_code)]
    pub log_immediately: bool,
}

pub(crate) fn make_result_telemetry(
    result_extra_data: Option<telemetry::T>,
    log_immediately: Option<bool>,
    count: isize,
) -> ResultTelemetry {
    ResultTelemetry {
        result_count: count,
        result_extra_data,
        log_immediately: log_immediately.unwrap_or(true),
    }
}

static INITIALIZE_PARAMS_REF: Mutex<Option<Arc<initialize::Params>>> = Mutex::new(None);

/// `!initialize_params_ref`
pub(crate) fn initialize_params() -> Option<Arc<initialize::Params>> {
    INITIALIZE_PARAMS_REF
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone()
}

/// This flag is used to control how much will be written
/// to log-files. It can be turned on initially by --verbose at the command-line or
/// setting "trace:Verbose" in initializationParams. Thereafter, it can
/// be changed by the user dynamically via $/setTraceNotification.
/// Don't alter this reference directly; instead use [set_verbose_to_file]
/// so as to pass the message on to ide_service as well.
/// Note: control for how much will be written to stderr is solely
/// controlled by --verbose at the command-line, stored in env.verbose.
static VERBOSE_TO_FILE: AtomicBool = AtomicBool::new(false);

static REQUESTS_OUTSTANDING: LazyLock<Mutex<lsp::id_map::T<(LspRequest, ResultHandler)>>> =
    LazyLock::new(|| Mutex::new(lsp::id_map::T::new()));

fn requests_outstanding() -> std::sync::MutexGuard<'static, lsp::id_map::T<(LspRequest, ResultHandler)>> {
    REQUESTS_OUTSTANDING.lock().unwrap_or_else(|e| e.into_inner())
}

/// `get_outstanding_request_exn`, without the exception: `None` where it
/// raises.
fn get_outstanding_request(id: &LspId) -> Option<LspRequest> {
    requests_outstanding().get(id).map(|(request, _)| request.clone())
}

/// hh_server pushes errors to an errors.bin file, which we tail along.
/// (Only in ide_standalone mode; we don't do anything in other modes.)
/// This variable is where we store our progress in seeking an errors.bin, or tailing
/// one we already found. It's updated
/// (1) by [handle_tick] which runs every second and may call [try_open_errors_file] to seek errors.bin;
/// (2) by [handle_errors_file_item] which tails an errors.bin file.
static LATEST_HH_SERVER_ERRORS: Mutex<ErrorsConn> = Mutex::new(ErrorsConn::SeekingErrors {
    prev_st_ino: None,
    seek_reason: SeekReason::Init,
});

fn latest_hh_server_errors() -> std::sync::MutexGuard<'static, ErrorsConn> {
    LATEST_HH_SERVER_ERRORS.lock().unwrap_or_else(|e| e.into_inner())
}

/// This is the latest state of the progress.json file, updated once a second
/// in a background Lwt process [background_status_refresher]. This file is where the
/// monitor reports its status like "starting up", and hh_server reports its status
/// like "typechecking".
static LATEST_HH_SERVER_PROGRESS: LazyLock<Mutex<server_progress::T>> = LazyLock::new(|| {
    Mutex::new(server_progress::T {
        pid: 0,
        disposition: Disposition::DWorking,
        message: "connecting".to_string(),
        timestamp: ocaml_unix::gettimeofday(),
    })
});

/// Have we already sent a status message over LSP? If so, and our new
/// status will be just the same as the previous one, we won't need to send it
/// again. This stores the most recent status that the LSP client has.
static SHOW_STATUS_OUTSTANDING: Mutex<String> = Mutex::new(String::new());

pub(crate) fn log(s: &str) {
    hh_logger::log(&format!("[client-lsp] {}", s))
}

pub(crate) fn log_debug(s: &str) {
    hh_logger::debug(None, None, &format!("[client-lsp] {}", s))
}

pub(crate) fn log_error(s: &str) {
    hh_logger::error(None, None, &format!("[client-lsp] {}", s))
}

/// The lock of stdout: one message at a time.
static STDOUT: Mutex<()> = Mutex::new(());

/// `Sys_error msg`, as `Printexc.to_string` prints it.
pub(crate) struct SysError(String);

impl std::fmt::Debug for SysError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Sys_error({:?})", self.0)
    }
}

/// The message of `Sys_error` for an I/O error: the `strerror` text.
pub(crate) fn sys_error_message(e: &std::io::Error) -> String {
    match e.raw_os_error() {
        // SAFETY: `strerror` returns a static string for any errno.
        Some(errno) => unsafe { std::ffi::CStr::from_ptr(libc::strerror(errno)) }
            .to_string_lossy()
            .into_owned(),
        None => e.to_string(),
    }
}

pub(crate) fn to_stdout(json: yojson::T) {
    // unsorted: LSP output, parsed by editor, not snapshot-tested
    let s = yojson::to_string(&json) + "\r\n\r\n";
    let _lock = STDOUT.lock().unwrap_or_else(|e| e.into_inner());
    let stdout = std::io::stdout();
    let mut stdout = stdout.lock();
    if let Err(e) = http_lite::write_message(&mut stdout, &s) {
        // `Sys_error "Broken pipe"` and the like: an exception.
        std::panic::panic_any(exception::wrap(SysError(sys_error_message(&e))));
    }
}

fn get_editor_open_files(state: &State) -> Option<&uri_map::T<text_document_item::T>> {
    match state {
        State::PreInit | State::PostShutdown => None,
        State::Running(lenv) => Some(&lenv.editor_open_files),
    }
}

/// `match get_editor_open_files state with Some files -> files | None -> UriMap.empty`
pub(crate) fn editor_open_files_or_empty(state: &State) -> uri_map::T<text_document_item::T> {
    get_editor_open_files(state).cloned().unwrap_or_default()
}

/// `Lwt.wakeup_later cancellation_token ()`, which it is fine to do more
/// than once.
pub(crate) fn ensure_cancelled(cancellation_token: &mut Option<Sender<()>>) {
    // Dropping the sender resolves the token for whoever waits on it.
    *cancellation_token = None;
}

/// The architecture of clientLsp is a single-threaded message loop inside
/// [Client_lsp.main]. The loop calls [get_next_event] to wait for the next
/// event from a variety of sources, dispatches it according to what kind of event
/// it is, and repeats until it finally receives an event that an "exit" lsp notification
/// has been received from the client.
pub(crate) enum Event {
    /// The editor e.g. VSCode might send a request or notification LSP message to us
    /// at any time. This event represents those LSP messages. The fields store
    /// raw json as well as the parsed form of it. Handled by [handle_client_message].
    ClientMessage(IncomingMetadata, LspMessage),
    /// This event represents whenever clientIdeDaemon
    /// pushes a notification to us, e.g. a progress or status update.
    /// Handled by [handle_client_ide_notification].
    DaemonNotification(Notification),
    /// Under [--config ide_standalone=true], we once a second seek out a new errors.bin
    /// file that the server has produced to accumulate errors in the current typecheck.
    /// Once we have one, we "tail -f" it until it's finished. This event signals
    /// with [Some Ok _] that new errors have been appended to the file in the current typecheck,
    /// or [Some Error _] that either the typecheck completed or hh_server failed.
    /// The [None] case never arises; it represents a logic bug, an unexpected close
    /// of the underlying [Lwt_stream.t]. All handled in [handle_errors_file_item].
    ErrorsFile(Option<ErrorsItem>),
    /// If the editor sent a find-refs-request with a partialResultsToken, then
    /// we create a partial-results file and "tail -f" it until the shell-out to "hh --ide-find-refs-by-symbol3"
    /// has finished. This event signals with [Some] that new refs have been appended to the file.
    /// The [None] case never arises; it represents a logic bug, an unexpected close
    /// of the underlying [Lwt_stream.t].
    RefsFile(Option<Vec<HalfOpenOneBased>>),
    /// Under [--config ide_standlone=true], LSP requests for rename or
    /// find-refs are accomplished by kicking off an asynchronous shell-out to
    /// "hh --refactor" or "hh --ide-find-refs". This event signals that the
    /// shell-out has completed and it's now time to process the results.
    /// Handled in [handle_shell_out_complete].
    /// Invariant: if we have one of these events, then we must eventually produce
    /// an LSP response for it.
    ShellOutComplete(
        shell_out::ProcessResult,
        run_env::TriggeringRequest,
        run_env::ShellableType,
    ),
    /// If there had been a didOpen/didChange without a subsequent didClose,
    /// and no other events are pending, we will recompute squiggles for it.
    DeferredCheck(DocumentUri, ErrorsTrigger),
    /// Once a second, if no other events are pending, we synthesize a Tick
    /// event. Handled in [handle_tick]. It does things like see if there's a new
    /// errors.bin streaming-error file to tail, and flush HackEventLogger telemetry.
    Tick,
}

fn event_to_string(event: &Event) -> String {
    match event {
        Event::ClientMessage(metadata, m) => format!(
            "Client_message(#{}: {})",
            metadata.tracking_id,
            lsp_fmt::denorm_message_to_string(m)
        ),
        Event::DaemonNotification(n) => format!(
            "Daemon_notification({})",
            client_ide_message::notification_to_string(n)
        ),
        Event::Tick => "Tick".to_string(),
        Event::RefsFile(None) => "Refs_file(anomalous end-of-stream)".to_string(),
        Event::RefsFile(Some(refs)) => format!("Refs_file({} refs)", refs.len()),
        Event::ErrorsFile(None) => "Errors_file(anomalous end-of-stream)".to_string(),
        Event::ErrorsFile(Some(Ok(ReadResult::RItem(server_progress::ErrorsFileItem::Telemetry(
            _,
        ))))) => "Errors_file: telemetry".to_string(),
        Event::ErrorsFile(Some(Ok(ReadResult::RItem(server_progress::ErrorsFileItem::Errors {
            errors,
            timestamp: _,
        })))) => match errors.iter().next() {
            None => "Errors_file(anomalous empty report)".to_string(),
            Some((file, errors_in_file)) => format!(
                "Errors_file({} errors in {}, ...)",
                errors_in_file.len(),
                relative_path::suffix(file)
            ),
        },
        Event::ErrorsFile(Some(Ok(ReadResult::RCompleted(completion, msg)))) => format!(
            "Errors_file({}{})",
            server_progress::completion_reason_short_description(completion),
            if msg.is_empty() {
                String::new()
            } else {
                format!(" [{}]", msg)
            }
        ),
        Event::ErrorsFile(Some(Err(err))) => format!(
            "Errors_file({})",
            server_progress_lwt::watch_error_short_description(err)
        ),
        Event::ShellOutComplete(..) => "Shell_out_complete".to_string(),
        Event::DeferredCheck(uri, _trigger) => {
            format!("Deferred_check({})", lsp::string_of_uri(uri))
        }
    }
}

fn is_tick(event: &Event) -> bool {
    match event {
        Event::Tick => true,
        Event::ErrorsFile(_)
        | Event::RefsFile(_)
        | Event::ShellOutComplete(..)
        | Event::ClientMessage(..)
        | Event::DaemonNotification(_)
        | Event::DeferredCheck(..) => false,
    }
}

// Here are some exit points.

/// `exit 0`
fn exit_ok() -> ! {
    exit_process(0)
}

/// `exit 1`
fn exit_fail() -> ! {
    exit_process(1)
}

/// `Stdlib.exit code`: what is buffered is flushed first (`at_exit`).
fn exit_process(code: i32) -> ! {
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
    std::process::exit(code)
}

/// The exceptions of this module, and those it catches by name.
///
/// The following connection exceptions inform the main LSP event loop how to
/// respond to an exception: was the exception a connection-related exception
/// (one of these) or did it arise during other logic (not one of these)? Can
/// we report the exception to the LSP client? Can we continue handling
/// further LSP messages or must we quit? If we quit, can we do so immediately
/// or must we delay?  --  Separately, they also help us marshal callstacks
/// across daemon- and process-boundaries.
pub(crate) enum Exn {
    ClientFatalConnectionException(RemoteExceptionData),
    ClientRecoverableConnectionException(RemoteExceptionData),
    DaemonNonfatalException(error::T),
    /// `Lsp.Error.LspException`
    LspException(error::T),
    /// Any other exception
    Other(exception::T),
}

impl std::fmt::Debug for Exn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&exn_ctor_and_stack(self).0)
    }
}

impl From<error::LspException> for Exn {
    fn from(error::LspException(e): error::LspException) -> Self {
        Exn::LspException(e)
    }
}

impl From<lsp_fmt::LspFmtError> for Exn {
    fn from(e: lsp_fmt::LspFmtError) -> Self {
        match e {
            lsp_fmt::LspFmtError::LspException(error::LspException(e)) => Exn::LspException(e),
            e => Exn::Other(exception::wrap(e)),
        }
    }
}

impl From<exception::T> for Exn {
    fn from(e: exception::T) -> Self {
        Exn::Other(e)
    }
}

/// `Failure msg`, as `Printexc.to_string` prints it.
pub(crate) struct Failure(pub String);

impl std::fmt::Debug for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failure({:?})", self.0)
    }
}

/// `failwith msg`, as an [`Exn`].
pub(crate) fn failwith(msg: &str) -> Exn {
    Exn::Other(exception::wrap(Failure(msg.to_string())))
}

/// `raise (Error.LspException { Error.code; message; data = None })`
pub(crate) fn lsp_exception(code: error::Code, message: &str) -> Exn {
    Exn::LspException(error::T {
        code,
        message: message.to_string(),
        data: None,
    })
}

/// Helper function to construct an Lsp.Error. Its goal is to gather
/// useful information in the optional freeform 'data' field. It assembles
/// that data out of any data already provided, the provided stack, and the
/// current stack. A typical scenario is that we got an error marshalled
/// from a remote server with its remote stack where the error was generated,
/// and we also want to record the stack where we received it.
pub(crate) fn make_lsp_error(
    data: Option<yojson::T>,
    stack: Option<&str>,
    current_stack: Option<bool>,
    code: Option<error::Code>,
    message: &str,
) -> error::T {
    let current_stack = current_stack.unwrap_or(true);
    let code = code.unwrap_or(error::UnknownErrorCode);
    let mut elems = match data {
        None => vec![],
        Some(yojson::T::Assoc(elems)) => elems,
        Some(json) => vec![("data".to_string(), json)],
    };
    let mem = |elems: &[(String, yojson::T)], key: &str| elems.iter().any(|(k, _)| k == key);
    match stack {
        Some(stack) if !mem(&elems, "stack") => elems.insert(
            0,
            (
                "stack".to_string(),
                yojson::T::String(exception::clean_stack(stack)),
            ),
        ),
        _ => {}
    }
    if current_stack && !mem(&elems, "current_stack") {
        elems.insert(
            0,
            (
                "current_stack".to_string(),
                yojson::T::String(exception::clean_stack(
                    &exception::get_current_callstack_string(99),
                )),
            ),
        )
    }
    error::T {
        code,
        message: message.to_string(),
        data: Some(yojson::T::Assoc(elems)),
    }
}

/// Use ignore_promise_but_handle_failure when you want don't care about awaiting
/// results of an async piece of work, but still want any exceptions to be logged.
///
/// (Here: runs `f` on a thread of its own, which takes [`lwt`] for what `f`
/// does outside its own waits.)
fn ignore_promise_but_handle_failure(
    desc: &'static str,
    terminate_on_failure: bool,
    f: impl FnOnce() + Send + 'static,
) {
    std::thread::Builder::new()
        .name(desc.to_string())
        .spawn(move || {
            let result = std::panic::catch_unwind(AssertUnwindSafe(f));
            if let Err(payload) = result {
                lwt::with_lock(|| {
                    let exn = exception::wrap(payload);
                    let message =
                        format!("Unhandled exception: {}", exception::get_ctor_string(&exn));
                    let stack = exception::clean_stack(&exception::get_backtrace_string(&exn));
                    log_error(&format!("{}\n{}\n{}", message, desc, stack));
                    if terminate_on_failure {
                        // exit 2 is the same as used by Lwt.async
                        exit_process(2);
                    }
                })
            }
        })
        .expect("could not start a thread");
}

fn state_to_string(state: &State) -> &'static str {
    match state {
        State::PreInit => "Pre_init",
        State::Running(_) => "Running ",
        State::PostShutdown => "Post_shutdown",
    }
}

/// `read_hhconfig_version`
fn read_hhconfig_version(root: &path::T) -> String {
    let file = crate::rt::ocaml_filename::concat(&path::to_string(root), ".hhconfig");
    // `Config_file_lwt.parse_hhconfig file`
    match std::fs::read(&file) {
        Ok(hhconfig_contents) => {
            let config = crate::config_file_common::parse_contents(&hhconfig_contents);
            let version = crate::config_file_common::getters::string_opt("version", &config);
            let version = crate::config_file_version::parse_version(version.as_deref());
            crate::config_file_version::version_to_string_opt(None, &version)
                .unwrap_or_else(|| "[NoVersion]".to_string())
        }
        Err(_) => format!(
            "[NoHhconfig:{}]",
            format!(
                "Could not load hhconfig: {}",
                format!("Could not read the contents of the file at path {}", file)
            )
        ),
    }
}

fn read_hhconfig_version_and_switch(root: &path::T) -> String {
    let hack_rc_mode = match std::fs::read(crate::sys_utils::expanduser("~/.hack_rc_mode")) {
        Ok(s) => format!(" hack_rc_mode={}", String::from_utf8_lossy(&s)),
        Err(_) => String::new(),
    };
    let hh_home = match std::env::var("HH_HOME") {
        Ok(s) => format!(" HH_HOME={}", s),
        Err(_) => String::new(),
    };
    let hhconfig_version = read_hhconfig_version(root);
    format!("{}{}{}", hhconfig_version, hack_rc_mode, hh_home)
}

pub(crate) fn terminate_if_version_changed_since_start_of_lsp() {
    let env = env();
    let current_version_and_switch = read_hhconfig_version_and_switch(&env.root);
    let is_ok = env.hhconfig_version_and_switch == current_version_and_switch;
    if !is_ok {
        // In these cases we have to terminate our LSP server, and trust
        // VSCode to restart us. Note that we can't do clientStart because that
        // would start our (old) version of hh_server, not the new one!
        let message = format!(
            "Version in hhconfig+switch that spawned the current hh_client: {}\nVersion in hhconfig+switch currently: {}\n",
            env.hhconfig_version_and_switch, current_version_and_switch
        );
        lsp_helpers::telemetry_log(&to_stdout, None, &message);
        exit_fail()
    }
}

/// get_uris_with_unsaved_changes is the set of files for which we've
/// received didChange but haven't yet received didSave/didClose.
fn get_uris_with_unsaved_changes(state: &State) -> uri_set::T {
    match state {
        State::Running(lenv) => lenv.uris_with_unsaved_changes.clone(),
        State::PreInit | State::PostShutdown => uri_set::T::new(),
    }
}

// ~~ The one OCaml thread ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The one thread of the OCaml's Lwt (see the module doc): held by whoever
/// runs OCaml code between two waits.
pub(crate) mod lwt {
    use std::cell::Cell;
    use std::sync::Condvar;
    use std::sync::Mutex;

    static HELD: Mutex<bool> = Mutex::new(false);
    static CV: Condvar = Condvar::new();

    thread_local! {
        static HOLDS: Cell<bool> = const { Cell::new(false) };
    }

    fn acquire() {
        let mut held = HELD.lock().unwrap_or_else(|e| e.into_inner());
        while *held {
            held = CV.wait(held).unwrap_or_else(|e| e.into_inner());
        }
        *held = true;
        HOLDS.with(|h| h.set(true));
    }

    fn release() {
        HOLDS.with(|h| h.set(false));
        *HELD.lock().unwrap_or_else(|e| e.into_inner()) = false;
        CV.notify_all();
    }

    /// Whether this thread holds it.
    pub fn holds() -> bool {
        HOLDS.with(|h| h.get())
    }

    /// The main thread takes it at the start of `main`.
    pub fn enter() {
        if !holds() {
            acquire()
        }
    }

    /// A point where the OCaml waits (`let%lwt`): `f` runs without it, so
    /// that the other "promises" can run meanwhile.
    pub fn yield_during<A>(f: impl FnOnce() -> A) -> A {
        if holds() {
            release();
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
            acquire();
            match result {
                Ok(a) => a,
                Err(payload) => std::panic::resume_unwind(payload),
            }
        } else {
            f()
        }
    }

    /// What a "promise" does between two waits, from a thread of its own.
    pub fn with_lock<A>(f: impl FnOnce() -> A) -> A {
        if holds() {
            f()
        } else {
            acquire();
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
            release();
            match result {
                Ok(a) => a,
                Err(payload) => std::panic::resume_unwind(payload),
            }
        }
    }
}

/// The notifications of the IDE service, forwarded to a channel that
/// [`get_next_event`] can wait on together with its other sources. (The
/// sender is kept for ever: once the queue is closed, nothing more comes, as
/// the OCaml's never-fulfilled promise.)
struct IdeNotifications {
    rx: Receiver<Notification>,
    _tx: Sender<Notification>,
}

fn forward_ide_notifications(ide_service: &client_ide_service::T) -> IdeNotifications {
    let (tx, rx) = crossbeam_channel::unbounded();
    let queue = client_ide_service::get_notifications(ide_service);
    let tx_ = tx.clone();
    std::thread::Builder::new()
        .name("ClientLspNotifications".to_string())
        .spawn(move || {
            while let Some(notification) = crate::lwt_message_queue::pop(&queue) {
                if tx_.send(notification).is_err() {
                    break;
                }
            }
        })
        .expect("could not start a thread");
    IdeNotifications { rx, _tx: tx }
}

/// Where the next event comes from (`get_client_message_source`).
enum MessageSource {
    FromClient,
    FromIdeService(Event),
    FromQ(Option<ErrorsItem>),
    FromRefsQ(Option<Vec<HalfOpenOneBased>>),
    FromUrisThatNeedCheck(DocumentUri, ErrorsTrigger),
    NoSource,
}

/// Determine whether to read a message from the client (the editor) if
/// we've yet received an initialize message, or from
/// clientIdeDaemon, or whether neither is ready within 1s.
fn get_client_message_source(
    client: Option<&jsonrpc::T>,
    ide_notifications: &IdeNotifications,
    errors_q_opt: Option<&Receiver<ErrorsItem>>,
    refs_q_opt: Option<&Receiver<Vec<HalfOpenOneBased>>>,
    uri_needs_check: Option<(DocumentUri, ErrorsTrigger)>,
) -> MessageSource {
    // This code embodies the following rules:
    // 1. If something is available from the client, then pick it
    // 2. Otherwise if client/ide_service/errors-q/refs-q is available right away then pick one arbitrarily
    // 3. Otherwise if there's a uri-that-needs-check then pick it
    // 4. Otherwise wait at most 1 second for any of the above
    // 5. Otherwise return an idle [Tick].
    //
    // Alas Lwt.pick doesn't let us prioritize amongst the items we're awaiting.
    // So we do it a bit hacky, using "0.01 seconds" as an artificial delay
    // to make file-that-needs-check be avoided if anything else is available immediately.
    let delay_to_force_lower_priority = Duration::from_millis(10);
    if client.is_some_and(jsonrpc::has_message) {
        return MessageSource::FromClient;
    }
    let deadline = Instant::now()
        + if uri_needs_check.is_some() {
            delay_to_force_lower_priority
        } else {
            Duration::from_secs(1)
        };
    lwt::yield_during(|| {
        loop {
            let client_rx = match client.map(jsonrpc::await_until_message) {
                None => None,
                Some(jsonrpc::AwaitUntilMessage::AlreadyHasMessage) => {
                    return MessageSource::FromClient;
                }
                Some(jsonrpc::AwaitUntilMessage::WaitForDataHere(rx)) => Some(rx),
            };
            let mut sel = Select::new();
            let i_client = client_rx.map(|rx| sel.recv(rx));
            let i_ide = sel.recv(&ide_notifications.rx);
            let i_errors = errors_q_opt.map(|q| sel.recv(q));
            let i_refs = refs_q_opt.map(|q| sel.recv(q));
            let i = match sel.ready_deadline(deadline) {
                Ok(i) => i,
                Err(crossbeam_channel::ReadyTimeoutError) => {
                    return match uri_needs_check {
                        Some((uri, trigger)) => MessageSource::FromUrisThatNeedCheck(uri, trigger),
                        None => MessageSource::NoSource,
                    };
                }
            };
            if Some(i) == i_client {
                if client.is_some_and(jsonrpc::has_message) {
                    return MessageSource::FromClient;
                }
            } else if i == i_ide {
                if let Ok(notification) = ide_notifications.rx.try_recv() {
                    return MessageSource::FromIdeService(Event::DaemonNotification(notification));
                }
            } else if Some(i) == i_errors {
                match errors_q_opt.unwrap().try_recv() {
                    Ok(item) => return MessageSource::FromQ(Some(item)),
                    Err(crossbeam_channel::TryRecvError::Disconnected) => {
                        return MessageSource::FromQ(None);
                    }
                    Err(crossbeam_channel::TryRecvError::Empty) => {}
                }
            } else if Some(i) == i_refs {
                match refs_q_opt.unwrap().try_recv() {
                    Ok(item) => return MessageSource::FromRefsQ(Some(item)),
                    Err(crossbeam_channel::TryRecvError::Disconnected) => {
                        return MessageSource::FromRefsQ(None);
                    }
                    Err(crossbeam_channel::TryRecvError::Empty) => {}
                }
            }
        }
    })
}

/// Pick up the next available message from the JsonRPC client.
/// At the first character of a message, block until that message is completely received.
fn get_next_event(
    state: &mut State,
    client: &jsonrpc::T,
    ide_service: &client_ide_service::T,
    ide_notifications: &IdeNotifications,
) -> Result<Event, Exn> {
    let can_use_client = match initialize_params() {
        Some(params) if params.initialization_options.delay_until_done_init => {
            match client_ide_service::get_status(ide_service) {
                client_ide_service::status::T::Initializing
                | client_ide_service::status::T::Rpc(_) => false,
                client_ide_service::status::T::Ready
                | client_ide_service::status::T::Stopped(_) => true,
            }
        }
        _ => true,
    };
    let client = if can_use_client { Some(client) } else { None };
    let from_client = |client: &jsonrpc::T| -> Result<Event, Exn> {
        let message = lwt::yield_during(|| jsonrpc::get_message(client));
        match message {
            jsonrpc::GetMessage::Message(jsonrpc::TimestampedJson { json, timestamp }) => {
                let parsed = std::panic::catch_unwind(AssertUnwindSafe(
                    || -> Result<Event, exception::T> {
                        let missing = Cell::new(false);
                        let message = lsp_fmt::parse_lsp(&json, |id| {
                            match get_outstanding_request(id) {
                                Some(request) => request,
                                None => {
                                    // `failwith "response id doesn't correspond to an outstanding request"`
                                    missing.set(true);
                                    LspRequest::ShutdownRequest
                                }
                            }
                        });
                        if missing.get() {
                            return Err(exception::wrap(Failure(
                                "response id doesn't correspond to an outstanding request"
                                    .to_string(),
                            )));
                        }
                        let message = message.map_err(exception::wrap)?;
                        let activity_key = jget::obj_opt(Some(&json), "activityKey");
                        let activity_id = jget::string_d(
                            activity_key,
                            "id",
                            format!("[hh]{}", random_id::short_string()),
                        );
                        // activity_id is used in telemetry for joins on other tables;
                        // tracking_suffix is used as extra disambiguation since activity-ids
                        // are sometimes shared between events
                        let rnd = random_id::short_string();
                        let tracking_suffix = match &message {
                            LspMessage::RequestMessage(id, _) => {
                                format!("{}.{}", rnd, lsp_fmt::id_to_string(id))
                            }
                            _ => rnd,
                        };
                        let tracking_id = format!("{}.{}", activity_id, tracking_suffix);
                        Ok(Event::ClientMessage(
                            IncomingMetadata {
                                tracking_id,
                                activity_id,
                                tracking_suffix,
                                timestamp,
                            },
                            message,
                        ))
                    },
                ))
                .unwrap_or_else(|payload| Err(exception::wrap(payload)));
                match parsed {
                    Ok(event) => Ok(event),
                    Err(e) => {
                        let edata = RemoteExceptionData {
                            stack: exception::get_backtrace_string(&e),
                            message: exception::get_ctor_string(&e),
                        };
                        Err(Exn::ClientRecoverableConnectionException(edata))
                    }
                }
            }
            jsonrpc::GetMessage::FatalException(edata) => {
                Err(Exn::ClientFatalConnectionException(edata))
            }
            jsonrpc::GetMessage::RecoverableException(edata) => {
                Err(Exn::ClientRecoverableConnectionException(edata))
            }
        }
    };
    if let State::Running(lenv) = state {
        if let Some(sh) = &mut lenv.current_hh_shell {
            if sh.process.is_resolved() {
                // Invariant is that if current_hh_shell is Some, then we will eventually
                // produce an LSP response for it. We're turning it into None here;
                // the obligation to return an LSP response has been transferred onto
                // our Shell_out_complete result.
                let sh = lenv.current_hh_shell.take().unwrap();
                let result = sh.process.into_result();
                return Ok(Event::ShellOutComplete(
                    result,
                    sh.triggering_request,
                    sh.shellable_type,
                ));
            }
        }
    }
    // invariant used by [handle_tick_event]: Errors_file events solely arise
    // in state [Running ] in conjunction with [TailingErrors].
    let errors_queue_opt = match (&*latest_hh_server_errors(), &*state) {
        (ErrorsConn::TailingErrors { q, .. }, State::Running(_)) => Some(q.clone()),
        _ => None,
    };
    let refs_queue_opt = match &*state {
        State::Running(run_env::T {
            current_hh_shell:
                Some(run_env::CurrentHhShell {
                    shellable_type:
                        run_env::ShellableType::FindRefs(run_env::ShelloutStandardResponse {
                            stream_file: Some(run_env::StreamFile { q, .. }),
                            ..
                        }),
                    ..
                }),
            ..
        }) => Some(q.clone()),
        _ => None,
    };
    let uri_needs_check = match &*state {
        State::Running(run_env::T {
            uris_that_need_check,
            ..
        }) => uris_that_need_check
            .get_min()
            .map(|(uri, trigger)| (uri.clone(), trigger.clone())),
        _ => None,
    };
    let message_source = get_client_message_source(
        client,
        ide_notifications,
        errors_queue_opt.as_ref(),
        refs_queue_opt.as_ref(),
        uri_needs_check,
    );
    match message_source {
        MessageSource::FromClient => from_client(client.unwrap()),
        MessageSource::FromIdeService(message) => Ok(message),
        MessageSource::FromQ(message) => Ok(Event::ErrorsFile(message)),
        MessageSource::FromRefsQ(message) => Ok(Event::RefsFile(message)),
        MessageSource::NoSource => Ok(Event::Tick),
        MessageSource::FromUrisThatNeedCheck(uri, trigger) => {
            Ok(Event::DeferredCheck(uri, trigger))
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PoweredBy {
    HhServer,
    LanguageServer,
    ServerlessIde,
}

fn add_powered_by(powered_by: PoweredBy, json: yojson::T) -> yojson::T {
    match (json, powered_by) {
        (yojson::T::Assoc(mut props), PoweredBy::ServerlessIde) => {
            props.insert(
                0,
                (
                    "powered_by".to_string(),
                    yojson::T::String("serverless_ide".to_string()),
                ),
            );
            yojson::T::Assoc(props)
        }
        (json, _) => json,
    }
}

pub(crate) fn respond_jsonrpc(powered_by: PoweredBy, id: &LspId, result: &LspResult) {
    to_stdout(add_powered_by(
        powered_by,
        lsp_fmt::print_lsp_response(id, result),
    ))
}

pub(crate) fn notify_jsonrpc(powered_by: PoweredBy, notification: &LspNotification) {
    to_stdout(add_powered_by(
        powered_by,
        lsp_fmt::print_lsp_notification(notification),
    ))
}

/// What the error handlers of the main loop need of `!ref_event`.
#[derive(Clone)]
enum RefEvent {
    /// (The OCaml reads the metadata only for `Hack_event_logger`, in
    /// `hack_log_error`, which has no counterpart.)
    ClientMessage(#[allow(dead_code)] IncomingMetadata, LspMessage),
    /// (The OCaml reads the request only in `log_response_if_necessary`, for
    /// `Hack_event_logger`, which has no counterpart.)
    ShellOutComplete(#[allow(dead_code)] run_env::TriggeringRequest),
    Other,
}

/// respond_to_error: if we threw an exception during the handling of a request,
/// report the exception to the client as the response to their request.
fn respond_to_error(event: Option<&RefEvent>, e: &error::T) {
    let result = LspResult::ErrorResult(e.clone());
    match event {
        Some(RefEvent::ClientMessage(_, LspMessage::RequestMessage(id, _request))) => {
            respond_jsonrpc(PoweredBy::LanguageServer, id, &result)
        }
        _ => {
            // We want to report LSP error 'e' over jsonrpc. But jsonrpc only allows
            // errors to be reported in response to requests. So we'll stick the information
            // in a telemetry/event. The format of this event isn't defined. We're going to
            // roll our own, using ad-hoc json fields to emit all the data out of 'e'
            let mut extras = vec![(
                "code".to_string(),
                yojson::T::String(error::show_code(e.code)),
            )];
            if let Some(data) = &e.data {
                extras.push(("data".to_string(), data.clone()));
            }
            lsp_helpers::telemetry_error(&to_stdout, Some(extras), &e.message)
        }
    }
}

/// request_showStatusFB: pops up a dialog
fn request_show_status_fb(params: show_status_fb::Params, initialize_params: &initialize::Params) {
    if !lsp_helpers::supports_status(initialize_params) {
    } else {
        // We try not to send duplicate statuses.
        // That means: if you call request_showStatus but your message is the same as
        // what's already up, then you won't be shown, and your callbacks won't be shown.
        let msg = &params.request.message;
        let mut outstanding = SHOW_STATUS_OUTSTANDING
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if *msg == *outstanding {
        } else {
            *outstanding = msg.clone();
            drop(outstanding);
            let id = lsp::NumberId(jsonrpc::get_next_request_id());
            let request = LspRequest::ShowStatusRequestFB(params);
            to_stdout(lsp_fmt::print_lsp_request(&id, &request));
            let handler: ResultHandler = Arc::new(|_result, _state| {});
            requests_outstanding().insert(id, (request, handler));
        }
    }
}

/// Dismiss all diagnostics.
fn dismiss_diagnostics(state: &mut State) {
    if let State::Running(lenv) = state {
        // [uris_with_standalone_diagnostics] are the files-with-squiggles that we've reported
        // to the editor; these came either from clientIdeDaemon or from tailing
        // the errors.bin file in which hh_server accumulates diagnostics for the current typecheck.
        for (uri, _time) in lenv.uris_with_standalone_diagnostics.iter() {
            let params = publish_diagnostics::Params {
                uri: uri.clone(),
                diagnostics: vec![],
                is_status_fb: false,
            };
            let notification = LspNotification::PublishDiagnosticsNotification(params);
            to_stdout(lsp_fmt::print_lsp_notification(&notification));
        }
        lenv.uris_with_standalone_diagnostics = uri_map::T::new();
    }
}

// ~~ Conversions - ad-hoc ones written as needed them, not systematic ~~~~~~~~~

pub(crate) fn lsp_uri_to_path(uri: &DocumentUri) -> Result<String, Exn> {
    Ok(lsp_helpers::lsp_uri_to_path(uri)?)
}

pub(crate) fn path_string_to_lsp_uri(path: &str, default_path: &str) -> DocumentUri {
    lsp_helpers::path_string_to_lsp_uri(path, default_path)
}

pub(crate) fn lsp_position_to_ide(lsp::Position { line, character }: &lsp::Position) -> file_content::position::T {
    file_content::position::from_zero_based(*line, *character)
}

pub(crate) fn lsp_file_position_to_hack(
    params: &lsp::text_document_position_params::T,
) -> Result<(String, file_content::position::T), Exn> {
    let pos = lsp_position_to_ide(&params.position);
    let filename = lsp_helpers::lsp_text_document_identifier_to_filename(&params.text_document)?;
    Ok((filename, pos))
}

pub(crate) fn rename_params_to_document_position(
    params: &lsp::rename::Params,
) -> lsp::text_document_position_params::T {
    lsp::text_document_position_params::T {
        text_document: params.text_document.clone(),
        position: params.position,
    }
}

pub(crate) fn ide_shell_out_pos_to_lsp_location(pos: &HalfOpenOneBased) -> lsp::location::T {
    lsp::location::T {
        uri: path_string_to_lsp_uri(&pos.filename, &pos.filename),
        range: lsp::Range {
            start: lsp::Position {
                line: pos.line - 1,
                character: pos.char_start - 1,
            },
            end_: lsp::Position {
                line: pos.line - 1,
                character: pos.char_end - 1,
            },
        },
    }
}

pub(crate) fn hack_pos_to_lsp_location(pos: &pos::Absolute, default_path: &str) -> lsp::location::T {
    lsp::location::T {
        uri: path_string_to_lsp_uri(&pos::filename(pos), default_path),
        range: lsp_helpers::hack_pos_to_lsp_range(|a: &String, b: &String| a == b, pos),
    }
}

pub(crate) fn ide_range_to_lsp(ide_api_types::Range { st, ed }: &ide_api_types::Range) -> lsp::Range {
    lsp::Range {
        start: {
            let (line, character) = file_content::position::line_column_zero_based(st);
            lsp::Position { line, character }
        },
        end_: {
            let (line, character) = file_content::position::line_column_zero_based(ed);
            lsp::Position { line, character }
        },
    }
}

pub(crate) fn lsp_range_to_ide(range: &lsp::Range) -> ide_api_types::Range {
    ide_api_types::Range {
        st: lsp_position_to_ide(&range.start),
        ed: lsp_position_to_ide(&range.end_),
    }
}

/// See documentation for `args` field `notebook_mode`
const DIAGNOSTICS_TO_EXCLUDE_FROM_NOTEBOOKS: [&str; 3] = [
    "Hack does not support top level statements. Use the __EntryPoint attribute on a function instead",
    "The function prep is deprecated: use await, see https://fburl.com/goodbye-prep",
    "await cannot be used in a toplevel statement",
];

fn filter_diagnostics(
    diagnostics: Vec<publish_diagnostics::Diagnostic>,
) -> Vec<publish_diagnostics::Diagnostic> {
    if env().args.notebook_mode {
        let is_at_breakpoint: LazyCell<bool> = LazyCell::new(|| match std::env::var("HOME") {
            Ok(home_dir) => std::path::Path::new(&format!("{}/.vscode-sockets/hhvm-paused", home_dir))
                .exists(),
            Err(_) => false,
        });
        let should_include_diagnostic = |d: &publish_diagnostics::Diagnostic| match d.code {
            // undefined variable
            publish_diagnostics::DiagnosticCode::IntCode(2050) => {
                // When we're breakpoint-debugging in a Hack notebook,
                // suppress all undefined variable errors.
                // There can be variables that exist the runtime environment
                // but aren't written in the notebook and vice-versa.
                !*is_at_breakpoint
            }
            _ => !DIAGNOSTICS_TO_EXCLUDE_FROM_NOTEBOOKS.contains(&d.message.as_str()),
        };
        diagnostics
            .into_iter()
            .filter(should_include_diagnostic)
            .collect()
    } else {
        diagnostics
    }
}

use std::cell::LazyCell;

/// `Printf.sprintf "%x"` of an OCaml `int` (63 bits, printed unsigned).
fn ocaml_hex(n: isize) -> String {
    format!("{:x}", (n as u64) & 0x7fff_ffff_ffff_ffff)
}

/// `Pos.set_file filename pos`, for an absolute position.
fn set_file_absolute(filename: &str, pos: &pos::Absolute) -> pos::Absolute {
    let oxidized::pos_span_raw::PosSpanRaw { start, end } = pos::APos::raw_span(pos);
    pos::make_absolute(filename.to_string(), start, end)
}

pub(crate) fn ide_diagnostics_to_lsp_diagnostics(
    filename: &str,
    diagnostics: &[Diagnostic],
) -> publish_diagnostics::Params {
    let location_message = |message: &oxidized::message::Message<pos::Absolute>| -> (lsp::location::T, String) {
        let oxidized::message::Message(pos, message) = message;
        // It's known and expected that hh_server sometimes sends an error
        // with empty filename in its list of messages. These implicitly
        // refer to the file in which the error is reported.
        let pos = if pos::filename(pos).is_empty() {
            set_file_absolute(filename, pos)
        } else {
            pos.clone()
        };
        let lsp::location::T { uri, range } = hack_pos_to_lsp_location(&pos, filename);
        (
            lsp::location::T { uri, range },
            markdown_lite::render(None, None, &String::from_utf8_lossy(message)),
        )
    };
    let ide_diagnostic_to_lsp_diagnostics =
        |diagnostic: &Diagnostic| -> Vec<publish_diagnostics::Diagnostic> {
            let Diagnostic {
                diagnostic_error,
                diagnostic_hash,
                ..
            } = diagnostic;
            let all_messages: Vec<(lsp::location::T, String)> =
                user_diagnostic::to_list(diagnostic_error)
                    .iter()
                    .map(location_message)
                    .collect();
            let (first_message, additional_messages) = match all_messages.split_first() {
                Some((hd, tl)) => (hd, tl),
                None => panic!("Expected at least one error in the error list"),
            };
            let (
                lsp::location::T {
                    range,
                    // This is the file of the first message of the error which is supposed to correspond to [filename]
                    uri: _,
                },
                message,
            ) = first_message;
            let data = Some(yojson::T::Assoc(vec![(
                "lineAgnosticHash".to_string(),
                yojson::T::String(ocaml_hex(*diagnostic_hash)),
            )]));
            let mut related_information: Vec<publish_diagnostics::DiagnosticRelatedInformation> =
                additional_messages
                    .iter()
                    .map(|(location, message)| publish_diagnostics::DiagnosticRelatedInformation {
                        related_location: location.clone(),
                        related_message: message.clone(),
                    })
                    .collect();
            let first_loc = &first_message.0;
            let custom_errors = diagnostic_error.custom_msgs.iter().map(|msg| {
                let related_message = markdown_lite::render(None, None, msg);
                publish_diagnostics::DiagnosticRelatedInformation {
                    related_location: first_loc.clone(),
                    related_message,
                }
            });
            related_information.extend(custom_errors);
            let error_for_diagnostic = publish_diagnostics::Diagnostic {
                range: *range,
                severity: Some(match diagnostic_error.severity {
                    user_diagnostic::Severity::Err => publish_diagnostics::DiagnosticSeverity::Error,
                    user_diagnostic::Severity::Warning { .. } => {
                        publish_diagnostics::DiagnosticSeverity::Warning
                    }
                }),
                code: publish_diagnostics::DiagnosticCode::IntCode(diagnostic_error.code),
                source: Some("Hack".to_string()),
                message: message.clone(),
                related_locations: related_information.clone(), // legacy FB extension
                related_information,
                data,
            };
            let additional_diagnostics: Vec<publish_diagnostics::Diagnostic> = diagnostic
                .diagnostic_related_hints
                .iter()
                .map(|hint_pos| {
                    let lsp::location::T { uri: _, range } =
                        hack_pos_to_lsp_location(hint_pos, filename);
                    publish_diagnostics::Diagnostic {
                        range,
                        severity: Some(publish_diagnostics::DiagnosticSeverity::Hint),
                        ..error_for_diagnostic.clone()
                    }
                })
                .collect();
            let mut res = vec![error_for_diagnostic];
            res.extend(additional_diagnostics);
            res
        };
    // The caller is required to give us a non-empty filename. If it is empty,
    // the following path_to_lsp_uri will fall back to the default path - which
    // is also empty - and throw, logging appropriate telemetry.
    let diagnostics = filter_diagnostics(
        diagnostics
            .iter()
            .flat_map(ide_diagnostic_to_lsp_diagnostics)
            .collect(),
    );
    publish_diagnostics::Params {
        uri: path_string_to_lsp_uri(filename, ""),
        is_status_fb: false,
        diagnostics,
    }
}

/// Retrieves a TextDocumentItem for a given URI from editor_open_files,
/// or raises LSP [InvalidRequest] if not open
pub(crate) fn get_text_document_item(
    editor_open_files: &uri_map::T<text_document_item::T>,
    uri: &DocumentUri,
) -> Result<text_document_item::T, Exn> {
    match editor_open_files.get(uri) {
        Some(document) => Ok(document.clone()),
        None => Err(lsp_exception(
            error::InvalidRequest,
            "action on a file not open in LSP server",
        )),
    }
}

/// Retrieves the content of this file, or raises an LSP [InvalidRequest] exception
/// if the file isn't currently open
pub(crate) fn get_document_contents(
    editor_open_files: &uri_map::T<text_document_item::T>,
    uri: &DocumentUri,
) -> Result<String, Exn> {
    let document = get_text_document_item(editor_open_files, uri)?;
    Ok(document.text)
}

/// Converts a single TextDocumentItem (an element in editor_open_files, for example) into a document that ClientIdeDaemon uses
pub(crate) fn lsp_document_to_ide(
    text_document: &text_document_item::T,
) -> Result<client_ide_message::Document, Exn> {
    let fn_ = &text_document.uri;
    Ok(client_ide_message::Document {
        file_path: path::make(&lsp_helpers::lsp_uri_to_path(fn_)?),
        file_contents: text_document.text.clone(),
    })
}

/// Turns the complete set of editor_open_files into a format
/// suitable for clientIdeDaemon
pub(crate) fn get_documents_from_open_files(
    editor_open_files: &uri_map::T<text_document_item::T>,
) -> Result<Vec<client_ide_message::Document>, Exn> {
    uri_map::values(editor_open_files)
        .iter()
        .map(lsp_document_to_ide)
        .collect()
}

/// Turns this Lsp uri+line+col into a format suitable for clientIdeDaemon.
/// Raises an LSP [InvalidRequest] exception if the file isn't currently open.
pub(crate) fn get_document_location(
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::text_document_position_params::T,
) -> Result<(client_ide_message::Document, file_content::position::T), Exn> {
    let (file_path, pos) = lsp_file_position_to_hack(params)?;
    let uri = &params.text_document.uri;
    let file_path = path::make(&file_path);
    let file_contents = get_document_contents(editor_open_files, uri)?;
    Ok((
        client_ide_message::Document {
            file_path,
            file_contents,
        },
        pos,
    ))
}

/// Parses output of "hh --ide-find-references" and "hh --ide-go-to-impl".
/// If the output is malformed, raises an exception.
pub(crate) fn shellout_locations_to_lsp_locations_exn(
    stdout: &str,
) -> Result<Vec<lsp::location::T>, Exn> {
    let positions = find_refs_wire_format::ide_shellout::from_string_exn(stdout)
        .map_err(|e| Exn::Other(exception::wrap(e)))?;
    Ok(positions
        .iter()
        .map(ide_shell_out_pos_to_lsp_location)
        .collect())
}

// ~~ Connection and rpc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn start_server() {
    // This basically does "hh_client start": a single attempt to open the
    // socket, send+read version and compare for mismatch, send handoff and
    // read response. It will print information to stderr. If the server is in
    // an unresponsive or invalid state then it will kill the server. Next if
    // necessary it tries to spawn the server and wait until the monitor is
    // responsive enough to print "ready". It will do a hard program exit if
    // there were spawn problems.
    let env = env();
    let env_start = client_start::Env {
        root: env.root.clone(),
        from: env.args.from.clone(),
        no_load: false,
        watchman_debug_logging: false,
        silent: true,
        exit_on_failure: false,
        ignore_hh_version: false,
        saved_state_ignore_hhconfig: false,
        mini_state: None,
        save_64bit: None,
        save_human_readable_64bit_dep_map: None,
        prechecked: None,
        config: env.args.config.clone(),
        custom_hhi_path: None,
        custom_telemetry_data: vec![],
        allow_non_opt_build: false,
        preexisting_warnings: false,
    };
    // `let _exit_status = Client_start.main env_start in ()`: the promise is
    // not awaited, so the start goes on while we carry on.
    std::thread::Builder::new()
        .name("ClientStart".to_string())
        .spawn(move || {
            let _exit_status = client_start::main(&env_start);
        })
        .expect("could not start a thread");
}

fn announce_ide_failure(error_data: &RichError) {
    let debug_details = format!(
        "{} - {}",
        error_data.category,
        // unsorted: parsed programmatically, not snapshot-tested
        error_data
            .data
            .as_ref()
            .map(yojson::to_string)
            .unwrap_or_default()
    );
    log(&format!(
        "IDE services could not be initialized.\n{}\n{}",
        error_data.long_user_message, debug_details
    ));
    let input = format!("{}\n\n{}", error_data.long_user_message, debug_details);
    let append_to_log = format!("\n\nMore details:\n{}\n{}", debug_details, input);
    lsp_helpers::log_error(
        &to_stdout,
        &format!("{}{}", error_data.long_user_message, append_to_log),
    );
    if error_data.is_actionable {
        lsp_helpers::show_message_error(
            &to_stdout,
            &format!("{}{}", error_data.medium_user_message, SEE_OUTPUT_HACK),
        );
    }
}

/// Like all async methods, this method has a synchronous preamble up
/// to its first await point, at which point it returns a promise to its
/// caller; the rest of the method will be scheduled asynchronously.
/// The synchronous preamble sends an "initialize" request to the ide_service.
/// The asynchronous continuation is triggered when the response comes back;
/// it then pumps messages to and from the ide service.
/// Note: the fact that the request is sent in the synchronous preamble, is
/// important for correctness - the rest of the codebase can send other requests
/// to the ide_service at any time, safe in the knowledge that such requests will
/// necessarily be delivered after the initialize request.
///
/// (Here: the synchronous preamble, then the rest on a thread, which calls
/// `Client_ide_service.initialize_from_saved_state` (it talks to the daemon
/// directly; the requests of [`ide_rpc`] wait in the service's queue until
/// [`client_ide_service::serve`] runs, after it).)
fn run_ide_service(
    ide_service: &client_ide_service::T,
    initialize_params: &initialize::Params,
    editor_open_files: Option<&uri_map::T<text_document_item::T>>,
) {
    if !initialize_params
        .client_capabilities
        .workspace
        .did_change_watched_files
        .dynamic_registration
    {
        log_error("client doesn't support file-watching");
    }
    let env = env();
    let naming_table_load_info = match (
        &initialize_params.initialization_options.naming_table_saved_state_path,
        &env.args.naming_table,
    ) {
        (Some(_), Some(_)) => {
            log_error(
                "naming table path supplied from both LSP initialization param and command line",
            );
            exit_fail()
        }
        (Some(path), _) | (_, Some(path)) => Some(
            client_ide_message::initialize_from_saved_state::NamingTableLoadInfo {
                path: path::make(path),
                test_delay: initialize_params
                    .initialization_options
                    .naming_table_saved_state_test_delay,
            },
        ),
        (None, None) => None,
    };
    let open_files: Vec<path::T> = editor_open_files
        .map(uri_map::keys)
        .unwrap_or_default()
        .iter()
        .map(|uri| {
            path::make(
                &lsp_helpers::lsp_uri_to_path(uri)
                    .unwrap_or_else(|e| std::panic::panic_any(exception::wrap(e))),
            )
        })
        .collect();
    log_debug("initialize_from_saved_state");
    let ide_service = ide_service.clone();
    ignore_promise_but_handle_failure("run-ide-after-init", true, move || {
        let result = client_ide_service::initialize_from_saved_state(
            &ide_service,
            env.root.clone(),
            naming_table_load_info,
            env.args.warnings_saved_state_path.clone(),
            env.args.config.clone(),
            env.args.ignore_hh_version,
            open_files,
        );
        lwt::with_lock(|| log_debug("initialize_from_saved_state.done"));
        match result {
            Ok(()) => client_ide_service::serve(&ide_service),
            Err(error_data) => lwt::with_lock(|| announce_ide_failure(&error_data)),
        }
    });
}

fn stop_ide_service(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    stop_reason: client_ide_service::stop_reason::T,
) {
    log(&format!(
        "Stopping IDE service process: {}",
        client_ide_service::stop_reason::to_log_string(stop_reason)
    ));
    lwt::yield_during(|| client_ide_service::stop(ide_service, tracking_id, stop_reason, None))
}

/// This function looks at three sources of information (1) hh_server progress.json file,
/// (2) whether we're currently tailing an errors.bin file or whether we failed to open one,
/// (3) status of clientIdeDaemon. It synthesizes a status message suitable for display
/// in the VSCode status bar.
fn merge_statuses_standalone(
    server: &server_progress::T,
    errors: &ErrorsConn,
    ide: &client_ide_service::T,
) -> show_status_fb::Params {
    use client_ide_service::status;
    let ((client_ide_disposition, client_ide_is_initializing), client_ide_message, client_ide_tooltip) =
        match client_ide_service::get_status(ide) {
            status::T::Initializing => (
                (Disposition::DWorking, true),
                "Hack: initializing".to_string(),
                "Hack IDE support is initializing (loading saved state)".to_string(),
            ),
            status::T::Rpc(_) => (
                (Disposition::DWorking, false),
                "Hack".to_string(),
                "Hack is working on IDE requests".to_string(),
            ),
            status::T::Ready => (
                (Disposition::DReady, false),
                "Hack".to_string(),
                "Hack IDE support is ready".to_string(),
            ),
            status::T::Stopped(s) => (
                (Disposition::DStopped, false),
                format!("Hack: {}", s.short_user_message),
                format!("{}{}", s.medium_user_message, SEE_OUTPUT_HACK),
            ),
        };
    let (hh_server_disposition, hh_server_message, hh_server_tooltip) = {
        use errors_read::OpenError;
        use server_progress::ErrorsFileReadError::Malformed;
        match (server, errors) {
            (
                server_progress::T {
                    disposition: Disposition::DStopped,
                    message,
                    ..
                },
                _,
            ) => (
                Disposition::DStopped,
                format!("Hack: hh_server {}", message),
                format!("hh_server is {}. {}", message, FIX_BY_RUNNING_HH),
            ),
            (
                _,
                ErrorsConn::SeekingErrors {
                    seek_reason: SeekReason::ErrorFileOpenError(e, log_message),
                    ..
                },
            ) if e.with(|e| matches!(e, OpenError::OBuildIdMismatch)) => (
                Disposition::DStopped,
                "Hack: hh_server wrong version".to_string(),
                format!(
                    "hh_server is the wrong version [{}]. {}",
                    log_message, FIX_BY_RUNNING_HH
                ),
            ),
            (
                server_progress::T {
                    disposition: Disposition::DWorking,
                    message,
                    ..
                },
                _,
            ) => (
                Disposition::DWorking,
                // following is little hack because "Hack: typechecking 1234/5678" is too big to fit
                // in the VSCode status bar. So we shorten this special case.
                if message.contains("typechecking") {
                    message.clone()
                } else {
                    format!("Hack: {}", message)
                },
                format!("hh_server is busy [{}]", message),
            ),
            (
                server_progress::T {
                    disposition: Disposition::DReady,
                    ..
                },
                ErrorsConn::SeekingErrors { seek_reason, .. },
            ) if matches!(
                seek_reason,
                SeekReason::WatchError(e) if e.with(|e| matches!(e, WatchError::Killed(_)))
            ) || matches!(seek_reason, SeekReason::Completed(CompletionReason::Stopped, _))
                || matches!(
                    seek_reason,
                    SeekReason::ErrorFileOpenError(e, _) if e.with(|e| matches!(e, OpenError::OKilled(_)))
                ) =>
            {
                (
                    Disposition::DStopped,
                    "Hack: hh_server stopped".to_string(),
                    format!(
                        "hh_server has stopped [{}]. {}",
                        seek_reason_short_description(seek_reason),
                        FIX_BY_RUNNING_HH
                    ),
                )
            }
            (
                server_progress::T {
                    disposition: Disposition::DReady,
                    ..
                },
                ErrorsConn::SeekingErrors { seek_reason, .. },
            ) if matches!(seek_reason, SeekReason::ErrorFileOpenExn(_))
                || matches!(
                    seek_reason,
                    SeekReason::ErrorFileOpenError(e, _)
                        if e.with(|e| matches!(e, OpenError::OReadError(Malformed)))
                )
                || matches!(
                    seek_reason,
                    SeekReason::WatchError(e) if e.with(|e| matches!(e, WatchError::ReadError(Malformed)))
                )
                || matches!(seek_reason, SeekReason::UnexpectedEndOfStream) =>
            {
                (
                    Disposition::DReady,
                    "Hack: internal error".to_string(),
                    format!(
                        "hh_server internal error [{}]. {}",
                        seek_reason_short_description(seek_reason),
                        FIX_BY_RUNNING_HH
                    ),
                )
            }
            (
                server_progress::T {
                    disposition: Disposition::DReady,
                    ..
                },
                ErrorsConn::SeekingErrors {
                    seek_reason: SeekReason::Completed(CompletionReason::Restarted { .. }, _),
                    ..
                },
            )
            | (
                server_progress::T {
                    disposition: Disposition::DReady,
                    ..
                },
                ErrorsConn::TailingErrors { .. },
            ) => (
                Disposition::DWorking,
                "Hack: typechecking".to_string(),
                "hh_server is busy [typechecking].".to_string(),
            ),
            (
                server_progress::T {
                    disposition: Disposition::DReady,
                    ..
                },
                ErrorsConn::SeekingErrors {
                    seek_reason:
                        SeekReason::Completed(CompletionReason::Complete(_), _)
                        | SeekReason::Init
                        | SeekReason::AbsentErrorsFile,
                    ..
                },
            ) => (
                Disposition::DReady,
                "Hack".to_string(),
                "hh_server is ready".to_string(),
            ),
            // The cases the guards above leave (they cannot happen: each
            // seek reason has its row).
            (_, ErrorsConn::SeekingErrors { .. }) => unreachable!("merge_statuses_standalone"),
        }
    };
    let (disposition, message) = match (
        client_ide_disposition,
        client_ide_is_initializing,
        hh_server_disposition,
    ) {
        (Disposition::DWorking, true, _) => (Disposition::DWorking, client_ide_message),
        (_, _, Disposition::DWorking) => (Disposition::DWorking, hh_server_message),
        (Disposition::DWorking, false, Disposition::DStopped) => {
            (Disposition::DWorking, hh_server_message)
        }
        (Disposition::DWorking, false, _) => (Disposition::DWorking, client_ide_message),
        (Disposition::DStopped, _, _) => (Disposition::DStopped, client_ide_message),
        (_, _, Disposition::DStopped) => (Disposition::DStopped, hh_server_message),
        (Disposition::DReady, _, Disposition::DReady) => {
            (Disposition::DReady, "Hack".to_string())
        }
    };
    let root_tooltip = if crate::sys_utils::deterministic_behavior_for_tests() {
        "<ROOT>".to_string()
    } else {
        path::to_string(&env().root)
    };
    let tooltip = format!(
        "{}\n\n{}\n\n{}",
        root_tooltip, client_ide_tooltip, hh_server_tooltip
    );
    let type_ = match disposition {
        Disposition::DStopped => message_type::ErrorMessage,
        Disposition::DWorking => message_type::WarningMessage,
        Disposition::DReady => message_type::InfoMessage,
    };
    show_status_fb::Params {
        short_message: Some(message),
        request: show_status_fb::ShowStatusRequestParams {
            type_,
            message: tooltip,
        },
        progress: None,
        total: None,
        telemetry: None,
    }
}

pub(crate) fn refresh_status(ide_service: &client_ide_service::T) {
    match initialize_params() {
        Some(initialize_params) => {
            let status = {
                let progress = LATEST_HH_SERVER_PROGRESS
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone();
                merge_statuses_standalone(&progress, &latest_hh_server_errors(), ide_service)
            };
            request_show_status_fb(status, &initialize_params)
        }
        None => {
            // [initialize_params_ref] gets set in the Initialize message. We can't report
            // status unless we know what client capabilities were sent in that message.
        }
    }
}

/// This kicks off a permanent process which, once a second, reads progress.json
/// and calls [refresh_status]. Because it's an Lwt process, it's able to update
/// status even when we're stuck waiting for RPC.
fn background_status_refresher(ide_service: &client_ide_service::T) {
    let step = |ide_service: &client_ide_service::T| {
        let progress = server_progress::read();
        *LATEST_HH_SERVER_PROGRESS
            .lock()
            .unwrap_or_else(|e| e.into_inner()) = progress;
        refresh_status(ide_service);
    };
    // The first step runs at once, as the OCaml's `loop ()` up to its sleep.
    step(ide_service);
    let ide_service = ide_service.clone();
    std::thread::Builder::new()
        .name("ClientLspStatus".to_string())
        .spawn(move || {
            loop {
                std::thread::sleep(Duration::from_secs(1));
                lwt::with_lock(|| step(&ide_service));
            }
        })
        .expect("could not start a thread");
}

/// A thin wrapper around ClientIdeMessage which turns errors into exceptions.
pub(crate) fn ide_rpc<A: IdeResult>(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    message: client_ide_message::Request<A>,
) -> Result<A, Exn> {
    let result = lwt::yield_during(|| {
        client_ide_service::rpc(
            ide_service,
            tracking_id,
            ref_unblocked_time,
            &mut || lwt::with_lock(|| refresh_status(ide_service)),
            message,
        )
    });
    match result {
        Ok(result) => Ok(result),
        Err(error_data) => Err(Exn::DaemonNonfatalException(error_data)),
    }
}

/// This sets up a background watcher which polls the file for size changes due
/// to it being appended to; each file size change, it writes to an [Lwt_stream.t] everything that
/// has been appended since last append. (Except: the first item it places on the stream
/// comes not from the file, but rather from the [open_file_results] parameter; moreover
/// subsequent items that it reads from the file are culled if they refer to files
/// mentioned in [open_file_results]. This exception is a vehicle for (1) the rest of the
/// code to read IDE-results and file-results in a uniform way, (2) an easy way for us
/// to "mask" file-results by culling out all file-results that pertain to files open in the IDE.)
///
/// Once the file has been unlinked, then
/// the background watcher will gather everything that has been appended until
/// that point, write it to the stream, close the stream, and terminate.
/// Note: if you have a watcher, and unlink the file, and start a new file
/// with the same name without first waiting for the stream to close, then
/// there might be a race condition. Suggestion: wait for the stream to close
/// before starting a new file!
pub(crate) fn watch_refs_stream_file(
    file: &path::T,
    open_file_results: &uri_map::T<Vec<search_types::find_refs::Absolute>>,
) -> Receiver<Vec<HalfOpenOneBased>> {
    let (add, q) = crossbeam_channel::unbounded();
    let ide_results: Vec<HalfOpenOneBased> = uri_map::values(open_file_results)
        .concat()
        .iter()
        .map(|search_types::find_refs::Result { name: _, pos }| {
            find_refs_wire_format::from_absolute(pos)
        })
        .collect();
    if !ide_results.is_empty() {
        let _ = add.send(ide_results);
    }
    let file = file.clone();
    let open_file_results = open_file_results.clone();
    let watcher = move || -> std::io::Result<()> {
        let fd = std::fs::File::open(path::to_string(&file))?;
        let mut file_pos: i64 = 0;
        loop {
            let size = fd.metadata()?.len() as i64;
            if file_pos == size && !path::file_exists(&file) {
                // The stream only gets closed if we've read everything up to the end...
                return Ok(());
            } else if file_pos == size {
                std::thread::sleep(Duration::from_millis(200));
            } else {
                // `Lwt_utils.with_lock fd Unix.F_RLOCK ~f:(fun () -> Ide_stream.read_from_locked_file fd ~pos)`
                let raw = std::os::fd::AsRawFd::as_raw_fd(&fd);
                // `with_pos0`: lockf is applied starting at the file-descriptors current position.
                // Set it to 0 so that when we acquire or release the lock, we're locking from the
                // start of the file through to (len=0) the end; then restore it.
                let with_pos0 = |cmd: ocaml_unix::LockCommand| -> std::io::Result<()> {
                    use std::io::Seek;
                    let mut f = &fd;
                    let pos = f.stream_position()?;
                    f.seek(std::io::SeekFrom::Start(0))?;
                    let result = ocaml_unix::lockf(raw, cmd, 0);
                    f.seek(std::io::SeekFrom::Start(pos))?;
                    result
                };
                with_pos0(ocaml_unix::LockCommand::FRlock)?;
                let r = find_refs_wire_format::ide_stream::read_from_locked_file(&fd, file_pos);
                with_pos0(ocaml_unix::LockCommand::FUlock)?;
                let (results, new_pos) = match r {
                    Ok(r) => r,
                    Err(e) => panic!("{:?}", e),
                };
                file_pos = new_pos;
                let results: Vec<HalfOpenOneBased> = results
                    .into_iter()
                    .filter(|HalfOpenOneBased { filename, .. }| {
                        let uri = path_string_to_lsp_uri(filename, filename);
                        !open_file_results.contains_key(&uri)
                    })
                    .collect();
                if !results.is_empty() && add.send(results).is_err() {
                    return Ok(());
                }
            }
        }
    };
    std::thread::Builder::new()
        .name("ClientLspRefsFile".to_string())
        .spawn(move || {
            let _ = watcher();
        })
        .expect("could not start a thread");
    q
}

/// If there was a streaming find-refs result file, this function will unlink it.
/// We do this first just to clean up after ourselves, but second because doing this will
/// terminate the [watch_refs_stream_file] background thread.
pub(crate) fn unlink_refs_stream_file_if_present(shellable_type: &run_env::ShellableType) {
    if let run_env::ShellableType::FindRefs(run_env::ShelloutStandardResponse {
        stream_file: Some(run_env::StreamFile { file, .. }),
        ..
    }) = shellable_type
    {
        match std::fs::remove_file(path::to_string(file)) {
            Ok(()) => log(&format!(
                "unlinked streaming-find-refs file {}",
                path::to_string(file)
            )),
            Err(_e) => {
                // The [current_hh_shell] invariant is that if and only if it is Some, then the stream-file exists:
                // whoever changes [current_hh_shell] to None should be responsible for deleting it -- by calling this
                // function -- and can thereby be sure that the file exists when they try to delete it.
                // Hence: going down this codepath via ENOENT is unexpected.
                hh_logger::log("Streaming find-refs unlinking error")
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ErrorSource {
    ErrorFromClientFatal,
    ErrorFromClientRecoverable,
    ErrorFromDaemonRecoverable,
    ErrorFromLspCancelled,
    ErrorFromLspMisc,
}

/// `hack_log_error`: the log line (the rest is `Hack_event_logger`).
fn hack_log_error(
    _event: Option<&RefEvent>,
    e: &error::T,
    source: ErrorSource,
    _unblocked_time: f64,
) {
    let is_expected = match source {
        ErrorSource::ErrorFromLspCancelled => true,
        ErrorSource::ErrorFromClientFatal
        | ErrorSource::ErrorFromClientRecoverable
        | ErrorSource::ErrorFromDaemonRecoverable
        | ErrorSource::ErrorFromLspMisc => false,
    };
    if !is_expected {
        log(&lsp_fmt::error_to_log_string(e))
    }
}

/// Running the shell-outs of find-refs, go-to-impl and rename
/// (`Lwt_utils.exec_checked Exec_command.Current_executable cmd ~cancel ~env`).
pub(crate) mod shell_out {
    use std::io::Read;

    use super::*;

    /// `Unix.process_status`, the signal numbers as OCaml numbers them.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ProcessStatus {
        WExited(i32),
        WSignaled(isize),
        WStopped(isize),
    }

    /// `Process.status_to_string`
    pub fn status_to_string(status: ProcessStatus) -> String {
        match status {
            ProcessStatus::WExited(i) => format!("Unix.WEXITED {}", i),
            ProcessStatus::WSignaled(i) => format!("Unix.WSIGNALED {}", i),
            ProcessStatus::WStopped(i) => format!("Unix.WSTOPPED {}", i),
        }
    }

    /// OCaml's `Sys.sigkill`
    pub const SIGKILL: isize = -7;

    /// `Lwt_utils.Process_success.t`
    #[derive(Clone, Debug)]
    pub struct ProcessSuccess {
        /// (`command_line` and `stderr`: the OCaml never reads them either.)
        #[allow(dead_code)]
        pub command_line: String,
        pub stdout: String,
        #[allow(dead_code)]
        pub stderr: String,
        pub start_time: f64,
        pub end_time: f64,
    }

    /// `Lwt_utils.Process_failure.t`
    #[derive(Clone, Debug)]
    pub struct ProcessFailure {
        pub command_line: String,
        pub process_status: ProcessStatus,
        pub stdout: String,
        pub stderr: String,
        /// `exn option`: `Printexc.to_string` of it.
        pub exn: Option<String>,
        pub start_time: f64,
        pub end_time: f64,
    }

    pub type ProcessResult = Result<ProcessSuccess, ProcessFailure>;

    /// `Print_signal.string_of_signal`, on OCaml's signal numbers.
    fn string_of_signal(n: isize) -> String {
        let names = [
            (-1, "sigabrt"),
            (-2, "sigalrm"),
            (-3, "sigfpe"),
            (-4, "sighup"),
            (-5, "sigill"),
            (-6, "sigint"),
            (-7, "sigkill"),
            (-8, "sigpipe"),
            (-9, "sigquit"),
            (-10, "sigsegv"),
            (-11, "sigterm"),
            (-12, "sigusr1"),
            (-13, "sigusr2"),
            (-14, "sigchld"),
            (-15, "sigcont"),
            (-16, "sigstop"),
            (-17, "sigtstp"),
            (-18, "sigttin"),
            (-19, "sigttou"),
            (-20, "sigvtalrm"),
            (-21, "sigprof"),
            (-22, "sigbus"),
            (-23, "sigpoll"),
            (-24, "sigsys"),
            (-25, "sigtrap"),
            (-26, "sigurg"),
            (-27, "sigxcpu"),
            (-28, "sigxfsz"),
        ];
        match names.iter().find(|(i, _)| *i == n) {
            Some((_, name)) => name.to_string(),
            None => format!("unknown signal {}", n),
        }
    }

    /// `Lwt_utils.Process_failure.to_string`
    pub fn process_failure_to_string(process_failure: &ProcessFailure) -> String {
        let exn_message = match &process_failure.exn {
            Some(exn) => exn.clone(),
            None => "<none>".to_string(),
        };
        let exit_code = match process_failure.process_status {
            ProcessStatus::WExited(exit_code) => format!(
                "WEXITED {} ({})",
                exit_code,
                crate::exit_status::exit_code_to_string(exit_code as isize)
            ),
            ProcessStatus::WSignaled(exit_code) => format!(
                "WSIGNALLED {} ({}){}",
                exit_code,
                string_of_signal(exit_code),
                if exit_code == SIGKILL {
                    " - this often indicates a timeout"
                } else {
                    ""
                }
            ),
            ProcessStatus::WStopped(exit_code) => format!(
                "WSTOPPED {} ({})",
                exit_code,
                string_of_signal(exit_code)
            ),
        };
        let stderr = match process_failure.stderr.as_str() {
            "" => "<none>",
            stderr => stderr,
        };
        format!(
            "Process '{}' failed with\nExit code: {}\n{} -- {}\nException: {}\nStderr: {}\nStdout: {}",
            process_failure.command_line,
            exit_code,
            utils::timestring(process_failure.start_time),
            utils::timestring(process_failure.end_time),
            exn_message,
            stderr,
            process_failure.stdout
        )
    }

    /// The `(Process_success.t, Process_failure.t) Lwt_result.t` of a
    /// running shell-out.
    pub struct Process {
        rx: Receiver<ProcessResult>,
        result: Option<ProcessResult>,
    }

    impl Process {
        /// `not (Lwt.is_sleeping process)`
        pub fn is_resolved(&mut self) -> bool {
            if self.result.is_none() {
                if let Ok(r) = self.rx.try_recv() {
                    self.result = Some(r)
                }
            }
            self.result.is_some()
        }

        /// The result, once [`Process::is_resolved`].
        pub fn into_result(self) -> ProcessResult {
            self.result.expect("the shell-out has completed")
        }
    }

    /// `Lwt_utils.exec_checked program args ~cancel ~env`: `program` is the
    /// running executable (`Exec_command.Current_executable`); `env` is put
    /// before the environment of this process. Once `cancel` is resolved
    /// (its sender dropped), the process is killed (SIGKILL).
    pub fn exec_checked(
        args: Vec<String>,
        cancel: Receiver<()>,
        env: Vec<(String, String)>,
    ) -> Process {
        let start_time = ocaml_unix::gettimeofday();
        let program = path::to_string(&path::executable_name());
        let command_line = std::iter::once(program.clone())
            .chain(args.iter().cloned())
            .collect::<Vec<_>>()
            .join(" ");
        let (tx, rx) = crossbeam_channel::bounded(1);
        std::thread::Builder::new()
            .name("ClientLspShellOut".to_string())
            .spawn(move || {
                let mut command = std::process::Command::new(&program);
                command
                    .arg0(&program)
                    .args(&args)
                    .stdin(std::process::Stdio::null())
                    .stdout(std::process::Stdio::piped())
                    .stderr(std::process::Stdio::piped());
                for (k, v) in &env {
                    command.env(k, v);
                }
                let failure = |status, exn: Option<String>| ProcessFailure {
                    command_line: command_line.clone(),
                    process_status: status,
                    stdout: String::new(),
                    stderr: String::new(),
                    exn,
                    start_time,
                    end_time: ocaml_unix::gettimeofday(),
                };
                let mut child = match command.spawn() {
                    Ok(child) => child,
                    Err(e) => {
                        // The OCaml's child exits 127 when the exec fails.
                        let _ = tx.send(Err(failure(
                            ProcessStatus::WExited(127),
                            Some(format!("Unix.Unix_error(Unix.{:?}, \"execvp\", \"\")", e.kind())),
                        )));
                        return;
                    }
                };
                let mut out = child.stdout.take().unwrap();
                let mut err = child.stderr.take().unwrap();
                let out_reader = std::thread::spawn(move || {
                    let mut s = Vec::new();
                    let _ = out.read_to_end(&mut s);
                    String::from_utf8_lossy(&s).into_owned()
                });
                let err_reader = std::thread::spawn(move || {
                    let mut s = Vec::new();
                    let _ = err.read_to_end(&mut s);
                    String::from_utf8_lossy(&s).into_owned()
                });
                let mut killed = false;
                let status = loop {
                    match child.try_wait() {
                        Ok(Some(status)) => break Ok(status),
                        Ok(None) => {}
                        Err(e) => break Err(e),
                    }
                    if !killed {
                        let mut sel = Select::new();
                        sel.recv(&cancel);
                        if sel.ready_timeout(Duration::from_millis(20)).is_ok() {
                            killed = true;
                            let _ = child.kill();
                        }
                    } else {
                        std::thread::sleep(Duration::from_millis(20));
                    }
                };
                let stdout = out_reader.join().unwrap_or_default();
                let stderr = err_reader.join().unwrap_or_default();
                let end_time = ocaml_unix::gettimeofday();
                let result = match status {
                    Ok(status) => {
                        use std::os::unix::process::ExitStatusExt;
                        match (status.code(), status.signal(), status.stopped_signal()) {
                            (Some(0), _, _) => Ok(ProcessSuccess {
                                command_line,
                                stdout,
                                stderr,
                                start_time,
                                end_time,
                            }),
                            (code, signal, stopped) => {
                                let process_status = match (code, signal, stopped) {
                                    (Some(code), _, _) => ProcessStatus::WExited(code),
                                    (None, Some(signal), _) => ProcessStatus::WSignaled(
                                        ocaml_unix::rev_convert_signal_number(signal),
                                    ),
                                    (None, None, Some(signal)) => ProcessStatus::WStopped(
                                        ocaml_unix::rev_convert_signal_number(signal),
                                    ),
                                    (None, None, None) => ProcessStatus::WExited(0),
                                };
                                Err(ProcessFailure {
                                    command_line,
                                    process_status,
                                    stdout,
                                    stderr,
                                    exn: None,
                                    start_time,
                                    end_time,
                                })
                            }
                        }
                    }
                    Err(e) => Err(ProcessFailure {
                        stdout,
                        stderr,
                        end_time,
                        ..failure(ProcessStatus::WExited(127), Some(format!("{:?}", e)))
                    }),
                };
                let _ = tx.send(result);
            })
            .expect("could not start a thread");
        Process { rx, result: None }
    }

    use std::os::unix::process::CommandExt;
}

pub(crate) fn kickoff_shell_out_and_maybe_cancel(
    state: &mut State,
    shellable_type: run_env::ShellableType,
    triggering_request: run_env::TriggeringRequest,
) -> Result<ResultTelemetry, Exn> {
    terminate_if_version_changed_since_start_of_lsp();
    let compose_shellout_cmd = |from: &str, args: Vec<String>| -> Vec<String> {
        let mut args = args;
        args.extend([
            "--from".to_string(),
            format!("clientLsp:{}", from),
            "--json".to_string(),
            "--autostart-server".to_string(),
            "false".to_string(),
            path::to_string(&env().root),
        ]);
        args
    };
    match state {
        State::Running(lenv) => {
            // Cancel any existing shell-out, if there is one.
            if let Some(run_env::CurrentHhShell {
                mut cancellation_token,
                shellable_type,
                triggering_request:
                    run_env::TriggeringRequest {
                        id: prev_id,
                        metadata: prev_metadata,
                        request: prev_request,
                        start_time_local_handle: prev_start_time_local_handle,
                    },
                ..
            }) = lenv.current_hh_shell.take()
            {
                unlink_refs_stream_file_if_present(&shellable_type);
                // Send SIGTERM to the underlying process.
                // We won't wait for it -- that'd make it too hard to reason about concurrency.
                ensure_cancelled(&mut cancellation_token);
                // We still have to respond to the LSP's prev request. We'll do so now
                // without waiting for the underlying process to finish. In this way we fulfill
                // the invariant that "current_hh_shell must always give rise to an LSP response".
                // (Later in the function we overwrite current_hh_shell with the new shellout, so right here
                // right now is the only place that can fulfill that invariant for the prev shellout).
                let lsp_error = make_lsp_error(
                    Some(yojson::T::Assoc(vec![(
                        "new_request_id".to_string(),
                        yojson::T::String(lsp_fmt::id_to_string(&triggering_request.id)),
                    )])),
                    None,
                    None,
                    Some(error::RequestCancelled),
                    "Cancelled (displaced by another request)",
                );
                respond_jsonrpc(
                    PoweredBy::LanguageServer,
                    &prev_id,
                    &LspResult::ErrorResult(lsp_error.clone()),
                );
                hack_log_error(
                    Some(&RefEvent::ClientMessage(
                        prev_metadata,
                        LspMessage::RequestMessage(prev_id, prev_request),
                    )),
                    &lsp_error,
                    ErrorSource::ErrorFromDaemonRecoverable,
                    prev_start_time_local_handle,
                );
            }
            let (cancellation_token, cancel) = crossbeam_channel::bounded::<()>(1);
            let cmd = match &shellable_type {
                run_env::ShellableType::FindRefs(run_env::ShelloutStandardResponse {
                    symbol,
                    find_refs_action,
                    hint_suffixes,
                    stream_file,
                    ide_calculated_positions: _,
                }) => {
                    let (action, stream_file, hints) = find_refs_wire_format::cli_args::to_string_triple(
                        &find_refs_wire_format::cli_args::T {
                            symbol_name: symbol.clone(),
                            action: find_refs_action.clone(),
                            stream_file: stream_file.as_ref().map(|sf| sf.file.clone()),
                            hint_suffixes: hint_suffixes.clone(),
                        },
                    )
                    .map_err(|e| Exn::Other(exception::wrap(e)))?;
                    compose_shellout_cmd(
                        "find-refs-by-symbol",
                        vec![
                            "--ide-find-refs-by-symbol3".to_string(),
                            action,
                            stream_file,
                            hints,
                        ],
                    )
                }
                run_env::ShellableType::GoToImpl(run_env::ShelloutStandardResponse {
                    symbol,
                    find_refs_action,
                    ..
                }) => {
                    let symbol_action_arg =
                        find_refs_wire_format::cli_args::to_string(&find_refs_wire_format::cli_args::T {
                            symbol_name: symbol.clone(),
                            action: find_refs_action.clone(),
                            stream_file: None,
                            hint_suffixes: vec![],
                        })
                        .map_err(|e| Exn::Other(exception::wrap(e)))?;
                    compose_shellout_cmd(
                        "go-to-impl-by-symbol",
                        vec!["--ide-go-to-impl-by-symbol".to_string(), symbol_action_arg],
                    )
                }
                run_env::ShellableType::Rename {
                    symbol_definition,
                    find_refs_action,
                    new_name,
                    ..
                } => {
                    let name_action_definition_string =
                        server_command_types::rename::arguments_to_string_exn(
                            new_name,
                            find_refs_action,
                            &symbol_definition,
                        )
                        .map_err(|e| Exn::Other(exception::wrap(e)))?;
                    compose_shellout_cmd(
                        "rename",
                        vec![
                            "--ide-rename-by-symbol".to_string(),
                            name_action_definition_string,
                        ],
                    )
                }
            };
            // Two environment variables FIND_HH_START_TIME and FIND_HH_RETRIED are
            // used in HackEventLogger.ml for telemetry, expected to be set by the
            // caller find_hh.sh, but [Exec_command.Current_executable] bypasses
            // find_hh.sh and hence we need to override them ourselves.
            let env = vec![
                (
                    "FIND_HH_START_TIME".to_string(),
                    format!("{:.3}", ocaml_unix::gettimeofday()),
                ),
                ("FIND_HH_RETRIED".to_string(), "0".to_string()),
            ];
            let process = shell_out::exec_checked(cmd.clone(), cancel, env);
            log(&format!("kickoff_shell_out: {}", cmd.join(" ")));
            lenv.current_hh_shell = Some(run_env::CurrentHhShell {
                process,
                cancellation_token: Some(cancellation_token),
                shellable_type,
                triggering_request,
            });
            let result_telemetry = make_result_telemetry(None, Some(false), 0);
            Ok(result_telemetry)
        }
        _ => Ok(make_result_telemetry(None, None, 0)),
    }
}

/// If there's a current_hh_shell with [id], then send it a SIGTERM.
/// All we're doing is triggering the cancellation; we rely upon normal
/// [handle_shell_out_complete] for once the process has terminated.
fn cancel_shellout_if_applicable(state: &mut State, id: &LspId) {
    if let State::Running(run_env::T {
        current_hh_shell:
            Some(run_env::CurrentHhShell {
                cancellation_token,
                triggering_request: run_env::TriggeringRequest { id: peek_id, .. },
                ..
            }),
        ..
    }) = state
    {
        if lsp::id_key::compare(id, peek_id) == 0 {
            ensure_cancelled(cancellation_token)
        }
    }
}

// ~~ Protocol ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn do_shutdown(state: &mut State, ide_service: &client_ide_service::T, tracking_id: &str) {
    log("Received shutdown request");
    // `let _state = dismiss_diagnostics state in`: its new state is dropped.
    dismiss_diagnostics(state);
    stop_ide_service(
        ide_service,
        tracking_id,
        client_ide_service::stop_reason::T::EditorExited,
    );
    *state = State::PostShutdown;
}

fn state_to_rage(state: &State) -> String {
    let uris_to_string = |uris: Vec<DocumentUri>| {
        uris.iter()
            .map(|lsp::document_uri::Uri(uri)| uri.clone())
            .collect::<Vec<_>>()
            .join(",")
    };
    let timestamped_uris_to_string = |uris: Vec<(DocumentUri, (f64, DiagnosticsFrom))>| {
        uris.iter()
            .map(|(lsp::document_uri::Uri(uri), (timestamp, diagnostics_from))| {
                format!(
                    "{} [{}] @ {:.2}",
                    show_diagnostics_from(diagnostics_from),
                    uri,
                    timestamp
                )
            })
            .collect::<Vec<_>>()
            .join(",")
    };
    let details = match state {
        State::PreInit => String::new(),
        State::PostShutdown => String::new(),
        State::Running(lenv) => format!(
            "editor_open_files: {}\nuris_with_unsaved_changes: {}\nurs_with_standalone_diagnostics: {}\n",
            uris_to_string(uri_map::keys(&lenv.editor_open_files)),
            uris_to_string(lenv.uris_with_unsaved_changes.iter().cloned().collect()),
            timestamped_uris_to_string(uri_map::elements(&lenv.uris_with_standalone_diagnostics))
        ),
    };
    format!(
        "clientLsp state: {}\n{}\n",
        state_to_string(state),
        details
    )
}

fn do_rage_fb(state: &State) -> lsp::rage_fb::Result {
    let env = env();
    let current_version_and_switch = read_hhconfig_version_and_switch(&env.root);
    let data = format!(
        "{}\n\nversion previously read from .hhconfig and switch: {}\nversion in .hhconfig and switch: {}\n\n",
        state_to_rage(state),
        env.hhconfig_version_and_switch,
        current_version_and_switch
    );
    vec![lsp::rage_fb::RageItem { title: None, data }]
}

/// This reports on every live-squiggle-recheck that we attempt.
/// An Ok [result] means the recheck succeeded and we published diagnostics;
/// Error means the recheck was cancelled.
fn report_recheck_telemetry(
    trigger: &ErrorsTrigger,
    _ref_unblocked_time: &mut f64,
    uri: &DocumentUri,
    result: Result<&[Diagnostic], ()>,
) {
    let (result, _result_count) = match result {
        Ok([]) => ("publishedEmpty", Some(0)),
        Ok(diagnostics) => ("publishedErrors", Some(diagnostics.len())),
        Err(()) => ("cancelled", None),
    };
    let s = |x: &str| yojson::T::String(x.to_string());
    let mut extras = vec![
        ("telemetryKind".to_string(), s("timingForCheck")),
        ("checkScope".to_string(), s("file")),
        ("uri".to_string(), s(&lsp::string_of_uri(uri))),
        ("checkResult".to_string(), s(result)),
    ];
    match trigger {
        ErrorsTrigger::InitializeTrigger => extras.push(("triggerKind".to_string(), s("init"))),
        ErrorsTrigger::MessageTrigger { message, metadata } => extras.extend([
            ("triggerKind".to_string(), s("message")),
            (
                "durationMs".to_string(),
                yojson::T::Int(
                    ((ocaml_unix::gettimeofday() - metadata.timestamp) * 1000.0) as isize,
                ),
            ),
            (
                "triggerMessage".to_string(),
                yojson::T::Assoc(vec![
                    (
                        "method".to_string(),
                        s(&lsp_fmt::message_name_to_string(message)),
                    ),
                    ("activityId".to_string(), s(&metadata.activity_id)),
                ]),
            ),
        ]),
    }
    let notification = LspNotification::TelemetryNotification(
        lsp::log_message::LogMessageParams {
            type_: message_type::InfoMessage,
            message: "timing info for file check".to_string(),
        },
        extras,
    );
    notify_jsonrpc(PoweredBy::ServerlessIde, &notification);
    // `Hack_event_logger.client_lsp_recheck`: a no-op.
}

/// This function should be called anytime we've recomputed live squiggles
/// (e.g. upon didChange, codeAction, didClose). It (1) sends publishDiagnostics
/// as necessary, (2) sends an LSP telemetry/event to say what it has done.
fn publish_and_report_after_recomputing_live_squiggles(
    state: &mut State,
    file_path: &path::T,
    diagnostics: Vec<Diagnostic>,
    trigger: &ErrorsTrigger,
    ref_unblocked_time: &mut f64,
) -> Result<(), Exn> {
    match state {
        State::PreInit => Err(failwith("how we got errors before initialize?")),
        State::PostShutdown => Ok(()), // no-op
        State::Running(lenv) => {
            let file_path = path::to_string(file_path);
            let uri = path_string_to_lsp_uri(&file_path, &file_path);
            let params = ide_diagnostics_to_lsp_diagnostics(&file_path, &diagnostics);
            // (`Hack_event_logger.Diagnostics.log`, to track error lifetime: a no-op.)
            let notification = LspNotification::PublishDiagnosticsNotification(params);
            notify_jsonrpc(PoweredBy::ServerlessIde, &notification);
            report_recheck_telemetry(trigger, ref_unblocked_time, &uri, Ok(&diagnostics));
            if diagnostics.is_empty() {
                lenv.uris_with_standalone_diagnostics.remove(&uri);
            } else {
                lenv.uris_with_standalone_diagnostics.insert(
                    uri,
                    (
                        ocaml_unix::gettimeofday(),
                        DiagnosticsFrom::DiagnosticsFromClientIdeDaemon {
                            diagnostics,
                            validated: false,
                        },
                    ),
                );
            }
            Ok(())
        }
    }
}

/// `Unix.fstat fd`.st_ino
fn st_ino(fd: &std::fs::File) -> u64 {
    match fd.metadata() {
        Ok(stat) => stat.ino(),
        Err(e) => std::panic::panic_any(exception::wrap(unix_error(&e, "fstat", ""))),
    }
}

/// `Unix.Unix_error (err, call, arg)`, as `Printexc.to_string` prints it.
struct UnixError(String);

impl std::fmt::Debug for UnixError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

fn unix_error(e: &std::io::Error, call: &str, arg: &str) -> UnixError {
    let name = match e.raw_os_error() {
        Some(libc::ENOENT) => "ENOENT".to_string(),
        Some(libc::EACCES) => "EACCES".to_string(),
        Some(libc::EISDIR) => "EISDIR".to_string(),
        Some(libc::EBADF) => "EBADF".to_string(),
        Some(libc::EMFILE) => "EMFILE".to_string(),
        Some(libc::ENOTDIR) => "ENOTDIR".to_string(),
        Some(libc::EPERM) => "EPERM".to_string(),
        Some(n) => format!("EUNKNOWNERR {}", n),
        None => "EUNKNOWNERR 0".to_string(),
    };
    UnixError(format!("Unix.Unix_error(Unix.{}, {:?}, {:?})", name, call, arg))
}

/// When the errors-file gets new items or is closed, this function updates diagnostics as necessary,
/// and switches from TailingErrors to SeekingErrors if it's closed.
/// Principles: (1) don't touch open files, since they are governed solely by clientIdeDaemon;
/// (2) only update an existing diagnostic if the scrape's start_time is newer than it,
/// since these will have come recently from clientIdeDaemon, to which we grant primacy.
fn handle_errors_file_item(
    state: &mut State,
    item: Option<ErrorsItem>,
    error_filter: &filter_diagnostics::filter::T,
) -> Result<Option<ResultTelemetry>, Exn> {
    // a small helper, to send the actual lsp message
    let publish = |params: publish_diagnostics::Params| {
        notify_jsonrpc(
            PoweredBy::HhServer,
            &LspNotification::PublishDiagnosticsNotification(params),
        )
    };
    // a small helper, to construct empty diagnostic params
    let empty_diagnostics = |uri: DocumentUri| publish_diagnostics::Params {
        uri,
        diagnostics: vec![],
        is_status_fb: false,
    };
    // We must be in this state, else how could we have gotten an item from the errors-file q?
    // See code in [get_next_event].
    let mut conn = latest_hh_server_errors();
    let (lenv, fd, start_time) = match (&mut *state, &*conn) {
        (State::Running(lenv), ErrorsConn::TailingErrors { fd, start_time, .. }) => {
            (lenv, fd, *start_time)
        }
        _ => {
            return Err(failwith(
                "unexpected state when processing handle_errors_file_item",
            ));
        }
    };
    match item {
        None => {
            // We must have an item, because the errors-stream always ends with a sentinel, and we stop tailing upon the sentinel.
            log("Errors-file: unexpected end of stream");
            *conn = ErrorsConn::SeekingErrors {
                prev_st_ino: None,
                seek_reason: SeekReason::UnexpectedEndOfStream,
            };
            Ok(None)
        }
        Some(Err(watch_error)) => {
            let ino = st_ino(fd);
            // `Unix.close fd`: dropped with the old state.
            *conn = ErrorsConn::SeekingErrors {
                prev_st_ino: Some(ino),
                seek_reason: SeekReason::WatchError(Shared::new(watch_error)),
            };
            Ok(None)
        }
        Some(Ok(ReadResult::RCompleted(completion, log_message))) => {
            // Close the errors-file, and switch to "seeking mode" for the next errors-file to come along.
            let ino = st_ino(fd);
            match &completion {
                CompletionReason::Stopped => {
                    // At this point we'd like to erase all the squiggles that came from hh_server.
                    // All we'll do is leave the errors for now, and then a subsequent [try_open_errors_file]
                    // will determine that we've transitioned from an ok state (like we leave it in right now)
                    // to an error state, and it takes that opportunity to erase all squiggles.
                }
                CompletionReason::Restarted { .. } => {
                    // If the typecheck restarted, we'll just leave all existing errors as they are.
                    // We have no evidence upon which to add or erase anything.
                    // It will all be fixed in the next typecheck to complete.
                }
                CompletionReason::Complete(_telemetry) => {
                    // If the typecheck completed, then we can erase all diagnostics (from closed-files)
                    // that were reported prior to the start of the typecheck - regardless of whether that
                    // diagnostic had most recently been reported from errors-file or from clientIdeDaemon.
                    // Why only from closed-files? ... because diagnostics for open files are produced live by clientIdeDaemon,
                    // and our information from errors-file is necessarily more stale than that from clientIdeDaemon.
                    let mut kept = uri_map::T::new();
                    for (uri, (existing_time, diagnostics_from)) in
                        lenv.uris_with_standalone_diagnostics.iter()
                    {
                        if lenv.uris_with_unsaved_changes.contains(uri) || *existing_time > start_time {
                            kept.insert(uri.clone(), (*existing_time, diagnostics_from.clone()));
                        } else {
                            publish(empty_diagnostics(uri.clone()));
                        }
                    }
                    lenv.uris_with_standalone_diagnostics = kept;
                }
            }
            *conn = ErrorsConn::SeekingErrors {
                prev_st_ino: Some(ino),
                seek_reason: SeekReason::Completed(completion, log_message),
            };
            Ok(None)
        }
        Some(Ok(ReadResult::RItem(server_progress::ErrorsFileItem::Telemetry(_)))) => Ok(None),
        Some(Ok(ReadResult::RItem(server_progress::ErrorsFileItem::Errors { errors, timestamp }))) => {
            // If the php file is closed and has no diagnostics newer than start_time, replace or add.
            //
            // Why only for closed files? well, if the file is currently open in the IDE, then
            // clientIdeDaemon-generated diagnostics (1) reflect unsaved changes which the errors-file
            // doesn't, (2) is more up-to-date than the errors-file, or at least no older.
            //
            // Why only newer than start time? There are a lot of scenarios but all boil down to this
            // simple rule. (See the OCaml for the five of them.)
            let mut acc = lenv.uris_with_standalone_diagnostics.clone();
            for (path, file_errors) in errors.iter() {
                let path = relative_path::to_absolute(path);
                let uri = path_string_to_lsp_uri(&path, &path);
                if lenv.uris_with_unsaved_changes.contains(&uri) {
                    continue;
                }
                match acc.get(&uri) {
                    Some((existing_timestamp, _diagnostics_from))
                        if *existing_timestamp > start_time => {}
                    _ => {
                        let file_errors =
                            filter_diagnostics::filter_with_hash(error_filter, file_errors.clone());
                        // We do not precompute additional diagnostic information (like
                        // where to display additional LSP visual hints) for errors
                        // received from the server. They will in general only be received
                        // for closed files anyways.
                        let diagnostics: Vec<Diagnostic> = file_errors
                            .into_iter()
                            .map(client_ide_message::diagnostic_of_finalized_error_without_related_hints)
                            .collect();
                        publish(ide_diagnostics_to_lsp_diagnostics(&path, &diagnostics));
                        acc.insert(uri, (timestamp, DiagnosticsFrom::DiagnosticsFromErrorsFile));
                    }
                }
            }
            lenv.uris_with_standalone_diagnostics = acc;
            Ok(None)
        }
    }
}

/// If we're in [errors_conn = SeekingErrors], then this function will try to open the
/// current errors-file. If success then we'll set [latest_hh_server_errors] to [TailingErrors].
/// If failure then we'll set it to [SeekingErrors], which includes error explanation for why
/// the attempt failed. We'll also clear out all squiggles.
///
/// If the failure was due to a version mismatch, we also take the opportunity
/// to check: has the version changed under our feet since we ourselves started?
/// If it has, then we exit with an error code (so that VSCode will relaunch
/// the correct version of lsp afterwards). If it hasn't, then we continue,
/// and the version mismatch must necessarily indicate that hh_server is the
/// wrong version.
///
/// If we're in [errors_conn = TrailingErrors] already, this function is a no-op.
///
/// If we're called before even having received the initialize request from LSP client
/// (hence before we even know the project root), this is a no-op.
fn try_open_errors_file(state: &mut State) {
    let (prev_st_ino, seek_reason) = match &*latest_hh_server_errors() {
        ErrorsConn::TailingErrors { .. } => return,
        ErrorsConn::SeekingErrors {
            prev_st_ino,
            seek_reason,
        } => (*prev_st_ino, seek_reason.clone()),
    };
    let errors_file_path = server_files::errors_file_path(&env().root);
    // 1. can we open the file?
    let result: Result<std::fs::File, ErrorsConn> = {
        use std::os::unix::fs::OpenOptionsExt;
        match std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NONBLOCK)
            .open(&errors_file_path)
        {
            Ok(fd) => Ok(fd),
            Err(e) if e.raw_os_error() == Some(libc::ENOENT) => Err(ErrorsConn::SeekingErrors {
                prev_st_ino,
                seek_reason: SeekReason::AbsentErrorsFile,
            }),
            Err(e) => Err(ErrorsConn::SeekingErrors {
                prev_st_ino,
                seek_reason: SeekReason::ErrorFileOpenExn(format!(
                    "{:?}",
                    unix_error(&e, "open", &errors_file_path)
                )),
            }),
        }
    };
    // 2. is it different from the previous time we looked?
    let result = match (prev_st_ino, result) {
        (Some(ino), Ok(fd)) if ino == st_ino(&fd) => {
            drop(fd);
            Err(ErrorsConn::SeekingErrors {
                prev_st_ino,
                seek_reason,
            })
        }
        (_, result) => result,
    };
    // 3. can we [Server_progress.ErrorsRead.openfile] on it?
    let errors_conn = match result {
        Err(errors_conn) => errors_conn,
        Ok(fd) => match errors_read::openfile(&fd) {
            Err((e, log_message)) => {
                let prev_st_ino = Some(st_ino(&fd));
                drop(fd);
                log(&format!(
                    "Errors-file: failed to open. {} [{}]",
                    errors_read::show_open_error(&e),
                    log_message
                ));
                terminate_if_version_changed_since_start_of_lsp();
                ErrorsConn::SeekingErrors {
                    prev_st_ino,
                    seek_reason: SeekReason::ErrorFileOpenError(Shared::new(e), log_message),
                }
            }
            Ok(errors_read::OpenSuccess { timestamp, pid, .. }) => {
                log(&format!(
                    "Errors-file: opened and tailing the check from {}",
                    utils::timestring(timestamp)
                ));
                let reader = fd
                    .try_clone()
                    .unwrap_or_else(|e| std::panic::panic_any(exception::wrap(unix_error(&e, "dup", ""))));
                let watched = server_progress_lwt::watch_errors_file(pid, reader);
                let (tx, q) = crossbeam_channel::unbounded();
                std::thread::Builder::new()
                    .name("ClientLspErrorsFile".to_string())
                    .spawn(move || {
                        for item in watched {
                            if tx.send(item).is_err() {
                                break;
                            }
                        }
                    })
                    .expect("could not start a thread");
                ErrorsConn::TailingErrors {
                    fd,
                    start_time: timestamp,
                    q,
                }
            }
        },
    };
    // If we've transitioned to failure, then we'll have to erase all outstanding squiggles.
    // It'd be nice to leave the ones produced by clientIdeDaemon.
    // But that's too much book-keeping to be worth complicating the code for an edge case,
    // so in the words of c3po "shut them all down. hurry!"
    let is_ok = |conn: &ErrorsConn| match conn {
        ErrorsConn::TailingErrors { .. } => true,
        ErrorsConn::SeekingErrors { seek_reason, .. } => match seek_reason {
            SeekReason::Init
            | SeekReason::Completed(CompletionReason::Complete(_), _)
            | SeekReason::Completed(CompletionReason::Restarted { .. }, _) => true,
            SeekReason::UnexpectedEndOfStream
            | SeekReason::WatchError(_)
            | SeekReason::Completed(CompletionReason::Stopped, _)
            | SeekReason::AbsentErrorsFile
            | SeekReason::ErrorFileOpenExn(_)
            | SeekReason::ErrorFileOpenError(..) => false,
        },
    };
    let has_transitioned_to_failure = is_ok(&latest_hh_server_errors()) && !is_ok(&errors_conn);
    if has_transitioned_to_failure {
        dismiss_diagnostics(state)
    }
    *latest_hh_server_errors() = errors_conn;
}

/// This function handles the success/failure of a shell-out.
/// It is guaranteed to produce an LSP response for [shellable_type].
fn handle_shell_out_complete(
    result: shell_out::ProcessResult,
    triggering_request: run_env::TriggeringRequest,
    shellable_type: run_env::ShellableType,
) -> Result<Option<ResultTelemetry>, Exn> {
    let start_postprocess_time = ocaml_unix::gettimeofday();
    let make_duration_telemetry = |start_time: f64, end_time: f64| {
        let end_postprocess_time = ocaml_unix::gettimeofday();
        let start_time_local_handle = triggering_request.start_time_local_handle;
        let t = telemetry::create();
        let t = telemetry::duration(Some("local_duration"), start_time_local_handle, Some(start_time), t);
        let t = telemetry::duration(Some("shellout_duration"), start_time, Some(end_time), t);
        let t = telemetry::duration(
            Some("post_shellout_wait"),
            end_time,
            Some(start_postprocess_time),
            t,
        );
        telemetry::duration(
            Some("postprocess_duration"),
            start_postprocess_time,
            Some(end_postprocess_time),
            t,
        )
    };
    let (lsp_result, result_count, result_extra_data) = match result {
        Err(failure) => {
            let shell_out::ProcessFailure {
                start_time,
                end_time,
                stderr,
                stdout,
                command_line,
                process_status,
                exn: _,
            } = &failure;
            let code = match process_status {
                shell_out::ProcessStatus::WSignaled(shell_out::SIGKILL) => error::RequestCancelled,
                _ => error::InternalError,
            };
            let process_status = shell_out::status_to_string(*process_status);
            log(&format!(
                "shell-out failure: {}",
                shell_out::process_failure_to_string(&failure)
            ));
            let message = [stderr.as_str(), stdout.as_str(), process_status.as_str()]
                .iter()
                .map(|s| s.trim())
                .filter(|s| !s.is_empty())
                .collect::<Vec<_>>()
                .join("\n");
            let telemetry = make_duration_telemetry(*start_time, *end_time);
            let telemetry = telemetry::string_(None, "command_line", command_line, telemetry);
            let telemetry = telemetry::string_(None, "status", &process_status, telemetry);
            // `Telemetry.error ~e:message`
            let telemetry = telemetry::json(
                "error",
                yojson::T::Assoc(vec![("message".to_string(), yojson::T::String(message.clone()))]),
                telemetry,
            );
            let lsp_error = make_lsp_error(
                Some(telemetry::to_yojson(&telemetry)),
                None,
                Some(false),
                Some(code),
                &message,
            );
            unlink_refs_stream_file_if_present(&shellable_type);
            (LspResult::ErrorResult(lsp_error), 0, None)
        }
        Ok(shell_out::ProcessSuccess {
            stdout,
            start_time,
            end_time,
            ..
        }) => {
            log(&format!(
                "shell-out completed. {}",
                crate::string_utils::truncate(
                    80,
                    crate::string_utils::split_into_lines(&stdout)
                        .first()
                        .map(|s| s.as_str())
                        .unwrap_or("")
                )
            ));
            let r = std::panic::catch_unwind(AssertUnwindSafe(|| -> Result<(LspResult, isize), Exn> {
                match shellable_type {
                    run_env::ShellableType::FindRefs(shellout_standard_response) => {
                        let hh_locations = shellout_locations_to_lsp_locations_exn(&stdout)?;
                        do_find_references::do_find_references2(
                            shellout_standard_response,
                            hh_locations,
                        )
                    }
                    run_env::ShellableType::GoToImpl(run_env::ShelloutStandardResponse {
                        ide_calculated_positions,
                        ..
                    }) => {
                        let hh_locations = shellout_locations_to_lsp_locations_exn(&stdout)?;
                        do_go_to_implementation::do_go_to_implementation2(
                            ide_calculated_positions,
                            hh_locations,
                        )
                    }
                    run_env::ShellableType::Rename {
                        ide_calculated_patches,
                        ..
                    } => {
                        let hh_edits =
                            do_document_rename::shellout_patch_list_to_lsp_edits_exn(&stdout)?;
                        do_document_rename::do_document_rename2(ide_calculated_patches, hh_edits)
                    }
                }
            }));
            let r = match r {
                Ok(r) => r,
                Err(payload) => Err(Exn::Other(exception::wrap(payload))),
            };
            match r {
                Ok((lsp_result, result_count)) => (
                    lsp_result,
                    result_count,
                    Some(make_duration_telemetry(start_time, end_time)),
                ),
                Err(exn) => {
                    let (message, stack) = exn_ctor_and_stack(&exn);
                    let telemetry = make_duration_telemetry(start_time, end_time);
                    let lsp_error = make_lsp_error(
                        Some(telemetry::to_yojson(&telemetry)),
                        Some(&stack),
                        Some(false),
                        Some(error::InternalError),
                        &message,
                    );
                    (LspResult::ErrorResult(lsp_error), 0, None)
                }
            }
        }
    };
    let run_env::TriggeringRequest {
        id,
        metadata,
        start_time_local_handle,
        request,
    } = triggering_request;
    // The normal error-response-and-logging flow isn't easy for us to fit into,
    // because it handles errors+exceptions thinking they come from the current event.
    // So we'll do our json response and error-logging ourselves.
    respond_jsonrpc(PoweredBy::HhServer, &id, &lsp_result);
    match lsp_result {
        LspResult::ErrorResult(lsp_error) => {
            hack_log_error(
                Some(&RefEvent::ClientMessage(
                    metadata,
                    LspMessage::RequestMessage(id, request),
                )),
                &lsp_error,
                ErrorSource::ErrorFromDaemonRecoverable,
                start_time_local_handle,
            );
            Ok(Some(make_result_telemetry(None, Some(false), 0)))
        }
        _ => Ok(Some(make_result_telemetry(
            result_extra_data,
            None,
            result_count,
        ))),
    }
}

/// `Exception.get_ctor_string` and `Exception.get_backtrace_string` of an
/// exception, for the handlers that turn any exception into an LSP error.
fn exn_ctor_and_stack(exn: &Exn) -> (String, String) {
    match exn {
        Exn::Other(e) => (exception::get_ctor_string(e), exception::get_backtrace_string(e)),
        Exn::LspException(_) | Exn::DaemonNonfatalException(_) => (
            if matches!(exn, Exn::LspException(_)) {
                "Lsp.Error.LspException(_)".to_string()
            } else {
                "Client_lsp.Daemon_nonfatal_exception(_)".to_string()
            },
            String::new(),
        ),
        Exn::ClientFatalConnectionException(_) => (
            "Client_lsp.Client_fatal_connection_exception(_)".to_string(),
            String::new(),
        ),
        Exn::ClientRecoverableConnectionException(_) => (
            "Client_lsp.Client_recoverable_connection_exception(_)".to_string(),
            String::new(),
        ),
    }
}

fn do_initialize(initialize_params: &initialize::Params) -> initialize::Result {
    use initialize::*;
    let env = env();
    Result {
        server_capabilities: ServerCapabilities {
            text_document_sync: TextDocumentSyncOptions {
                open_close: true,
                change: TextDocumentSyncKind::IncrementalSync,
                will_save: false,
                will_save_wait_until: !env.args.disable_format_on_save,
                did_save: Some(SaveOptions { include_text: false }),
            },
            hover_provider: true,
            completion_provider: Some(completion_options::T {
                resolve_provider: true,
                completion_trigger_characters: ["$", ">", "\\", ":", "<", "[", "'", "\"", "{", "#"]
                    .iter()
                    .map(|s| s.to_string())
                    .collect(),
            }),
            signature_help_provider: Some(SignatureHelpOptions {
                sighelp_trigger_characters: vec!["(".to_string(), ",".to_string()],
            }),
            definition_provider: true,
            type_definition_provider: true,
            references_provider: true,
            call_hierarchy_provider: true,
            document_highlight_provider: true,
            document_symbol_provider: true,
            workspace_symbol_provider: true,
            code_action_provider: Some(code_action_options::T {
                resolve_provider: true,
            }),
            code_lens_provider: None,
            document_formatting_provider: true,
            document_range_formatting_provider: true,
            document_on_type_formatting_provider:
                // the Code@FB client always sets this to `true`, but non-Code@FB clients are likely to use `false`
                if !initialize_params
                    .initialization_options
                    .skip_lsp_server_on_type_formatting
                {
                    Some(DocumentOnTypeFormattingOptions {
                        first_trigger_character: ";".to_string(),
                        more_trigger_character: vec!["}".to_string()],
                    })
                } else {
                    None
                },
            rename_provider: true,
            document_link_provider: None,
            execute_command_provider: None,
            implementation_provider: env.local_config.go_to_implementation,
            rage_provider_fb: true,
            server_experimental: Some(server_experimental_capabilities::T {
                snippet_text_edit: true,
                auto_close_jsx: true,
            }),
        },
    }
}

fn do_did_change_watched_files_register_capability() -> LspRequest {
    // We want a glob-pattern like "**/*.{php,phpt,hack,hackpartial,hck,hh,hhi,xhp}".
    // I'm constructing it from Find_utils.extensions so our glob-pattern doesn't get out
    // of sync with Find_utils.file_filter.
    let extensions: Vec<String> = find_utils::EXTENSIONS
        .iter()
        .map(|s| s.strip_prefix('.').unwrap_or(s).to_string())
        .collect();
    let glob_pattern = format!("**/*.{{{}}}", extensions.join(","));
    let registration_options = lsp::LspRegistrationOptions::DidChangeWatchedFilesRegistrationOptions(
        lsp::did_change_watched_files::RegisterOptions {
            watchers: vec![lsp::did_change_watched_files::FileSystemWatcher { glob_pattern }],
        },
    );
    let registration = lsp::register_capability::make_registration(registration_options);
    LspRequest::RegisterCapabilityRequest(lsp::register_capability::Params {
        registrations: vec![registration],
    })
}

fn track_open_and_recent_files(state: &mut State, event: &Event) -> Result<(), Exn> {
    // We'll keep track of which files are opened by the editor.
    if let State::Running(lenv) = state {
        let prev_opened_files = &mut lenv.editor_open_files;
        match event {
            Event::ClientMessage(_, LspMessage::NotificationMessage(LspNotification::DidOpenNotification(params))) => {
                let doc = params.text_document.clone();
                let uri = params.text_document.uri.clone();
                prev_opened_files.insert(uri, doc);
            }
            Event::ClientMessage(_, LspMessage::NotificationMessage(LspNotification::DidChangeNotification(params))) => {
                let uri = &params.text_document.uri;
                if let Some(doc) = prev_opened_files.get(uri) {
                    let doc_ = text_document_item::T {
                        version: params.text_document.version,
                        text: lsp_helpers::apply_changes_unsafe(&doc.text, &params.content_changes),
                        ..doc.clone()
                    };
                    prev_opened_files.insert(uri.clone(), doc_);
                }
            }
            Event::ClientMessage(_, LspMessage::NotificationMessage(LspNotification::DidCloseNotification(params))) => {
                let uri = &params.text_document.uri;
                prev_opened_files.remove(uri);
            }
            _ => {}
        }
    }
    Ok(())
}

fn track_edits_if_necessary(state: &mut State, event: &Event) {
    // We'll keep track of which files have unsaved edits. Note that not all
    // clients send didSave messages; for those we only rely on didClose.
    let mut uris_with_unsaved_changes = get_uris_with_unsaved_changes(state);
    match event {
        Event::ClientMessage(_, LspMessage::NotificationMessage(LspNotification::DidChangeNotification(params))) => {
            uris_with_unsaved_changes.insert(params.text_document.uri.clone());
        }
        Event::ClientMessage(_, LspMessage::NotificationMessage(LspNotification::DidCloseNotification(params))) => {
            uris_with_unsaved_changes.remove(&params.text_document.uri);
        }
        Event::ClientMessage(_, LspMessage::NotificationMessage(LspNotification::DidSaveNotification(params))) => {
            uris_with_unsaved_changes.remove(&params.text_document.uri);
        }
        _ => {}
    }
    if let State::Running(lenv) = state {
        lenv.uris_with_unsaved_changes = uris_with_unsaved_changes;
    }
}

pub(crate) const SHORT_TIMEOUT: f64 = 2.5;

pub(crate) const LONG_TIMEOUT: f64 = 15.0;

/// If a message is stale, throw the necessary exception to cancel it. A message is
/// considered stale if it's sufficiently old and there are other messages in the queue
/// that are newer than it.
pub(crate) fn cancel_if_stale(client: &jsonrpc::T, timestamp: f64, timeout: f64) -> Result<(), Exn> {
    let time_elapsed = ocaml_unix::gettimeofday() - timestamp;
    if time_elapsed >= timeout
        && jsonrpc::has_message(client)
        && !crate::sys_utils::deterministic_behavior_for_tests()
    {
        let message = if timestamp < *BINARY_START_TIME {
            "binary took too long to launch"
        } else {
            "request timed out"
        };
        Err(lsp_exception(error::RequestCancelled, message))
    } else {
        Ok(())
    }
}

/// Assert that workers from the worker controller are not stopped.
fn assert_workers_are_not_stopped() {
    if worker_cancel::is_stop_requested() {
        // (`Hack_event_logger.invariant_violation_bug "ClientLsp workers are stopped but shouldn't be"`)
        worker_cancel::resume_workers();
    }
}

/// This predicate will return true if and only if the second parameter
/// is a $/cancelRequest notification for LSP request [message].
/// (`Err`: the exception the parse of the queued message raised.)
fn is_cancellation_of_request(
    message: &LspMessage,
    jsonrpc::TimestampedJson { json, .. }: &jsonrpc::TimestampedJson,
) -> Result<bool, Exn> {
    match message {
        LspMessage::ResponseMessage(..) | LspMessage::NotificationMessage(_) => Ok(false),
        LspMessage::RequestMessage(id, _request) => {
            // `exception Is_response`: `parse_lsp` raises it as soon as it
            // asks for the request of a response.
            let is_response = Cell::new(false);
            let peek = std::panic::catch_unwind(AssertUnwindSafe(|| {
                lsp_fmt::parse_lsp(json, |_| {
                    is_response.set(true);
                    LspRequest::ShutdownRequest
                })
            }));
            if is_response.get() {
                return Ok(false);
            }
            match peek {
                Err(payload) => Err(Exn::Other(exception::wrap(payload))),
                Ok(Err(e)) => Err(e.into()),
                Ok(Ok(LspMessage::NotificationMessage(LspNotification::CancelRequestNotification(
                    lsp::cancel_request::Params { id: peek_id },
                )))) => Ok(lsp::id_key::compare(id, &peek_id) == 0),
                Ok(Ok(_)) => Ok(false),
            }
        }
    }
}

/// This will run [f] but wrap it up in a way that respects cancellation:
/// 1. If there's already a cancellation request for [message] in the queue, then we'll
///    just raise [RequestCancelled] Lsp exception immediately.
/// 2. Otherwise, we'll await the callback [f], but if a cancellation request arrives
///    in the queue while awaiting then we'll use [WorkerCancel.stop_workers] to cooperatively
///    request it to finish.
///
/// INVARIANT: only one concurrent caller should invoke this function. (why? because
/// our cancellation mechanism [WorkerCancel.stop_workers] is a single bit, hence unable
/// to know which of multiple concurrent calls should be stopped).
///
/// INVARIANT: This function assumes the invariant that workers are not stopped
/// prior to entering this function, and restores the invariant upon exiting.
fn respect_cancellation<A>(
    client: &Arc<jsonrpc::T>,
    message: &LspMessage,
    f: impl FnOnce() -> Result<A, Exn>,
) -> Result<A, Exn> {
    assert_workers_are_not_stopped();
    // Explanation: this statement embodies the invariant that workers are not
    // stopped prior to entering. This function is the only place in the code which
    // can stop workers, and it unstops workers in its [~finally] clause.
    //
    // The predicate's exception, if it raises one (the OCaml's predicate
    // raises out of `Jsonrpc.await_until_found`): the first one wins.
    let predicate_error: Arc<Mutex<Option<Exn>>> = Arc::new(Mutex::new(None));
    let predicate = {
        let predicate_error = Arc::clone(&predicate_error);
        let message = message.clone();
        move |m: &jsonrpc::TimestampedJson| -> bool {
            match is_cancellation_of_request(&message, m) {
                Ok(b) => b,
                Err(e) => {
                    let mut pe = predicate_error.lock().unwrap_or_else(|e| e.into_inner());
                    if pe.is_none() {
                        *pe = Some(e);
                    }
                    // stop looking: the promise has failed
                    true
                }
            }
        }
    };
    // Following promise will be fulfilled immediately if cancellation is already in the queue;
    // otherwise will be fulfilled when it eventually arrives, or with [None] if [cancellation_token]
    // is completed first or if there's a stream error
    if jsonrpc::find_already_queued_message(&predicate, client).is_some() {
        if let Some(e) = predicate_error.lock().unwrap_or_else(|e| e.into_inner()).take() {
            return Err(e);
        }
        // If there was already a cancel request in the queue, we'll skip all processing right now!
        return Err(lsp_exception(error::RequestCancelled, "request cancelled"));
    }
    // Otherwise, cancellation will cooperatively request clientIdeDaemon to stop
    let (cancellation_source, cancellation_token) = crossbeam_channel::bounded::<()>(1);
    let promise = {
        let client = Arc::clone(client);
        std::thread::Builder::new()
            .name("ClientLspCancellation".to_string())
            .spawn(move || {
                let cancel_notification_opt =
                    jsonrpc::await_until_found(&client, predicate, &cancellation_token);
                match cancel_notification_opt {
                    None => {}
                    Some(jsonrpc::TimestampedJson { timestamp, .. }) => lwt::with_lock(|| {
                        hh_logger::log(&format!(
                            "acting upon cancellation at {}",
                            utils::timestring(timestamp)
                        ));
                        worker_cancel::stop_workers()
                    }),
                }
            })
            .expect("could not start a thread")
    };
    let result = std::panic::catch_unwind(AssertUnwindSafe(f));
    // `~finally`
    drop(cancellation_source);
    let _ = lwt::yield_during(|| promise.join());
    worker_cancel::resume_workers();
    let result = match result {
        Ok(result) => result,
        Err(payload) => std::panic::resume_unwind(payload),
    };
    match result {
        Ok(a) => match predicate_error.lock().unwrap_or_else(|e| e.into_inner()).take() {
            Some(e) => Err(e),
            None => Ok(a),
        },
        Err(e) => Err(e),
    }
}

/// This function is called upon didOpen/didChange
/// to stick a uri into the [uris_that_need_check] queue.
fn send_file_to_ide_and_defer_check(
    ide_service: &client_ide_service::T,
    state: &mut State,
    uri: &DocumentUri,
    file_contents: String,
    trigger: ErrorsTrigger,
    ref_unblocked_time: &mut f64,
) -> Result<(), Exn> {
    let file_path = path::make(&lsp_uri_to_path(uri)?);
    let tracking_id = match &trigger {
        ErrorsTrigger::InitializeTrigger => random_id::short_string(),
        ErrorsTrigger::MessageTrigger { metadata, .. } => metadata.tracking_id.clone(),
    };
    let _errors = ide_rpc(
        ide_service,
        &tracking_id,
        ref_unblocked_time,
        client_ide_message::request::did_open_or_change(client_ide_message::Document {
            file_path,
            file_contents,
        }),
    )?;
    if let State::Running(renv) = state {
        if let Some(prev_trigger) = renv.uris_that_need_check.get(uri) {
            // We had a previous trigger to typecheck the file and then a new trigger arrived.
            // How to report on the previous attempt? ... as cancelled, just like the rest of LSP does it.
            report_recheck_telemetry(prev_trigger, ref_unblocked_time, uri, Err(()));
        }
        renv.uris_that_need_check.insert(uri.clone(), trigger);
    }
    Ok(())
}

// ~~ Message handling ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// send DidOpen/Close/Change/Save ide_service as needed
fn handle_editor_buffer_message(
    state: &mut State,
    ide_service: &client_ide_service::T,
    metadata: &IncomingMetadata,
    ref_unblocked_time: &mut f64,
    message: &LspMessage,
) -> Result<(), Exn> {
    let uri_to_path = |uri: &DocumentUri| -> Result<path::T, Exn> { Ok(path::make(&lsp_uri_to_path(uri)?)) };
    match message {
        LspMessage::NotificationMessage(
            LspNotification::DidOpenNotification(lsp::did_open::Params {
                text_document: text_document_item::T { uri, .. },
            })
            | LspNotification::DidChangeNotification(lsp::did_change::Params {
                text_document: lsp::versioned_text_document_identifier::T { uri, .. },
                ..
            }),
        ) => {
            let editor_open_files = editor_open_files_or_empty(state);
            let file_contents = get_document_contents(&editor_open_files, uri)?;
            send_file_to_ide_and_defer_check(
                ide_service,
                state,
                uri,
                file_contents,
                ErrorsTrigger::MessageTrigger {
                    metadata: metadata.clone(),
                    message: message.clone(),
                },
                ref_unblocked_time,
            )
        }
        LspMessage::NotificationMessage(LspNotification::DidCloseNotification(params)) => {
            let uri = &params.text_document.uri;
            let file_path = uri_to_path(uri)?;
            let diagnostics = ide_rpc(
                ide_service,
                &metadata.tracking_id,
                ref_unblocked_time,
                client_ide_message::request::did_close(file_path.clone()),
            )?;
            let trigger = ErrorsTrigger::MessageTrigger {
                message: message.clone(),
                metadata: metadata.clone(),
            };
            publish_and_report_after_recomputing_live_squiggles(
                state,
                &file_path,
                diagnostics,
                &trigger,
                ref_unblocked_time,
            )?;
            if let State::Running(renv) = state {
                if let Some(prev_trigger) = renv.uris_that_need_check.get(uri) {
                    report_recheck_telemetry(prev_trigger, ref_unblocked_time, uri, Err(()));
                }
                renv.uris_that_need_check.remove(uri);
            }
            Ok(())
        }
        _ => {
            // Don't handle other events for now. When we show typechecking errors for
            // the open file, we'll start handling them.
            *ref_unblocked_time = ocaml_unix::gettimeofday();
            Ok(())
        }
    }
}

fn set_verbose_to_file(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    value: bool,
) -> Result<(), Exn> {
    VERBOSE_TO_FILE.store(value, Ordering::SeqCst);
    if VERBOSE_TO_FILE.load(Ordering::SeqCst) {
        hh_logger::level::set_min_level_file(hh_logger::level::T::Debug)
    } else {
        hh_logger::level::set_min_level_file(hh_logger::level::T::Info)
    }
    let mut ref_unblocked_time = 0.;
    ide_rpc(
        ide_service,
        tracking_id,
        &mut ref_unblocked_time,
        client_ide_message::request::verbose_to_file(VERBOSE_TO_FILE.load(Ordering::SeqCst)),
    )
}

/// Process and respond to a message from VSCode, and update [state] accordingly.
fn handle_client_message(
    state: &mut State,
    client: &jsonrpc::T,
    ide_service: &client_ide_service::T,
    metadata: &IncomingMetadata,
    message: &LspMessage,
    ref_unblocked_time: &mut f64,
) -> Result<Option<ResultTelemetry>, Exn> {
    use LspMessage::*;
    use LspNotification::*;
    use LspRequest::*;
    // make sure to wrap any exceptions below in the promise
    let tracking_id = metadata.tracking_id.as_str();
    let timestamp = metadata.timestamp;
    let editor_open_files = editor_open_files_or_empty(state);
    let rt = |count: usize| Ok(Some(make_result_telemetry(None, None, count as isize)));
    match (&*state, message) {
        // response
        (_, ResponseMessage(id, response)) => {
            let handler = match requests_outstanding().get(id) {
                Some((_, handler)) => Arc::clone(handler),
                None => return Err(Exn::Other(exception::wrap(NotFound))),
            };
            handler(response, state);
            Ok(None)
        }
        // shutdown request
        (_, RequestMessage(id, ShutdownRequest)) => {
            do_shutdown(state, ide_service, tracking_id);
            respond_jsonrpc(PoweredBy::LanguageServer, id, &LspResult::ShutdownResult);
            Ok(None)
        }
        // cancel notification
        (_, NotificationMessage(CancelRequestNotification(lsp::cancel_request::Params { id }))) => {
            // Most requests are handled in-order here in clientLsp:
            // our loop gets around to pickup up request ID "x" off the queue,
            // before doing anything else it does [cancel_if_has_pending_cancel_request]
            // to see if there's a CancelRequestNotification ahead of it in the queue
            // and if so just sends a cancellation response rather than handling it.
            // Thus, we'll still get around to picking the CancelRequestNotification
            // off the queue right here and now, which is fine!
            //
            // A few requests are handled asynchronously, though -- those that shell out
            // to hh. In these cases, upon receipt of the CancelRequestNotification,
            // we should actively SIGTERM the shell-out...
            cancel_shellout_if_applicable(state, id);
            Ok(None)
        }
        // exit notification
        (_, NotificationMessage(ExitNotification)) => {
            if is_post_shutdown(state) {
                exit_ok()
            } else {
                exit_fail()
            }
        }
        // setTrace notification
        (_, NotificationMessage(SetTraceNotification(params)))
        | (_, NotificationMessage(SetTrace(params))) => {
            let value = match params {
                lsp::set_trace_notification::Params::Verbose => true,
                lsp::set_trace_notification::Params::Off => false,
            };
            set_verbose_to_file(ide_service, tracking_id, value)?;
            Ok(None)
        }
        // test entrypoint: shutdown client_ide_service
        (_, RequestMessage(id, HackTestShutdownServerlessRequestFB)) => {
            stop_ide_service(
                ide_service,
                tracking_id,
                client_ide_service::stop_reason::T::Testing,
            );
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::HackTestShutdownServerlessResultFB,
            );
            Ok(None)
        }
        // test entrypoint: stop hh_server
        (_, RequestMessage(id, HackTestStopServerRequestFB)) => {
            let env = env();
            lwt::yield_during(|| client_stop::kill_server(&env.root, &env.args.from))
                .map_err(|e| Exn::Other(exception::wrap(e)))?;
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::HackTestStopServerResultFB,
            );
            Ok(None)
        }
        // test entrypoint: start hh_server
        (_, RequestMessage(id, HackTestStartServerRequestFB)) => {
            start_server();
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::HackTestStartServerResultFB,
            );
            Ok(None)
        }
        // initialize request
        (State::PreInit, RequestMessage(id, InitializeRequest(initialize_params))) => {
            let initialize_params = Arc::new(initialize_params.clone());
            *INITIALIZE_PARAMS_REF.lock().unwrap_or_else(|e| e.into_inner()) =
                Some(Arc::clone(&initialize_params));
            let root_from_initialize_params = match wwwroot::interpret_command_line_root_parameter(&[
                lsp_helpers::get_root(&initialize_params)?,
            ])
            .map_err(|e| Exn::Other(exception::wrap(e)))?
            {
                Ok(root) => root,
                Err(message) => {
                    // Unlike in hh_client, we do *not* currently get telemetry in hh_server_events
                    // for invocations of `hh_client lsp` in directories with bad roots.
                    // Seems fine: invocations of `hh_client lsp` are usually done
                    // deterministic and not by agents nor humans.
                    eprintln!("Error: {}", message);
                    let _ = std::io::stderr().flush();
                    exit_process(1)
                }
            };
            let env_ = env();
            if !path::equal(&env_.args.root_from_cli, &root_from_initialize_params) {
                let data = format!(
                    "root_from_cli={} initialize.root={}",
                    path::to_string(&env_.args.root_from_cli),
                    path::to_string(&root_from_initialize_params)
                );
                return Err(failwith(&format!(
                    "lsp initialize.root differs from launch arg - {}",
                    data
                )));
            }
            *state = State::Running(run_env::T {
                editor_open_files: uri_map::T::new(),
                uris_that_need_check: uri_map::T::new(),
                uris_with_unsaved_changes: uri_set::T::new(),
                uris_with_standalone_diagnostics: uri_map::T::new(),
                current_hh_shell: None,
            });
            let result = do_initialize(&initialize_params);
            respond_jsonrpc(
                PoweredBy::LanguageServer,
                id,
                &LspResult::InitializeResult(result),
            );
            run_ide_service(ide_service, &initialize_params, None);
            // Invariant: at all times after InitializeRequest, ide_service has
            // already been sent an "initialize" message.
            let id = lsp::NumberId(jsonrpc::get_next_request_id());
            let request = do_did_change_watched_files_register_capability();
            to_stdout(lsp_fmt::print_lsp_request(&id, &request));
            // TODO: our handler should really handle an error response properly
            let handler: ResultHandler = Arc::new(|_response, _state| {});
            requests_outstanding().insert(id, (request, handler));
            if !crate::sys_utils::deterministic_behavior_for_tests() {
                lsp_helpers::telemetry_log(
                    &to_stdout,
                    None,
                    &format!(
                        "Version in hhconfig and switch={}",
                        env_.hhconfig_version_and_switch
                    ),
                );
            }
            // If editor sent 'trace: on' then that will turn on verbose_to_file. But we won't turn off
            // verbose here, since the command-line argument --verbose trumps initialization params.
            match initialize_params.trace {
                initialize::Trace::Off => {}
                initialize::Trace::Messages | initialize::Trace::Verbose => {
                    set_verbose_to_file(ide_service, tracking_id, true)?
                }
            }
            Ok(None)
        }
        // any request/notification if we haven't yet initialized
        (State::PreInit, _) => Err(lsp_exception(
            error::ServerNotInitialized,
            "Server not yet initialized",
        )),
        (State::PostShutdown, _c) => Err(lsp_exception(
            error::InvalidRequest,
            "already received shutdown request",
        )),
        // initialized notification
        (_, NotificationMessage(InitializedNotification)) => Ok(None),
        // rage request
        (_, RequestMessage(id, RageRequestFB)) => {
            let result = do_rage_fb(state);
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::LanguageServer,
                id,
                &LspResult::RageResultFB(result),
            );
            rt(n)
        }
        (_, NotificationMessage(DidChangeWatchedFilesNotification(notification))) => {
            let mut changes = relative_path::set::T::new();
            for change in &notification.changes {
                let path = lsp_uri_to_path(&change.uri)?;
                // This is just the file:///foo/bar uri turned into a string path /foo/bar.
                // There's nothing in VSCode/LSP spec to stipulate that the uris are
                // canonical paths file:///data/users/ljw/www-hg/foo.php or to
                // symlinked paths file:///home/ljw/www/foo.php (where ~/www -> /data/users/ljw/www-hg)
                // but experimentally the uris seem to be canonical paths. That's lucky
                // because if we had to turn a symlink of a deleted file file:///home/ljw/www/foo.php
                // into the actual canonical path /data/users/ljw/www-hg/foo.php then it'd be hard!
                // Anyway, because they refer to canonical paths, we can safely use [Find_utils.file_filter]
                // and [Relative_path.create_detect_prefix], both of which match string prefix on the
                // canonical root.
                if find_utils::file_filter(&path) {
                    changes.insert(relative_path::create_detect_prefix(&path));
                }
            }
            let n = changes.len();
            ide_rpc(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                client_ide_message::request::did_change_watched_files(changes),
            )?;
            rt(n)
        }
        // Text document completion: "AutoComplete!"
        (_, RequestMessage(id, CompletionRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_completion::do_completion(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            let n = result.items.len();
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::CompletionResult(result),
            );
            rt(n)
        }
        // Resolve documentation for a symbol: "Autocomplete Docblock!"
        (_, RequestMessage(id, CompletionItemResolveRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_resolve::do_resolve(ide_service, tracking_id, ref_unblocked_time, params)?;
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::CompletionItemResolveResult(result),
            );
            Ok(None)
        }
        // Document highlighting in serverless IDE
        (_, RequestMessage(id, DocumentHighlightRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_highlight::do_highlight(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::DocumentHighlightResult(result),
            );
            rt(n)
        }
        // Hover docblocks in serverless IDE
        (_, RequestMessage(id, HoverRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_hover::do_hover(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            let result_count = match &result {
                None => 0,
                Some(lsp::hover::HoverResult { contents, .. }) => contents.len(),
            };
            respond_jsonrpc(PoweredBy::ServerlessIde, id, &LspResult::HoverResult(result));
            rt(result_count)
        }
        (_, RequestMessage(id, DocumentSymbolRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_document_symbol::do_document_symbol(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::DocumentSymbolResult(result),
            );
            rt(n)
        }
        (_, RequestMessage(id, WorkspaceSymbolRequest(params))) => {
            cancel_if_stale(client, timestamp, LONG_TIMEOUT)?;
            let result = do_workspace_symbol::do_workspace_symbol(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                params,
            )?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::WorkspaceSymbolResult(result),
            );
            rt(n)
        }
        (_, RequestMessage(id, DefinitionRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let (result, _has_xhp_attribute) = do_definition::do_definition(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::DefinitionResult(result),
            );
            rt(n)
        }
        (_, RequestMessage(id, TypeDefinitionRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_type_definition::do_type_definition(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::TypeDefinitionResult(result),
            );
            rt(n)
        }
        // textDocument/references request
        (_, RequestMessage(id, FindReferencesRequest(params))) => {
            cancel_if_stale(client, timestamp, LONG_TIMEOUT)?;
            let result_telemetry = do_find_references::do_find_references(
                state,
                ide_service,
                metadata,
                ref_unblocked_time,
                &editor_open_files,
                params,
                id,
            )?;
            Ok(Some(result_telemetry))
        }
        // textDocument/implementation request
        (_, RequestMessage(id, ImplementationRequest(params))) => {
            cancel_if_stale(client, timestamp, LONG_TIMEOUT)?;
            let result_telemetry = do_go_to_implementation::do_go_to_implementation(
                state,
                ide_service,
                metadata,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
                id,
            )?;
            Ok(Some(result_telemetry))
        }
        // textDocument/rename request
        (_, RequestMessage(id, RenameRequest(params))) => {
            cancel_if_stale(client, timestamp, LONG_TIMEOUT)?;
            let result_telemetry = do_document_rename::do_document_rename(
                state,
                ide_service,
                metadata,
                ref_unblocked_time,
                &editor_open_files,
                params,
                id,
            )?;
            Ok(Some(result_telemetry))
        }
        // Resolve documentation for a symbol: "Autocomplete Docblock!"
        (_, RequestMessage(id, SignatureHelpRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_signature_help::do_signature_help(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            let result_count = match &result {
                None => 0,
                Some(lsp::signature_help::T { signatures, .. }) => signatures.len(),
            };
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::SignatureHelpResult(result),
            );
            rt(result_count)
        }
        (_, RequestMessage(id, TopLevelDefNameAtPosRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_top_level_def_name_at_pos::do_top_level_def_name_at_pos(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::TopLevelDefNameAtPosResult(result),
            );
            Ok(None)
        }
        // textDocument/codeAction request
        (State::Running(_), RequestMessage(id, CodeActionRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let (result, _file_path, errors_opt) = do_code_action::do_code_action(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::CodeActionResult(result, params.clone()),
            );
            match errors_opt {
                None => {}
                Some(_errors) => {
                    let uri = &params.text_document.uri;
                    if let State::Running(renv) = state {
                        renv.uris_that_need_check.insert(
                            uri.clone(),
                            ErrorsTrigger::MessageTrigger {
                                message: message.clone(),
                                metadata: metadata.clone(),
                            },
                        );
                    }
                }
            }
            rt(n)
        }
        // codeAction/resolve request
        (_, RequestMessage(id, CodeActionResolveRequest(params))) => {
            let lsp::code_action_resolve_request::Params {
                data: code_action_request_params,
                title,
            } = params;
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_code_action::do_code_action_resolve(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                code_action_request_params,
                title,
            )?;
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::CodeActionResolveResult(result),
            );
            let result_extra_data =
                telemetry::string_(None, "title", title, telemetry::create());
            Ok(Some(make_result_telemetry(Some(result_extra_data), None, 1)))
        }
        // textDocument/formatting
        (_, RequestMessage(id, DocumentFormattingRequest(params))) => {
            let result = do_formatting::do_document_formatting(&editor_open_files, params)?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::LanguageServer,
                id,
                &LspResult::DocumentFormattingResult(result),
            );
            rt(n)
        }
        // textDocument/rangeFormatting
        (_, RequestMessage(id, DocumentRangeFormattingRequest(params))) => {
            let result = do_formatting::do_document_range_formatting(&editor_open_files, params)?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::LanguageServer,
                id,
                &LspResult::DocumentRangeFormattingResult(result),
            );
            rt(n)
        }
        // textDocument/onTypeFormatting.
        //  - The Meta Hack extension does not use this, instead uses hackfmt directly (D46758283)
        //  - We keep this implementation for non-VSCode extension clients (notebooks, Vim, etc.)
        (_, RequestMessage(id, DocumentOnTypeFormattingRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_formatting::do_document_on_type_formatting(&editor_open_files, params)?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::LanguageServer,
                id,
                &LspResult::DocumentOnTypeFormattingResult(result),
            );
            rt(n)
        }
        // textDocument/willSaveWaitUntil request
        (_, RequestMessage(id, WillSaveWaitUntilRequest(params))) => {
            let result = do_formatting::do_will_save_wait_until(&editor_open_files, params)?;
            let n = result.len();
            respond_jsonrpc(
                PoweredBy::LanguageServer,
                id,
                &LspResult::WillSaveWaitUntilResult(result),
            );
            rt(n)
        }
        // editor buffer events
        (
            _,
            NotificationMessage(
                DidOpenNotification(_)
                | DidChangeNotification(_)
                | DidCloseNotification(_)
                | DidSaveNotification(_),
            ),
        ) => {
            handle_editor_buffer_message(state, ide_service, metadata, ref_unblocked_time, message)?;
            Ok(None)
        }
        // autoclose request
        (_, RequestMessage(id, AutoCloseRequest(params))) => {
            cancel_if_stale(client, timestamp, SHORT_TIMEOUT)?;
            let result = do_autoclose::do_autoclose(
                ide_service,
                tracking_id,
                ref_unblocked_time,
                &editor_open_files,
                params,
            )?;
            let result_count = result.iter().count();
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::AutoCloseResult(result),
            );
            rt(result_count)
        }
        // unhandled
        (State::Running(_), _) => Err(lsp_exception(
            error::MethodNotFound,
            &format!(
                "not implemented: {}",
                lsp_fmt::denorm_message_to_string(message)
            ),
        )),
    }
}

/// `Not_found`, as `Printexc.to_string` prints it.
struct NotFound;

impl std::fmt::Debug for NotFound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Not_found")
    }
}

/// Process and respond to a notification from clientIdeDaemon, and update [state] accordingly.
fn handle_daemon_notification(
    state: &mut State,
    ide_service: &client_ide_service::T,
    notification: Notification,
    ref_unblocked_time: &mut f64,
) -> Result<Option<ResultTelemetry>, Exn> {
    // In response to ide_service notifications we have these goals:
    // * in case of Done_init failure, we have to announce the failure to the user
    // * in case of Done_init success, we need squiggles for open files
    // * in a few other cases, we send telemetry events so that test harnesses
    //   get insight into the internal state of the ide_service
    // * after every single event, including client_ide_notification events,
    //   our caller queries the ide_service for what status it wants to display to
    //   the user, so these notifications have the goal of triggering that refresh.
    match notification {
        Notification::DoneInit(Ok(())) => {
            lsp_helpers::telemetry_log(&to_stdout, None, "[client-ide] Finished init: ok");
            let editor_open_files = uri_map::elements(&editor_open_files_or_empty(state));
            for (uri, text_document_item::T { text: file_contents, .. }) in editor_open_files {
                send_file_to_ide_and_defer_check(
                    ide_service,
                    state,
                    &uri,
                    file_contents,
                    ErrorsTrigger::InitializeTrigger,
                    ref_unblocked_time,
                )?;
            }
            Ok(None)
        }
        Notification::DoneInit(Err(error_data)) => {
            log_debug("<-- done_init");
            lsp_helpers::telemetry_log(&to_stdout, None, "[client-ide] Finished init: failure");
            announce_ide_failure(&error_data);
            Ok(None)
        }
    }
}

fn handle_deferred_check(
    state: &mut State,
    ide_service: &client_ide_service::T,
    ref_unblocked_time: &mut f64,
    uri: &DocumentUri,
    trigger: ErrorsTrigger,
) -> Result<Option<ResultTelemetry>, Exn> {
    match state {
        State::PreInit | State::PostShutdown => Ok(None),
        State::Running(renv) => {
            renv.uris_that_need_check.remove(uri);
            let editor_open_files = editor_open_files_or_empty(state);
            let file_contents = get_document_contents(&editor_open_files, uri)?;
            let file_path = path::make(&lsp_uri_to_path(uri)?);
            let tracking_id = match &trigger {
                ErrorsTrigger::InitializeTrigger => random_id::short_string(),
                ErrorsTrigger::MessageTrigger { metadata, .. } => metadata.tracking_id.clone(),
            };
            let diagnostics = ide_rpc(
                ide_service,
                &tracking_id,
                ref_unblocked_time,
                client_ide_message::request::diagnostics(client_ide_message::Document {
                    file_path: file_path.clone(),
                    file_contents,
                }),
            )?;
            publish_and_report_after_recomputing_live_squiggles(
                state,
                &file_path,
                diagnostics,
                &trigger,
                ref_unblocked_time,
            )?;
            Ok(None)
        }
    }
}

/// Called once a second but only when there are no pending messages from client
/// or clientIdeDaemon
fn handle_tick(state: &mut State) -> Result<Option<ResultTelemetry>, Exn> {
    // (`Event_logger.recheck_disk_files ()`, `Hack_event_logger.Memory.profile_if_needed ()`,
    // `Event_logger_lwt.flush ()`: no-ops.)
    try_open_errors_file(state);
    Ok(None)
}

fn setup_logging(root: &path::T, verbose: bool) -> String {
    // Log to a file on disk. Note that calls to `Hh_logger` will always write to
    // `stderr`; this is in addition to that.
    let log_filename = server_files::client_lsp_log(root);
    let _ = std::fs::rename(&log_filename, format!("{}.old", log_filename));
    hh_logger::set_log(&log_filename);
    // The --verbose flag in env.verbose is the only thing that controls verbosity
    // to stderr. Meanwhile, verbosity-to-file can be altered dynamically by the user.
    // Why are they different? because we should write to stderr under a test harness,
    // but we should never write to stderr when invoked by VSCode - it's not even guaranteed
    // to drain the stderr pipe.
    if verbose {
        hh_logger::level::set_min_level_stderr(hh_logger::level::T::Debug);
        hh_logger::level::set_min_level_file(hh_logger::level::T::Debug);
    } else {
        hh_logger::level::set_min_level_stderr(hh_logger::level::T::Error);
        hh_logger::level::set_min_level_file(hh_logger::level::T::Info);
    }
    log_filename
}

/// `Client_lsp.main args ~init_id ~config ~local_config ~init_proc_stack`:
/// it only returns by exiting the process.
pub fn main(
    args: Args,
    init_id: &str,
    config: &server_config::T,
    local_config: &server_local_config::T,
    _init_proc_stack: Option<Vec<String>>,
) -> ! {
    LazyLock::force(&BINARY_START_TIME);
    // `Printexc.record_backtrace true`; and the exceptions it catches do not
    // print, as an OCaml exception does not: no panic message on stderr.
    std::panic::set_hook(Box::new(|_info| {}));
    lwt::enter();

    let root = args.root_from_cli.clone();

    let log_filename = setup_logging(&root, args.verbose);
    log(&format!("Starting clientLsp at {}", log_filename));
    log(&format!("cmd: {}", crate::rt::ocaml_sys::argv().join(" ")));
    log(&format!("LSP Init id: {}", init_id));

    server_progress::set_root(root.clone());
    relative_path::set_path_prefix(relative_path::Prefix::Root, std::path::Path::new(&root));

    let _version = read_hhconfig_version(&root);
    let hhconfig_version_and_switch = read_hhconfig_version_and_switch(&root);
    // (`Hack_event_logger.set_hhconfig_version`, `Hack_event_logger.client_lsp_start`:
    // no-ops. `Shared_mem.init Shared_mem.empty_config ~num_workers:1`: the
    // globals it gives, like `workers_should_exit`, are `Worker_cancel`'s
    // here.)

    set_env(Env {
        args: args.clone(),
        hhconfig_version_and_switch,
        root,
        local_config: local_config.clone(),
    });

    let error_filter = filter_diagnostics::filter::make(
        local_config.warnings_default_all,
        server_config::warnings_generated_files(config)
            .iter()
            .map(|s| match crate::rt::ocaml_str::regexp(s) {
                Ok(re) => re,
                Err(crate::rt::ocaml_str::Failure(message)) => panic!("Failure: {}", message),
            })
            .collect(),
        vec![],
    );
    let ide_service = client_ide_service::make(client_ide_message::DaemonArgs {
        init_id: init_id.to_string(),
        verbose_to_stderr: args.verbose,
        verbose_to_file: args.verbose,
        client_lsp_log_fn: log_filename,
        error_filter: error_filter.clone(),
    });
    let ide_notifications = forward_ide_notifications(&ide_service);
    background_status_refresher(&ide_service);

    let client = Arc::new(jsonrpc::make_t());
    let mut state = State::PreInit;
    let mut ref_event: Option<RefEvent> = None;
    // `ref_unblocked_time` is the time at which we're no longer blocked on either
    // clientLsp message-loop or hh_server, and can start actually handling.
    // Everything that blocks will update this variable.
    let mut ref_unblocked_time = ocaml_unix::gettimeofday();
    loop {
        process_next_event(
            &mut state,
            &client,
            &ide_service,
            &ide_notifications,
            &mut ref_event,
            &mut ref_unblocked_time,
            &error_filter,
        );
    }
}

fn process_next_event(
    state: &mut State,
    client: &Arc<jsonrpc::T>,
    ide_service: &client_ide_service::T,
    ide_notifications: &IdeNotifications,
    ref_event: &mut Option<RefEvent>,
    ref_unblocked_time: &mut f64,
    error_filter: &filter_diagnostics::filter::T,
) {
    // The following assertion is satisfied because the only place that stops workers is inside
    // [respect_cancellation], but its ~finally clause guarantees that it unstops workers
    // before it completes i.e. before we continue this [process_next_event] loop.
    assert_workers_are_not_stopped();
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| -> Result<(), Exn> {
        let event = get_next_event(state, client, ide_service, ide_notifications)?;
        if !is_tick(&event) {
            log_debug(&format!("next event: {}", event_to_string(&event)));
        }
        *ref_event = Some(match &event {
            Event::ClientMessage(metadata, message) => {
                RefEvent::ClientMessage(metadata.clone(), message.clone())
            }
            Event::ShellOutComplete(_, triggering_request, _) => {
                RefEvent::ShellOutComplete(triggering_request.clone())
            }
            _ => RefEvent::Other,
        });
        *ref_unblocked_time = ocaml_unix::gettimeofday();

        // we keep track of all open files and their contents
        track_open_and_recent_files(state, &event)?;

        // we keep track of all files that have unsaved changes in them
        track_edits_if_necessary(state, &event);

        // this is the main handler for each message
        let _result_telemetry_opt = match event {
            Event::ClientMessage(metadata, message) => {
                // Note: the function [respect_cancellation] requires the invariant that it not be called
                // concurrently with itself. That's satisfied because here in the ClientLsp main loop
                // is the only place we call it, and the main loop isn't concurrent.
                respect_cancellation(client, &message, || {
                    handle_client_message(
                        state,
                        client,
                        ide_service,
                        &metadata,
                        &message,
                        ref_unblocked_time,
                    )
                })?
            }
            Event::DaemonNotification(notification) => {
                handle_daemon_notification(state, ide_service, notification, ref_unblocked_time)?
            }
            Event::ErrorsFile(result) => handle_errors_file_item(state, result, error_filter)?,
            Event::RefsFile(result) => do_find_references::handle_refs_file_items(state, result),
            Event::ShellOutComplete(result, triggering_request, shellable_type) => {
                // this handler doesn't change state; the state was already changed earlier
                // by [get_next_event], which removed [current_hh_shell] from [state]
                // and stored it within the arguments here to [Shell_out_complete].
                handle_shell_out_complete(result, triggering_request, shellable_type)?
            }
            Event::Tick => handle_tick(state)?,
            Event::DeferredCheck(uri, trigger) => {
                handle_deferred_check(state, ide_service, ref_unblocked_time, &uri, trigger)?
            }
        };
        // for LSP requests and notifications, we keep a log of what+when we responded.
        // INVARIANT: every LSP request gets either a response logged here,
        // or an error logged by one of the handlers below.
        // (`log_response_if_necessary`: only `Hack_event_logger`, a no-op.)
        Ok(())
    }));
    let exn = match result {
        Ok(Ok(())) => return,
        Ok(Err(exn)) => exn,
        Err(payload) => Exn::Other(exception::wrap(payload)),
    };
    let ref_event = ref_event.as_ref();
    match exn {
        Exn::ClientFatalConnectionException(RemoteExceptionData { stack, message }) => {
            let e = make_lsp_error(None, Some(&stack), None, None, &message);
            hack_log_error(ref_event, &e, ErrorSource::ErrorFromClientFatal, *ref_unblocked_time);
            lsp_helpers::telemetry_error(
                &to_stdout,
                None,
                &format!("{}, from_client\n{}", message, stack),
            );
            exit_fail()
        }
        Exn::ClientRecoverableConnectionException(RemoteExceptionData { stack, message }) => {
            let e = make_lsp_error(None, Some(&stack), None, None, &message);
            hack_log_error(
                ref_event,
                &e,
                ErrorSource::ErrorFromClientRecoverable,
                *ref_unblocked_time,
            );
            lsp_helpers::telemetry_error(
                &to_stdout,
                None,
                &format!("{}, from_client\n{}", message, stack),
            );
        }
        exn @ (Exn::DaemonNonfatalException(_) | Exn::LspException(_)) => {
            let (e, is_daemon) = match exn {
                Exn::DaemonNonfatalException(e) => (e, true),
                Exn::LspException(e) => (e, false),
                _ => unreachable!(),
            };
            let error_source = match (e.code, is_daemon) {
                (error::RequestCancelled, _) => ErrorSource::ErrorFromLspCancelled,
                (_, true) => ErrorSource::ErrorFromDaemonRecoverable,
                (_, _) => ErrorSource::ErrorFromLspMisc,
            };
            let e = make_lsp_error(e.data, None, None, Some(e.code), &e.message);
            respond_to_error(ref_event, &e);
            hack_log_error(ref_event, &e, error_source, *ref_unblocked_time);
        }
        Exn::Other(exn) => {
            let e = make_lsp_error(
                None,
                Some(&exception::get_backtrace_string(&exn)),
                Some(false),
                None,
                &exception::get_ctor_string(&exn),
            );
            respond_to_error(ref_event, &e);
            hack_log_error(ref_event, &e, ErrorSource::ErrorFromLspMisc, *ref_unblocked_time);
        }
    }
}

/// `show_diagnostics_from` of the diagnostic that `telemetry/rage` showed in
/// the oracle's recording (a.php: `function f(): int {\n  return "x";\n}`).
#[cfg(test)]
mod show_diagnostics_from_tests {
    use oxidized::explanation::Elem;
    use oxidized::explanation::Explanation;
    use oxidized::file_pos_large::FilePosLarge;
    use oxidized::message::Message;

    use super::*;

    fn pos(l1: usize, b1: usize, o1: usize, l2: usize, b2: usize, o2: usize) -> crate::pos::Absolute {
        crate::pos::make_absolute(
            "/private/tmp/hh-incr/g3/roots/a/a.php".to_string(),
            FilePosLarge::from_lnum_bol_offset(l1, b1, o1),
            FilePosLarge::from_lnum_bol_offset(l2, b2, o2),
        )
    }

    #[test]
    fn as_the_oracle_shows_it() {
        let expr = || pos(4, 26, 35, 4, 26, 38);
        let hint = || pos(3, 6, 20, 3, 6, 23);
        let s = |x: &str| x.to_string();
        let diagnostic_error = crate::user_diagnostic::T {
            severity: crate::user_diagnostic::Severity::Err,
            code: 4110,
            claim: Message(expr(), "Invalid return type".into()),
            reasons: vec![
                Message(hint(), "Expected `int`".into()),
                Message(expr(), "But got `string`".into()),
            ],
            explanation: Explanation::Derivation(vec![
                Elem::Step(s("Step 1 of 1"), true),
                Elem::Rule(s("I started by checking this subtype relationship.")),
                Elem::Prefix { prefix: s("The subtype comes from this"), sep: s(" ") },
                Elem::Witness(expr(), s("expression")),
                Elem::Prefix { prefix: s("and flows into this"), sep: s(" ") },
                Elem::Witness(pos(4, 26, 28, 4, 26, 39), s("expression")),
                Elem::Suffix { suffix: s("because it is used in a return position"), sep: s(" ") },
                Elem::Prefix { prefix: s("The supertype comes from this"), sep: s(" ") },
                Elem::Witness(hint(), s("hint")),
            ]),
            quickfixes: vec![],
            custom_msgs: vec![],
            is_fixmed: false,
            function_pos: Some(pos(3, 6, 6, 5, 40, 41)),
        };
        let d = DiagnosticsFrom::DiagnosticsFromClientIdeDaemon {
            diagnostics: vec![Diagnostic {
                diagnostic_error,
                diagnostic_hash: 749650515366715043,
                diagnostic_related_hints: vec![],
            }],
            validated: false,
        };
        assert_eq!(show_diagnostics_from(&d), EXPECTED);
        assert_eq!(
            show_diagnostics_from(&DiagnosticsFrom::DiagnosticsFromErrorsFile),
            "Diagnostics_from_errors_file"
        );
    }

    const EXPECTED: &str = r#"Diagnostics_from_clientIdeDaemon {
  diagnostics =
  [{ Client_ide_message.diagnostic_error =
     { User_diagnostic.severity = User_diagnostic.Err; code = 4110;
       claim =
       (Pos.Pos_tiny {pos_file = "/private/tmp/hh-incr/g3/roots/a/a.php";
          pos_span = 4:10-13},
        "Invalid return type");
       reasons =
       [(Pos.Pos_tiny {pos_file = "/private/tmp/hh-incr/g3/roots/a/a.php";
           pos_span = 3:15-18},
         "Expected `int`");
         (Pos.Pos_tiny {pos_file = "/private/tmp/hh-incr/g3/roots/a/a.php";
            pos_span = 4:10-13},
          "But got `string`")
         ];
       explanation =
       (Explanation.Derivation
          [(Explanation.Step ("Step 1 of 1", true));
            (Explanation.Rule
               "I started by checking this subtype relationship.");
            Explanation.Prefix {prefix = "The subtype comes from this";
              sep = " "};
            (Explanation.Witness (
               Pos.Pos_tiny {
                 pos_file = "/private/tmp/hh-incr/g3/roots/a/a.php";
                 pos_span = 4:10-13},
               "expression"));
            Explanation.Prefix {prefix = "and flows into this"; sep = " "};
            (Explanation.Witness (
               Pos.Pos_tiny {
                 pos_file = "/private/tmp/hh-incr/g3/roots/a/a.php";
                 pos_span = 4:3-14},
               "expression"));
            Explanation.Suffix {
              suffix = "because it is used in a return position"; sep = " "};
            Explanation.Prefix {prefix = "The supertype comes from this";
              sep = " "};
            (Explanation.Witness (
               Pos.Pos_tiny {
                 pos_file = "/private/tmp/hh-incr/g3/roots/a/a.php";
                 pos_span = 3:15-18},
               "hint"))
            ]);
       quickfixes = []; custom_msgs = []; is_fixmed = false;
       function_pos =
       (Some Pos.Pos_small {
               pos_file = "/private/tmp/hh-incr/g3/roots/a/a.php";
               pos_start = 3:1; pos_end = 5:2})
       };
     diagnostic_hash = 749650515366715043; diagnostic_related_hints = [] }
    ];
  validated = false}"#;
}
