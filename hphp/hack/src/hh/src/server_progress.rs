// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_progress.ml`. See `hh/PORTING.md`.
//!
//! # progress.json
//!
//! Ported in full: `/tmp/hh_server/<root>.progress.json` is written exactly
//! as OCaml writes it (`Yojson.Safe.pretty_to_string` of the
//! `ppx_yojson_conv` encoding, `{ "pid": .., "disposition": [ "DWorking" ],
//! "message": .., "timestamp": .. }`, under an exclusive `lockf` lock), and
//! read as OCaml reads it: a missing file, or one left by a dead process,
//! reads as `DStopped "stopped"`; anything else that fails reads as
//! `DStopped "unknown state"`. Whether the process is alive is
//! `Proc.is_alive` (which this port can also answer on macOS: see
//! `crate::proc`).
//!
//! The JSON is
//! read with `crate::yojson::safe::from_string` and written with
//! `crate::yojson::safe::pretty_to_string` (Yojson 2.0.2's pretty printer).
//! The calls to `Hack_event_logger.server_progress_*_exn` and
//! `invariant_violation_bug` are left out: they do nothing in the OSS build
//! (`stubs/logging/hack_event_logger.ml`), and `crate::hack_event_logger` is
//! compiled with the `port` feature only. `Hh_logger.log` is
//! `crate::hh_logger::log`.
//!
//! # The errors file
//!
//! `ErrorsFile`, `ErrorsWrite` and `ErrorsRead` are ported in full: the
//! server streams the errors of each typecheck to
//! `/tmp/hh_server/<root>.errors.bin`, in the OCaml's format, so that an
//! OCaml client reads a file of this server and this client a file of the
//! OCaml server. Each message is the 5-byte preamble of `Marshal_tools`
//! (`0x8E`, then the size on 4 bytes, most significant first) and the
//! `Marshal.to_bytes message []` of the OCaml `ErrorsFile.message` (written
//! by `crate::rt::ocaml_marshal`; the OCaml representation of each type is
//! in [`codec`]). The lock discipline, the order of unlink / new file / end
//! sentinel, the state machine and the log lines are the OCaml's.
//!
//! Differences that can be seen from outside:
//!
//! - The OCaml shares in a message the objects its program shares (a string
//!   literal or a constant met twice is written once, then referred to):
//!   [`codec`] writes no shared reference, so for the same errors the bytes
//!   can differ where the OCaml's has shared references; both decode to the
//!   same value.
//! - On macOS the OCaml server cannot write the file at all (no
//!   `/proc/<pid>/cmdline` for `Proc.get_cmdline`, no `O_TMPFILE` for
//!   `Sys_utils.atomically_create_and_init_file`: it dies at its first
//!   typecheck unless `produce_streaming_errors=false`). Here `crate::proc`
//!   answers on macOS, and the atomic creation goes through a hidden file of
//!   the directory (see [`atomically_create_and_init_file`]).
//! - `Unix.Unix_error`s and the `failwith`s, which nothing catches in the
//!   OCaml, are panics with the same message.
//! - `Sys_utils.with_lock`'s `lockf` locks keep other processes out; a
//!   mutex also keeps out the other threads of this process.
//! - `Hack_event_logger.invariant_violation_bug` (a no-op in the OSS build)
//!   is left out.

use std::sync::LazyLock;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use crate::diagnostics::FinalizedDiagnostic;
use crate::exception;
use crate::exit_status;
use crate::format;
use crate::format::Formatter;
use crate::hh_logger;
use crate::path;
use crate::diagnostics;
use crate::proc;
use crate::relative_path;
use crate::rt::ocaml_marshal;
use crate::rt::ocaml_marshal::ocaml_map;
use crate::rt::ocaml_printf;
use crate::rt::ocaml_unix::UnixError;
use crate::rt::ocaml_unix;
use crate::rt::ocaml_unix::LockCommand;
use crate::server_files;
use crate::server_notifier_types;
use crate::sys_utils::ProtectedIoError;
use crate::telemetry;
use crate::user_diagnostic;
use crate::yojson::safe as yojson;

/// Disposition of hh_server
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Disposition {
    /// Hh_server has failed in some way, so will be unable to handle future work until it's been fixed.
    DStopped,
    /// Hh_server is working on something, e.g. doing a typecheck or handling a request in ServerRpc
    DWorking,
    /// Hh_server is ready to handle requests, i.e. not doing any work.
    DReady,
}

/// `pp_disposition` (`[@@deriving show { with_path = false }]`)
pub fn pp_disposition(fmt: &mut Formatter, disposition: &Disposition) {
    format::pp_print_string(fmt, &show_disposition(disposition))
}

/// `show_disposition`: `DStopped`, `DWorking`, `DReady`.
pub fn show_disposition(disposition: &Disposition) -> String {
    match disposition {
        Disposition::DStopped => "DStopped",
        Disposition::DWorking => "DWorking",
        Disposition::DReady => "DReady",
    }
    .to_string()
}

/// `yojson_of_disposition` (`ppx_yojson_conv`): `["DStopped"]`...
fn yojson_of_disposition(disposition: &Disposition) -> yojson::T {
    yojson::T::List(vec![yojson::T::String(show_disposition(disposition))])
}

/// An `Of_yojson_error` of `ppx_yojson_conv`, with its message. (`read`
/// catches it and logs it as `Printexc` shows it, without the message.)
#[derive(Clone, Debug, PartialEq, Eq)]
struct OfYojsonError(#[allow(dead_code)] String);

fn of_yojson_error<A>(msg: &str, json: &yojson::T) -> Result<A, OfYojsonError> {
    Err(OfYojsonError(format!("{}: {}", msg, yojson::to_string(json))))
}

/// `disposition_of_yojson`: exactly `["DStopped"]`, `["DWorking"]` or
/// `["DReady"]` (a bare string is an error, as for any constant constructor
/// of `ppx_yojson_conv`).
fn disposition_of_yojson(json: &yojson::T) -> Result<Disposition, OfYojsonError> {
    let tp_loc = "server_progress.ml.disposition";
    match json {
        yojson::T::List(l) => match l.as_slice() {
            [yojson::T::String(s)] if s == "DStopped" => Ok(Disposition::DStopped),
            [yojson::T::String(s)] if s == "DWorking" => Ok(Disposition::DWorking),
            [yojson::T::String(s)] if s == "DReady" => Ok(Disposition::DReady),
            _ => of_yojson_error(&format!("{}: unexpected variant constructor", tp_loc), json),
        },
        _ => of_yojson_error(&format!("{}: unexpected variant constructor", tp_loc), json),
    }
}

/// Progress is a file in /tmp/hh_server/<repo>.progress.json which is written
/// by monitor+server. It lives from the moment the monitor starts up until the
/// moment it finally dies or is killed. You should only read it by the [read]
/// call, since that protects against races. It also protects against server death,
/// because if you try to [read] a progress.json that had been created by a now-dead
/// server PID then it detects that fact and returns an "unknown" status.
///
/// The state fields [disposition] and [message] are intended to be shown to the
/// user, not acted upon in code -- they're slightly handwavey in places (e.g. there's
/// an interval from when a server dies until the monitor realizes that fact when
/// [read] will return "unknown").
#[derive(Clone, Debug, PartialEq)]
pub struct T {
    /// pid of the process that wrote this status
    pub pid: isize,
    pub disposition: Disposition,
    /// e.g. "typechecking 5/15 files"
    pub message: String,
    pub timestamp: f64,
}

/// `yojson_of_t` (`ppx_yojson_conv`): the fields in order.
fn yojson_of_t(t: &T) -> yojson::T {
    yojson::T::Assoc(vec![
        ("pid".to_string(), yojson::T::Int(t.pid)),
        ("disposition".to_string(), yojson_of_disposition(&t.disposition)),
        ("message".to_string(), yojson::T::String(t.message.clone())),
        ("timestamp".to_string(), yojson::T::Float(t.timestamp)),
    ])
}

/// `t_of_yojson` (`ppx_yojson_conv`): an object with each field once, in any
/// order, and no other field (`record_check_extra_fields` is on by default).
/// Each value is converted as it is met: `pid` an `Int`, `message` a
/// `String`, `timestamp` a `Float`, an `Int` or an `Intlit`.
fn t_of_yojson(json: &yojson::T) -> Result<T, OfYojsonError> {
    let tp_loc = "server_progress.ml.t";
    let field_yojsons = match json {
        yojson::T::Assoc(fields) => fields,
        _ => return of_yojson_error(&format!("{}: record list instead of atom", tp_loc), json),
    };
    let mut pid_field = None;
    let mut disposition_field = None;
    let mut message_field = None;
    let mut timestamp_field = None;
    let mut duplicates: Vec<&str> = vec![];
    let mut extra: Vec<&str> = vec![];
    for (field_name, field_yojson) in field_yojsons {
        match field_name.as_str() {
            "pid" => match pid_field {
                None => {
                    // int_of_yojson
                    let fvalue = match field_yojson {
                        yojson::T::Int(v) => *v,
                        _ => return of_yojson_error("int_of_yojson: integer needed", field_yojson),
                    };
                    pid_field = Some(fvalue)
                }
                Some(_) => duplicates.push(field_name),
            },
            "disposition" => match disposition_field {
                None => disposition_field = Some(disposition_of_yojson(field_yojson)?),
                Some(_) => duplicates.push(field_name),
            },
            "message" => match message_field {
                None => {
                    // string_of_yojson
                    let fvalue = match field_yojson {
                        yojson::T::String(v) => v.clone(),
                        _ => return of_yojson_error("string_of_yojson: string needed", field_yojson),
                    };
                    message_field = Some(fvalue)
                }
                Some(_) => duplicates.push(field_name),
            },
            "timestamp" => match timestamp_field {
                None => {
                    // float_of_yojson
                    let fvalue = match field_yojson {
                        yojson::T::Float(v) => *v,
                        yojson::T::Int(i) => *i as f64,
                        yojson::T::Intlit(s) => match s.parse::<f64>() {
                            Ok(v) => v,
                            Err(_) => return of_yojson_error("float_of_string", field_yojson),
                        },
                        _ => return of_yojson_error("float_of_yojson: float needed", field_yojson),
                    };
                    timestamp_field = Some(fvalue)
                }
                Some(_) => duplicates.push(field_name),
            },
            _ => extra.push(field_name),
        }
    }
    if !duplicates.is_empty() {
        return of_yojson_error(
            &format!("{}: duplicate fields: {}", tp_loc, duplicates.join(" ")),
            json,
        );
    }
    if !extra.is_empty() {
        return of_yojson_error(
            &format!("{}: extra fields: {}", tp_loc, extra.join(" ")),
            json,
        );
    }
    match (pid_field, disposition_field, message_field, timestamp_field) {
        (Some(pid), Some(disposition), Some(message), Some(timestamp)) => Ok(T {
            pid,
            disposition,
            message,
            timestamp,
        }),
        _ => of_yojson_error(
            &format!("{}: the following record elements were undefined", tp_loc),
            json,
        ),
    }
}

/// `stack : string ref list ref`, whose head is the last element here. (A
/// panic while it is held leaves it as it is, like OCaml's ref.)
fn stack() -> MutexGuard<'static, Vec<String>> {
    // `ref [ref ""]`
    static STACK: LazyLock<Mutex<Vec<String>>> = LazyLock::new(|| Mutex::new(vec![String::new()]));
    STACK.lock().unwrap_or_else(|e| e.into_inner())
}

fn write_stack(message: &str) {
    // List.hd_exn !stack := message
    match stack().last_mut() {
        Some(top) => *top = message.to_string(),
        None => panic!("hd_exn"),
    }
}

fn push_stack() {
    stack().push(String::new())
}

fn pop_stack_and_peek() -> String {
    let mut stack = stack();
    if stack.pop().is_none() {
        panic!("tl_exn")
    }
    match stack.last() {
        Some(top) => top.clone(),
        None => panic!("hd_exn"),
    }
}

/// The caller must set this before attempting to send progress, otherwise exception
fn root() -> MutexGuard<'static, Option<path::T>> {
    static ROOT: Mutex<Option<path::T>> = Mutex::new(None);
    ROOT.lock().unwrap_or_else(|e| e.into_inner())
}

/// Sets the root path of the repository.
/// All functions in this file will throw unless you've already called set_root
/// at the start of your process.
pub fn set_root(r: path::T) {
    *root() = Some(r)
}

/// use this in tests, instead of set_root,
/// to disable progress-logging and error-streaming.
pub fn disable() {
    *root() = Some(path::dummy_path())
}

fn server_progress_file() -> Option<String> {
    let root = root().clone();
    match root {
        None => panic!("Server_progress.set_root must be called first"),
        Some(root) if path::equal(&root, &path::dummy_path()) => None,
        Some(root) => Some(server_files::server_progress_file(&root)),
    }
}

/// Call this upon monitor shutdown to delete the progress file
pub fn try_delete() {
    match server_progress_file() {
        None => {}
        Some(server_progress_file) => {
            let _ = std::fs::remove_file(server_progress_file);
        }
    }
}

/// This writes to the specified progress file. It first acquires
/// an exclusive (writer) lock. (Locks on unix are advisory; we trust
/// [read] below to also acquire a lock). It overwrites
/// whatever was there before. In case of failure, it logs but is
/// silent. That's on the principle that defects in
/// progress-reporting should never break hh_server.
fn write_file(t: &T) {
    crate::exit::with_world(|| write_file_unstopped(t))
}

fn write_file_unstopped(t: &T) {
    match server_progress_file() {
        None => {}
        Some(server_progress_file) => {
            let content = crate::yojson::safe::pretty_to_string(&yojson_of_t(t));
            if let Err(exn) = crate::sys_utils::protected_write_exn(&server_progress_file, &content) {
                let e = exception::wrap(exn);
                hh_logger::log(&format!(
                    "SERVER_PROGRESS_EXCEPTION(write) {}\n{}",
                    exception::get_ctor_string(&e),
                    exception::clean_stack(&exception::get_backtrace_string(&e))
                ));
                // Hack_event_logger.server_progress_write_exn ~server_progress_file e
                // (a no-op in the OSS build).
            }
        }
    }
}

/// Reads the current progress.json file. If there is none, or if there is one
/// but it came from a dead PID, or if it was corrupt, this function synthesizes
/// a [DStopped] response with a appropriate human-readable message that reflects
/// on the precise reason, but simply says "stopped" in the typical case of absent
/// file or dead PID.
///
/// It first acquires a non-exclusive (reader) lock. (Locks on unix are
/// advisory; we trust [write_file] above to also acquire a writer
/// lock). If there are failures, we log, and return a human-readable
/// string that indicates why.
pub fn read() -> T {
    let synthesize_stopped = |message: &str| T {
        pid: 0,
        disposition: Disposition::DStopped,
        message: message.to_string(),
        timestamp: ocaml_unix::gettimeofday(),
    };
    /// What the `try` of `read` catches. Its `Debug` is what
    /// `Exception.get_ctor_string` shows of the OCaml exception.
    enum ReadExn {
        Io(ProtectedIoError),
        /// `Yojson.Json_error msg`
        JsonError(String),
        /// `Ppx_yojson_conv_lib.Yojson_conv.Of_yojson_error (exn, json)`
        OfYojsonError,
    }
    impl std::fmt::Debug for ReadExn {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                ReadExn::Io(e) => e.fmt(f),
                ReadExn::JsonError(msg) => {
                    write!(f, "Yojson.Json_error({})", ocaml_printf::sprintf_s(msg))
                }
                // `Printexc` shows the arguments that are not strings or
                // integers as `_`; the exception is defined in the wrapped
                // library `ppx_yojson_conv_lib`.
                ReadExn::OfYojsonError => {
                    f.write_str("Ppx_yojson_conv_lib__Yojson_conv.Of_yojson_error(_, _)")
                }
            }
        }
    }
    match server_progress_file() {
        None => panic!("Server_progress.disable: can't read it"),
        Some(server_progress_file) => {
            let mut content = "[not yet read content]".to_string();
            let result = (|| -> Result<T, ReadExn> {
                content = crate::sys_utils::protected_read_exn(&server_progress_file).map_err(ReadExn::Io)?;
                let json = yojson::from_string(&content)
                    .map_err(|crate::yojson::JsonError(msg)| ReadExn::JsonError(msg))?;
                let t = t_of_yojson(&json).map_err(|OfYojsonError(_)| ReadExn::OfYojsonError)?;
                // If the status had been left behind on disk by a process that terminated without deleting it,
                // well, we'll return the same 'unknown' as if the file didn't exist.
                if proc::is_alive(t.pid, "") {
                    Ok(t)
                } else {
                    Ok(synthesize_stopped("stopped"))
                }
            })();
            match result {
                Ok(t) => t,
                Err(ReadExn::Io(ProtectedIoError::UnixError(err, _, _)))
                    if err.raw_os_error() == Some(libc::ENOENT) =>
                {
                    synthesize_stopped("stopped")
                }
                Err(exn) => {
                    let e = exception::wrap(exn);
                    hh_logger::log(&format!(
                        "SERVER_PROGRESS_EXCEPTION(read) {}\n{}\n{}",
                        exception::get_ctor_string(&e),
                        exception::clean_stack(&exception::get_backtrace_string(&e)),
                        content
                    ));
                    // Hack_event_logger.server_progress_read_exn ~server_progress_file e
                    // (a no-op in the OSS build).
                    synthesize_stopped("unknown state")
                }
            }
        }
    }
}

/// `include_in_logs` defaults to `true`, `disposition` to `DWorking`.
/// Not in the OCaml: a record of every message written (whether or not a
/// progress file is written), for the tests that compare the sequence
/// with the OCaml's. Off unless [`trace_for_test::start`] was called.
pub mod trace_for_test {
    use std::sync::Mutex;
    use std::sync::atomic::AtomicBool;
    use std::sync::atomic::Ordering;

    use super::Disposition;

    static ON: AtomicBool = AtomicBool::new(false);
    static TRACE: Mutex<Vec<(Disposition, String)>> = Mutex::new(Vec::new());

    pub fn start() {
        TRACE.lock().unwrap_or_else(|e| e.into_inner()).clear();
        ON.store(true, Ordering::SeqCst);
    }

    /// The messages written since [`start`] or the last `take`.
    pub fn take() -> Vec<(Disposition, String)> {
        std::mem::take(&mut *TRACE.lock().unwrap_or_else(|e| e.into_inner()))
    }

    pub(super) fn record(disposition: &Disposition, message: &str) {
        if ON.load(Ordering::Relaxed) {
            TRACE
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .push((disposition.clone(), message.to_string()));
        }
    }
}

fn write_message(include_in_logs: Option<bool>, disposition: Option<Disposition>, message: &str) {
    let include_in_logs = include_in_logs.unwrap_or(true);
    let disposition = disposition.unwrap_or(Disposition::DWorking);
    trace_for_test::record(&disposition, message);
    if include_in_logs {
        hh_logger::log(&format!("[progress] {}", message));
    }
    let timestamp = ocaml_unix::gettimeofday();
    write_file(&T {
        pid: ocaml_unix::getpid(),
        disposition,
        message: message.to_string(),
        timestamp,
    });
}

/// [write ~include_in_logs ~disposition fmt_string] writes
/// [disposition] and the formatted string [fmt_string] to progress.json.
/// (The caller formats: `message` is the formatted string.)
///
/// Default disposition is [DWorking]. If you want to indicate that the server is stopped
/// or ready, you must provide a disposition explicitly. `include_in_logs`
/// defaults to `true`.
pub fn write(include_in_logs: Option<bool>, disposition: Option<Disposition>, message: &str) {
    let include_in_logs = include_in_logs.unwrap_or(true);
    let disposition = disposition.unwrap_or(Disposition::DWorking);
    write_stack(message);
    write_message(Some(include_in_logs), Some(disposition), message)
}

/// [with_message msg f] writes message [msg], calls [f], then writes
/// back the message displayed before calling [with_message].
/// [f] can call [write], [with_message] or [with_frame]: we'd still
/// show the message displayed before this call to [with_message]
/// when [f] finishes.
pub fn with_message<A>(
    include_in_logs: Option<bool>,
    disposition: Option<Disposition>,
    message: &str,
    f: impl FnOnce() -> A,
) -> A {
    let include_in_logs = include_in_logs.unwrap_or(true);
    let disposition = disposition.unwrap_or(Disposition::DWorking);
    push_stack();
    write_stack(message);
    write_message(Some(include_in_logs), Some(disposition), message);
    let res = f();
    let previous_message = pop_stack_and_peek();
    write_message(Some(false), Some(disposition), &previous_message);
    res
}

/// [with_frame f] calls [f] (which can display messages using
/// [write], [with_message] or [with_frame]) then writes
/// back the message displayed before calling [with_frame].
pub fn with_frame<A>(disposition: Option<Disposition>, f: impl FnOnce() -> A) -> A {
    let disposition = disposition.unwrap_or(Disposition::DWorking);
    push_stack();
    let res = f();
    let previous_message = pop_stack_and_peek();
    write_message(Some(false), Some(disposition), &previous_message);
    res
}

/// The message will look roughly like this:
/// <operation> <done_count>/<total_count> <unit> <percent done> <extra>
fn make_percentage_progress_message(
    operation: &str,
    done_count: isize,
    total_count: isize,
    unit: &str,
    extra: Option<&str>,
) -> String {
    let unit = if unit.is_empty() {
        unit.to_string()
    } else {
        format!("{} ", unit)
    };
    // so that 999999/1000000 will show as 99.9%, not 100.0%
    let percent = (1000.0 * done_count as f64 / total_count as f64).floor() / 10.0;
    let main_message = format!(
        "{} {}/{} {}({}%)",
        operation,
        done_count,
        total_count,
        unit,
        ocaml_printf::sprintf_f(1, percent)
    );
    match extra {
        Some(extra) => format!("{} {}", main_message, extra),
        None => main_message,
    }
}

/// Shorthand for [write ~include_in_logs:false ~disposition:DWorking "%s" message]
/// for the message "<operation> <done_count>/<total_count> <unit> <percent done> <extra>".
pub fn write_percentage(
    operation: &str,
    done_count: isize,
    total_count: isize,
    unit: &str,
    extra: Option<&str>,
) {
    write(
        Some(false),
        None,
        &make_percentage_progress_message(operation, done_count, total_count, unit, extra),
    )
}

// ~~ The errors file ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Reason for marking the errors file as complete (using the "complete" sentinel)
#[derive(Clone, Debug, PartialEq)]
pub enum CompletionReason {
    /// The typecheck has finished, i.e. server called [ErrorsWrite.complete].
    Complete(telemetry::T),
    /// The typecheck didn't complete; a new typecheck in a new errors-file has started.
    /// i.e. server called [ErrorsWrite.new_empty_file] before [ErrorsWrite.complete].
    /// [user_message] is a human-facing reason for why it was restarted, and [log_message]
    /// contains extra logging information.
    Restarted {
        user_message: String,
        log_message: String,
    },
    /// Hh_server was stopped gracefully so we can't read errors. i.e. server called [ErrorsWrite.unlink].
    Stopped,
}

/// `pp_completion_reason` (`[@@deriving show { with_path = false }]`, with
/// printers that show the constructor alone): `Complete`, `Restarted`,
/// `Stopped`.
pub fn pp_completion_reason(fmt: &mut Formatter, reason: &CompletionReason) {
    format::pp_print_string(fmt, &show_completion_reason(reason))
}

pub fn show_completion_reason(reason: &CompletionReason) -> String {
    match reason {
        CompletionReason::Complete(_) => "Complete",
        CompletionReason::Restarted { .. } => "Restarted",
        CompletionReason::Stopped => "Stopped",
    }
    .to_string()
}

pub fn completion_reason_short_description(reason: &CompletionReason) -> String {
    match reason {
        CompletionReason::Complete(_) => "typecheck completed",
        CompletionReason::Restarted { .. } => "typecheck restarted due to file changes",
        CompletionReason::Stopped => "hh_server gracefully stopped",
    }
    .to_string()
}

/// Each item that a consumer reads from the errors-file is one of these.
#[derive(Clone, Debug, PartialEq)]
pub enum ErrorsFileItem {
    Errors {
        /// we convert to finalized_error (i.e. turn paths absolute) before writing in the file,
        /// because consumers don't know hhi paths. As for the [Relative_path.Map.t], it
        /// is guaranteed to only have root-relative paths. (we don't have a type to indicate
        /// "I am the suffix of a root-relative path" so this is the best we can do.)
        /// Each diagnostic comes with its `User_diagnostic.hash_diagnostic_for_saved_state`.
        errors: relative_path::map::T<Vec<(FinalizedDiagnostic, isize)>>,
        /// the errors were detected by reading the files not later than this time.
        timestamp: f64,
    },
    Telemetry(telemetry::T),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorsFileReadError {
    Malformed,
}

/// `pp_errors_file_read_error` (`[@@deriving show]`): `Server_progress.Malformed`.
pub fn pp_errors_file_read_error(fmt: &mut Formatter, e: &ErrorsFileReadError) {
    format::pp_print_string(fmt, &show_errors_file_read_error(e))
}

pub fn show_errors_file_read_error(e: &ErrorsFileReadError) -> String {
    match e {
        ErrorsFileReadError::Malformed => "Server_progress.Malformed".to_string(),
    }
}

fn is_production_enabled() -> &'static AtomicBool {
    static IS_PRODUCTION_ENABLED: AtomicBool = AtomicBool::new(true);
    &IS_PRODUCTION_ENABLED
}

pub fn enable_error_production(b: bool) {
    is_production_enabled().store(b, Ordering::SeqCst)
}

/// The errors file of the root, `None` when error production is disabled or
/// progress is [`disable`]d.
pub(crate) fn errors_file_path() -> Option<String> {
    let root = root().clone();
    match root {
        None => panic!("Server_progress.set_root must be called first"),
        Some(_) if !is_production_enabled().load(Ordering::SeqCst) => None,
        Some(root) if path::equal(&root, &path::dummy_path()) => None,
        Some(root) => Some(server_files::errors_file_path(&root)),
    }
}

// ~~ Sys_utils and Marshal_tools ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// The functions of `Sys_utils` and `Marshal_tools` that the errors file uses
// and that `crate::sys_utils` does not have (yet). Their exceptions
// (`Unix.Unix_error`) are the `std::io::Error` of the failing call, which
// the callers turn into a panic with what `Printexc` shows of the OCaml
// exception, as nothing in OCaml catches them.

fn raise(e: UnixError) -> ! {
    panic!("{}", e)
}

/// This is an internal module concerned with the binary format of the errors-file.
pub(crate) mod errors_file {
    use super::*;

    /// The errors-file is a binary format consisting of a sequence of messages
    /// written by the hh_server process.
    ///
    /// The first two messages are [VersionHeader] followed by [Header], and these
    /// always exist (they are placed atomically at error-file creation by
    /// [ErrorsWrite.new_empty_file]). Then there are zero or more [Item], each
    /// one appended by a call to [ErrorsWrite.report]. Finally, there may be an [End],
    /// appended by a call to [ErrorsWrite.complete] or [unlink_after_stopped] or [new_empty_file].
    ///
    /// Each message consists of a 5-byte preamble (one sync byte, 4 size bites)
    /// followed by a marshalled [message] structure.
    #[derive(Clone, Debug, PartialEq)]
    pub enum Message {
        VersionHeader {
            /// from Build_id.build_revision, or empty if dev build or --ignore-hh-version
            version: String,
            /// CARE! The hh_client binary might read the [VersionHeader] message that was written by either
            /// an older or a newer version of the hh_server binary. Therefore, it is impossible to
            /// change the datatype! Any new fields will have to be added to 'extra' if they're needed
            /// cross-version, or more commonly just placed in [Header] since it is version-safe.
            extra: yojson::T,
        },
        Header {
            /// the pid of the hh_server that wrote this file; clients check "sigkill 0 <pid>" to see if it's still alive
            pid: isize,
            /// the /proc/pid/cmdline of hh_server; clients check that the current /proc/pid/cmdline is the same (proving that the pid hasn't been recycled)
            cmdline: String,
            /// the time at which the typecheck began
            timestamp: f64,
            /// the file watcher clock at which the typecheck began, i.e. reflecting all file-changes up to here
            clock: Option<server_notifier_types::Clock>,
        },
        Item(ErrorsFileItem),
        End {
            reason: CompletionReason,
            timestamp: f64,
            log_message: String,
        },
    }

    /// 4 GB
    pub fn max_payload_size() -> isize {
        4_000_000_000
    }

    /// `` `Read `` / `` `Write ``
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Direction {
        Read,
        Write,
    }

    pub fn assert_payload_size_ok(size: isize, direction: Direction, message: Option<&Message>) {
        if size >= max_payload_size() {
            let msg = format!(
                "{} error payload with size {}, which is too big.{}",
                match direction {
                    Direction::Read => "Reading",
                    Direction::Write => "Writing",
                },
                size,
                match message {
                    None => "".to_string(),
                    Some(message) => format!(
                        " Message is {}.",
                        match message {
                            Message::VersionHeader { .. } => "the version header".to_string(),
                            Message::Header { .. } => "the header".to_string(),
                            Message::Item(ErrorsFileItem::Errors {
                                errors,
                                timestamp: _,
                            }) => {
                                let error_count = errors
                                    .iter()
                                    .fold(0, |cnt, (_path, errors)| cnt + errors.len());
                                format!("some {} errors", error_count)
                            }
                            Message::Item(ErrorsFileItem::Telemetry(telemetry)) => {
                                let nchar = telemetry::to_string(None, telemetry).len();
                                format!("some telemetry of {} characters", nchar)
                            }
                            Message::End { .. } => "the end sentinel".to_string(),
                        }
                    ),
                }
            );
            // Hack_event_logger.invariant_violation_bug msg (a no-op in the
            // OSS build).
            panic!("{}", msg)
        }
    }

    /// `Marshal.to_bytes message []`
    pub fn marshal(message: &Message) -> Vec<u8> {
        match ocaml_marshal::to_bytes(&codec::message(message), &[]) {
            Ok(payload) => payload,
            Err(e) => panic!("{}", e),
        }
    }

    /// `(Marshal.from_bytes payload 0 : message)`. A payload that does not
    /// decode, or is not a `message`, is a panic: OCaml raises `Failure` (or
    /// worse) and nothing catches it.
    pub fn unmarshal(payload: &[u8]) -> Message {
        let v = match ocaml_marshal::from_bytes(payload, 0) {
            Ok(v) => v,
            Err(e) => panic!("{}", e),
        };
        match codec::message_of_ocaml(&v) {
            Ok(m) => m,
            Err(e) => panic!("errors-file message: {}", e),
        }
    }

    /// This helper acquires an exclusive lock on the file, appends the message, then releases the lock.
    /// It does not do any state validation - that's left to its caller.
    pub fn write_message(fd: &std::fs::File, message: &Message) -> Result<(), UnixError> {
        let payload = marshal(message);
        let size = payload.len();
        // Since we do this assertion when reading (to avoid creating buffers that are too big),
        // we also do the same assertion when writing, just in case we ever write very big
        // messages by mistake.
        assert_payload_size_ok(size as isize, Direction::Write, Some(message));
        let preamble = crate::marshal_tools::make_preamble(size);
        crate::sys_utils::with_lock(fd, LockCommand::FLock, || {
            crate::sys_utils::write_non_intr(fd, &preamble)?;
            crate::sys_utils::write_non_intr(fd, &payload)
        })
    }

    pub fn read_message(fd: &std::fs::File) -> Result<Result<Option<Message>, ErrorsFileReadError>, UnixError> {
        crate::sys_utils::with_lock(fd, LockCommand::FRlock, || {
            let preamble = crate::sys_utils::read_non_intr(fd, crate::marshal_tools::EXPECTED_PREAMBLE_SIZE)?;
            match preamble {
                None => Ok(Ok(None)),
                Some(preamble) => {
                    let size = crate::marshal_tools::parse_preamble(&preamble);
                    // This assert is in case the file is garbled, and we read a crazy-big size,
                    // to avoid allocating say a 10gb bytes array and having the machine get stuck.
                    assert_payload_size_ok(size as isize, Direction::Read, None);
                    match crate::sys_utils::read_non_intr(fd, size)? {
                        None => Ok(Err(ErrorsFileReadError::Malformed)),
                        Some(payload) => Ok(Ok(Some(unmarshal(&payload)))),
                    }
                }
            }
        })
    }
}

pub mod errors_write {
    use super::*;

    /// This structure represent's hh_server's current knowledge about the errors-file.
    /// Only hh_server should be manipulating the errors-file; hence, this knowledge is authoritative.
    #[derive(Debug)]
    pub enum WriteState {
        /// The errors-file either doesn't exist because this hh_server instance hasn't
        /// yet called [new_empty_file], or because it called [unlink_at_server_stop].
        Absent,
        /// The errors-file does exist,
        /// due to a previous call to [new_empty_file], and it's fine to call [report] or [complete].
        Reporting(std::fs::File, isize),
        /// The errors-file has an end-marker due to a call to [complete].
        Closed,
    }

    /// `show_write_state` (`[@@deriving show { with_path = false }]`, with a
    /// printer for `Reporting`).
    pub fn show_write_state(write_state: &WriteState) -> String {
        match write_state {
            WriteState::Absent => "Absent".to_string(),
            WriteState::Reporting(_fd, n) => format!("Reporting[{}]", n),
            WriteState::Closed => "Closed".to_string(),
        }
    }

    /// This mutable value tracks the current state of the errors-file belonging to this
    /// instance of hh_server.
    /// The errors-file is deemed absent when hh_server starts up. Even if there had been a leftover
    /// errors-file from a previous hh_server instance, any attempt to read it will fail because it
    /// necessarily must have come from a now-dead PID.
    fn write_state() -> MutexGuard<'static, WriteState> {
        static WRITE_STATE: Mutex<WriteState> = Mutex::new(WriteState::Absent);
        WRITE_STATE.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn ok<A>(r: Result<A, UnixError>) -> A {
        match r {
            Ok(a) => a,
            Err(e) => raise(e),
        }
    }

    /// This helper is called by [new_empty_file] and [unlink_at_server_stop]...
    ///    1. It unlinks the current file, if any (in states [Reporting], [Closed])
    ///    2. It calls the [after_unlink] callback
    ///    3. It writes a End message if needed (in state [Reporting])
    ///    4. It closes the file-descriptor for the current file (in state [Reporting]).
    ///
    /// For example: in the case of caller [new_empty_file], its [after_unlink] callback creates a new errors file.
    /// In this way, if a client with an existing file-descriptor should read a sentinel, then it knows
    /// for sure it can immediately close that file-descriptor and re-open the new errors file.
    ///
    /// (The state is passed in: the caller holds it.)
    fn unlink_sentinel_close<A>(
        state: &mut WriteState,
        reason: CompletionReason,
        log_message: &str,
        errors_file_path: &str,
        after_unlink: impl FnOnce() -> A,
    ) -> A {
        let _ = std::fs::remove_file(errors_file_path);
        let result = after_unlink();
        if let WriteState::Reporting(fd, count) = &*state {
            hh_logger::log(&format!(
                "Errors-file: ending old {} with its {} reports, with sentinel {}",
                crate::sys_utils::show_inode(fd),
                count,
                show_completion_reason(&reason)
            ));
            ok(errors_file::write_message(
                fd,
                &errors_file::Message::End {
                    reason,
                    timestamp: ocaml_unix::gettimeofday(),
                    log_message: log_message.to_string(),
                },
            ));
            // Unix.close fd: the state's descriptor is closed when the caller
            // replaces the state.
        }
        result
    }

    /// To be called at start of typechecking.
    /// This creates a new errors file. If there had been a previous errors file, then the previous
    /// one gets unlinked; and if the previous error file was not yet complete then anyone
    /// reading from the previous errors file will now get a [Error (Restarted cancel_reason)].
    pub fn new_empty_file(
        clock: Option<server_notifier_types::Clock>,
        ignore_hh_version: bool,
        cancel_reason: (String, String),
    ) {
        crate::exit::with_world(|| new_empty_file_unstopped(clock, ignore_hh_version, cancel_reason))
    }

    fn new_empty_file_unstopped(
        clock: Option<server_notifier_types::Clock>,
        ignore_hh_version: bool,
        cancel_reason: (String, String),
    ) {
        match errors_file_path() {
            None => {}
            Some(errors_file_path) => {
                // (1) unlink the old errors file, (2) atomically create a new errors-file with
                // Version_header+Header messages in it, (3) write a End marker into the old errors file.
                //
                // **Atomicity** is so that a client can be assured that if they open an errors-file
                // then it will necessarily have two errors in it.
                // **Sentinel-after-new** is so that a client can be assured that if they encounter
                // a sentinel then there's already a new errors-file ready to be read immediately
                // or, if not, then the server must have died.
                //
                // Both mechanisms are there to make the client-side code easier to write!
                let pid = ocaml_unix::getpid();
                let version = if ignore_hh_version {
                    String::new()
                } else {
                    crate::build_id::build_revision()
                };
                let version_header = errors_file::Message::VersionHeader {
                    version,
                    extra: yojson::T::Assoc(vec![]),
                };
                let cmdline = match proc::get_cmdline(pid) {
                    Ok(cmdline) => cmdline,
                    Err(msg) => panic!("{}", msg),
                };
                let header = errors_file::Message::Header {
                    pid,
                    cmdline,
                    timestamp: ocaml_unix::gettimeofday(),
                    clock: clock.clone(),
                };
                let (user_message, log_message) = cancel_reason;
                let mut state = write_state();
                let fd = unlink_sentinel_close(
                    &mut state,
                    CompletionReason::Restarted {
                        user_message,
                        log_message,
                    },
                    "new_empty_file",
                    &errors_file_path,
                    || {
                        let fd = ok(crate::sys_utils::atomically_create_and_init_file(
                            &errors_file_path,
                            false,
                            true,
                            0o666,
                            |fd| {
                                errors_file::write_message(fd, &version_header)?;
                                errors_file::write_message(fd, &header)
                            },
                        ));
                        match fd {
                            None => {
                                panic!("Errors-file was created by someone else under our feet")
                            }
                            Some(fd) => {
                                hh_logger::log(&format!(
                                    "Errors-file: starting new {} at clock {}",
                                    crate::sys_utils::show_inode(&fd),
                                    match &clock {
                                        Some(clock) => server_notifier_types::show_clock(clock),
                                        None => "[none]".to_string(),
                                    }
                                ));
                                fd
                            }
                        }
                    },
                );
                *state = WriteState::Reporting(fd, 0);
            }
        }
    }

    /// To be called during typechecking.
    /// Anyone reading the current errors file will get this error report as [Ok errors].
    /// This call will failwith if called before [new_empty_file], or after [complete]/[unlink_at_server_stop].
    pub fn report(errors: &diagnostics::T) {
        crate::exit::with_world(|| report_unstopped(errors))
    }

    fn report_unstopped(errors: &diagnostics::T) {
        match errors_file_path() {
            None => {}
            Some(_) => {
                let mut state = write_state();
                match &*state {
                    WriteState::Absent | WriteState::Closed => {
                        panic!("Cannot report in state {}", show_write_state(&state))
                    }
                    WriteState::Reporting(..)
                        if diagnostics::has_no_errors_or_warnings(Some(true), errors) => {}
                    WriteState::Reporting(fd, n) => {
                        let n = n + 1;
                        if n <= 5 {
                            let (error_count, warning_count) =
                                diagnostics::count_errors_and_warnings(
                                    &diagnostics::get_diagnostic_list(Some(true), errors.clone()),
                                );
                            hh_logger::log(&format!(
                                "Errors-file: report#{} on {}: {} new errors, {} new warnings{}",
                                n,
                                crate::sys_utils::show_inode(fd),
                                error_count,
                                warning_count,
                                if n == 5 {
                                    " [won't report any more this typecheck...]"
                                } else {
                                    ""
                                }
                            ));
                        }
                        // sort and dedupe
                        // (`Relative_path.Map.filter` then `map`, over the map of
                        // `drop_fixmed_errors_in_files`; the shape of the OCaml map is
                        // made when the message is written, see `codec::errors`.)
                        let errors: relative_path::map::T<Vec<(FinalizedDiagnostic, isize)>> =
                            diagnostics::as_map(
                                diagnostics::drop_fixmed_errors_in_files(errors.clone()),
                            )
                            .into_iter()
                            .filter(|(path, _errors)| {
                                let is_root = relative_path::is_root(path.prefix());
                                if !is_root {
                                    // Hack_event_logger.invariant_violation_bug
                                    // "error in file outside root" ~path (a no-op in
                                    // the OSS build).
                                }
                                is_root
                            })
                            .map(|(path, errors)| {
                                let errors = diagnostics::sort(errors)
                                    .iter()
                                    .map(|err| {
                                        (
                                            user_diagnostic::to_absolute(err),
                                            user_diagnostic::hash_diagnostic_for_saved_state(err),
                                        )
                                    })
                                    .collect::<Vec<_>>();
                                (path, errors)
                            })
                            .collect();
                        let timestamp = ocaml_unix::gettimeofday();
                        ok(errors_file::write_message(
                            fd,
                            &errors_file::Message::Item(ErrorsFileItem::Errors {
                                errors,
                                timestamp,
                            }),
                        ));
                        match &mut *state {
                            WriteState::Reporting(_, count) => *count = n,
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }
    }

    /// To be called during typechecking.
    /// Anyone reading the current errors file will get this as [Ok Telemetry].
    /// This call will failwith if called before [new_empty_file], or after [complete]/[unlink_at_server_stop].
    pub fn telemetry(telemetry: &telemetry::T) {
        crate::exit::with_world(|| telemetry_unstopped(telemetry))
    }

    fn telemetry_unstopped(telemetry: &telemetry::T) {
        match errors_file_path() {
            None => {}
            Some(_) => {
                let state = write_state();
                match &*state {
                    WriteState::Absent | WriteState::Closed => {
                        panic!("Cannot report in state {}", show_write_state(&state))
                    }
                    WriteState::Reporting(fd, n) => {
                        hh_logger::log(&format!(
                            "Errors-file: report#{} on {}: telemetry [{}]",
                            n,
                            crate::sys_utils::show_inode(fd),
                            telemetry::to_string(None, telemetry)
                        ));
                        ok(errors_file::write_message(
                            fd,
                            &errors_file::Message::Item(ErrorsFileItem::Telemetry(
                                telemetry.clone(),
                            )),
                        ));
                    }
                }
            }
        }
    }

    /// To be called at the end of typechecking.
    /// After this, anyone reading the errors file will get [Error Complete].
    /// This call will failwith if called before [new_empty_file] or after [complete]/[unlink_at_server_stop].
    pub fn complete(telemetry: &telemetry::T) {
        crate::exit::with_world(|| complete_unstopped(telemetry))
    }

    fn complete_unstopped(telemetry: &telemetry::T) {
        match errors_file_path() {
            None => {}
            Some(_) => {
                let mut state = write_state();
                match &*state {
                    WriteState::Absent | WriteState::Closed => {
                        panic!("Cannot complete in state {}", show_write_state(&state))
                    }
                    WriteState::Reporting(fd, n) => {
                        hh_logger::log(&format!(
                            "Errors-file: completing {} after {} reports",
                            crate::sys_utils::show_inode(fd),
                            n
                        ));
                        ok(errors_file::write_message(
                            fd,
                            &errors_file::Message::End {
                                reason: CompletionReason::Complete(telemetry.clone()),
                                timestamp: ocaml_unix::gettimeofday(),
                                log_message: "complete".to_string(),
                            },
                        ));
                        // OCaml leaves the descriptor open (and unreachable):
                        // it is kept open here until the process ends, so
                        // that descriptor numbers are allotted as in OCaml.
                        let old = std::mem::replace(&mut *state, WriteState::Closed);
                        if let WriteState::Reporting(fd, _) = old {
                            std::mem::forget(fd);
                        }
                    }
                }
            }
        }
    }

    /// To be called upon server shutdown, e.g. after "hh stop" or .hhconfig change.
    /// After this, anyone reading the errors file will get [Error Stopped].
    pub fn unlink_at_server_stop() {
        match errors_file_path() {
            None => {}
            Some(errors_file_path) => {
                let mut state = write_state();
                unlink_sentinel_close(
                    &mut state,
                    CompletionReason::Stopped,
                    "unlink",
                    &errors_file_path,
                    || (),
                );
                *state = WriteState::Absent;
            }
        }
    }

    /// Internal, for testing only.
    pub fn get_state_for_test() -> String {
        show_write_state(&write_state())
    }

    /// Internal, for testing only
    pub fn create_file_for_test(pid: isize, cmdline: &str) {
        use std::os::unix::fs::OpenOptionsExt;
        let path = errors_file_path().expect("Option.value_exn");
        let fd = match std::fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .mode(0o666)
            .open(&path)
        {
            Ok(fd) => fd,
            Err(e) => raise(UnixError(e, "open", path)),
        };
        ok(errors_file::write_message(
            &fd,
            &errors_file::Message::VersionHeader {
                version: String::new(),
                extra: yojson::T::Assoc(vec![]),
            },
        ));
        ok(errors_file::write_message(
            &fd,
            &errors_file::Message::Header {
                pid,
                cmdline: cmdline.to_string(),
                timestamp: 0.0,
                clock: None,
            },
        ));
    }
}

pub mod errors_read {
    use super::*;

    /// A [log_message] is a string which should go to logs, but not be surfaced to users.
    pub type LogMessage = String;

    /// A successful call to [openfile] returns this.
    #[derive(Clone, Debug, PartialEq)]
    pub struct OpenSuccess {
        /// the PID of the server process that produced this errors file
        pub pid: isize,
        /// The time at which the typecheck started.
        pub timestamp: f64,
        /// The file watcher clock at which this typecheck started.
        pub clock: Option<server_notifier_types::Clock>,
    }

    #[derive(Debug)]
    pub enum OpenError {
        OReadError(ErrorsFileReadError),
        /// The hh_server that produced these errors is incompatible with the current binary.
        OBuildIdMismatch,
        OKilled(Option<exit_status::FinaleData>),
    }

    /// `pp_open_error` (`[@@deriving show]`, in `ErrorsRead`).
    pub fn pp_open_error(fmt: &mut Formatter, e: &OpenError) {
        // A constructor with an argument: "(@[<2>%s@ " ctor, the argument, "@])"
        let with_arg = |fmt: &mut Formatter, ctor: &str, arg: &dyn Fn(&mut Formatter)| {
            format::pp_print_string(fmt, "(");
            format::pp_open_box(fmt, 2);
            format::pp_print_string(fmt, ctor);
            format::pp_print_space(fmt);
            arg(fmt);
            format::pp_close_box(fmt);
            format::pp_print_string(fmt, ")");
        };
        match e {
            OpenError::OReadError(a0) => with_arg(
                fmt,
                "Server_progress.ErrorsRead.ORead_error",
                &|fmt| pp_errors_file_read_error(fmt, a0),
            ),
            OpenError::OBuildIdMismatch => {
                format::pp_print_string(fmt, "Server_progress.ErrorsRead.OBuild_id_mismatch")
            }
            OpenError::OKilled(a0) => {
                with_arg(fmt, "Server_progress.ErrorsRead.OKilled", &|fmt| match a0 {
                    None => format::pp_print_string(fmt, "None"),
                    Some(x) => {
                        format::pp_print_string(fmt, "(Some ");
                        exit_status::pp_finale_data(fmt, x);
                        format::pp_print_string(fmt, ")");
                    }
                })
            }
        }
    }

    pub fn show_open_error(e: &OpenError) -> String {
        format::asprintf(|fmt| pp_open_error(fmt, e))
    }

    pub fn open_error_short_description(e: &OpenError) -> String {
        match e {
            OpenError::OReadError(ErrorsFileReadError::Malformed) => "malformed header",
            OpenError::OBuildIdMismatch => "client server version mismatch",
            OpenError::OKilled(_) => "hh_server died",
        }
        .to_string()
    }

    fn read_message(fd: &std::fs::File) -> Result<Option<errors_file::Message>, ErrorsFileReadError> {
        match errors_file::read_message(fd) {
            Ok(r) => r,
            Err(e) => raise(e),
        }
    }

    /// [openfile fd] opens an error-file for reading, one that has been created
    /// through [ErrorsWrite.new_empty_file].
    pub fn openfile(fd: &std::fs::File) -> Result<OpenSuccess, (OpenError, LogMessage)> {
        let read_message =
            |fd| read_message(fd).map_err(|e| (OpenError::OReadError(e), String::new()));
        let message1 = read_message(fd)?;
        let message2 = read_message(fd)?;
        match (message1, message2) {
            (
                Some(errors_file::Message::VersionHeader { version, .. }),
                Some(errors_file::Message::Header {
                    pid,
                    cmdline,
                    clock,
                    timestamp,
                }),
            ) => {
                let build_revision = crate::build_id::build_revision();
                if version.len() > 16 && build_revision.len() > 16 && version != build_revision {
                    // This is a version mismatch which we can't ignore. (We always ignore mismatch from dev-builds...
                    // version="" means a buck dev build, and version.length<=16 means a dune dev build.)
                    let msg = format!(
                        "errors-file is version {}, but we are {}",
                        version, build_revision
                    );
                    Err((OpenError::OBuildIdMismatch, msg))
                } else if !proc::is_alive(pid, &cmdline) {
                    let server_finale_file = server_files::server_finale_file(pid);
                    let finale_data = exit_status::get_finale_data(&server_finale_file);
                    Err((
                        OpenError::OKilled(finale_data),
                        "Errors-file is from defunct PID".to_string(),
                    ))
                } else {
                    Ok(OpenSuccess {
                        pid,
                        clock,
                        timestamp,
                    })
                }
            }
            _ => panic!("impossible message combination"),
        }
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum ReadResult {
        RItem(ErrorsFileItem),
        RCompleted(CompletionReason, String),
    }

    /// Attempt to get the next batch of errors. It returns based on a queue
    /// of what the server was written to the errors file...
    /// * For each time the server did [ErrorsWrite.report errors], this function will return [Ok (Some (RItem (Errors { errors; timestamp })))].
    /// * If the server hasn't yet done further [ErrorsWrite.report], this will return [Ok None].
    /// * If the server did [ErrorsWrite.complete] then this will return [Ok (Some (RCompleted (Complete _, _)))].
    /// * If the server did [ErrorsWrite.new_empty_file] then this will return [Ok (Some (RCompleted (Restarted _, _)))].
    /// * If the server did [ErrorsWrite.unlink_at_server_stop] then this will return [Ok (Some (RCompleted (Stopped, _)))].
    pub fn read_next_errors(fd: &std::fs::File) -> Result<Option<ReadResult>, ErrorsFileReadError> {
        Ok(read_message(fd)?.map(|message| match message {
            errors_file::Message::VersionHeader { .. } | errors_file::Message::Header { .. } => {
                panic!(
                    "do Server_progress.ErrorsRead.openfile before read_next_error or Server_progress_lwt.watch_errors_file"
                )
            }
            errors_file::Message::Item(item) => ReadResult::RItem(item),
            errors_file::Message::End {
                reason,
                log_message,
                ..
            } => ReadResult::RCompleted(reason, log_message),
        }))
    }
}

/// The OCaml representation of the errors-file messages (what `Marshal`
/// writes and reads).
///
/// The values are built without sharing. The OCaml shares what its program
/// shares: the same string literal (`"Invalid return type"`, the `" "` of an
/// explanation's `Prefix`, a telemetry key), or the same constant
/// (`Prefix { prefix = "The subtype comes from this"; sep = " " }`), met
/// twice in one message is one object, written once then as a shared
/// reference. Nothing in the Rust values says which strings were literals,
/// so a file written here can differ from the OCaml's for the same errors in
/// that the OCaml's has shared references where this one repeats the
/// object; both decode to the same value, so each implementation reads the
/// other's files.
pub(crate) mod codec {
    use oxidized::classish_positions_types;
    use oxidized::explanation::Elem;
    use oxidized::explanation::Explanation;
    use oxidized::file_pos_large::FilePosLarge;
    use oxidized::message::Message as DiagMessage;
    use oxidized::quickfix::Edits;
    use oxidized::quickfix::HintStyle;
    use oxidized::quickfix::Quickfix;

    use super::*;
    use crate::pos::APos;
    use crate::rt::ocaml_marshal::ConvError;
    use crate::rt::ocaml_marshal::FromOcaml;
        use crate::rt::ocaml_marshal::Value;
    use crate::user_diagnostic::Severity;

    type R<A> = Result<A, ConvError>;

    fn bad<A>(what: &str, v: &Value) -> R<A> {
        let mut d = format!("{:?}", v);
        if d.len() > 300 {
            let mut cut = 300;
            while !d.is_char_boundary(cut) {
                cut -= 1;
            }
            d.truncate(cut);
            d.push_str("...");
        }
        Err(ConvError(format!("not {}: {}", what, d)))
    }

    fn string(s: &str) -> Value {
        Value::string(s.as_bytes())
    }

    fn string_of(v: &Value) -> R<String> {
        String::from_ocaml(v)
    }

    // ~~ Yojson.Safe.t ~~

    pub fn yojson(j: &yojson::T) -> Value {
        use yojson::T as J;
        let pv = |name: &str, arg: Option<Value>| Value::poly_variant(name, arg);
        match j {
            J::Null => pv("Null", None),
            J::Bool(b) => pv("Bool", Some(Value::bool(*b))),
            J::Int(i) => pv("Int", Some(Value::int(*i as i64))),
            J::Intlit(s) => pv("Intlit", Some(string(s))),
            J::Float(f) => pv("Float", Some(Value::double(*f))),
            J::String(s) => pv("String", Some(string(s))),
            J::Assoc(l) => pv(
                "Assoc",
                Some(Value::list(
                    l.iter()
                        .map(|(k, v)| Value::block(0, vec![string(k), yojson(v)]))
                        .collect::<Vec<_>>(),
                )),
            ),
            J::List(l) => pv("List", Some(Value::list(l.iter().map(yojson).collect::<Vec<_>>()))),
        }
    }

    pub fn yojson_of_ocaml(v: &Value) -> R<yojson::T> {
        use yojson::T as J;
        let h = ocaml_marshal::hash_variant;
        match v {
            Value::Int(n) if *n == h("Null") => Ok(J::Null),
            Value::Int(_) => bad("a Yojson.Safe.t", v),
            Value::Ptr(_) => {
                let f = v.fields(0, 2)?;
                let tag = f[0].as_int()?;
                let arg = &f[1];
                if tag == h("Bool") {
                    Ok(J::Bool(bool::from_ocaml(arg)?))
                } else if tag == h("Int") {
                    Ok(J::Int(arg.as_int()? as isize))
                } else if tag == h("Intlit") {
                    Ok(J::Intlit(string_of(arg)?))
                } else if tag == h("Float") {
                    Ok(J::Float(arg.as_double()?))
                } else if tag == h("String") {
                    Ok(J::String(string_of(arg)?))
                } else if tag == h("Assoc") {
                    let mut l = vec![];
                    for kv in arg.list_items()? {
                        let kv = kv.fields(0, 2)?;
                        l.push((string_of(&kv[0])?, yojson_of_ocaml(&kv[1])?));
                    }
                    Ok(J::Assoc(l))
                } else if tag == h("List") {
                    let l: R<Vec<_>> = arg.list_items()?.into_iter().map(yojson_of_ocaml).collect();
                    Ok(J::List(l?))
                } else {
                    // `Tuple and `Variant have no Rust counterpart.
                    bad("a Yojson.Safe.t that the Rust Yojson has", v)
                }
            }
        }
    }

    // ~~ Telemetry.t = (string * Yojson.Safe.t) list ~~

    /// The pairs of a telemetry, head (most recent) first.
    fn telemetry_pairs(t: &telemetry::T) -> Vec<(String, yojson::T)> {
        match telemetry::to_yojson(t) {
            yojson::T::Assoc(l) => l.into_iter().rev().collect(),
            _ => unreachable!(),
        }
    }

    pub fn telemetry(t: &telemetry::T) -> Value {
        Value::list(
            telemetry_pairs(t)
                .iter()
                .map(|(k, v)| Value::block(0, vec![string(k), yojson(v)]))
                .collect::<Vec<_>>(),
        )
    }

    pub fn telemetry_of_ocaml(v: &Value) -> R<telemetry::T> {
        let mut pairs = vec![];
        for kv in v.list_items()? {
            let kv = kv.fields(0, 2)?;
            pairs.push((string_of(&kv[0])?, yojson_of_ocaml(&kv[1])?));
        }
        // `json` conses a pair onto the list: rebuild from the tail.
        let mut t = telemetry::create();
        for (k, v) in pairs.into_iter().rev() {
            t = telemetry::json(&k, v, t);
        }
        Ok(t)
    }

    // ~~ Server_notifier_types.clock ~~

    fn clock(c: &server_notifier_types::Clock) -> Value {
        match c {
            server_notifier_types::Clock::Watchman(s) => Value::block(0, vec![string(s)]),
            server_notifier_types::Clock::Eden(s) => Value::block(1, vec![string(s)]),
        }
    }

    fn clock_of_ocaml(v: &Value) -> R<server_notifier_types::Clock> {
        match v.as_block()? {
            (0, [s]) => Ok(server_notifier_types::Clock::Watchman(string_of(s)?)),
            (1, [s]) => Ok(server_notifier_types::Clock::Eden(string_of(s)?)),
            _ => bad("a Server_notifier_types.clock", v),
        }
    }

    // ~~ completion_reason ~~

    fn completion_reason(r: &CompletionReason) -> Value {
        match r {
            CompletionReason::Complete(t) => Value::block(0, vec![telemetry(t)]),
            CompletionReason::Restarted {
                user_message,
                log_message,
            } => Value::block(1, vec![string(user_message), string(log_message)]),
            CompletionReason::Stopped => Value::int(0),
        }
    }

    fn completion_reason_of_ocaml(v: &Value) -> R<CompletionReason> {
        match v {
            Value::Int(0) => Ok(CompletionReason::Stopped),
            Value::Int(_) => bad("a completion_reason", v),
            Value::Ptr(_) => match v.as_block()? {
                (0, [t]) => Ok(CompletionReason::Complete(telemetry_of_ocaml(t)?)),
                (1, [u, l]) => Ok(CompletionReason::Restarted {
                    user_message: string_of(u)?,
                    log_message: string_of(l)?,
                }),
                _ => bad("a completion_reason", v),
            },
        }
    }

    // ~~ Pos.absolute = string Pos.pos ~~
    //
    // `Pos_small { pos_file; pos_start; pos_end }` (tag 0, two
    // `File_pos_small.t`), `Pos_large` (tag 1, two `File_pos_large.t`
    // records `{pos_lnum; pos_bol; pos_offset}`), `Pos_tiny { pos_file;
    // pos_span }` (tag 2, a `Pos_span_tiny.t`), `Pos_from_reason p` (tag 3).
    // `Pos.to_absolute` keeps the constructor of the relative position,
    // which the OCaml makes compressed (`Pos.compress`: tiny if it fits,
    // else small, else large), as the Rust positions are: a position is
    // written compressed.

    /// `File_pos_large.t` as `(pos_lnum, pos_bol, pos_offset)`, the dummy
    /// being `(0, 0, -1)`.
    fn large_of(p: FilePosLarge) -> (i64, i64, i64) {
        let (lnum, bol, offset) = p.line_beg_offset();
        (lnum as i64, bol as i64, offset as isize as i64)
    }

    fn large_to(lnum: i64, bol: i64, offset: i64) -> FilePosLarge {
        if lnum == 0 && bol == 0 && offset == -1 {
            FilePosLarge::make_dummy()
        } else {
            FilePosLarge::from_lnum_bol_offset(lnum as usize, bol as usize, offset as usize)
        }
    }

    const TINY_DUMMY: i64 = -1;

    fn mask(bits: u32) -> i64 {
        (1 << bits) - 1
    }

    /// `Pos_span_tiny.make ~pos_start ~pos_end`
    fn tiny_make(start: (i64, i64, i64), end: (i64, i64, i64)) -> Option<i64> {
        let dummy = (0, 0, -1);
        if start == dummy || end == dummy {
            return Some(TINY_DUMMY);
        }
        let (start_line, start_bol, start_offset) = start;
        let (end_line, end_bol, end_offset) = end;
        if start_offset < start_bol
            || end_bol < start_bol
            || end_line < start_line
            || end_offset < start_offset
        {
            return None;
        }
        let start_col = start_offset - start_bol;
        let bol_increment = end_bol - start_bol;
        let line_increment = end_line - start_line;
        let width = end_offset - start_offset;
        if start_bol > mask(21)
            || start_line > mask(16)
            || start_col > mask(20)
            || bol_increment > mask(0)
            || line_increment > mask(0)
            || width > mask(6)
        {
            return None;
        }
        Some((start_bol << 42) | (start_line << 26) | (start_col << 6) | width)
    }

    /// The start and end of a `Pos_span_tiny.t`.
    fn tiny_span(span: i64) -> (FilePosLarge, FilePosLarge) {
        if span == TINY_DUMMY {
            return (FilePosLarge::make_dummy(), FilePosLarge::make_dummy());
        }
        let field = |offset: u32, bits: u32| ((span as u64 >> offset) as i64) & mask(bits);
        let start_bol = field(42, 21);
        let start_line = field(26, 16);
        let start_col = field(6, 20);
        let width = field(0, 6);
        let start_offset = start_bol + start_col;
        (
            large_to(start_line, start_bol, start_offset),
            large_to(start_line, start_bol, start_offset + width),
        )
    }

    /// `File_pos_small.of_large_pos`
    fn small_of_large((lnum, bol, offset): (i64, i64, i64)) -> Option<i64> {
        let col = offset - bol;
        if col > mask(9) || lnum > mask(24) || bol > mask(30) {
            None
        } else if col < 0 {
            Some(-1)
        } else {
            Some((bol << 33) + (lnum << 9) + col)
        }
    }

    /// `File_pos_small.as_large_pos`
    fn small_to_large(p: i64) -> FilePosLarge {
        if p == -1 {
            // line_column_beg dummy = (0, -1, 0): of_lnum_bol_offset 0 0 (-1)
            return FilePosLarge::make_dummy();
        }
        let bol = ((p as u64 >> 33) as i64) & mask(30);
        let line = ((p as u64 >> 9) as i64) & mask(24);
        let col = p & mask(9);
        large_to(line, bol, bol + col)
    }

    pub fn pos(p: &crate::pos::Absolute) -> Value {
        let file = string(&p.pos_file());
        let span = p.raw_span();
        let start = large_of(span.start);
        let end = large_of(span.end);
        match tiny_make(start, end) {
            Some(span) => Value::block(2, vec![file, Value::int(span)]),
            None => match (small_of_large(start), small_of_large(end)) {
                (Some(s), Some(e)) => Value::block(0, vec![file, Value::int(s), Value::int(e)]),
                _ => {
                    let large = |(l, b, o): (i64, i64, i64)| {
                        Value::block(0, vec![Value::int(l), Value::int(b), Value::int(o)])
                    };
                    Value::block(1, vec![file, large(start), large(end)])
                }
            },
        }
    }

    pub fn pos_of_ocaml(v: &Value) -> R<crate::pos::Absolute> {
        let (file, start, end) = match v.as_block()? {
            (0, [file, s, e]) => (file, small_to_large(s.as_int()?), small_to_large(e.as_int()?)),
            (1, [file, s, e]) => {
                let large = |v: &Value| -> R<FilePosLarge> {
                    let f = v.fields(0, 3)?;
                    Ok(large_to(f[0].as_int()?, f[1].as_int()?, f[2].as_int()?))
                };
                (file, large(s)?, large(e)?)
            }
            (2, [file, span]) => {
                let (s, e) = tiny_span(span.as_int()?);
                (file, s, e)
            }
            (3, [p]) => return pos_of_ocaml(p),
            _ => return bad("a Pos.absolute", v),
        };
        Ok(crate::pos::make_absolute(string_of(file)?, start, end))
    }

    // ~~ Diagnostics.finalized_diagnostic ~~

    fn diag_message(m: &DiagMessage<crate::pos::Absolute>) -> Value {
        Value::block(0, vec![pos(&m.0), Value::string(m.1.to_vec())])
    }

    fn diag_message_of(v: &Value) -> R<DiagMessage<crate::pos::Absolute>> {
        let f = v.fields(0, 2)?;
        Ok(DiagMessage(pos_of_ocaml(&f[0])?, bstr::BString::from_ocaml(&f[1])?))
    }

    fn elem(e: &Elem<crate::pos::Absolute>) -> Value {
        match e {
            Elem::Witness(p, s) => Value::block(0, vec![pos(p), string(s)]),
            Elem::WitnessNoPos(s) => Value::block(1, vec![string(s)]),
            Elem::Rule(s) => Value::block(2, vec![string(s)]),
            Elem::Step(s, b) => Value::block(3, vec![string(s), Value::bool(*b)]),
            Elem::Trans(s) => Value::block(4, vec![string(s)]),
            Elem::Prefix { prefix, sep } => Value::block(5, vec![string(prefix), string(sep)]),
            Elem::Suffix { suffix, sep } => Value::block(6, vec![string(suffix), string(sep)]),
        }
    }

    fn elem_of(v: &Value) -> R<Elem<crate::pos::Absolute>> {
        match v.as_block()? {
            (0, [p, s]) => Ok(Elem::Witness(pos_of_ocaml(p)?, string_of(s)?)),
            (1, [s]) => Ok(Elem::WitnessNoPos(string_of(s)?)),
            (2, [s]) => Ok(Elem::Rule(string_of(s)?)),
            (3, [s, b]) => Ok(Elem::Step(string_of(s)?, bool::from_ocaml(b)?)),
            (4, [s]) => Ok(Elem::Trans(string_of(s)?)),
            (5, [p, s]) => Ok(Elem::Prefix {
                prefix: string_of(p)?,
                sep: string_of(s)?,
            }),
            (6, [p, s]) => Ok(Elem::Suffix {
                suffix: string_of(p)?,
                sep: string_of(s)?,
            }),
            _ => bad("an Explanation.elem", v),
        }
    }

    fn explanation(e: &Explanation<crate::pos::Absolute>) -> Value {
        match e {
            Explanation::Derivation(elems) => {
                Value::block(0, vec![Value::list(elems.iter().map(elem).collect::<Vec<_>>())])
            }
            Explanation::Debug(s) => Value::block(1, vec![string(s)]),
            Explanation::Empty => Value::int(0),
        }
    }

    fn explanation_of(v: &Value) -> R<Explanation<crate::pos::Absolute>> {
        match v {
            Value::Int(0) => Ok(Explanation::Empty),
            Value::Int(_) => bad("an Explanation.t", v),
            Value::Ptr(_) => match v.as_block()? {
                (0, [l]) => Ok(Explanation::Derivation(
                    l.list_items()?.into_iter().map(elem_of).collect::<R<_>>()?,
                )),
                (1, [s]) => Ok(Explanation::Debug(string_of(s)?)),
                _ => bad("an Explanation.t", v),
            },
        }
    }

    fn classish_pos(p: &classish_positions_types::Pos<crate::pos::Absolute>) -> Value {
        use classish_positions_types::Pos as C;
        match p {
            C::Precomputed(p) => Value::block(0, vec![pos(p)]),
            C::ClassishEndOfBody(s) => Value::block(1, vec![string(s)]),
            C::ClassishStartOfBody(s) => Value::block(2, vec![string(s)]),
            C::ClassishClosingBrace(s) => Value::block(3, vec![string(s)]),
        }
    }

    fn classish_pos_of(v: &Value) -> R<classish_positions_types::Pos<crate::pos::Absolute>> {
        use classish_positions_types::Pos as C;
        match v.as_block()? {
            (0, [p]) => Ok(C::Precomputed(pos_of_ocaml(p)?)),
            (1, [s]) => Ok(C::ClassishEndOfBody(string_of(s)?)),
            (2, [s]) => Ok(C::ClassishStartOfBody(string_of(s)?)),
            (3, [s]) => Ok(C::ClassishClosingBrace(string_of(s)?)),
            _ => bad("a Classish_positions_types.pos", v),
        }
    }

    fn quickfix(q: &Quickfix<crate::pos::Absolute>) -> Value {
        let edits = match &q.edits {
            Edits::Eager(l) => Value::block(
                0,
                vec![Value::list(
                    l.iter()
                        .map(|(s, p)| Value::block(0, vec![string(s), pos(p)]))
                        .collect::<Vec<_>>(),
                )],
            ),
            Edits::ClassishEnd { new_text, name } => {
                Value::block(1, vec![string(new_text), string(name)])
            }
            Edits::AddFunctionAttribute {
                function_pos,
                attribute_name,
            } => Value::block(2, vec![pos(function_pos), string(attribute_name)]),
        };
        let hint_styles = Value::list(
            q.hint_styles
                .iter()
                .map(|h| match h {
                    HintStyle::HintStyleSilent(p) => Value::block(0, vec![classish_pos(p)]),
                    HintStyle::HintStyleHint(p) => Value::block(1, vec![classish_pos(p)]),
                })
                .collect::<Vec<_>>(),
        );
        Value::block(0, vec![string(&q.title), edits, hint_styles])
    }

    fn quickfix_of(v: &Value) -> R<Quickfix<crate::pos::Absolute>> {
        let f = v.fields(0, 3)?;
        let edits = match f[1].as_block()? {
            (0, [l]) => {
                let mut edits = vec![];
                for e in l.list_items()? {
                    let e = e.fields(0, 2)?;
                    edits.push((string_of(&e[0])?, pos_of_ocaml(&e[1])?));
                }
                Edits::Eager(edits)
            }
            (1, [t, n]) => Edits::ClassishEnd {
                new_text: string_of(t)?,
                name: string_of(n)?,
            },
            (2, [p, a]) => Edits::AddFunctionAttribute {
                function_pos: pos_of_ocaml(p)?,
                attribute_name: string_of(a)?,
            },
            _ => return bad("a Quickfix.edits", &f[1]),
        };
        let mut hint_styles = vec![];
        for h in f[2].list_items()? {
            hint_styles.push(match h.as_block()? {
                (0, [p]) => HintStyle::HintStyleSilent(classish_pos_of(p)?),
                (1, [p]) => HintStyle::HintStyleHint(classish_pos_of(p)?),
                _ => return bad("a Quickfix.hint_style", h),
            });
        }
        Ok(Quickfix {
            title: string_of(&f[0])?,
            edits,
            hint_styles,
        })
    }

    fn severity(s: &Severity) -> Value {
        match s {
            Severity::Warning { is_trusted } => Value::block(0, vec![Value::bool(*is_trusted)]),
            Severity::Err => Value::int(0),
        }
    }

    fn severity_of(v: &Value) -> R<Severity> {
        match v {
            Value::Int(0) => Ok(Severity::Err),
            Value::Int(_) => bad("a User_diagnostic.severity", v),
            Value::Ptr(_) => Ok(Severity::Warning {
                is_trusted: bool::from_ocaml(&v.fields(0, 1)?[0])?,
            }),
        }
    }

    pub fn diagnostic(d: &FinalizedDiagnostic) -> Value {
        Value::block(
            0,
            vec![
                severity(&d.severity),
                Value::int(d.code as i64),
                diag_message(&d.claim),
                Value::list(d.reasons.iter().map(diag_message).collect::<Vec<_>>()),
                explanation(&d.explanation),
                Value::list(d.quickfixes.iter().map(quickfix).collect::<Vec<_>>()),
                Value::list(d.custom_msgs.iter().map(|s| string(s)).collect::<Vec<_>>()),
                Value::bool(d.is_fixmed),
                match &d.function_pos {
                    None => Value::int(0),
                    Some(p) => Value::some(pos(p)),
                },
            ],
        )
    }

    pub fn diagnostic_of(v: &Value) -> R<FinalizedDiagnostic> {
        let f = v.fields(0, 9)?;
        Ok(user_diagnostic::UserDiagnostic {
            severity: severity_of(&f[0])?,
            code: f[1].as_int()? as isize,
            claim: diag_message_of(&f[2])?,
            reasons: f[3].list_items()?.into_iter().map(diag_message_of).collect::<R<_>>()?,
            explanation: explanation_of(&f[4])?,
            quickfixes: f[5].list_items()?.into_iter().map(quickfix_of).collect::<R<_>>()?,
            custom_msgs: Vec::<String>::from_ocaml(&f[6])?,
            is_fixmed: bool::from_ocaml(&f[7])?,
            function_pos: match &f[8] {
                Value::Int(0) => None,
                p => Some(pos_of_ocaml(&p.fields(0, 1)?[0])?),
            },
        })
    }

    // ~~ Relative_path.t = prefix * string ~~

    fn prefix(p: relative_path::Prefix) -> Value {
        Value::int(match p {
            relative_path::Prefix::Root => 0,
            relative_path::Prefix::Hhi => 1,
            relative_path::Prefix::Dummy => 2,
            relative_path::Prefix::Tmp => 3,
        })
    }

    fn relative_path(p: &relative_path::T) -> Value {
        use std::os::unix::ffi::OsStrExt;
        Value::block(
            0,
            vec![prefix(p.prefix()), Value::string(p.path().as_os_str().as_bytes())],
        )
    }

    fn relative_path_of(v: &Value) -> R<relative_path::T> {
        use std::os::unix::ffi::OsStrExt;
        let f = v.fields(0, 2)?;
        let prefix = match f[0].as_int()? {
            0 => relative_path::Prefix::Root,
            1 => relative_path::Prefix::Hhi,
            2 => relative_path::Prefix::Dummy,
            3 => relative_path::Prefix::Tmp,
            _ => return bad("a Relative_path.prefix", &f[0]),
        };
        let suffix = std::ffi::OsStr::from_bytes(f[1].as_bytes()?);
        Ok(relative_path::T::make(prefix, std::path::PathBuf::from(suffix)))
    }

    // ~~ errors_file_item and message ~~

    /// `(Diagnostics.finalized_diagnostic * int) list Relative_path.Map.t`:
    /// the map that adding the bindings in key order makes (the shape of
    /// what [`errors_write::report`] writes).
    pub fn errors(errors: &relative_path::map::T<Vec<(FinalizedDiagnostic, isize)>>) -> Value {
        let m = ocaml_map::of_iter(errors.iter().map(|(k, v)| (k, v)), &|a, b| a.cmp(b));
        ocaml_map::to_ocaml(&m, &mut |k| relative_path(k), &mut |l| {
            Value::list(
                l.iter()
                    .map(|(d, h)| Value::block(0, vec![diagnostic(d), Value::int(*h as i64)]))
                    .collect::<Vec<_>>(),
            )
        })
    }

    fn errors_of(v: &Value) -> R<relative_path::map::T<Vec<(FinalizedDiagnostic, isize)>>> {
        let mut m = relative_path::map::T::new();
        for (k, d) in ocaml_map::bindings_of_ocaml(v)? {
            let mut l = vec![];
            for e in d.list_items()? {
                let e = e.fields(0, 2)?;
                l.push((diagnostic_of(&e[0])?, e[1].as_int()? as isize));
            }
            m.insert(relative_path_of(k)?, l);
        }
        Ok(m)
    }

    fn item(i: &ErrorsFileItem) -> Value {
        match i {
            ErrorsFileItem::Errors { errors: e, timestamp } => {
                Value::block(0, vec![errors(e), Value::double(*timestamp)])
            }
            ErrorsFileItem::Telemetry(t) => Value::block(1, vec![telemetry(t)]),
        }
    }

    fn item_of(v: &Value) -> R<ErrorsFileItem> {
        match v.as_block()? {
            (0, [e, t]) => Ok(ErrorsFileItem::Errors {
                errors: errors_of(e)?,
                timestamp: t.as_double()?,
            }),
            (1, [t]) => Ok(ErrorsFileItem::Telemetry(telemetry_of_ocaml(t)?)),
            _ => bad("an errors_file_item", v),
        }
    }

    pub fn message(m: &errors_file::Message) -> Value {
        use errors_file::Message as M;
        match m {
            M::VersionHeader { version, extra } => {
                Value::block(0, vec![string(version), yojson(extra)])
            }
            M::Header {
                pid,
                cmdline,
                timestamp,
                clock: c,
            } => Value::block(
                1,
                vec![
                    Value::int(*pid as i64),
                    string(cmdline),
                    Value::double(*timestamp),
                    match c {
                        None => Value::int(0),
                        Some(c) => Value::some(clock(c)),
                    },
                ],
            ),
            M::Item(i) => Value::block(2, vec![item(i)]),
            M::End {
                reason,
                timestamp,
                log_message,
            } => Value::block(
                3,
                vec![
                    completion_reason(reason),
                    Value::double(*timestamp),
                    string(log_message),
                ],
            ),
        }
    }

    pub fn message_of_ocaml(v: &Value) -> R<errors_file::Message> {
        use errors_file::Message as M;
        match v.as_block()? {
            (0, [version, extra]) => Ok(M::VersionHeader {
                version: string_of(version)?,
                extra: yojson_of_ocaml(extra)?,
            }),
            (1, [pid, cmdline, timestamp, c]) => Ok(M::Header {
                pid: pid.as_int()? as isize,
                cmdline: string_of(cmdline)?,
                timestamp: timestamp.as_double()?,
                clock: match c {
                    Value::Int(0) => None,
                    c => Some(clock_of_ocaml(&c.fields(0, 1)?[0])?),
                },
            }),
            (2, [i]) => Ok(M::Item(item_of(i)?)),
            (3, [reason, timestamp, log_message]) => Ok(M::End {
                reason: completion_reason_of_ocaml(reason)?,
                timestamp: timestamp.as_double()?,
                log_message: string_of(log_message)?,
            }),
            _ => bad("an errors-file message", v),
        }
    }
}

#[cfg(test)]
mod errors_tests;

#[cfg(test)]
pub(crate) mod tests {
    use std::os::unix::fs::MetadataExt;

    use super::*;

    /// The root, the stack and `Server_files`' temporary directory are
    /// global: the tests that use them take turns (those of `errors_tests`
    /// too, and the daemon's tests in `server_main`).
    pub(crate) fn serial() -> MutexGuard<'static, ()> {
        static SERIAL: Mutex<()> = Mutex::new(());
        SERIAL.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// A root of its own (the progress file is named after it).
    fn set_test_root(name: &str) -> String {
        crate::server_files::tests::testing_tmp();
        let root = format!("/nonexistent/hh_server_progress_test/{}/{}", std::process::id(), name);
        set_root(root.clone());
        let file = server_files::server_progress_file(&root);
        let _ = std::fs::remove_file(&file);
        file
    }

    /// The `progress.json` of the OCaml server (captured from the oracle,
    /// `DReady "ready"`): the same text for the same record.
    #[test]
    fn ocaml_progress_json() {
        let ocaml = "{\n  \"pid\": 52306,\n  \"disposition\": [ \"DReady\" ],\n  \"message\": \"ready\",\n  \"timestamp\": 1794517138.037042\n}";
        let t = T {
            pid: 52306,
            disposition: Disposition::DReady,
            message: "ready".to_string(),
            timestamp: 1794517138.037042,
        };
        assert_eq!(crate::yojson::safe::pretty_to_string(&yojson_of_t(&t)), ocaml);
        assert_eq!(t_of_yojson(&yojson::from_string(ocaml).unwrap()), Ok(t));
        // A whole-second timestamp keeps its ".0".
        let t = T {
            pid: 1,
            disposition: Disposition::DWorking,
            message: "typechecking 5/15 files (33.3%)".to_string(),
            timestamp: 1794517138.0,
        };
        assert!(crate::yojson::safe::pretty_to_string(&yojson_of_t(&t)).contains("\"timestamp\": 1794517138.0\n"));
    }

    #[test]
    fn the_file_is_what_ocaml_writes() {
        let _serial = serial();
        let file = set_test_root("format");
        write(None, Some(Disposition::DReady), "ready");
        let content = std::fs::read_to_string(&file).unwrap();
        let t = read();
        assert_eq!(t.pid, ocaml_unix::getpid());
        assert_eq!(t.disposition, Disposition::DReady);
        assert_eq!(t.message, "ready");
        assert_eq!(
            content,
            format!(
                "{{\n  \"pid\": {},\n  \"disposition\": [ \"DReady\" ],\n  \"message\": \"ready\",\n  \"timestamp\": {}\n}}",
                t.pid,
                yojson::to_string(&yojson::T::Float(t.timestamp))
            )
        );
        assert_eq!(std::fs::metadata(&file).unwrap().mode() & 0o777, 0o666);
        // What test/integration/test_edenfs_file_watcher.py reads.
        let json: serde_json::Value = serde_json::from_str(&content).unwrap();
        assert_eq!(json["disposition"], serde_json::json!(["DReady"]));
        // A shorter message after a longer one: the file is truncated.
        write(None, None, "typechecking 5/15 files (33.3%) and a long tail");
        write(None, None, "x");
        assert_eq!(read().message, "x");
        assert_eq!(read().disposition, Disposition::DWorking);
        try_delete();
        assert!(!std::path::Path::new(&file).exists());
        try_delete();
    }

    #[test]
    fn missing_dead_and_corrupt_files() {
        let _serial = serial();
        let file = set_test_root("read");
        // No file.
        let t = read();
        assert_eq!(
            (t.pid, t.disposition, t.message.as_str()),
            (0, Disposition::DStopped, "stopped")
        );
        // Left behind by a dead process.
        let mut child = std::process::Command::new("true").spawn().unwrap();
        let dead_pid = child.id();
        child.wait().unwrap();
        let write_raw = |content: &str| std::fs::write(&file, content).unwrap();
        write_raw(&format!(
            "{{\"pid\": {}, \"disposition\": [\"DWorking\"], \"message\": \"typechecking\", \"timestamp\": 1.5}}",
            dead_pid
        ));
        let t = read();
        assert_eq!(
            (t.pid, t.disposition, t.message.as_str()),
            (0, Disposition::DStopped, "stopped")
        );
        // Written by a live one, by hand: any order, an `Int` timestamp,
        // Yojson's comments and unquoted names.
        let me = ocaml_unix::getpid();
        write_raw(&format!(
            "/* hi */ {{timestamp: 2, \"message\": \"m\", \"disposition\": [\"DReady\"], \"pid\": {}}}",
            me
        ));
        assert_eq!(
            read(),
            T {
                pid: me,
                disposition: Disposition::DReady,
                message: "m".to_string(),
                timestamp: 2.0
            }
        );
        // Corrupt: unknown state.
        for content in [
            "not json".to_string(),
            "{}".to_string(),
            "[1]".to_string(),
            // A bare string is not a constructor.
            format!(
                "{{\"pid\": {}, \"disposition\": \"DReady\", \"message\": \"m\", \"timestamp\": 1.0}}",
                me
            ),
            // An extra field.
            format!(
                "{{\"pid\": {}, \"disposition\": [\"DReady\"], \"message\": \"m\", \"timestamp\": 1.0, \"x\": 1}}",
                me
            ),
            // A duplicate one.
            format!(
                "{{\"pid\": {}, \"pid\": {}, \"disposition\": [\"DReady\"], \"message\": \"m\", \"timestamp\": 1.0}}",
                me, me
            ),
            // A pid that is not an int.
            "{\"pid\": 1.0, \"disposition\": [\"DReady\"], \"message\": \"m\", \"timestamp\": 1.0}"
                .to_string(),
        ] {
            write_raw(&content);
            let t = read();
            assert_eq!(
                (t.pid, t.disposition, t.message.as_str()),
                (0, Disposition::DStopped, "unknown state"),
                "{}",
                content
            );
        }
        try_delete();
    }

    #[test]
    fn of_yojson_messages() {
        let parse = |s: &str| t_of_yojson(&yojson::from_string(s).unwrap());
        assert_eq!(
            parse(r#"{"pid": 1, "disposition": ["DReady"], "message": "m", "timestamp": 1.0, "x": 1, "y": 2}"#),
            Err(OfYojsonError(
                r#"server_progress.ml.t: extra fields: x y: {"pid":1,"disposition":["DReady"],"message":"m","timestamp":1.0,"x":1,"y":2}"#
                    .to_string()
            ))
        );
        assert_eq!(
            parse(r#"{"pid": 1}"#),
            Err(OfYojsonError(
                r#"server_progress.ml.t: the following record elements were undefined: {"pid":1}"#
                    .to_string()
            ))
        );
        assert_eq!(
            parse(r#"{"pid": "1"}"#),
            Err(OfYojsonError(r#"int_of_yojson: integer needed: "1""#.to_string()))
        );
        assert_eq!(
            disposition_of_yojson(&yojson::T::String("DReady".to_string())),
            Err(OfYojsonError(
                r#"server_progress.ml.disposition: unexpected variant constructor: "DReady""#
                    .to_string()
            ))
        );
        // An integer that is too big for a timestamp `Int` is still a float.
        assert_eq!(
            parse(r#"{"pid": 1, "disposition": ["DReady"], "message": "m", "timestamp": 12345678901234567890}"#)
                .map(|t| t.timestamp),
            Ok(12345678901234567890.0)
        );
    }

    #[test]
    fn messages_and_frames() {
        let _serial = serial();
        set_test_root("frames");
        write(None, None, "outer");
        let x = with_message(None, None, "inner", || {
            assert_eq!(read().message, "inner");
            write(None, None, "inner changed");
            assert_eq!(read().message, "inner changed");
            with_frame(Some(Disposition::DReady), || {
                write(None, None, "in frame");
                assert_eq!(read().message, "in frame");
            });
            // The frame restored the message of `with_message`, with its
            // disposition.
            assert_eq!(read().message, "inner changed");
            assert_eq!(read().disposition, Disposition::DReady);
            42
        });
        assert_eq!(x, 42);
        assert_eq!(read().message, "outer");
        write_percentage("typechecking", 5, 15, "files", None);
        assert_eq!(read().message, "typechecking 5/15 files (33.3%)");
        try_delete();
    }

    /// The monitor and the server, two processes in OCaml, are threads of
    /// one process here: a reader never sees a writer half-way (a long
    /// message overwritten by a short one before the file is truncated would
    /// read as "unknown state").
    #[test]
    fn writers_and_readers_on_threads() {
        let _serial = serial();
        set_test_root("threads");
        let long = "l".repeat(2000);
        write_message(Some(false), None, "short");
        std::thread::scope(|s| {
            for i in 0..4 {
                let long = &long;
                s.spawn(move || {
                    for j in 0..100 {
                        let message = if (i + j) % 2 == 0 { long.as_str() } else { "short" };
                        write_message(Some(false), None, message);
                    }
                });
            }
            for _ in 0..2 {
                let long = &long;
                s.spawn(move || {
                    for _ in 0..200 {
                        let t = read();
                        assert!(t.message == "short" || t.message == *long, "{}", t.message);
                        assert_eq!(t.disposition, Disposition::DWorking);
                    }
                });
            }
        });
        try_delete();
    }

    #[test]
    fn percentage_messages() {
        assert_eq!(
            make_percentage_progress_message("typechecking", 5, 15, "files", None),
            "typechecking 5/15 files (33.3%)"
        );
        assert_eq!(
            make_percentage_progress_message("op", 999999, 1000000, "", Some("[x]")),
            "op 999999/1000000 (99.9%) [x]"
        );
        assert_eq!(
            make_percentage_progress_message("op", 1, 1, "u", None),
            "op 1/1 u (100.0%)"
        );
        assert_eq!(
            make_percentage_progress_message("op", 1, 0, "u", None),
            "op 1/0 u (inf%)"
        );
    }

    #[test]
    fn disabled() {
        let _serial = serial();
        disable();
        write(None, None, "nowhere");
        try_delete();
        let err = std::panic::catch_unwind(read).unwrap_err();
        assert_eq!(
            err.downcast_ref::<&str>().copied(),
            Some("Server_progress.disable: can't read it")
        );
        assert_eq!(errors_file_path(), None);
    }

    #[test]
    fn errors_file_types() {
        let _serial = serial();
        assert_eq!(show_disposition(&Disposition::DWorking), "DWorking");
        assert_eq!(
            show_completion_reason(&CompletionReason::Complete(telemetry::create())),
            "Complete"
        );
        assert_eq!(
            show_completion_reason(&CompletionReason::Restarted {
                user_message: "u".to_string(),
                log_message: "l".to_string()
            }),
            "Restarted"
        );
        assert_eq!(
            completion_reason_short_description(&CompletionReason::Stopped),
            "hh_server gracefully stopped"
        );
        assert_eq!(
            errors_read::show_open_error(&errors_read::OpenError::OReadError(
                ErrorsFileReadError::Malformed
            )),
            "(Server_progress.ErrorsRead.ORead_error Server_progress.Malformed)"
        );
        assert_eq!(
            errors_read::show_open_error(&errors_read::OpenError::OBuildIdMismatch),
            "Server_progress.ErrorsRead.OBuild_id_mismatch"
        );
        assert_eq!(
            errors_read::show_open_error(&errors_read::OpenError::OKilled(None)),
            "(Server_progress.ErrorsRead.OKilled None)"
        );
        assert_eq!(
            errors_read::open_error_short_description(&errors_read::OpenError::OKilled(None)),
            "hh_server died"
        );
        assert_eq!(
            errors_write::show_write_state(&errors_write::WriteState::Reporting(
                std::fs::File::open("/dev/null").unwrap(),
                7
            )),
            "Reporting[7]"
        );
        let err = std::panic::catch_unwind(|| {
            errors_file::assert_payload_size_ok(
                4_000_000_000,
                errors_file::Direction::Write,
                Some(&errors_file::Message::End {
                    reason: CompletionReason::Stopped,
                    timestamp: 0.,
                    log_message: String::new(),
                }),
            )
        })
        .unwrap_err();
        assert_eq!(
            err.downcast_ref::<String>().unwrap(),
            "Writing error payload with size 4000000000, which is too big. Message is the end sentinel."
        );
        errors_file::assert_payload_size_ok(10, errors_file::Direction::Read, None);

        set_test_root("errors");
        assert!(errors_file_path().unwrap().ends_with(".errors.bin"));
        enable_error_production(false);
        assert_eq!(errors_file_path(), None);
        enable_error_production(true);
    }
}
