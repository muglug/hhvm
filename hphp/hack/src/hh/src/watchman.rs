// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `watchman/watchman.ml` (`Watchman_actual`, with the types of
//! `watchman/watchman_sig.ml`): the Watchman backend of `Server_notifier`
//! (`crate::server_notifier`).
//!
//! This speaks watchman's JSON protocol over its Unix socket, one JSON value
//! per line, as the OCaml does, rather than through the `watchman_client`
//! crate that the design names: that crate names every subscription
//! `sub-[<argv0>]-<n>` (hh's is `hh_type_check_watcher.<pid>`, which other
//! watchman clients see), and has neither `flush-subscriptions` nor the
//! line-at-a-time reads that `get_changes` and `notification_fd` are built
//! on. So the functions below are those of `Watchman_actual`, with the same
//! names, requests, log lines, timeouts and decisions: query mode unless
//! `watchman_subscribe_v2` (`Defer_changes`, deferring on `hg.update` and
//! `meerkat-build`), `since` the last clock with `empty_on_fresh_instance`,
//! a dead instance re-initialised with its prior clock after a backoff (at
//! most 8 times, then `Exit_with Watchman_failed`), a fresh instance found
//! on re-initialisation raising `Watchman_restarted`.
//!
//! The exceptions are the [`Exn`] of a `Result` (PORTING.md, "Exceptions"),
//! inside this module and out of it: the functions that OCaml lets raise
//! (`init`, `get_all_files`, `get_changes`, `get_changes_synchronously`)
//! return them to their callers (`Server_notifier`, then `Server_main`).
//!
//! Not here: `get_changes_since_mergebase`, `get_mergebase` (hg, Meta-only),
//! the `Mocking` and `Testing` modules and `Watchman_mock` (the tests below
//! build their environments directly), the `Process` functor. The
//! `Event_logger` calls are no-ops in the open-source build and are left
//! out.

// ---------------------------------------------------------------------------
// `Watchman_sig.Types`
// ---------------------------------------------------------------------------

use std::io::Read;
use std::io::Write;
use std::os::fd::AsRawFd;
use std::os::fd::RawFd;
use std::os::unix::net::UnixStream;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::MutexGuard;

use crate::exception;
use crate::exit_status;
use crate::hh_json_helpers;
use crate::hh_json_helpers::adhoc_json_helpers as j;
use crate::hh_json_helpers::jget;
use crate::hh_logger;
use crate::path;
use crate::rt::ocaml_printf::sprintf_s;
use crate::rt::ocaml_unix;
use crate::s_map;
use crate::s_set;
use crate::yojson::safe as yojson;

/// `exception Timeout`
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Timeout;

impl std::fmt::Debug for Timeout {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Watchman_sig.Types.Timeout")
    }
}

/// `exception Watchman_error of string`
#[derive(Clone, PartialEq, Eq)]
pub struct WatchmanError(pub String);

impl std::fmt::Debug for WatchmanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Watchman_sig.Types.Watchman_error({})",
            sprintf_s(&self.0)
        )
    }
}

/// `exception Subscription_canceled_by_watchman`
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct SubscriptionCanceledByWatchman;

impl std::fmt::Debug for SubscriptionCanceledByWatchman {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Watchman_sig.Types.Subscription_canceled_by_watchman")
    }
}

/// `exception Watchman_restarted`
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WatchmanRestarted;

impl std::fmt::Debug for WatchmanRestarted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Watchman_sig.Types.Watchman_restarted")
    }
}

/// `subscribe_mode`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SubscribeMode {
    AllChanges,
    DeferChanges,
    ScmAware,
}

/// `type timeout` (named so because the exception `Timeout` has the name).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TimeoutSetting {
    NoTimeout,
    DefaultTimeout,
    ExplicitTimeout(f64),
}

/// `init_settings`
#[derive(Clone, Debug, PartialEq)]
pub struct InitSettings {
    /// None for query mode, otherwise specify subscriptions mode.
    pub subscribe_mode: Option<SubscribeMode>,
    /// Seconds used for init timeout - will be reused for reinitialization.
    pub init_timeout: TimeoutSetting,
    /// See watchman expression terms.
    pub expression_terms: Vec<yojson::T>,
    pub debug_logging: bool,
    pub roots: Vec<path::T>,
    pub sockname: Option<String>,
    pub subscription_prefix: String,
}

/// The message's clock.
pub type Clock = String;

/// `pushed_changes`
#[derive(Clone, Debug, PartialEq)]
pub enum PushedChanges {
    /// State name and metadata. For example: State name: "hg.update".
    StateEnter(String, Option<yojson::T>),
    StateLeave(String, Option<yojson::T>),
    /// `Hg.Rev.t` (a string), the files, the clock.
    ChangedMergeBase(String, s_set::T, Clock),
    FilesChanged(s_set::T),
}

/// `changes`
#[derive(Clone, Debug, PartialEq)]
pub enum Changes {
    WatchmanUnavailable,
    WatchmanPushed(PushedChanges),
    WatchmanSynchronous(Vec<PushedChanges>),
}

// ---------------------------------------------------------------------------
// The exceptions inside this module
// ---------------------------------------------------------------------------

/// The OCaml exceptions that the functions of this module raise and catch.
/// `Debug` prints them as `Printexc.to_string` does.
pub enum Exn {
    Timeout,
    WatchmanError(String),
    SubscriptionCanceledByWatchman,
    WatchmanRestarted,
    /// `Watchman_conn.Read_payload_too_long`
    ReadPayloadTooLong,
    /// `Sys_error msg`: writing to the connection failed.
    SysError(String),
    /// `End_of_file`: watchman closed the connection.
    EndOfFile,
    /// `Unix.Unix_error`, printed.
    UnixError(String),
    /// `Exit_status.Exit_with`
    ExitWith(exit_status::T),
    /// `Yojson.Json_error`
    JsonError(String),
    /// `Hh_json_helpers.AdhocJsonHelpers.Not_found`
    NotFound,
    /// `Failure msg`
    Failure(String),
    /// `Assert_failure`, `Yojson.Safe.Util.Type_error`: printed.
    Other(String),
}

impl std::fmt::Debug for Exn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Exn::Timeout => write!(f, "{:?}", Timeout),
            Exn::WatchmanError(msg) => write!(f, "{:?}", WatchmanError(msg.clone())),
            Exn::SubscriptionCanceledByWatchman => {
                write!(f, "{:?}", SubscriptionCanceledByWatchman)
            }
            Exn::WatchmanRestarted => write!(f, "{:?}", WatchmanRestarted),
            Exn::ReadPayloadTooLong => f.write_str("Watchman.Watchman_conn.Read_payload_too_long"),
            Exn::SysError(msg) => write!(f, "Sys_error({})", sprintf_s(msg)),
            Exn::EndOfFile => f.write_str("End_of_file"),
            Exn::UnixError(s) | Exn::Other(s) => f.write_str(s),
            Exn::ExitWith(t) => write!(f, "Exit_status.Exit_with({})", exit_status::show(t)),
            Exn::JsonError(msg) => write!(f, "Yojson.Json_error({})", sprintf_s(msg)),
            Exn::NotFound => write!(f, "{:?}", j::NotFound),
            Exn::Failure(msg) => write!(f, "Failure({})", sprintf_s(msg)),
        }
    }
}

impl From<j::NotFound> for Exn {
    fn from(_: j::NotFound) -> Self {
        Exn::NotFound
    }
}

/// The message of `Sys_error` for an error of a channel: `strerror`.
fn sys_error_of_io(e: &std::io::Error) -> Exn {
    let msg = e.to_string();
    let msg = match msg.rfind(" (os error ") {
        Some(i) => msg[..i].to_string(),
        None => msg,
    };
    Exn::SysError(msg)
}

/// A printed exception, to log it with `Hh_logger.exception_`.
struct Printed(String);

impl std::fmt::Debug for Printed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// `List.Assoc.find`-style lookups of `Hh_json_helpers.Access`: the first
/// binding of `key` in an object.
fn member<'a>(json: &'a yojson::T, key: &str) -> Option<&'a yojson::T> {
    jget::member(key, json)
}

// ---------------------------------------------------------------------------
// `Testing_common`
// ---------------------------------------------------------------------------

/// `Testing_common.test_settings`
pub fn test_settings() -> InitSettings {
    InitSettings {
        subscribe_mode: Some(SubscribeMode::DeferChanges),
        init_timeout: TimeoutSetting::NoTimeout,
        expression_terms: vec![],
        debug_logging: false,
        roots: vec![path::dummy_path()],
        sockname: None,
        subscription_prefix: "dummy_prefix".to_string(),
    }
}

// ---------------------------------------------------------------------------
// `Helpers`
// ---------------------------------------------------------------------------

pub fn timeout_to_secs(t: TimeoutSetting) -> Option<f64> {
    match t {
        TimeoutSetting::NoTimeout => None,
        TimeoutSetting::DefaultTimeout => Some(1200.),
        TimeoutSetting::ExplicitTimeout(timeout) => Some(timeout),
    }
}

/// Look for common errors in watchman responses
fn assert_no_error(obj: &yojson::T) -> Result<(), Exn> {
    if let Ok(warning) = j::get_string_val("warning", None, obj) {
        hh_logger::log(&format!("Watchman warning: {}\n", warning));
    }
    if let Ok(error) = j::get_string_val("error", None, obj) {
        return Err(Exn::WatchmanError(error));
    }
    match j::get_bool_val("canceled", None, obj) {
        Ok(true) => Err(Exn::SubscriptionCanceledByWatchman),
        Ok(false) | Err(j::NotFound) => Ok(()),
    }
}

pub const MAX_ARRAY_ELT_IN_JSON_LOGGING: isize = 5;

/// `max_array_elt_in_json_logging`
pub fn max_array_elt_in_json_logging() -> isize {
    MAX_ARRAY_ELT_IN_JSON_LOGGING
}

/// `Hh_json_helpers.json_truncate ~max_array_elt_count:5 ~has_changed json`,
/// and whether it changed.
fn truncate_for_logging(json: &yojson::T) -> (yojson::T, bool) {
    let mut has_changed = false;
    let json = hh_json_helpers::json_truncate(
        None,
        None,
        Some(MAX_ARRAY_ELT_IN_JSON_LOGGING),
        None,
        None,
        Some(&mut has_changed),
        json,
    );
    (json, has_changed)
}

/// Verifies that a watchman response is valid JSON and free from common errors
pub fn sanitize_watchman_response(debug_logging: bool, output: &str) -> Result<yojson::T, Exn> {
    if debug_logging {
        hh_logger::info(None, None, &format!("Watchman response: {}", output));
    }
    let response = match yojson::from_string(output) {
        Ok(response) => {
            if !debug_logging {
                // if debug_logging, we've already logged the full watchman
                // response, so skip logging truncated one.
                let (json, has_changed) = truncate_for_logging(&response);
                hh_logger::info(
                    None,
                    None,
                    &format!(
                        "Watchman response: {}{}",
                        if has_changed { "(truncated) " } else { "" },
                        yojson::to_string(&json)
                    ),
                );
            }
            response
        }
        Err(e) => {
            // `Exception.to_string e`: `Printexc.to_string`, the message as an
            // OCaml string literal.
            let e = Exn::JsonError(e.0);
            hh_logger::error(
                None,
                None,
                &format!("Failed to parse string as JSON: {}\n{:?}", output, e),
            );
            return Err(e);
        }
    };
    assert_no_error(&response)?;
    Ok(response)
}

// ---------------------------------------------------------------------------
// `Watchman_conn`
// ---------------------------------------------------------------------------

/// `Buffered_line_reader.t` on a file descriptor, whose reads can be given a
/// deadline (OCaml's `Timeout.with_timeout` around `get_next_line`).
pub struct Reader<R> {
    fd: R,
    buf: Vec<u8>,
}

/// Why [`Reader::get_next_line`] failed.
enum LineError {
    /// The deadline passed (`Timeout.with_timeout`'s `on_timeout`).
    TimedOut,
    Exn(Exn),
}

/// `select [fd] [] [] timeout` (`Sys_utils.select_non_intr`): whether `fd`
/// is readable within `timeout` seconds (a negative timeout waits forever).
/// An error or a hang-up counts as readable, as for `select`.
pub fn fd_is_readable(fd: RawFd, timeout: f64) -> bool {
    let deadline = if timeout < 0. {
        None
    } else {
        Some(std::time::Instant::now() + std::time::Duration::from_secs_f64(timeout))
    };
    loop {
        let ms: libc::c_int = match deadline {
            None => -1,
            Some(d) => {
                let left = d.saturating_duration_since(std::time::Instant::now());
                left.as_millis().min(libc::c_int::MAX as u128) as libc::c_int
            }
        };
        let mut pfd = libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        };
        // SAFETY: one valid `pollfd`.
        let ret = unsafe { libc::poll(&mut pfd, 1, ms) };
        if ret < 0 {
            if std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            return true;
        }
        return ret > 0;
    }
}

impl<R: Read + AsRawFd> Reader<R> {
    fn create(fd: R) -> Self {
        Reader { fd, buf: vec![] }
    }

    pub fn has_buffered_content(&self) -> bool {
        !self.buf.is_empty()
    }

    pub fn get_fd(&self) -> RawFd {
        self.fd.as_raw_fd()
    }

    /// The next line, without its `\n` (and without a `\r` before it:
    /// `Buffered_line_reader.trim_trailing_cr`).
    fn get_next_line(&mut self, deadline: Option<std::time::Instant>) -> Result<String, LineError> {
        loop {
            if let Some(i) = self.buf.iter().position(|&c| c == b'\n') {
                let line: Vec<u8> = self.buf.drain(..=i).collect();
                let mut line = &line[..line.len() - 1];
                if let Some((b'\r', rest)) = line.split_last() {
                    line = rest;
                }
                return Ok(String::from_utf8_lossy(line).into_owned());
            }
            if let Some(d) = deadline {
                let left = d.saturating_duration_since(std::time::Instant::now());
                if left.is_zero() || !fd_is_readable(self.get_fd(), left.as_secs_f64()) {
                    return Err(LineError::TimedOut);
                }
            }
            let mut chunk = [0u8; 65536];
            match self.fd.read(&mut chunk) {
                Ok(0) => return Err(LineError::Exn(Exn::EndOfFile)),
                Ok(n) => self.buf.extend_from_slice(&chunk[..n]),
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => {
                    return Err(LineError::Exn(Exn::UnixError(
                        ocaml_unix::unix_error_to_string(&e, "read", ""),
                    )));
                }
            }
        }
    }
}

/// `Watchman_conn.conn`: the reader and the output channel of the socket.
pub struct Conn {
    reader: Reader<UnixStream>,
    oc: UnixStream,
}

/// Send a request to the watchman process
fn send_request(debug_logging: bool, oc: &mut UnixStream, json: &yojson::T) -> Result<(), Exn> {
    let json_str = yojson::to_string(json);
    if debug_logging {
        // As in OCaml, where the `let ... in` of the `else` branch takes the
        // writes with it: with debug logging, the request is logged but not
        // sent.
        hh_logger::info(None, None, &format!("Watchman request: {}", json_str));
    } else {
        let (json, has_changed) = truncate_for_logging(json);
        hh_logger::info(
            None,
            None,
            &format!(
                "Watchman request: {}{}",
                if has_changed { "(truncated) " } else { "" },
                yojson::to_string(&json)
            ),
        );
        oc.write_all(json_str.as_bytes())
            .and_then(|()| oc.write_all(b"\n"))
            .and_then(|()| oc.flush())
            .map_err(|e| sys_error_of_io(&e))?;
    }
    Ok(())
}

fn has_input<R: Read + AsRawFd>(timeout: TimeoutSetting, reader: &Reader<R>) -> bool {
    if reader.has_buffered_content() {
        true
    } else {
        // Negative means "no timeout" to select
        let timeout = timeout_to_secs(timeout).unwrap_or(-1.);
        fd_is_readable(reader.get_fd(), timeout)
    }
}

fn read_with_timeout<R: Read + AsRawFd>(
    timeout: TimeoutSetting,
    reader: &mut Reader<R>,
) -> Result<String, Exn> {
    let start_t = crate::rt::ocaml_unix::time();
    if !has_input(timeout, reader) {
        Err(Exn::Timeout)
    } else {
        match timeout_to_secs(timeout) {
            None => reader.get_next_line(None).map_err(|e| match e {
                LineError::TimedOut => Exn::ReadPayloadTooLong,
                LineError::Exn(e) => e,
            }),
            Some(timeout) => {
                let remaining = start_t + timeout - crate::rt::ocaml_unix::time();
                let timeout = remaining as i64;
                let timeout = std::cmp::max(timeout, 10);
                let deadline =
                    std::time::Instant::now() + std::time::Duration::from_secs(timeout as u64);
                reader.get_next_line(Some(deadline)).map_err(|e| match e {
                    LineError::TimedOut => Exn::ReadPayloadTooLong,
                    LineError::Exn(e) => e,
                })
            }
        }
    }
}

/// Asks watchman for the path to the socket file
fn get_sockname(timeout: TimeoutSetting) -> Result<String, Exn> {
    // `Timeout.open_process_in Exec_command.Watchman [|"watchman";
    // "get-sockname"; "--no-pretty"|]`
    let mut child = std::process::Command::new("watchman")
        .args(["get-sockname", "--no-pretty"])
        .stdout(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| {
            Exn::UnixError(ocaml_unix::unix_error_to_string(
                &e,
                "create_process",
                "watchman",
            ))
        })?;
    let stdout = child.stdout.take().expect("piped stdout");
    let mut reader = Reader::create(stdout);
    let output = read_with_timeout(timeout, &mut reader);
    let output = match output {
        Ok(output) => output,
        Err(e) => {
            let _ = child.kill();
            let _ = child.wait();
            return Err(e);
        }
    };
    drop(reader);
    match child.wait() {
        Ok(status) if status.code() == Some(0) => {}
        _ => {
            return Err(Exn::Other(
                "File \"hack/src/watchman/watchman.ml\", line 233, characters 4-10: Assertion failed"
                    .to_string(),
            ));
        }
    }
    let json = yojson::from_string(&output).map_err(|e| Exn::JsonError(e.0))?;
    Ok(j::get_string_val("sockname", None, &json)?)
}

/// Opens a connection to the watchman process through the socket
fn open_connection(timeout: TimeoutSetting, sockname: &Option<String>) -> Result<Conn, Exn> {
    let sockname = match sockname {
        Some(sockname) => sockname.clone(),
        None => get_sockname(timeout)?,
    };
    let stream = UnixStream::connect(&sockname)
        .map_err(|e| Exn::UnixError(ocaml_unix::unix_error_to_string(&e, "connect", "")))?;
    let oc = stream
        .try_clone()
        .map_err(|e| Exn::UnixError(ocaml_unix::unix_error_to_string(&e, "dup", "")))?;
    Ok(Conn {
        reader: Reader::create(stream),
        oc,
    })
}

fn close_connection(conn: &Conn) {
    let _ = conn.reader.fd.shutdown(std::net::Shutdown::Both);
}

/// Open a connection to the watchman socket, call the continuation, then
/// close.
fn with_watchman_conn<A>(
    timeout: TimeoutSetting,
    sockname: &Option<String>,
    f: impl FnOnce(&mut Conn) -> Result<A, Exn>,
) -> Result<A, Exn> {
    let mut conn = open_connection(timeout, sockname)?;
    let result = f(&mut conn);
    close_connection(&conn);
    result
}

/// Sends a request to watchman and returns the response. If we don't have a
/// connection, a new connection will be created before the request and
/// destroyed after the response. `timeout` defaults to `Default_timeout`.
pub fn request(
    debug_logging: bool,
    conn: Option<&mut Conn>,
    timeout: Option<TimeoutSetting>,
    sockname: &Option<String>,
    json: &yojson::T,
) -> Result<yojson::T, Exn> {
    let timeout = timeout.unwrap_or(TimeoutSetting::DefaultTimeout);
    match conn {
        None => with_watchman_conn(timeout, sockname, |conn| {
            request(debug_logging, Some(conn), Some(timeout), sockname, json)
        }),
        Some(Conn { reader, oc }) => {
            send_request(debug_logging, oc, json)?;
            let output = read_with_timeout(timeout, reader)?;
            sanitize_watchman_response(debug_logging, &output)
        }
    }
}

pub fn send_request_and_do_not_wait_for_response(
    debug_logging: bool,
    conn: &mut Conn,
    json: &yojson::T,
) -> Result<(), Exn> {
    send_request(debug_logging, &mut conn.oc, json)
}

/// `timeout` defaults to `Explicit_timeout 0.`.
pub fn blocking_read(
    debug_logging: bool,
    timeout: Option<TimeoutSetting>,
    conn: &mut Conn,
) -> Result<Option<yojson::T>, Exn> {
    let timeout = timeout.unwrap_or(TimeoutSetting::ExplicitTimeout(0.));
    let ready = has_input(timeout, &conn.reader);
    if !ready {
        match timeout {
            TimeoutSetting::NoTimeout => Ok(None),
            TimeoutSetting::ExplicitTimeout(timeout) if timeout == 0. => Ok(None),
            _ => Err(Exn::Timeout),
        }
    } else {
        // Use the timeout mechanism to limit maximum time to read payload (cap
        // data size) so we don't freeze if watchman sends an inordinate amount of
        // data, or if it is malformed (i.e. doesn't end in a newline).
        let timeout = 40;
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(timeout);
        let output = match conn.reader.get_next_line(Some(deadline)) {
            Ok(output) => output,
            Err(LineError::TimedOut) => {
                hh_logger::log("Watchman_conn.blocking_read timed out");
                return Err(Exn::ReadPayloadTooLong);
            }
            Err(LineError::Exn(e)) => return Err(e),
        };
        Ok(Some(sanitize_watchman_response(debug_logging, &output)?))
    }
}

// ---------------------------------------------------------------------------
// `Watchman_actual`
// ---------------------------------------------------------------------------

/// This number is totally arbitrary. Just need some cap.
pub const MAX_REINIT_ATTEMPTS: isize = 8;

/// `max_reinit_attempts`
pub fn max_reinit_attempts() -> isize {
    MAX_REINIT_ATTEMPTS
}

/// Triggers watchman to flush buffered updates on this subscription.
/// See watchman/docs/cmd/flush-subscriptions.html
pub const FLUSH_SUBSCRIPTIONS_CMD: &str = "cmd-flush-subscriptions";

/// `flush_subscriptions_cmd`
pub fn flush_subscriptions_cmd() -> &'static str {
    FLUSH_SUBSCRIPTIONS_CMD
}

/// `dead_env`
#[derive(Clone, Debug)]
pub struct DeadEnv {
    /// Will reuse original settings to reinitializing watchman subscription.
    pub prior_settings: InitSettings,
    pub reinit_attempts: isize,
    pub dead_since: f64,
    pub prior_clockspec: String,
}

/// `env`. OCaml's record is mutable (`clockspec`) and shared: the
/// environment `Server_notifier` keeps for its indexer is the one its
/// instance starts with, so both see the clock that the other sets. Here it
/// is an `Arc`.
#[derive(Clone)]
pub struct Env(Arc<EnvInner>);

pub struct EnvInner {
    /// See https://facebook.github.io/watchman/docs/clockspec.html
    /// This is also used to reliably detect a crashed watchman. Watchman has a
    /// facility to detect watchman process crashes between two "since" queries.
    /// See also assert_no_fresh_instance
    clockspec: Mutex<String>,
    /// `None` once closed.
    conn: Mutex<Option<Conn>>,
    /// The file descriptor of the connection (`Buffered_line_reader.get_fd`),
    /// readable without waiting for a request that holds the connection.
    reader_fd: RawFd,
    settings: InitSettings,
    subscription: String,
    watch_root: String,
    watched_path_expression_terms: Option<yojson::T>,
}

fn lock<A>(m: &Mutex<A>) -> MutexGuard<'_, A> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

impl Env {
    fn clockspec(&self) -> String {
        lock(&self.0.clockspec).clone()
    }

    fn set_clockspec(&self, clockspec: String) {
        *lock(&self.0.clockspec) = clockspec
    }

    /// Runs `f` on the connection (`Sys_error "Bad file descriptor"` once it
    /// is closed).
    fn with_conn<A>(&self, f: impl FnOnce(&mut Conn) -> Result<A, Exn>) -> Result<A, Exn> {
        let mut conn = lock(&self.0.conn);
        match conn.as_mut() {
            None => Err(Exn::SysError("Bad file descriptor".to_string())),
            Some(conn) => f(conn),
        }
    }

    pub fn settings(&self) -> &InitSettings {
        &self.0.settings
    }

    pub fn subscription(&self) -> &str {
        &self.0.subscription
    }

    pub fn watch_root(&self) -> &str {
        &self.0.watch_root
    }
}

pub fn dead_env_from_alive(env: &Env) -> DeadEnv {
    DeadEnv {
        prior_settings: env.0.settings.clone(),
        dead_since: crate::rt::ocaml_unix::time(),
        reinit_attempts: 0,
        // When we start a new watchman connection, we continue to use the prior
        // clockspec. If the same watchman server is still alive, then all is
        // good. If not, the clockspec allows us to detect whether a new watchman
        // server had to be started. See also "is_fresh_instance" on watchman's
        // "since" response.
        prior_clockspec: env.clockspec(),
    }
}

/// `watchman_instance`
#[derive(Clone)]
pub enum WatchmanInstance {
    /// Indicates a dead watchman instance (most likely due to chef upgrading,
    /// reconfiguration, or a user terminating watchman, or a timeout reading
    /// from the connection) detected by, for example, a pipe error or a timeout.
    WatchmanDead(DeadEnv),
    WatchmanAlive(Env),
}

// JSON methods.

pub fn clock(root: &str) -> yojson::T {
    j::strlist(&["clock", root])
}

/// `watch_command`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WatchCommand {
    Subscribe,
    Query,
}

/// Conjunction of extra_expressions and env.settings.expression_terms.
pub fn request_json(
    extra_kv: Option<Vec<(String, yojson::T)>>,
    extra_expressions: Option<Vec<yojson::T>>,
    watchman_command: WatchCommand,
    env: &Env,
) -> Result<yojson::T, Exn> {
    let extra_kv = extra_kv.unwrap_or_default();
    let extra_expressions = extra_expressions.unwrap_or_default();
    let mut header = vec![
        yojson::T::String(
            match watchman_command {
                WatchCommand::Subscribe => "subscribe",
                WatchCommand::Query => "query",
            }
            .to_string(),
        ),
        yojson::T::String(env.0.watch_root.clone()),
    ];
    match watchman_command {
        WatchCommand::Subscribe => header.push(yojson::T::String(env.0.subscription.clone())),
        WatchCommand::Query => {}
    }
    let mut expressions = extra_expressions;
    expressions.extend(env.0.settings.expression_terms.iter().cloned());
    let expressions = match &env.0.watched_path_expression_terms {
        Some(terms) => {
            let mut l = vec![terms.clone()];
            l.extend(expressions);
            l
        }
        None => expressions,
    };
    if expressions.is_empty() {
        return Err(Exn::Other(
            "File \"hack/src/watchman/watchman.ml\", line 436, characters 6-12: Assertion failed"
                .to_string(),
        ));
    }
    let mut kv = extra_kv;
    kv.push(("fields".to_string(), j::strlist(&["name"])));
    // Watchman doesn't allow an empty allof expression. But expressions is never empty
    kv.push(("expression".to_string(), j::pred("allof", expressions)));
    let mut request = header;
    request.push(yojson::T::Assoc(kv));
    Ok(yojson::T::List(request))
}

pub fn get_changes_since_mergebase_query(env: &Env) -> Result<yojson::T, Exn> {
    let extra_kv = vec![(
        "since".to_string(),
        yojson::T::Assoc(vec![(
            "scm".to_string(),
            yojson::T::Assoc(vec![(
                "mergebase-with".to_string(),
                yojson::T::String("master".to_string()),
            )]),
        )]),
    )];
    request_json(Some(extra_kv), None, WatchCommand::Query, env)
}

pub fn since_query(env: &Env) -> Result<yojson::T, Exn> {
    request_json(
        Some(vec![
            ("since".to_string(), yojson::T::String(env.clockspec())),
            ("empty_on_fresh_instance".to_string(), yojson::T::Bool(true)),
        ]),
        None,
        WatchCommand::Query,
        env,
    )
}

pub fn subscribe(mode: SubscribeMode, env: &Env) -> Result<yojson::T, Exn> {
    let (since, mode) = match mode {
        SubscribeMode::AllChanges => (yojson::T::String(env.clockspec()), vec![]),
        SubscribeMode::DeferChanges => (
            yojson::T::String(env.clockspec()),
            vec![(
                "defer".to_string(),
                j::strlist(&[crate::hg_states::UPDATE, "meerkat-build"]),
            )],
        ),
        SubscribeMode::ScmAware => {
            hh_logger::log("Making Scm_aware subscription");
            let scm = yojson::T::Assoc(vec![(
                "mergebase-with".to_string(),
                yojson::T::String("master".to_string()),
            )]);
            let since = yojson::T::Assoc(vec![
                ("scm".to_string(), scm),
                (
                    "drop".to_string(),
                    j::strlist(&[crate::hg_states::UPDATE, "meerkat-build"]),
                ),
            ]);
            (since, vec![])
        }
    };
    let mut extra_kv = vec![("since".to_string(), since)];
    extra_kv.extend(mode);
    extra_kv.push(("empty_on_fresh_instance".to_string(), yojson::T::Bool(true)));
    request_json(Some(extra_kv), None, WatchCommand::Subscribe, env)
}

pub fn watch_project(root: &str) -> yojson::T {
    j::strlist(&["watch-project", root])
}

/// See https://facebook.github.io/watchman/docs/cmd/version.html
/// `optional` defaults to `[]`.
pub fn capability_check(optional: Option<&[&str]>, required: &[&str]) -> yojson::T {
    let optional = optional.unwrap_or(&[]);
    yojson::T::List(vec![
        yojson::T::String("version".to_string()),
        yojson::T::Assoc(vec![
            ("optional".to_string(), j::strlist(optional)),
            ("required".to_string(), j::strlist(required)),
        ]),
    ])
}

/// We filter all responses from `get_changes` through this. This is to detect
/// Watchman server crashes.
///
/// See also Watchman docs on "since" query parameter.
pub fn assert_no_fresh_instance(obj: &yojson::T) -> Result<(), Exn> {
    if let Some(yojson::T::Bool(is_fresh)) = member(obj, "is_fresh_instance") {
        if *is_fresh {
            hh_logger::log("Watchman server is fresh instance. Exiting.");
            return Err(Exn::ExitWith(exit_status::T::WatchmanFreshInstance));
        }
    }
    Ok(())
}

// Initialization, reinitialization, and crash-tracking.

pub fn with_crash_record_exn<A>(
    source: &str,
    f: impl FnOnce() -> Result<A, Exn>,
) -> Result<A, Exn> {
    match f() {
        Ok(a) => Ok(a),
        Err(exn) => {
            let e = exception::wrap(Printed(format!("{:?}", exn)));
            hh_logger::exception_(Some(&format!("Watchman {}: ", source)), &e);
            Err(exn)
        }
    }
}

pub fn with_crash_record_opt<A>(
    source: &str,
    f: impl FnOnce() -> Result<A, Exn>,
) -> Result<Option<A>, Exn> {
    match with_crash_record_exn(source, f) {
        Ok(a) => Ok(Some(a)),
        // Avoid swallowing these
        Err(exn @ (Exn::ExitWith(_) | Exn::WatchmanRestarted)) => Err(exn),
        Err(_) => Ok(None),
    }
}

pub fn has_capability(name: &str, capabilities: &yojson::T) -> bool {
    // Projects down from the boolean error monad into booleans.
    // Error states go to false, values are projected directly.
    match member(capabilities, "capabilities") {
        Some(caps @ yojson::T::Assoc(_)) => {
            matches!(member(caps, name), Some(yojson::T::Bool(true)))
        }
        _ => false,
    }
}

/// When we re-init our connection to Watchman, we use the old clockspec to get all the changes
/// since our last response. However, if Watchman has restarted and the old clockspec pre-dates
/// the new Watchman, then we may miss updates. It is important for Flow and Hack to restart
/// in that case.
///
/// Unfortunately, the response to "subscribe" doesn't have the "is_fresh_instance" field. So
/// we'll instead send a small "query" request. It should always return 0 files, but it should
/// tell us whether the Watchman service has restarted since clockspec.
pub fn assert_watchman_has_not_restarted_since(
    debug_logging: bool,
    conn: &mut Conn,
    sockname: &Option<String>,
    watch_root: &str,
    clockspec: &str,
) -> Result<(), Exn> {
    let hard_to_match_name = "irrelevant.potato";
    let query = yojson::T::List(vec![
        yojson::T::String("query".to_string()),
        yojson::T::String(watch_root.to_string()),
        yojson::T::Assoc(vec![
            (
                "since".to_string(),
                yojson::T::String(clockspec.to_string()),
            ),
            ("empty_on_fresh_instance".to_string(), yojson::T::Bool(true)),
            (
                "expression".to_string(),
                yojson::T::List(vec![
                    yojson::T::String("name".to_string()),
                    yojson::T::String(hard_to_match_name.to_string()),
                ]),
            ),
        ]),
    ]);
    let response = request(debug_logging, Some(conn), None, sockname, &query)?;
    match jget::bool_opt(Some(&response), "is_fresh_instance") {
        Some(false) => Ok(()),
        Some(true) => {
            hh_logger::error(
                None,
                None,
                "Watchman server restarted so we may have missed some updates",
            );
            Err(Exn::WatchmanRestarted)
        }
        None => {
            // The response to this query **always** should include the `is_fresh_instance` boolean
            // property. If it is missing then something has gone wrong with Watchman. Since we can't
            // prove that Watchman has not restarted, we must treat this as an error.
            hh_logger::error(
                None,
                None,
                &format!(
                    "Invalid Watchman response to `empty_on_fresh_instance` query:\n{}",
                    // unsorted: watchman query, consumed by external tool
                    crate::yojson::safe::pretty_to_string(&response)
                ),
            );
            Err(Exn::ExitWith(exit_status::T::WatchmanFailed))
        }
    }
}

/// Given a list of terms [a;b;c], this constructs [ ["dirname","relative_path"]; a; b; c]
/// It's used because if the watchman root is /fbsource but we want to watch /fbsource/www,
/// then watchman needs us to pass "/fbsource" as the watched-root and then use our
/// own dirname query to restrict to the directory we want.
///
/// CARE: watchman is fast with [dirname,relative_path] and [alloff, [dirname, relative_path]]
/// but it's slow with [anyof, [dirname,relative_path], [name,relative_path]]. That's because
/// watchman indexes on dirname and the first two queries can be done fast, but the third
/// query would require an item-by-item search over every item in /fbsource to see if it
/// matches the "name" predicate.
///
/// This function doesn't do anything if relative_path is empty or there are no terms, then
/// we don't add the restrictions (since it wouldn't be needed).
pub fn prepend_relative_path_of_directory(
    relative_path: &str,
    terms: Option<Vec<yojson::T>>,
) -> Option<Vec<yojson::T>> {
    match terms {
        None => None,
        // If we're watching the watch root directory, then there's no point in specifying a list of
        // files and directories to watch. We're already subscribed to any change in this watch root
        // anyway
        Some(_) if relative_path.is_empty() => None,
        Some(terms) => {
            // So lets say we're being told to watch foo/bar. Is foo/bar a directory? Is it a file? If it
            // is a file now, might it become a directory later? I'm not aware of aterm which will watch for either a file or a directory, so let's add two terms
            let mut l = vec![j::strlist(&["dirname", relative_path])];
            l.extend(terms);
            Some(l)
        }
    }
}

pub fn re_init(
    prior_clockspec: Option<String>,
    settings: &InitSettings,
) -> Result<Option<Env>, Exn> {
    let InitSettings {
        init_timeout,
        subscribe_mode,
        expression_terms,
        debug_logging,
        roots,
        sockname,
        subscription_prefix,
    } = settings.clone();
    with_crash_record_opt("init", || {
        let mut conn = open_connection(init_timeout, &sockname)?;
        let result = (|| {
            let capabilities = request(
                debug_logging,
                Some(&mut conn),
                Some(TimeoutSetting::DefaultTimeout),
                &sockname,
                &capability_check(Some(&[FLUSH_SUBSCRIPTIONS_CMD]), &["relative_root"]),
            )?;
            let supports_flush = has_capability(FLUSH_SUBSCRIPTIONS_CMD, &capabilities);
            // Disable subscribe if Watchman flush feature isn't supported.
            let subscribe_mode = if supports_flush { subscribe_mode } else { None };
            let mut terms: Option<Vec<yojson::T>> = Some(vec![]);
            let mut watch_roots = s_set::T::new();
            let mut failed_paths = s_set::T::new();
            for path in &roots {
                // Watch this root. If the path doesn't exist, watch_project will throw. In that case catch
                // the error and continue for now.
                let response = request(
                    debug_logging,
                    Some(&mut conn),
                    None,
                    &sockname,
                    &watch_project(&path::to_string(path)),
                )
                .ok();
                match response {
                    None => {
                        failed_paths.insert(path::to_string(path));
                    }
                    Some(response) => {
                        let watch_root = j::get_string_val("watch", None, &response)?;
                        let relative_path =
                            j::get_string_val("relative_path", Some(String::new()), &response)?;
                        terms = prepend_relative_path_of_directory(&relative_path, terms);
                        watch_roots.insert(watch_root);
                    }
                }
            }
            // The failed_paths are likely includes which don't exist on the filesystem, so watch_project
            // returned an error. Let's do a best effort attempt to infer the watch root and relative
            // path for each bad include
            for path in failed_paths.iter() {
                match watch_roots
                    .iter()
                    .find(|root| path.starts_with(root.as_str()))
                {
                    None => {
                        return Err(Exn::Failure(format!(
                            "Cannot deduce watch root for path {}",
                            path
                        )));
                    }
                    Some(root) => {
                        let relative_path = crate::string_utils::lstrip(crate::string_utils::lstrip(path, root), "/");
                        terms = prepend_relative_path_of_directory(relative_path, terms);
                    }
                }
            }
            // All of our watched paths should have the same watch root. Let's assert that
            let watch_root = match watch_roots.len() {
                0 => {
                    return Err(Exn::Failure(
                        "Cannot run watchman with fewer than 1 root".to_string(),
                    ));
                }
                1 => watch_roots.iter().next().unwrap().clone(),
                n => {
                    return Err(Exn::Failure(format!(
                        "Can't watch paths across multiple Watchman watch_roots. Found {} watch_roots",
                        n
                    )));
                }
            };
            // If we don't have a prior clockspec, grab the current clock
            let clockspec = match &prior_clockspec {
                Some(clockspec) => {
                    assert_watchman_has_not_restarted_since(
                        debug_logging,
                        &mut conn,
                        &sockname,
                        &watch_root,
                        clockspec,
                    )?;
                    clockspec.clone()
                }
                None => {
                    let response = request(
                        debug_logging,
                        Some(&mut conn),
                        None,
                        &sockname,
                        &clock(&watch_root),
                    )?;
                    j::get_string_val("clock", None, &response)?
                }
            };
            let watched_path_expression_terms = terms.map(|terms| j::pred("anyof", terms));
            Ok((
                subscribe_mode,
                watch_root,
                watched_path_expression_terms,
                clockspec,
            ))
        })();
        let (subscribe_mode, watch_root, watched_path_expression_terms, clockspec) = match result {
            Ok(x) => x,
            Err(e) => {
                // OCaml leaves the connection to the garbage collector.
                close_connection(&conn);
                return Err(e);
            }
        };
        let reader_fd = conn.reader.get_fd();
        let env = Env(Arc::new(EnvInner {
            settings: InitSettings {
                init_timeout,
                debug_logging,
                subscribe_mode,
                expression_terms: expression_terms.clone(),
                roots: roots.clone(),
                sockname: sockname.clone(),
                subscription_prefix: subscription_prefix.clone(),
            },
            conn: Mutex::new(Some(conn)),
            reader_fd,
            watch_root,
            watched_path_expression_terms,
            clockspec: Mutex::new(clockspec),
            subscription: format!("{}.{}", subscription_prefix, ocaml_unix::getpid()),
        }));
        match subscribe_mode {
            None => {}
            Some(mode) => {
                let req = subscribe(mode, &env)?;
                let _response: yojson::T = env
                    .with_conn(|conn| request(debug_logging, Some(conn), None, &sockname, &req))?;
            }
        }
        Ok(env)
    })
}

/// `init ?since_clockspec settings ()`
pub fn init(since_clockspec: Option<String>, settings: &InitSettings) -> Result<Option<Env>, Exn> {
    let prior_clockspec = since_clockspec;
    re_init(prior_clockspec, settings)
}

pub fn extract_file_names(env: &Env, json: &yojson::T) -> Result<Vec<String>, Exn> {
    let files = match j::get_array_val("files", None, json) {
        Ok(files) => files,
        // When an hg.update happens, it shows up in the watchman subscription
        // as a notification with no files key present.
        Err(j::NotFound) => vec![],
    };
    files
        .iter()
        .map(|json| match json {
            yojson::T::String(s) => Ok(crate::rt::ocaml_filename::concat(&env.0.watch_root, s)),
            json => Err(Exn::Other(format!(
                "Yojson.Safe.Util.Type_error(\"Expected string, got {}\", _)",
                crate::yojson::safe::util::typeof_(json)
            ))),
        })
        .collect()
}

pub fn within_backoff_time(attempts: isize, time: f64) -> bool {
    let offset = 4.0 * 2.0f64.powi(if attempts > 3 { 3 } else { attempts as i32 });
    crate::rt::ocaml_unix::time() >= time + offset
}

pub fn maybe_restart_instance(instance: WatchmanInstance) -> Result<WatchmanInstance, Exn> {
    match instance {
        WatchmanInstance::WatchmanAlive(_) => Ok(instance),
        WatchmanInstance::WatchmanDead(ref dead_env) => {
            if dead_env.reinit_attempts >= MAX_REINIT_ATTEMPTS {
                hh_logger::log("Ran out of watchman reinit attempts. Exiting.");
                Err(Exn::ExitWith(exit_status::T::WatchmanFailed))
            } else if within_backoff_time(dead_env.reinit_attempts, dead_env.dead_since) {
                hh_logger::log("Attemping to reestablish watchman subscription");
                match re_init(
                    Some(dead_env.prior_clockspec.clone()),
                    &dead_env.prior_settings,
                )? {
                    None => {
                        hh_logger::log("Reestablishing watchman subscription failed.");
                        Ok(WatchmanInstance::WatchmanDead(DeadEnv {
                            reinit_attempts: dead_env.reinit_attempts + 1,
                            ..dead_env.clone()
                        }))
                    }
                    Some(env) => {
                        hh_logger::log("Watchman connection reestablished.");
                        Ok(WatchmanInstance::WatchmanAlive(env))
                    }
                }
            } else {
                Ok(instance)
            }
        }
    }
}

pub fn close(env: &Env) {
    let conn = lock(&env.0.conn).take();
    if let Some(conn) = conn {
        close_connection(&conn)
    }
}

pub fn close_channel_on_instance(env: &Env) -> (WatchmanInstance, Changes) {
    close(env);
    (
        WatchmanInstance::WatchmanDead(dead_env_from_alive(env)),
        Changes::WatchmanUnavailable,
    )
}

pub fn with_instance<A>(
    instance: WatchmanInstance,
    try_to_restart: bool,
    on_alive: impl FnOnce(Env) -> Result<A, Exn>,
    on_dead: impl FnOnce(DeadEnv) -> Result<A, Exn>,
) -> Result<A, Exn> {
    let instance = if try_to_restart {
        maybe_restart_instance(instance)?
    } else {
        instance
    };
    match instance {
        WatchmanInstance::WatchmanDead(dead_env) => on_dead(dead_env),
        WatchmanInstance::WatchmanAlive(env) => on_alive(env),
    }
}

/// Calls f on the instance, maybe restarting it if its dead and maybe
/// reverting it to a dead state if things go south. For example, if watchman
/// shuts the connection on us, or shuts down, or crashes, we revert to a dead
/// instance, upon which a restart will be attempted down the road.
/// Alternatively, we also proactively revert to a dead instance if it appears
/// to be unresponsive (Timeout), and if reading the payload from it is
/// taking too long.
pub fn call_on_instance(
    instance: WatchmanInstance,
    source: &str,
    f: impl FnOnce(&Env) -> Result<Changes, Exn>,
) -> Result<(WatchmanInstance, Changes), Exn> {
    let on_dead = |dead_env| {
        Ok((
            WatchmanInstance::WatchmanDead(dead_env),
            Changes::WatchmanUnavailable,
        ))
    };
    let on_alive = |env: Env| match with_crash_record_exn(source, || f(&env)) {
        Ok(result) => Ok((WatchmanInstance::WatchmanAlive(env), result)),
        Err(Exn::SysError(msg)) if msg == "Broken pipe" => {
            hh_logger::log("Watchman Pipe broken.");
            Ok(close_channel_on_instance(&env))
        }
        Err(Exn::SysError(msg)) if msg == "Connection reset by peer" => {
            hh_logger::log("Watchman connection reset by peer.");
            Ok(close_channel_on_instance(&env))
        }
        Err(Exn::SysError(msg)) if msg == "Bad file descriptor" => {
            // This happens when watchman is tearing itself down after we
            // retrieved a sock address and connected to the sock address. That's
            // because Unix.open_connection doesn't
            // error even when the sock address is no longer valid and actually -
            // it returns a channel that will error at some later time when you
            // actually try to do anything with it (write to it, or even get the
            // file descriptor of it). I'm pretty sure we don't need to close the
            // channel when that happens since we never had a useable channel
            // to start with.
            hh_logger::log("Watchman bad file descriptor.");
            Ok((
                WatchmanInstance::WatchmanDead(dead_env_from_alive(&env)),
                Changes::WatchmanUnavailable,
            ))
        }
        Err(Exn::EndOfFile) => {
            hh_logger::log("Watchman connection End_of_file. Closing channel");
            Ok(close_channel_on_instance(&env))
        }
        Err(Exn::ReadPayloadTooLong) => {
            hh_logger::log("Watchman reading payload too long. Closing channel");
            Ok(close_channel_on_instance(&env))
        }
        Err(Exn::Timeout) => {
            hh_logger::log("Watchman reading Timeout. Closing channel");
            Ok(close_channel_on_instance(&env))
        }
        Err(Exn::WatchmanError(msg)) => {
            hh_logger::log(&format!("Watchman error: {}. Closing channel", msg));
            Ok(close_channel_on_instance(&env))
        }
        Err(_) => Err(Exn::ExitWith(exit_status::T::WatchmanFailed)),
    };
    with_instance(instance, true, on_alive, on_dead)
}

/// This is a large >50MB payload, which could take longer than 2 minutes for
/// Watchman to generate and push down the channel.
pub fn get_all_files(env: &Env) -> Result<Vec<String>, Exn> {
    let result = with_crash_record_exn("get_all_files", || {
        let response = request(
            env.0.settings.debug_logging,
            None,
            Some(TimeoutSetting::DefaultTimeout),
            &env.0.settings.sockname,
            &request_json(
                None,
                Some(vec![yojson::T::String("exists".to_string())]),
                WatchCommand::Query,
                env,
            )?,
        )?;
        // WARNING:
        // Updating the clockspec to the one we got from the response above has the
        // following consequences, *but only if `subscribe_mode` is None*.
        // If any file changes happened in between the last call to `get_changes`
        // or `get_changes_synchronously` and the request above, they are
        // effectively discarded and will never be reported by subsequent calls
        // to these two functions!
        env.set_clockspec(j::get_string_val("clock", None, &response)?);
        extract_file_names(env, &response)
    });
    match result {
        Ok(files) => Ok(files),
        Err(_) => Err(Exn::ExitWith(exit_status::T::WatchmanFailed)),
    }
}

/// `module RepoStates`
pub mod repo_states {
    use std::sync::Mutex;

    use crate::s_map;

    pub type State = String;

    /// `t`
    #[derive(Clone)]
    struct T {
        /// Maps state name to [Unix.gettimeofday] timestamp of last leave
        past_states: s_map::T<f64>,
        current_states: Vec<State>,
    }

    static STATES: Mutex<Option<T>> = Mutex::new(None);

    fn with_states<A>(f: impl FnOnce(&mut T) -> A) -> A {
        let mut states = super::lock(&STATES);
        let states = states.get_or_insert_with(|| T {
            past_states: s_map::T::new(),
            current_states: vec![],
        });
        f(states)
    }

    pub fn enter(state: State) {
        with_states(|states| states.current_states.insert(0, state))
    }

    fn remove_first(list: &[String], elt: &str) -> Vec<String> {
        let mut list = list.to_vec();
        if let Some(i) = list.iter().position(|hd| hd == elt) {
            list.remove(i);
        }
        list
    }

    pub fn leave(state: State) {
        with_states(|states| {
            let current_states = remove_first(&states.current_states, &state);
            let past_states = states
                .past_states
                .update(state, crate::rt::ocaml_unix::gettimeofday());
            *states = T {
                current_states,
                past_states,
            };
        })
    }

    /// Returns (current_states, past_states).
    /// [past_states] maps each state name to the [Unix.gettimeofday] timestamp
    /// of the last time it was left.
    pub fn get() -> (Vec<String>, s_map::T<f64>) {
        with_states(|states| (states.current_states.clone(), states.past_states.clone()))
    }
}

/// The state change of `make_state_change_response`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateChange {
    Enter,
    Leave,
}

pub fn make_state_change_response(
    state: StateChange,
    name: String,
    data: &yojson::T,
) -> PushedChanges {
    let metadata = j::try_get_val("metadata", data).ok().flatten().cloned();
    match state {
        StateChange::Enter => {
            repo_states::enter(name.clone());
            PushedChanges::StateEnter(name, metadata)
        }
        StateChange::Leave => {
            repo_states::leave(name.clone());
            PushedChanges::StateLeave(name, metadata)
        }
    }
}

/// returns (data.clock.scm.mergebase, data.since?.scm.mergebase).
/// The watchman docs explain: "The since field holds the fat clock that was returned
/// in the clock field from the prior subscription update. It is present as a convenience
/// for you; you can compare the mergebase fields between the two to determine that the
/// merge base changed in this update."
/// Edge cases: (1) when we send the first subscribe request, we get back an answer that
/// lacks the since property entirely, (2) the next thing we hear has an empty since.mergebase,
/// (3) the next thing we hear has a full since.mergebase.
pub fn extract_mergebase(data: &yojson::T) -> Option<(String, Option<Option<String>>)> {
    fn get_obj<'a>(json: &'a yojson::T, key: &str) -> Option<&'a yojson::T> {
        match member(json, key) {
            Some(v @ yojson::T::Assoc(_)) => Some(v),
            _ => None,
        }
    }
    fn get_string(json: &yojson::T, key: &str) -> Option<String> {
        match member(json, key) {
            Some(yojson::T::String(s)) => Some(s.clone()),
            _ => None,
        }
    }
    let mergebase = get_obj(data, "clock")
        .and_then(|c| get_obj(c, "scm"))
        .and_then(|scm| get_string(scm, "mergebase"))?;
    let since_mergebase = get_obj(data, "since")
        .and_then(|s| get_obj(s, "scm"))
        .and_then(|scm| get_string(scm, "mergebase"));
    // `Hg.Rev.of_string_check_empty`
    Some((
        mergebase,
        since_mergebase.map(|s| if s.is_empty() { None } else { Some(s) }),
    ))
}

/// watchman's data.clock property is either a slim-clock "string", or a fat-clock "{clock, scm}".
/// This function extracts either.
pub fn extract_clock(data: &yojson::T) -> Result<String, Exn> {
    let fat = match member(data, "clock") {
        Some(c @ yojson::T::Assoc(_)) => match member(c, "clock") {
            Some(yojson::T::String(clock)) => Some(clock.clone()),
            _ => None,
        },
        _ => None,
    };
    let slim = match member(data, "clock") {
        Some(yojson::T::String(clock)) => Some(clock.clone()),
        _ => None,
    };
    match (fat, slim) {
        (Some(clock), _) | (_, Some(clock)) => Ok(clock),
        _ => Err(Exn::Failure("watchman response lacks clock".to_string())),
    }
}

pub fn transform_asynchronous_get_changes_response(
    env: &Env,
    data: Option<&yojson::T>,
) -> Result<PushedChanges, Exn> {
    match data {
        None => Ok(PushedChanges::FilesChanged(s_set::T::new())),
        Some(data) => {
            let clock = extract_clock(data)?;
            env.set_clockspec(clock.clone());
            let files: s_set::T = extract_file_names(env, data)?.into_iter().collect();
            match extract_mergebase(data) {
                Some((mergebase, Some(None))) => {
                    Ok(PushedChanges::ChangedMergeBase(mergebase, files, clock))
                }
                Some((mergebase, Some(Some(since_mergebase)))) if mergebase != since_mergebase => {
                    Ok(PushedChanges::ChangedMergeBase(mergebase, files, clock))
                }
                _ => {
                    assert_no_fresh_instance(data)?;
                    match j::get_string_val("state-enter", None, data) {
                        Ok(name) => Ok(make_state_change_response(StateChange::Enter, name, data)),
                        Err(j::NotFound) => match j::get_string_val("state-leave", None, data) {
                            Ok(name) => {
                                Ok(make_state_change_response(StateChange::Leave, name, data))
                            }
                            Err(j::NotFound) => Ok(PushedChanges::FilesChanged(files)),
                        },
                    }
                }
            }
        }
    }
}

pub fn get_clock(instance: &WatchmanInstance) -> Clock {
    match instance {
        WatchmanInstance::WatchmanAlive(env) => env.clockspec(),
        WatchmanInstance::WatchmanDead(DeadEnv {
            prior_clockspec, ..
        }) => prior_clockspec.clone(),
    }
}

/// `get_changes ?deadline instance`
pub fn get_changes(
    deadline: Option<f64>,
    instance: WatchmanInstance,
) -> Result<(WatchmanInstance, Changes), Exn> {
    let result = call_on_instance(instance, "get_changes", |env| {
        let timeout = deadline.map(|deadline| {
            let timeout = deadline - crate::rt::ocaml_unix::time();
            TimeoutSetting::ExplicitTimeout(timeout.max(0.0))
        });
        let debug_logging = env.0.settings.debug_logging;
        let sockname = &env.0.settings.sockname;
        if env.0.settings.subscribe_mode.is_some() {
            let response = env.with_conn(|conn| blocking_read(debug_logging, timeout, conn))?;
            let result = transform_asynchronous_get_changes_response(env, response.as_ref())?;
            Ok(Changes::WatchmanPushed(result))
        } else {
            let query = since_query(env)?;
            let response = env
                .with_conn(|conn| request(debug_logging, Some(conn), timeout, sockname, &query))?;
            let changes = transform_asynchronous_get_changes_response(env, Some(&response))?;
            Ok(Changes::WatchmanSynchronous(vec![changes]))
        }
    });
    result
}

pub fn flush_request(timeout: isize, watch_root: &str) -> yojson::T {
    let directive = yojson::T::Assoc(vec![(
        // Watchman expects timeout milliseconds.
        "sync_timeout".to_string(),
        yojson::T::Intlit((timeout * 1000).to_string()),
    )]);
    yojson::T::List(vec![
        yojson::T::String("flush-subscriptions".to_string()),
        yojson::T::String(watch_root.to_string()),
        directive,
    ])
}

/// `poll_until_sync ~deadline env`: the changes, the last one first.
pub fn poll_until_sync(deadline: f64, env: &Env) -> Result<Vec<PushedChanges>, Exn> {
    // An element that is not a string is the `assert false` of
    // `Hh_json_helpers.get_string_exn`, an exception that `call_on_instance`
    // turns into `Exit_with Watchman_failed`.
    let is_finished_flush_response = |json: Option<&yojson::T>| -> Result<bool, Exn> {
        match json {
            None => Ok(false),
            Some(json) => {
                let contains = |key: &str| -> Result<bool, Exn> {
                    match member(json, key) {
                        // `List.exists`: stops at the first match.
                        Some(yojson::T::List(vs)) => {
                            for v in vs {
                                match v {
                                    yojson::T::String(s) => {
                                        if s == &env.0.subscription {
                                            return Ok(true);
                                        }
                                    }
                                    _ => {
                                        return Err(Exn::Other(
                                            "File \"hack/src/utils/hh_json/hh_json_helpers.ml\", line 248, characters 9-15: Assertion failed"
                                                .to_string(),
                                        ));
                                    }
                                }
                            }
                            Ok(false)
                        }
                        _ => Ok(false),
                    }
                };
                // `Lazy.force is_synced || Lazy.force is_not_needed`
                Ok(contains("synced")? || contains("no_sync_needed")?)
            }
        }
    };
    let mut acc = vec![];
    loop {
        let timeout = {
            let timeout = deadline - crate::rt::ocaml_unix::time();
            if timeout <= 0.0 {
                return Err(Exn::Timeout);
            } else {
                TimeoutSetting::ExplicitTimeout(timeout)
            }
        };
        let debug_logging = env.0.settings.debug_logging;
        let json = env.with_conn(|conn| blocking_read(debug_logging, Some(timeout), conn))?;
        if is_finished_flush_response(json.as_ref())? {
            return Ok(acc);
        }
        match json {
            None => {}
            Some(json) => {
                let result = transform_asynchronous_get_changes_response(env, Some(&json))?;
                acc.insert(0, result);
            }
        }
    }
}

/// `get_changes_synchronously ~timeout instance`
pub fn get_changes_synchronously(
    timeout: isize,
    instance: WatchmanInstance,
) -> Result<(WatchmanInstance, Vec<PushedChanges>), Exn> {
    let result = call_on_instance(instance, "get_changes_synchronously", |env| {
        if env.0.settings.subscribe_mode.is_none() {
            let timeout = TimeoutSetting::ExplicitTimeout(timeout as f64);
            let query = since_query(env)?;
            let response = env.with_conn(|conn| {
                request(
                    env.0.settings.debug_logging,
                    Some(conn),
                    Some(timeout),
                    &env.0.settings.sockname,
                    &query,
                )
            })?;
            let changes = transform_asynchronous_get_changes_response(env, Some(&response))?;
            Ok(Changes::WatchmanSynchronous(vec![changes]))
        } else {
            let request = flush_request(timeout, &env.0.watch_root);
            env.with_conn(|conn| {
                send_request_and_do_not_wait_for_response(
                    env.0.settings.debug_logging,
                    conn,
                    &request,
                )
            })?;
            let deadline = crate::rt::ocaml_unix::time() + timeout as f64;
            let mut changes = poll_until_sync(deadline, env)?;
            changes.reverse();
            Ok(Changes::WatchmanSynchronous(changes))
        }
    });
    let (instance, status) = result?;
    match status {
        Changes::WatchmanUnavailable => Err(Exn::WatchmanError(
            "Watchman unavailable for synchronous response".to_string(),
        )),
        Changes::WatchmanPushed(_) => Err(Exn::WatchmanError(
            "Wtf? pushed response from synchronous request".to_string(),
        )),
        Changes::WatchmanSynchronous(files) => Ok((instance, files)),
    }
}

/// `conn_of_instance`: whether the instance has a connection (the
/// connection itself stays inside its environment).
pub fn conn_of_instance(instance: &WatchmanInstance) -> Option<&Env> {
    match instance {
        WatchmanInstance::WatchmanDead(_) => None,
        WatchmanInstance::WatchmanAlive(env) => Some(env),
    }
}

/// `get_reader instance`, as the file descriptor of the reader
/// (`Buffered_line_reader.get_fd`), which is all `Server_notifier` uses it
/// for.
pub fn get_reader(instance: &WatchmanInstance) -> Option<RawFd> {
    conn_of_instance(instance).map(|env| env.0.reader_fd)
}

/// `RepoStates.get` of the signature, for `Server_notifier`.
pub fn repo_states_get() -> (Vec<String>, s_map::T<f64>) {
    repo_states::get()
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// `Testing.get_test_env`, on a connection to nothing (a socket pair whose
    /// other end is dropped).
    fn get_test_env() -> Env {
        get_test_env_with_peer().0
    }

    /// [`get_test_env`], and the other end of its connection (watchman's).
    fn get_test_env_with_peer() -> (Env, UnixStream) {
        let (a, b) = UnixStream::pair().unwrap();
        let oc = a.try_clone().unwrap();
        let reader_fd = a.as_raw_fd();
        let env = Env(Arc::new(EnvInner {
            settings: test_settings(),
            conn: Mutex::new(Some(Conn {
                reader: Reader::create(a),
                oc,
            })),
            reader_fd,
            watch_root: "/path/to/root".to_string(),
            clockspec: Mutex::new(String::new()),
            watched_path_expression_terms: Some(j::pred(
                "anyof",
                vec![
                    j::strlist(&["dirname", "foo"]),
                    j::strlist(&["name", "foo"]),
                ],
            )),
            subscription: "dummy_prefix.123456789".to_string(),
        }));
        (env, b)
    }

    #[test]
    fn lines_and_flush_responses() {
        let (env, mut peer) = get_test_env_with_peer();
        // `Buffered_line_reader` drops the `\r` of a CRLF line.
        peer.write_all(b"{\"clock\":\"c:1\",\"files\":[\"a.php\"]}\r\n")
            .unwrap();
        let mut instance = WatchmanInstance::WatchmanAlive(env.clone());
        let (i, changes) = get_changes(None, instance).unwrap();
        instance = i;
        assert!(matches!(&instance, WatchmanInstance::WatchmanAlive(_)));
        assert_eq!(
            changes,
            Changes::WatchmanPushed(PushedChanges::FilesChanged(
                std::iter::once("/path/to/root/a.php".to_string()).collect()
            ))
        );
        // The flush response names our subscription: synced, with the
        // changes that came before it, in order.
        peer.write_all(
            b"{\"clock\":\"c:2\",\"files\":[\"b.php\"]}\n{\"clock\":\"c:3\",\"files\":[\"c.php\"]}\n{\"synced\":[\"other\",\"dummy_prefix.123456789\"]}\n",
        )
        .unwrap();
        let (i, changes) = get_changes_synchronously(10, instance).unwrap();
        instance = i;
        assert_eq!(
            changes,
            vec![
                PushedChanges::FilesChanged(
                    std::iter::once("/path/to/root/b.php".to_string()).collect()
                ),
                PushedChanges::FilesChanged(
                    std::iter::once("/path/to/root/c.php".to_string()).collect()
                ),
            ]
        );
        assert_eq!(get_clock(&instance), "c:3");
        // `no_sync_needed` ends the sync as well.
        peer.write_all(b"{\"no_sync_needed\":[\"dummy_prefix.123456789\"]}\n")
            .unwrap();
        let (i, changes) = get_changes_synchronously(10, instance).unwrap();
        instance = i;
        assert!(changes.is_empty());
        // A name that is not a string is `get_string_exn`'s `assert false`,
        // which `call_on_instance` turns into `Exit_with Watchman_failed`.
        peer.write_all(b"{\"synced\":[1]}\n").unwrap();
        let r = get_changes_synchronously(10, instance);
        assert!(matches!(
            r,
            Err(Exn::ExitWith(exit_status::T::WatchmanFailed))
        ));
    }

    #[test]
    fn init_without_a_watchman() {
        // Nothing listens on the socket: `init` is `None` (and
        // `Server_notifier` falls back to dfind).
        let settings = InitSettings {
            sockname: Some(format!(
                "{}/hh_no_watchman_{}.sock",
                std::env::temp_dir().display(),
                std::process::id()
            )),
            ..test_settings()
        };
        assert!(init(None, &settings).unwrap().is_none());
    }

    fn json(s: &str) -> yojson::T {
        yojson::from_string(s).unwrap()
    }

    #[test]
    fn requests() {
        let env = get_test_env();
        env.set_clockspec("c:1:2".to_string());
        assert_eq!(
            yojson::to_string(&subscribe(SubscribeMode::DeferChanges, &env).unwrap()),
            r#"["subscribe","/path/to/root","dummy_prefix.123456789",{"since":"c:1:2","defer":["hg.update","meerkat-build"],"empty_on_fresh_instance":true,"fields":["name"],"expression":["allof",["anyof",["dirname","foo"],["name","foo"]]]}]"#
        );
        assert_eq!(
            yojson::to_string(&since_query(&env).unwrap()),
            r#"["query","/path/to/root",{"since":"c:1:2","empty_on_fresh_instance":true,"fields":["name"],"expression":["allof",["anyof",["dirname","foo"],["name","foo"]]]}]"#
        );
        assert_eq!(
            yojson::to_string(&flush_request(120, "/r")),
            r#"["flush-subscriptions","/r",{"sync_timeout":120000}]"#
        );
        assert_eq!(
            yojson::to_string(&capability_check(
                Some(&[FLUSH_SUBSCRIPTIONS_CMD]),
                &["relative_root"]
            )),
            r#"["version",{"optional":["cmd-flush-subscriptions"],"required":["relative_root"]}]"#
        );
        assert_eq!(
            prepend_relative_path_of_directory("www", Some(vec![])),
            Some(vec![j::strlist(&["dirname", "www"])])
        );
        assert_eq!(prepend_relative_path_of_directory("", Some(vec![])), None);
        assert_eq!(prepend_relative_path_of_directory("www", None), None);
    }

    #[test]
    fn async_responses() {
        let env = get_test_env();
        let r = transform_asynchronous_get_changes_response(
            &env,
            Some(&json(
                r#"{"clock":"c:3","files":["a.php","b/c.php"],"is_fresh_instance":false}"#,
            )),
        )
        .unwrap();
        assert_eq!(
            r,
            PushedChanges::FilesChanged(
                ["/path/to/root/a.php", "/path/to/root/b/c.php"]
                    .iter()
                    .map(|s| s.to_string())
                    .collect()
            )
        );
        assert_eq!(env.clockspec(), "c:3");
        let r = transform_asynchronous_get_changes_response(
            &env,
            Some(&json(
                r#"{"clock":{"clock":"c:4"},"state-enter":"hg.update","metadata":{"rev":"x"}}"#,
            )),
        )
        .unwrap();
        assert_eq!(
            r,
            PushedChanges::StateEnter("hg.update".to_string(), Some(json(r#"{"rev":"x"}"#)))
        );
        assert_eq!(env.clockspec(), "c:4");
        assert!(repo_states::get().0.contains(&"hg.update".to_string()));
        let r = transform_asynchronous_get_changes_response(
            &env,
            Some(&json(r#"{"clock":"c:5","state-leave":"hg.update"}"#)),
        )
        .unwrap();
        assert_eq!(r, PushedChanges::StateLeave("hg.update".to_string(), None));
        assert!(repo_states::get().1.contains_key("hg.update"));
        let r = transform_asynchronous_get_changes_response(
            &env,
            Some(&json(r#"{"clock":{"clock":"c:6","scm":{"mergebase":"m2"}},"since":{"scm":{"mergebase":"m1"}},"files":[]}"#)),
        )
        .unwrap();
        assert_eq!(
            r,
            PushedChanges::ChangedMergeBase("m2".to_string(), s_set::T::new(), "c:6".to_string())
        );
        assert!(matches!(
            transform_asynchronous_get_changes_response(
                &env,
                Some(&json(
                    r#"{"clock":"c:7","files":[],"is_fresh_instance":true}"#
                ))
            ),
            Err(Exn::ExitWith(exit_status::T::WatchmanFreshInstance))
        ));
        assert!(matches!(
            transform_asynchronous_get_changes_response(&env, Some(&json(r#"{"files":[]}"#))),
            Err(Exn::Failure(_))
        ));
        assert_eq!(
            transform_asynchronous_get_changes_response(&env, None).unwrap(),
            PushedChanges::FilesChanged(s_set::T::new())
        );
    }

    #[test]
    fn errors_and_capabilities() {
        assert!(matches!(
            sanitize_watchman_response(false, r#"{"error":"bad"}"#),
            Err(Exn::WatchmanError(m)) if m == "bad"
        ));
        assert!(matches!(
            sanitize_watchman_response(false, r#"{"canceled":true}"#),
            Err(Exn::SubscriptionCanceledByWatchman)
        ));
        assert!(matches!(
            sanitize_watchman_response(false, "not json"),
            Err(Exn::JsonError(_))
        ));
        assert!(sanitize_watchman_response(false, r#"{"warning":"w","x":1}"#).is_ok());
        assert!(has_capability(
            FLUSH_SUBSCRIPTIONS_CMD,
            &json(r#"{"capabilities":{"cmd-flush-subscriptions":true}}"#)
        ));
        assert!(!has_capability(
            FLUSH_SUBSCRIPTIONS_CMD,
            &json(r#"{"capabilities":{}}"#)
        ));
        assert_eq!(
            format!("{:?}", Exn::WatchmanError("a\"b".to_string())),
            r#"Watchman_sig.Types.Watchman_error("a\"b")"#
        );
        assert_eq!(
            format!("{:?}", Exn::ExitWith(exit_status::T::WatchmanFailed)),
            "Exit_status.Exit_with(Exit_status.Watchman_failed)"
        );
        assert_eq!(
            extract_clock(&json(r#"{"clock":"c:1"}"#)).ok(),
            Some("c:1".to_string())
        );
        // The backoff: 4s, 8s, 16s, then 32s.
        assert!(within_backoff_time(0, crate::rt::ocaml_unix::time() - 4.));
        assert!(!within_backoff_time(1, crate::rt::ocaml_unix::time() - 4.));
        assert!(within_backoff_time(9, crate::rt::ocaml_unix::time() - 32.));
        assert!(!within_backoff_time(9, crate::rt::ocaml_unix::time() - 31.));
    }

    #[test]
    fn dead_instances() {
        let env = get_test_env();
        env.set_clockspec("c:9".to_string());
        let (instance, changes) = close_channel_on_instance(&env);
        assert_eq!(changes, Changes::WatchmanUnavailable);
        assert_eq!(get_clock(&instance), "c:9");
        assert!(get_reader(&instance).is_none());
        // Out of attempts: `Exit_with Watchman_failed`.
        let dead = match instance {
            WatchmanInstance::WatchmanDead(d) => d,
            WatchmanInstance::WatchmanAlive(_) => unreachable!(),
        };
        let exhausted = WatchmanInstance::WatchmanDead(DeadEnv {
            reinit_attempts: MAX_REINIT_ATTEMPTS,
            ..dead.clone()
        });
        let r = get_changes(None, exhausted.clone());
        assert!(matches!(
            r,
            Err(Exn::ExitWith(exit_status::T::WatchmanFailed))
        ));
        // Within the backoff time: still dead, unavailable.
        let (instance, changes) = get_changes(None, WatchmanInstance::WatchmanDead(dead.clone())).unwrap();
        assert_eq!(changes, Changes::WatchmanUnavailable);
        assert!(matches!(instance, WatchmanInstance::WatchmanDead(_)));
        // A synchronous request to a dead instance raises `Watchman_error`.
        let r = get_changes_synchronously(1, WatchmanInstance::WatchmanDead(dead));
        match r {
            Err(Exn::WatchmanError(msg)) => {
                assert_eq!(msg, "Watchman unavailable for synchronous response")
            }
            r => panic!("{:?}", r.map(|_| ())),
        }
    }

    #[test]
    fn closed_connection_is_end_of_file() {
        // The other end of the test connection is closed: watchman went away.
        let env = get_test_env();
        env.set_clockspec("c:8".to_string());
        // A hang-up reads as readable (as for `select`), and the read gives
        // `End_of_file`: "Watchman connection End_of_file. Closing channel",
        // and the instance is dead with the last clock.
        let (instance, changes) = get_changes(None, WatchmanInstance::WatchmanAlive(env.clone())).unwrap();
        assert_eq!(changes, Changes::WatchmanUnavailable);
        match &instance {
            WatchmanInstance::WatchmanDead(dead) => {
                assert_eq!(dead.prior_clockspec, "c:8");
                assert_eq!(dead.reinit_attempts, 0);
            }
            WatchmanInstance::WatchmanAlive(_) => panic!("still alive"),
        }
    }

    #[test]
    fn nothing_to_read() {
        // The other end is open but has sent nothing: with the default
        // timeout of 0, `blocking_read` is `None`, an empty change.
        let (env, _peer) = get_test_env_with_peer();
        let (instance, changes) = get_changes(None, WatchmanInstance::WatchmanAlive(env)).unwrap();
        assert!(matches!(instance, WatchmanInstance::WatchmanAlive(_)));
        assert_eq!(
            changes,
            Changes::WatchmanPushed(PushedChanges::FilesChanged(s_set::T::new()))
        );
    }

    // The tests below run against the watchman that is installed, if there
    // is one (they pass without doing anything otherwise).

    pub(crate) fn watchman_is_installed() -> bool {
        let installed = std::process::Command::new("watchman")
            .arg("version")
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .is_ok_and(|s| s.success());
        if !installed {
            eprintln!("watchman is not installed: skipping the test");
        }
        installed
    }

    /// A temporary root, canonical (as `Server_args.root` is), with a few
    /// files.
    pub(crate) fn scratch_root(name: &str) -> String {
        let dir = std::env::temp_dir().join(format!(
            "hh_notifier_watchman_{}_{}",
            name,
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join(".git")).unwrap();
        let dir = std::fs::canonicalize(&dir)
            .unwrap()
            .to_str()
            .unwrap()
            .to_string();
        for f in ["a.php", "b.php", "c.php", ".hhconfig", "readme.txt"] {
            std::fs::write(format!("{dir}/{f}"), "1").unwrap();
        }
        dir
    }

    pub(crate) fn watch_del(root: &str) {
        let _ = request(false, None, None, &None, &j::strlist(&["watch-del", root]));
        let _ = std::fs::remove_dir_all(root);
    }

    /// [`watch_del`] of its root when dropped, so that a test that fails
    /// does not leave its watch in the user's watchman (leaked watches use
    /// up FSEvents streams and file descriptors).
    pub(crate) struct WatchDelOnDrop(pub String);

    impl Drop for WatchDelOnDrop {
        fn drop(&mut self) {
            watch_del(&self.0)
        }
    }

    pub(crate) fn settings(root: &str, subscribe_mode: Option<SubscribeMode>) -> InitSettings {
        InitSettings {
            subscribe_mode,
            init_timeout: TimeoutSetting::ExplicitTimeout(10.),
            expression_terms: crate::files_to_ignore::watchman_server_expression_terms(),
            debug_logging: false,
            roots: vec![root.to_string()],
            sockname: None,
            subscription_prefix: "hh_type_check_watcher".to_string(),
        }
    }

    fn files_of(changes: &[PushedChanges]) -> s_set::T {
        let mut files = s_set::T::new();
        for c in changes {
            if let PushedChanges::FilesChanged(f) = c {
                files = files.union(f.clone());
            }
        }
        files
    }

    /// Edits the root: a change, a creation, a deletion, a rename, a
    /// `.hhconfig` change, and files that the expression leaves out.
    pub(crate) fn edit(root: &str) {
        std::fs::write(format!("{root}/a.php"), "2").unwrap();
        std::fs::write(format!("{root}/new.php"), "").unwrap();
        std::fs::remove_file(format!("{root}/b.php")).unwrap();
        std::fs::rename(format!("{root}/c.php"), format!("{root}/c2.php")).unwrap();
        std::fs::write(format!("{root}/.hhconfig"), "2").unwrap();
        std::fs::write(format!("{root}/.git/x.php"), "").unwrap();
        std::fs::write(format!("{root}/readme.txt"), "2").unwrap();
    }

    pub(crate) fn check_edits(root: &str, files: &s_set::T) {
        for f in ["a.php", "new.php", "b.php", "c.php", "c2.php", ".hhconfig"] {
            assert!(
                files.contains(&format!("{root}/{f}")),
                "{f} not in {files:?}"
            );
        }
        for f in [".git/x.php", "readme.txt"] {
            assert!(!files.contains(&format!("{root}/{f}")), "{f} in {files:?}");
        }
    }

    #[test]
    fn subscription_with_a_real_watchman() {
        if !watchman_is_installed() {
            return;
        }
        let root = scratch_root("subscribe");
        let _watch = WatchDelOnDrop(root.clone());
        let env =
            init(None, &settings(&root, Some(SubscribeMode::DeferChanges)))
                .unwrap()
                .expect("watchman init");
        assert_eq!(
            env.subscription(),
            format!("hh_type_check_watcher.{}", std::process::id())
        );
        assert_eq!(env.watch_root(), root);
        assert_eq!(
            env.settings().subscribe_mode,
            Some(SubscribeMode::DeferChanges)
        );
        let instance = WatchmanInstance::WatchmanAlive(env.clone());
        let clock0 = get_clock(&instance);
        // In sync with what is on disk: nothing changed.
        let (instance, changes) = get_changes_synchronously(30, instance).unwrap();
        assert!(files_of(&changes).is_empty(), "{changes:?}");
        // The changes, synchronously (flush-subscriptions).
        edit(&root);
        let (instance, changes) = get_changes_synchronously(30, instance).unwrap();
        check_edits(&root, &files_of(&changes));
        assert_ne!(get_clock(&instance), clock0);
        // A change, pushed: the connection becomes readable, and one
        // `get_changes` reads one notification.
        std::fs::write(format!("{root}/a.php"), "3").unwrap();
        let fd = get_reader(&instance).unwrap();
        let mut instance = instance;
        let mut seen = s_set::T::new();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
        while !seen.contains(&format!("{root}/a.php")) {
            assert!(std::time::Instant::now() < deadline, "no pushed change");
            if fd_is_readable(fd, 1.0) {
                let (i, changes) = get_changes(None, instance).unwrap();
                instance = i;
                match changes {
                    Changes::WatchmanPushed(PushedChanges::FilesChanged(f)) => seen = seen.union(f),
                    Changes::WatchmanPushed(_) => {}
                    c => panic!("unexpected {c:?}"),
                }
            }
        }
        // Nothing more to read: an empty set, at once.
        let (_, changes) = get_changes(None, instance.clone()).unwrap();
        assert!(matches!(changes, Changes::WatchmanPushed(_)));
        // All the Hack files and the .hhconfig (`exists`).
        let mut all: Vec<String> = get_all_files(&env)
            .unwrap()
            .into_iter()
            .map(|f| f[root.len() + 1..].to_string())
            .collect();
        all.sort();
        assert_eq!(all, vec![".hhconfig", "a.php", "c2.php", "new.php"]);
        close(&env);
        watch_del(&root);
    }

    #[test]
    fn query_mode_with_a_real_watchman() {
        if !watchman_is_installed() {
            return;
        }
        let root = scratch_root("query");
        let _watch = WatchDelOnDrop(root.clone());
        let env = init(None, &settings(&root, None))
            .unwrap()
            .expect("watchman init");
        let instance = WatchmanInstance::WatchmanAlive(env.clone());
        edit(&root);
        // A `since` query: synchronous changes.
        let (instance, changes) = get_changes(None, instance).unwrap();
        match changes {
            Changes::WatchmanSynchronous(changes) => check_edits(&root, &files_of(&changes)),
            c => panic!("unexpected {c:?}"),
        }
        // And nothing new since.
        let (_instance, changes) = get_changes_synchronously(30, instance).unwrap();
        assert!(files_of(&changes).is_empty(), "{changes:?}");
        // A clock that watchman does not know (another watchman instance):
        // re-initialising with it is `Watchman_restarted`.
        let dead = DeadEnv {
            prior_settings: settings(&root, None),
            reinit_attempts: 0,
            dead_since: 0.,
            prior_clockspec: "c:0:0".to_string(),
        };
        let r = get_changes(None, WatchmanInstance::WatchmanDead(dead));
        assert!(matches!(r, Err(Exn::WatchmanRestarted)));
        // With its own clock, a dead instance comes back to life.
        let dead = match close_channel_on_instance(&env).0 {
            WatchmanInstance::WatchmanDead(d) => DeadEnv {
                dead_since: 0.,
                ..d
            },
            WatchmanInstance::WatchmanAlive(_) => unreachable!(),
        };
        let (instance, changes) = get_changes(None, WatchmanInstance::WatchmanDead(dead)).unwrap();
        assert!(matches!(instance, WatchmanInstance::WatchmanAlive(_)));
        assert!(matches!(changes, Changes::WatchmanSynchronous(_)));
        drop(instance);
        watch_del(&root);
    }
}
