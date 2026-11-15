// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/monitor_client_api/monitor_utils.ml`.

use std::sync::LazyLock;

use serde::Deserialize;
use serde::Serialize;

use crate::build_id;
use crate::connection_tracker;
use crate::exception;
use crate::rt::ocaml_marshal::Value;
use crate::rt::ocaml_sys;
use crate::rt::ocaml_unix;
use crate::telemetry;
use crate::yojson::safe as yojson;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MonitorConfig {
    /// The socket file on which the monitor is listening for connections.
    pub socket_file: String,
    /// This lock is held when a monitor is alive.
    pub lock_file: String,
    /// The path to the server log file
    pub server_log_file: String,
    /// The path to the monitor log file
    pub monitor_log_file: String,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BuildMismatchInfo {
    pub existing_version: String,
    pub existing_build_commit_time: String,
    pub existing_argv: Vec<String>,
    pub existing_launch_time: f64,
}

/// `current_build_info`: OCaml computes it when the program starts (its
/// launch time is then); here when it is first used. The server calls
/// it as it starts ([`crate::server_client_provider::server_end`] does, when it
/// binds), so that the launch time is the server's.
pub fn current_build_info() -> BuildMismatchInfo {
    static CURRENT_BUILD_INFO: LazyLock<BuildMismatchInfo> =
        LazyLock::new(|| BuildMismatchInfo {
            existing_version: build_id::build_revision(),
            existing_build_commit_time: build_id::build_commit_time_string(),
            existing_argv: ocaml_sys::argv(),
            existing_launch_time: ocaml_unix::gettimeofday(),
        });
    CURRENT_BUILD_INFO.clone()
}

#[derive(Debug)]
pub enum ConnectFailureReason {
    ConnectTimeout,
    ConnectException(exception::T),
}

/// `show_connect_failure_reason` (`[@@deriving show { with_path = false }]`,
/// with its printer for the exception).
pub fn show_connect_failure_reason(r: &ConnectFailureReason) -> String {
    match r {
        ConnectFailureReason::ConnectTimeout => "Connect_timeout".to_string(),
        ConnectFailureReason::ConnectException(e) => {
            format!("Connect_exception({})", exception::get_ctor_string(e))
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConnectFailurePhase {
    ConnectOpenSocket,
    ConnectSendVersion,
    ConnectSendNewline,
    ConnectReceiveConnectionOk,
    ConnectSendShutdown,
}

/// `show_connect_failure_phase` (`[@@deriving show { with_path = false }]`)
pub fn show_connect_failure_phase(p: ConnectFailurePhase) -> &'static str {
    match p {
        ConnectFailurePhase::ConnectOpenSocket => "Connect_open_socket",
        ConnectFailurePhase::ConnectSendVersion => "Connect_send_version",
        ConnectFailurePhase::ConnectSendNewline => "Connect_send_newline",
        ConnectFailurePhase::ConnectReceiveConnectionOk => "Connect_receive_connection_ok",
        ConnectFailurePhase::ConnectSendShutdown => "Connect_send_shutdown",
    }
}

#[derive(Debug)]
pub struct ConnectToMonitorFailure {
    /// This reflects the state of the lock file shortly after the failure happened.
    pub server_exists: bool,
    pub failure_phase: ConnectFailurePhase,
    pub failure_reason: ConnectFailureReason,
}

#[derive(Debug)]
pub enum ConnectionError {
    ConnectToMonitorFailure(ConnectToMonitorFailure),
    ServerDied,
    /// Server dormant, i.e. waiting for a rebase to settle, and monitor's queue
    /// of pending connections in the now-full queue of connections waiting for the next server.
    ServerDormant,
    ServerDormantOutOfRetries,
    /// hh_client binary is a different version from hh_server binary,
    /// so hh_server will terminate.
    BuildIdMismatchedMonitorWillTerminate(Option<BuildMismatchInfo>),
    /// hh_client binary is a different version and must abandon its connection attempt
    BuildIdMismatchedClientMustTerminate(BuildMismatchInfo),
}

/// `pp_build_mismatch_info` (`[@@deriving show]`), on one line (OCaml's
/// `Format` boxes may break it; only the logs show it).
fn show_build_mismatch_info(info: &BuildMismatchInfo) -> String {
    use crate::rt::ocaml_printf::sprintf_s;
    format!(
        "{{ Monitor_utils.existing_version = {}; existing_build_commit_time = {}; existing_argv = [{}]; existing_launch_time = {} }}",
        sprintf_s(&info.existing_version),
        sprintf_s(&info.existing_build_commit_time),
        info.existing_argv
            .iter()
            .map(|s| sprintf_s(s))
            .collect::<Vec<_>>()
            .join("; "),
        info.existing_launch_time,
    )
}

/// `show_connection_error` (`[@@deriving show { with_path = false }]`),
/// on one line (OCaml's `Format` boxes may break the records; only the
/// logs show them).
pub fn show_connection_error(e: &ConnectionError) -> String {
    match e {
        ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
            server_exists,
            failure_phase,
            failure_reason,
        }) => format!(
            "(Connect_to_monitor_failure {{ server_exists = {}; failure_phase = {}; failure_reason = {} }})",
            server_exists,
            show_connect_failure_phase(*failure_phase),
            show_connect_failure_reason(failure_reason)
        ),
        ConnectionError::ServerDied => "Server_died".to_string(),
        ConnectionError::ServerDormant => "Server_dormant".to_string(),
        ConnectionError::ServerDormantOutOfRetries => "Server_dormant_out_of_retries".to_string(),
        ConnectionError::BuildIdMismatchedMonitorWillTerminate(None) => {
            "(Build_id_mismatched_monitor_will_terminate None)".to_string()
        }
        ConnectionError::BuildIdMismatchedMonitorWillTerminate(Some(info)) => format!(
            "(Build_id_mismatched_monitor_will_terminate (Some {}))",
            show_build_mismatch_info(info)
        ),
        ConnectionError::BuildIdMismatchedClientMustTerminate(info) => format!(
            "(Build_id_mismatched_client_must_terminate {})",
            show_build_mismatch_info(info)
        ),
    }
}

/// The telemetry we get from this ends up appearing in our telemetry a HUGE number of times.
/// I guess [HackEventLogger.client_connect_once_failure] is just called a lot.
/// We therefore take pains to make this as minimal as we can.
pub fn connection_error_to_telemetry(e: &ConnectionError) -> (String, Option<telemetry::T>) {
    match e {
        ConnectionError::ServerDied
        | ConnectionError::ServerDormant
        | ConnectionError::ServerDormantOutOfRetries
        | ConnectionError::BuildIdMismatchedMonitorWillTerminate(_)
        | ConnectionError::BuildIdMismatchedClientMustTerminate(_) => {
            // these errors come from MonitorConnection.connect_to_monitor [match cstate]
            (show_connection_error(e), None)
        }
        ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
            server_exists,
            failure_phase,
            failure_reason,
        }) => {
            let (reason, stack) = match failure_reason {
                ConnectFailureReason::ConnectTimeout => {
                    // comes from MonitorConnection.connect_to_monitor [Unix.open_connection]
                    ("Connect_timeout".to_string(), None)
                }
                ConnectFailureReason::ConnectException(e) => {
                    // comes from MonitorConnection.connect_to_monitor and [phase] says what part
                    let ctor = exception::get_ctor_string(e);
                    let errno = exception::unwrap(e)
                        .downcast_ref::<UnixError>()
                        .and_then(|u| u.0.raw_os_error().map(|c| (c, u.1)));
                    match errno {
                        Some((libc::ECONNREFUSED, "connect")) => {
                            // Generally comes from [Unix.open_connection]
                            ("ECONNREFUSED".to_string(), None)
                        }
                        Some((libc::ENOENT, "connect")) => {
                            // Generally comes from [Unix.open_connection]
                            ("ENOENT".to_string(), None)
                        }
                        Some((libc::EMFILE, "pipe")) => {
                            // Usually comes from [Process.exec Exec_command.Pgrep]
                            ("EMFILE".to_string(), None)
                        }
                        Some((libc::ECONNRESET, "read")) => {
                            // Usually from [let cstate : ... = from_channel_without_buffering ic]
                            ("ECONNRESET".to_string(), None)
                        }
                        _ => (
                            ctor,
                            Some(exception::clean_stack(&exception::get_backtrace_string(e))),
                        ),
                    }
                }
            };
            let exists = if *server_exists { "exists" } else { "absent" };
            let reason = format!(
                "{}:{} [{}]",
                show_connect_failure_phase(*failure_phase),
                reason,
                exists
            );
            let telemetry =
                stack.map(|value| telemetry::string_(None, "stack", &value, telemetry::create()));
            (reason, telemetry)
        }
    }
}

/// `Unix.Unix_error (err, fun_name, "")`, as an exception: what
/// `ConnectException` wraps.
pub struct UnixError(pub std::io::Error, pub &'static str);

impl std::fmt::Debug for UnixError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&ocaml_unix::unix_error_to_string(&self.0, self.1, ""))
    }
}

/// The first part of the client/monitor handshake is that client sends
/// a [VersionPayload.serialized] over the socket, followed by a newline byte.
/// Note that [VersionPayload.serialized] is just an ocaml string, and can
/// never be anything else, because we have to maintain forwards and backwards
/// compatibility between different version of hh_client and hh_server.
pub mod version_payload {
    use super::*;

    pub type Serialized = String;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub client_version: String,
        pub tracker_id: String,
        pub terminate_monitor_on_version_mismatch: bool,
        /// What a Rust client asks a Rust monitor (the field
        /// [`RUST_TERMINATE_KEY`], which only Rust clients send and only
        /// Rust monitors read): `terminate_monitor_on_version_mismatch`
        /// is then what it asks a monitor of the other implementation
        /// (see [`crate::rt::protocol::cross_implementation_policy`]).
        pub rust_terminate_monitor_on_version_mismatch: Option<bool>,
    }

    /// The field of the payload that only the Rust implementation reads.
    pub const RUST_TERMINATE_KEY: &str = "rust_terminate_monitor_on_version_mismatch";

    /// `serialize ~tracker ~terminate_monitor_on_version_mismatch`, by a
    /// Rust client: `terminate_monitor_on_version_mismatch` is what it
    /// asks a Rust monitor, `terminate_other_implementation` what it asks
    /// an OCaml monitor (the OCaml's field).
    pub fn serialize(
        tracker: &connection_tracker::T,
        terminate_monitor_on_version_mismatch: bool,
        terminate_other_implementation: bool,
    ) -> Serialized {
        yojson::to_string(&yojson::T::Assoc(vec![
            (
                "client_version".to_string(),
                yojson::T::String(build_id::build_revision()),
            ),
            (
                "tracker_id".to_string(),
                yojson::T::String(connection_tracker::log_id(tracker)),
            ),
            (
                "terminate_monitor_on_version_mismatch".to_string(),
                yojson::T::Bool(terminate_other_implementation),
            ),
            (
                RUST_TERMINATE_KEY.to_string(),
                yojson::T::Bool(terminate_monitor_on_version_mismatch),
            ),
        ]))
    }

    /// How `deserialize` fails: its `Error`, or the exception that the
    /// `Yojson.Safe.Util` accessors raise (`Type_error`, as
    /// `Printexc.to_string` shows it), which OCaml does not catch there.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum DeserializeError {
        Error(String),
        TypeError(String),
    }

    pub fn deserialize(s: &str) -> Result<T, DeserializeError> {
        // Newer clients send version in a json object; older clients sent just a client_version string
        let json = if s.starts_with('{') {
            match yojson::from_string(s) {
                Ok(json) => json,
                Err(exn) => return Err(DeserializeError::Error(exn.to_string())),
            }
        } else {
            yojson::T::Assoc(vec![(
                "client_version".to_string(),
                yojson::T::String(s.to_string()),
            )])
        };
        let raised = DeserializeError::TypeError;
        let client_version =
            match util::to_string_option(util::member("client_version", &json).map_err(raised)?)
                .map_err(raised)?
            {
                Some(s) => s,
                None => return Err(DeserializeError::Error("Missing client_version".to_string())),
            };
        let tracker_id =
            util::to_string_option(util::member("tracker_id", &json).map_err(raised)?)
                .map_err(raised)?
                .unwrap_or_else(|| "t#?".to_string());
        let terminate_monitor_on_version_mismatch = util::to_bool_option(
            util::member("terminate_monitor_on_version_mismatch", &json).map_err(raised)?,
        )
        .map_err(raised)?
        .unwrap_or(true);
        let rust_terminate_monitor_on_version_mismatch =
            util::to_bool_option(util::member(RUST_TERMINATE_KEY, &json).map_err(raised)?)
                .map_err(raised)?;
        Ok(T {
            client_version,
            tracker_id,
            terminate_monitor_on_version_mismatch,
            rust_terminate_monitor_on_version_mismatch,
        })
    }
}

/// The accessors of `Yojson.Safe.Util` that the payloads use. They raise
/// `Type_error (msg, json)`: here an `Err` of what `Printexc.to_string`
/// shows of it.
mod util {
    use super::yojson;

    /// `typerr msg js`
    fn typerr(msg: &str, json: &yojson::T) -> String {
        format!(
            "Yojson.Safe.Util.Type_error({}, _)",
            crate::rt::ocaml_printf::sprintf_s(&format!("{}{}", msg, crate::yojson::safe::util::typeof_(json)))
        )
    }

    /// `member name json`: the field `name` of an object, `Null` if
    /// there is none.
    pub fn member<'a>(name: &str, json: &'a yojson::T) -> Result<&'a yojson::T, String> {
        match json {
            yojson::T::Assoc(fields) => Ok(fields
                .iter()
                .find(|(k, _)| k == name)
                .map_or(&yojson::T::Null, |(_, v)| v)),
            js => Err(typerr(
                &format!("Can't get member '{}' of non-object type ", name),
                js,
            )),
        }
    }

    pub fn to_string_option(json: &yojson::T) -> Result<Option<String>, String> {
        match json {
            yojson::T::String(s) => Ok(Some(s.clone())),
            yojson::T::Null => Ok(None),
            js => Err(typerr("Expected string or null, got ", js)),
        }
    }

    pub fn to_bool_option(json: &yojson::T) -> Result<Option<bool>, String> {
        match json {
            yojson::T::Bool(b) => Ok(Some(*b)),
            yojson::T::Null => Ok(None),
            js => Err(typerr("Expected bool or null, got ", js)),
        }
    }
}

/// The second part of the client/monitor handshake is that monitor sends
/// [connection_state] over the socket. In case of version mismatch it sends
/// [Build_id_mismatch_v3], which includes a [MismatchPayload.serialized].
/// Note that this is just an ocaml string, and can never be anything else,
/// because we have to maintain forwards and backwards compatibility between
/// different versions of hh_client and hh_server. (However, every version
/// in existince understands the binary format of Build_id_mismatch_v3...)
pub mod mismatch_payload {
    use super::*;

    pub type Serialized = String;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct T {
        pub monitor_will_terminate: bool,
    }

    pub fn serialize(monitor_will_terminate: bool) -> Serialized {
        yojson::to_string(&yojson::T::Assoc(vec![(
            "monitor_will_terminate".to_string(),
            yojson::T::Bool(monitor_will_terminate),
        )]))
    }

    /// `Yojson.Safe.Util.(json |> member .. |> to_bool_option)` is
    /// outside the `try`: its `Type_error` is not caught, here or by the
    /// callers (until the catch-all of the program). It is the outer
    /// error.
    pub fn deserialize(
        s: &str,
    ) -> Result<Result<T, String>, crate::rt::protocol::UncaughtReadError> {
        let json = match yojson::from_string(s) {
            Ok(json) => json,
            Err(exn) => return Ok(Err(exn.to_string())),
        };
        let monitor_will_terminate = match util::member("monitor_will_terminate", &json)
            .and_then(util::to_bool_option)
        {
            Ok(b) => b.unwrap_or(true),
            Err(exn) => return Err(crate::rt::protocol::UncaughtReadError(exn)),
        };
        Ok(Ok(T {
            monitor_will_terminate,
        }))
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum ConnectionState {
    ConnectionOk,
    /// Build_is_mismatch is never used, but it can't be removed, because
    /// the sequence of constructors here is part of the binary protocol
    /// we want to support between mismatched versions of client_server.
    BuildIdMismatch,
    /// Build_id_mismatch_ex also isn't used.
    BuildIdMismatchEx(BuildMismatchInfo),
    /// Build_id_mismatch_v3 is used!
    BuildIdMismatchV3(BuildMismatchInfo, mismatch_payload::Serialized),
    /// Connection_ok_v2 isn't used yet, but might be
    ConnectionOkV2(String),
}

/// `show_connection_state` (`[@@deriving show]`), for the constructors the
/// server sends; the logs only.
pub fn show_connection_state(c: &ConnectionState) -> String {
    match c {
        ConnectionState::ConnectionOk => "Monitor_utils.Connection_ok".to_string(),
        ConnectionState::BuildIdMismatch => "Monitor_utils.Build_id_mismatch".to_string(),
        ConnectionState::BuildIdMismatchEx(info) => format!(
            "(Monitor_utils.Build_id_mismatch_ex {})",
            show_build_mismatch_info(info)
        ),
        ConnectionState::BuildIdMismatchV3(info, payload) => format!(
            "(Monitor_utils.Build_id_mismatch_v3 ({}, {}))",
            show_build_mismatch_info(info),
            crate::rt::ocaml_printf::sprintf_s(payload)
        ),
        ConnectionState::ConnectionOkV2(s) => format!(
            "(Monitor_utils.Connection_ok_v2 {})",
            crate::rt::ocaml_printf::sprintf_s(s)
        ),
    }
}

/// Result of a shutdown monitor RPC.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShutdownResult {
    /// Request sent and channel hung up, indicating the process has exited.
    ShutdownVerified,
    /// Request sent, but channel hasn't hung up.
    ShutdownUnverified,
}

/// Message we send to the --waiting-client
pub const READY: &str = "ready";

// ~~ The two implementations ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// What a client and a monitor of different implementations (Rust and
/// OCaml, installed side by side and sharing the files of a root) do on
/// their version mismatch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CrossImplementationPolicy {
    /// Neither replaces the other's server: the Rust monitor answers an
    /// OCaml client `monitor_will_terminate = false` (the OCaml client
    /// says "Error: version mismatch" and exits `Build_id_mismatch`); a
    /// Rust client asks an OCaml monitor not to terminate, says which
    /// server runs and how to stop it, and exits `Build_id_mismatch`.
    /// An explicit `stop` still stops the other's server.
    Refuse,
    /// As between two versions of one implementation (the OCaml's
    /// `terminate_monitor_on_version_mismatch`).
    TakeOver,
}

/// The policy between the two implementations: the one place to change
/// it.
pub fn cross_implementation_policy() -> CrossImplementationPolicy {
    CrossImplementationPolicy::Refuse
}

/// What a Rust client asks a monitor of the other implementation, when
/// it would ask a Rust one `terminate` (a `stop` asks both to terminate,
/// whatever the policy).
pub fn terminate_other_implementation(terminate: bool, is_stop: bool) -> bool {
    match cross_implementation_policy() {
        _ if is_stop => true,
        CrossImplementationPolicy::Refuse => false,
        CrossImplementationPolicy::TakeOver => terminate,
    }
}

/// Whether this (Rust) monitor terminates on a version mismatch with the
/// client of `payload`.
pub fn monitor_will_terminate(payload: &version_payload::T) -> bool {
    if build_id::is_rust_build_revision(&payload.client_version) {
        payload
            .rust_terminate_monitor_on_version_mismatch
            .unwrap_or(payload.terminate_monitor_on_version_mismatch)
    } else {
        match cross_implementation_policy() {
            CrossImplementationPolicy::Refuse => false,
            CrossImplementationPolicy::TakeOver => payload.terminate_monitor_on_version_mismatch,
        }
    }
}

/// Whether the monitor of a mismatch is of the other implementation.
pub fn is_other_implementation(info: &BuildMismatchInfo) -> bool {
    !build_id::is_rust_build_revision(&info.existing_version)
}

/// What the Rust client says when it finds a monitor of the other
/// implementation, which it does not replace.
pub fn other_implementation_message(info: &BuildMismatchInfo, root: &str) -> String {
    format!(
        "Error: an OCaml hh_server is running for {}; this hh_client is the Rust one and does not replace it.\n  hh_server '{}', version '{}', launched {}\nStop it first (`hh_client stop {}`, with either hh_client), then retry.\n",
        root,
        info.existing_argv.join(" "),
        info.existing_version,
        crate::utils::timestring(info.existing_launch_time),
        root
    )
}

// ~~ The OCaml values of the handshake ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn build_mismatch_info_to_ocaml(info: &BuildMismatchInfo) -> Value {
    Value::block(
        0,
        vec![
            Value::string(info.existing_version.as_bytes()),
            Value::string(info.existing_build_commit_time.as_bytes()),
            Value::list(info.existing_argv.iter().map(|a| Value::string(a.as_bytes()))),
            Value::double(info.existing_launch_time),
        ],
    )
}

fn string_of_ocaml(v: &Value) -> Result<String, String> {
    v.as_bytes()
        .map(|b| String::from_utf8_lossy(b).into_owned())
        .map_err(|e| e.0)
}

fn build_mismatch_info_of_ocaml(v: &Value) -> Result<BuildMismatchInfo, String> {
    let f = v.fields(0, 4).map_err(|e| e.0)?;
    Ok(BuildMismatchInfo {
        existing_version: string_of_ocaml(&f[0])?,
        existing_build_commit_time: string_of_ocaml(&f[1])?,
        existing_argv: f[2]
            .list_items()
            .map_err(|e| e.0)?
            .into_iter()
            .map(string_of_ocaml)
            .collect::<Result<_, _>>()?,
        existing_launch_time: f[3].as_double().map_err(|e| e.0)?,
    })
}

/// The OCaml value of a `connection_state`, as the OCaml monitor
/// marshals it.
pub fn connection_state_to_ocaml(c: &ConnectionState) -> Value {
    match c {
        ConnectionState::ConnectionOk => Value::int(0),
        ConnectionState::BuildIdMismatch => Value::int(1),
        ConnectionState::BuildIdMismatchEx(info) => {
            Value::block(0, vec![build_mismatch_info_to_ocaml(info)])
        }
        ConnectionState::BuildIdMismatchV3(info, payload) => Value::block(
            1,
            vec![
                build_mismatch_info_to_ocaml(info),
                Value::string(payload.as_bytes()),
            ],
        ),
        ConnectionState::ConnectionOkV2(s) => Value::block(2, vec![Value::string(s.as_bytes())]),
    }
}

/// A `connection_state` of its OCaml value; `Err` for a value of
/// another type.
pub fn connection_state_of_ocaml(v: &Value) -> Result<ConnectionState, String> {
    if let Ok(n) = v.as_int() {
        return match n {
            0 => Ok(ConnectionState::ConnectionOk),
            1 => Ok(ConnectionState::BuildIdMismatch),
            n => Err(format!("connection_state: constant {}", n)),
        };
    }
    let (tag, fields) = v.as_block().map_err(|e| e.0)?;
    match (tag, fields) {
        (0, [info]) => Ok(ConnectionState::BuildIdMismatchEx(
            build_mismatch_info_of_ocaml(info)?,
        )),
        (1, [info, payload]) => Ok(ConnectionState::BuildIdMismatchV3(
            build_mismatch_info_of_ocaml(info)?,
            string_of_ocaml(payload)?,
        )),
        (2, [s]) => Ok(ConnectionState::ConnectionOkV2(string_of_ocaml(s)?)),
        (tag, f) => Err(format!("connection_state: block {} of {}", tag, f.len())),
    }
}
