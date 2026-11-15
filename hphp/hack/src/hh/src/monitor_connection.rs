// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/monitor_client_api/monitor_connection.ml`: the client's end
//! of frames 1 to 4.

use std::io::Read;
use std::os::unix::net::UnixStream;

use crate::connection_tracker;
use crate::connection_tracker::Key;
use crate::exception;
use crate::hh_logger;
use crate::lock;
use crate::monitor_rpc;
use crate::monitor_utils::ConnectFailurePhase;
use crate::monitor_utils::ConnectFailureReason;
use crate::monitor_utils::ConnectToMonitorFailure;
use crate::monitor_utils::ConnectionError;
use crate::monitor_utils::ConnectionState;
use crate::monitor_utils::MonitorConfig;
use crate::monitor_utils::ShutdownResult;
use crate::monitor_utils::UnixError;
use crate::path;
use crate::prehandoff;
use crate::rt::ocaml_unix;
use crate::rt::protocol::Deadline;
use crate::rt::protocol::ReadError;
use crate::rt::protocol::UncaughtReadError;
use crate::rt::protocol::read_value;
use crate::rt::protocol::write_value;
use crate::server_command_types::ServerSpecificFiles;
use crate::server_files;
use crate::socket;

use crate::monitor_utils::{self};

fn log(s: &str, tracker: &connection_tracker::T) {
    hh_logger::log(&format!("[{}] {}", connection_tracker::log_id(tracker), s))
}

pub fn server_exists(lock_file: &str) -> bool {
    !lock::check(lock_file)
}

pub fn hh_monitor_config(root: &path::T) -> MonitorConfig {
    MonitorConfig {
        lock_file: server_files::lock_file(root),
        socket_file: server_files::socket_file(root),
        server_log_file: server_files::log_link(root),
        monitor_log_file: server_files::monitor_log_link(root),
    }
}

/// The server is out of date and is going to exit. Subsequent calls
/// to connect on the Unix Domain Socket might succeed, connecting to
/// the server that is about to die, and eventually we will be hung
/// up on while trying to read from our end.
///
/// To avoid that fate, when we know the server is about to exit, we
/// wait for the connection to be closed, signaling that the server
/// has exited and the OS has cleaned up after it, then we try again.
///
/// See also: MonitorMain.client_out_of_date
///
/// (`Err` only for a timeout of the enclosing `Timeout.with_timeout`:
/// the socket's timeout, which the caller set.)
pub fn wait_on_server_restart(ic: &mut UnixStream) -> Result<(), ()> {
    let mut c = [0u8; 1];
    loop {
        match ic.read(&mut c) {
            Ok(0) => return Ok(()),
            Ok(_) => {}
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            // Server has exited and hung up on us (`End_of_file`,
            // `Sys_error _`)
            Err(e) if !crate::rt::protocol::is_timeout(&e) => return Ok(()),
            Err(_) => return Err(()),
        }
    }
}

pub fn get_sockaddr(config: &MonitorConfig) -> String {
    socket::make_valid_socket_path(&config.socket_file)
}

/// What interrupts the `do_` of a `Timeout.with_timeout`.
enum Interrupt {
    /// The deadline passed.
    Timeout,
    /// `Unix.Unix_error`
    Unix(std::io::Error, &'static str),
    /// Another exception, which nothing here catches.
    Raise(UncaughtReadError),
}

fn of_read_error(e: ReadError) -> Interrupt {
    match e {
        ReadError::Unix(e) if crate::rt::protocol::is_timeout(&e) => Interrupt::Timeout,
        ReadError::Unix(e) => Interrupt::Unix(e, "read"),
        e => Interrupt::Raise(crate::rt::protocol::uncaught_read_error(e)),
    }
}

fn of_write_error(e: std::io::Error) -> Interrupt {
    if crate::rt::protocol::is_timeout(&e) {
        Interrupt::Timeout
    } else {
        Interrupt::Unix(e, "write")
    }
}

/// Consume sequence of Prehandoff messages.
fn consume_prehandoff_messages(
    ic: &mut UnixStream,
) -> Result<Result<ServerSpecificFiles, ConnectionError>, Interrupt> {
    let m: prehandoff::Msg = read_value(ic).map_err(of_read_error)?;
    match m {
        prehandoff::Msg::Sentinel(server_specific_files) => Ok(Ok(server_specific_files)),
        prehandoff::Msg::ServerDormantConnectionsLimitReached => {
            eprint!(
                "Connections limit on dormant server reached. Be patient waiting for a server to be started."
            );
            Ok(Err(ConnectionError::ServerDormant))
        }
        prehandoff::Msg::ServerNotAliveDormant(_) => {
            // `Client_messages.waiting_for_server_to_be_started_doc` is
            // `""` (`stubs/client_messages.ml`).
            eprint!("Waiting for a server to be started...{}\n", "");
            consume_prehandoff_messages(ic)
        }
        prehandoff::Msg::ServerDiedConfigChange => {
            eprint!(
                "Last server exited due to config change. Please re-run client to force discovery of the correct version of the client."
            );
            Ok(Err(ConnectionError::ServerDied))
        }
        prehandoff::Msg::ServerDied(prehandoff::ExitStatus { status, was_oom }) => {
            match (was_oom, status) {
                (true, _) => eprint!("Last server killed by OOM Manager.\n"),
                (false, crate::rt::ocaml_unix::ProcessStatus::WExited(exit_code)) => {
                    eprint!("Last server exited with code: {}.\n", exit_code)
                }
                (false, crate::rt::ocaml_unix::ProcessStatus::WSignaled(signal)) => {
                    eprint!("Last server killed by signal: {}.\n", signal)
                }
                (false, crate::rt::ocaml_unix::ProcessStatus::WStopped(signal)) => {
                    eprint!("Last server stopped by signal: {}.\n", signal)
                }
            }
            // Monitor will exit now that it has provided a client with a reason
            // for the last server dying. Wait for the Monitor to exit.
            wait_on_server_restart(ic).map_err(|()| Interrupt::Timeout)?;
            Ok(Err(ConnectionError::ServerDied))
        }
    }
}

/// The `do_` of `connect_to_monitor`'s `Timeout.with_timeout`.
fn connect_to_monitor_do(
    phase: &mut ConnectFailurePhase,
    deadline: &Deadline,
    tracker: connection_tracker::T,
    terminate_monitor_on_version_mismatch: bool,
    is_stop: bool,
    config: &MonitorConfig,
) -> Result<
    Result<(UnixStream, UnixStream, connection_tracker::T), ConnectionError>,
    Interrupt,
> {
    // 1. open the socket
    *phase = ConnectFailurePhase::ConnectOpenSocket;
    let sockaddr = get_sockaddr(config);
    let mut ic = crate::rt::protocol::open_connection(&sockaddr, deadline).map_err(|e| {
        if crate::rt::protocol::is_timeout(&e) {
            Interrupt::Timeout
        } else {
            Interrupt::Unix(e, "connect")
        }
    })?;
    deadline.apply(&ic).map_err(|_| Interrupt::Timeout)?;
    let mut oc = ic.try_clone().map_err(|e| Interrupt::Unix(e, "dup"))?;
    let tracker = connection_tracker::track(Key::ClientOpenedSocket, None, None, None, None, tracker);

    // 2. send version, followed by newline
    *phase = ConnectFailurePhase::ConnectSendVersion;
    let version_str = monitor_utils::version_payload::serialize(
        &tracker,
        terminate_monitor_on_version_mismatch,
        monitor_utils::terminate_other_implementation(
            terminate_monitor_on_version_mismatch,
            is_stop,
        ),
    );
    crate::rt::protocol::ocaml_frame::write_value(
        &mut oc,
        &crate::rt::ocaml_marshal::Value::string(version_str.as_bytes()),
    )
    .map_err(of_write_error)?;
    *phase = ConnectFailurePhase::ConnectSendNewline;
    {
        use std::io::Write;
        oc.write_all(b"\n").map_err(of_write_error)?;
    }
    let tracker = connection_tracker::track(Key::ClientSentVersion, None, None, None, None, tracker);

    // 3. wait for Connection_ok
    // timeout/exn -> Server_missing_exn/Monitor_connection_misc_exception
    *phase = ConnectFailurePhase::ConnectReceiveConnectionOk;
    let cstate: ConnectionState =
        crate::rt::protocol::ocaml_frame::read_connection_state(&mut ic).map_err(of_read_error)?;
    let tracker = connection_tracker::track(Key::ClientGotCstate, None, None, None, None, tracker);

    // 4. return Ok
    match cstate {
        ConnectionState::ConnectionOk | ConnectionState::ConnectionOkV2(_) => {
            Ok(Ok((ic, oc, tracker)))
        }
        ConnectionState::BuildIdMismatch => {
            wait_on_server_restart(&mut ic).map_err(|()| Interrupt::Timeout)?;
            Ok(Err(ConnectionError::BuildIdMismatchedMonitorWillTerminate(None)))
        }
        ConnectionState::BuildIdMismatchEx(mismatch_info) => {
            wait_on_server_restart(&mut ic).map_err(|()| Interrupt::Timeout)?;
            Ok(Err(ConnectionError::BuildIdMismatchedMonitorWillTerminate(
                Some(mismatch_info),
            )))
        }
        ConnectionState::BuildIdMismatchV3(mismatch_info, mismatch_payload) => {
            let monitor_will_terminate =
                match monitor_utils::mismatch_payload::deserialize(&mismatch_payload)
                    .map_err(Interrupt::Raise)?
                {
                    Err(msg) => {
                        hh_logger::log(&format!(
                            "Unparseable response from monitor - {}\n{}",
                            msg, mismatch_payload
                        ));
                        true
                    }
                    Ok(monitor_utils::mismatch_payload::T {
                        monitor_will_terminate,
                    }) => monitor_will_terminate,
                };
            if monitor_will_terminate {
                wait_on_server_restart(&mut ic).map_err(|()| Interrupt::Timeout)?;
                Ok(Err(ConnectionError::BuildIdMismatchedMonitorWillTerminate(
                    Some(mismatch_info),
                )))
            } else {
                Ok(Err(ConnectionError::BuildIdMismatchedClientMustTerminate(
                    mismatch_info,
                )))
            }
        }
    }
}

/// (`log_on_slow_connect` defaults to `false`, and nothing passes it:
/// see the module documentation of `rt::protocol`.) On success the
/// socket's timeouts are those of `timeout`; the caller changes them.
///
/// The exceptions that OCaml does not catch here (a read error other
/// than a `Unix_error`, such as `End_of_file` when the other end closes
/// before it answers) are the outer `Err` (`UncaughtReadError`).
pub fn connect_to_monitor(
    tracker: connection_tracker::T,
    timeout: isize,
    terminate_monitor_on_version_mismatch: bool,
    config: &MonitorConfig,
) -> Result<
    Result<(UnixStream, UnixStream, connection_tracker::T), ConnectionError>,
    UncaughtReadError,
> {
    connect_to_monitor_inner(tracker, timeout, terminate_monitor_on_version_mismatch, false, config)
}

/// [`connect_to_monitor`]; `is_stop` for `connect_and_shut_down`, which
/// asks a monitor of the other implementation to terminate too
/// (`monitor_utils::terminate_other_implementation`).
fn connect_to_monitor_inner(
    tracker: connection_tracker::T,
    timeout: isize,
    terminate_monitor_on_version_mismatch: bool,
    is_stop: bool,
    config: &MonitorConfig,
) -> Result<
    Result<(UnixStream, UnixStream, connection_tracker::T), ConnectionError>,
    UncaughtReadError,
> {
    // There are some pathological scenarios concerned with high volumes of requests.
    // (See `monitor_connection.ml`.)
    let mut phase = ConnectFailurePhase::ConnectOpenSocket;
    let deadline = Deadline::in_seconds(timeout as f64);
    // Note: Timeout.with_timeout is accomplished internally by an exception;
    // hence, our "try/with exn ->" catch-all must be outside with_timeout.
    // (`finally`: the socket closes when it is dropped.)
    Ok(match connect_to_monitor_do(
        &mut phase,
        &deadline,
        tracker,
        terminate_monitor_on_version_mismatch,
        is_stop,
        config,
    ) {
        Ok(res) => res,
        Err(Interrupt::Timeout) => Err(ConnectionError::ConnectToMonitorFailure(
            ConnectToMonitorFailure {
                server_exists: server_exists(&config.lock_file),
                failure_phase: phase,
                failure_reason: ConnectFailureReason::ConnectTimeout,
            },
        )),
        Err(Interrupt::Unix(e, fun_name)) => {
            let e = exception::wrap(UnixError(e, fun_name));
            Err(ConnectionError::ConnectToMonitorFailure(
                ConnectToMonitorFailure {
                    server_exists: server_exists(&config.lock_file),
                    failure_phase: phase,
                    failure_reason: ConnectFailureReason::ConnectException(e),
                },
            ))
        }
        Err(Interrupt::Raise(e)) => {
            return Err(e);
        }
    })
}

/// The outer `Err` is an exception that OCaml raises out of
/// `connect_and_shut_down` (an uncaught read error of
/// `connect_to_monitor`, or a failed write of `SHUT_DOWN`): its only
/// caller, `Client_stop.nice_kill`, catches every exception.
pub fn connect_and_shut_down(
    tracker: connection_tracker::T,
    root: &path::T,
) -> Result<Result<ShutdownResult, ConnectionError>, UncaughtReadError> {
    let config = hh_monitor_config(root);
    let (ic, mut oc, tracker) = match connect_to_monitor_inner(tracker, 3, true, true, &config)? {
        Ok(conn) => conn,
        Err(e) => return Ok(Err(e)),
    };
    // The OCaml never closes the channels of this connection (a channel
    // that the GC collects keeps its descriptor open): the socket stays
    // open until the client exits, which shows in the descriptor number
    // `hh_client restart` gives the server it starts next
    // (`--waiting-client 9`, not 8). So the socket (`ic`) is leaked
    // here too; `oc` is a duplicate the OCaml does not have, and is
    // closed.
    let mut ic = std::mem::ManuallyDrop::new(ic);
    log("send_shutdown", &tracker);
    if let Err(e) = write_value(&mut oc, &monitor_rpc::Command::ShutDown(tracker)) {
        return Err(UncaughtReadError(ocaml_unix::unix_error_to_string(
            &e, "write", "",
        )));
    }
    let on_timeout = || {
        if server_exists(&config.lock_file) {
            Ok(ShutdownResult::ShutdownUnverified)
        } else {
            Err(ConnectionError::ConnectToMonitorFailure(
                ConnectToMonitorFailure {
                    server_exists: false,
                    failure_phase: ConnectFailurePhase::ConnectSendShutdown,
                    failure_reason: ConnectFailureReason::ConnectTimeout,
                },
            ))
        }
    };
    // `Timeout.with_timeout ~timeout:3`
    let deadline = Deadline::in_seconds(3.);
    if deadline.apply(&ic).is_err() {
        return Ok(on_timeout());
    }
    Ok(match wait_on_server_restart(&mut ic) {
        Ok(()) => Ok(ShutdownResult::ShutdownVerified),
        Err(()) => on_timeout(),
    })
}

/// The exceptions that OCaml does not catch here are the outer `Err`
/// (`UncaughtReadError`): they skip the logging, as in OCaml.
pub fn connect_once(
    tracker: connection_tracker::T,
    timeout: isize,
    terminate_monitor_on_version_mismatch: bool,
    root: &path::T,
    handoff_options: monitor_rpc::HandoffOptions,
) -> Result<
    Result<(UnixStream, UnixStream, ServerSpecificFiles), ConnectionError>,
    UncaughtReadError,
> {
    let config = hh_monitor_config(root);
    let t_start = ocaml_unix::gettimeofday();
    let log_tracker = tracker.clone();
    let result = (|| {
        let tracker = connection_tracker::track(
            Key::ClientStartConnect,
            Some(t_start),
            None,
            None,
            None,
            tracker,
        );
        let (mut ic, mut oc, tracker) = match connect_to_monitor(
            tracker,
            timeout,
            terminate_monitor_on_version_mismatch,
            &config,
        )? {
            Ok(conn) => conn,
            Err(e) => return Ok(Err(e)),
        };
        let tracker =
            connection_tracker::track(Key::ClientReadyToSendHandoff, None, None, None, None, tracker);
        if let Err(e) = write_value(
            &mut oc,
            &monitor_rpc::Command::HandoffToServer(tracker, handoff_options),
        ) {
            return Err(crate::rt::protocol::uncaught_write_error(e));
        }
        let elapsed_t = (ocaml_unix::gettimeofday() - t_start) as isize;
        let timeout = std::cmp::max(timeout - elapsed_t, 1);
        let deadline = Deadline::in_seconds(timeout as f64);
        let res = match deadline.apply(&ic) {
            Err(_) => Err(Interrupt::Timeout),
            Ok(()) => consume_prehandoff_messages(&mut ic),
        };
        Ok(match res {
            Ok(Ok(server_specific_files)) => {
                crate::rt::protocol::clear_timeouts(&ic);
                Ok((ic, oc, server_specific_files))
            }
            Ok(Err(e)) => Err(e),
            Err(Interrupt::Timeout) => Err(ConnectionError::ServerDormantOutOfRetries),
            // `Timeout.with_timeout` catches nothing else.
            Err(Interrupt::Unix(e, fun_name)) => {
                return Err(crate::rt::protocol::UncaughtReadError(ocaml_unix::unix_error_to_string(
                    &e, fun_name, "",
                )));
            }
            Err(Interrupt::Raise(e)) => return Err(e),
        })
    })()?;
    // oops too heavy
    match &result {
        Ok(_) => {
            log("CLIENT_CONNECT_ONCE", &log_tracker);
            // `Hack_event_logger.client_connect_once ~t_start`: a no-op
            // in the OSS build.
        }
        Err(e) => {
            let (reason, _telemetry) = monitor_utils::connection_error_to_telemetry(e);
            log(&format!("CLIENT_CONNECT_ONCE {}", reason), &log_tracker);
            // `Hack_event_logger.client_connect_once_failure ~t_start
            // reason telemetry`: a no-op in the OSS build.
        }
    }
    Ok(result)
}
