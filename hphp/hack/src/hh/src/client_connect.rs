// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_connect.ml`. See `hh/PORTING.md`.
//!
//! The connection goes over the socket protocol of `crate::rt::protocol`
//! (design 7.5), whose `monitor_connection` stands for OCaml's
//! `Monitor_connection` and keeps its results (`Monitor_utils.connection_error`),
//! so that the decisions here (retry, autostart, the messages and exit codes)
//! are OCaml's.
//!
//! - `Lwt` is gone: the functions block. `Lwt_utils.select` is a `poll` of
//!   the socket.
//! - The exceptions that OCaml lets through to the callers are
//!   [`ClientConnectError`]s: `Exit_status.Exit_with` (returned after the
//!   message on stderr, as in OCaml), the read and write errors that OCaml
//!   does not catch here (a read error other than the end of the stream:
//!   `crate::rt::protocol::UncaughtReadError`), and the
//!   `Done_or_retry.Two_retries_in_a_row` of [`rpc_with_retry`].
//! - The `rec connect` and `wait_for_server_message` loop instead of calling
//!   themselves (OCaml's calls are tail calls).
//! - `Hack_event_logger` calls (`client_connect_autostart`,
//!   `client_established_connection`, `server_hung_up`) are no-ops in the
//!   OSS build (`stubs/logging/hack_event_logger.ml`) and are not made.
//! - `Unix.time` (whole seconds) is [`unix_time`].

use std::os::unix::net::UnixStream;
use std::sync::Arc;

use crate::build_id;
use crate::client_start;
use crate::connection_tracker;
use crate::connection_tracker::Key;
use crate::exit_status;
use crate::exit_status::ExitWith;
use crate::hh_logger;
use crate::path;
use crate::rt::ocaml_sys;
use crate::rt::ocaml_unix;
use crate::rt::protocol;
use crate::rt::protocol::ReadError;
use crate::rt::protocol::monitor_connection;
use crate::rt::protocol::monitor_rpc;
use crate::rt::protocol::monitor_utils;
use crate::rt::protocol::monitor_utils::ConnectToMonitorFailure;
use crate::rt::protocol::monitor_utils::ConnectionError;
use crate::server_command_types;
use crate::server_command_types::CmdMetadata;
use crate::server_command_types::CommandResult;
use crate::server_command_types::ConnectionType;
use crate::server_command_types::MessageType;
use crate::server_command_types::ResultOf;
use crate::server_command_types::ServerSpecificFiles;
use crate::server_command_types::done_or_retry;
use crate::server_command_types_utils;
use crate::server_progress;
use crate::telemetry;
use crate::utils;

/// `progress_callback: string option -> unit`
pub type ProgressCallback = Arc<dyn Fn(Option<String>) + Send + Sync>;

/// `Unix.time ()`: the time in whole seconds.
fn unix_time() -> f64 {
    ocaml_unix::gettimeofday().floor()
}

/// The exceptions that `connect`, `rpc` and their variants let through.
#[derive(Debug)]
pub enum ClientConnectError {
    /// `Exit_status.Exit_with`
    ExitWith(ExitWith),
    /// A read or write error that nothing catches
    UncaughtReadError(protocol::UncaughtReadError),
    /// `Done_or_retry.Two_retries_in_a_row`
    TwoRetriesInARow(done_or_retry::Two_retries_in_a_row),
}

impl From<ExitWith> for ClientConnectError {
    fn from(e: ExitWith) -> Self {
        ClientConnectError::ExitWith(e)
    }
}

impl From<protocol::UncaughtReadError> for ClientConnectError {
    fn from(e: protocol::UncaughtReadError) -> Self {
        ClientConnectError::UncaughtReadError(e)
    }
}

impl From<client_start::ClientStartError> for ClientConnectError {
    fn from(e: client_start::ClientStartError) -> Self {
        match e {
            client_start::ClientStartError::ExitWith(e) => e.into(),
            client_start::ClientStartError::UncaughtReadError(e) => e.into(),
        }
    }
}

impl From<done_or_retry::Two_retries_in_a_row> for ClientConnectError {
    fn from(e: done_or_retry::Two_retries_in_a_row) -> Self {
        ClientConnectError::TwoRetriesInARow(e)
    }
}

/// `raise (Exit_status.Exit_with es)`
fn exit_with<A>(es: exit_status::T) -> Result<A, ClientConnectError> {
    Err(ClientConnectError::ExitWith(ExitWith(es)))
}

/// `log ?tracker ?connection_log_id s`
fn log(tracker: Option<&connection_tracker::T>, connection_log_id: Option<&str>, s: &str) {
    let id = match tracker {
        Some(tracker) => Some(connection_tracker::log_id(tracker)),
        None => connection_log_id.map(|s| s.to_string()),
    };
    match id {
        Some(id) => hh_logger::log(&format!("[{}] [client-connect] {}", id, s)),
        None => hh_logger::log(&format!("[client-connect] {}", s)),
    }
}

/// Used solely as an argument to [connect]
#[derive(Clone)]
pub struct Env {
    pub root: path::T,
    pub from: String,
    pub abort_on_distc_failure: bool,
    pub autostart: bool,
    pub force_dormant_start: bool,
    pub deadline: Option<f64>,
    pub no_load: bool,
    pub watchman_debug_logging: bool,
    pub progress_callback: ProgressCallback,
    pub do_post_handoff_handshake: bool,
    pub ignore_hh_version: bool,
    pub save_64bit: Option<String>,
    pub save_human_readable_64bit_dep_map: Option<String>,
    pub saved_state_ignore_hhconfig: bool,
    pub mini_state: Option<String>,
    pub use_priority_pipe: bool,
    pub prechecked: Option<bool>,
    pub config: Vec<(String, String)>,
    pub custom_hhi_path: Option<String>,
    pub custom_telemetry_data: Vec<(String, String)>,
    pub allow_non_opt_build: bool,
    pub preexisting_warnings: bool,
}

/// [connect] returns this record, which contains everything needed for subsequent rpc calls
pub struct Conn {
    pub connection_log_id: String,
    pub t_connected_to_monitor: f64,
    pub t_received_hello: f64,
    pub t_sent_connection_type: f64,
    /// `(ic, oc)`: the socket, twice.
    pub channels: (UnixStream, UnixStream),
    pub server_specific_files: ServerSpecificFiles,
    pub conn_progress_callback: ProgressCallback,
    pub conn_root: path::T,
    pub conn_deadline: Option<f64>,
    pub conn_abort_on_distc_failure: bool,
    pub from: String,
}

fn read_and_show_progress(progress_callback: &ProgressCallback) {
    let server_progress::T { message, .. } = server_progress::read();
    progress_callback(Some(message));
}

fn check_for_deadline(
    progress_callback: &ProgressCallback,
    deadline_opt: Option<f64>,
) -> Result<(), ClientConnectError> {
    let now = unix_time();
    match deadline_opt {
        Some(deadline) if now > deadline => {
            log(
                None,
                None,
                &format!(
                    "check_for_deadline expired: {} > {}",
                    utils::timestring(now),
                    utils::timestring(deadline)
                ),
            );
            // must hide the spinner prior to printing output or exiting
            progress_callback(None);
            eprint!("\nError: hh_client hit timeout, giving up!\n");
            exit_with(exit_status::T::OutOfTime)
        }
        _ => Ok(()),
    }
}

fn server_exit_should_abort(abort_on_distc_failure: bool, es: &exit_status::T) -> bool {
    match es {
        exit_status::T::DistcFailed => abort_on_distc_failure,
        exit_status::T::FailedToLoadShouldAbort | exit_status::T::ServerNonOptBuildMode => true,
        _ => false,
    }
}

pub mod for_test {
    pub fn server_exit_should_abort(
        abort_on_distc_failure: bool,
        es: &crate::exit_status::T,
    ) -> bool {
        super::server_exit_should_abort(abort_on_distc_failure, es)
    }
}

/// `Poly.( = ) msg expected`: structural equality (a `Response` by its
/// encoding).
fn poly_equal_message_type(a: &MessageType<CommandResult>, b: &MessageType<CommandResult>) -> bool {
    match (a, b) {
        (MessageType::Hello, MessageType::Hello)
        | (MessageType::MonitorFailedToHandoff, MessageType::MonitorFailedToHandoff)
        | (MessageType::Ping, MessageType::Ping) => true,
        (MessageType::Response(..), MessageType::Response(..)) => {
            protocol::wire::encode(a) == protocol::wire::encode(b)
        }
        _ => false,
    }
}

/// The exception that ends `wait_for_server_message`'s `try`: an
/// `End_of_file`, or the inline `M.Monitor_failed_to_handoff`.
enum HungUp {
    EndOfFile,
    MonitorFailedToHandoff,
}

/// The `with` of `wait_for_server_message`: the server hung up. Returns the
/// `Exit_with` it raises.
fn server_hung_up(
    abort_on_distc_failure: bool,
    exn: HungUp,
    server_specific_files: &ServerSpecificFiles,
    progress_callback: &ProgressCallback,
) -> ClientConnectError {
    let finale_data = exit_status::get_finale_data(&server_specific_files.server_finale_file);
    let _client_exn = match exn {
        HungUp::EndOfFile => "End_of_file",
        HungUp::MonitorFailedToHandoff => "Client_connect.M.Monitor_failed_to_handoff",
    };
    // must hide the spinner prior to printing output or exiting
    progress_callback(None);
    // stderr
    let msg = match (&exn, &finale_data) {
        (HungUp::MonitorFailedToHandoff, None) => "Hack server is too busy.".to_string(),
        (_, None) => "Hack server disconnected suddenly. It might have crashed.".to_string(),
        (_, Some(finale_data)) => format!(
            "Hack server disconnected suddenly [{}]\n{}",
            exit_status::show(&finale_data.exit_status),
            finale_data.msg.as_deref().unwrap_or("")
        ),
    };
    eprint!("{}\n", msg);
    // exception, caught by hh_client.ml and logged.
    // In most cases we report that find_hh.sh should simply retry the failed command.
    let should_abort = match &finale_data {
        Some(d) => server_exit_should_abort(abort_on_distc_failure, &d.exit_status),
        None => false,
    };
    let external_exit_status = if should_abort {
        exit_status::T::ServerHungUpShouldAbort(finale_data.map(Box::new))
    } else {
        exit_status::T::ServerHungUpShouldRetry(finale_data.map(Box::new))
    };
    // log to telemetry: `Hack_event_logger.server_hung_up ~external_exit_status
    // ~server_exit_status ~client_exn ~client_stack ~server_stack ~server_msg`,
    // a no-op in the OSS build.
    ClientConnectError::ExitWith(ExitWith(external_exit_status))
}

/// Sleeps until the server sends a message. While waiting, prints out spinner
/// and progress information using the argument callback.
#[allow(clippy::too_many_arguments)]
fn wait_for_server_message(
    abort_on_distc_failure: bool,
    connection_log_id: &str,
    expected_message: Option<&MessageType<CommandResult>>,
    ic: &UnixStream,
    deadline: Option<f64>,
    server_specific_files: &ServerSpecificFiles,
    progress_callback: &ProgressCallback,
    _root: &path::T,
) -> Result<MessageType<CommandResult>, ClientConnectError> {
    loop {
        check_for_deadline(progress_callback, deadline)?;
        let readable = match protocol::select_readable(ic, 1.0) {
            Ok(readable) => readable,
            Err(e) => return Err(protocol::uncaught_read_error(ReadError::Unix(e)).into()),
        };
        if !readable {
            read_and_show_progress(progress_callback);
            continue;
        }
        let mut ic_ref = ic;
        let msg: MessageType<CommandResult> = match protocol::read_value(&mut ic_ref) {
            Ok(msg) => msg,
            Err(ReadError::EndOfFile) => {
                return Err(server_hung_up(
                    abort_on_distc_failure,
                    HungUp::EndOfFile,
                    server_specific_files,
                    progress_callback,
                ));
            }
            // Not caught here in OCaml.
            Err(e) => return Err(protocol::uncaught_read_error(e).into()),
        };
        let (is_ping, is_handoff_failed) = match msg {
            MessageType::Ping => (true, false),
            MessageType::MonitorFailedToHandoff => (false, true),
            _ => (false, false),
        };
        let matches_expected = match expected_message {
            None => true,
            Some(expected) => poly_equal_message_type(&msg, expected),
        };
        if is_handoff_failed {
            return Err(server_hung_up(
                abort_on_distc_failure,
                HungUp::MonitorFailedToHandoff,
                server_specific_files,
                progress_callback,
            ));
        } else if matches_expected && !is_ping {
            log(
                None,
                Some(connection_log_id),
                &format!(
                    "wait_for_server_message: got expected {}",
                    server_command_types_utils::debug_describe_message_type(&msg)
                ),
            );
            progress_callback(None);
            return Ok(msg);
        } else {
            log(
                None,
                Some(connection_log_id),
                &format!(
                    "wait_for_server_message: didn't want {}",
                    server_command_types_utils::debug_describe_message_type(&msg)
                ),
            );
            if !is_ping {
                read_and_show_progress(progress_callback);
            }
        }
    }
}

fn wait_for_server_hello(
    abort_on_distc_failure: bool,
    connection_log_id: &str,
    ic: &UnixStream,
    deadline: Option<f64>,
    server_specific_files: &ServerSpecificFiles,
    progress_callback: &ProgressCallback,
    root: &path::T,
) -> Result<(), ClientConnectError> {
    let _: MessageType<CommandResult> = wait_for_server_message(
        abort_on_distc_failure,
        connection_log_id,
        Some(&MessageType::Hello),
        ic,
        deadline,
        server_specific_files,
        progress_callback,
        root,
    )?;
    Ok(())
}

fn describe_mismatch(mismatch_info: Option<&monitor_utils::BuildMismatchInfo>) -> String {
    match mismatch_info {
        None => String::new(),
        Some(monitor_utils::BuildMismatchInfo {
            existing_version,
            existing_argv,
            existing_launch_time,
            ..
        }) => format!(
            "  hh_server '{}', version '{}', launched {}\n  hh_client '{}', version '{}', launched [just now]\n",
            existing_argv.join(" "),
            existing_version,
            utils::timestring(*existing_launch_time),
            ocaml_sys::argv().join(" "),
            build_id::build_revision()
        ),
    }
}

/// [connect] essentially connects to the monitor which will hand off that
/// connection to the server, then wait for 'hello' from the server.
///
/// (OCaml's `let rec connect env start_time`, whose calls to itself are a
/// loop here.)
fn connect_from(env: &Env, start_time: f64) -> Result<Conn, ClientConnectError> {
    let mut env = env.clone();
    let mut start_time = start_time;
    loop {
        let Env {
            root,
            from,
            abort_on_distc_failure,
            autostart,
            force_dormant_start,
            deadline,
            no_load,
            preexisting_warnings,
            watchman_debug_logging,
            progress_callback,
            do_post_handoff_handshake,
            ignore_hh_version,
            save_64bit,
            save_human_readable_64bit_dep_map,
            saved_state_ignore_hhconfig,
            mini_state,
            use_priority_pipe,
            prechecked,
            config,
            custom_hhi_path,
            custom_telemetry_data,
            allow_non_opt_build,
        } = &env;
        progress_callback(Some("connecting".to_string()));
        check_for_deadline(progress_callback, *deadline)?;
        let handoff_options = monitor_rpc::HandoffOptions {
            force_dormant_start: *force_dormant_start,
            pipe_type: if *force_dormant_start {
                monitor_rpc::PipeType::ForceDormantStartOnly
            } else if *use_priority_pipe {
                monitor_rpc::PipeType::Priority
            } else {
                monitor_rpc::PipeType::Default
            },
        };
        let tracker = connection_tracker::create();
        let connection_log_id = connection_tracker::log_id(&tracker);
        // We'll attempt to connect, with timeout up to [deadline]. Effectively, the
        // unix process list will be where we store our (unbounded) queue of incoming client requests,
        // each of them waiting for the monitor's incoming socket to become available; if there's a backlog
        // in the monitor->server pipe and the monitor's incoming queue is full, then the monitor's incoming
        // socket will become only available after the server has finished a request, and the monitor gets to
        // send its next handoff, and take the next item off its incoming queue.
        // If the deadline is infinite, I arbitrarily picked 60s as the timeout coupled with "will retry..."
        // if it timed out. That's because I distrust infinite timeouts, just in case something got stuck for
        // unknown causes, and maybe retrying the connection attempt will get it unstuck? -- a sort of
        // "try turning it off then on again". This timeout must be comfortably longer than the monitor's
        // own 30s timeout in MonitorMain.hand_off_client_connection_wrapper to handoff to the server;
        // if it were shorter, then the monitor's incoming queue would be entirely full of requests that
        // were all stale by the time it got to handle them.
        let timeout: isize = match deadline {
            None => 60,
            Some(deadline) => std::cmp::max(1, (deadline - ocaml_unix::gettimeofday()) as isize),
        };
        log(
            None,
            Some(&connection_log_id),
            &format!(
                "ClientConnect.connect: attempting MonitorConnection.connect_once ({}s)",
                timeout
            ),
        );
        let terminate_monitor_on_version_mismatch = *autostart;
        // We've put our money where our mouth is -- only ask the monitor to terminate
        // if we're prepared to start it again afterwards!
        let conn = monitor_connection::connect_once(
            tracker.clone(),
            timeout,
            terminate_monitor_on_version_mismatch,
            root,
            handoff_options,
        )?;

        let t_connected_to_monitor = ocaml_unix::gettimeofday();
        match conn {
            Ok((ic, oc, server_specific_files)) => {
                log(
                    None,
                    Some(&connection_log_id),
                    "ClientConnect.connect: successfully connected to monitor.",
                );
                if *do_post_handoff_handshake {
                    wait_for_server_hello(
                        *abort_on_distc_failure,
                        &connection_log_id,
                        &ic,
                        *deadline,
                        &server_specific_files,
                        progress_callback,
                        root,
                    )?
                }
                let t_received_hello = ocaml_unix::gettimeofday();
                progress_callback(Some("connected".to_string()));
                return Ok(Conn {
                    connection_log_id: connection_tracker::log_id(&tracker),
                    t_connected_to_monitor,
                    t_received_hello,
                    // placeholder, until we actually send it
                    t_sent_connection_type: 0.,
                    channels: (ic, oc),
                    server_specific_files,
                    conn_progress_callback: progress_callback.clone(),
                    conn_root: root.clone(),
                    conn_deadline: *deadline,
                    conn_abort_on_distc_failure: *abort_on_distc_failure,
                    from: from.clone(),
                });
            }
            Err(e) => {
                // must hide the spinner prior to printing output or exiting
                progress_callback(None);
                match e {
                    ConnectionError::ServerDied
                    | ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
                        server_exists: true,
                        ..
                    }) => {
                        log(
                            Some(&tracker),
                            None,
                            "connect: no response yet from server; will retry...",
                        );
                        std::thread::sleep(std::time::Duration::from_millis(100));
                        // `connect env start_time`
                        continue;
                    }
                    ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
                        server_exists: false,
                        ..
                    }) => {
                        log(
                            Some(&tracker),
                            None,
                            &format!("connect: autostart={}", autostart),
                        );
                        if *autostart {
                            // `Hack_event_logger.client_connect_autostart ()`: a
                            // no-op in the OSS build.
                            client_start::start_server(&client_start::Env {
                                root: root.clone(),
                                from: from.clone(),
                                no_load: *no_load,
                                watchman_debug_logging: *watchman_debug_logging,
                                silent: false,
                                exit_on_failure: false,
                                ignore_hh_version: *ignore_hh_version,
                                save_64bit: save_64bit.clone(),
                                save_human_readable_64bit_dep_map: save_human_readable_64bit_dep_map
                                    .clone(),
                                saved_state_ignore_hhconfig: *saved_state_ignore_hhconfig,
                                prechecked: *prechecked,
                                mini_state: mini_state.clone(),
                                config: config.clone(),
                                custom_hhi_path: custom_hhi_path.clone(),
                                custom_telemetry_data: custom_telemetry_data.clone(),
                                allow_non_opt_build: *allow_non_opt_build,
                                preexisting_warnings: *preexisting_warnings,
                            })?;
                            // `connect env start_time`
                            continue;
                        } else {
                            eprint!(
                                "Error: no hh_server running. Either start hh_server yourself or run hh_client without --autostart-server false\n"
                            );
                            return exit_with(exit_status::T::NoServerRunningShouldRetry);
                        }
                    }
                    ConnectionError::ServerDormantOutOfRetries => {
                        eprint!(
                            "Ran out of retries while waiting for Mercurial to finish rebase. Starting the server in the middle of rebase is strongly not recommended and you should first finish the rebase before retrying. If you really know what you're doing, maybe try --force-dormant-start true\n"
                        );
                        return exit_with(exit_status::T::OutOfRetries);
                    }
                    ConnectionError::ServerDormant => {
                        eprint!(
                            "Error: No server running and connection limit reached for waiting on next server to be started. Please wait patiently. If you really know what you're doing, maybe try --force-dormant-start true\n"
                        );
                        return exit_with(exit_status::T::NoServerRunningShouldRetry);
                    }
                    ConnectionError::BuildIdMismatchedClientMustTerminate(mismatch_info)
                        if monitor_utils::is_other_implementation(&mismatch_info) =>
                    {
                        // (Not in the OCaml: the monitor of the other
                        // implementation, which this client does not replace:
                        // `monitor_utils::cross_implementation_policy`.)
                        eprint!(
                            "{}",
                            monitor_utils::other_implementation_message(
                                &mismatch_info,
                                &path::to_string(root)
                            )
                        );
                        return exit_with(exit_status::T::BuildIdMismatch);
                    }
                    ConnectionError::BuildIdMismatchedClientMustTerminate(mismatch_info) => {
                        eprint!(
                            "Error: version mismatch.\nUse --autostart-server true if you want it to restart.\n{}",
                            describe_mismatch(Some(&mismatch_info))
                        );
                        return exit_with(exit_status::T::BuildIdMismatch);
                    }
                    ConnectionError::BuildIdMismatchedMonitorWillTerminate(mismatch_info_opt) => {
                        eprint!(
                            "hh_server's version doesn't match the client's, so it will exit.\n{}",
                            describe_mismatch(mismatch_info_opt.as_ref())
                        );
                        if *autostart {
                            // The new server is definitely not running yet, adjust the
                            // start time and deadline to absorb the server startup time.
                            let now = unix_time();
                            let deadline = deadline.map(|d| d + (now - start_time));
                            eprint!("Going to launch a new one.\n");
                            // `connect { env with deadline } now`
                            env = Env {
                                deadline,
                                ..env.clone()
                            };
                            start_time = now;
                            continue;
                        } else {
                            return exit_with(exit_status::T::BuildIdMismatch);
                        }
                    }
                }
            }
        }
    }
}

/// Establishes a connection to the server: (1) connects to the monitor and exchanges
/// messages, (2) has the monitor handoff the FD to the server, (3) if env.do_post_handoff_handshake
/// is true then also waits for the server to send back ServerCommandTypes.Hello.
pub fn connect(env: &Env) -> Result<Conn, ClientConnectError> {
    let start_time = unix_time();
    let conn = connect_from(env, start_time)?;
    // `Hack_event_logger.client_established_connection start_time`: a no-op
    // in the OSS build.
    if env.do_post_handoff_handshake {
        // read by [ServerClientProvider.read_connection_type_from_channel]
        let mut oc = &conn.channels.1;
        if let Err(e) = protocol::write_value(&mut oc, &ConnectionType::NonPersistent) {
            return Err(protocol::uncaught_write_error(e).into());
        }
    }
    Ok(Conn {
        t_sent_connection_type: ocaml_unix::gettimeofday(),
        ..conn
    })
}

/// Sends a request to the server, and waits for the response
///
/// (`'a` is the type the caller names, as OCaml infers it: see
/// `server_command_types::ResultOf`. A response for another command than
/// `cmd` is a bug of the server: a `failwith`.)
pub fn rpc<A: ResultOf>(
    conn: &Conn,
    desc: &str,
    cmd: server_command_types::T,
) -> Result<(A, telemetry::T), ClientConnectError> {
    let Conn {
        connection_log_id,
        t_connected_to_monitor,
        t_received_hello,
        t_sent_connection_type,
        channels: (ic, oc),
        server_specific_files,
        conn_progress_callback: progress_callback,
        conn_root,
        conn_deadline: deadline,
        conn_abort_on_distc_failure: abort_on_distc_failure,
        from,
    } = conn;
    let t_ready_to_send_cmd = ocaml_unix::gettimeofday();
    let metadata = CmdMetadata {
        from: from.clone(),
        desc: desc.to_string(),
    };
    let cmd_name = server_command_types_utils::debug_describe_t(&cmd);
    let mut oc = oc;
    if let Err(e) = protocol::write_value(&mut oc, &(metadata, cmd)) {
        return Err(protocol::uncaught_write_error(e).into());
    }
    let t_sent_cmd = ocaml_unix::gettimeofday();
    let res = wait_for_server_message(
        *abort_on_distc_failure,
        connection_log_id,
        None,
        ic,
        *deadline,
        server_specific_files,
        progress_callback,
        conn_root,
    )?;
    match res {
        MessageType::Response(response, tracker) => {
            let tracker = connection_tracker::track(
                Key::ClientReadyToSendCmd,
                Some(t_ready_to_send_cmd),
                None,
                None,
                None,
                tracker,
            );
            let tracker =
                connection_tracker::track(Key::ClientSentCmd, Some(t_sent_cmd), None, None, None, tracker);
            let tracker =
                connection_tracker::track(Key::ClientReceivedResponse, None, None, None, None, tracker);
            // now we can fill in missing information in tracker, which we couldn't fill in earlier
            // because we'd already transferred ownership of the tracker to the monitor...
            let tracker = connection_tracker::track(
                Key::ClientConnectedToMonitor,
                Some(*t_connected_to_monitor),
                None,
                None,
                None,
                tracker,
            );
            let tracker = connection_tracker::track(
                Key::ClientReceivedHello,
                Some(*t_received_hello),
                None,
                None,
                None,
                tracker,
            );
            let tracker = connection_tracker::track(
                Key::ClientSentConnectionType,
                Some(*t_sent_connection_type),
                None,
                None,
                None,
                tracker,
            );
            let telemetry = connection_tracker::get_telemetry(&tracker);
            let response_name = server_command_types::command_result_name(&response);
            match A::of_command_result(response) {
                Some(response) if response_name == cmd_name => Ok((response, telemetry)),
                _ => panic!(
                    "Failure: unexpected {} response to {}",
                    response_name, cmd_name
                ),
            }
        }
        MessageType::Hello => panic!("Failure: unexpected 'hello' RPC response"),
        MessageType::Ping => panic!("Failure: unexpected 'ping' RPC response"),
        MessageType::MonitorFailedToHandoff => {
            panic!("Failure: unexpected 'monitor_failed_to_handoff' RPC response")
        }
    }
}

/// A handful of rpc commands (find-refs, go-to-impl, refactor), for grotty implementation
/// details, don't return an answer but instead return the message "Done_or_retry.Retry"
/// indicating that ClientConnect should make the exact same request a second time.
/// Which, through this API, it does.
pub fn rpc_with_retry<A>(
    mut conn_f: impl FnMut() -> Result<Conn, ClientConnectError>,
    desc: &str,
    cmd: server_command_types::T,
) -> Result<A, ClientConnectError>
where
    done_or_retry::T<A>: ResultOf,
{
    done_or_retry::call(|| {
        let conn = conn_f()?;
        let (result, _telemetry): (done_or_retry::T<A>, _) = rpc(&conn, desc, cmd.clone())?;
        Ok(result)
    })
}

/// For batch commands, retries each result in turn
pub fn rpc_with_retry_list<A>(
    mut conn_f: impl FnMut() -> Result<Conn, ClientConnectError>,
    desc: &str,
    cmd: server_command_types::T,
) -> Result<Vec<A>, ClientConnectError>
where
    Vec<done_or_retry::T<A>>: ResultOf,
{
    // `call_here s = Done_or_retry.call ~f:(fun () -> Lwt.return s)`: the
    // same `s` each time (a `Retry` stays one).
    let call_here = |s: done_or_retry::T<A>| -> Result<A, ClientConnectError> {
        let mut s = Some(s);
        done_or_retry::call(move || Ok(s.take().unwrap_or(done_or_retry::T::Retry)))
    };
    let conn = conn_f()?;
    let (job_list, _): (Vec<done_or_retry::T<A>>, _) = rpc(&conn, desc, cmd)?;
    job_list.into_iter().map(call_here).collect()
}

#[cfg(test)]
pub(crate) mod tests;
