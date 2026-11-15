// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/monitor_main.ml`.
//!
//! The server monitor is the parent process for a server. It
//! listens to a socket for client connections and passes the connections
//! to the server and serves the following objectives:
//!
//! 1) Readily accepts client connections
//! 2) Confirms a Build ID match (killing itself and the server quickly
//!    on mismatch)
//! 3) Hands the client connection to the daemon server
//! 4) Tracks when the server process crashes or OOMs and echos
//!    its fate to the next client.
//!
//! # Differences from the OCaml
//!
//! - The OCaml threads an immutable `env` through the `env msg_update`
//!   monad (`(env, env * string) result`) and raises exceptions. Here the
//!   env is a `&mut Env`, the `Error (env, msg)` of the monad is an
//!   `Ok(Err(msg))`, and an exception is an `Err(`[`Exn`]`)`. The only
//!   difference: an update the OCaml makes to its env before an exception
//!   is lost there and kept here (its mutable parts, the purgatory queue
//!   and the sent fds, behave the same either way).
//! - Client connections are `UnixStream`s, closed when dropped. Where the
//!   OCaml drops an fd without closing it (a malformed version payload), it
//!   is leaked here too.
//! - The socket frames are those of `rt::protocol` (the version payload is
//!   a frame, with no newline after it).

// ~~ Exceptions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

use std::collections::VecDeque;
use std::mem::ManuallyDrop;
use std::os::fd::AsRawFd;
use std::os::fd::FromRawFd;
use std::os::fd::RawFd;
use std::os::unix::net::UnixListener;
use std::os::unix::net::UnixStream;
use std::sync::Mutex;

use crate::config_file;
use crate::connection_tracker;
use crate::connection_tracker::Key;
use crate::exception;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::informant;
use crate::libancillary;
use crate::lock;
use crate::monitor_rpc;
use crate::monitor_utils;
use crate::monitor_utils::ConnectionState;
use crate::monitor_utils::MonitorConfig;
use crate::prehandoff;
use crate::relative_path;
use crate::rt::ocaml_unix;
use crate::rt::ocaml_unix::ProcessStatus;
use crate::rt::ocaml_unix::UnixError;
use crate::rt::protocol;
use crate::rt::protocol::ReadError;
use crate::server_command_types::CommandResult;
use crate::server_command_types::MessageType;
use crate::server_args;
use crate::server_controller;
use crate::server_files;
use crate::server_process::ProcessData;
use crate::server_process::ServerProcess;
use crate::server_process::show_server_process;
use crate::server_progress;
use crate::telemetry;
use crate::utils;

/// The exceptions the monitor's loop raises and catches.
pub enum Exn {
    /// `Unix.Unix_error (err, fun_name, arg)`
    Unix(std::io::Error, &'static str, String),
    /// `Send_fd_failure status`
    SendFdFailure(i32),
    /// `Failure msg`
    Failure(String),
    /// `Assert_failure`, as `Printexc.to_string` shows it.
    AssertFailure(String),
    /// Another exception (a read error of `Marshal_tools`, a `Yojson` type
    /// error), as `Printexc.to_string` shows it.
    Other(String),
}

impl std::fmt::Debug for Exn {
    /// `Printexc.to_string`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Exn::Unix(e, fun_name, arg) => {
                f.write_str(&ocaml_unix::unix_error_to_string(e, fun_name, arg))
            }
            Exn::SendFdFailure(status) => write!(f, "Monitor_main.Send_fd_failure({})", status),
            Exn::Failure(msg) => write!(f, "Failure({})", crate::rt::ocaml_printf::sprintf_s(msg)),
            Exn::AssertFailure(s) | Exn::Other(s) => f.write_str(s),
        }
    }
}

impl Exn {
    fn errno(&self) -> Option<i32> {
        match self {
            Exn::Unix(e, _, _) => e.raw_os_error(),
            _ => None,
        }
    }

    fn of_read_error(e: ReadError) -> Exn {
        match e {
            ReadError::Unix(e) => Exn::Unix(e, "read", String::new()),
            e => Exn::Other(protocol::read_error_to_string(&e, "read")),
        }
    }

    fn of_write_error(e: std::io::Error) -> Exn {
        Exn::Unix(e, "write", String::new())
    }
}

type Res<A> = Result<A, Exn>;

/// An update of the env (`env msg_update`): `Err(msg)` is the monad's
/// `Error (env, msg)` (the env itself is the caller's).
pub type MsgUpdate = Result<(), String>;

fn log(s: &str, tracker: &connection_tracker::T) {
    hh_logger::log(&format!("[{}] {}", connection_tracker::log_id(tracker), s))
}

/// If you try to Unix.close the same FD twice, you get EBADF the second time.
/// Ocaml doesn't have a linear type system, so it's too hard to be crisp about
/// when we hand off responsibility for closing the FD. Therefore: we call this
/// method to ensure an FD is closed, and we just silently gobble up the EBADF
/// if someone else already closed it. (Here an fd is a `UnixStream`, closed
/// once, when it is dropped.)
fn ensure_fd_closed(fd: UnixStream) {
    drop(fd)
}

/// A descriptor of the monitor's (the pipes to the server), to read and
/// write without taking it over.
fn borrow_fd(fd: RawFd) -> ManuallyDrop<UnixStream> {
    // SAFETY: the descriptor stays open while it is used; `ManuallyDrop`
    // never closes it.
    ManuallyDrop::new(unsafe { UnixStream::from_raw_fd(fd) })
}

// ~~ Sent_fds_collector ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// This module is to help using Unix "sendmsg" to handoff the client FD
/// to the server. It's not entirely clear whether it's safe for us in the
/// monitor to close the FD immediately after calling sendmsg, or whether
/// we must wait until the server has actually received the FD upon recvmsg.
///
/// (See `monitor_main.ml`: the monitor waits to close the FD until after
/// the server has read it, which the server says by writing the highest
/// handoff number it has received to the "server_receipt_to_monitor_file".)
pub mod sent_fds_collector {
    use super::*;

    /// [sequence_number] is a monotonically increasing integer to identify which
    /// handoff message has been sent from monitor to server. The first sequence
    /// number is number 1.
    static SEQUENCE_NUMBER: Mutex<isize> = Mutex::new(0);

    pub fn get_and_increment_sequence_number() -> isize {
        let mut n = SEQUENCE_NUMBER.lock().unwrap_or_else(|e| e.into_inner());
        *n += 1;
        *n
    }

    struct HandedOffFdToClose {
        tracker: connection_tracker::T,
        fd: UnixStream,
        /// A unique number incremented for each client socket handoff from monitor to server.
        /// Useful to correlate monitor and server logs.
        m2s_sequence_number: isize,
    }

    static HANDED_OFF_FDS_TO_CLOSE: Mutex<Vec<HandedOffFdToClose>> = Mutex::new(Vec::new());

    pub fn cleanup_fd(tracker: connection_tracker::T, m2s_sequence_number: isize, fd: UnixStream) {
        // (`::` onto the list: the newest first.)
        HANDED_OFF_FDS_TO_CLOSE
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(
                0,
                HandedOffFdToClose {
                    tracker,
                    fd,
                    m2s_sequence_number,
                },
            );
    }

    pub fn collect_fds(sequence_receipt_high_water_mark: isize) {
        // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.

        // Note: this code is a filter with a side-effect. The side-effect is to
        // close FDs that have received their read-receipts. The filter will retain
        // the FDs that haven't yet received their read-receipts.
        let mut fds = HANDED_OFF_FDS_TO_CLOSE
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let all = std::mem::take(&mut *fds);
        for h in all {
            if h.m2s_sequence_number > sequence_receipt_high_water_mark {
                fds.push(h)
            } else {
                log(
                    &format!(
                        "closing client socket from handoff #{} upon receipt of #{}",
                        h.m2s_sequence_number, sequence_receipt_high_water_mark
                    ),
                    &h.tracker,
                );
                ensure_fd_closed(h.fd);
            }
        }
    }

    /// This must be called in all paths where the server has died, so that the client can
    /// properly see an EOF on its FD.
    pub fn collect_all_fds() {
        collect_fds(isize::MAX)
    }

    /// How many are waiting for their receipt (tests).
    pub fn count() -> usize {
        HANDED_OFF_FDS_TO_CLOSE
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .len()
    }
}

// ~~ The env ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub struct Env {
    pub informant: informant::T,
    pub server: ServerProcess,
    pub server_start_options: server_controller::ServerStartOptions,
    pub allow_restart_from_precomputed_saved_state: bool,
    /// How many times have we tried to relaunch it?
    pub retries: isize,
    pub sql_retries: isize,
    pub watchman_retries: isize,
    pub edenfs_watcher_retries: isize,
    pub max_purgatory_clients: isize,
    /// Version of this running server, as specified in the config file.
    pub current_version: config_file::Version,
    /// After sending a Server_not_alive_dormant during Prehandoff,
    /// clients are put here waiting for a server to come alive, at
    /// which point they get pushed through the rest of prehandoff and
    /// then sent to the living server.
    pub purgatory_clients:
        VecDeque<(connection_tracker::T, monitor_rpc::HandoffOptions, UnixStream)>,
    /// Whether to ignore hh version mismatches
    pub ignore_hh_version: bool,
}

/// The constructor of a `server_process` (to match on while the env
/// changes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    NotYetStarted,
    Alive,
    DiedUnexpectedly,
    DiedConfigChanged,
}

fn kind(s: &ServerProcess) -> Kind {
    match s {
        ServerProcess::NotYetStarted => Kind::NotYetStarted,
        ServerProcess::Alive(_) => Kind::Alive,
        ServerProcess::DiedUnexpectedly(_, _) => Kind::DiedUnexpectedly,
        ServerProcess::DiedConfigChanged => Kind::DiedConfigChanged,
    }
}

/// Use this as the only way to change server.
/// It closes all outstanding FDs. That's needed so clients know that they can give up.
fn set_server(env: &mut Env, new_server: ServerProcess) {
    sent_fds_collector::collect_all_fds();
    env.server = new_server;
}

/// This FD will be passed to a server process, so avoid using Ocaml's
/// channels which have built-in buffering. (Frames are written whole.)
fn msg_to_channel<V: serde::Serialize>(fd: &mut UnixStream, msg: &V) -> Res<()> {
    protocol::write_value(fd, msg).map_err(Exn::of_write_error)
}

// ~~ Signals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn setup_handler_for_signals(handler: crate::rt::ocaml_sys::Handler, signals: &[i32]) {
    for signal in signals {
        crate::rt::ocaml_sys::set_signal(
            *signal,
            crate::rt::ocaml_sys::SignalBehavior::SignalHandle(handler.clone()),
        );
    }
}

fn setup_autokill_server_on_exit(process: &ProcessData) {
    let pid = process.pid;
    let res = std::panic::catch_unwind(|| {
        setup_handler_for_signals(
            std::sync::Arc::new(move |_| {
                hh_logger::log("Got an exit signal. Killing server and exiting.");
                server_controller::kill_server_pid(false, pid);
                exit::exit(None, None, None, None, exit_status::T::Interrupted)
            }),
            &[libc::SIGINT, libc::SIGQUIT, libc::SIGTERM, libc::SIGHUP],
        )
    });
    if res.is_err() {
        hh_logger::log("Failed to set signal handler")
    }
}

/// `Unix.select [socket] [] [] 1.0`: whether a client is waiting.
fn sleep_and_check(socket: &UnixListener) -> Res<bool> {
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    poll_one(socket.as_raw_fd(), libc::POLLIN, 1.0).map_err(|e| Exn::Unix(e, "select", String::new()))
}

/// `poll` of one descriptor for `events`, at most `timeout` seconds.
fn poll_one(fd: RawFd, events: libc::c_short, timeout: f64) -> std::io::Result<bool> {
    let deadline = ocaml_unix::gettimeofday() + timeout;
    loop {
        let mut pfd = libc::pollfd {
            fd,
            events,
            revents: 0,
        };
        let ms = ((deadline - ocaml_unix::gettimeofday()) * 1000.).max(0.) as libc::c_int;
        // SAFETY: one valid `pollfd`.
        let ret = unsafe { libc::poll(&mut pfd, 1, ms) };
        if ret < 0 {
            let e = std::io::Error::last_os_error();
            if e.raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            return Err(e);
        }
        return Ok(ret > 0);
    }
}

// ~~ Starting and killing servers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn start_server(
    informant_managed: bool,
    options: &server_controller::ServerStartOptions,
    exit_status: Option<isize>,
) -> Res<ServerProcess> {
    let server_process = server_controller::start_server(informant_managed, exit_status, options)
        .map_err(|e| Exn::Unix(e, "create_process", String::new()))?;
    setup_autokill_server_on_exit(&server_process);
    Ok(ServerProcess::Alive(server_process))
}

fn maybe_start_first_server(
    options: &server_controller::ServerStartOptions,
    informant: &informant::T,
) -> Res<ServerProcess> {
    if informant::should_start_first_server(informant) {
        hh_logger::log("Starting first server");
        // `Hack_event_logger.starting_first_server ()`: a no-op in OSS.
        start_server(informant::is_managing(informant), options, None)
    } else {
        hh_logger::log("Not starting first server. Starting will be triggered by informant later.");
        Ok(ServerProcess::NotYetStarted)
    }
}

fn kill_server_with_check_and_wait(server: &ServerProcess) -> Res<()> {
    sent_fds_collector::collect_all_fds();
    match server {
        ServerProcess::Alive(server) => {
            let start_t = ocaml_unix::gettimeofday();
            loop {
                server_controller::kill_server(
                    ocaml_unix::gettimeofday() - start_t >= 4.0,
                    server,
                );
                let success = server_controller::wait_for_server_exit(
                    ocaml_unix::gettimeofday() + 2.0,
                    server,
                )
                .map_err(|e| Exn::Unix(e, "waitpid", String::new()))?;
                if success {
                    let _: f64 = hh_logger::log_duration(
                        None,
                        None,
                        "typechecker has exited. Time since first signal: ",
                        start_t,
                    );
                    return Ok(());
                }
            }
        }
        _ => Ok(()),
    }
}

/// Reads current hhconfig contents from disk and returns true if the
/// version specified in there matches our currently running version.
fn is_config_version_matching(env: &Env) -> bool {
    let filename = relative_path::from_root(config_file::FILE_PATH_RELATIVE_TO_REPO_ROOT);
    let config = config_file::parse_hhconfig(&relative_path::to_absolute(&filename));
    let new_version = crate::config_file_version::parse_version(
        crate::config_file_common::getters::string_opt("version", &config).as_deref(),
    );
    0 == crate::config_file_version::compare_versions(&env.current_version, &new_version)
}

/// Actually starts a new server.
fn start_new_server(env: &mut Env, exit_status: Option<isize>) -> Res<MsgUpdate> {
    let informant_managed = informant::is_managing(&env.informant);
    let new_server = start_server(informant_managed, &env.server_start_options, exit_status)?;
    set_server(env, new_server);
    env.retries += 1;
    Ok(Ok(()))
}

/// Kill the server (if it's running) and restart it - maybe. Obeying the rules
/// of state transitions. See docs on the ServerProcess.server_process ADT for
/// state transitions.
fn kill_and_maybe_restart_server(env: &mut Env, exit_status: Option<isize>) -> Res<MsgUpdate> {
    hh_logger::log(&format!(
        "kill_and_maybe_restart_server (env.server={})",
        show_server_process(&env.server)
    ));
    // We're going to collect all FDs right here and now. This will be done again below,
    // in [kill_server_with_check_and_wait], but Informant.reinit might take too long or might throw.
    sent_fds_collector::collect_all_fds();
    // Iff we just restart and keep going, we risk
    // Changed_merge_base eventually arriving and restarting the already started server
    // for no reason. Re-issuing merge base query here should bring the Monitor and Server
    // understanding of current revision to be the same
    kill_server_with_check_and_wait(&env.server)?;

    let version_matches = is_config_version_matching(env);
    if server_controller::is_saved_state_precomputed(&env.server_start_options)
        && !env.allow_restart_from_precomputed_saved_state
    {
        let reason = "Not restarting server as requested, server was launched using a precomputed saved-state. Exiting monitor";
        hh_logger::log(reason);
        // `Hack_event_logger.refuse_to_restart_server`: a no-op in OSS.
        let _ = version_matches;
        exit::exit(
            None,
            None,
            None,
            None,
            exit_status::T::NotRestartingServerWithPrecomputedSavedState,
        )
    }
    if server_controller::is_saved_state_precomputed(&env.server_start_options) {
        let server_start_options =
            server_args::clear_precomputed_saved_state(env.server_start_options.clone());
        hh_logger::log(
            "Discarding precomputed saved-state for server restart; using configured saved-state loading",
        );
        env.server_start_options = server_start_options;
    }
    match (kind(&env.server), version_matches) {
        (Kind::DiedConfigChanged, _) => {
            // Now we can start a new instance safely.
            // See diagram on ServerProcess.server_process docs.
            start_new_server(env, exit_status)
        }
        (Kind::NotYetStarted | Kind::Alive | Kind::DiedUnexpectedly, false) => {
            // Can't start server instance. State goes to Died_config_changed
            // See diagram on ServerProcess.server_process docs.
            hh_logger::log(
                "Avoiding starting a new server because version in config no longer matches.",
            );
            set_server(env, ServerProcess::DiedConfigChanged);
            Ok(Ok(()))
        }
        (Kind::NotYetStarted | Kind::Alive | Kind::DiedUnexpectedly, true) => {
            // Start new server instance because config matches.
            // See diagram on ServerProcess.server_process docs.
            start_new_server(env, exit_status)
        }
    }
}

// ~~ Clients ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `read_version_string_then_newline`: the OCaml's frame (as the OCaml
/// client sends it, `rt::protocol::ocaml_frame`), then the newline (`Err` of
/// the inner result: "missing newline after version"). An OCaml string is
/// any bytes: one that is not UTF-8 is read lossily.
fn read_version_string_then_newline(fd: &mut UnixStream) -> Res<Result<String, String>> {
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    protocol::ocaml_frame::read_version(fd).map_err(Exn::of_read_error)
}

/// `hand_off_client_connection ~tracker ~agent_session_id server_fd
/// client_fd`: on failure, the exception and the client fd (not handed off).
fn hand_off_client_connection(
    tracker: &connection_tracker::T,
    agent_session_id: Option<String>,
    server_fd: RawFd,
    client_fd: UnixStream,
) -> Result<(), (Exn, UnixStream)> {
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    let m2s_sequence_number = sent_fds_collector::get_and_increment_sequence_number();
    let msg = monitor_rpc::MonitorToServerHandoffMsg {
        m2s_tracker: tracker.clone(),
        m2s_sequence_number,
        m2s_agent_session_id: agent_session_id,
    };
    if let Err(e) = msg_to_channel(&mut borrow_fd(server_fd), &msg) {
        return Err((e, client_fd));
    }
    log(
        &format!(
            "Handed off tracker to server (client socket handoff #{})",
            m2s_sequence_number
        ),
        tracker,
    );
    let status = libancillary::ancil_send_fd(server_fd, client_fd.as_raw_fd());
    if status == 0 {
        log(
            &format!(
                "Handed off client socket to server (handoff #{})",
                m2s_sequence_number
            ),
            tracker,
        );
        sent_fds_collector::cleanup_fd(tracker.clone(), m2s_sequence_number, client_fd);
        Ok(())
    } else {
        log(
            &format!(
                "Failed to handoff client socket to server (handoff #{})",
                m2s_sequence_number
            ),
            tracker,
        );
        Err((Exn::SendFdFailure(status), client_fd))
    }
}

/// Sends the client connection FD to the server process then closes the FD.
///
/// Backpressure: We have a timeout of 30s here to wait for the server to accept
/// the handoff. That timeout will be exceeded if monitor->server pipe has filled
/// up from previous requests and the server's current work item is costly. In this
/// case we'll give up on the handoff, and hh_client will fail with Server_hung_up_should_retry,
/// and find_hh.sh will retry with exponential backoff.
///
/// (See `monitor_main.ml` for the rest of the comment.)
fn hand_off_client_connection_wrapper(
    tracker: &connection_tracker::T,
    agent_session_id: Option<String>,
    server_fd: RawFd,
    client_fd: UnixStream,
) -> Res<()> {
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    let timeout = 30.0;
    let to_finally_close: Option<UnixStream> = match poll_one(server_fd, libc::POLLOUT, timeout) {
        Err(e) => {
            // `Unix.select` raised: the `finally` runs, then it propagates.
            finally_close(tracker, Some(client_fd))?;
            return Err(Exn::Unix(e, "select", String::new()));
        }
        Ok(false) => {
            log(
                &format!(
                    "Handoff FD timed out ({:.1}s): server's current iteration is taking longer than that, and its incoming pipe is full",
                    timeout
                ),
                tracker,
            );
            Some(client_fd)
        }
        Ok(true) => match hand_off_client_connection(tracker, agent_session_id, server_fd, client_fd)
        {
            Ok(()) => None,
            Err((e, client_fd)) if e.errno() == Some(libc::EPIPE) => {
                log(
                    "Handoff FD failed: server has closed its end of pipe (EPIPE), maybe due to large rebase or incompatible .hhconfig change or crash",
                    tracker,
                );
                Some(client_fd)
            }
            Err((e, client_fd)) => {
                let e = exception::wrap(e);
                log(
                    &format!("Handoff FD failed unexpectedly - {}", exception::to_string(&e)),
                    tracker,
                );
                // `Hack_event_logger.send_fd_failure e`: a no-op in OSS.
                Some(client_fd)
            }
        },
    };
    finally_close(tracker, to_finally_close)
}

/// The `~finally` of `hand_off_client_connection_wrapper`.
fn finally_close(tracker: &connection_tracker::T, to_finally_close: Option<UnixStream>) -> Res<()> {
    match to_finally_close {
        None => Ok(()),
        Some(mut client_fd) => {
            log("Sending Monitor_failed_to_handoff to client, and closing FD", tracker);
            msg_to_channel(
                &mut client_fd,
                &MessageType::<CommandResult>::MonitorFailedToHandoff,
            )?;
            ensure_fd_closed(client_fd);
            Ok(())
        }
    }
}

/// Send (possibly empty) sequences of messages before handing off to
/// server.
fn client_prehandoff(
    tracker: connection_tracker::T,
    is_purgatory_client: bool,
    env: &mut Env,
    handoff_options: monitor_rpc::HandoffOptions,
    mut client_fd: UnixStream,
) -> Res<MsgUpdate> {
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    match &env.server {
        ServerProcess::Alive(server) => {
            let server_fd = server.out_fds[&handoff_options.pipe_type];
            let t_ready = ocaml_unix::gettimeofday();
            let tracker =
                connection_tracker::track(Key::MonitorReady, Some(t_ready), None, None, None, tracker);
            // TODO: Send this to client so it is visible.
            log(
                &format!(
                    "Got {} request for typechecker. Prior request {:.1} seconds ago",
                    monitor_rpc::pipe_type_to_string(handoff_options.pipe_type),
                    t_ready - server.last_request_handoff.get()
                ),
                &tracker,
            );
            msg_to_channel(
                &mut client_fd,
                &prehandoff::Msg::Sentinel(server.server_specific_files.clone()),
            )?;
            let tracker = connection_tracker::track(
                Key::MonitorSentAckToClient,
                None,
                None,
                None,
                None,
                tracker,
            );
            hand_off_client_connection_wrapper(
                &tracker,
                handoff_options.agent_session_id.clone(),
                server_fd,
                client_fd,
            )?;
            server.last_request_handoff.set(ocaml_unix::gettimeofday().floor());
            Ok(Ok(()))
        }
        ServerProcess::DiedUnexpectedly(status, was_oom) => {
            // Server has died; notify the client
            msg_to_channel(
                &mut client_fd,
                &prehandoff::Msg::ServerDied(prehandoff::ExitStatus {
                    status: *status,
                    was_oom: *was_oom,
                }),
            )?;

            // Next client to connect starts a new server.
            exit::exit(None, None, None, None, exit_status::T::NoError)
        }
        ServerProcess::DiedConfigChanged => {
            if !is_purgatory_client {
                if let Err(msg) = kill_and_maybe_restart_server(env, None)? {
                    return Ok(Err(msg));
                }
                // Assert that the restart succeeded, and then push prehandoff through again.
                match &env.server {
                    ServerProcess::Alive(_) => {
                        // Server restarted. We want to re-run prehandoff, which will
                        // actually do the prehandoff this time.
                        client_prehandoff(
                            tracker,
                            is_purgatory_client,
                            env,
                            handoff_options,
                            client_fd,
                        )
                    }
                    ServerProcess::DiedUnexpectedly(_, _)
                    | ServerProcess::DiedConfigChanged
                    | ServerProcess::NotYetStarted => {
                        hh_logger::log(
                            "Unreachable state. Server should be alive after trying a restart from Died_config_changed state",
                        );
                        Err(Exn::Failure(
                            "Failed starting server transitioning off Died_config_changed state"
                                .to_string(),
                        ))
                    }
                }
            } else {
                msg_to_channel(&mut client_fd, &prehandoff::Msg::ServerDiedConfigChange)?;
                Ok(Ok(()))
            }
        }
        ServerProcess::NotYetStarted => {
            if handoff_options.force_dormant_start {
                msg_to_channel(
                    &mut client_fd,
                    &prehandoff::Msg::ServerNotAliveDormant(
                        "Warning - starting a server by force-dormant-start option...".to_string(),
                    ),
                )?;
                if let Err(msg) = kill_and_maybe_restart_server(env, None)? {
                    return Ok(Err(msg));
                }
            } else {
                msg_to_channel(
                    &mut client_fd,
                    &prehandoff::Msg::ServerNotAliveDormant(
                        "Server killed by informant. Waiting for next server...".to_string(),
                    ),
                )?;
            }
            if env.purgatory_clients.len() as isize >= env.max_purgatory_clients {
                msg_to_channel(
                    &mut client_fd,
                    &prehandoff::Msg::ServerDormantConnectionsLimitReached,
                )?;
                Ok(Ok(()))
            } else {
                env.purgatory_clients
                    .push_back((tracker, handoff_options, client_fd));
                Ok(Ok(()))
            }
        }
    }
}

fn handle_monitor_rpc(env: &mut Env, mut client_fd: UnixStream) -> Res<MsgUpdate> {
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    let cmd: monitor_rpc::Command =
        protocol::read_value(&mut client_fd).map_err(Exn::of_read_error)?;
    match cmd {
        monitor_rpc::Command::HandoffToServer(tracker, handoff_options) => {
            let tracker = connection_tracker::track(
                Key::MonitorReceivedHandoff,
                None,
                None,
                None,
                None,
                tracker,
            );
            client_prehandoff(tracker, false, env, handoff_options, client_fd)
        }
        monitor_rpc::Command::ShutDown(tracker) => {
            log("Got shutdown RPC. Shutting down.", &tracker);
            kill_server_with_check_and_wait(&env.server)?;
            exit::exit(None, None, None, None, exit_status::T::NoError)
        }
    }
}

/// `ack_and_handoff_client`, for a monitor of version `monitor_version`
/// (`Build_id.build_revision`; the tests give another).
fn ack_and_handoff_client_with_version(
    env: &mut Env,
    mut client_fd: UnixStream,
    monitor_version: &str,
) -> Res<MsgUpdate> {
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    let start_time = ocaml_unix::gettimeofday();
    let s = match read_version_string_then_newline(&mut client_fd)? {
        Ok(s) => s,
        Err(_err) => {
            // (OCaml returns the error without closing the fd.)
            std::mem::forget(client_fd);
            return Ok(Err("Malformed Build ID".to_string()));
        }
    };
    let payload = match monitor_utils::version_payload::deserialize(&s) {
        Ok(payload) => payload,
        Err(monitor_utils::version_payload::DeserializeError::Error(_err)) => {
            // (OCaml returns the error without closing the fd.)
            std::mem::forget(client_fd);
            return Ok(Err("Malformed Build ID".to_string()));
        }
        // `Yojson.Safe.Util.Type_error`, raised (not an `Error`).
        Err(monitor_utils::version_payload::DeserializeError::TypeError(exn)) => {
            return Err(Exn::Other(exn));
        }
    };
    let will_terminate = monitor_utils::monitor_will_terminate(&payload);
    let monitor_utils::version_payload::T {
        client_version,
        tracker_id,
        terminate_monitor_on_version_mismatch,
        ..
    } = payload;
    // (What a Rust client asks a Rust monitor is its own field: see
    // `version_payload::T`.)
    let client_is_rust = crate::build_id::is_rust_build_revision(&client_version);
    let terminate_monitor_on_version_mismatch = if client_is_rust {
        will_terminate
    } else {
        terminate_monitor_on_version_mismatch
    };
    hh_logger::log(&format!(
        "[{}] read_version: start_wait={}, client_version={}, monitor_version={}, monitor_ignore_hh_version={}, terminate_monitor_on_version_mismatch={}",
        tracker_id,
        utils::timestring(start_time),
        client_version,
        monitor_version,
        env.ignore_hh_version,
        terminate_monitor_on_version_mismatch
    ));
    // Version is okay if *monitor* was started with --ignore-hh-version, or versions match.
    let is_version_ok = env.ignore_hh_version || client_version == monitor_version;
    if is_version_ok {
        let connection_state = ConnectionState::ConnectionOk;
        hh_logger::log(&format!(
            "[{}] sending {}",
            tracker_id,
            monitor_utils::show_connection_state(&connection_state)
        ));
        protocol::ocaml_frame::write_connection_state(&mut client_fd, &connection_state)
            .map_err(Exn::of_write_error)?;
        // following function returns [env msg_update] monad
        handle_monitor_rpc(env, client_fd)
    } else {
        let monitor_will_terminate = will_terminate;
        if monitor_will_terminate != terminate_monitor_on_version_mismatch {
            // (Not in the OCaml: a client of the other implementation.)
            hh_logger::log(&format!(
                "[{}] client of another implementation: monitor_will_terminate={} (cross-implementation policy {:?})",
                tracker_id,
                monitor_will_terminate,
                monitor_utils::cross_implementation_policy()
            ));
        }
        let connection_state = ConnectionState::BuildIdMismatchV3(
            monitor_utils::BuildMismatchInfo {
                existing_version: monitor_version.to_string(),
                ..monitor_utils::current_build_info()
            },
            monitor_utils::mismatch_payload::serialize(monitor_will_terminate),
        );
        hh_logger::log(&format!(
            "[{}] sending {}",
            tracker_id,
            monitor_utils::show_connection_state(&connection_state)
        ));
        if let Err(exn) =
            protocol::ocaml_frame::write_connection_state(&mut client_fd, &connection_state)
        {
            hh_logger::log(&format!("while sending, exn: {:?}", Exn::of_write_error(exn)));
        }
        if monitor_will_terminate {
            kill_server_with_check_and_wait(&env.server)?;
            exit::exit(None, None, None, None, exit_status::T::BuildIdMismatch)
        } else {
            hh_logger::log("Closing client_fd");
            close_after_client(client_fd);
            Ok(Ok(()))
        }
    }
}

/// Closes the connection of a client told `Build_id_mismatch_v3` (and that
/// the monitor will not terminate) once the client has closed its end, at
/// most a second later. (Not in the OCaml, which closes at once: on macOS
/// the OCaml client then fails its `Unix.shutdown_connection` with
/// `ENOTCONN` and exits `Uncaught_exception` instead of reporting the
/// mismatch, which an OCaml client meeting this monitor must report.)
fn close_after_client(client_fd: UnixStream) {
    let _ = poll_one(client_fd.as_raw_fd(), libc::POLLIN, 1.0);
    drop(client_fd)
}

fn ack_and_handoff_client(env: &mut Env, client_fd: UnixStream) -> Res<MsgUpdate> {
    ack_and_handoff_client_with_version(env, client_fd, &crate::build_id::build_revision())
}

fn push_purgatory_clients(env: &mut Env) -> Res<MsgUpdate> {
    // We create a queue and transfer all the purgatory clients to it before
    // processing to avoid repeatedly retrying the same client even after
    // an EBADF. Control flow is easier this way than trying to manage an
    // immutable env in the face of exceptions.
    let clients = std::mem::take(&mut env.purgatory_clients);
    let mut acc: MsgUpdate = Ok(());
    for (tracker, handoff_options, client_fd) in clients {
        if acc.is_err() {
            // (`env_accumulator >>= ...`: an `Error` goes through the rest
            // unchanged; their fds are dropped.)
            continue;
        }
        match client_prehandoff(tracker.clone(), true, env, handoff_options, client_fd) {
            Ok(res) => acc = res,
            Err(e) if matches!(e.errno(), Some(libc::EPIPE) | Some(libc::EBADF)) => {
                log("Purgatory client disconnected. Dropping.", &tracker);
            }
            Err(e) => return Err(e),
        }
    }
    Ok(acc)
}

fn maybe_push_purgatory_clients(env: &mut Env) -> Res<MsgUpdate> {
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    match (kind(&env.server), env.purgatory_clients.len()) {
        (Kind::Alive, 0) => Ok(Ok(())),
        (Kind::DiedConfigChanged, _) => {
            // These clients are waiting for a server to be started. But this Monitor
            // is waiting for a new client to connect (which confirms to us that we
            // are running the correct version of the Monitor). So let them know
            // that they might want to do something.
            push_purgatory_clients(env)
        }
        (Kind::Alive, _) => push_purgatory_clients(env),
        (Kind::NotYetStarted, _) | (Kind::DiedUnexpectedly, _) => Ok(Ok(())),
    }
}

// ~~ The status of the server ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Kill command from client is handled by server server, so the monitor
/// needs to check liveness of the server process to know whether
/// to stop itself.
fn update_status_(
    env: &mut Env,
    monitor_config: &MonitorConfig,
) -> Res<(Option<isize>, informant::ServerState)> {
    let _ = monitor_config;
    if let ServerProcess::Alive(process) = &env.server {
        let (pid, proc_stat) = server_controller::wait_pid(process)
            .map_err(|e| Exn::Unix(e, "waitpid", String::new()))?;
        match (pid, proc_stat) {
            (0, _) => {
                // "pid=0" means the pid we waited for (i.e. process) hasn't yet died/stopped
            }
            (_, ProcessStatus::WExited(0)) => {
                // "pid<>0, WEXITED 0" means the process had a clean exit
                set_server(env, ServerProcess::DiedUnexpectedly(proc_stat, false));
            }
            (_, _) => {
                // this case is any kind of unexpected exit
                let is_oom = match proc_stat {
                    ProcessStatus::WExited(code)
                        if code == exit_status::exit_code(&exit_status::T::OutOfSharedMemory)
                            || code == exit_status::exit_code(&exit_status::T::WorkerOomed) =>
                    {
                        true
                    }
                    // (The name of the process: `hh_server` and the suffix of
                    // this executable, `hh_server_rust` as it is installed.)
                    _ => crate::sys_utils::check_dmesg_for_oom(
                        process.pid,
                        &format!("hh_server{}", crate::rt::exe_suffix::executable_suffix()),
                    )
                    .map_err(|e| match e {
                        crate::sys_utils::ExecReadLinesError::Unix(UnixError(e, f, a)) => Exn::Unix(e, f, a),
                        crate::sys_utils::ExecReadLinesError::AssertFailure(m) => Exn::AssertFailure(m),
                    })?,
                };
                let (exit_type, exit_code) = crate::exit_status::unpack(proc_stat);
                let time_taken = ocaml_unix::gettimeofday().floor() - process.start_t;
                let _ = time_taken;
                server_progress::write(
                    None,
                    None,
                    &format!(
                        "writing crash log (pid: {}, hint: `hh --logname` OR `bunnylol coredumper`)",
                        pid
                    ),
                );
                let telemetry = telemetry::create();
                let telemetry = telemetry::int_("pid", pid as isize, telemetry);
                let telemetry = telemetry::string_(None, "unix_exit_type", &exit_type, telemetry);
                let telemetry = telemetry::int_("unix_exit_code", exit_code, telemetry);
                let telemetry = telemetry::bool_("is_oom", is_oom, telemetry);
                let (telemetry, exit_status) = match exit_status::get_finale_data(
                    &process.server_specific_files.server_finale_file,
                ) {
                    None => (telemetry, None),
                    Some(exit_status::FinaleData {
                        exit_status,
                        msg,
                        stack: utils::Callstack(stack),
                        telemetry: finale_telemetry,
                    }) => {
                        let telemetry = telemetry::string_(
                            None,
                            "exit_status",
                            &exit_status::show(&exit_status),
                            telemetry,
                        );
                        let telemetry = telemetry::string_opt(None, "msg", msg.as_deref(), telemetry);
                        let telemetry = telemetry::string_(None, "stack", &stack, telemetry);
                        let telemetry = telemetry::object_opt("data", finale_telemetry, telemetry);
                        (telemetry, Some(exit_status))
                    }
                };
                hh_logger::log(&format!(
                    "TYPECHECKER_EXIT {}",
                    telemetry::to_string(None, &telemetry)
                ));
                // `Hack_event_logger.typechecker_exit`: a no-op in OSS.
                server_progress::write(
                    None,
                    Some(server_progress::Disposition::DStopped),
                    &exit_status
                        .as_ref()
                        .map_or("server stopped".to_string(), exit_status::show),
                );
                set_server(env, ServerProcess::DiedUnexpectedly(proc_stat, is_oom));
            }
        }
    }

    let (exit_status, server_state) = match &env.server {
        ServerProcess::Alive(_) => (None, informant::ServerState::ServerAlive),
        ServerProcess::DiedUnexpectedly(ProcessStatus::WExited(c), _) => {
            (Some(*c), informant::ServerState::ServerDead)
        }
        ServerProcess::NotYetStarted => (None, informant::ServerState::ServerNotYetStarted),
        ServerProcess::DiedUnexpectedly(
            ProcessStatus::WSignaled(_) | ProcessStatus::WStopped(_),
            _,
        )
        | ServerProcess::DiedConfigChanged => (None, informant::ServerState::ServerDead),
    };
    Ok((exit_status, server_state))
}

fn is_exit(exit_status: Option<isize>, statuses: &[exit_status::T]) -> bool {
    match exit_status {
        Some(c) => statuses.iter().any(|s| c == exit_status::exit_code(s)),
        None => false,
    }
}

fn update_status(env: &mut Env, monitor_config: &MonitorConfig) -> Res<MsgUpdate> {
    use exit_status::T::*;
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    let (exit_status, server_state) = update_status_(env, monitor_config)?;
    let informant_report = informant::report(&env.informant, server_state);
    let is_watchman_fresh_instance = is_exit(exit_status, &[WatchmanFreshInstance]);
    let is_watchman_failed = is_exit(exit_status, &[WatchmanFailed]);
    let is_edenfs_watcher_lost_changes = is_exit(exit_status, &[EdenfsWatcherLostChanges]);
    let is_edenfs_watcher_failed = is_exit(exit_status, &[EdenfsWatcherFailed]);
    let is_edenfs_watcher_eden_shutting_down =
        is_exit(exit_status, &[EdenfsWatcherEdenShuttingDown]);
    let is_config_changed = is_exit(exit_status, &[HhconfigChanged]);
    let is_heap_stale = is_exit(exit_status, &[FileProviderStale, DeclNotFound]);
    let is_depgraph_unavailable = is_exit(exit_status, &[DepgraphUnavailable]);
    let is_sql_assertion_failure = is_exit(
        exit_status,
        &[SqlAssertionFailure, SqlCantopen, SqlCorrupt, SqlMisuse],
    );
    let is_worker_error = is_exit(
        exit_status,
        &[WorkerNotFoundException, WorkerBusy, WorkerFailedToSendJob],
    );
    let is_decl_heap_elems_bug = is_exit(exit_status, &[DeclHeapElemsBug]);
    let is_big_rebase = is_exit(exit_status, &[BigRebaseDetected]);
    let max_watchman_retries = 3;
    let max_edenfs_watcher_retries = 3;
    let max_sql_retries = 3;
    let (reason, msg_update): (Option<String>, MsgUpdate) =
        match (informant_report, kind(&env.server)) {
            (informant::Report::MoveAlong, Kind::DiedConfigChanged) => {
                // No "reason" here -- we're on an "inner-loop non-failure" path
                (None, Ok(()))
            }
            (informant::Report::RestartServer, Kind::DiedConfigChanged) => {
                let reason = "Ignoring Informant directed restart - waiting for next client connection to verify server version first";
                (Some(reason.to_string()), Ok(()))
            }
            (informant::Report::RestartServer, _) => {
                let reason = "Informant directed server restart. Restarting server.";
                (
                    Some(reason.to_string()),
                    kill_and_maybe_restart_server(env, exit_status)?,
                )
            }
            (informant::Report::MoveAlong, _) => {
                if (is_watchman_failed || is_watchman_fresh_instance)
                    && env.watchman_retries < max_watchman_retries
                {
                    let reason = format!(
                        "Watchman died. Restarting hh_server (attempt: {})",
                        env.watchman_retries + 1
                    );
                    env.watchman_retries += 1;
                    set_server(env, ServerProcess::NotYetStarted);
                    (Some(reason), Ok(()))
                } else if (is_edenfs_watcher_failed
                    || is_edenfs_watcher_eden_shutting_down
                    || is_edenfs_watcher_lost_changes)
                    && env.edenfs_watcher_retries < max_edenfs_watcher_retries
                {
                    let reason = format!(
                        "Edenfs_watcher died. Restarting hh_server (attempt: {})",
                        env.edenfs_watcher_retries + 1
                    );
                    env.edenfs_watcher_retries += 1;
                    set_server(env, ServerProcess::NotYetStarted);
                    (Some(reason), Ok(()))
                } else if is_decl_heap_elems_bug {
                    let reason = "hh_server died due to Decl_heap_elems_bug. Restarting";
                    set_server(env, ServerProcess::NotYetStarted);
                    (Some(reason.to_string()), Ok(()))
                } else if is_worker_error {
                    let reason = "hh_server died due to worker error. Restarting";
                    set_server(env, ServerProcess::NotYetStarted);
                    (Some(reason.to_string()), Ok(()))
                } else if is_config_changed {
                    let reason = "hh_server died from hh config change. Restarting";
                    set_server(env, ServerProcess::NotYetStarted);
                    (Some(reason.to_string()), Ok(()))
                } else if is_heap_stale {
                    let reason =
                        "Several large rebases caused shared heap to be stale. Restarting";
                    set_server(env, ServerProcess::NotYetStarted);
                    (Some(reason.to_string()), Ok(()))
                } else if is_depgraph_unavailable {
                    let reason = "hh_server dependency graph became unavailable. Restarting";
                    set_server(env, ServerProcess::NotYetStarted);
                    (Some(reason.to_string()), Ok(()))
                } else if is_big_rebase {
                    let reason = "Server exited because of big rebase. Restarting";
                    set_server(env, ServerProcess::NotYetStarted);
                    (Some(reason.to_string()), Ok(()))
                } else if is_sql_assertion_failure && env.sql_retries < max_sql_retries {
                    let reason = format!(
                        "Sql failed. Restarting hh_server in fresh mode (attempt: {})",
                        env.sql_retries + 1
                    );
                    env.sql_retries += 1;
                    set_server(env, ServerProcess::NotYetStarted);
                    (Some(reason), Ok(()))
                } else {
                    // No reason here, on the inner-loop non-failure path.
                    (None, Ok(()))
                }
            }
        };
    if let Some(reason) = reason {
        hh_logger::log(&format!("MONITOR_UPDATE_STATUS {}", reason));
        // The telemetry of `Hack_event_logger.monitor_update_status` (the
        // exit status, the report, the states of the server before and
        // after): a no-op in OSS.
    }
    Ok(msg_update)
}

// ~~ The loop ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn check_and_run_loop_(
    env: &mut Env,
    monitor_config: &MonitorConfig,
    socket: &UnixListener,
) -> Res<MsgUpdate> {
    // WARNING! Don't use the (slow) HackEventLogger here, in the inner loop non-failure path.
    // That's because HackEventLogger for the monitor is synchronous and takes 50ms/call.
    // But the monitor's non-failure inner loop must handle hundres of clients per second
    let lock_file = &monitor_config.lock_file;
    if !lock::grab(lock_file) {
        // e.g. (conjectured) tmpcleaner deletes the .lock file we have a lock on, and another instance of hh_server
        // starts up and acquires its own lock on a lockfile by the same name; our "Lock.grab" will return false because
        // we're unable to grab a lock on the file currently under pathname "lock_file".
        // Or, maybe users just manually deleted the file.
        hh_logger::log("Lost lock; terminating.\n");
        // `Hack_event_logger.lock_stolen lock_file`: a no-op in OSS.
        exit::exit(None, None, None, None, exit_status::T::LockStolen)
    }
    let sequence_receipt_high_water_mark = match &env.server {
        ServerProcess::Alive(process_data) => {
            let pid = process_data.pid;
            monitor_rpc::read_server_receipt_to_monitor_file(
                &server_files::server_receipt_to_monitor_file(pid as isize),
            )
            .unwrap_or(0)
        }
        _ => 0,
    };
    let res = maybe_push_purgatory_clients(env)?;
    // The first sequence number we send is 1; hence, the default "0" will be a no-op
    sent_fds_collector::collect_fds(sequence_receipt_high_water_mark);
    let has_client = sleep_and_check(socket)?;
    let res = match res {
        Err(msg) => Err(msg),
        Ok(()) => update_status(env, monitor_config)?,
    };
    if !has_client {
        // Note: this call merely reads from disk; it doesn't go via the slow HackEventLogger.
        // (`Event_logger.recheck_disk_files ()`: a no-op in OSS.)
        Ok(res)
    } else {
        let fd = match socket.accept() {
            Ok((fd, _)) => fd,
            Err(e) => {
                let e = Exn::Unix(e, "accept", String::new());
                hh_logger::log(&format!(
                    "ACCEPTING_ON_SOCKET_EXCEPTION; closing client FD. {}",
                    exception::clean_stack(&exception::to_string(&exception::wrap(format!(
                        "{:?}",
                        e
                    ))))
                ));
                return Err(e);
            }
        };
        if let Err(msg) = res {
            // `env >>= ...`: the client is not served (nor closed).
            std::mem::forget(fd);
            return Ok(Err(msg));
        }
        let fd_copy = fd.try_clone().ok();
        match ack_and_handoff_client(env, fd) {
            Ok(res) => Ok(res),
            Err(e) if e.errno() == Some(libc::EINVAL) => {
                hh_logger::log(&format!(
                    "Ack_and_handoff failure; closing client FD: {:?}",
                    e
                ));
                if let Some(fd) = fd_copy {
                    ensure_fd_closed(fd);
                }
                server_progress::try_delete();
                exit::exit(None, None, None, None, exit_status::T::SocketError)
            }
            Err(e) => {
                let msg = format!("Ack_and_handoff failure; closing client FD: {:?}", e);
                hh_logger::log(&msg);
                if let Some(fd) = fd_copy {
                    ensure_fd_closed(fd);
                }
                Ok(Err(msg))
            }
        }
    }
}

pub fn check_and_run_loop(mut env: Env, monitor_config: MonitorConfig, socket: UnixListener) -> ! {
    let mut consecutive_throws = 0;
    loop {
        let res = match check_and_run_loop_(&mut env, &monitor_config, &socket) {
            Ok(res) => {
                consecutive_throws = 0;
                res
            }
            Err(e) if e.errno() == Some(libc::ECHILD) => {
                let e = exception::wrap(e);
                hh_logger::log(&format!(
                    "check_and_run_loop_ threw with Unix.ECHILD. Exiting. - {}",
                    exception::get_backtrace_string(&e)
                ));
                exit::exit(None, None, None, None, exit_status::T::NoServerRunningShouldRetry)
            }
            Err(e) => {
                let e = exception::wrap(e);
                if consecutive_throws > 500 {
                    hh_logger::log("Too many consecutive exceptions.");
                    hh_logger::log(&format!(
                        "Probably an uncaught exception rethrown each retry. Exiting. {}",
                        exception::to_string(&e)
                    ));
                    // `Hack_event_logger.monitor_giving_up_exception e`: a no-op in OSS.
                    exit::exit(None, None, None, None, exit_status::T::UncaughtException(e))
                }
                hh_logger::log(&format!(
                    "check_and_run_loop_ threw with exception: {}",
                    exception::to_string(&e)
                ));
                consecutive_throws += 1;
                Ok(())
            }
        };
        if let Err(msg) = res {
            hh_logger::log(&format!(
                "Encountered error in check_and_run_loop: {}, starting new loop",
                msg
            ));
        }
    }
}

/// `check_and_run_loop_once (env, monitor_config, socket)`
pub fn check_and_run_loop_once(
    env: &mut Env,
    monitor_config: &MonitorConfig,
    socket: &UnixListener,
) -> Res<()> {
    if let Err(msg) = check_and_run_loop_(env, monitor_config, socket)? {
        hh_logger::log(&msg);
    }
    Ok(())
}

/// `start_monitor`. The error is the exception that starting the first
/// server raises.
pub fn start_monitor(
    current_version: config_file::Version,
    waiting_client: Option<RawFd>,
    max_purgatory_clients: isize,
    server_start_options: server_controller::ServerStartOptions,
    informant_init_env: &informant::InitEnv,
    monitor_config: &MonitorConfig,
) -> Res<(Env, UnixListener)> {
    let socket = crate::socket::init_unix_socket(&monitor_config.socket_file);
    // If the client started the server, it opened an FD before forking, so it
    // can be notified when the monitor socket is ready. The FD number was
    // passed in program args.
    if let Some(fd) = waiting_client {
        if let Err(e) = crate::server_client_provider::server_end::send_ready_to_waiting_client(fd) {
            eprint!(
                "Caught exception while waking client: {}\n",
                ocaml_unix::unix_error_to_string(&e, "write", "")
            );
        }
    }

    // It is essential that we initiate the Informant before the server if we
    // want to give the opportunity for the Informant to truly take
    // ownership over the lifetime of the server.
    //
    // This is because start_server won't actually start a server if it sees
    // a hg update sentinel file indicating an hg update is in-progress.
    // Starting the informant first ensures that its Watchman watch is started
    // before we check for the hgupdate sentinel file - this is required
    // for the informant to properly observe an update is complete without
    // hitting race conditions.
    let informant = informant::init(informant_init_env);
    let server_process = maybe_start_first_server(&server_start_options, &informant)?;
    let env = Env {
        informant,
        max_purgatory_clients,
        current_version,
        purgatory_clients: VecDeque::new(),
        server: server_process,
        server_start_options,
        allow_restart_from_precomputed_saved_state: informant_init_env
            .allow_restart_from_precomputed_saved_state,
        retries: 0,
        sql_retries: 0,
        watchman_retries: 0,
        edenfs_watcher_retries: 0,
        ignore_hh_version: informant::should_ignore_hh_version(informant_init_env),
    };
    Ok((env, socket))
}

/// Start the monitor and repeatedly run the check and run loop.
/// Does not return.
pub fn start_monitoring(
    current_version: config_file::Version,
    waiting_client: Option<RawFd>,
    max_purgatory_clients: isize,
    server_start_options: server_controller::ServerStartOptions,
    informant_init_env: &informant::InitEnv,
    monitor_config: MonitorConfig,
) -> Res<std::convert::Infallible> {
    let (env, socket) = start_monitor(
        current_version,
        waiting_client,
        max_purgatory_clients,
        server_start_options,
        informant_init_env,
        &monitor_config,
    )?;
    check_and_run_loop(env, monitor_config, socket)
}

#[cfg(test)]
mod tests;
