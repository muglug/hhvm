// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_client_provider.ml`: the clients handed
//! off by the monitor on its three pipes (the `monitor_to_server_handoff_msg`,
//! then the client's descriptor, then the receipt file), with
//! `crate::client_provider_sig::S`. [`server_end`] has the functions on a
//! client's connection.

use std::fs::File;
use std::mem::ManuallyDrop;
use std::os::fd::FromRawFd;
use std::os::fd::RawFd;
use std::os::unix::net::UnixStream;

use crate::client_provider_sig::*;
use crate::connection_tracker;
use crate::connection_tracker::Key;
use crate::exception;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::libancillary;
use crate::monitor_rpc;
use crate::rt::ocaml_unix;
use crate::rt::protocol;
use crate::rt::protocol::ReadError;
use crate::server_command_types::Command;
use crate::server_command_types::CommandResult;
use crate::server_command_types::ConnectionType;
use crate::server_files;

impl ClientError {
    pub fn other(what: String) -> ClientError {
        ClientError::Other(exception::wrap(protocol::UncaughtReadError(what)))
    }

    /// The error of a write to the client (`Unix_error (_, "write", "")`).
    pub fn of_write_error(e: std::io::Error) -> ClientError {
        let s = ocaml_unix::unix_error_to_string(&e, "write", "");
        match e.raw_os_error() {
            Some(libc::EPIPE) => ClientError::ChannelWentBad(s),
            _ => ClientError::other(s),
        }
    }

    /// The error of `input_value` on the client's channel: a reset
    /// connection is `Sys_error "Connection reset by peer"`, anything else
    /// is the exception as is.
    fn of_read_error(e: ReadError) -> ClientError {
        match &e {
            ReadError::Unix(io) if io.raw_os_error() == Some(libc::ECONNRESET) => {
                ClientError::ChannelWentBad("Sys_error(\"Connection reset by peer\")".to_string())
            }
            _ => ClientError::other(protocol::read_error_to_string(&e, "read")),
        }
    }

    fn of_read_client_error(e: server_end::ReadClientError) -> ClientError {
        match e {
            server_end::ReadClientError::ReadCommandTimeout => ClientError::ReadCommandTimeout,
            server_end::ReadClientError::ClientWentAway => ClientError::ClientWentAway,
            server_end::ReadClientError::Other(e) => ClientError::of_read_error(e),
        }
    }
}

/// `priority`: which of the three pipes of the monitor the client came on.
///
/// Priorities are used so that some hh commands can be treated more urgently
/// than others... When the monitor creates the server in
/// server_controller.ml, it creates three FDs, [Priority_high /
/// Server_controller.Priority], and [Priority_default /
/// Server_controller.Default], and [Priority_dormant /
/// Server_controller.Force_dormant_start_only].
///
/// In [Client_connect.connect], it decides which of the three to request:
/// "hh --force-dormant-start" will use the last one, and anything which
/// doesn't require a full typecheck (e.g. --type-at-pos) will use priority,
/// and anything which does require a full typecheck (e.g. hh status) will
/// use default. The monitor, when it performs handshake, looks at the request
/// and dispatches to one of the three FDs.
///
/// In [Server_main.serve_one_iteration], it decides which of the three FDs
/// to poll for incoming requests. For instance if it's in the middle of a
/// typecheck then it's willing to listen for priority requests (so it can
/// interrupt the current typecheck to handle thenm) but not for default
/// requests. And if we're "dormant" e.g. in the middle of a rebase, then
/// it's only willing to listen to Priority_dormant requests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Priority {
    PriorityHigh,
    PriorityDefault,
    PriorityDormant,
}

/// The three pipes from the monitor (`provider_from_file_descriptors
/// (default_in_fd, priority_in_fd, force_dormant_start_only_in_fd)`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InFds {
    /// Default pipe. Used for non time sensitive commands and IDE connections.
    pub default: RawFd,
    /// Priority pipe. There's a handler for events happening on this pipe
    /// which will interrupt the typing service. In practice this is used for
    /// commands that can be served immediately.
    pub priority: RawFd,
    /// Force formant start only pipe, used to perform the
    /// --force-dormant-start command.
    pub force_dormant_start_only: RawFd,
}


/// `t`: the pipes from the monitor.
pub struct T {
    pub in_fds: InFds,
}

/// `provider_from_file_descriptors`
pub fn provider_from_file_descriptors(in_fds: InFds) -> T {
    T { in_fds }
}

/// Why accepting a client failed: `End_of_file` on the pipe (the monitor
/// is gone), or another exception.
enum AcceptError {
    EndOfFile,
    Other(exception::T),
}

/// The pipe as a reader that does not close it.
fn pipe_reader(fd: RawFd) -> ManuallyDrop<File> {
    // SAFETY: the descriptor stays open for the life of the process; the
    // `File` is never dropped.
    ManuallyDrop::new(unsafe { File::from_raw_fd(fd) })
}

/// Retrieve channels to client from monitor process.
fn accept_client(
    priority: Priority,
    parent_in_fd: RawFd,
    t_sleep_and_check: f64,
    t_monitor_fd_ready: f64,
) -> Result<Handoff, AcceptError> {
    let msg: monitor_rpc::MonitorToServerHandoffMsg = {
        let mut r = pipe_reader(parent_in_fd);
        match protocol::read_value(&mut *r) {
            Ok(msg) => msg,
            Err(ReadError::EndOfFile) => return Err(AcceptError::EndOfFile),
            Err(e) => {
                return Err(AcceptError::Other(exception::wrap(
                    protocol::uncaught_read_error(e),
                )));
            }
        }
    };
    let monitor_rpc::MonitorToServerHandoffMsg {
        m2s_tracker: tracker,
        m2s_sequence_number,
        m2s_agent_session_id: agent_session_id,
    } = msg;
    let t_got_tracker = ocaml_unix::gettimeofday();
    hh_logger::log(&format!(
        "[{}] got tracker #{} handoff from monitor",
        connection_tracker::log_id(&tracker),
        m2s_sequence_number
    ));
    let socket = match libancillary::ancil_recv_fd(parent_in_fd) {
        Ok(fd) => {
            // (Close-on-exec, which the OCaml does not set: the client's
            // socket must not stay open in the processes the server spawns.)
            // SAFETY: `fcntl` on the descriptor just received, which is ours.
            unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) };
            // SAFETY: the descriptor was just received and is owned here.
            unsafe { <std::os::fd::OwnedFd as std::os::fd::FromRawFd>::from_raw_fd(fd) }
        }
        Err(libancillary::ReceivingFdException(msg)) => {
            return Err(AcceptError::Other(exception::wrap(protocol::UncaughtReadError(
                format!("Libancillary.Receiving_Fd_Exception(\"{}\")", msg),
            ))));
        }
    };
    let t_got_client_fd = ocaml_unix::gettimeofday();
    monitor_rpc::write_server_receipt_to_monitor_file(
        &server_files::server_receipt_to_monitor_file(ocaml_unix::getpid()),
        m2s_sequence_number,
    );
    hh_logger::log(&format!(
        "[{}] got FD#{} handoff from monitor",
        connection_tracker::log_id(&tracker),
        m2s_sequence_number
    ));
    let tracker = connection_tracker::track(
        Key::ServerSleepAndCheck,
        Some(t_sleep_and_check),
        None,
        None,
        None,
        tracker,
    );
    let tracker = connection_tracker::track(
        Key::ServerMonitorFdReady,
        Some(t_monitor_fd_ready),
        None,
        None,
        None,
        tracker,
    );
    let tracker =
        connection_tracker::track(Key::ServerGotTracker, Some(t_got_tracker), None, None, None, tracker);
    let tracker = connection_tracker::track(
        Key::ServerGotClientFd,
        Some(t_got_client_fd),
        None,
        None,
        None,
        tracker,
    );
    let ic = UnixStream::from(socket);
    let oc = ic
        .try_clone()
        .map_err(|e| AcceptError::Other(exception::wrap(protocol::uncaught_write_error(e))))?;
    let pipe_type = match priority {
        Priority::PriorityHigh => monitor_rpc::PipeType::Priority,
        Priority::PriorityDefault => monitor_rpc::PipeType::Default,
        Priority::PriorityDormant => monitor_rpc::PipeType::ForceDormantStartOnly,
    };
    Ok(Handoff {
        client: Client::Socket(
            server_end::Client {
                ic,
                oc,
                tracker,
                handoff_options: monitor_rpc::HandoffOptions {
                    force_dormant_start: priority == Priority::PriorityDormant,
                    pipe_type,
                    agent_session_id: agent_session_id.clone(),
                },
                agent_session_id,
            },
            priority,
        ),
        m2s_sequence_number,
    })
}

/// `Unix.select fd_list [] [] timeout`: the descriptors ready to read.
/// (`Server_idle_gc.select ~slice` does slices of the shared-memory GC
/// while it waits; there is no shared memory here, so it waits.)
pub fn select(fd_list: &[RawFd], timeout: f64) -> Vec<RawFd> {
    let mut fds: Vec<libc::pollfd> = fd_list
        .iter()
        .map(|&fd| libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        })
        .collect();
    let deadline = ocaml_unix::gettimeofday() + timeout;
    loop {
        let remaining = (deadline - ocaml_unix::gettimeofday()).max(0.0);
        // SAFETY: `fds` is a live array of `fds.len()` pollfds.
        let r = unsafe {
            libc::poll(
                fds.as_mut_ptr(),
                fds.len() as libc::nfds_t,
                (remaining * 1000.0).ceil() as libc::c_int,
            )
        };
        if r >= 0 {
            break;
        }
        if std::io::Error::last_os_error().kind() != std::io::ErrorKind::Interrupted {
            break;
        }
    }
    fds.iter()
        .filter(|p| p.revents & (libc::POLLIN | libc::POLLHUP | libc::POLLERR) != 0)
        .map(|p| p.fd)
        .collect()
}

fn socket_client(c: &mut Client) -> &mut server_end::Client {
    match c {
        Client::Socket(c, _) => c,
        Client::Test => panic!("Server_client_provider: a test client"),
    }
}

impl S for T {
    /// Waits up to 0.1 seconds and checks for new connection attempts.
    /// Select what client to serve next and call
    /// retrieve channels to client from monitor process.
    fn sleep_and_check(&mut self, idle_gc_slice: isize, kind: ClientKind) -> SelectOutcome {
        let _ = idle_gc_slice;
        let InFds {
            default: default_in_fd,
            priority: priority_in_fd,
            force_dormant_start_only: force_dormant_start_only_in_fd,
        } = self.in_fds;
        let t_sleep_and_check = ocaml_unix::gettimeofday();
        let in_fds = [default_in_fd, priority_in_fd, force_dormant_start_only_in_fd];
        let fd_l: &[RawFd] = match kind {
            ClientKind::ForceDormantStartOnly => &[force_dormant_start_only_in_fd],
            ClientKind::Priority => &[priority_in_fd],
            ClientKind::Any => &in_fds,
        };
        let ready_fd_l = select(fd_l, 0.1);
        let t_monitor_fd_ready = ocaml_unix::gettimeofday();
        let res = if ready_fd_l.contains(&priority_in_fd) {
            accept_client(
                Priority::PriorityHigh,
                priority_in_fd,
                t_sleep_and_check,
                t_monitor_fd_ready,
            )
            .map(SelectOutcome::SelectNew)
        } else if ready_fd_l.contains(&default_in_fd) {
            accept_client(
                Priority::PriorityDefault,
                default_in_fd,
                t_sleep_and_check,
                t_monitor_fd_ready,
            )
            .map(SelectOutcome::SelectNew)
        } else if ready_fd_l.contains(&force_dormant_start_only_in_fd) {
            accept_client(
                Priority::PriorityDormant,
                force_dormant_start_only_in_fd,
                t_sleep_and_check,
                t_monitor_fd_ready,
            )
            .map(SelectOutcome::SelectNew)
        } else if ready_fd_l.is_empty() {
            Ok(SelectOutcome::SelectNothing)
        } else {
            Err(AcceptError::Other(exception::wrap(protocol::UncaughtReadError(
                "Failure(\"sleep_and_check got impossible fd\")".to_string(),
            ))))
        };
        match res {
            Ok(outcome) => outcome,
            Err(AcceptError::EndOfFile) => {
                hh_logger::log("GET_CLIENT_CHANNELS_EXCEPTION End_of_file. Terminating.");
                exit::exit(None, None, None, None, exit_status::T::ServerGotEofFromMonitor)
            }
            Err(AcceptError::Other(e)) => {
                hh_logger::log(&format!(
                    "GET_CLIENT_CHANNELS_EXCEPTION({}). Ignoring.",
                    exception::get_ctor_string(&e)
                ));
                std::thread::sleep(std::time::Duration::from_millis(500));
                SelectOutcome::SelectException(e)
            }
        }
    }

    fn priority_fd(&self) -> Option<RawFd> {
        Some(self.in_fds.priority)
    }

    fn track(
        &mut self,
        c: &mut Client,
        key: Key,
        time: Option<f64>,
        log: Option<bool>,
        msg: Option<&str>,
        long_delay_okay: Option<bool>,
    ) {
        let c = socket_client(c);
        c.tracker =
            connection_tracker::track(key, time, log, msg, long_delay_okay, c.tracker.clone());
    }

    fn read_connection_type(&mut self, c: &mut Client) -> Result<ConnectionType, ClientError> {
        server_end::read_connection_type(socket_client(c)).map_err(ClientError::of_read_client_error)
    }

    fn send_response_to_client(
        &mut self,
        c: &mut Client,
        response: CommandResult,
    ) -> Result<(), ClientError> {
        server_end::send_response_to_client(socket_client(c), response)
            .map_err(ClientError::of_write_error)
    }

    fn read_client_msg(&mut self, c: &mut Client) -> Result<Command, ClientError> {
        server_end::read_client_msg(socket_client(c)).map_err(ClientError::of_read_client_error)
    }

    fn priority_to_string(&self, c: &Client) -> String {
        match c {
            Client::Socket(_, Priority::PriorityHigh) => "high",
            Client::Socket(_, Priority::PriorityDefault) => "default",
            Client::Socket(_, Priority::PriorityDormant) => "dormant",
            Client::Test => "mock",
        }
        .to_string()
    }

    fn agent_session_id(&self, c: &Client) -> Option<String> {
        match c {
            Client::Socket(c, _) => c.agent_session_id.clone(),
            Client::Test => None,
        }
    }

    /// `Server_utils.shutdown_client (ic, oc)`
    fn shutdown_client(&mut self, c: &mut Client) {
        let c = socket_client(c);
        let _ = c.oc.shutdown(std::net::Shutdown::Both);
    }

    fn ping(&mut self, c: &mut Client) -> Result<(), ClientWentAway> {
        server_end::ping(socket_client(c))
    }

    fn clone_provider(&self) -> Box<dyn S + Send> {
        Box::new(T {
            in_fds: self.in_fds,
        })
    }
}

/// The server's end of the protocol (`ServerClientProvider`'s
/// `say_hello`, `read_connection_type`, `read_client_msg`,
/// `send_response_to_client`, `ping`), on a client connection that the
/// monitor (`crate::monitor_main`) handed off. For the client's tests only
/// (`#[cfg(test)]`): a monitor and a server in one (`bind`,
/// [`ack_and_handoff_client`]), the monitor's half of the handshake as
/// `Monitor_main.ack_and_handoff_client` does it.
pub mod server_end {
    #[cfg(test)]
    use std::os::unix::net::UnixListener;
    use std::os::unix::net::UnixStream;

    use crate::rt::protocol::Deadline;
    use crate::rt::protocol::ReadError;
    use crate::monitor_rpc;
    use crate::monitor_utils;
    #[cfg(test)]
    use crate::monitor_utils::ConnectionState;
    #[cfg(test)]
    use crate::prehandoff;
    use crate::rt::protocol::input_value;
    use crate::rt::protocol::write_value;
    #[cfg(test)]
    use crate::build_id;
    use crate::client_provider_sig::ClientWentAway;
    use crate::connection_tracker;
    use crate::connection_tracker::Key;
    #[cfg(test)]
    use crate::hh_logger;
    #[cfg(test)]
    use crate::path;
    use crate::server_command_types::Command;
    use crate::server_command_types::CommandResult;
    use crate::server_command_types::ConnectionType;
    use crate::server_command_types::MessageType;
    #[cfg(test)]
    use crate::server_command_types::ServerSpecificFiles;
    #[cfg(test)]
    use crate::server_files;
    #[cfg(test)]
    use crate::socket;
    #[cfg(test)]
    use crate::utils;

    #[cfg(test)]
    /// The listening socket of a root (`Socket.init_unix_socket
    /// (Server_files.socket_file root)`). Binding it also fixes the launch
    /// time that a version mismatch reports
    /// (`Monitor_utils.current_build_info`).
    pub fn bind(root: &path::T) -> UnixListener {
        let _ = monitor_utils::current_build_info();
        let listener = socket::init_unix_socket(&server_files::socket_file(root));
        // `last_request_handoff = ref (Unix.time ())` when the server starts
        // (`Server_controller.start_server`).
        set_last_request_handoff();
        listener
    }

    #[cfg(test)]
    /// `server.last_request_handoff` (`Server_process.server_process`): the
    /// time (`Unix.time`) of the last handoff, which the monitor logs.
    static LAST_REQUEST_HANDOFF: std::sync::Mutex<Option<f64>> = std::sync::Mutex::new(None);

    #[cfg(test)]
    /// `server.last_request_handoff := Unix.time ()`
    fn set_last_request_handoff() {
        *LAST_REQUEST_HANDOFF
            .lock()
            .unwrap_or_else(|e| e.into_inner()) =
            Some(crate::rt::ocaml_unix::gettimeofday().floor());
    }

    #[cfg(test)]
    fn last_request_handoff() -> f64 {
        let last = *LAST_REQUEST_HANDOFF.lock().unwrap_or_else(|e| e.into_inner());
        match last {
            Some(t) => t,
            // A server that did not [`bind`] (the tests): as if it had just
            // started.
            None => {
                set_last_request_handoff();
                last_request_handoff()
            }
        }
    }

    /// `Server_command_types.Read_command_timeout` or `Client_went_away`.
    #[derive(Debug)]
    pub enum ReadClientError {
        ReadCommandTimeout,
        ClientWentAway,
        /// Any other exception (the OCaml does not catch it).
        Other(ReadError),
    }

    /// A client whose handshake is done: the server talks to it (`client`
    /// of `ServerClientProvider`).
    pub struct Client {
        pub ic: UnixStream,
        pub oc: UnixStream,
        pub tracker: connection_tracker::T,
        pub handoff_options: monitor_rpc::HandoffOptions,
        /// The agent session responsible for this client request, if any
        /// (`agent_session_id`, from the monitor's handoff message).
        pub agent_session_id: Option<String>,
    }

    #[cfg(test)]
    /// What the handshake of a connection came to.
    pub enum Handshake {
        /// `HANDOFF_TO_SERVER`: the `Sentinel` is sent; the server goes on
        /// with [`read_connection_type`].
        Handoff(Client),
        /// `SHUT_DOWN`: the server shuts down and exits with `No_error`
        /// (`kill_server_with_check_and_wait`, `Exit.exit No_error`); the
        /// client sees the connection close when it exits.
        ShutDown(connection_tracker::T, UnixStream),
        /// The client is another version, and was told
        /// `Build_id_mismatch_v3`. If `monitor_will_terminate`, the server
        /// exits with `Build_id_mismatch` (keeping the connection until it
        /// does, so that the client sees it close then); otherwise the
        /// connection was closed.
        VersionMismatch {
            monitor_will_terminate: bool,
            conn: Option<UnixStream>,
        },
    }

    #[cfg(test)]
    /// `read_version_string_then_newline` (there is no newline here). An
    /// OCaml string is any bytes: one that is not UTF-8 is read lossily (it
    /// is then a version that matches no build). The error is the exception
    /// that `Marshal_tools.from_fd_with_preamble` raises, which OCaml does
    /// not turn into `"Malformed Build ID"`: the monitor's handler logs it
    /// and closes the connection.
    fn read_version_string(fd: &mut UnixStream) -> Result<String, ReadError> {
        match crate::rt::protocol::ocaml_frame::read_version(fd)? {
            Ok(s) => Ok(s),
            Err(msg) => Err(ReadError::Malformed(msg)),
        }
    }

    #[cfg(test)]
    /// `Monitor_main.ack_and_handoff_client` for a server that is alive
    /// (frames 1 to 4), with the monitor's `ignore_hh_version`. `Err` is
    /// `"Malformed Build ID"` (a version payload that does not parse), or
    /// the exception of reading the version or the command (OCaml's
    /// `Printexc.to_string` of it), or of writing: the connection is dropped
    /// (the monitor logs `Ack_and_handoff failure; closing client FD: %s`).
    pub fn ack_and_handoff_client(
        client_fd: UnixStream,
        ignore_hh_version: bool,
        server_specific_files: &ServerSpecificFiles,
    ) -> Result<Handshake, String> {
        ack_and_handoff_client_as(
            client_fd,
            &build_id::build_revision(),
            ignore_hh_version,
            server_specific_files,
        )
    }

    #[cfg(test)]
    /// [`ack_and_handoff_client`] for a server whose version
    /// (`Build_id.build_revision`) is `monitor_version`: what the tests use
    /// to be another version than their client.
    pub fn ack_and_handoff_client_as(
        mut client_fd: UnixStream,
        monitor_version: &str,
        ignore_hh_version: bool,
        server_specific_files: &ServerSpecificFiles,
    ) -> Result<Handshake, String> {
        // OCaml's monitor reads the version and the monitor command with no
        // timeout. Here a connection that sends nothing for 30 seconds is
        // dropped (as a malformed one), so that it cannot hold its task.
        let _ = Deadline::in_seconds(30.).apply(&client_fd);
        let start_time = crate::rt::ocaml_unix::gettimeofday();
        let payload = match read_version_string(&mut client_fd) {
            Err(e) => return Err(crate::rt::protocol::read_error_to_string(&e, "read")),
            Ok(s) => match monitor_utils::version_payload::deserialize(&s) {
                Ok(payload) => payload,
                Err(monitor_utils::version_payload::DeserializeError::Error(_err)) => {
                    return Err("Malformed Build ID".to_string());
                }
                // `Yojson.Safe.Util.Type_error`, raised (not an `Error`).
                Err(monitor_utils::version_payload::DeserializeError::TypeError(exn)) => {
                    return Err(exn);
                }
            },
        };
        let monitor_will_terminate = monitor_utils::monitor_will_terminate(&payload);
        let monitor_utils::version_payload::T {
            client_version,
            tracker_id,
            terminate_monitor_on_version_mismatch,
            ..
        } = payload;
        hh_logger::log(&format!(
            "[{}] read_version: start_wait={}, client_version={}, monitor_version={}, monitor_ignore_hh_version={}, terminate_monitor_on_version_mismatch={}",
            tracker_id,
            utils::timestring(start_time),
            client_version,
            monitor_version,
            ignore_hh_version,
            terminate_monitor_on_version_mismatch
        ));
        // Version is okay if *monitor* was started with --ignore-hh-version, or versions match.
        let is_version_ok = ignore_hh_version || client_version == monitor_version;
        if is_version_ok {
            let connection_state = ConnectionState::ConnectionOk;
            hh_logger::log(&format!(
                "[{}] sending {}",
                tracker_id,
                monitor_utils::show_connection_state(&connection_state)
            ));
            crate::rt::protocol::ocaml_frame::write_connection_state(&mut client_fd, &connection_state)
                .map_err(|e| e.to_string())?;
            // following function returns [env msg_update] monad
            handle_monitor_rpc(client_fd, server_specific_files)
        } else {
            let _ = terminate_monitor_on_version_mismatch;
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
                crate::rt::protocol::ocaml_frame::write_connection_state(&mut client_fd, &connection_state)
            {
                hh_logger::log(&format!("while sending, exn: {}", exn));
            }
            if monitor_will_terminate {
                Ok(Handshake::VersionMismatch {
                    monitor_will_terminate,
                    conn: Some(client_fd),
                })
            } else {
                hh_logger::log("Closing client_fd");
                drop(client_fd);
                Ok(Handshake::VersionMismatch {
                    monitor_will_terminate,
                    conn: None,
                })
            }
        }
    }

    #[cfg(test)]
    /// `handle_monitor_rpc`, and `client_prehandoff` for a server that is
    /// alive: the `Sentinel`.
    fn handle_monitor_rpc(
        mut client_fd: UnixStream,
        server_specific_files: &ServerSpecificFiles,
    ) -> Result<Handshake, String> {
        let cmd: monitor_rpc::Command =
            crate::rt::protocol::read_value(&mut client_fd).map_err(|e| crate::rt::protocol::read_error_to_string(&e, "read"))?;
        match cmd {
            monitor_rpc::Command::HandoffToServer(tracker, handoff_options) => {
                let tracker =
                    connection_tracker::track(Key::MonitorReceivedHandoff, None, None, None, None, tracker);
                let t_ready = crate::rt::ocaml_unix::gettimeofday();
                let tracker =
                    connection_tracker::track(Key::MonitorReady, Some(t_ready), None, None, None, tracker);
                // TODO: Send this to client so it is visible.
                hh_logger::log(&format!(
                    "[{}] Got {} request for typechecker. Prior request {:.1} seconds ago",
                    connection_tracker::log_id(&tracker),
                    monitor_rpc::pipe_type_to_string(handoff_options.pipe_type),
                    t_ready - last_request_handoff()
                ));
                write_value(
                    &mut client_fd,
                    &prehandoff::Msg::Sentinel(server_specific_files.clone()),
                )
                .map_err(|e| e.to_string())?;
                let tracker =
                    connection_tracker::track(Key::MonitorSentAckToClient, None, None, None, None, tracker);
                // (`hand_off_client_connection_wrapper`: the connection is
                // the server's from here.)
                set_last_request_handoff();
                crate::rt::protocol::clear_timeouts(&client_fd);
                let oc = client_fd.try_clone().map_err(|e| e.to_string())?;
                Ok(Handshake::Handoff(Client {
                    ic: client_fd,
                    oc,
                    tracker,
                    agent_session_id: handoff_options.agent_session_id.clone(),
                    handoff_options,
                }))
            }
            monitor_rpc::Command::ShutDown(tracker) => {
                hh_logger::log(&format!(
                    "[{}] Got shutdown RPC. Shutting down.",
                    connection_tracker::log_id(&tracker)
                ));
                Ok(Handshake::ShutDown(tracker, client_fd))
            }
        }
    }

    pub fn say_hello(oc: &mut UnixStream) -> Result<(), std::io::Error> {
        write_value(oc, &MessageType::<CommandResult>::Hello)
    }

    /// `read_connection_type_from_channel`: sent by
    /// [ClientConnection.connect], within a second.
    fn read_connection_type_from_channel(
        ic: &mut UnixStream,
    ) -> Result<ConnectionType, ReadClientError> {
        let deadline = Deadline::in_seconds(1.);
        if deadline.apply(ic).is_err() {
            return Err(ReadClientError::ReadCommandTimeout);
        }
        let res = input_value(ic);
        crate::rt::protocol::clear_timeouts(ic);
        match res {
            Ok(connection_type) => Ok(connection_type),
            Err(e) if e.is_timeout() => Err(ReadClientError::ReadCommandTimeout),
            Err(e) => Err(ReadClientError::Other(e)),
        }
    }

    /// Says hello, then reads the connection type. A broken pipe while
    /// saying hello (`Unix_error (EPIPE, "write", _)`) or a reset connection
    /// while reading (`Sys_error "Connection reset by peer"`, from
    /// `input_value`) is `Client_went_away`; anything else is not caught.
    pub fn read_connection_type(client: &mut Client) -> Result<ConnectionType, ReadClientError> {
        if let Err(e) = say_hello(&mut client.oc) {
            return match e.raw_os_error() {
                Some(libc::EPIPE) => Err(ReadClientError::ClientWentAway),
                _ => Err(ReadClientError::Other(ReadError::Unix(e))),
            };
        }
        client.tracker = connection_tracker::track(
            Key::ServerSentHello,
            None,
            None,
            None,
            None,
            client.tracker.clone(),
        );
        let connection_type = match read_connection_type_from_channel(&mut client.ic) {
            Err(ReadClientError::Other(ReadError::Unix(e)))
                if e.raw_os_error() == Some(libc::ECONNRESET) =>
            {
                return Err(ReadClientError::ClientWentAway);
            }
            res => res?,
        };
        client.tracker = connection_tracker::track(
            Key::ServerGotConnectionType,
            None,
            None,
            None,
            None,
            client.tracker.clone(),
        );
        Ok(connection_type)
    }

    pub fn send_response_to_client(
        client: &mut Client,
        response: CommandResult,
    ) -> Result<(), std::io::Error> {
        write_value(
            &mut client.oc,
            &MessageType::Response(response, client.tracker.clone()),
        )
    }

    /// `read_client_msg`: the command, within a second. The end of the
    /// stream is `Client_went_away`.
    pub fn read_client_msg(client: &mut Client) -> Result<Command, ReadClientError> {
        let deadline = Deadline::in_seconds(1.);
        if deadline.apply(&client.ic).is_err() {
            return Err(ReadClientError::ReadCommandTimeout);
        }
        let res = input_value(&mut client.ic);
        crate::rt::protocol::clear_timeouts(&client.ic);
        match res {
            Ok(cmd) => Ok(cmd),
            Err(ReadError::EndOfFile) => Err(ReadClientError::ClientWentAway),
            Err(e) if e.is_timeout() => Err(ReadClientError::ReadCommandTimeout),
            Err(e) => Err(ReadClientError::Other(e)),
        }
    }

    pub fn ping(client: &mut Client) -> Result<(), ClientWentAway> {
        write_value(&mut client.oc, &MessageType::<CommandResult>::Ping).map_err(|_| ClientWentAway)
    }

    /// Tells the client waiting in `Client_start.start_server` (through the
    /// `--waiting-client` descriptor) that the server is ready:
    /// `Monitor_utils.ready` and a newline.
    pub fn send_ready_to_waiting_client(fd: std::os::fd::RawFd) -> std::io::Result<()> {
        use std::io::Write;
        use std::os::fd::FromRawFd;
        // SAFETY: the descriptor was given on the command line by the
        // client; it is used once and closed.
        let mut f = unsafe { std::fs::File::from_raw_fd(fd) };
        f.write_all(format!("{}\n", monitor_utils::READY).as_bytes())?;
        f.flush()
    }
}
