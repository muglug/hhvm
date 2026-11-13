// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_client_provider.ml` (clients handed
//! off by the monitor on its three pipes: the `monitor_to_server_handoff_msg`,
//! then the client's descriptor, then the receipt file) and of
//! `client_and_server/test_client_provider.ml` (a canned request, the
//! response captured), behind one trait (`Client_provider_sig.S`).
//!
//! Owned by **SRV** (plan §3.1, §8 item 2).
//!
//! Differences in form from the OCaml: the functions of the signature that
//! take a client are methods of the provider (`provider.ping(client)` for
//! `Client_provider.ping client`); the exceptions they raise
//! (`Client_went_away`, `Read_command_timeout`, `Unix_error (EPIPE, ..)`,
//! ...) are a [`ClientError`]. `select_outcome` keeps the OCaml's
//! `Select_new of handoff` (plan §8 wrote it as a record variant).

use std::fs::File;
use std::mem::ManuallyDrop;
use std::os::fd::FromRawFd;
use std::os::fd::RawFd;
use std::os::unix::net::UnixStream;

use crate::connection_tracker;
use crate::connection_tracker::Key;
use crate::exception;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::rt::fd_passing;
use crate::rt::ocaml_unix;
use crate::rt::protocol;
use crate::rt::protocol::ReadError;
use crate::rt::protocol::monitor_rpc;
use crate::rt::protocol::server_end;
use crate::server_command_types::CmdMetadata;
use crate::server_command_types::Command;
use crate::server_command_types::CommandResult;
use crate::server_command_types::ConnectionType;
use crate::server_files;

/// `ClientProvider.Client_went_away`
pub type ClientWentAway = server_end::Client_went_away;

/// The exceptions of the functions of a provider that
/// `Client_command_handler.handle_client_command_exception` tells apart.
#[derive(Debug)]
pub enum ClientError {
    /// `Client_provider.Client_went_away`
    ClientWentAway,
    /// `Server_command_types.Read_command_timeout`
    ReadCommandTimeout,
    /// `Unix.Unix_error (Unix.EPIPE, _, _)`, `Sys_error "Broken pipe"`,
    /// `Sys_error "Connection reset by peer"`: the client channel went bad.
    ChannelWentBad(String),
    /// Any other exception.
    Other(exception::T),
}

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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Priority {
    PriorityHigh,
    PriorityDefault,
    PriorityDormant,
}

/// `client`: an instance of hh_client calling clientConnect.rpc (its
/// socket, tracker and priority), or the client of a test (which has no
/// socket: its request and its response are in the [`TestProvider`]).
pub enum Client {
    Socket(server_end::Client, Priority),
    Test,
}

/// `handoff`
pub struct Handoff {
    pub client: Client,
    /// A unique number incremented for each client socket handoff from
    /// monitor to server. Useful to correlate monitor and server logs.
    pub m2s_sequence_number: isize,
}

/// `select_outcome`: outcome of the POSIX [select] system call.
pub enum SelectOutcome {
    SelectNew(Handoff),
    SelectNothing,
    SelectException(exception::T),
    NotSelectingDeferring(Vec<String>),
}

/// `` [ `Any | `Priority | `Force_dormant_start_only ] ``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClientKind {
    Any,
    Priority,
    ForceDormantStartOnly,
}

/// The name W0 gave [`ClientKind`].
pub type SelectKind = ClientKind;

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

/// `Client_provider_sig.S`
pub trait ClientProvider {
    /// Wait up to 0.1 seconds and checks for new connection attempts.
    /// Select what client to serve next and retrieve channels to
    /// client from monitor process (connection hand-off).
    fn sleep_and_check(&mut self, idle_gc_slice: isize, kind: ClientKind) -> SelectOutcome;
    fn priority_fd(&self) -> Option<RawFd>;
    /// See explanation in Connection_tracker.track
    fn track(
        &mut self,
        c: &mut Client,
        key: Key,
        time: Option<f64>,
        log: Option<bool>,
        msg: Option<&str>,
        long_delay_okay: Option<bool>,
    );
    fn read_connection_type(&mut self, c: &mut Client) -> Result<ConnectionType, ClientError>;
    fn send_response_to_client(
        &mut self,
        c: &mut Client,
        response: CommandResult,
    ) -> Result<(), ClientError>;
    fn read_client_msg(&mut self, c: &mut Client) -> Result<Command, ClientError>;
    fn priority_to_string(&self, c: &Client) -> String;
    /// Shutdown socket connection to client (errors are ignored; the
    /// descriptors are closed when the client is dropped).
    fn shutdown_client(&mut self, c: &mut Client);
    fn ping(&mut self, c: &mut Client) -> Result<(), ClientWentAway>;
    /// A provider on the same pipes, for the priority interrupt handler
    /// (the OCaml's provider is an immutable record that the handler's
    /// closure shares).
    fn clone_provider(&self) -> Box<dyn ClientProvider + Send>;
}

/// `Server_client_provider.t`: the pipes from the monitor.
pub struct MonitorPipesProvider {
    pub in_fds: InFds,
}

/// `provider_from_file_descriptors`
pub fn provider_from_file_descriptors(in_fds: InFds) -> MonitorPipesProvider {
    MonitorPipesProvider { in_fds }
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
    } = msg;
    let t_got_tracker = ocaml_unix::gettimeofday();
    hh_logger::log(&format!(
        "[{}] got tracker #{} handoff from monitor",
        connection_tracker::log_id(&tracker),
        m2s_sequence_number
    ));
    let socket = match fd_passing::ancil_recv_fd(parent_in_fd) {
        Ok(fd) => {
            // (Close-on-exec, which the OCaml does not set: the client's
            // socket must not stay open in the processes the server spawns.)
            // SAFETY: `fcntl` on the descriptor just received, which is ours.
            unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) };
            // SAFETY: the descriptor was just received and is owned here.
            unsafe { <std::os::fd::OwnedFd as std::os::fd::FromRawFd>::from_raw_fd(fd) }
        }
        Err(fd_passing::ReceivingFdException(msg)) => {
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
                },
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

impl ClientProvider for MonitorPipesProvider {
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
                exit::exit(None, None, None, exit_status::T::ServerGotEofFromMonitor)
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

    /// `Server_utils.shutdown_client (ic, oc)`
    fn shutdown_client(&mut self, c: &mut Client) {
        let c = socket_client(c);
        let _ = c.oc.shutdown(std::net::Shutdown::Both);
    }

    fn ping(&mut self, c: &mut Client) -> Result<(), ClientWentAway> {
        server_end::ping(socket_client(c))
    }

    fn clone_provider(&self) -> Box<dyn ClientProvider + Send> {
        Box::new(MonitorPipesProvider {
            in_fds: self.in_fds,
        })
    }
}

/// `Test_client_provider`: what the OCaml keeps in its `Refs` (the mocked
/// connection type and request, the response recorded). It is not cleared
/// by reading: `sleep_and_check` gives a new client as long as
/// `new_client_type` is set.
#[derive(Default)]
pub struct TestProvider {
    pub new_client_type: Option<ConnectionType>,
    pub client_request: Option<crate::server_command_types::T>,
    pub client_response: Option<CommandResult>,
}

impl TestProvider {
    /// `clear ()`
    pub fn clear(&mut self) {
        self.new_client_type = None;
        self.client_request = None;
        self.client_response = None;
    }

    /// `mock_new_client_type x`
    pub fn mock_new_client_type(&mut self, x: ConnectionType) {
        self.new_client_type = Some(x)
    }

    /// `mock_client_request x`
    pub fn mock_client_request(&mut self, x: crate::server_command_types::T) {
        self.client_request = Some(x)
    }

    /// `get_client_response Non_persistent`
    pub fn get_client_response(&self) -> Option<&CommandResult> {
        self.client_response.as_ref()
    }
}

impl ClientProvider for TestProvider {
    fn sleep_and_check(&mut self, _idle_gc_slice: isize, _kind: ClientKind) -> SelectOutcome {
        match self.new_client_type {
            Some(_) => SelectOutcome::SelectNew(Handoff {
                client: Client::Test,
                m2s_sequence_number: 0,
            }),
            None => SelectOutcome::SelectNothing,
        }
    }

    fn priority_fd(&self) -> Option<RawFd> {
        None
    }

    fn track(
        &mut self,
        _c: &mut Client,
        _key: Key,
        _time: Option<f64>,
        _log: Option<bool>,
        _msg: Option<&str>,
        _long_delay_okay: Option<bool>,
    ) {
    }

    fn read_connection_type(&mut self, _c: &mut Client) -> Result<ConnectionType, ClientError> {
        // `Utils.unsafe_opt`
        Ok(self.new_client_type.expect("Utils.unsafe_opt"))
    }

    fn send_response_to_client(
        &mut self,
        _c: &mut Client,
        response: CommandResult,
    ) -> Result<(), ClientError> {
        self.client_response = Some(response);
        Ok(())
    }

    fn read_client_msg(&mut self, _c: &mut Client) -> Result<Command, ClientError> {
        let metadata = CmdMetadata {
            from: "test".to_string(),
            desc: "cmd".to_string(),
        };
        Ok((
            metadata,
            self.client_request.clone().expect("Utils.unsafe_opt"),
        ))
    }

    fn priority_to_string(&self, _c: &Client) -> String {
        "mock".to_string()
    }

    fn shutdown_client(&mut self, _c: &mut Client) {}

    fn ping(&mut self, _c: &mut Client) -> Result<(), ClientWentAway> {
        Ok(())
    }

    fn clone_provider(&self) -> Box<dyn ClientProvider + Send> {
        // (`priority_fd` is `None`: no interrupt handler uses it.)
        Box::new(NoClients)
    }
}

/// A provider without clients: what a [`TestProvider`] gives to the
/// interrupt handlers (which it has no descriptor for).
struct NoClients;

impl ClientProvider for NoClients {
    fn sleep_and_check(&mut self, _idle_gc_slice: isize, _kind: ClientKind) -> SelectOutcome {
        SelectOutcome::SelectNothing
    }

    fn priority_fd(&self) -> Option<RawFd> {
        None
    }

    fn track(
        &mut self,
        _c: &mut Client,
        _key: Key,
        _time: Option<f64>,
        _log: Option<bool>,
        _msg: Option<&str>,
        _long_delay_okay: Option<bool>,
    ) {
    }

    fn read_connection_type(&mut self, _c: &mut Client) -> Result<ConnectionType, ClientError> {
        Err(ClientError::ClientWentAway)
    }

    fn send_response_to_client(
        &mut self,
        _c: &mut Client,
        _response: CommandResult,
    ) -> Result<(), ClientError> {
        Err(ClientError::ClientWentAway)
    }

    fn read_client_msg(&mut self, _c: &mut Client) -> Result<Command, ClientError> {
        Err(ClientError::ClientWentAway)
    }

    fn priority_to_string(&self, _c: &Client) -> String {
        "mock".to_string()
    }

    fn shutdown_client(&mut self, _c: &mut Client) {}

    fn ping(&mut self, _c: &mut Client) -> Result<(), ClientWentAway> {
        Err(server_end::Client_went_away)
    }

    fn clone_provider(&self) -> Box<dyn ClientProvider + Send> {
        Box::new(NoClients)
    }
}
