// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/client_provider_sig.ml`: what a provider of
//! clients does (`S`), implemented by `crate::server_client_provider` (the
//! clients the monitor hands off) and `crate::test_client_provider`.
//!
//! Differences in form from the OCaml: the functions of the signature that
//! take a client are methods of the provider (`provider.ping(client)` for
//! `Client_provider.ping client`); the exceptions they raise
//! (`Client_went_away`, `Read_command_timeout`, `Unix_error (EPIPE, ..)`,
//! ...) are a [`ClientError`]. `select_outcome` keeps the OCaml's
//! `Select_new of handoff`. The types `client` and `handoff` are shared by
//! the two providers. `get_channels` is not ported.

use std::os::fd::RawFd;

use crate::connection_tracker::Key;
use crate::exception;
use crate::server_command_types::Command;
use crate::server_command_types::CommandResult;
use crate::server_command_types::ConnectionType;

/// `exception Client_went_away`
pub struct ClientWentAway;

/// Prints the OCaml constructor's name, `Client_went_away` (the text of the
/// exception: `exception::wrap` takes it from `Debug`).
impl std::fmt::Debug for ClientWentAway {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Client_went_away")
    }
}

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

/// `client`: an instance of hh_client calling clientConnect.rpc (its
/// socket, tracker and priority), or the client of a test (which has no
/// socket: its request and its response are in the `crate::test_client_provider::T`).
pub enum Client {
    Socket(crate::server_client_provider::server_end::Client, crate::server_client_provider::Priority),
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

/// `S`
pub trait S {
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
    /// The agent session responsible for this client request, if any.
    fn agent_session_id(&self, c: &Client) -> Option<String>;
    /// Shutdown socket connection to client (errors are ignored; the
    /// descriptors are closed when the client is dropped).
    fn shutdown_client(&mut self, c: &mut Client);
    fn ping(&mut self, c: &mut Client) -> Result<(), ClientWentAway>;
    /// A provider on the same pipes, for the priority interrupt handler
    /// (the OCaml's provider is an immutable record that the handler's
    /// closure shares).
    fn clone_provider(&self) -> Box<dyn S + Send>;
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The exception's text (`exception::wrap` takes it from `Debug`) is the
    /// OCaml constructor's name.
    #[test]
    fn client_went_away_prints_its_ocaml_name() {
        assert_eq!(format!("{:?}", ClientWentAway), "Client_went_away");
    }
}
