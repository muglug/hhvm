// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/test_client_provider.ml`: a canned request,
//! the response captured.

use std::os::fd::RawFd;

use crate::client_provider_sig::*;
use crate::connection_tracker::Key;
use crate::server_command_types::CmdMetadata;
use crate::server_command_types::Command;
use crate::server_command_types::CommandResult;
use crate::server_command_types::ConnectionType;

/// `t`: what the OCaml keeps in its `Refs` (the mocked
/// connection type and request, the response recorded). It is not cleared
/// by reading: `sleep_and_check` gives a new client as long as
/// `new_client_type` is set.
#[derive(Default)]
pub struct T {
    pub new_client_type: Option<ConnectionType>,
    pub client_request: Option<crate::server_command_types::T>,
    pub client_response: Option<CommandResult>,
}

impl T {
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

impl S for T {
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

    fn agent_session_id(&self, _c: &Client) -> Option<String> {
        None
    }

    fn shutdown_client(&mut self, _c: &mut Client) {}

    fn ping(&mut self, _c: &mut Client) -> Result<(), ClientWentAway> {
        Ok(())
    }

    fn clone_provider(&self) -> Box<dyn S + Send> {
        // (`priority_fd` is `None`: no interrupt handler uses it.)
        Box::new(NoClients)
    }
}

/// A provider without clients: what a [`T`] gives to the
/// interrupt handlers (which it has no descriptor for).
struct NoClients;

impl S for NoClients {
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

    fn agent_session_id(&self, _c: &Client) -> Option<String> {
        None
    }

    fn shutdown_client(&mut self, _c: &mut Client) {}

    fn ping(&mut self, _c: &mut Client) -> Result<(), ClientWentAway> {
        Err(ClientWentAway)
    }

    fn clone_provider(&self) -> Box<dyn S + Send> {
        Box::new(NoClients)
    }
}
