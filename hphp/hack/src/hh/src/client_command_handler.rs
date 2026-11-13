// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/client_command_handler.ml`: a client handed off by the
//! monitor, from its connection type to the end of its command.
//!
//! Owned by **SRV** (plan §3.1).

use crate::connection_tracker::Key;
use crate::exception;
use crate::hh_logger;
use crate::rt::client_provider::Client;
use crate::rt::client_provider::ClientError;
use crate::rt::client_provider::ClientProvider;
use crate::server_command;
use crate::server_command::FallibleFinish;
use crate::server_command::HandleResult;
use crate::server_command_types::ConnectionType;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_idle;
use crate::server_utils::HandleCommandResult;

/// `NonPersistent.handle_client_command_exception ~env ~client e`
pub fn handle_client_command_exception(
    env: Env,
    cp: &mut dyn ClientProvider,
    client: &mut Client,
    e: ClientError,
) -> Env {
    match e {
        // (`Typing_deps.Depgraph_unavailable _ -> Server_utils.exit_on_exception
        // e`: the dependency graph is in memory, it cannot be unavailable.)
        ClientError::ClientWentAway | ClientError::ReadCommandTimeout => {
            hh_logger::log(
                "Client went away or server took too long to read command. Shutting down client socket.",
            );
            cp.shutdown_client(client);
            env
        }
        // Connection dropped off. Its unforunate that we don't actually know
        // which connection went bad (could be any write to any connection to
        // child processes/daemons), we just assume at this top-level that
        // since it's not caught elsewhere, it's the connection to the client.
        ClientError::ChannelWentBad(_) => {
            hh_logger::log("Client channel went bad. Shutting down client socket");
            cp.shutdown_client(client);
            env
        }
        ClientError::Other(e) => {
            hh_logger::log(&format!(
                "HANDLE_CONNECTION_EXCEPTION(inner) {}",
                exception::to_string(&e)
            ));
            cp.shutdown_client(client);
            env
        }
    }
}

/// `Server_utils.wrap ~try_:(handle_client_command_try (fun x -> x) client)`:
/// the continuation of a `Needs_full_recheck`, its exception handled.
fn wrap(r: HandleResult) -> HandleCommandResult {
    match r {
        HandleResult::Done(env) => HandleCommandResult::Done(env),
        HandleResult::NeedsFullRecheck {
            env,
            finish_command_handling,
            reason,
        } => {
            let f: FallibleFinish = finish_command_handling;
            HandleCommandResult::NeedsFullRecheck {
                env,
                finish_command_handling: Box::new(move |genv, cp, client, env| {
                    match f(genv, cp, client, env) {
                        Ok(env) => env,
                        Err((e, env)) => handle_client_command_exception(env, cp, client, e),
                    }
                }),
                reason,
            }
        }
    }
}

/// `NonPersistent.handle_client_command_or_persistent_connection_`
fn handle_client_command_or_persistent_connection_(
    genv: &Genv,
    env: Env,
    cp: &mut dyn ClientProvider,
    client: &mut Client,
) -> Result<HandleResult, server_command::CommandError> {
    cp.track(client, Key::ServerStartHandleConnection, None, None, None, None);
    match cp.read_connection_type(client) {
        Err(e) => Err((e, env)),
        Ok(ConnectionType::NonPersistent) => {
            hh_logger::log("Handling non-persistent client command.");
            server_command::handle(genv, env, cp, client)
        }
    }
}

/// `handle_client_command_or_persistent_connection genv env client`
pub fn handle_client_command_or_persistent_connection(
    genv: &Genv,
    env: Env,
    cp: &mut dyn ClientProvider,
    client: &mut Client,
) -> HandleCommandResult {
    server_idle::stamp_connection();
    hh_logger::log_with(
        None,
        Some("clients"),
        "Handling non-persistent client command or persistent client connection.",
    );
    // [command] represents a non-persistent command coming from client. If executing [command]
    // throws, we need to dispose of this client (possibly recovering updated
    // environment from Nonfatal_rpc_exception).
    let r = match handle_client_command_or_persistent_connection_(genv, env, cp, client) {
        Ok(r) => r,
        Err((e, env)) => HandleResult::Done(handle_client_command_exception(env, cp, client, e)),
    };
    // Similarly to persistent client commands, we wrap in handle_client_command_try a second time here.
    wrap(r)
}
