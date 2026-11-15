// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/client_command_handler.ml`: a client handed off by the
//! monitor, from its connection type to the end of its command.
//!
//! Handle client command messages and connections from persistent clients.

use crate::connection_tracker::Key;
use crate::exception;
use crate::hh_logger;
use crate::client_provider_sig::Client;
use crate::client_provider_sig::ClientError;
use crate::client_provider_sig;
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
    cp: &mut dyn client_provider_sig::S,
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

/// `handle_client_command_try return client env command`: runs `command`;
/// what it raises (an error, or a panic) is handled by
/// [`handle_client_command_exception`] with the environment from before the
/// command. `env` goes to `command`; its pending command is kept out of
/// it and put back in the environment that comes out.
fn handle_client_command_try(
    cp: &mut dyn client_provider_sig::S,
    client: &mut Client,
    mut env: Env,
    command: impl FnOnce(&mut dyn client_provider_sig::S, &mut Client, Env) -> Result<HandleResult, server_command::CommandError>,
) -> HandleResult {
    let pending = env
        .nonpersistent_client_pending_command_needs_full_check
        .take();
    server_command::set_pre_command_env(&env);
    // (Every panic is reported below, with where it was raised, as the OCaml
    // logs the exception and its backtrace: the panic hook does not print it
    // too.)
    let r = crate::rt::quiet_panic::catch_reported(|_| true, || command(&mut *cp, &mut *client, env));
    let r = match r {
        Ok(Ok(r)) => r,
        Ok(Err((e, env))) => HandleResult::Done(handle_client_command_exception(env, cp, client, e)),
        Err(payload) => {
            let env = server_command::take_pre_command_env()
                .expect("the environment from before the command");
            HandleResult::Done(handle_client_command_exception(
                env,
                cp,
                client,
                ClientError::Other(exception::wrap_with_raise_site(
                    payload,
                    crate::rt::quiet_panic::take_raise_site(),
                )),
            ))
        }
    };
    let _ = server_command::take_pre_command_env();
    let put_back = |mut env: Env| {
        env.nonpersistent_client_pending_command_needs_full_check = pending;
        env
    };
    match r {
        HandleResult::Done(env) => HandleResult::Done(put_back(env)),
        HandleResult::NeedsFullRecheck {
            env,
            finish_command_handling,
            reason,
        } => HandleResult::NeedsFullRecheck {
            env: put_back(env),
            finish_command_handling,
            reason,
        },
    }
}

/// `Server_utils.wrap ~try_:(handle_client_command_try (fun x -> x) client)`:
/// the continuation of a `Needs_full_recheck`, its exceptions handled.
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
                    match handle_client_command_try(cp, client, env, |cp, client, env| {
                        f(genv, cp, client, env).map(HandleResult::Done)
                    }) {
                        HandleResult::Done(env) => env,
                        HandleResult::NeedsFullRecheck { .. } => unreachable!(),
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
    cp: &mut dyn client_provider_sig::S,
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
    cp: &mut dyn client_provider_sig::S,
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
    let r = handle_client_command_try(cp, client, env, |cp, client, env| {
        handle_client_command_or_persistent_connection_(genv, env, cp, client)
    });
    // Similarly to persistent client commands, we wrap in handle_client_command_try a second time here.
    wrap(r)
}
