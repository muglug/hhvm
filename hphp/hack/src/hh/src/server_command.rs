// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_command.ml`: handling a client's command, and
//! parking the ones that need a full check until `Full_check_done`.
//!
//! The exceptions of handling a command are the `Err` of the functions
//! here, with the environment the OCaml's handler gets back: the one from
//! before the command (`Nonfatal_rpc_exception (e, env)` when
//! `Server_rpc.handle` raises, here panics; the environment of the
//! enclosing `try` otherwise, which is the same one).

use crate::connection_tracker::Key;
use crate::diagnostics;
use crate::exception;
use crate::hh_logger;
use crate::client_provider_sig::Client;
use crate::client_provider_sig::ClientError;
use crate::client_provider_sig;
use crate::server_command_types;
use crate::server_command_types::Command;
use crate::server_command_types_utils;
use crate::server_env;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_progress;
use crate::server_rpc;
use crate::typing_deps;

/// What handling a command failed with, and the environment to go on with.
pub type CommandError = (ClientError, Env);

/// The continuation of a command that needs a full check, which may fail.
pub type FallibleFinish = Box<
    dyn FnOnce(&Genv, &mut dyn client_provider_sig::S, &mut Client, Env) -> Result<Env, CommandError>
        + Send,
>;

/// `Server_utils.handle_command_result` before `Client_command_handler`
/// wraps the continuation in its `try`.
pub enum HandleResult {
    Done(Env),
    NeedsFullRecheck {
        env: Env,
        finish_command_handling: FallibleFinish,
        reason: String,
    },
}

/// `reason = Server_command_types_utils.debug_describe_cmd`
pub fn reason(msg: &Command) -> String {
    server_command_types_utils::debug_describe_cmd(msg)
}

/// Only grant access to dependency table to commands that declared that they
/// need full check - without full check, there are no guarantees about
/// dependency table being up to date.
fn with_dependency_table_reads<A>(
    mode: &typing_deps::mode::T,
    full_recheck_needed: bool,
    f: impl FnOnce() -> A,
) -> A {
    let deptable_unlocked = if full_recheck_needed {
        Some(typing_deps::allow_dependency_table_reads(mode, true))
    } else {
        None
    };
    crate::utils::try_finally(f, || {
        if let Some(deptable_unlocked) = deptable_unlocked {
            let _: bool = typing_deps::allow_dependency_table_reads(mode, deptable_unlocked);
        }
    })
}

#[cfg(test)]
pub(crate) type RpcHook = fn(
    &Genv,
    Env,
    bool,
    &server_command_types::CmdMetadata,
    server_command_types::T,
) -> (Env, server_command_types::CommandResult);

#[cfg(test)]
thread_local! {
    /// What the tests put instead of `Server_rpc.handle`.
    pub(crate) static RPC_FOR_TEST: std::cell::RefCell<Option<RpcHook>> =
        const { std::cell::RefCell::new(None) };
}

thread_local! {
    /// The environment from before the command being handled: what the
    /// OCaml's handlers get back when handling it raises (the `env` of
    /// `Client_command_handler.handle_client_command_try`, and of
    /// `Nonfatal_rpc_exception (e, env)`, which is the same one). One copy per
    /// command, made by `Client_command_handler` when the command starts.
    static PRE_COMMAND_ENV: std::cell::RefCell<Option<Env>> = const { std::cell::RefCell::new(None) };
}

/// Records a copy of `env` (without its pending command) as the
/// environment from before the command.
pub(crate) fn set_pre_command_env(env: &Env) {
    let copy = server_env::copy_without_pending_command(env);
    PRE_COMMAND_ENV.with(|e| *e.borrow_mut() = Some(copy))
}

/// Takes the environment from before the command, if one was recorded.
pub(crate) fn take_pre_command_env() -> Option<Env> {
    PRE_COMMAND_ENV.with(|e| e.borrow_mut().take())
}

fn has_pre_command_env() -> bool {
    PRE_COMMAND_ENV.with(|e| e.borrow().is_some())
}

/// The environment from before the command: the recorded one, or `local`
/// (the copy made here when none was recorded).
fn pre_command_env(local: Option<Env>) -> Env {
    match local {
        Some(env) => env,
        None => take_pre_command_env().expect("the environment from before the command"),
    }
}

/// `Server_rpc.handle ~is_stale genv env metadata cmd`, a panic being
/// `Nonfatal_rpc_exception (e, env)` with the environment from before the
/// command. (A copy of `env` is made here only when the caller recorded
/// none, [`set_pre_command_env`]; it is returned for the errors after the
/// RPC.)
fn handle_rpc(
    genv: &Genv,
    env: Env,
    is_stale: bool,
    metadata: &server_command_types::CmdMetadata,
    cmd: server_command_types::T,
) -> Result<(Env, server_command_types::CommandResult, Option<Env>), CommandError> {
    let local = if has_pre_command_env() {
        None
    } else {
        Some(server_env::copy_without_pending_command(&env))
    };
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        #[cfg(test)]
        {
            if let Some(f) = RPC_FOR_TEST.with(|h| *h.borrow()) {
                return f(genv, env, is_stale, metadata, cmd);
            }
        }
        server_rpc::handle(genv, env, is_stale, metadata, cmd)
    })) {
        Ok((env, result)) => Ok((env, result, local)),
        Err(payload) => Err((
            ClientError::Other(exception::wrap_with_raise_site(
                payload,
                crate::rt::quiet_panic::take_raise_site(),
            )),
            pre_command_env(local),
        )),
    }
}

/// Construct a continuation that will finish handling the command and update
/// the environment. The server can execute the continuation immediately, or store it
/// to be completed later (when full recheck is completed, when workers are
/// available, when current recheck is cancelled...
/// (`actually_handle genv client msg full_recheck_needed ~is_stale env`.)
pub fn actually_handle(
    genv: &Genv,
    cp: &mut dyn client_provider_sig::S,
    client: &mut Client,
    msg: Command,
    full_recheck_needed: bool,
    is_stale: bool,
    mut env: Env,
) -> Result<Env, CommandError> {
    hh_logger::debug(None, None, "SeverCommand.actually_handle preamble");
    // The command runs without the pending command of the environment (no
    // RPC reads it), which is put back in the environment that comes out.
    let pending = env
        .nonpersistent_client_pending_command_needs_full_check
        .take();
    let deps_mode = env.deps_mode.clone();
    let res = with_dependency_table_reads(&deps_mode, full_recheck_needed, || {
        diagnostics::ignore_(|| {
            assert!(
                !full_recheck_needed || server_env::is_full_check_done(env.full_check_status)
            );
            cp.track(
                client,
                Key::ServerDoneFullRecheck,
                None,
                None,
                None,
                Some(true),
            );
            let (metadata, cmd) = msg;
            if cp.ping(client).is_err() {
                return Err((ClientError::ClientWentAway, env));
            }
            let t_start = crate::rt::ocaml_unix::gettimeofday();
            cp.track(client, Key::ServerStartHandle, Some(t_start), None, None, None);
            let handle_request = |env: Env, cmd: server_command_types::T, cp: &mut dyn client_provider_sig::S, client: &mut Client| {
                let result = handle_rpc(genv, env, is_stale, &metadata, cmd)?;
                cp.track(client, Key::ServerEndHandle, None, Some(true), None, None);
                // (`Hack_event_logger.handled_command
                // ?agent_session_id:(Client_provider.agent_session_id client)`:
                // a no-op.)
                Ok(result)
            };
            match server_command_types::handle_after_send(&cmd) {
                None => {
                    let (new_env, response, backup) = handle_request(env, cmd, cp, client)?;
                    if let Err(e) = cp.send_response_to_client(client, response) {
                        return Err((e, pre_command_env(backup)));
                    }
                    cp.shutdown_client(client);
                    Ok(new_env)
                }
                Some((response, post_send_cmd)) => {
                    if let Err(e) = cp.send_response_to_client(client, response) {
                        return Err((e, env));
                    }
                    cp.shutdown_client(client);
                    let (new_env, _unit, _backup) = handle_request(env, post_send_cmd, cp, client)?;
                    Ok(new_env)
                }
            }
        })
    });
    let put_back = |mut env: Env| {
        env.nonpersistent_client_pending_command_needs_full_check = pending;
        env
    };
    match res {
        Ok(env) => Ok(put_back(env)),
        Err((e, env)) => Err((e, put_back(env))),
    }
}

/// `handle genv env client`: handle a client command. This can either execute
/// the command immediately, or store it as a continuation to be completed
/// later (when full recheck is completed, when workers are available, when
/// current recheck is cancelled...).
/// Invariant (checked in [Server_main.priority_client_interrupt_handler]):
/// if this returns anything other than [Done], then [use_priority_pipe] must
/// have returned false for the command we fetch from the client to handle.
pub fn handle(
    genv: &Genv,
    env: Env,
    cp: &mut dyn client_provider_sig::S,
    client: &mut Client,
) -> Result<HandleResult, CommandError> {
    // In the case if LSP, it's normal that this [Server_waiting_for_cmd]
    // track happens on a per-message basis, much later than the previous
    // [Server_got_connection_type] track that happened when the persistent
    // connection was established; the flag [long_delay_okay]
    // means that the default behavior, of alarming log messages in case of delays,
    // will be suppressed.
    cp.track(client, Key::ServerWaitingForCmd, None, None, None, Some(false));
    let msg = match cp.read_client_msg(client) {
        Ok(msg) => msg,
        Err(e) => return Err((e, env)),
    };
    // This is a helper to update progress.json to things like "[hh_client:idle done]" or "[HackAst:--type-at-pos check]"
    // or "[HackAst:--type-at-pos]". We try to balance something useful to the user, with something that helps the hack
    // team know what's going on and who is to blame.
    // The form is [FROM:CMD PHASE].
    let status = server_command_types_utils::status_describe_cmd(&msg);
    let send_progress = |phase: &str| {
        server_progress::write(Some(false), None, &format!("{}{}", status, phase))
    };
    // Once again, it's expected that [Server_got_cmd] happens a long time
    // after we started waiting for one!
    let got_cmd = format!(
        "{} [{}]",
        server_command_types_utils::debug_describe_cmd(&msg),
        cp.priority_to_string(client)
    );
    cp.track(client, Key::ServerGotCmd, None, Some(true), Some(&got_cmd), Some(false));
    let full_recheck_needed = server_command_types::rpc_command_needs_full_check(&msg.1);
    let is_stale = env.last_recheck_loop_stats.updates_stale;
    // (`let handle_command = send_progress ""; let r = actually_handle ...
    // in send_progress " done"; r`: a partial application, so both
    // messages are written now, before the command runs.)
    send_progress("");
    let reason = reason(&msg);
    send_progress(" done");
    if full_recheck_needed {
        send_progress(" typechecking");
        Ok(HandleResult::NeedsFullRecheck {
            env,
            finish_command_handling: Box::new(move |genv, cp, client, env| {
                actually_handle(genv, cp, client, msg, full_recheck_needed, is_stale, env)
            }),
            reason,
        })
    } else {
        actually_handle(genv, cp, client, msg, full_recheck_needed, is_stale, env)
            .map(HandleResult::Done)
    }
}
