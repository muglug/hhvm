// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_utils.ml`: `handle_command_result`,
//! `wrap`, `exit_on_exception`, `with_exit_on_exception`,
//! `log_and_get_sharedmem_load_telemetry`.
//!
//! Owned by **SRV** (plan §3.1).
//!
//! Not here: `shutdown_client` (the client provider's
//! `shutdown_client`), `make_next` (the indexer of the init, S1's) and
//! `resugar_invariant_call` (used by the IDE services, phase 2).
//!
//! `exit_on_exception` tells the exceptions apart by the type of the
//! payload of [`exception::T`]. The exceptions of shared memory and of
//! worker processes cannot happen (plan §6 rows 2-3); a typing panic is the
//! `Coalesced_failures` of a worker that exited with 2 (TCS raises it).

use crate::exception;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::rt::notifier_watchman as watchman;
use crate::server_env::Env;
use crate::server_env::FinishCommandHandling;
use crate::telemetry;

/// `'env handle_command_result` (with `'env = Server_env.env`).
pub enum HandleCommandResult {
    Done(Env),
    NeedsFullRecheck {
        env: Env,
        finish_command_handling: FinishCommandHandling,
        reason: String,
    },
}

// (`wrap ~try_`: `Client_command_handler` wraps the continuation of a
// `Needs_full_recheck` in its `try` itself, see
// `client_command_handler::wrap`.)

/// `log_and_get_sharedmem_load_telemetry ()`: there is no shared hash
/// table (plan §6 row 3), so no "Hashtable load factor" line and an empty
/// telemetry.
pub fn log_and_get_sharedmem_load_telemetry() -> telemetry::T {
    telemetry::create()
}

/// `Exit_status.Exit_with ec -> Exit.exit ec` (the statuses raised as
/// `Exit_with` are constant constructors).
fn exit_with(ec: &exit_status::T, e: &exception::T) -> ! {
    match exit_status::constant_constructor_of_name(exit_status::constructor_name(ec)) {
        Some(ec) => exit::exit(None, None, None, ec),
        None => exit::exit(
            None,
            None,
            None,
            exit_status::T::UncaughtException(exception::wrap(crate::rt::protocol::UncaughtReadError(
                exception::get_ctor_string(e),
            ))),
        ),
    }
}

/// `exit_on_exception e`
pub fn exit_on_exception(e: exception::T) -> ! {
    let payload = exception::unwrap(&e);
    if let Some(exn) = payload.downcast_ref::<watchman::Exn>() {
        match exn {
            watchman::Exn::WatchmanError(s) => {
                hh_logger::exception_(None, &e);
                hh_logger::log(&format!("Exiting. Failed due to watchman error: {}", s));
                exit::exit(None, None, None, exit_status::T::WatchmanFailed)
            }
            watchman::Exn::ExitWith(ec) => exit_with(ec, &e),
            _ => {}
        }
    }
    if let Some(exit_status::ExitWith(ec)) = payload.downcast_ref::<exit_status::ExitWith>() {
        exit_with(ec, &e)
    }
    if let Some(failures) = payload.downcast_ref::<crate::typing_check_service::CoalescedFailures>()
    {
        // `Multi_threaded_call.Coalesced_failures [Worker_quit (WEXITED
        // 2)]`: the worker that typed the file died of the exception
        // (`Worker.process_job_and_exit`: `Exit_status.Type_error`, i.e. 2).
        let _ = failures;
        hh_logger::exception_(None, &e);
        hh_logger::log("Coalesced_failures[(Worker_quit WEXITED 2)]");
        // We attempt to exit with the same code as a worker by folding over
        // all the failures and looking for a WEXITED. (`exit i`: not
        // `Exit.exit`, so no finale.)
        {
            use std::io::Write;
            let _ = std::io::stdout().flush();
            let _ = std::io::stderr().flush();
        }
        std::process::exit(2)
    }
    hh_logger::exception_(None, &e);
    exit::exit(None, None, None, exit_status::T::UncaughtException(e))
}

/// `with_exit_on_exception f`: a panic in `f` is an exception.
pub fn with_exit_on_exception<A>(f: impl FnOnce() -> A) -> A {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(a) => a,
        Err(payload) => exit_on_exception(exception::wrap(payload)),
    }
}
