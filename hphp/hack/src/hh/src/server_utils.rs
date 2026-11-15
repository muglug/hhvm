// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_utils.ml`: `handle_command_result`,
//! `wrap`, `exit_on_exception`, `with_exit_on_exception`,
//! `log_and_get_sharedmem_load_telemetry`, `make_next`.
//!
//! Not here: `wrap` (`client_command_handler::wrap`), `shutdown_client` (the
//! client provider's `shutdown_client`) and `resugar_invariant_call`.
//!
//! `exit_on_exception` tells the exceptions apart by the type of the
//! payload of [`exception::T`]. The exceptions of shared memory and of
//! worker processes cannot happen (there are neither here); a typing panic is
//! the `Coalesced_failures` of a worker that exited with 2
//! (`typing_check_service` raises it).

use std::sync::Arc;

use crate::exception;
use crate::exit;
use crate::exit_status;
use crate::find_utils;
use crate::hh_logger;
use crate::relative_path;
use crate::server_config;
use crate::server_env::Env;
use crate::server_env::FinishCommandHandling;
use crate::server_env::Genv;
use crate::server_init_common::GetNext;
use crate::server_notifier;
use crate::telemetry;
use crate::watchman;

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

/// `log_and_get_sharedmem_load_telemetry ()`: the load of the shared hash
/// table, logged and as telemetry. The OCaml's server always has its shared
/// heap; here the daemon has it, and so has check mode when its stores are on
/// the shared heap (`HH_RUST_WORKERS=1`, see `check::start_workers`). With
/// the in-process stores of check mode (the default) there is no hash table:
/// no "Hashtable load factor" line then, and an empty telemetry, rather than
/// figures of a table that does not exist. (The OCaml's `try_with_stack`
/// catches an exception of `hash_stats`, which cannot raise here.)
pub fn log_and_get_sharedmem_load_telemetry() -> telemetry::T {
    let telemetry = telemetry::create();
    if !crate::hh_shared::is_initialized() {
        return telemetry;
    }
    let crate::shared_mem::sm_telemetry::TableStats {
        used_slots,
        slots,
        nonempty_slots,
    } = crate::shared_mem::sm_telemetry::hash_stats();
    let load_factor = used_slots as f64 / slots as f64;
    crate::hh_logger::log(&format!(
        "Hashtable load factor: {} / {} ({}) with {} nonempty slots",
        used_slots,
        slots,
        crate::rt::ocaml_printf::sprintf_f(2, load_factor),
        nonempty_slots
    ));
    telemetry::float_("hashtable_load_factor", load_factor, telemetry)
}

/// `Exit_status.Exit_with ec -> Exit.exit ec` (the statuses raised as
/// `Exit_with` are constant constructors).
fn exit_with(ec: &exit_status::T, e: &exception::T) -> ! {
    match exit_status::constant_constructor_of_name(exit_status::constructor_name(ec)) {
        Some(ec) => exit::exit(None, None, None, None, ec),
        None => exit::exit(
            None,
            None,
            None,
            None,
            exit_status::T::UncaughtException(exception::wrap(crate::rt::protocol::UncaughtReadError(
                exception::get_ctor_string(e),
            ))),
        ),
    }
}

/// `exit_on_exception e`: exit with exit code corresponding to given
/// exception. Perform any necessary cleanups.
pub fn exit_on_exception(e: exception::T) -> ! {
    let payload = exception::unwrap(&e);
    if let Some(exn) = payload.downcast_ref::<watchman::Exn>() {
        match exn {
            watchman::Exn::WatchmanError(s) => {
                hh_logger::exception_(None, &e);
                hh_logger::log(&format!("Exiting. Failed due to watchman error: {}", s));
                exit::exit(None, None, None, None, exit_status::T::WatchmanFailed)
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
        let failure_msg = "Coalesced_failures[(Worker_quit WEXITED 2)]";
        // (`Hh_logger.exception_ e`: the exception is printed as the
        // OCaml's printer prints it.)
        hh_logger::exc(None, &exception::get_backtrace_string(&e), failure_msg);
        hh_logger::log(failure_msg);
        // We attempt to exit with the same code as a worker by folding over
        // all the failures and looking for a WEXITED.
        // Exit with same code, but through `exit::exit` so that its hooks run:
        // a still-alive Edenfs_watcher instance makes Folly's exit handlers hang.
        exit::exit(
            Some(failure_msg.to_string()),
            None,
            None,
            Some(2),
            exit_status::T::UncaughtException(e),
        )
    }
    hh_logger::exception_(None, &e);
    exit::exit(None, None, None, None, exit_status::T::UncaughtException(e))
}

/// `with_exit_on_exception f`: execute given function. If function raises
/// and exception, exit with exit code corresponding to given exception.
/// Perform any necessary cleanups. (A panic in `f` is an exception.)
pub fn with_exit_on_exception<A>(f: impl FnOnce() -> A) -> A {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(a) => a,
        Err(payload) => exit_on_exception(exception::wrap(payload)),
    }
}

/// `Server_utils.make_next ?hhi_filter ~indexer ~extra_roots`: the hhi
/// files (those of the context: the binary's, which `Hhi.get_hhi_root ()`
/// extracts), then the files the indexer gives (under the root), then those
/// of the extra roots.
pub fn make_next(
    genv: &Genv,
    ctx: &Arc<crate::ctx::Ctx>,
    hhi_filter: Option<fn(&str) -> bool>,
) -> GetNext {
    let hhi_filter = hhi_filter.unwrap_or(find_utils::is_hack);
    let hhi_files: Vec<relative_path::T> = ctx
        .hhi_paths
        .iter()
        .map(|p| relative_path::T::from(*p))
        .filter(|p| hhi_filter(&relative_path::suffix(p)))
        .collect();
    let indexer = server_notifier::indexer(&genv.notifier, Box::new(find_utils::file_filter));
    let extra_roots = server_config::extra_paths(&genv.config);
    Box::new(move || {
        let mut files = hhi_files;
        let mut next = match indexer {
            Ok(next) => next,
            Err(e) => std::panic::panic_any(e),
        };
        loop {
            let batch = next();
            if batch.is_empty() {
                break;
            }
            files.extend(
                batch
                    .iter()
                    .map(|f| relative_path::create(relative_path::Prefix::Root, f)),
            );
        }
        for root in &extra_roots {
            let mut next = crate::find::make_next_files(
                None,
                None,
                Some(Box::new(find_utils::file_filter)),
                None,
                root,
            );
            loop {
                let batch = next();
                if batch.is_empty() {
                    break;
                }
                files.extend(batch.iter().map(|f| relative_path::create_detect_prefix(f)));
            }
        }
        files
    })
}

#[cfg(test)]
mod tests {
    /// A panic of the typing service (`CoalescedFailures`) ends the server
    /// as a worker failure does in the OCaml: `exit 2` (the worker's
    /// `Exit_status.Type_error`), after logging `Coalesced_failures[...]`.
    #[test]
    fn coalesced_failures_exit_2() {
        if std::env::var("HH_SRV_TEST_COALESCED").is_ok() {
            let payload: Box<dyn std::any::Any + Send> =
                Box::new(crate::typing_check_service::CoalescedFailures {
                    path: ::relative_path::RelativePath::make(
                        ::relative_path::Prefix::Root,
                        "a.php".into(),
                    ),
                    message: "boom".to_string(),
                });
            super::exit_on_exception(crate::exception::wrap(payload))
        }
        let exe = std::env::current_exe().unwrap();
        let out = std::process::Command::new(exe)
            .args(["--exact", "server_utils::tests::coalesced_failures_exit_2", "--nocapture"])
            .env("HH_SRV_TEST_COALESCED", "1")
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2));
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(stderr.contains("] Coalesced_failures[(Worker_quit WEXITED 2)]"), "{}", stderr);
    }
}
