// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_worker.ml`: the server's worker processes
//! (`crate::worker_controller`), with the call wrapper of their calls. See
//! `hh/PORTING.md`.
//!
//! The worker processes are made only with `HH_RUST_WORKERS=1`
//! (`multi_worker::workers_switched_on`): by default the threads of the
//! server's pool do the workers' work, in the master, where nothing needs
//! classifying or installing.
//!
//! The OCaml's `entry` (`Worker_controller_entry_point.register ~restore:
//! Server_global_state.restore`) is `crate::worker::ENTRY`, registered by
//! `crate::worker::run_if_worker`.

use serde::Deserialize;
use serde::Serialize;

use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::worker_controller;

/// The name of the call wrapper of [`make_call_wrapper`]
/// (`crate::worker_jobs::wrap` runs [`wrap`] under it in the worker).
pub const CALL_WRAPPER: &str = "Server_worker.make_call_wrapper";

/// The global provider backend that [`make_call_wrapper`] sends from the
/// master (`Provider_backend.t`, of the backends it sends: the port has
/// `Shared_memory`, and neither `Pessimised_shared_memory` nor
/// `Rust_provider_backend`, see `crate::provider_backend`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GlobalBackend {
    SharedMemory,
}

/// We use the call_wrapper to classify some exceptions in all calls in the
/// same way. (`catch_and_classify_exceptions f x`.)
///
/// `Stdlib.Not_found` and `Not_found_s` (`Worker_not_found_exception`) have
/// no counterpart: a missing entry is an `Option` here, never a panic.
pub fn catch_and_classify_exceptions<B>(f: impl FnOnce() -> B) -> B {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(b) => b,
        Err(exn) => {
            // `Decl_class.Decl_heap_elems_bug` is a panic with this message
            // (`decl_class::raise_decl_heap_elems_bug`).
            if crate::worker::panic_message(&exn).starts_with("Decl_class.Decl_heap_elems_bug(") {
                exit::exit(None, None, None, None, exit_status::T::DeclHeapElemsBug)
            } else if exn.is::<crate::file_provider::FileProviderStale>() {
                exit::exit(None, None, None, None, exit_status::T::FileProviderStale)
            } else if let Some(crate::typing_deps::DepgraphUnavailable(error)) =
                exn.downcast_ref::<crate::typing_deps::DepgraphUnavailable>()
            {
                let msg = crate::typing_deps::depgraph_load_error_to_string(error);
                hh_logger::log(&format!("Dependency graph unavailable: {}", msg));
                exit::exit(Some(msg), None, None, None, exit_status::T::DepgraphUnavailable)
            } else if let Some(crate::decl_defs::DeclNotFound(x)) =
                exn.downcast_ref::<crate::decl_defs::DeclNotFound>()
            {
                hh_logger::log(&format!("Decl_not_found {}", x));
                exit::exit(None, None, None, None, exit_status::T::DeclNotFound)
            } else {
                std::panic::resume_unwind(exn)
            }
        }
    }
}

/// `get_master_global_backend ~set_global_provider_backend_in_workers ()`:
/// this runs in the main process.
fn get_master_global_backend(
    set_global_provider_backend_in_workers: bool,
) -> Option<GlobalBackend> {
    if set_global_provider_backend_in_workers {
        // `Provider_backend.get ()`: the backend of the contexts made from
        // now on, which is `Shared_memory` when their stores are on the
        // shared heap (`crate::ctx::use_shared_memory_stores`).
        if crate::ctx::shared_memory_stores() {
            Some(GlobalBackend::SharedMemory)
        } else {
            // The stores are maps of this process (as `Local_memory`): we
            // could support this, but it would mean serializing the entire
            // store and copying it over to the worker.
            None
        }
    } else {
        None
    }
}

/// `install_worker_global_backend`: this runs in the worker.
fn install_worker_global_backend(backend: Option<GlobalBackend>) {
    match backend {
        None => {}
        // `Provider_backend.set_shared_memory_backend ()`
        Some(GlobalBackend::SharedMemory) => crate::ctx::use_shared_memory_stores(true),
    }
}

/// The `wrap` of [`make_call_wrapper`], in the worker: `data` is what its
/// `prepare` gave in the master.
pub fn wrap<B>(data: &[u8], f: impl FnOnce() -> B) -> B {
    let backend: Option<GlobalBackend> =
        crate::worker::decode(data).expect("Server_worker: a corrupt call wrapper data");
    catch_and_classify_exceptions(|| {
        install_worker_global_backend(backend);
        f()
    })
}

/// `make_call_wrapper ~set_global_provider_backend_in_workers`
pub fn make_call_wrapper(
    set_global_provider_backend_in_workers: bool,
) -> worker_controller::CallWrapper {
    worker_controller::CallWrapper {
        prepare: std::sync::Arc::new(move || {
            crate::worker::encode(&get_master_global_backend(
                set_global_provider_backend_in_workers,
            ))
        }),
        wrap: CALL_WRAPPER,
    }
}

/// `make ~longlived_workers ~set_global_provider_backend_in_workers
/// ~nbr_procs gc_control heap_handle ~logging_init` (the workers are not
/// long-lived, and there is no OCaml GC; `trace`: see
/// `Worker_controller.make`).
pub fn make(
    set_global_provider_backend_in_workers: bool,
    nbr_procs: usize,
    heap_handle: &crate::hh_shared::Handle,
    trace: bool,
) -> std::io::Result<Vec<worker_controller::Worker>> {
    worker_controller::make(
        Some(make_call_wrapper(set_global_provider_backend_in_workers)),
        nbr_procs,
        heap_handle,
        trace,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Without `set_global_provider_backend_in_workers`, no backend is sent.
    #[test]
    fn no_backend_without_the_option() {
        let wrapper = make_call_wrapper(false);
        let data = (wrapper.prepare)();
        assert_eq!(
            crate::worker::decode::<Option<GlobalBackend>>(&data).unwrap(),
            None
        );
        assert_eq!(wrapper.wrap, CALL_WRAPPER);
    }

    /// The master's backend as the option asks for it: none when its stores
    /// are not on the shared heap.
    #[test]
    fn backend_of_the_master() {
        let expected = crate::ctx::shared_memory_stores().then_some(GlobalBackend::SharedMemory);
        assert_eq!(get_master_global_backend(true), expected);
    }

    /// `wrap` runs the job and gives its result.
    #[test]
    fn wrap_runs_the_job() {
        let data = crate::worker::encode(&None::<GlobalBackend>);
        assert_eq!(wrap(&data, || 42), 42);
    }

    /// What `catch_and_classify_exceptions` does not classify goes through.
    #[test]
    fn other_panics_go_through() {
        let r = std::panic::catch_unwind(|| {
            catch_and_classify_exceptions(|| -> () { panic!("other") })
        });
        assert_eq!(crate::worker::panic_message(&r.unwrap_err()), "other");
    }
}
