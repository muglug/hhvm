// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: the jobs a worker's clone can run, by name. The
//! OCaml sends a marshalled closure (`Worker_controller.call w f x`); Rust
//! cannot marshal closures, so each `Multi_worker.call` site has a job here
//! that decodes its input, runs the function the OCaml's closure runs, and
//! encodes its output (`crate::worker`).

use std::cell::Cell;

thread_local! {
    static WORKER_ID: Cell<isize> = const { Cell::new(0) };
}

static PROCESS_WORKER_ID: std::sync::atomic::AtomicIsize = std::sync::atomic::AtomicIsize::new(0);

/// The id of the worker this process is (0 in the master): `Shared_mem.get_worker_id`.
pub fn set_worker_id(id: isize) {
    PROCESS_WORKER_ID.store(id, std::sync::atomic::Ordering::Relaxed);
    WORKER_ID.set(id);
}

/// `Shared_mem.get_worker_id ()`
pub fn worker_id() -> isize {
    PROCESS_WORKER_ID.load(std::sync::atomic::Ordering::Relaxed)
}

/// A job: its input's bytes to its output's bytes.
pub type JobFn = fn(&[u8]) -> Vec<u8>;

/// Wraps a typed job function as a [`JobFn`].
pub fn job<I: serde::de::DeserializeOwned, O: serde::Serialize>(f: fn(I) -> O, input: &[u8]) -> Vec<u8> {
    let input: I = crate::worker::decode(input).expect("Worker: a corrupt job input");
    crate::worker::encode(&f(input))
}

/// The test job: answers its input (a string) with the worker's id.
fn echo(input: String) -> (isize, String) {
    (worker_id(), input)
}

/// Runs the job `name` on `input` (in a clone), wrapped by its call wrapper
/// if it has one (`wrap data f x`, see `Worker_controller.CallWrapper`).
pub fn run_wrapped(call_wrapper: Option<&(String, Vec<u8>)>, name: &str, input: &[u8]) -> Vec<u8> {
    match call_wrapper {
        None => run(name, input),
        Some((wrapper, data)) => wrap(wrapper, data, || run(name, input)),
    }
}

/// The `wrap` of the call wrapper named `name` (`crate::worker_controller::CallWrapper`).
fn wrap(name: &str, data: &[u8], f: impl FnOnce() -> Vec<u8>) -> Vec<u8> {
    match name {
        crate::server_worker::CALL_WRAPPER => crate::server_worker::wrap(data, f),
        _ => panic!("Worker: unknown call wrapper {}", name),
    }
}

/// Runs the job `name` on `input` (in a clone).
pub fn run(name: &str, input: &[u8]) -> Vec<u8> {
    match name {
        "echo" => job(echo, input),
        _ => {
            #[cfg(feature = "port")]
            if let Some(out) = run_port(name, input) {
                return out;
            }
            panic!("Worker: unknown job {}", name)
        }
    }
}

#[cfg(feature = "port")]
fn run_port(name: &str, input: &[u8]) -> Option<Vec<u8>> {
    use crate::multi_worker::ServiceJob;
    match name {
        "Typing_check_service.process_workitems" => {
            Some(job(crate::typing_check_service::process_workitems_job, input))
        }
        "Direct_decl_service.parse" => Some(job(crate::check::declare_job, input)),
        crate::find_refs_service::FindRefsJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::find_refs_service::FindRefsJob>(input))
        }
        crate::symbol_info_service::SymbolInfoJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::symbol_info_service::SymbolInfoJob>(input))
        }
        crate::server_tast_holes_batch::TastHolesJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::server_tast_holes_batch::TastHolesJob>(input))
        }
        crate::server_go_to_impl::PositionsOfClassesJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::server_go_to_impl::PositionsOfClassesJob>(input))
        }
        crate::server_go_to_impl::PositionsOfMethodsJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::server_go_to_impl::PositionsOfMethodsJob>(input))
        }
        crate::server_lint::LintAndFilterJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::server_lint::LintAndFilterJob>(input))
        }
        crate::server_lint::LintJob::NAME => Some(crate::multi_worker::run_service::<crate::server_lint::LintJob>(input)),
        crate::server_infer_type_batch::InferTypeJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::server_infer_type_batch::InferTypeJob>(input))
        }
        crate::direct_decl_service::ParseBatchJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::direct_decl_service::ParseBatchJob>(input))
        }
        #[cfg(feature = "server")]
        crate::server_is_subtype::IsSubtypeJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::server_is_subtype::IsSubtypeJob>(input))
        }
        #[cfg(feature = "server")]
        crate::write_symbol_info::entrypoint::RecheckJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::write_symbol_info::entrypoint::RecheckJob>(input))
        }
        crate::method_jumps::MethodJumpsJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::method_jumps::MethodJumpsJob>(input))
        }
        crate::cst_search_service::CstSearchJob::NAME => {
            Some(crate::multi_worker::run_service::<crate::cst_search_service::CstSearchJob>(input))
        }
        <crate::server_rx_api_shared::RxApiJob<crate::server_fun_deps_batch::FunDepsHandlers> as ServiceJob>::NAME => Some(
            crate::multi_worker::run_service::<
                crate::server_rx_api_shared::RxApiJob<crate::server_fun_deps_batch::FunDepsHandlers>,
            >(input),
        ),
        "Decl_redecl_service.decl_files" => Some(job(crate::decl_redecl_service::workers::decl_files_job, input)),
        "Decl_redecl_service.load_defs_compare_and_get_fanout" => {
            Some(job(crate::decl_redecl_service::workers::compare_job, input))
        }
        "Decl_redecl_service.load_and_filter_descendant_classes" => {
            Some(job(crate::decl_redecl_service::workers::filter_job, input))
        }
        _ => None,
    }
}
