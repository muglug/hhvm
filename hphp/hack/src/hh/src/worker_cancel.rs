// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `worker_cancel.ml`. See `hh/PORTING.md`.
//!
//! OCaml workers are processes that share memory with the master; here a
//! worker is a thread. The `external`s of the OCaml are implemented in
//! `heap/hh_shared.c` over two flags, which become:
//!
//! - `workers_should_exit`, in shared memory (set by the master, read by
//!   every worker): a flag of the process, [`WORKERS_SHOULD_EXIT`]. In C it
//!   is a pointer that is null until shared memory is initialised, and no
//!   cancellation can be requested before; here the flag always exists and
//!   starts unset, which is the same thing.
//! - `worker_can_exit`, a static of each worker process: a flag of each
//!   thread, [`WORKER_CAN_EXIT`]. `with_no_cancellations_nested` is a
//!   global `ref` of each process, so it is one of each thread too.
//!
//! `hh_stop_workers` and `hh_resume_workers` also `assert_master ()` (that
//! they run in the master process): threads have no master, so there is
//! nothing to check.
//!
//! `exception Worker_should_exit` is caught far from where it is raised
//! (around the work of a job), so it is the payload of a panic,
//! [`WorkerShouldExit`]: `std::panic::panic_any(WorkerShouldExit)` raises it
//! and `std::panic::catch_unwind` with a downcast catches it.

use std::cell::Cell;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

/// This exception might be thrown in code which executes in Multi_worker
/// workers. If you happen to catch it, the best course of action is to
/// re-throw it to guarantee speedy cancellation.
///
/// `exception Worker_should_exit`: the payload of the panic that raises it.
/// (`Callback.register_exception "worker_should_exit" Worker_should_exit` lets
/// the C code raise it; [`raise_if_stop_requested`] raises it here.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WorkerShouldExit;

impl std::fmt::Display for WorkerShouldExit {
    /// `Printexc.to_string Worker_should_exit`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Worker_cancel.Worker_should_exit")
    }
}

impl std::error::Error for WorkerShouldExit {}

/// `workers_should_exit` of `hh_shared.c`: set by `stop_workers`, seen by
/// every worker.
static WORKERS_SHOULD_EXIT: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// `worker_can_exit` of `hh_shared.c`, one for each worker.
    static WORKER_CAN_EXIT: Cell<bool> = const { Cell::new(true) };

    /// `with_no_cancellations_nested`
    static WITH_NO_CANCELLATIONS_NESTED: Cell<bool> = const { Cell::new(false) };
}

/// `external stop_workers : unit -> unit = "hh_stop_workers"`
pub fn stop_workers() {
    WORKERS_SHOULD_EXIT.store(true, Ordering::SeqCst);
}

/// `external resume_workers : unit -> unit = "hh_resume_workers"`
pub fn resume_workers() {
    WORKERS_SHOULD_EXIT.store(false, Ordering::SeqCst);
}

/// `external set_can_worker_stop : bool -> unit = "hh_set_can_worker_stop"`
fn set_can_worker_stop(val: bool) {
    WORKER_CAN_EXIT.with(|can_exit| can_exit.set(val));
}

/// `should_exit` of `hh_shared.c`.
///
/// [`WORKER_CAN_EXIT`] is used by [`with_no_cancellations`] to protect
/// critical regions against cancellation. The content of
/// [`WORKERS_SHOULD_EXIT`] is set by [`stop_workers`].
fn should_exit() -> bool {
    WORKER_CAN_EXIT.with(Cell::get) && WORKERS_SHOULD_EXIT.load(Ordering::SeqCst)
}

/// `external is_stop_requested : unit -> bool = "hh_should_exit"`
pub fn is_stop_requested() -> bool {
    should_exit()
}

/// `external raise_if_stop_requested : unit -> unit = "hh_raise_if_should_exit"`
pub fn raise_if_stop_requested() {
    if should_exit() {
        std::panic::panic_any(WorkerShouldExit)
    }
}

pub fn with_no_cancellations<A>(f: impl FnOnce() -> A) -> A {
    if WITH_NO_CANCELLATIONS_NESTED.with(Cell::get) {
        panic!("with_no_cancellations cannot be nested");
    }
    WITH_NO_CANCELLATIONS_NESTED.with(|nested| nested.set(true));
    crate::utils::try_finally(
        || {
            set_can_worker_stop(false);
            f()
        },
        || {
            set_can_worker_stop(true);
            WITH_NO_CANCELLATIONS_NESTED.with(|nested| nested.set(false));
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// [`WORKERS_SHOULD_EXIT`] belongs to the process, and the tests run in
    /// parallel with others that may call `raise_if_stop_requested`: no test
    /// sets it. These check the flags of the thread.
    #[test]
    fn cancellation() {
        assert!(!is_stop_requested());
        raise_if_stop_requested();
        assert!(WORKER_CAN_EXIT.with(Cell::get));
        assert!(with_no_cancellations(|| !WORKER_CAN_EXIT.with(Cell::get)));
        assert!(WORKER_CAN_EXIT.with(Cell::get));
        // Another thread has flags of its own.
        let other = std::thread::spawn(|| {
            set_can_worker_stop(false);
            WORKER_CAN_EXIT.with(Cell::get)
        });
        assert!(!other.join().unwrap());
        assert!(WORKER_CAN_EXIT.with(Cell::get));
        assert_eq!(WorkerShouldExit.to_string(), "Worker_cancel.Worker_should_exit");
    }

    #[test]
    fn no_nesting() {
        let nested = std::panic::catch_unwind(|| with_no_cancellations(|| with_no_cancellations(|| ())));
        assert!(nested.is_err());
        // The outer call restored the flags as it unwound.
        assert!(!WITH_NO_CANCELLATIONS_NESTED.with(Cell::get));
        assert!(WORKER_CAN_EXIT.with(Cell::get));
        assert_eq!(with_no_cancellations(|| 1), 1);
    }
}
