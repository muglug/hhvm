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
//!   every worker): the flag of a group of workers, [`Workers`]. Shared
//!   memory is what a master and its workers have in common; here that is
//!   the group, which the master makes for one multi-worker call and each of
//!   its worker threads enters ([`Workers::enter`]). (One flag for the whole
//!   process would also stop the threads of another server of the process:
//!   the tests run several at once.) In C the flag is a pointer that is null
//!   until shared memory is initialised, and no cancellation can be
//!   requested before; a thread that is in no group is never asked to stop,
//!   which is the same thing.
//! - `worker_can_exit`, a static of each worker process: a flag of each
//!   thread, [`WORKER_CAN_EXIT`]. `with_no_cancellations_nested` is a
//!   global `ref` of each process, so it is one of each thread too.
//!
//! `hh_stop_workers` and `hh_resume_workers` also `assert_master ()` (that
//! they run in the master process): they are methods of the group, which
//! the master holds.
//!
//! `exception Worker_should_exit` is caught far from where it is raised
//! (around the work of a job), so it is the payload of a panic,
//! [`WorkerShouldExit`]: `std::panic::panic_any(WorkerShouldExit)` raises it
//! and `std::panic::catch_unwind` with a downcast catches it.

use std::cell::Cell;
use std::cell::RefCell;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

/// This exception might be thrown in code which executes in Multi_worker
/// workers. If you happen to catch it, the best course of action is to
/// re-throw it to guarantee speedy cancellation.
///
/// `exception Worker_should_exit`: the payload of the panic that raises it.
/// (`Callback.register_exception "worker_should_exit" Worker_should_exit` lets
/// the C raise it: here [`raise_if_stop_requested`] does.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkerShouldExit;

impl std::fmt::Display for WorkerShouldExit {
    /// `Printexc.to_string Worker_should_exit`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Worker_cancel.Worker_should_exit")
    }
}

impl std::error::Error for WorkerShouldExit {}

/// The workers of one master: what shares the `workers_should_exit` of
/// `hh_shared.c` (see the module documentation).
#[derive(Clone, Debug, Default)]
pub struct Workers {
    /// `workers_should_exit`: set by `stop_workers`, seen by every worker of
    /// the group.
    should_exit: Arc<AtomicBool>,
}

/// How many groups are asked to stop now. It is zero except while a
/// cancellation is under way, so [`should_exit`], which runs at every read
/// of a decl store, reads nothing else.
static STOPPED_GROUPS: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// The group this thread is a worker of.
    static WORKERS: RefCell<Option<Workers>> = const { RefCell::new(None) };

    /// `worker_can_exit` of `hh_shared.c`, one for each worker.
    static WORKER_CAN_EXIT: Cell<bool> = const { Cell::new(true) };

    /// `with_no_cancellations_nested`
    static WITH_NO_CANCELLATIONS_NESTED: Cell<bool> = const { Cell::new(false) };
}

/// A thread's membership of a group, until it is dropped (see
/// [`Workers::enter`]).
pub struct Entered {
    previous: Option<Workers>,
}

impl Drop for Entered {
    fn drop(&mut self) {
        let previous = self.previous.take();
        WORKERS.with(|workers| *workers.borrow_mut() = previous);
    }
}

impl Workers {
    pub fn new() -> Workers {
        Workers::default()
    }

    /// The calling thread is a worker of this group until the result is
    /// dropped (a worker process of the OCaml is one for its whole life; a
    /// thread of the pool works for one call at a time).
    pub fn enter(&self) -> Entered {
        let previous = WORKERS.with(|workers| workers.borrow_mut().replace(self.clone()));
        Entered { previous }
    }

    /// `external stop_workers : unit -> unit = "hh_stop_workers"`
    pub fn stop_workers(&self) {
        if !self.should_exit.swap(true, Ordering::SeqCst) {
            STOPPED_GROUPS.fetch_add(1, Ordering::SeqCst);
        }
    }

    /// `external resume_workers : unit -> unit = "hh_resume_workers"`
    pub fn resume_workers(&self) {
        if self.should_exit.swap(false, Ordering::SeqCst) {
            STOPPED_GROUPS.fetch_sub(1, Ordering::SeqCst);
        }
    }
}

/// `external set_can_worker_stop : bool -> unit = "hh_set_can_worker_stop"`
fn set_can_worker_stop(val: bool) {
    WORKER_CAN_EXIT.with(|can_exit| can_exit.set(val));
}

/// `should_exit` of `hh_shared.c`.
///
/// [`WORKER_CAN_EXIT`] is used by [`with_no_cancellations`] to protect
/// critical regions against cancellation. The flag of the group is set by
/// [`Workers::stop_workers`].
#[inline]
fn should_exit() -> bool {
    STOPPED_GROUPS.load(Ordering::Relaxed) != 0 && should_exit_slow()
}

#[cold]
#[inline(never)]
fn should_exit_slow() -> bool {
    WORKER_CAN_EXIT.with(Cell::get)
        && WORKERS.with(|workers| {
            workers
                .borrow()
                .as_ref()
                .is_some_and(|workers| workers.should_exit.load(Ordering::SeqCst))
        })
}

/// `external is_stop_requested : unit -> bool = "hh_should_exit"`
pub fn is_stop_requested() -> bool {
    should_exit()
}

/// `external raise_if_stop_requested : unit -> unit = "hh_raise_if_should_exit"`
///
/// Also `raise_if_should_exit` of `hh_shared.c`, which the reads and writes
/// of shared memory start with (`hh_get_and_deserialize`, `hh_mem`,
/// `hh_add`): that is how a worker that is asked to stop does, at its next
/// lookup of a declaration. The stores of a `crate::ctx::Ctx` stand for
/// those heaps, and their reads call this (`decl_provider::store_result`,
/// `decl_store::store_result`).
#[inline]
pub fn raise_if_stop_requested() {
    if should_exit() {
        raise_worker_should_exit()
    }
}

#[cold]
#[inline(never)]
fn raise_worker_should_exit() -> ! {
    // (`resume_unwind`: an exception that is caught, not a failure: the
    // panic hook, which prints a message and a backtrace, does not run.)
    std::panic::resume_unwind(Box::new(WorkerShouldExit))
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

    /// The workers of a group are asked to stop, and no other thread is.
    #[test]
    fn stop_and_resume_workers() {
        let workers = Workers::new();
        let other_group = Workers::new();
        workers.stop_workers();
        // The master is no worker of its group.
        assert!(!is_stop_requested());
        {
            let _entered = other_group.enter();
            assert!(!is_stop_requested());
        }
        let in_worker = |workers: &Workers| {
            let workers = workers.clone();
            std::thread::spawn(move || {
                let _entered = workers.enter();
                let stop_requested = is_stop_requested();
                // Critical regions are protected against cancellation.
                assert!(with_no_cancellations(|| !is_stop_requested()));
                let raised = std::panic::catch_unwind(raise_if_stop_requested);
                let raised = match raised {
                    Ok(()) => false,
                    Err(exn) => exn.is::<WorkerShouldExit>(),
                };
                (stop_requested, raised)
            })
            .join()
            .unwrap()
        };
        assert_eq!(in_worker(&workers), (true, true));
        // (Stopping twice is stopping once.)
        workers.stop_workers();
        workers.resume_workers();
        assert_eq!(in_worker(&workers), (false, false));
        // A thread leaves its group, for the one it was in before.
        {
            let _outer = other_group.enter();
            {
                let _inner = workers.enter();
                workers.stop_workers();
                assert!(is_stop_requested());
            }
            assert!(!is_stop_requested());
            workers.resume_workers();
        }
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
