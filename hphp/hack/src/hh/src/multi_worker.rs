// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `procs/multi_worker.ml` and `procs/multi_threaded_call.ml`: a
//! parallel call over the workers (`crate::worker_controller`). See
//! `hh/PORTING.md`.
//!
//! The job of a call is named (`crate::worker_jobs`): its input is a bucket
//! (serde), its output what the worker's clone answers; `merge` folds the
//! outputs into the accumulator in the master, as they come.
//!
//! Also the master's set of workers ([`set_workers`], [`with_workers`]):
//! `genv.workers` of the OCaml, made once by `Server_main.setup_server` with
//! `HH_RUST_WORKERS=1` ([`workers_switched_on`]); without it there are none,
//! and every caller runs its buckets on the threads of the pool.

use std::os::fd::RawFd;
use std::sync::Mutex;

use crate::worker_controller;
use crate::worker_controller::Handle;
use crate::worker_controller::Worker;

/// `'a Bucket.bucket`
#[derive(Debug)]
pub enum Bucket<A> {
    Job(A),
    Wait,
    Done,
}

/// `Multi_threaded_call.cancel_reason`
#[derive(Clone, Debug)]
pub struct CancelReason {
    pub user_message: String,
    pub log_message: String,
    pub timestamp: f64,
}

/// `Multi_threaded_call.interrupt_result`
pub enum InterruptResult {
    Cancel(CancelReason),
    Continue,
}

/// `'env interrupt_handler`
pub type InterruptHandler<'a, E> = Box<dyn FnMut(E) -> (E, InterruptResult) + 'a>;

/// `'env interrupt_config` (the handlers do not depend on the environment
/// at any caller: a list).
pub struct InterruptConfig<'a, E> {
    pub env: E,
    pub handlers: Vec<(RawFd, InterruptHandler<'a, E>)>,
}

/// `no_interrupt env`
pub fn no_interrupt<'a, E>(env: E) -> InterruptConfig<'a, E> {
    InterruptConfig { env, handlers: vec![] }
}

/// `exception Coalesced_failures of Worker_controller.worker_failure list`:
/// a panic payload.
#[derive(Clone, Debug)]
pub struct CoalescedFailures(pub Vec<worker_controller::WorkerFailed>);

impl std::fmt::Display for CoalescedFailures {
    /// `coalesced_failures_to_string`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let failures: Vec<String> = self.0.iter().map(|w| worker_controller::failure_to_string(&w.failure)).collect();
        write!(f, "Coalesced_failures[{}]", failures.join(", "))
    }
}

static CALL_ID: Mutex<usize> = Mutex::new(0);

/// `multi_threaded_call workers job merge neutral next ?on_cancelled
/// interrupt`: the accumulator and environment, and if cancelled, the
/// unfinished inputs with the reason.
#[allow(clippy::type_complexity)]
pub fn call_with_interrupt<I, O, A, E>(
    workers: &mut [Worker],
    job: &str,
    mut merge: impl FnMut(isize, O, A) -> A,
    neutral: A,
    mut next: impl FnMut() -> Bucket<I>,
    on_cancelled: Option<&mut dyn FnMut() -> Vec<I>>,
    interrupt: InterruptConfig<'_, E>,
) -> ((A, E), Option<(Vec<I>, CancelReason)>)
where
    I: serde::Serialize,
    O: serde::de::DeserializeOwned,
{
    let call_id = {
        let mut id = CALL_ID.lock().unwrap();
        *id += 1;
        *id
    };
    let InterruptConfig { mut env, mut handlers } = interrupt;
    let mut acc = neutral;
    let mut idle: Vec<usize> = (0..workers.len()).rev().collect();
    let mut handles: Vec<Handle<I>> = vec![];
    let mut no_more_jobs = false;
    let mut failures: Vec<worker_controller::WorkerFailed> = vec![];
    loop {
        // `dispatch`
        while !no_more_jobs && !idle.is_empty() {
            match next() {
                Bucket::Wait => break,
                Bucket::Done => {
                    no_more_jobs = true;
                }
                Bucket::Job(bucket) => {
                    let w = idle.pop().unwrap();
                    handles.push(worker_controller::call(workers, w, call_id, job, bucket));
                }
            }
        }
        if handles.is_empty() {
            if no_more_jobs || idle.is_empty() {
                break;
            }
            // (`Wait` with nothing in progress: ask again.)
            continue;
        }
        // `collect`
        let fds: Vec<RawFd> = handlers.iter().map(|(fd, _)| *fd).collect();
        let (readys, waiters, ready_fds) = worker_controller::select(std::mem::take(&mut handles), &fds);
        handles = waiters;
        // The results are read, the workers that gave them get their next
        // bucket, and then the results are decoded and merged. (The OCaml
        // merges each result before it hands out the next bucket; the order
        // of the merges is the same, and a worker does not wait for the
        // master's merge: about 5% of the typing phase at Slack's scale.)
        let mut results = vec![];
        for h in readys {
            let worker_id = workers[h.worker].worker_id();
            idle.push(h.worker);
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                worker_controller::get_result_bytes::<I>(workers, &h)
            })) {
                Ok(Ok(bytes)) => results.push((worker_id, bytes)),
                Ok(Err(failed)) => failures.push(failed),
                Err(panic) => std::panic::resume_unwind(panic),
            }
        }
        if !failures.is_empty() {
            std::panic::panic_any(CoalescedFailures(failures))
        }
        while !no_more_jobs && !idle.is_empty() {
            match next() {
                Bucket::Wait => break,
                Bucket::Done => {
                    no_more_jobs = true;
                }
                Bucket::Job(bucket) => {
                    let w = idle.pop().unwrap();
                    handles.push(worker_controller::call(workers, w, call_id, job, bucket));
                }
            }
        }
        for (worker_id, bytes) in results {
            match crate::worker::decode::<O>(&bytes) {
                Ok(res) => acc = merge(worker_id, res, acc),
                Err(e) => panic!("Worker_controller.get_result: {}", e),
            }
        }
        // `check_cancel`
        let mut decision = InterruptResult::Continue;
        for (fd, handler) in handlers.iter_mut() {
            if !ready_fds.contains(fd) {
                continue;
            }
            let (env_, d) = handler(env);
            env = env_;
            if let InterruptResult::Cancel(_) = d {
                decision = d;
                break;
            }
        }
        if let InterruptResult::Cancel(reason) = decision {
            if let Err(failed) = worker_controller::cancel(workers, &handles) {
                std::panic::panic_any(CoalescedFailures(vec![failed]))
            }
            let unfinished = match on_cancelled {
                Some(f) => f(),
                None => {
                    let mut unfinished: Vec<I> = handles.into_iter().map(|h| h.input).collect();
                    // `add_pending`
                    loop {
                        match next() {
                            Bucket::Done => break,
                            Bucket::Job(a) => unfinished.push(a),
                            Bucket::Wait => panic!("cancelling jobs with Wait not supported"),
                        }
                    }
                    unfinished
                }
            };
            return ((acc, env), Some((unfinished, reason)));
        }
    }
    ((acc, env), None)
}

/// `Multi_worker.call workers ~job ~merge ~neutral ~next`
pub fn call<I, O, A>(
    workers: &mut [Worker],
    job: &str,
    merge: impl FnMut(isize, O, A) -> A,
    neutral: A,
    next: impl FnMut() -> Bucket<I>,
) -> A
where
    I: serde::Serialize,
    O: serde::de::DeserializeOwned,
{
    let ((acc, ()), _) = call_with_interrupt(workers, job, merge, neutral, next, None, no_interrupt(()));
    acc
}

/// `Multi_worker.next workers xs`: buckets of `xs` (`Bucket.make
/// ~num_workers`).
pub fn next<X: Clone + Send + 'static>(num_workers: usize, max_size: Option<isize>, xs: Vec<X>) -> impl FnMut() -> Bucket<Vec<X>> {
    let mut maker = crate::bucket::make_list(num_workers.max(1) as isize, None, max_size, xs);
    move || {
        let b = maker();
        if b.is_empty() { Bucket::Done } else { Bucket::Job(b) }
    }
}

/// `HH_RUST_WORKERS=1`: the server and the batch check make the OCaml's
/// worker processes (`ServerWorker.make`) and run their `Multi_worker` calls
/// on them. Off by default: the master's threads do that work. The OCaml's
/// workers are processes because its threads could not run in parallel;
/// Rust's can, and on Slack's code the threads use 6-10% less CPU for the
/// batch check (wall: 4% less at 7 workers, 20% less at 14), for more memory
/// (the batch check's peak 3.7-3.8 GB against 1.3-1.5 GB; see
/// `check::start_workers` and `Server_main.setup_server`). For measurements
/// (comparing the two models): not a user option, not documented for users.
pub fn workers_switched_on() -> bool {
    crate::rt::heap_stats::switch("HH_RUST_WORKERS", false)
}

/// The master's workers (`genv.workers`).
static WORKERS: Mutex<Option<Vec<Worker>>> = Mutex::new(None);

/// `Server_main.setup_server`'s `make_workers`: the workers of this process
/// from now on.
pub fn set_workers(workers: Vec<Worker>) {
    *WORKERS.lock().unwrap() = Some(workers);
}

/// Whether this process has workers.
pub fn has_workers() -> bool {
    WORKERS.lock().unwrap().as_ref().is_some_and(|w| !w.is_empty())
}

/// The number of workers of this process.
pub fn num_workers() -> usize {
    WORKERS.lock().unwrap().as_ref().map_or(0, |w| w.len())
}

/// `f` on this process's workers (`None`: it has none). Calls do not nest.
pub fn with_workers<T>(f: impl FnOnce(Option<&mut [Worker]>) -> T) -> T {
    let mut guard = WORKERS.lock().unwrap();
    f(guard.as_mut().map(|w| &mut w[..]))
}

/// The pids of the workers (for the `.pids` file and the tests).
pub fn worker_pids() -> Vec<i32> {
    WORKERS.lock().unwrap().as_ref().map_or(vec![], |w| w.iter().map(|w| w.pid()).collect())
}

// ~~ The jobs of the batch services ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// A job of a service that calls `Multi_worker.call workers ~job ~merge
/// ~neutral ~next:(Multi_worker.next workers items)` (find-refs, lint, the
/// batch requests of the daemon...): the OCaml's `job` closure, which
/// captures the context and the request's parameters, as a function of
/// them. It runs in a worker's clone on the neutral accumulator (each
/// bucket's result is merged in the master, as the OCaml's).
#[cfg(feature = "port")]
pub trait ServiceJob: 'static {
    /// The job's name in `crate::worker_jobs`.
    const NAME: &'static str;
    type Params: serde::Serialize + serde::de::DeserializeOwned + Clone;
    type Item: serde::Serialize + serde::de::DeserializeOwned + Clone + Send + Sync + 'static;
    type Output: serde::Serialize + serde::de::DeserializeOwned;
    /// `job neutral bucket`
    fn run(ctx: &std::sync::Arc<crate::ctx::Ctx>, params: &Self::Params, bucket: Vec<Self::Item>) -> Self::Output;
}

/// The input of a service job.
#[cfg(feature = "port")]
#[derive(serde::Serialize, serde::Deserialize)]
pub struct ServiceInput<P, I> {
    ctx: crate::ctx::WorkerSnapshot,
    params: P,
    /// The index of the bucket (the outputs are merged in the order of the
    /// buckets: one of the orders a run of the OCaml gives, and the order
    /// of the threads' version).
    index: usize,
    bucket: Vec<I>,
}

/// A service job in a clone (`crate::worker_jobs`).
#[cfg(feature = "port")]
pub fn run_service<J: ServiceJob>(input: &[u8]) -> Vec<u8> {
    let ServiceInput { ctx, params, index, bucket }: ServiceInput<J::Params, J::Item> =
        crate::worker::decode(input).expect("Worker: a corrupt job input");
    let ctx = std::sync::Arc::new(crate::ctx::Ctx::of_worker_snapshot(ctx).expect("the worker's context"));
    crate::server_type_check::install_ctx(&ctx);
    crate::worker::encode(&(index, J::run(&ctx, &params, bucket)))
}

/// [`call_service`] with the buckets given (`Hh_bucket.of_list` of the
/// indexer's lists: lint), merged in the order they finish.
#[cfg(feature = "port")]
pub fn call_service_buckets<J: ServiceJob, C>(
    ctx: &crate::ctx::Ctx,
    params: J::Params,
    buckets: Vec<Vec<J::Item>>,
    mut merge: impl FnMut(J::Output, C) -> C,
    neutral: C,
    fallback: impl FnOnce(Vec<Vec<J::Item>>, C) -> C,
) -> C {
    let snapshot = if has_workers() { ctx.worker_snapshot() } else { None };
    let Some(snapshot) = snapshot else {
        return fallback(buckets, neutral);
    };
    let mut buckets = buckets.into_iter().enumerate();
    let next = || match buckets.next() {
        Some((index, bucket)) => Bucket::Job(ServiceInput {
            ctx: snapshot.clone(),
            params: params.clone(),
            index,
            bucket,
        }),
        None => Bucket::Done,
    };
    let mut outputs = with_workers(|workers| {
        call(
            workers.expect("call_service_buckets: no workers"),
            J::NAME,
            |_, out: (usize, J::Output), mut acc: Vec<(usize, J::Output)>| {
                acc.push(out);
                acc
            },
            vec![],
            next,
        )
    });
    outputs.sort_by_key(|(index, _)| *index);
    outputs.into_iter().fold(neutral, |acc, (_, out)| merge(out, acc))
}

/// `Multi_worker.call workers ~job:J ~merge ~neutral ~next:(Multi_worker.next
/// workers items)` on this process's workers, when it has some and `ctx`
/// can be rebuilt in a clone (its stores on the shared heap, no entries);
/// `should_stop` is asked before each bucket is handed out (`next` gives
/// `Done` then). Otherwise `fallback` (the threads, or the calling thread).
#[cfg(feature = "port")]
pub fn call_service<J: ServiceJob, C>(
    ctx: &crate::ctx::Ctx,
    params: J::Params,
    items: &[J::Item],
    mut merge: impl FnMut(J::Output, C) -> C,
    neutral: C,
    should_stop: impl Fn() -> bool,
    fallback: impl FnOnce(C) -> C,
) -> C {
    let snapshot = if has_workers() { ctx.worker_snapshot() } else { None };
    let Some(snapshot) = snapshot else {
        return fallback(neutral);
    };
    let mut buckets = next(num_workers(), None, items.to_vec());
    let mut index = 0;
    let next = || {
        if should_stop() {
            return Bucket::Done;
        }
        match buckets() {
            Bucket::Job(bucket) => {
                index += 1;
                Bucket::Job(ServiceInput {
                    ctx: snapshot.clone(),
                    params: params.clone(),
                    index: index - 1,
                    bucket,
                })
            }
            Bucket::Wait => Bucket::Wait,
            Bucket::Done => Bucket::Done,
        }
    };
    let mut outputs = with_workers(|workers| {
        call(
            workers.expect("call_service: no workers"),
            J::NAME,
            |_, out: (usize, J::Output), mut acc: Vec<(usize, J::Output)>| {
                acc.push(out);
                acc
            },
            vec![],
            next,
        )
    });
    outputs.sort_by_key(|(index, _)| *index);
    outputs.into_iter().fold(neutral, |acc, (_, out)| merge(out, acc))
}

