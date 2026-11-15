// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_check_service.ml` (`process_file`,
//! `process_workitems`, `go`, `go_with_interrupt`, `TestMocking`; no distc,
//! decl prefetching (`Declare` workitems), map-reduce or memory caps). See
//! `hh/PORTING.md`.
//!
//! The files are checked on threads, as follows: the OCaml's workers are
//! processes because its threads could not run in parallel; Rust's can (on
//! Slack's code 6-10% less CPU than worker processes, for more memory: see
//! `multi_worker::workers_switched_on`). With `HH_RUST_WORKERS=1` the files
//! are checked as the OCaml checks them, in buckets on worker processes'
//! clones (`check_paths_on_workers`).
//!
//! # How the OCaml maps onto threads
//!
//! The OCaml master splits the files into buckets that forked workers check
//! (`process_workitems`: push the AST and file heaps, check each file, flush
//! the worker's dependency edges, pop the heaps) and merges what each bucket
//! gives (`Merge.merge`: progress, streamed errors, edges registered). Here
//! the threads of rayon's global pool take the files a few at a time, in
//! order ([`check_paths`]); each thread does what an OCaml worker does around
//! a batch once around its whole share (heaps pushed and popped, edges
//! flushed with `Typing_deps.flush_ideps_batch`), and the calling thread
//! merges the edges and registers them (`Typing_deps.register_discovered_dep_edges`)
//! before returning, as `go_with_interrupt` does. Only what is observable
//! is the OCaml's: the diagnostics, the edges, the progress messages, the
//! files left unchecked by a cancellation and its reason.
//!
//! The batch checker (`check.rs`: `hh check`, `hh_server --check`) uses the
//! same loop ([`check_paths`]) with the options of check mode: fixmed
//! diagnostics dropped, no edges recorded unless `--save-64bit` asks for them
//! (`typing_deps::TRACE`, see `check::check_root`), and a panic while
//! checking a file reported as an internal error of that file (`Typing[4001]`;
//! the OCaml's worker would fail).
//!
//! # Deviations
//!
//! - The diagnostics of [`go`] are merged as if one worker had checked every
//!   file, in order, in one bucket (as `server_main::full_init_diagnostics`
//!   does): the OCaml's order of the diagnostics of a file reported while
//!   checking several *other* files depends on how the files were spread over
//!   the workers, which threads cannot reproduce.
//! - A cancellation abandons the files being checked at their next
//!   read of a declaration or method (see "Cancelling a file in progress"
//!   below) and returns them as
//!   unfinished, with the files not started; the files a thread finished
//!   before count as checked. The OCaml returns its in-progress buckets
//!   (several files each) as unfinished. Either way a file is in exactly one
//!   of the two.
//! - `Typechecker_options.num_local_workers` does not limit the threads (the
//!   pool is built once per process).

use std::os::fd::RawFd;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::Instant;

use file_provider::FileProvider;

use crate::ctx::Ctx;
use crate::diagnostics;
use crate::relative_path::RelativePath;
use crate::typing_deps;

type Diag = crate::diagnostics::T;

/// `Server_env.type_check_testing_hooks`.
#[cfg(feature = "server")]
pub use crate::server_env::TypeCheckTestingHooks;

/// Without the server there is no `Server_env`, and no hooks: a type
/// without values.
#[cfg(not(feature = "server"))]
pub enum TypeCheckTestingHooks {}

/// `invoke_testing_hook_after_file_check hooks ~deferred_workitems file`.
/// (A deferred check queues declaration work and a retry of this file, so it
/// has not completed and must not invoke the completion hook: there are no
/// `Declare` workitems here, so a check is never deferred.)
fn invoke_testing_hook_after_file_check(
    hooks: Option<&TypeCheckTestingHooks>,
    file: &RelativePath,
) {
    #[cfg(feature = "server")]
    if let Some(hooks) = hooks {
        (hooks.after_file_check)(file)
    }
    #[cfg(not(feature = "server"))]
    if let Some(hooks) = hooks {
        match *hooks {}
    }
    let _ = file;
}

/// `invoke_testing_hook_before_file_checks hooks ~workers ~hh_distc_config
/// files`. (`workers`: the worker processes of `HH_RUST_WORKERS=1`; there
/// is no distc.)
fn invoke_testing_hook_before_file_checks(
    hooks: Option<&TypeCheckTestingHooks>,
    files: &[RelativePath],
) {
    #[cfg(feature = "server")]
    let has_workers = crate::multi_worker::has_workers();
    #[cfg(not(feature = "server"))]
    let has_workers = false;
    if hooks.is_some() && has_workers {
        panic!("Typechecking test hooks require workers=None and hh_distc_config=None");
    }
    #[cfg(feature = "server")]
    if let Some(hooks) = hooks {
        (hooks.before_file_checks)(files)
    }
    #[cfg(not(feature = "server"))]
    if let Some(hooks) = hooks {
        match *hooks {}
    }
    let _ = files;
}

/// The options of a check (`Typing_service_types.check_info` of the OCaml,
/// with what the daemon and the batch check differ by).
#[derive(Clone, Debug, Default)]
pub struct CheckInfo {
    /// Keep the diagnostics that an `HH_FIXME` suppresses, flagged (the
    /// OCaml's `~drop_fixmed:false`: the daemon); the batch check drops them.
    pub keep_fixmed: bool,
    pub check_reason: String,
    pub discard_warnings: bool,
    /// `log_errors`: log the first errors of each batch and stream them to
    /// the errors file (`Server_progress.ErrorsWrite.report`).
    pub log_errors: bool,
}

/// `result` (no `time_first_error`: the check does not time its first
/// error).
pub struct Result {
    pub diagnostics: Diag,
    pub warnings_saved_state: Option<WarningsSavedState>,
    pub telemetry: crate::telemetry::T,
}

/// `'a job_result`: the files which have not been processed fully or at all
/// due to interrupts, and why.
pub type JobResult<A> = (A, Option<(Vec<RelativePath>, CancelReason)>);

/// `(user_message, log_message)` of `Multi_threaded_call.cancel_reason`.
pub type CancelReason = (String /* user_message */, String /* log_message */);

/// `Multi_threaded_call.interrupt_result`
pub enum InterruptResult {
    Continue,
    Cancel {
        /// Followed by "\nPlease re-run hh", printed by `ClientCheckStatus`.
        user_message: String,
        /// Only for the logs.
        log_message: String,
        /// Only for the logs.
        timestamp: f64,
    },
}

/// `'env Multi_threaded_call.interrupt_handler`
pub type InterruptHandler<'a, E> = Box<dyn FnMut(E) -> (E, InterruptResult) + 'a>;

/// `'env Multi_threaded_call.interrupt_config`. The OCaml's `handlers` is a
/// function of the environment, called again after each handler runs; every
/// caller of the OCaml (`Server_main.setup_interrupts`) ignores the
/// environment, so the handlers are a list here.
pub struct InterruptConfig<'a, E> {
    pub env: E,
    pub handlers: Vec<(RawFd, InterruptHandler<'a, E>)>,
}

/// `Multi_threaded_call.no_interrupt env`
pub fn no_interrupt<'a, E>(env: E) -> InterruptConfig<'a, E> {
    InterruptConfig {
        env,
        handlers: vec![],
    }
}

/// The payload of the panic that [`go_with_interrupt`] raises on the calling
/// thread when checking a file panicked: the OCaml's worker dies ("Exception
/// on file ...", `process_file`), and `Multi_threaded_call` raises
/// `Coalesced_failures`, which ends the server (`Server_utils.exit_on_exception`:
/// `Worker_failed`).
#[derive(Debug, Clone)]
pub struct CoalescedFailures {
    pub path: RelativePath,
    pub message: String,
}

/// `Typing[4001]`, the code of internal errors.
const INTERNAL_ERROR: isize = 4001;

/// `process_file ctx file` (without decl prefetching): the diagnostics of the
/// file, those an `HH_FIXME` suppresses kept (flagged) when `keep_fixmed`
/// (the OCaml's `~drop_fixmed:false`), dropped otherwise (what
/// `Diagnostics.get_diagnostic_list` would do with them).
pub fn process_file(ctx: &Arc<Ctx>, path: &RelativePath, keep_fixmed: bool) -> Diag {
    let fn_ = path;
    let (file_errors, ast) = crate::ast_provider::get_ast_with_error(true, ctx, fn_);
    let errors = if diagnostics::has_errors(None, &file_errors) {
        file_errors
    } else {
        // (`Provider_context.map_tcopt ctx ~f:(fun _ -> opts)` is the
        // identity.)
        crate::typing_check_job::calc_errors(ctx, Some(false), fn_, ast)
    };
    if keep_fixmed {
        errors
    } else {
        diagnostics::drop_fixmed_errors_in_files(errors)
    }
}

/// What a panic while checking one file does.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum OnPanic {
    /// The file gets an internal error (`hh check`, `hh_server --check`).
    InternalError,
    /// "Exception on file ..." on stderr, no file is started any more, and
    /// [`CoalescedFailures`] is raised on the calling thread (the daemon).
    WorkerFailed,
}

/// What checking one file gave.
pub(crate) struct FileOutcome {
    pub diagnostics: Diag,
    /// The size of the file.
    pub bytes: usize,
}

/// What [`check_paths`] gives.
pub(crate) struct CheckedPaths {
    /// The outcome of each file, in the order of the paths; `None` for the
    /// files a cancellation left unchecked.
    pub outcomes: Vec<Option<FileOutcome>>,
    /// The edges the threads flushed (`None` in `SaveToDiskMode`, where they
    /// went to disk), merged; not registered yet.
    pub dep_edges: typing_deps::DepEdges,
}

/// What the threads do while they check, besides checking.
struct Shared<'p> {
    paths: &'p [pos::RelativePath],
    keep_fixmed: bool,
    on_panic: OnPanic,
    /// Set to stop starting files (a cancellation, or a failed file).
    stop: AtomicBool,
    /// The first failure ([`OnPanic::WorkerFailed`]).
    failure: Mutex<Option<CoalescedFailures>>,
    /// How many files are done.
    done: AtomicUsize,
    /// The files done, by index, as they finish, with a copy of their
    /// diagnostics when `stream_diagnostics` (for the calling thread to
    /// report progress and stream errors; only when it asks).
    finished: Option<crossbeam_channel::Sender<Finished>>,
    stream_diagnostics: bool,
    /// The write end of a pipe written after each message on `finished`,
    /// so that the calling thread can wait on it and on other file
    /// descriptors at once.
    wake: Option<RawFd>,
    /// `type_check_testing_hooks` of `process_one_workitem`.
    type_check_testing_hooks: Option<&'p TypeCheckTestingHooks>,
}

/// What the pool tells the calling thread: a file finished (its index, and
/// a copy of its diagnostics when they are streamed), or (`None`) the pool
/// is done.
pub(crate) type Finished = Option<(usize, Option<Diag>)>;

impl Shared<'_> {
    fn tell(&self, message: Finished) {
        if let Some(finished) = &self.finished {
            let _ = finished.send(message);
            if let Some(fd) = self.wake {
                // (Non-blocking: when the pipe is full, it is readable
                // already.)
                unsafe { libc::write(fd, b"x".as_ptr().cast(), 1) };
            }
        }
    }
}

/// What the calling thread does while the pool checks (see [`check_paths`]):
/// it is given a function that stops the pool from starting files, the
/// messages of the pool (the files finished, as they finish, then the end),
/// and a file descriptor that is readable whenever a message was sent (read
/// it empty with [`drain_fd`]).
pub(crate) type During<'d> =
    &'d mut dyn FnMut(&dyn Fn(), &crossbeam_channel::Receiver<Finished>, RawFd);

/// Reads a non-blocking file descriptor until it has nothing more.
fn drain_fd(fd: RawFd) {
    let mut buf = [0u8; 256];
    while unsafe { libc::read(fd, buf.as_mut_ptr().cast(), buf.len()) } > 0 {}
}

/// A pipe whose two ends are non-blocking and closed on drop.
struct WakePipe {
    read: RawFd,
    write: RawFd,
}

impl WakePipe {
    fn new() -> Self {
        let mut fds = [0; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0, "pipe");
        for fd in fds {
            unsafe {
                let flags = libc::fcntl(fd, libc::F_GETFL);
                libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK);
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
        }
        WakePipe {
            read: fds[0],
            write: fds[1],
        }
    }
}

impl Drop for WakePipe {
    fn drop(&mut self) {
        unsafe {
            libc::close(self.read);
            libc::close(self.write);
        }
    }
}

// ~~ Cancelling a file in progress ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// An OCaml cancellation reaches a file in progress: `WorkerController.cancel`
// sets the "should exit" flag of the shared memory (`Worker_cancel.stop_workers`),
// each worker raises `Worker_should_exit` at its next shared-memory access
// (here: a read of a decl store of the `Ctx`, `decl_provider::store_result`)
// or `Worker_cancel.raise_if_stop_requested` (the typing of a method), its
// bucket comes back as unfinished, and the flag is reset (`resume_workers`)
// once every worker has stopped. So does a cancel here, for the threads of
// the call (a `worker_cancel::Workers` group): the thread unwinds with
// `WorkerShouldExit`, the file is left unfinished and the thread cleaned as
// after a panic. In `hh check` and `hh_server --check` nothing stops a group,
// and the check is one relaxed load.

/// The loop of the typing service: [`process_file`] on every path, on the
/// threads of rayon's global pool, which take the files a few at a time in
/// order; a thread of its own reads the files a little ahead (see
/// `ReadAhead`). Each thread pushes the AST and file heaps before its share
/// and pops them after, and flushes the dependency edges it recorded
/// (`process_workitems`). `during`, if any, runs on the calling thread while
/// the pool works, until the pool is done (without it the calling thread
/// just waits); the files finished are sent to it, with a copy of their
/// diagnostics if `stream_diagnostics`.
pub(crate) fn check_paths(
    ctx: &Arc<Ctx>,
    paths: &[pos::RelativePath],
    keep_fixmed: bool,
    on_panic: OnPanic,
    during: Option<During<'_>>,
    stream_diagnostics: bool,
) -> CheckedPaths {
    check_paths_with_testing_hooks(
        ctx,
        paths,
        keep_fixmed,
        on_panic,
        during,
        stream_diagnostics,
        None,
    )
}

/// [`check_paths`], with the `type_check_testing_hooks` of
/// [`go_with_interrupt`]: `after_file_check` is called after each file is
/// checked. The OCaml allows hooks only without workers, where the master
/// checks the files one after the other in their order; so do the threads
/// here when there are hooks: the pool is then one thread of its own.
fn check_paths_with_testing_hooks(
    ctx: &Arc<Ctx>,
    paths: &[pos::RelativePath],
    keep_fixmed: bool,
    on_panic: OnPanic,
    during: Option<During<'_>>,
    stream_diagnostics: bool,
    type_check_testing_hooks: Option<&TypeCheckTestingHooks>,
) -> CheckedPaths {
    #[cfg(feature = "server")]
    if crate::multi_worker::has_workers() {
        if let Some(snapshot) = ctx.worker_snapshot() {
            return check_paths_on_workers(snapshot, paths, keep_fixmed, on_panic, during, stream_diagnostics);
        }
    }
    check_paths_on_threads(
        ctx,
        paths,
        keep_fixmed,
        on_panic,
        during,
        stream_diagnostics,
        type_check_testing_hooks,
    )
}

// ~~ The workers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// `process_in_parallel`: the master hands buckets of files (`next`: at most
// `Bucket.calculate_bucket_size ~num_jobs:to_process_count ~num_workers` of
// the files still to process, in order) to the workers' clones, which run
// `process_workitems` on the master's stores (the shared heap) and send back
// the diagnostics of each file and the edges they discovered; `Merge.merge`
// takes each result as it comes. The calling thread of [`check_paths`] gets
// the files finished as before (`During`), from a thread of the master that
// runs `Multi_worker.call_with_interrupt`; its `stop` is the interrupt that
// cancels the workers (`Worker_controller.cancel`: the files of the buckets
// in progress come back unfinished).

/// The input of a job of `process_workitems` (the OCaml's closure captures
/// the context; the workitems are the bucket).
#[cfg(feature = "server")]
#[derive(serde::Serialize, serde::Deserialize)]
pub struct WorkitemsInput {
    pub ctx: crate::ctx::WorkerSnapshot,
    /// The files, with their index in the paths of the call.
    pub paths: Vec<(usize, RelativePath)>,
    pub keep_fixmed: bool,
    /// [`OnPanic::InternalError`] (else `WorkerFailed`).
    pub internal_error_on_panic: bool,
}

/// The output of a job of `process_workitems` (`typing_result`).
#[cfg(feature = "server")]
#[derive(serde::Serialize, serde::Deserialize)]
pub struct WorkitemsOutput {
    /// The diagnostics and size of each file checked, with its index.
    pub outcomes: Vec<(usize, Diag, usize)>,
    pub dep_edges: Option<Vec<(i64, i64)>>,
    /// The file whose check failed ([`OnPanic::WorkerFailed`]) and why.
    pub failure: Option<(RelativePath, String)>,
}

/// `process_workitems` in a worker's clone: the files of the bucket, on the
/// master's stores, with the AST and file heaps pushed around them and the
/// discovered edges flushed at the end.
#[cfg(feature = "server")]
pub fn process_workitems_job(input: WorkitemsInput) -> WorkitemsOutput {
    let WorkitemsInput {
        ctx,
        paths,
        keep_fixmed,
        internal_error_on_panic,
    } = input;
    let t_setup = std::time::Instant::now();
    let ctx = Arc::new(Ctx::of_worker_snapshot(ctx).expect("process_workitems: the worker's context"));
    crate::server_type_check::install_ctx(&ctx);
    crate::worker::JOB_SETUP_NANOS.store(t_setup.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
    let records_edges = !typing_deps::add_idep_is_noop(&ctx.deps_mode);
    // (`Typing_deps.worker_id` also names the fine-grained dependency
    // database of `Typing_pessimisation_deps`.)
    if records_edges || ctx.tco.tco_record_fine_grained_dependencies {
        typing_deps::WORKER_ID.set(Some(crate::worker_jobs::worker_id()));
    }
    // `if not longlived_workers then Shared_mem.invalidate_local_caches ()`:
    // a clone starts with empty caches.
    crate::file_provider::local_changes_push_sharedmem_stack();
    crate::ast_provider::local_changes_push_sharedmem_stack();
    let on_panic = if internal_error_on_panic {
        OnPanic::InternalError
    } else {
        OnPanic::WorkerFailed
    };
    let mut outcomes = vec![];
    let mut failure = None;
    for (index, fn_) in paths {
        crate::worker_cancel::raise_if_stop_requested();
        match check_file_in_clone(&ctx, &fn_, keep_fixmed, on_panic) {
            Ok((diagnostics, bytes)) => outcomes.push((index, diagnostics, bytes)),
            Err(message) => {
                eprintln!("Exception on file {}", crate::relative_path::s::to_string(&fn_));
                failure = Some((fn_, message));
                break;
            }
        }
    }
    let dep_edges = if records_edges {
        typing_deps::dep_edges_to_raw(&typing_deps::flush_ideps_batch(&ctx.deps_mode))
    } else {
        typing_deps::dep_edges_to_raw(&typing_deps::dep_edges_make())
    };
    // `Typing_pessimisation_deps.finalize` whenever fine-grained dependencies
    // are recorded, whether or not `add_idep` records coarse edges
    // (typing_check_service.ml:673-677).
    if ctx.tco.tco_record_fine_grained_dependencies {
        crate::typing_pessimisation_deps::finalize(&ctx.deps_mode);
    }
    crate::ast_provider::local_changes_pop_sharedmem_stack();
    crate::file_provider::local_changes_pop_sharedmem_stack();
    WorkitemsOutput {
        outcomes,
        dep_edges,
        failure,
    }
}

/// [`process_file`] on one file of a clone, with what [`check_one`] adds
/// around it (the retry when a snapshot was missed, what a panic does);
/// `Err`: the check failed and the job ends ([`OnPanic::WorkerFailed`]). A
/// cancellation unwinds (`Worker_should_exit`: the whole bucket comes back
/// unfinished, as in the OCaml).
#[cfg(feature = "server")]
fn check_file_in_clone(
    ctx: &Arc<Ctx>,
    fn_: &RelativePath,
    keep_fixmed: bool,
    on_panic: OnPanic,
) -> std::result::Result<(Diag, usize), String> {
    let path = pos::RelativePath::from(fn_);
    let bytes = ctx.files.len(path).unwrap_or(0);
    let check = || {
        crate::typing::expr::snapshots::reset_fake_exceptions();
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| process_file(ctx, fn_, keep_fixmed)))
    };
    let (checked, missed) = crate::typing::expr::snapshots::check_without_snapshots(check);
    if let Err(panic) = &checked {
        if panic.is::<crate::worker_cancel::WorkerShouldExit>() {
            std::panic::panic_any(crate::worker_cancel::WorkerShouldExit)
        }
    }
    let checked = if missed {
        crate::rt::decl_epoch::after_panic();
        crate::typing_phase::forget_locl_cache();
        check()
    } else {
        checked
    };
    match checked {
        Ok(diagnostics) => Ok((diagnostics, bytes)),
        Err(panic) => {
            if panic.is::<crate::worker_cancel::WorkerShouldExit>() {
                std::panic::panic_any(crate::worker_cancel::WorkerShouldExit)
            }
            crate::rt::decl_epoch::after_panic();
            let what = crate::worker::panic_message(&panic);
            match on_panic {
                OnPanic::InternalError => {
                    let pos = oxidized::pos::Pos::from_lnum_bol_offset(Arc::new(fn_.clone()), (1, 0, 0), (1, 0, 0));
                    Ok((
                        Diag::from([(
                            fn_.clone(),
                            vec![crate::diagnostics_helpers::error(
                                INTERNAL_ERROR,
                                pos,
                                format!("Internal error: the typechecker panicked: {}", what),
                            )],
                        )]),
                        bytes,
                    ))
                }
                OnPanic::WorkerFailed => Err(what),
            }
        }
    }
}

/// [`check_paths`] over the workers (see above).
#[cfg(feature = "server")]
fn check_paths_on_workers(
    snapshot: crate::ctx::WorkerSnapshot,
    paths: &[pos::RelativePath],
    keep_fixmed: bool,
    on_panic: OnPanic,
    during: Option<During<'_>>,
    stream_diagnostics: bool,
) -> CheckedPaths {
    use crate::multi_worker;
    let (sender, receiver) = crossbeam_channel::unbounded::<Finished>();
    let wake = WakePipe::new();
    let stop_pipe = WakePipe::new();
    let total = paths.len();
    let fnl: Vec<RelativePath> = paths.iter().map(|p| RelativePath::from(*p)).collect();
    // `HH_PHASE_MARKERS=1`: say when the check phase starts (for profiling).
    if std::env::var_os("HH_PHASE_MARKERS").is_some() {
        eprintln!("phase: check");
    }
    let tell = |message: Finished| {
        let _ = sender.send(message);
        unsafe { libc::write(wake.write, b"x".as_ptr().cast(), 1) };
    };
    let dispatch = || -> (Vec<Option<FileOutcome>>, typing_deps::DepEdges, Option<CoalescedFailures>) {
        let mut outcomes: Vec<Option<FileOutcome>> = Vec::with_capacity(total);
        outcomes.resize_with(total, || None);
        let mut next_index = 0usize;
        let num_workers = multi_worker::num_workers().max(1);
        // `Todo.consume`
        let next = || {
            if next_index >= total {
                return multi_worker::Bucket::Done;
            }
            let remaining = total - next_index;
            let size = bucket_size(remaining, num_workers).min(remaining);
            let bucket: Vec<(usize, RelativePath)> =
                (next_index..next_index + size).map(|i| (i, fnl[i].clone())).collect();
            next_index += size;
            multi_worker::Bucket::Job(WorkitemsInput {
                ctx: snapshot.clone(),
                paths: bucket,
                keep_fixmed,
                internal_error_on_panic: on_panic == OnPanic::InternalError,
            })
        };
        let mut failure: Option<CoalescedFailures> = None;
        let merge = |_worker_id: isize, out: WorkitemsOutput, (mut edges, ()): (typing_deps::DepEdges, ())| {
            for (index, diagnostics, bytes) in out.outcomes {
                let copy = stream_diagnostics.then(|| diagnostics.clone());
                outcomes[index] = Some(FileOutcome { diagnostics, bytes });
                tell(Some((index, copy)));
            }
            edges = typing_deps::merge_dep_edges(edges, typing_deps::dep_edges_of_raw(out.dep_edges));
            if let Some((path, message)) = out.failure {
                if failure.is_none() {
                    failure = Some(CoalescedFailures { path, message });
                }
                // (No file is started any more: see the interrupt below.)
                unsafe { libc::write(stop_pipe.write, b"x".as_ptr().cast(), 1) };
            }
            (edges, ())
        };
        let handlers: Vec<(RawFd, multi_worker::InterruptHandler<'_, ()>)> = vec![(
            stop_pipe.read,
            Box::new(|()| {
                (
                    (),
                    multi_worker::InterruptResult::Cancel(multi_worker::CancelReason {
                        user_message: String::new(),
                        log_message: String::new(),
                        timestamp: 0.0,
                    }),
                )
            }),
        )];
        let ((acc, ()), _cancelled) = multi_worker::with_workers(|workers| {
            multi_worker::call_with_interrupt(
                workers.expect("check_paths_on_workers: no workers"),
                "Typing_check_service.process_workitems",
                merge,
                (typing_deps::dep_edges_make(), ()),
                next,
                None,
                multi_worker::InterruptConfig { env: (), handlers },
            )
        });
        (outcomes, acc.0, failure)
    };
    let (outcomes, dep_edges, failure) = std::thread::scope(|scope| {
        let handle = scope.spawn(|| {
            let _done = OnDrop(Some(|| tell(None)));
            dispatch()
        });
        if let Some(during) = during {
            let stop = || {
                unsafe { libc::write(stop_pipe.write, b"x".as_ptr().cast(), 1) };
            };
            during(&stop, &receiver, wake.read);
        }
        match handle.join() {
            Ok(r) => r,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    });
    if let Some(failure) = failure {
        std::panic::panic_any(failure)
    }
    CheckedPaths { outcomes, dep_edges }
}

/// [`check_paths`] on the threads of rayon's global pool (no workers: `hh
/// single` and the unit tests).
fn check_paths_on_threads(
    ctx: &Arc<Ctx>,
    paths: &[pos::RelativePath],
    keep_fixmed: bool,
    on_panic: OnPanic,
    during: Option<During<'_>>,
    stream_diagnostics: bool,
    type_check_testing_hooks: Option<&TypeCheckTestingHooks>,
) -> CheckedPaths {
    let (sender, receiver) = if during.is_some() {
        let (s, r) = crossbeam_channel::unbounded();
        (Some(s), Some(r))
    } else {
        (None, None)
    };
    let wake = during.is_some().then(WakePipe::new);
    let shared = Shared {
        paths,
        keep_fixmed,
        on_panic,
        stop: AtomicBool::new(false),
        failure: Mutex::new(None),
        done: AtomicUsize::new(0),
        finished: sender,
        stream_diagnostics,
        wake: wake.as_ref().map(|pipe| pipe.write),
        type_check_testing_hooks,
    };
    // With hooks, one thread checks the files in their order (see
    // [`check_paths_with_testing_hooks`]).
    let sequential_pool = type_check_testing_hooks.map(|_| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .stack_size(crate::check::STACK_SIZE)
            .build()
            .expect("Typing_check_service: cannot start the thread of the testing hooks")
    });
    // `HH_PHASE_MARKERS=1`: say when the check phase starts (for profiling).
    if std::env::var_os("HH_PHASE_MARKERS").is_some() {
        eprintln!("phase: check");
    }
    // Not in the OCaml, whose `process_workitems` always sets `worker_id` and
    // calls `Typing_deps.flush_ideps_batch`: when `add_idep` records nothing
    // (a batch check without `--save-64bit`), there is no batch to flush and no
    // file to name, so both are skipped. The edges are the same (none).
    // (`Typing_pessimisation_deps.finalize` does not depend on this: it runs
    // whenever `record_fine_grained_dependencies` is on, as in the OCaml.)
    let records_edges = !typing_deps::add_idep_is_noop(&ctx.deps_mode);
    let start = Instant::now();
    // `HH_SLOW_FILE_SECS=N`: report the files that take longer than N seconds.
    let slow_file_secs: Option<f64> = std::env::var("HH_SLOW_FILE_SECS")
        .ok()
        .and_then(|s| s.parse().ok());
    let read_ahead = ReadAhead::new(paths.len());
    // The threads of the pool take the files in order, a few at a time; a
    // thread of its own reads them a little ahead (see `ReadAhead`).
    let next = AtomicUsize::new(0);
    // (A few consecutive files at a time: related files are often next to
    // one another, and the caches of a thread are per thread.)
    const CHUNK: usize = 4;
    // The outcome of each file, with the edges flushed by each thread.
    type Share = (Vec<(usize, FileOutcome)>, typing_deps::DepEdges);
    let workers = crate::worker_cancel::Workers::new();
    let work = || -> Vec<Share> {
        let op = |broadcast: rayon::BroadcastContext<'_>| {
            // `Typing_deps.worker_id`, which names the files of
            // `SaveToDiskMode` (`new-edges-worker-<id>.bin`): the OCaml's
            // workers are numbered from 1.
            // (Also the name of the fine-grained dependency database of
            // `Typing_pessimisation_deps`.)
            if (records_edges || ctx.tco.tco_record_fine_grained_dependencies)
                && typing_deps::WORKER_ID.get().is_none()
            {
                typing_deps::WORKER_ID.set(Some(broadcast.index() as isize + 1));
            }
            crate::file_provider::local_changes_push_sharedmem_stack();
            crate::ast_provider::local_changes_push_sharedmem_stack();
            // This thread is a worker of this call: its master may ask it
            // to stop (see `stop` below).
            let _worker = workers.enter();
            let mut results = vec![];
            'share: loop {
                let first = next.fetch_add(CHUNK, Ordering::Relaxed);
                if first >= paths.len() {
                    break;
                }
                for index in first..paths.len().min(first + CHUNK) {
                    if shared.stop.load(Ordering::Relaxed) {
                        // (The other files of the chunk stay unchecked.)
                        break 'share;
                    }
                    let outcome = check_one(ctx, &shared, &read_ahead, index, slow_file_secs, start);
                    match outcome {
                        Some(outcome) => {
                            invoke_testing_hook_after_file_check(
                                shared.type_check_testing_hooks,
                                &RelativePath::from(shared.paths[index]),
                            );
                            if shared.finished.is_some() {
                                let copy = shared
                                    .stream_diagnostics
                                    .then(|| outcome.diagnostics.clone());
                                shared.tell(Some((index, copy)));
                            }
                            results.push((index, outcome));
                        }
                        None => break 'share,
                    }
                }
            }
            // Update edges
            let dep_edges = if records_edges {
                typing_deps::flush_ideps_batch(&ctx.deps_mode)
            } else {
                typing_deps::dep_edges_make()
            };
            // Fine-grained dependencies are recorded whether or not `add_idep`
            // records coarse edges, so they are persisted whenever the option
            // is on, as in the OCaml.
            if ctx.tco.tco_record_fine_grained_dependencies {
                crate::typing_pessimisation_deps::finalize(&ctx.deps_mode);
            }
            crate::ast_provider::local_changes_pop_sharedmem_stack();
            crate::file_provider::local_changes_pop_sharedmem_stack();
            (results, dep_edges)
        };
        match &sequential_pool {
            None => rayon::broadcast(op),
            Some(pool) => pool.broadcast(op),
        }
    };
    let per_thread: Vec<Share> = std::thread::scope(|scope| {
        scope.spawn(|| read_ahead.run(ctx, paths, &next, &shared.stop));
        let per_thread = match during {
            None => std::panic::catch_unwind(std::panic::AssertUnwindSafe(work)),
            Some(during) => {
                let handle = scope.spawn(|| {
                    // The end is told even when the pool panics.
                    let _done = OnDrop(Some(|| shared.tell(None)));
                    work()
                });
                // `WorkerController.cancel handles`: the workers are asked to
                // stop (`Worker_cancel.stop_workers ()`: the file a worker is
                // in the middle of ends at its next read of a declaration,
                // with `Worker_should_exit`), they are waited for
                // (`wait_for_cancel`: the join), and then may work again
                // (`Worker_cancel.resume_workers ()`).
                let stop = || {
                    shared.stop.store(true, Ordering::Relaxed);
                    workers.stop_workers();
                };
                // (Also if `during` unwinds; nothing to do unless stopped.)
                struct Resume<'a>(&'a crate::worker_cancel::Workers);
                impl Drop for Resume<'_> {
                    fn drop(&mut self) {
                        self.0.resume_workers()
                    }
                }
                let resume = Resume(&workers);
                during(&stop, receiver.as_ref().unwrap(), wake.as_ref().unwrap().read);
                let per_thread = handle.join();
                drop(resume);
                per_thread
            }
        };
        // The reader stops too (it waits for the files to be taken, and
        // after a cancellation or a failure they no longer are).
        shared.stop.store(true, Ordering::Relaxed);
        match per_thread {
            Ok(per_thread) => per_thread,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    });
    if let Some(failure) = shared.failure.into_inner().unwrap() {
        std::panic::panic_any(failure)
    }
    let mut outcomes: Vec<Option<FileOutcome>> = Vec::with_capacity(paths.len());
    outcomes.resize_with(paths.len(), || None);
    let mut dep_edges = typing_deps::dep_edges_make();
    for (results, edges) in per_thread {
        for (index, outcome) in results {
            outcomes[index] = Some(outcome);
        }
        dep_edges = typing_deps::merge_dep_edges(dep_edges, edges);
    }
    CheckedPaths {
        outcomes,
        dep_edges,
    }
}

/// [`process_file`] on the file `index` of the paths, with what the loop
/// adds around it: the decl epoch, the contents read ahead, the retry when
/// a snapshot was missed, and what a panic does (`None`: stop).
fn check_one(
    ctx: &Arc<Ctx>,
    shared: &Shared<'_>,
    read_ahead: &ReadAhead,
    index: usize,
    slow_file_secs: Option<f64>,
    start: Instant,
) -> Option<FileOutcome> {
    let path = shared.paths[index];
    // Not in the OCaml, which reads declarations from shared memory each
    // time: the per-thread memos of what was derived from declarations are
    // valid for one decl epoch; forget them if declarations changed since this
    // thread last checked a file (an OCaml worker starts each job with empty
    // local caches).
    crate::rt::decl_epoch::sync_thread();
    let file_start = Instant::now();
    let _report = OnDrop(Some(|| {
        let n = shared.done.fetch_add(1, Ordering::Relaxed) + 1;
        let secs = file_start.elapsed().as_secs_f64();
        if let Some(limit) = slow_file_secs {
            if secs > limit {
                eprintln!("slow file: {:.2}s {}", secs, path.path().display());
            }
            if n % 10000 == 0 {
                eprintln!("checked {} files in {:.1}s", n, start.elapsed().as_secs_f64());
            }
        }
    }));
    // The contents, if the reader got to the file first: the parser takes
    // them from `ctx.files`, which would read the file again.
    let text = read_ahead.take(index);
    let bytes = match &text {
        Some(text) => text.len(),
        // (The size of the file, without reading it a second time.)
        None => ctx.files.len(path).unwrap_or(0),
    };
    ctx.files.set_read_ahead(text.map(|text| (path, text)));
    let fn_: RelativePath = path.into();
    let check = || {
        crate::typing::expr::snapshots::reset_fake_exceptions();
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            process_file(ctx, &fn_, shared.keep_fixmed)
        }))
    };
    // The expressions keep no copy of the environment for the rare
    // `InconsistentTypeVarState`; if one happens, the file is checked again
    // the OCaml way (see `check_without_snapshots`).
    let (checked, missed) = crate::typing::expr::snapshots::check_without_snapshots(check);
    if let Err(panic) = &checked {
        if panic.is::<crate::worker_cancel::WorkerShouldExit>() {
            // Cancelled (`Worker_should_exit`, see above): unfinished, the
            // thread as clean as after a panic.
            crate::rt::decl_epoch::after_panic();
            crate::typing_phase::forget_locl_cache();
            ctx.files.set_read_ahead(None);
            return None;
        }
    }
    let checked = if missed {
        // (The first check ended in a caught panic.)
        crate::rt::decl_epoch::after_panic();
        crate::typing_phase::forget_locl_cache();
        check()
    } else {
        checked
    };
    ctx.files.set_read_ahead(None);
    let diagnostics = match checked {
        Ok(diagnostics) => diagnostics,
        // `Worker_cancel.Worker_should_exit -> `Worker_cancelled` (`Worker`):
        // the master asked the workers to stop. The file is not checked: it
        // is one of the unfinished ones of the cancellation.
        Err(panic) if panic.is::<crate::worker_cancel::WorkerShouldExit>() => {
            crate::rt::decl_epoch::after_panic();
            crate::typing_phase::forget_locl_cache();
            return None;
        }
        Err(panic) => {
            crate::rt::decl_epoch::after_panic();
            let what = panic
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| panic.downcast_ref::<&str>().copied())
                .unwrap_or("unknown panic")
                .to_string();
            match shared.on_panic {
                OnPanic::InternalError => {
                    let pos = oxidized::pos::Pos::from_lnum_bol_offset(
                        Arc::new(fn_.clone()),
                        (1, 0, 0),
                        (1, 0, 0),
                    );
                    Diag::from([(
                        fn_.clone(),
                        vec![crate::diagnostics_helpers::error(
                            INTERNAL_ERROR,
                            pos,
                            format!("Internal error: the typechecker panicked: {}", what),
                        )],
                    )])
                }
                OnPanic::WorkerFailed => {
                    eprintln!(
                        "Exception on file {}",
                        crate::relative_path::s::to_string(&fn_)
                    );
                    shared.stop.store(true, Ordering::Relaxed);
                    let mut failure = shared.failure.lock().unwrap();
                    if failure.is_none() {
                        *failure = Some(CoalescedFailures {
                            path: fn_.clone(),
                            message: what,
                        });
                    }
                    return None;
                }
            }
        }
    };
    Some(FileOutcome { diagnostics, bytes })
}

/// The files of [`check_paths`], read a little ahead of the threads that
/// check them by one thread of its own. Opening a file can cost as much CPU
/// as parsing a small one (where file accesses are monitored), and the
/// threads of the pool would otherwise open each file a second time (after
/// the declaration phase). A file the reader has not read when its turn
/// comes is read by the thread that checks it.
struct ReadAhead {
    slots: Vec<Mutex<ReadAheadSlot>>,
}

enum ReadAheadSlot {
    Unread,
    Read(bstr::BString),
    Taken,
}

impl ReadAhead {
    /// How many files the reader may read beyond the last one taken.
    const WINDOW: usize = 64;

    fn new(files: usize) -> Self {
        Self {
            slots: (0..files)
                .map(|_| Mutex::new(ReadAheadSlot::Unread))
                .collect(),
        }
    }

    /// Read the files, in order, while the threads that check them take
    /// them in order from `next` (the index of the next file to take), until
    /// `stop`.
    fn run(&self, ctx: &Ctx, paths: &[pos::RelativePath], next: &AtomicUsize, stop: &AtomicBool) {
        'files: for (index, &path) in paths.iter().enumerate() {
            loop {
                if stop.load(Ordering::Relaxed) {
                    return;
                }
                let taken = next.load(Ordering::Relaxed);
                if index < taken {
                    continue 'files;
                }
                if index < taken + Self::WINDOW {
                    break;
                }
                std::thread::sleep(Duration::from_micros(500));
            }
            // (A file that cannot be read is left to the thread that checks
            // it, which reports what it reports.)
            if let Ok(text) = ctx.files.get(path) {
                let mut slot = self.slots[index].lock().unwrap();
                if let ReadAheadSlot::Unread = *slot {
                    *slot = ReadAheadSlot::Read(text);
                }
            }
        }
    }

    /// The contents of the file `index`, if the reader got to it first.
    fn take(&self, index: usize) -> Option<bstr::BString> {
        let mut slot = self.slots[index].lock().unwrap();
        match std::mem::replace(&mut *slot, ReadAheadSlot::Taken) {
            ReadAheadSlot::Read(text) => Some(text),
            ReadAheadSlot::Unread | ReadAheadSlot::Taken => None,
        }
    }
}

/// Runs its function when dropped, even when unwinding.
struct OnDrop<F: FnOnce()>(Option<F>);

impl<F: FnOnce()> Drop for OnDrop<F> {
    fn drop(&mut self) {
        if let Some(f) = self.0.take() {
            f()
        }
    }
}

/// `TestMocking`: the files [`set_is_cancelled`] names are taken out of the
/// next check and returned as unfinished, with the reason "mock cancel"
/// (the OCaml uses it when `Injector_config.use_test_stubbing`; with no file
/// named it is the identity, `NoMocking`).
pub mod test_mocking {
    use std::sync::Mutex;

    use crate::relative_path::RelativePath;

    static CANCELLED: Mutex<std::collections::BTreeSet<RelativePath>> =
        Mutex::new(std::collections::BTreeSet::new());

    pub fn set_is_cancelled(x: RelativePath) {
        CANCELLED.lock().unwrap().insert(x);
    }

    /// Takes the cancelled files out of `fnl`: what is left, and the files
    /// taken out (in the order of `fnl`). Only cancels once.
    pub(super) fn with_test_mocking_partition(fnl: Vec<RelativePath>) -> (Vec<RelativePath>, Vec<RelativePath>) {
        let mut cancelled = CANCELLED.lock().unwrap();
        if cancelled.is_empty() {
            return (fnl, vec![]);
        }
        let (mock_cancelled, fnl) = fnl.into_iter().partition(|path| cancelled.contains(path));
        // Only cancel once to avoid infinite loops
        cancelled.clear();
        (fnl, mock_cancelled)
    }
}

/// `Diagnostics.merge` of the diagnostics of each file onto those of the
/// files before it (one worker's accumulator), then onto the master's empty
/// accumulator (`accumulate_job_output`).
fn merge_in_order(per_file: impl IntoIterator<Item = Diag>) -> Diag {
    diagnostics::merge(merge_job_output(per_file), Diag::new())
}

/// The diagnostics of a job (`produced_by_job.diagnostics`, what
/// `process_errors` logs): `Diagnostics.merge` of the diagnostics of each
/// file onto those of the files before it, from nothing.
pub(crate) fn merge_job_output(per_file: impl IntoIterator<Item = Diag>) -> Diag {
    let mut worker = Diag::new();
    for file_diagnostics in per_file {
        worker = diagnostics::merge(file_diagnostics, worker);
    }
    worker
}

/// The line `Multi_threaded_call.call_with_interrupt` logs as it starts.
pub(crate) fn log_call_with_interrupt(num_workers: usize) {
    crate::hh_logger::log(&format!(
        "Multi_threaded_call.call_with_interrupt called with {} workers",
        num_workers
    ));
}

/// `Merge.process_errors ~log_errors`: the first errors of a batch, logged.
pub(crate) fn process_errors(errors: &Diag) {
    let error_count = diagnostics::count(None, errors);
    if error_count > 0 {
        let max_errors = 5;
        crate::hh_logger::log(&format!(
            "{} errors in batch. Showing first {}:",
            error_count, max_errors
        ));
        for error in diagnostics::get_diagnostic_list(None, errors.clone())
            .iter()
            .take(max_errors)
        {
            let oxidized::message::Message(pos, msg) = &error.claim;
            let (l1, l2, c1, c2) = crate::pos::info_pos_extended(pos);
            crate::hh_logger::log(&format!(
                "{}: {}({}:{}-{}:{}) [{}] {}",
                crate::user_diagnostic::severity::to_all_caps_string(&error.severity),
                crate::relative_path::suffix(pos.filename()),
                l1,
                c1,
                l2,
                c2,
                error.code,
                msg
            ));
        }
    }
}

/// `add_warnings_to_ss mergebase_warning_hashes errors ~discard_warnings`:
/// if `discard_warnings`, adds the hashes of the warnings in `errors` to
/// `mergebase_warning_hashes`.
pub fn add_warnings_to_ss(
    mergebase_warning_hashes: Option<WarningsSavedState>,
    errors: &Diag,
    discard_warnings: bool,
) -> Option<WarningsSavedState> {
    mergebase_warning_hashes.map(|mergebase_warning_hashes| {
        if discard_warnings {
            let warning_hashes = diagnostics::make_warning_saved_state(errors);
            mergebase_warning_hashes.union(&warning_hashes).copied().collect()
        } else {
            mergebase_warning_hashes
        }
    })
}

/// `filter_out_warnings mergebase_warning_hashes errors ~discard_warnings`
pub fn filter_out_warnings(
    mergebase_warning_hashes: Option<WarningsSavedState>,
    errors: Diag,
    discard_warnings: bool,
) -> (Option<WarningsSavedState>, Diag) {
    let mergebase_warning_hashes = add_warnings_to_ss(mergebase_warning_hashes, &errors, discard_warnings);
    let errors = diagnostics::filter_out_mergebase_warnings(mergebase_warning_hashes.as_ref(), errors);
    (mergebase_warning_hashes, errors)
}

/// `Warnings_saved_state.t`
pub type WarningsSavedState = oxidized::warnings_saved_state_impl::WarningsSavedState;

/// `Bucket.calculate_bucket_size ~num_jobs ~num_workers ()`
fn bucket_size(num_jobs: usize, num_workers: usize) -> usize {
    #[cfg(feature = "server")]
    return crate::bucket::calculate_bucket_size(num_jobs as isize, num_workers as isize, None).max(1)
        as usize;
    // (Without the server, `Bucket` is not compiled: the same formula.)
    #[cfg(not(feature = "server"))]
    {
        let max_size = 500;
        if num_jobs < num_workers * max_size {
            1 + num_jobs / num_workers
        } else {
            max_size
        }
    }
}

/// The buckets of the OCaml's typing service, as files finish. Its `next`
/// gives each worker `Bucket.calculate_bucket_size
/// ~num_jobs:to_process_count ~num_workers` of the files still to process
/// (`Todo.consume`), and `Merge.merge` writes the percentage when a bucket
/// comes back. Here the files are not dealt out in buckets (each thread
/// takes the next files), so the sizes the OCaml's buckets would have, in
/// the order it would make them, delimit the progress reports: as many as
/// the OCaml writes, after about as many files.
pub(crate) struct Buckets {
    to_process_count: usize,
    num_workers: usize,
    bucket_size: usize,
    done_in_bucket: usize,
}

impl Buckets {
    pub(crate) fn new(total_count: usize, num_workers: usize) -> Self {
        let mut buckets = Buckets {
            to_process_count: total_count,
            num_workers: num_workers.max(1),
            bucket_size: 0,
            done_in_bucket: 0,
        };
        buckets.bucket_size = buckets.next();
        buckets
    }

    /// `Todo.consume`: the size of the next bucket.
    fn next(&mut self) -> usize {
        let size = bucket_size(self.to_process_count, self.num_workers)
            .min(self.to_process_count.max(1));
        self.to_process_count = self.to_process_count.saturating_sub(size);
        size
    }

    /// One more file is finished: whether that finishes a bucket.
    pub(crate) fn file_done(&mut self) -> bool {
        self.done_in_bucket += 1;
        if self.done_in_bucket >= self.bucket_size {
            self.done_in_bucket = 0;
            self.bucket_size = self.next();
            true
        } else {
            false
        }
    }
}

/// `go_with_interrupt ctx workers telemetry fnl ~root ~interrupt
/// ~longlived_workers ~hh_distc_config ~check_info ~type_check_testing_hooks
/// ~warnings_saved_state`:
/// checks `files` on the pool while the calling thread runs the handlers of
/// `interrupt` whose file descriptors become readable (it waits on them and
/// on the pool at once, as `Multi_threaded_call` selects on the workers and
/// the interrupt fds; without handlers it only waits for the pool). A `Cancel` stops starting
/// files: the files not checked are returned with the reason. The edges the
/// threads recorded are registered before returning.
///
/// The last element returned, a list of paths, are the files which have not
/// been processed fully or at all due to interrupts.
///
/// A panic while checking a file ends the check: "Exception on file ..." on
/// stderr, then [`CoalescedFailures`] is raised (`panic_any`) on the calling
/// thread, as `Multi_threaded_call` raises it when a worker fails.
///
/// `warnings_saved_state` (`env.init_env.mergebase_warning_hashes`, set
/// after a saved-state load): each bucket's diagnostics go through
/// [`filter_out_warnings`] (the warnings of the saved state are not
/// reported), and the updated hashes are in the result. (The merge applies
/// the filter to each bucket as the OCaml's
/// `Merge.process_and_merge_typing_results`; the result is the filter of all
/// the diagnostics with the final hashes, which is the same: with
/// `discard_warnings` every warning is added before it is filtered, without
/// it the hashes do not change.)
///
/// There is no `workers`, `root`, `longlived_workers` or `hh_distc_config`:
/// the files are checked on the threads of rayon's global pool (or, with
/// `HH_RUST_WORKERS=1`, on the worker processes of `multi_worker`), which
/// this function picks itself because a pool of threads cannot be handed
/// around as the OCaml's list of forked workers is; and there is no distc.
pub fn go_with_interrupt<E>(
    ctx: &Arc<Ctx>,
    telemetry: crate::telemetry::T,
    files: &[RelativePath],
    interrupt: InterruptConfig<'_, E>,
    check_info: &CheckInfo,
    type_check_testing_hooks: Option<&TypeCheckTestingHooks>,
    warnings_saved_state: Option<WarningsSavedState>,
) -> JobResult<(E, Result)> {
    invoke_testing_hook_before_file_checks(type_check_testing_hooks, files);
    let sample_rate = ctx.tco.tco_typecheck_sample_rate;
    #[cfg(feature = "server")]
    crate::server_progress::write(
        None,
        None,
        &format!("typechecking {} files", files.len()),
    );
    let fnl: Vec<RelativePath> = if sample_rate >= 1.0 {
        files.to_vec()
    } else {
        let result: Vec<RelativePath> = files
            .iter()
            .filter(|x| crate::find_utils::sample_filter(sample_rate, x))
            .cloned()
            .collect();
        crate::hh_logger::log(&format!(
            "Sampling {} percent of files: {} out of {}",
            crate::rt::ocaml_printf::sprintf_f(6, sample_rate),
            result.len(),
            files.len()
        ));
        result
    };
    // `Mocking.with_test_mocking`
    let (fnl, mock_cancelled) = test_mocking::with_test_mocking_partition(fnl);
    // (No hh_distc: `will_use_distc` is false.)
    #[cfg(feature = "server")]
    if check_info.log_errors {
        crate::server_progress::errors_write::telemetry(&crate::telemetry::bool_(
            "will_use_distc",
            false,
            crate::telemetry::create(),
        ));
        crate::server_progress::errors_write::telemetry(&crate::telemetry::bool_(
            "process_in_parallel",
            true,
            crate::telemetry::create(),
        ));
    }
    let paths: Vec<pos::RelativePath> = fnl.iter().map(pos::RelativePath::from).collect();
    let InterruptConfig { env, mut handlers } = interrupt;
    let mut env_slot = Some(env);
    let mut cancel_reason: Option<CancelReason> = None;
    let mut done_count = 0usize;
    let total_count = paths.len();
    // The files finished since the last progress report: a bucket of the
    // OCaml (see [`Buckets`]).
    let mut buckets = Buckets::new(total_count, rayon::current_num_threads());
    let mut batch: Vec<Diag> = vec![];
    let mut batch_len = 0usize;
    let log_errors = check_info.log_errors;
    let discard_warnings = check_info.discard_warnings;
    let mut stream_warnings_saved_state = warnings_saved_state.clone();
    // `Merge.merge` of a bucket: progress, then `process_errors`.
    let mut merge_batch = |batch: &mut Vec<Diag>, done_count: usize| {
        #[cfg(feature = "server")]
        crate::server_progress::write_percentage(
            "typechecking",
            done_count as isize,
            total_count as isize,
            "files",
            None,
        );
        let _ = done_count;
        if log_errors {
            let errors = merge_job_output(std::mem::take(batch));
            let errors = if stream_warnings_saved_state.is_some() {
                let (ws, errors) =
                    filter_out_warnings(stream_warnings_saved_state.take(), errors, discard_warnings);
                stream_warnings_saved_state = ws;
                errors
            } else {
                errors
            };
            process_errors(&errors);
            // Handle errors paradigm (3) - push updates to errors-file as
            // soon as their batch is finished (`stream_errors` is
            // `check_info.log_errors`).
            #[cfg(feature = "server")]
            crate::server_progress::errors_write::report(&errors);
        }
        batch.clear();
    };
    let fds: Vec<RawFd> = handlers.iter().map(|(fd, _)| *fd).collect();
    // `Multi_threaded_call`: the master waits (`select`) on the workers and
    // on the interrupt fds at once; here on the messages of the pool and,
    // when there are handlers, their fds (without handlers, or after a
    // cancellation, only on the pool).
    let mut during = |stop: &dyn Fn(),
                      finished: &crossbeam_channel::Receiver<Finished>,
                      wake: RawFd| {
        let mut on_message = |message: Finished| -> bool {
            match message {
                Some((_index, diagnostics)) => {
                    batch.extend(diagnostics);
                    batch_len += 1;
                    done_count += 1;
                    if buckets.file_done() {
                        batch_len = 0;
                        merge_batch(&mut batch, done_count);
                    }
                    false
                }
                None => {
                    if batch_len > 0 {
                        batch_len = 0;
                        merge_batch(&mut batch, done_count);
                    }
                    true
                }
            }
        };
        loop {
            if fds.is_empty() || cancel_reason.is_some() {
                match finished.recv() {
                    Ok(message) => {
                        if on_message(message) {
                            break;
                        }
                    }
                    Err(_) => break,
                }
                continue;
            }
            let ready = poll_readable(&fds, wake);
            drain_fd(wake);
            let mut done = false;
            while let Ok(message) = finished.try_recv() {
                done |= on_message(message);
            }
            if done {
                break;
            }
            // `check_cancel`: the handlers whose fd is ready, in order,
            // until one cancels.
            for (fd, handler) in handlers.iter_mut() {
                if !ready.contains(fd) {
                    continue;
                }
                let (new_env, decision) = handler(env_slot.take().unwrap());
                env_slot = Some(new_env);
                if let InterruptResult::Cancel {
                    user_message,
                    log_message,
                    timestamp: _,
                } = decision
                {
                    cancel_reason = Some((user_message, log_message));
                    stop();
                    break;
                }
            }
        }
    };
    log_call_with_interrupt(rayon::current_num_threads());
    let checked = check_paths_with_testing_hooks(
        ctx,
        &paths,
        check_info.keep_fixmed,
        OnPanic::WorkerFailed,
        Some(&mut during),
        log_errors,
        type_check_testing_hooks,
    );
    drop(during);
    let env = env_slot.take().unwrap();
    let CheckedPaths {
        outcomes,
        dep_edges,
    } = checked;
    let mut unfinished: Vec<RelativePath> = vec![];
    let mut per_file = Vec::with_capacity(outcomes.len());
    for (path, outcome) in fnl.iter().zip(outcomes) {
        match outcome {
            Some(outcome) => per_file.push(outcome.diagnostics),
            None => unfinished.push(path.clone()),
        }
    }
    let diagnostics = merge_in_order(per_file);
    let (warnings_saved_state, diagnostics) = if warnings_saved_state.is_some() {
        filter_out_warnings(warnings_saved_state, diagnostics, discard_warnings)
    } else {
        (None, diagnostics)
    };
    typing_deps::register_discovered_dep_edges(&dep_edges);
    let profiling_info = crate::telemetry::create();
    let telemetry = crate::telemetry::object_("profiling_info", profiling_info, telemetry);
    let cancelled_fnl_and_reason = match cancel_reason {
        Some(reason) => Some((unfinished, reason)),
        None => {
            assert!(
                unfinished.is_empty(),
                "Typing_check_service.go_with_interrupt: unfinished files without a cancellation"
            );
            None
        }
    };
    // `Mocking.with_test_mocking`: the files it took out are unfinished.
    let cancelled_fnl_and_reason = match cancelled_fnl_and_reason {
        None if mock_cancelled.is_empty() => None,
        None => Some((
            mock_cancelled,
            ("mock cancel".to_string(), "mock cancel".to_string()),
        )),
        Some((mut cancelled, reason)) => {
            let mut all = mock_cancelled;
            all.append(&mut cancelled);
            Some((all, reason))
        }
    };
    (
        (
            env,
            Result {
                diagnostics,
                warnings_saved_state,
                telemetry,
            },
        ),
        cancelled_fnl_and_reason,
    )
}

/// Waits until one of `fds` or `wake` is readable: those of `fds` that are
/// (all of them are returned at once when several are).
fn poll_readable(fds: &[RawFd], wake: RawFd) -> Vec<RawFd> {
    let mut pollfds: Vec<libc::pollfd> = fds
        .iter()
        .chain(std::iter::once(&wake))
        .map(|&fd| libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        })
        .collect();
    loop {
        let n = unsafe { libc::poll(pollfds.as_mut_ptr(), pollfds.len() as libc::nfds_t, -1) };
        if n > 0 {
            break;
        }
        if n < 0 && std::io::Error::last_os_error().kind() != std::io::ErrorKind::Interrupted {
            return vec![];
        }
        // (Interrupted by a signal: wait again.)
    }
    pollfds[..fds.len()]
        .iter()
        .filter(|p| p.revents & (libc::POLLIN | libc::POLLHUP | libc::POLLERR) != 0)
        .map(|p| p.fd)
        .collect()
}

/// `go ctx workers telemetry fnl ~root ~longlived_workers ~hh_distc_config
/// ~check_info ~warnings_saved_state`: [`go_with_interrupt`] without
/// interrupts.
pub fn go(
    ctx: &Arc<Ctx>,
    telemetry: crate::telemetry::T,
    files: &[RelativePath],
    check_info: &CheckInfo,
    warnings_saved_state: Option<WarningsSavedState>,
) -> Result {
    let interrupt = no_interrupt(());
    let (((), result), unfinished_and_reason) =
        go_with_interrupt(ctx, telemetry, files, interrupt, check_info, None, warnings_saved_state);
    assert!(unfinished_and_reason.is_none());
    result
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use oxidized::typechecker_options::TypecheckerOptions;
    use relative_path::Prefix;

    use super::*;

    /// The progress reports follow the OCaml's buckets: 3,355 files at 7
    /// workers are 480 files, then 1 + remaining/7 each time, down to
    /// buckets of 1 file (43 reports; the OCaml wrote about 40 percentages
    /// for such a check, some buckets coming back together).
    #[test]
    fn progress_reports_follow_the_buckets() {
        let mut buckets = Buckets::new(3355, 7);
        let reports: Vec<usize> = (1..=3355).filter(|_| buckets.file_done()).collect();
        assert_eq!(&reports[..3], &[480, 891, 1244]);
        assert_eq!(reports.last(), Some(&3355));
        assert_eq!(reports.len(), 43);
        // More files than 500 per worker: buckets of 500.
        let mut buckets = Buckets::new(10_000, 2);
        let reports: Vec<usize> = (1..=10_000).filter(|_| buckets.file_done()).collect();
        assert_eq!(&reports[..3], &[500, 1000, 1500]);
        assert_eq!(reports.last(), Some(&10_000));
        // One worker, few files: one bucket.
        let mut buckets = Buckets::new(3, 1);
        assert_eq!((1..=3).filter(|_| buckets.file_done()).count(), 1);
    }

    /// The tests run one at a time: `test_mocking` is global.
    static SERIAL: Mutex<()> = Mutex::new(());

    fn serial() -> std::sync::MutexGuard<'static, ()> {
        SERIAL.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// A context that declares the hhi files and `files` (name, contents),
    /// as `hh single` does; the paths of the files.
    fn ctx_of(files: &[(String, String)]) -> (Arc<Ctx>, Vec<RelativePath>) {
        // (As the OCaml's tests: no progress file.)
        #[cfg(feature = "server")]
        crate::server_progress::disable();
        // (As `check::check_root`.)
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, Path::new("/"));
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Hhi, Path::new("/hhi"));
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Tmp, Path::new("/tmp"));
        let ctx = Ctx::new(Path::new("/"), TypecheckerOptions::default()).unwrap();
        let mut decl_paths = ctx.hhi_paths.clone();
        let mut paths = vec![];
        for (name, contents) in files {
            let path = pos::RelativePath::new(pos::Prefix::Root, name);
            ctx.files.set(path, contents.as_str());
            decl_paths.push(path);
            paths.push(RelativePath::make(Prefix::Root, name.into()));
        }
        crate::check::declare_files(&ctx, &decl_paths, &mut crate::check::Stats::default());
        let ctx = Arc::new(ctx);
        crate::hh_single_type_check::install(&ctx);
        (ctx, paths)
    }

    /// `n` files, each with one error (a function returning a string as an
    /// int).
    fn files_with_an_error(prefix: &str, n: usize) -> Vec<(String, String)> {
        (0..n)
            .map(|i| {
                (
                    format!("{prefix}{i}.php"),
                    format!("<?hh\nfunction {prefix}{i}(): int {{ return 'x'; }}\n"),
                )
            })
            .collect()
    }

    fn files_of(diagnostics: &Diag) -> std::collections::BTreeSet<RelativePath> {
        diagnostics
            .iter()
            .filter(|(_, l)| !l.is_empty())
            .map(|(path, _)| path.clone())
            .collect()
    }

    #[test]
    fn go_checks_every_file() {
        let _serial = serial();
        let (ctx, paths) = ctx_of(&files_with_an_error("go", 20));
        let result = go(&ctx, crate::telemetry::create(), &paths, &CheckInfo::default(), None);
        assert_eq!(files_of(&result.diagnostics), paths.iter().cloned().collect());
        // The same diagnostics as the batch check's.
        let pos_paths: Vec<pos::RelativePath> = paths.iter().map(pos::RelativePath::from).collect();
        let batch = crate::check::check_files_typed_by_file(
            &ctx,
            &pos_paths,
            &mut crate::check::Stats::default(),
            None,
        );
        assert_eq!(merge_in_order(batch), result.diagnostics);
    }

    #[test]
    fn a_cancel_returns_the_files_not_checked() {
        let _serial = serial();
        let n = 400;
        let (ctx, paths) = ctx_of(&files_with_an_error("cancel", n));
        // A file descriptor that is readable at once.
        let mut fds = [0; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
        assert_eq!(unsafe { libc::write(fds[1], b"x".as_ptr().cast(), 1) }, 1);
        let handler: InterruptHandler<'_, usize> = Box::new(|calls| {
            (
                calls + 1,
                InterruptResult::Cancel {
                    user_message: "Files have changed on disk!".to_string(),
                    log_message: "test".to_string(),
                    timestamp: 0.0,
                },
            )
        });
        let interrupt = InterruptConfig {
            env: 0,
            handlers: vec![(fds[0], handler)],
        };
        let ((calls, result), cancelled) =
            go_with_interrupt(&ctx, crate::telemetry::create(), &paths, interrupt, &CheckInfo::default(), None, None);
        unsafe {
            libc::close(fds[0]);
            libc::close(fds[1]);
        }
        // The handler ran once: after a cancellation no handler runs.
        assert_eq!(calls, 1);
        let (unfinished, (user_message, log_message)) = cancelled.expect("cancelled");
        assert_eq!(user_message, "Files have changed on disk!");
        assert_eq!(log_message, "test");
        assert!(!unfinished.is_empty(), "the check finished before the cancellation");
        // Every file is either checked (it has its error) or unfinished.
        let checked = files_of(&result.diagnostics);
        let unfinished_set: std::collections::BTreeSet<RelativePath> =
            unfinished.iter().cloned().collect();
        assert_eq!(unfinished_set.len(), unfinished.len());
        assert!(checked.is_disjoint(&unfinished_set));
        assert_eq!(checked.len() + unfinished_set.len(), n);
    }

    #[test]
    fn handlers_whose_fd_is_not_ready_do_not_run() {
        let _serial = serial();
        let (ctx, paths) = ctx_of(&files_with_an_error("quiet", 20));
        let mut fds = [0; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
        let handler: InterruptHandler<'_, usize> =
            Box::new(|calls| (calls + 1, InterruptResult::Continue));
        let interrupt = InterruptConfig {
            env: 0,
            handlers: vec![(fds[0], handler)],
        };
        let ((calls, result), cancelled) =
            go_with_interrupt(&ctx, crate::telemetry::create(), &paths, interrupt, &CheckInfo::default(), None, None);
        unsafe {
            libc::close(fds[0]);
            libc::close(fds[1]);
        }
        assert_eq!(calls, 0);
        assert!(cancelled.is_none());
        assert_eq!(files_of(&result.diagnostics).len(), paths.len());
    }

    /// Without handlers nothing is polled: a tiny check returns as soon as
    /// it is done (no floor of a polling interval).
    #[test]
    fn a_tiny_check_returns_at_once() {
        let _serial = serial();
        let (ctx, paths) = ctx_of(&files_with_an_error("tiny", 1));
        // (The first check of a thread warms its caches.)
        let _ = go(&ctx, crate::telemetry::create(), &paths, &CheckInfo::default(), None);
        let start = Instant::now();
        let result = go(&ctx, crate::telemetry::create(), &paths, &CheckInfo::default(), None);
        let without_handlers = start.elapsed();
        assert_eq!(files_of(&result.diagnostics).len(), 1);
        // With a handler whose fd is never readable, the end of the pool
        // wakes the calling thread all the same.
        let mut fds = [0; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
        let handler: InterruptHandler<'_, ()> = Box::new(|()| ((), InterruptResult::Continue));
        let start = Instant::now();
        let (((), _), cancelled) = go_with_interrupt(
            &ctx,
            crate::telemetry::create(),
            &paths,
            InterruptConfig {
                env: (),
                handlers: vec![(fds[0], handler)],
            },
            &CheckInfo::default(),
            None,
            None,
        );
        let with_a_handler = start.elapsed();
        unsafe {
            libc::close(fds[0]);
            libc::close(fds[1]);
        }
        assert!(cancelled.is_none());
        assert!(
            without_handlers < Duration::from_millis(30) && with_a_handler < Duration::from_millis(30),
            "{without_handlers:?} {with_a_handler:?}"
        );
    }

    #[test]
    fn mock_cancel() {
        let _serial = serial();
        let (ctx, paths) = ctx_of(&files_with_an_error("mock", 5));
        test_mocking::set_is_cancelled(paths[2].clone());
        let (((), result), cancelled) =
            go_with_interrupt(&ctx, crate::telemetry::create(), &paths, no_interrupt(()), &CheckInfo::default(), None, None);
        let (unfinished, reason) = cancelled.expect("mock cancelled");
        assert_eq!(unfinished, vec![paths[2].clone()]);
        assert_eq!(reason, ("mock cancel".to_string(), "mock cancel".to_string()));
        assert_eq!(files_of(&result.diagnostics).len(), 4);
        // Only once.
        let (((), _), cancelled) =
            go_with_interrupt(&ctx, crate::telemetry::create(), &paths, no_interrupt(()), &CheckInfo::default(), None, None);
        assert!(cancelled.is_none());
    }
}
