// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_check_service.ml` (`process_file`,
//! `process_workitems`, `go`, `go_with_interrupt`, `TestMocking`; no distc,
//! worker processes, decl prefetching (`Declare` workitems), map-reduce or
//! memory caps). See `hh/PORTING.md` and plan D2.
//!
//! Owned by **TCS** (plan §3.1).
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
//! (`typing_deps::trace`, see `check::check_root`), and a panic while
//! checking a file reported as an internal error of that file (`Typing[4001]`;
//! plan §9.2: the OCaml's worker would fail).
//!
//! # Deviations
//!
//! - The diagnostics of [`go`] are merged as if one worker had checked every
//!   file, in order, in one bucket (as `server_main::full_init_diagnostics`
//!   does): the OCaml's order of the diagnostics of a file reported while
//!   checking several *other* files depends on how the files were spread over
//!   the workers, which threads cannot reproduce.
//! - A cancellation lets the files being checked finish (a thread cannot be
//!   killed as a worker process is); they count as checked, the files not
//!   started are returned as unfinished. The OCaml returns the in-progress
//!   buckets as unfinished instead. Either way a file is in exactly one of
//!   the two.
//! - `Typechecker_options.num_local_workers` does not limit the threads (the
//!   pool is built once per process; plan D12).

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
use crate::diagnostics_state;
use crate::relative_path::RelativePath;
use crate::typing_deps;

type Diag = crate::diagnostics_state::T;

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

pub struct TypingResult {
    pub diagnostics: Diag,
    pub telemetry: crate::telemetry::T,
}

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
/// environment, so the handlers are a list here (plan §8.4).
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
    let errors = if diagnostics_state::has_errors(None, &file_errors) {
        file_errors
    } else {
        // (`Provider_context.map_tcopt ctx ~f:(fun _ -> opts)` is the
        // identity.)
        crate::typing_check_job::calc_errors(ctx, Some(false), fn_, ast)
    };
    if keep_fixmed {
        errors
    } else {
        diagnostics_state::drop_fixmed_errors_in_files(errors)
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
    finished: Option<crossbeam_channel::Sender<(usize, Option<Diag>)>>,
    stream_diagnostics: bool,
}

/// What the calling thread does while the pool checks (see [`check_paths`]):
/// it is given whether the pool is done, a function that stops it from
/// starting files, and the files finished, as they finish.
pub(crate) type During<'d> = &'d mut dyn FnMut(
    &dyn Fn() -> bool,
    &dyn Fn(),
    &crossbeam_channel::Receiver<(usize, Option<Diag>)>,
);

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
    let (sender, receiver) = if during.is_some() {
        let (s, r) = crossbeam_channel::unbounded();
        (Some(s), Some(r))
    } else {
        (None, None)
    };
    let shared = Shared {
        paths,
        keep_fixmed,
        on_panic,
        stop: AtomicBool::new(false),
        failure: Mutex::new(None),
        done: AtomicUsize::new(0),
        finished: sender,
        stream_diagnostics,
    };
    // `HH_PHASE_MARKERS=1`: say when the check phase starts (for profiling).
    if std::env::var_os("HH_PHASE_MARKERS").is_some() {
        eprintln!("phase: check");
    }
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
    let work = || -> Vec<Share> {
        rayon::broadcast(|broadcast| {
            // `Typing_deps.worker_id`, which names the files of
            // `SaveToDiskMode` (`new-edges-worker-<id>.bin`): the OCaml's
            // workers are numbered from 1.
            if records_edges && typing_deps::worker_id.get().is_none() {
                typing_deps::worker_id.set(Some(broadcast.index() as isize + 1));
            }
            crate::file_provider::local_changes_push_sharedmem_stack();
            crate::ast_provider::local_changes_push_sharedmem_stack();
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
                            if let Some(finished) = &shared.finished {
                                let copy = shared
                                    .stream_diagnostics
                                    .then(|| outcome.diagnostics.clone());
                                let _ = finished.send((index, copy));
                            }
                            results.push((index, outcome));
                        }
                        None => break 'share,
                    }
                }
            }
            // Update edges
            let dep_edges = if records_edges {
                let new_dep_edges = typing_deps::flush_ideps_batch(&ctx.deps_mode);
                if ctx.tco.tco_record_fine_grained_dependencies {
                    crate::typing_pessimisation_deps::finalize(&ctx.deps_mode);
                }
                new_dep_edges
            } else {
                typing_deps::dep_edges_make()
            };
            crate::ast_provider::local_changes_pop_sharedmem_stack();
            crate::file_provider::local_changes_pop_sharedmem_stack();
            (results, dep_edges)
        })
    };
    let per_thread: Vec<Share> = std::thread::scope(|scope| {
        scope.spawn(|| read_ahead.run(ctx, paths, &next, &shared.stop));
        let per_thread = match during {
            None => std::panic::catch_unwind(std::panic::AssertUnwindSafe(work)),
            Some(during) => {
                let handle = scope.spawn(work);
                let finished_all = || handle.is_finished();
                let stop = || shared.stop.store(true, Ordering::Relaxed);
                during(&finished_all, &stop, receiver.as_ref().unwrap());
                handle.join()
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
                        vec![crate::diagnostics::error(
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
    pub(super) fn take(fnl: Vec<RelativePath>) -> (Vec<RelativePath>, Vec<RelativePath>) {
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
    let mut worker = Diag::new();
    for file_diagnostics in per_file {
        worker = diagnostics_state::merge(file_diagnostics, worker);
    }
    diagnostics_state::merge(worker, Diag::new())
}

/// `Merge.process_errors ~log_errors`: the first errors of a batch, logged.
fn log_batch_errors(errors: &Diag) {
    let error_count = diagnostics_state::count(None, errors);
    if error_count > 0 {
        let max_errors = 5;
        crate::hh_logger::log(&format!(
            "{} errors in batch. Showing first {}:",
            error_count, max_errors
        ));
        for error in diagnostics_state::get_diagnostic_list(None, errors.clone())
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

/// `go_with_interrupt ctx workers telemetry fnl ~interrupt ~check_info`:
/// checks `files` on the pool while the calling thread runs the handlers of
/// `interrupt` whose file descriptors become readable (polled every 100 ms;
/// the OCaml selects on them between buckets). A `Cancel` stops starting
/// files: the files not checked are returned with the reason. The edges the
/// threads recorded are registered before returning.
///
/// A panic while checking a file ends the check: "Exception on file ..." on
/// stderr, then [`CoalescedFailures`] is raised (`panic_any`) on the calling
/// thread, as `Multi_threaded_call` raises it when a worker fails.
pub fn go_with_interrupt<E>(
    ctx: &Arc<Ctx>,
    files: &[RelativePath],
    check_info: &CheckInfo,
    interrupt: InterruptConfig<'_, E>,
) -> (E, TypingResult, Option<(Vec<RelativePath>, CancelReason)>) {
    let telemetry = crate::telemetry::create();
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
    let (fnl, mock_cancelled) = test_mocking::take(fnl);
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
    // The files finished since the last progress report: a "bucket" of the
    // OCaml, of the size it would have (`Bucket.calculate_bucket_size`).
    #[cfg(feature = "server")]
    let bucket_size = crate::bucket::calculate_bucket_size(
        total_count as isize,
        rayon::current_num_threads() as isize,
        None,
    )
    .max(1) as usize;
    // (Without the server, `Bucket` is not compiled: the same formula.)
    #[cfg(not(feature = "server"))]
    let bucket_size = {
        let (num_jobs, num_workers, max_size) =
            (total_count, rayon::current_num_threads().max(1), 500);
        if num_jobs < num_workers * max_size {
            1 + num_jobs / num_workers
        } else {
            max_size
        }
    };
    let mut batch: Vec<Diag> = vec![];
    let mut batch_len = 0usize;
    let log_errors = check_info.log_errors;
    // `Merge.merge` of a bucket: progress, then `process_errors`.
    let merge_batch = |batch: &mut Vec<Diag>, done_count: usize| {
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
            let errors = merge_in_order(std::mem::take(batch));
            log_batch_errors(&errors);
            // Handle errors paradigm (3) - push updates to errors-file as
            // soon as their batch is finished (`stream_errors` is
            // `check_info.log_errors`).
            #[cfg(feature = "server")]
            crate::server_progress::errors_write::report(&errors);
        }
        batch.clear();
    };
    let fds: Vec<RawFd> = handlers.iter().map(|(fd, _)| *fd).collect();
    let mut during = |finished_all: &dyn Fn() -> bool,
                      stop: &dyn Fn(),
                      finished: &crossbeam_channel::Receiver<(usize, Option<Diag>)>| {
        loop {
            let all = finished_all();
            while let Ok((_index, diagnostics)) = finished.try_recv() {
                batch.extend(diagnostics);
                batch_len += 1;
                done_count += 1;
                if batch_len >= bucket_size {
                    batch_len = 0;
                    merge_batch(&mut batch, done_count);
                }
            }
            if all {
                if batch_len > 0 {
                    batch_len = 0;
                    merge_batch(&mut batch, done_count);
                }
                break;
            }
            let ready = poll_readable(&fds, Duration::from_millis(100));
            if cancel_reason.is_none() && !ready.is_empty() {
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
        }
    };
    let checked = check_paths(
        ctx,
        &paths,
        check_info.keep_fixmed,
        OnPanic::WorkerFailed,
        Some(&mut during),
        log_errors,
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
        env,
        TypingResult {
            diagnostics,
            telemetry,
        },
        cancelled_fnl_and_reason,
    )
}

/// The file descriptors of `fds` that are readable within `timeout` (all of
/// them return at once when one is; none after the timeout). With no file
/// descriptor, sleeps for `timeout`.
fn poll_readable(fds: &[RawFd], timeout: Duration) -> Vec<RawFd> {
    if fds.is_empty() {
        std::thread::sleep(timeout);
        return vec![];
    }
    let mut pollfds: Vec<libc::pollfd> = fds
        .iter()
        .map(|&fd| libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        })
        .collect();
    let n = unsafe {
        libc::poll(
            pollfds.as_mut_ptr(),
            pollfds.len() as libc::nfds_t,
            timeout.as_millis() as libc::c_int,
        )
    };
    if n <= 0 {
        return vec![];
    }
    pollfds
        .iter()
        .filter(|p| p.revents & (libc::POLLIN | libc::POLLHUP | libc::POLLERR) != 0)
        .map(|p| p.fd)
        .collect()
}

/// `go ctx workers telemetry fnl ~check_info`: [`go_with_interrupt`] without
/// interrupts.
pub fn go(ctx: &Arc<Ctx>, files: &[RelativePath], check_info: &CheckInfo) -> TypingResult {
    let ((), result, unfinished_and_reason) =
        go_with_interrupt(ctx, files, check_info, no_interrupt(()));
    assert!(unfinished_and_reason.is_none());
    result
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use oxidized::typechecker_options::TypecheckerOptions;
    use relative_path::Prefix;

    use super::*;

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
        let result = go(&ctx, &paths, &CheckInfo::default());
        assert_eq!(files_of(&result.diagnostics), paths.iter().cloned().collect());
        // The same diagnostics as the batch check's.
        let pos_paths: Vec<pos::RelativePath> = paths.iter().map(pos::RelativePath::from).collect();
        let batch = crate::check::check_files_typed_by_file(
            &ctx,
            &pos_paths,
            &mut crate::check::Stats::default(),
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
        let (calls, result, cancelled) =
            go_with_interrupt(&ctx, &paths, &CheckInfo::default(), interrupt);
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
        let (calls, result, cancelled) =
            go_with_interrupt(&ctx, &paths, &CheckInfo::default(), interrupt);
        unsafe {
            libc::close(fds[0]);
            libc::close(fds[1]);
        }
        assert_eq!(calls, 0);
        assert!(cancelled.is_none());
        assert_eq!(files_of(&result.diagnostics).len(), paths.len());
    }

    #[test]
    fn mock_cancel() {
        let _serial = serial();
        let (ctx, paths) = ctx_of(&files_with_an_error("mock", 5));
        test_mocking::set_is_cancelled(paths[2].clone());
        let ((), result, cancelled) =
            go_with_interrupt(&ctx, &paths, &CheckInfo::default(), no_interrupt(()));
        let (unfinished, reason) = cancelled.expect("mock cancelled");
        assert_eq!(unfinished, vec![paths[2].clone()]);
        assert_eq!(reason, ("mock cancel".to_string(), "mock cancel".to_string()));
        assert_eq!(files_of(&result.diagnostics).len(), 4);
        // Only once.
        let ((), _, cancelled) =
            go_with_interrupt(&ctx, &paths, &CheckInfo::default(), no_interrupt(()));
        assert!(cancelled.is_none());
    }
}
