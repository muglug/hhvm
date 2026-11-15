// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `procs/worker_controller.ml`: the master's side of the workers.
//! See `crate::worker` (the workers' side) and `hh/PORTING.md`.
//!
//! The workers are prespawned by [`make`], each with a pipe pair for its
//! jobs and a side channel (`controller_fd`) for the exit status of a clone
//! that failed. [`call`] sends a job (its name in `crate::worker_jobs` and
//! its serialized input: see `crate::worker`, with the data of the call
//! wrapper, if any: [`CallWrapper`]),
//! [`select`] waits for results (and other file descriptors), [`get_result`]
//! reads one, [`cancel`] stops the jobs in progress
//! (`Worker_cancel.stop_workers`: the shared heap's flag).

use std::os::fd::RawFd;
use std::sync::Arc;

use crate::worker::ProcessStatus;

/// `worker_failure`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorkerFailure {
    /// Worker force quit by Out Of Memory.
    WorkerOomed,
    WorkerQuit(ProcessStatus),
}

/// `exception Worker_failed of (process_id * worker_failure)`: a panic
/// payload.
#[derive(Clone, Debug)]
pub struct WorkerFailed {
    pub pid: i32,
    pub failure: WorkerFailure,
}

/// `status_string`
pub fn status_string(s: ProcessStatus) -> String {
    match s {
        ProcessStatus::WExited(i) => format!("WEXITED {}", i),
        ProcessStatus::WSignaled(i) => format!("WSIGNALED {}", i),
        ProcessStatus::WStopped(i) => format!("WSTOPPED {}", i),
    }
}

/// `failure_to_string`
pub fn failure_to_string(f: &WorkerFailure) -> String {
    match f {
        WorkerFailure::WorkerOomed => "Worker_oomed".to_string(),
        WorkerFailure::WorkerQuit(s) => format!("(Worker_quit {})", status_string(*s)),
    }
}

impl std::fmt::Display for WorkerFailed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Worker_failed (process_id = {}): {}",
            self.pid,
            failure_to_string(&self.failure)
        )
    }
}

/// `call_wrapper = Call_wrapper : 'data wrapper -> call_wrapper`, with
/// `'data wrapper = { prepare; wrap }`: [prepare] runs in the calling process
/// for every request. The returned data is marshalled with the request;
/// [wrap data f x] runs in the worker.
///
/// Rust cannot marshal closures (see `crate::worker`): `prepare` gives the
/// data serialized, and `wrap` is the name under which the worker finds the
/// function (`crate::worker_jobs::wrap`), as it finds the jobs.
#[derive(Clone)]
pub struct CallWrapper {
    pub prepare: Arc<dyn Fn() -> Vec<u8> + Send + Sync>,
    pub wrap: &'static str,
}

impl std::fmt::Debug for CallWrapper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Call_wrapper {}", self.wrap)
    }
}

/// A worker (`Worker.t`): its process (prespawned), the master's ends of its
/// pipes, its side channel.
#[derive(Debug)]
pub struct Worker {
    pub id: isize,
    /// The call wrapper will wrap any workload sent to the worker (via "call"
    /// below) before invoking the workload.
    ///
    /// For each call, `prepare ()` runs in the calling process. Its result is sent
    /// with the request, and `wrap data f x` runs in the worker.
    ///
    /// This allows universal handling of workload at the time we create the actual
    /// workers. For example, this can be useful to handle exceptions uniformly
    /// across workers regardless what workload is called on them.
    call_wrapper: Option<CallWrapper>,
    pid: i32,
    /// The master reads the results here (`infd`).
    infd: RawFd,
    /// The master writes the jobs here.
    outfd: RawFd,
    controller_fd: Option<RawFd>,
    busy: bool,
    force_quit: bool,
}

impl Worker {
    /// `worker_id`
    pub fn worker_id(&self) -> isize {
        self.id
    }

    /// The pid of the worker's process (the `.pids` file's `subprocess_1`).
    pub fn pid(&self) -> i32 {
        self.pid
    }
}

/// The instructions and cycles of the clones whose results were read (not in
/// the OCaml: `hh check`'s instruction counts count every process).
static CLONE_INSTRUCTIONS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CLONE_CYCLES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

static CLONE_MICROS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CLONE_USER_MICROS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The user and user+system CPU seconds of the clones whose results were read.
pub fn clone_cpu_seconds() -> (f64, f64) {
    (
        CLONE_USER_MICROS.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e6,
        CLONE_MICROS.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e6,
    )
}

/// See [`CLONE_INSTRUCTIONS`].
pub fn clone_instructions_and_cycles() -> (u64, u64) {
    (
        CLONE_INSTRUCTIONS.load(std::sync::atomic::Ordering::Relaxed),
        CLONE_CYCLES.load(std::sync::atomic::Ordering::Relaxed),
    )
}

/// `max_workers`
const MAX_WORKERS: usize = 1000;

/// `make ?call_wrapper ~longlived_workers:false ~saved_state ~entry nbr_procs
/// ~gc_control ~heap_handle`: spawns the workers, named
/// `worker_process_<n>_out_of_<nbr_procs>_for_server_pid_<pid>`
/// (`Worker_utils.worker_name_fmt`).
///
/// `trace`: `Typing_deps.trace` of the workers. The OCaml's workers copy the
/// master's at spawn, `ref true` then (`Server_env_build.make_genv` turns the
/// master's off later in check mode): the daemon passes `true`; the batch
/// check traces only when the edges are saved (see `check::check_root`).
pub fn make(
    call_wrapper: Option<CallWrapper>,
    nbr_procs: usize,
    heap_handle: &crate::hh_shared::Handle,
    trace: bool,
) -> std::io::Result<Vec<Worker>> {
    if nbr_procs >= MAX_WORKERS {
        panic!("Too many workers");
    }
    let mut state = crate::server_global_state::save();
    state.trace = trace;
    let pid = std::process::id();
    let mut made = vec![];
    for n in 1..=nbr_procs {
        // `setup_controller_fd`
        let (parent_fd, child_fd) = pipe()?;
        crate::rt::ocaml_unix::set_close_on_exec(parent_fd);
        let name = format!("worker_process_{}_out_of_{}_for_server_pid_{}", n, nbr_procs, pid);
        // `spawn worker_id name child_fd ()`
        crate::hh_shared::set_close_on_exec(false);
        crate::rt::ocaml_unix::clear_close_on_exec(child_fd);
        let params = crate::worker::WorkerParams {
            state: state.clone(),
            heap_handle: heap_handle.clone(),
            worker_id: n as isize,
            controller_fd: Some(child_fd),
        };
        let handle = crate::daemon::spawn(
            crate::daemon::ChannelMode::Pipe,
            Some(&name),
            (crate::daemon::null_fd()?, 1, 2),
            crate::worker::ENTRY,
            &params,
        );
        crate::hh_shared::set_close_on_exec(true);
        // This process no longer needs child_fd after its spawned the child.
        unsafe { libc::close(child_fd) };
        let handle = handle?;
        made.push(Worker {
            id: n as isize,
            call_wrapper: call_wrapper.clone(),
            pid: handle.pid,
            infd: handle.channels.0,
            outfd: handle.channels.1,
            controller_fd: Some(parent_fd),
            busy: false,
            force_quit: false,
        });
    }
    Ok(made)
}

fn pipe() -> std::io::Result<(RawFd, RawFd)> {
    let mut fds = [0; 2];
    if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok((fds[0], fds[1]))
}

/// A job sent to a worker (`('a, 'b) handle` while `Processing`): the
/// worker's index in the list the call was given, its input (for
/// `on_cancelled`) and the call's id.
#[derive(Debug)]
pub struct Handle<I> {
    pub worker: usize,
    pub input: I,
    pub call_id: usize,
    infd: RawFd,
}

impl<I> Handle<I> {
    /// `get_job`
    pub fn get_job(&self) -> &I {
        &self.input
    }
}

/// `exception Worker_failed_to_send_job of send_job_failure`
#[derive(Debug)]
pub enum SendJobFailure {
    WorkerAlreadyExited(ProcessStatus),
    OtherSendJobFailure(String),
}

/// `exception Worker_failed_to_send_job`: a panic payload.
#[derive(Debug)]
pub struct WorkerFailedToSendJob(pub SendJobFailure);

/// `wrap_request w f x metadata_in`: if there is a call_wrapper, apply it
/// and create the Request.
fn wrap_request<I: serde::Serialize>(w: &Worker, job: &str, input: &I) -> crate::worker::Request {
    match &w.call_wrapper {
        Some(CallWrapper { prepare, wrap }) => {
            let data = prepare();
            crate::worker::Request {
                job: job.to_string(),
                input: crate::worker::encode(input),
                call_wrapper: Some((wrap.to_string(), data)),
            }
        }
        None => crate::worker::Request {
            job: job.to_string(),
            input: crate::worker::encode(input),
            call_wrapper: None,
        },
    }
}

/// `call ?call_id w f x`: sends the job `job` with `input` (serialized) to
/// `workers[w]`.
pub fn call<I: serde::Serialize>(
    workers: &mut [Worker],
    w: usize,
    call_id: usize,
    job: &str,
    input: I,
) -> Handle<I> {
    let worker = &mut workers[w];
    if worker.force_quit {
        panic!("force quit worker ({})", worker.id);
    }
    worker.busy = true;
    let request = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        wrap_request(worker, job, &input)
    })) {
        Ok(request) => request,
        Err(exn) => {
            // `mark_free w`
            worker.busy = false;
            std::panic::resume_unwind(exn)
        }
    };
    if let Err(e) = crate::worker::write_frame(worker.outfd, &crate::worker::encode(&request)) {
        let failure = match crate::worker::waitpid_non_intr(worker.pid, libc::WNOHANG) {
            Some((0, _)) | None => SendJobFailure::OtherSendJobFailure(e.to_string()),
            Some((_, status)) => SendJobFailure::WorkerAlreadyExited(status),
        };
        std::panic::panic_any(WorkerFailedToSendJob(failure))
    }
    Handle {
        worker: w,
        input,
        call_id,
        infd: worker.infd,
    }
}

/// `worker_failed pid_stat controller_fd`: the status of the clone (read
/// on the side channel, else the worker's), as a failure.
fn worker_failed(worker: &Worker, pid_stat: ProcessStatus) -> WorkerFailed {
    let status = match worker.controller_fd {
        None => pid_stat,
        Some(fd) => {
            // (`Timeout.with_timeout ~timeout:3`: the clone's status is
            // written before the worker exits.)
            if wait_readable(&[fd], Some(3000)).is_empty() {
                pid_stat
            } else {
                match crate::worker::read_frame(fd)
                    .ok()
                    .and_then(|b| crate::worker::decode::<crate::worker::SubprocessTerminated>(&b).ok())
                {
                    Some(crate::worker::SubprocessTerminated(status)) => status,
                    None => pid_stat,
                }
            }
        }
    };
    if let ProcessStatus::WExited(i) = status {
        eprint!("Subprocess({}): fail {}", worker.pid, i);
    }
    let failure = match status {
        ProcessStatus::WSignaled(9) => WorkerFailure::WorkerOomed,
        s => WorkerFailure::WorkerQuit(s),
    };
    WorkerFailed {
        pid: worker.pid,
        failure,
    }
}

/// `with_exit_status_check ?block_on_waitpid worker_pid f`
fn with_exit_status_check<T>(
    worker: &Worker,
    block_on_waitpid: bool,
    f: impl FnOnce() -> std::io::Result<T>,
) -> Result<std::io::Result<T>, WorkerFailed> {
    let flags = if block_on_waitpid { 0 } else { libc::WNOHANG };
    match crate::worker::waitpid_non_intr(worker.pid, flags) {
        Some((0, _)) => Ok(f()),
        Some((_, ProcessStatus::WExited(0))) => {
            // This will never actually happen. A worker process only exits
            // if this controller process has exited.
            panic!("Worker process exited 0 unexpectedly")
        }
        Some((_, status)) => Err(worker_failed(worker, status)),
        None => Ok(f()),
    }
}

/// `get_result d`: the job's output (blocks until the worker answers).
pub fn get_result<I, O: serde::de::DeserializeOwned>(
    workers: &mut [Worker],
    h: &Handle<I>,
) -> Result<O, WorkerFailed> {
    let bytes = get_result_bytes(workers, h)?;
    match crate::worker::decode::<O>(&bytes) {
        Ok(out) => Ok(out),
        Err(e) => panic!("Worker_controller.get_result: {}", e),
    }
}

/// [`get_result`] up to the decoding of the output (which the caller does,
/// once the worker has its next job).
pub fn get_result_bytes<I>(workers: &mut [Worker], h: &Handle<I>) -> Result<Vec<u8>, WorkerFailed> {
    type O = Vec<u8>;
    let worker = &workers[h.worker];
    let read = || -> std::io::Result<O> {
        let bytes = crate::worker::read_frame(h.infd)?;
        match crate::worker::decode::<crate::worker::Response>(&bytes)? {
            crate::worker::Response::Output(out, instructions, cycles, user, sys) => {
                CLONE_INSTRUCTIONS.fetch_add(instructions, std::sync::atomic::Ordering::Relaxed);
                CLONE_CYCLES.fetch_add(cycles, std::sync::atomic::Ordering::Relaxed);
                CLONE_MICROS.fetch_add(((user + sys) * 1e6) as u64, std::sync::atomic::Ordering::Relaxed);
                CLONE_USER_MICROS.fetch_add((user * 1e6) as u64, std::sync::atomic::Ordering::Relaxed);
                Ok(out)
            }
            crate::worker::Response::Cancelled => Err(std::io::Error::new(
                std::io::ErrorKind::Interrupted,
                "the job was cancelled",
            )),
        }
    };
    // We run the "with_exit_status_check" twice (first time
    // non-blockingly) because of a race with the worker's waitpid on a
    // failed clone (see the OCaml).
    let res = match with_exit_status_check(worker, false, read)? {
        Ok(out) => Ok(out),
        Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
            match with_exit_status_check(worker, true, read)? {
                Ok(out) => Ok(out),
                Err(e) => Err(e),
            }
        }
        Err(e) => Err(e),
    };
    workers[h.worker].busy = false;
    match res {
        Ok(out) => Ok(out),
        Err(e) => panic!("Worker_controller.get_result: {}", e),
    }
}

/// `wait_for_cancel d`: reads (and ignores) what the cancelled job answers.
fn wait_for_cancel<I>(workers: &mut [Worker], h: &Handle<I>) -> Result<(), WorkerFailed> {
    let worker = &workers[h.worker];
    let r = with_exit_status_check(worker, false, || crate::worker::read_frame(h.infd).map(|_| ()));
    workers[h.worker].busy = false;
    match r {
        Ok(_) => Ok(()),
        Err(failed) => Err(failed),
    }
}

/// `cancel handles`
pub fn cancel<I>(workers: &mut [Worker], handles: &[Handle<I>]) -> Result<(), WorkerFailed> {
    crate::hh_shared::stop_workers();
    let mut res = Ok(());
    for h in handles {
        if let Err(e) = wait_for_cancel(workers, h) {
            res = Err(e)
        }
    }
    crate::hh_shared::resume_workers();
    res
}

/// The file descriptors of `fds` that are readable (or hung up), waiting
/// at most `timeout_ms` (forever if `None`; `Sys_utils.select_non_intr`).
pub fn wait_readable(fds: &[RawFd], timeout_ms: Option<i32>) -> Vec<RawFd> {
    let mut pfds: Vec<libc::pollfd> = fds
        .iter()
        .map(|&fd| libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        })
        .collect();
    loop {
        let r = unsafe { libc::poll(pfds.as_mut_ptr(), pfds.len() as libc::nfds_t, timeout_ms.unwrap_or(-1)) };
        if r < 0 {
            if std::io::Error::last_os_error().raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            panic!("select: {}", std::io::Error::last_os_error())
        }
        return pfds
            .iter()
            .filter(|p| p.revents & (libc::POLLIN | libc::POLLHUP | libc::POLLERR) != 0)
            .map(|p| p.fd)
            .collect();
    }
}

/// `select ds additional_fds`: the handles whose worker answered (readys),
/// the others (waiters), and the additional fds that are ready.
pub fn select<I>(handles: Vec<Handle<I>>, additional_fds: &[RawFd]) -> (Vec<Handle<I>>, Vec<Handle<I>>, Vec<RawFd>) {
    if handles.is_empty() {
        return (vec![], vec![], vec![]);
    }
    let mut fds: Vec<RawFd> = handles.iter().map(|h| h.infd).collect();
    fds.extend_from_slice(additional_fds);
    let ready = wait_readable(&fds, None);
    let additional_ready: Vec<RawFd> = additional_fds.iter().copied().filter(|fd| ready.contains(fd)).collect();
    let (readys, waiters): (Vec<_>, Vec<_>) = handles.into_iter().partition(|h| ready.contains(&h.infd));
    (readys, waiters, additional_ready)
}

/// `force_quit w`: kills the worker's process.
pub fn force_quit(w: &mut Worker) {
    if !w.force_quit {
        w.force_quit = true;
        unsafe { libc::kill(w.pid, libc::SIGKILL) };
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    use super::*;

    /// A worker without a process whose requests go to a pipe: the read end.
    fn worker_on_a_pipe(call_wrapper: Option<CallWrapper>) -> (Worker, RawFd) {
        let (read, write) = pipe().unwrap();
        let worker = Worker {
            id: 1,
            call_wrapper,
            // (No process: `waitpid` of pid 0 is never reached, the writes
            // to the pipe succeed.)
            pid: 0,
            infd: -1,
            outfd: write,
            controller_fd: None,
            busy: false,
            force_quit: false,
        };
        (worker, read)
    }

    fn read_request(fd: RawFd) -> crate::worker::Request {
        crate::worker::decode(&crate::worker::read_frame(fd).unwrap()).unwrap()
    }

    /// `test_wrapper_prepares_each_request` (`worker_test.ml`): preparation
    /// runs once in the master for each request, observing changes made in
    /// the master after pool creation and between calls; its data travels
    /// with the request.
    #[test]
    fn wrapper_prepares_each_request() {
        let preparations = Arc::new(AtomicUsize::new(0));
        let call_wrapper = CallWrapper {
            prepare: {
                let preparations = Arc::clone(&preparations);
                Arc::new(move || {
                    let n = preparations.fetch_add(1, Ordering::SeqCst) + 1;
                    crate::worker::encode(&n)
                })
            },
            wrap: "test wrapper",
        };
        let (worker, read) = worker_on_a_pipe(Some(call_wrapper));
        let mut workers = vec![worker];
        // Pool creation must not take the snapshot.
        assert_eq!(preparations.load(Ordering::SeqCst), 0);
        for expected in 1..=2usize {
            let _h = call(&mut workers, 0, 0, "echo", "x".to_string());
            let request = read_request(read);
            assert_eq!(request.job, "echo");
            let (wrapper, data) = request.call_wrapper.unwrap();
            assert_eq!(wrapper, "test wrapper");
            assert_eq!(crate::worker::decode::<usize>(&data).unwrap(), expected);
            assert_eq!(preparations.load(Ordering::SeqCst), expected);
            workers[0].busy = false;
        }
        unsafe {
            libc::close(read);
            libc::close(workers[0].outfd);
        }
    }

    /// `test_wrapper_preparation_failure_leaves_worker_available`
    /// (`worker_test.ml`): a failed preparation sends no request and leaves
    /// the worker available for the next call. The exception is raised in
    /// the master.
    #[test]
    fn wrapper_preparation_failure_leaves_worker_available() {
        let fail = Arc::new(std::sync::atomic::AtomicBool::new(true));
        let call_wrapper = CallWrapper {
            prepare: {
                let fail = Arc::clone(&fail);
                Arc::new(move || {
                    if fail.load(Ordering::SeqCst) {
                        panic!("preparation failed")
                    }
                    crate::worker::encode(&())
                })
            },
            wrap: "test wrapper",
        };
        let (worker, read) = worker_on_a_pipe(Some(call_wrapper));
        let mut workers = vec![worker];
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            call(&mut workers, 0, 0, "echo", "x".to_string())
        }));
        assert_eq!(crate::worker::panic_message(&r.unwrap_err()), "preparation failed");
        assert!(!workers[0].busy);
        // Nothing was sent.
        assert!(wait_readable(&[read], Some(0)).is_empty());
        fail.store(false, Ordering::SeqCst);
        let _h = call(&mut workers, 0, 0, "echo", "x".to_string());
        assert!(workers[0].busy);
        assert!(read_request(read).call_wrapper.is_some());
        unsafe {
            libc::close(read);
            libc::close(workers[0].outfd);
        }
    }

    /// Without a call wrapper, the request has none.
    #[test]
    fn no_wrapper() {
        let (worker, read) = worker_on_a_pipe(None);
        let mut workers = vec![worker];
        let _h = call(&mut workers, 0, 0, "echo", "x".to_string());
        assert!(read_request(read).call_wrapper.is_none());
        unsafe {
            libc::close(read);
            libc::close(workers[0].outfd);
        }
    }
}
