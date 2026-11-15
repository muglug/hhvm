// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `procs/worker.ml` (with `procs/worker_controller_entry_point.ml`):
//! the worker process, which forks a clone for every job; the clone reads the
//! job, runs it, writes the result and exits. See `hh/PORTING.md`.
//!
//! Used only with `HH_RUST_WORKERS=1` (`multi_worker::workers_switched_on`):
//! by default the threads of the server's pool do the workers' work.
//!
//! A worker is the server's executable started again by `Daemon.spawn`
//! (`crate::daemon`), entry `subprocess_1`, with the master's global
//! state and the shared heap's handle. It stays single-threaded (it only
//! waits for a job and forks), so that the fork is safe; the clone runs the
//! job on one thread of its own with the typechecker's stack
//! (`check::STACK_SIZE`: the main thread's cannot be made larger) while its
//! main thread waits.
//!
//! What differs from the OCaml, and why:
//! - A job is a marshalled closure in the OCaml. Rust cannot marshal
//!   closures: a request names its job (`crate::worker_jobs`, which runs it)
//!   and carries its input, serialized with serde (bincode); results too.
//! - The frames are an 8-byte length then the bytes (`Marshal_tools`'
//!   preamble holds the size too).
//! - `Measure`'s statistics and `Hack_event_logger`'s globals (the
//!   `metadata_out` of the OCaml) are not sent back: nothing reads them here.

use std::io::Read;
use std::io::Write;
use std::os::fd::RawFd;

use serde::Deserialize;
use serde::Serialize;

/// `request = Request of (serializer -> unit) * metadata_in`: the job's name
/// (`crate::worker_jobs`) and its input, with the name of the call wrapper
/// that wraps it and the data its `prepare` gave in the master
/// (`Worker_controller.wrap_request`), if any.
#[derive(Debug, Serialize, Deserialize)]
pub struct Request {
    pub job: String,
    pub input: Vec<u8>,
    pub call_wrapper: Option<(String, Vec<u8>)>,
}

/// What a clone answers: the job's output, or `"anything"` after a
/// cancellation (`on_clone_cancelled`), which the controller ignores.
#[derive(Debug, Serialize, Deserialize)]
pub enum Response {
    /// The output, and the instructions and cycles the clone used (not in
    /// the OCaml: for the instruction counts of `hh check`, which must count
    /// every process).
    Output(Vec<u8>, u64, u64, f64, f64),
    Cancelled,
}

/// The user and system CPU seconds of this process so far.
pub fn cpu_times() -> (f64, f64) {
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut ru) };
    let secs = |t: libc::timeval| t.tv_sec as f64 + t.tv_usec as f64 / 1e6;
    (secs(ru.ru_utime), secs(ru.ru_stime))
}

/// Instructions retired and CPU cycles of this process so far (0 where the
/// OS does not say).
pub fn instructions_and_cycles() -> (u64, u64) {
    #[cfg(target_os = "macos")]
    unsafe {
        let mut info: libc::rusage_info_v4 = std::mem::zeroed();
        libc::proc_pid_rusage(
            libc::getpid(),
            libc::RUSAGE_INFO_V4,
            &mut info as *mut _ as *mut libc::rusage_info_t,
        );
        (info.ri_instructions, info.ri_cycles)
    }
    #[cfg(not(target_os = "macos"))]
    (0, 0)
}

/// `Unix.process_status`
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProcessStatus {
    WExited(i32),
    WSignaled(i32),
    WStopped(i32),
}

/// `subprocess_job_status = Subprocess_terminated of Unix.process_status`
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct SubprocessTerminated(pub ProcessStatus);

/// `job_outcome`
#[derive(Debug)]
enum JobOutcome {
    Success,
    Error(i32),
    WorkerCancelled,
    ControllerHasDied,
}

/// The parameter of the worker's entry point (`'a worker_params` with its
/// `entry_state`: the master's global state, the heap handle, the worker's
/// id; `controller_fd`, the side channel of the clones' exit statuses). The
/// workers are not long-lived (`longlived_workers = false` at Slack's
/// settings): a clone per job.
#[derive(Debug, Serialize, Deserialize)]
pub struct WorkerParams {
    pub state: crate::server_global_state::T,
    pub heap_handle: crate::hh_shared::Handle,
    pub worker_id: isize,
    pub controller_fd: Option<RawFd>,
}

/// The name of the workers' entry point
/// (`Worker_controller_entry_point.register`: `subprocess_<n>`).
pub const ENTRY: &str = "subprocess_1";

/// The exit code used when the controller died and the clone could not read
/// the input job.
const CONTROLLER_HAS_DIED_CODE: i32 = 1;

/// Writes a frame: the length (8 bytes, little-endian), then the bytes.
pub fn write_frame(fd: RawFd, bytes: &[u8]) -> std::io::Result<()> {
    let mut f = std::mem::ManuallyDrop::new(unsafe { <std::fs::File as std::os::fd::FromRawFd>::from_raw_fd(fd) });
    f.write_all(&(bytes.len() as u64).to_le_bytes())?;
    f.write_all(bytes)?;
    Ok(())
}

/// Reads a frame of [`write_frame`] (`UnexpectedEof`: the other end closed).
pub fn read_frame(fd: RawFd) -> std::io::Result<Vec<u8>> {
    let mut f = std::mem::ManuallyDrop::new(unsafe { <std::fs::File as std::os::fd::FromRawFd>::from_raw_fd(fd) });
    let mut len = [0u8; 8];
    f.read_exact(&mut len)?;
    let len = u64::from_le_bytes(len) as usize;
    let mut bytes = vec![0u8; len];
    f.read_exact(&mut bytes)?;
    Ok(bytes)
}

/// Serializes a value of a frame.
pub fn encode<T: Serialize>(v: &T) -> Vec<u8> {
    bincode::serde::encode_to_vec(intern::WithIntern(v), bincode::config::standard())
        .expect("Worker: a value that cannot be serialized")
}

/// Deserializes what [`encode`] wrote.
pub fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> std::io::Result<T> {
    bincode::serde::decode_from_slice::<intern::WithIntern<T>, _>(bytes, bincode::config::standard())
        .map(|(intern::WithIntern(v), _)| v)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e.to_string()))
}

/// The time a job of this clone took to make its context (instrumentation:
/// `HH_MEM_WORKER_FP`; set by the jobs that make one).
pub static JOB_SETUP_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// `on_clone_cancelled parent_outfd`: the cancelling controller ignores
/// what a cancelled job answers.
fn on_clone_cancelled(outfd: RawFd) {
    let _ = write_frame(outfd, &encode(&Response::Cancelled));
}

/// `read_and_process_job_fds infd outfd`, in the clone: the job runs on a
/// thread with the typechecker's stack.
fn read_and_process_job_fds(infd: RawFd, outfd: RawFd) -> JobOutcome {
    let t_start = std::time::Instant::now();
    if std::env::var_os("HH_MEM_WORKER_FP").is_some() {
        crate::hh_shared::GET_TIMING.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    let request: Request = match read_frame(infd) {
        Ok(bytes) => match decode(&bytes) {
            Ok(request) => request,
            Err(_) => return JobOutcome::ControllerHasDied,
        },
        // `End_of_file`
        Err(_) => return JobOutcome::ControllerHasDied,
    };
    let job = request.job.clone();
    let input_len = request.input.len();
    let t_read = t_start.elapsed();
    let run = std::thread::Builder::new()
        .name(format!("job {}", job))
        .stack_size(crate::check::STACK_SIZE)
        .spawn(move || {
            let t_thread = t_start.elapsed();
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                crate::worker_jobs::run_wrapped(
                    request.call_wrapper.as_ref(),
                    &request.job,
                    &request.input,
                )
            }));
            (r, t_thread)
        })
        .expect("Worker: cannot start the job's thread")
        .join();
    let t_ran = t_start.elapsed();
    let (run, t_thread) = match run {
        Ok((r, t)) => (Ok(r), t),
        Err(panic) => (Err(panic), t_ran),
    };
    let result: std::thread::Result<Vec<u8>> = match run {
        Ok(result) => result,
        Err(panic) => Err(panic),
    };
    match result {
        Ok(output) => {
            // After this point, it is critical to not throw a
            // Worker_should_exit exception; otherwise outfd might end up
            // being corrupted.
            crate::worker_cancel::set_can_worker_stop_forever();
            let (instructions, cycles) = instructions_and_cycles();
            let (user, sys) = cpu_times();
            // The MEM census (instrumentation, as the OCaml patch's
            // HH_MEM_WORKER_GC): HH_MEM_WORKER_FP=FILE appends the clone's
            // footprint and peak RSS at the end of each job.
            if let Some(out) = std::env::var_os("HH_MEM_WORKER_FP") {
                let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
                unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut ru) };
                // (One write: the clones append to the same file.)
                let line = format!(
                    "pid {} job {} phys_footprint {} maxrss {} user {:.3} read {:.4} thread {:.4} setup {:.4} ran {:.4} input {} gets {} get_s {:.4}\n",
                    std::process::id(),
                    job,
                    crate::rt::heap_stats::phys_footprint(),
                    ru.ru_maxrss,
                    user,
                    t_read.as_secs_f64(),
                    t_thread.as_secs_f64(),
                    JOB_SETUP_NANOS.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e9,
                    t_ran.as_secs_f64(),
                    input_len,
                    crate::hh_shared::GET_COUNT.load(std::sync::atomic::Ordering::Relaxed),
                    crate::hh_shared::GET_NANOS.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e9,
                );
                if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(out) {
                    let _ = f.write_all(line.as_bytes());
                }
            }
            match write_frame(outfd, &encode(&Response::Output(output, instructions, cycles, user, sys))) {
                Ok(()) => JobOutcome::Success,
                Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => {
                    // This happens in the expected abrupt shutdown path of
                    // hh_server: the controller process shuts down.
                    crate::hh_logger::log("Worker got EPIPE due to server shutdown");
                    JobOutcome::ControllerHasDied
                }
                Err(_) => JobOutcome::ControllerHasDied,
            }
        }
        Err(panic) if panic.is::<crate::worker_cancel::WorkerShouldExit>() => JobOutcome::WorkerCancelled,
        Err(panic) => {
            let what = panic_message(&panic);
            let code = match what.as_str() {
                "Shared_mem.Hash_table_full" => crate::exit_status::exit_code(&crate::exit_status::T::HashTableFull),
                "Shared_mem.Heap_full" => crate::exit_status::exit_code(&crate::exit_status::T::HeapFull),
                _ => {
                    crate::hh_logger::log(&format!("WORKER_EXCEPTION {}", what));
                    // (`Exit_status.Type_error`, exit code 2, as the OCaml.)
                    crate::exit_status::exit_code(&crate::exit_status::T::TypeError)
                }
            };
            JobOutcome::Error(code as i32)
        }
    }
}

/// `process_job_and_exit ic oc`
fn process_job_and_exit(infd: RawFd, outfd: RawFd) -> ! {
    match read_and_process_job_fds(infd, outfd) {
        JobOutcome::Success => exit_now(0),
        JobOutcome::Error(code) => exit_now(code),
        JobOutcome::WorkerCancelled => {
            on_clone_cancelled(outfd);
            exit_now(0)
        }
        JobOutcome::ControllerHasDied => exit_now(CONTROLLER_HAS_DIED_CODE),
    }
}

/// The clone's exit: no destructors, no atexit (the clone shares nothing to
/// flush with its parent but its standard streams, flushed here).
fn exit_now(code: i32) -> ! {
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
    unsafe { libc::_exit(code) }
}

/// `maybe_send_status_to_controller fd status`
fn maybe_send_status_to_controller(fd: Option<RawFd>, status: ProcessStatus) {
    match (fd, status) {
        (None, _) => {}
        (Some(_), ProcessStatus::WExited(0)) => {}
        // Since the controller died we'd get an error writing to its fd; so
        // we simply do not do anything.
        (Some(_), ProcessStatus::WExited(CONTROLLER_HAS_DIED_CODE)) => {}
        (Some(fd), status) => {
            let _ = write_frame(fd, &encode(&SubprocessTerminated(status)));
        }
    }
}

/// `Sys_utils.waitpid_non_intr [] pid`
pub fn waitpid_non_intr(pid: libc::pid_t, flags: libc::c_int) -> Option<(libc::pid_t, ProcessStatus)> {
    loop {
        let mut status = 0;
        let r = unsafe { libc::waitpid(pid, &mut status, flags) };
        if r < 0 {
            if std::io::Error::last_os_error().raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            return None;
        }
        if r == 0 {
            return Some((0, ProcessStatus::WExited(0)));
        }
        let s = if libc::WIFEXITED(status) {
            ProcessStatus::WExited(libc::WEXITSTATUS(status))
        } else if libc::WIFSIGNALED(status) {
            ProcessStatus::WSignaled(libc::WTERMSIG(status))
        } else {
            ProcessStatus::WStopped(libc::WSTOPSIG(status))
        };
        return Some((r, s));
    }
}

/// `unix_worker_main restore (state, controller_fd) (ic, oc)`: waits for a
/// job, forks a clone for it, waits for the clone, and so on until the
/// controller closes the pipe.
fn unix_worker_main(params: WorkerParams, (infd, outfd): (RawFd, RawFd)) -> ! {
    // `restore state`
    crate::server_global_state::restore(&params.state, params.worker_id);
    if let Err(e) = crate::hh_shared::connect(&params.heap_handle) {
        panic!("Shared_mem.connect: {}", e)
    }
    crate::ctx::use_shared_memory_stores(true);
    crate::worker_jobs::set_worker_id(params.worker_id);
    crate::worker_cancel::set_in_worker_process();
    loop {
        // Wait for an incoming job: is there something to read? But we
        // don't read it yet. It will be read by the forked clone.
        let mut pfd = libc::pollfd {
            fd: infd,
            events: libc::POLLIN,
            revents: 0,
        };
        let r = unsafe { libc::poll(&mut pfd, 1, -1) };
        if r < 0 {
            if std::io::Error::last_os_error().raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            exit_now(0)
        }
        if pfd.revents & libc::POLLIN == 0 {
            // (Hung up with nothing to read: the controller is gone.)
            exit_now(0)
        }
        // We fork a clone process for every incoming request and we let it
        // exit after one request. This is the quickest GC.
        let pid = unsafe { libc::fork() };
        if pid < 0 {
            panic!("fork: {}", std::io::Error::last_os_error())
        }
        if pid == 0 {
            process_job_and_exit(infd, outfd)
        }
        // Wait for the clone process termination...
        let status = match waitpid_non_intr(pid, 0) {
            Some((_, status)) => status,
            None => ProcessStatus::WExited(2),
        };
        maybe_send_status_to_controller(params.controller_fd, status);
        match status {
            ProcessStatus::WExited(0) => {}
            ProcessStatus::WExited(CONTROLLER_HAS_DIED_CODE) => {
                // The controller has died, we can stop working.
                exit_now(0)
            }
            ProcessStatus::WExited(code) => {
                println!("Worker exited (code: {})", code);
                exit_now(code)
            }
            ProcessStatus::WSignaled(x) => {
                println!("Worker interrupted with signal: {}", x);
                exit_now(2)
            }
            ProcessStatus::WStopped(x) => {
                println!("Worker stopped with signal: {}", x);
                exit_now(3)
            }
        }
    }
}

/// The workers' entry point (`Worker_controller_entry_point.register`'s
/// `worker_main`), registered with `crate::daemon`.
pub fn worker_main(param: &[u8], channels: (RawFd, RawFd)) {
    let params: WorkerParams = crate::daemon::decode_param(param);
    unix_worker_main(params, channels)
}

/// The message of a panic payload.
pub fn panic_message(panic: &Box<dyn std::any::Any + Send>) -> String {
    panic
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "unknown panic".to_string())
}

/// At the start of `hh_server` and `hh` (before any thread is made: a worker
/// forks): in a process spawned as a worker, runs the worker (and exits).
pub fn run_if_worker() {
    if std::env::var("HH_SERVER_DAEMON").as_deref() == Ok(ENTRY) {
        if !crate::daemon::is_registered(ENTRY) {
            crate::daemon::register_entry_point(ENTRY, worker_main);
        }
        crate::daemon::check_entry_point();
    }
}
