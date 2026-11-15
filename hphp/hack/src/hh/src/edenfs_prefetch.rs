// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/edenfs_prefetch/edenfs_prefetch.ml`. See `hh/PORTING.md`.
//!
//! The `Process` functions it uses (`exec`, `is_ready`,
//! `read_and_wait_pid ~timeout:0`, `failure_msg`, `terminate`) have no Rust
//! module: the part of them that a prefetch reaches is in [`process`] below,
//! over `std::process::Child`. As in OCaml, the output of the process is
//! only read (without blocking) when the prefetch is cleaned up.
//!
//! The exceptions that OCaml catches here (`attempt_cleanup`,
//! `with_prefetch`'s launch handler, `write_pattern_file`'s handler) are the
//! `Err(String)` of the functions, the string being what `Exn.to_string`
//! prints for them.

use std::cell::Cell;
use std::io::Write;
use std::sync::Arc;
use std::sync::Mutex;

use crate::exit;
use crate::hh_logger;
use crate::path;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::rt::ocaml_unix;
use crate::sys_utils::SysError;
use crate::telemetry;

/// [relpath:] is relative to Sapling's [--cwd], which we set to the Hack root,
/// so we can pass the file's root-relative suffix directly.
pub fn file_pattern(file: &RelativePath) -> String {
    format!("relpath:{}", relative_path::suffix(file))
}

/// What a prefetch needs of `Process` and `Process_types`.
mod process {
    use std::io::Read;
    use std::os::fd::AsRawFd;
    use std::process::Child;
    use std::process::ChildStderr;
    use std::process::ChildStdin;
    use std::process::ChildStdout;
    use std::process::ExitStatus;

    use crate::rt::ocaml_unix;

    /// `Process_types.lifecycle`
    enum Lifecycle {
        LifecycleRunning(Child),
        LifecycleExited(ExitStatus),
    }

    /// `Process_types.t`
    pub struct T {
        pid: i32,
        lifecycle: Lifecycle,
        stdin_fd: Option<ChildStdin>,
        stdout_fd: Option<ChildStdout>,
        stderr_fd: Option<ChildStderr>,
        acc: Vec<u8>,
        acc_err: Vec<u8>,
    }

    /// `Process_types.failure`, the cases a prefetch can see.
    pub enum Failure {
        AbnormalExit {
            stdout: String,
            stderr: String,
        },
        /// (What `Poll_exn` carries is the error of the read or the wait.)
        PollExn(String),
    }

    /// `Process.failure_msg`
    pub fn failure_msg(failure: &Failure) -> String {
        match failure {
            Failure::AbnormalExit { stdout, stderr } => format!(
                "Process exited abnormally. stdout:\n{}\nstderr:\n{}\n",
                stdout, stderr
            ),
            Failure::PollExn(flags) => format!(
                "Exception during `poll` syscall. Got error flags: {}",
                flags
            ),
        }
    }

    /// `Process.exec prog args`; the error is the `Unix_error` that
    /// `Unix.create_process` raises.
    pub fn exec(prog: &str, args: &[String]) -> Result<T, String> {
        let mut child = std::process::Command::new(prog)
            .args(args)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .map_err(|e| ocaml_unix::unix_error_to_string(&e, "create_process", prog))?;
        let stdout_fd = child.stdout.take();
        let stderr_fd = child.stderr.take();
        // `consume` polls before it reads: never block on the pipes.
        for fd in [
            stdout_fd.as_ref().map(|f| f.as_raw_fd()),
            stderr_fd.as_ref().map(|f| f.as_raw_fd()),
        ]
        .into_iter()
        .flatten()
        {
            // SAFETY: `fcntl` on a descriptor this process owns.
            unsafe {
                let flags = libc::fcntl(fd, libc::F_GETFL);
                libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK);
            }
        }
        Ok(T {
            pid: child.id() as i32,
            stdin_fd: child.stdin.take(),
            lifecycle: Lifecycle::LifecycleRunning(child),
            stdout_fd,
            stderr_fd,
            acc: vec![],
            acc_err: vec![],
        })
    }

    /// `maybe_consume fd_ref acc` (with a timeout of 0): reads what is
    /// there; at the end of the file, the descriptor is closed.
    fn maybe_consume(fd_ref: &mut Option<impl Read>, acc: &mut Vec<u8>) -> Result<(), String> {
        if let Some(fd) = fd_ref {
            let mut buffer = [0u8; 65536];
            loop {
                match fd.read(&mut buffer) {
                    Ok(0) => {
                        *fd_ref = None;
                        return Ok(());
                    }
                    Ok(n) => acc.extend_from_slice(&buffer[..n]),
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => return Ok(()),
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                    Err(e) => return Err(ocaml_unix::unix_error_to_string(&e, "read", "")),
                }
            }
        }
        Ok(())
    }

    /// `read_and_wait_pid_nonblocking`
    fn read_and_wait_pid_nonblocking(process: &mut T) -> Result<(), String> {
        if let Lifecycle::LifecycleRunning(child) = &mut process.lifecycle {
            maybe_consume(&mut process.stdout_fd, &mut process.acc)?;
            maybe_consume(&mut process.stderr_fd, &mut process.acc_err)?;
            match child.try_wait() {
                Ok(None) => {}
                Ok(Some(status)) => {
                    process.lifecycle = Lifecycle::LifecycleExited(status);
                    // Process has exited. Non-blockingly consume residual output.
                    maybe_consume(&mut process.stdout_fd, &mut process.acc)?;
                    maybe_consume(&mut process.stderr_fd, &mut process.acc_err)?;
                }
                Err(e) => return Err(ocaml_unix::unix_error_to_string(&e, "waitpid", "")),
            }
        }
        Ok(())
    }

    /// Returns true if read_and_close_pid would be nonblocking.
    pub fn is_ready(process: &mut T) -> Result<bool, String> {
        read_and_wait_pid_nonblocking(process)?;
        Ok(match process.lifecycle {
            Lifecycle::LifecycleRunning(_) => false,
            Lifecycle::LifecycleExited(_) => true,
        })
    }

    /// `read_and_wait_pid ~timeout:0` of a process that [`is_ready`] found
    /// exited: `Ok` is its stderr (`result.Process_types.stderr`).
    pub fn read_and_wait_pid_exited(process: &mut T) -> Result<String, Failure> {
        read_and_wait_pid_nonblocking(process).map_err(Failure::PollExn)?;
        let stdout = String::from_utf8_lossy(&process.acc).into_owned();
        let stderr = String::from_utf8_lossy(&process.acc_err).into_owned();
        match &process.lifecycle {
            Lifecycle::LifecycleExited(status) if status.success() => Ok(stderr),
            _ => Err(Failure::AbnormalExit { stdout, stderr }),
        }
    }

    fn send_signal(pid: i32, signal: i32) -> Result<(), String> {
        match ocaml_unix::kill(pid as isize, signal) {
            Ok(()) => Ok(()),
            // ESRCH means no process has this PID, so there is nothing to signal.
            // Other errors, such as insufficient permissions, still propagate.
            Err(e) if e.raw_os_error() == Some(libc::ESRCH) => Ok(()),
            Err(e) => Err(ocaml_unix::unix_error_to_string(&e, "kill", "")),
        }
    }

    /// Once a child has been reaped, its PID may be reused. The lifecycle
    /// check and update prevent repeated cleanup from signaling that PID.
    fn running_pid(process: &mut T) -> Result<Option<i32>, String> {
        match &mut process.lifecycle {
            Lifecycle::LifecycleExited(_) => Ok(None),
            Lifecycle::LifecycleRunning(child) => match child.try_wait() {
                Ok(None) => Ok(Some(process.pid)),
                Ok(Some(status)) => {
                    process.lifecycle = Lifecycle::LifecycleExited(status);
                    Ok(None)
                }
                Err(e) => Err(ocaml_unix::unix_error_to_string(&e, "waitpid", "")),
            },
        }
    }

    /// `Process.terminate ~graceful_signal ~grace_period process`
    pub fn terminate(
        graceful_signal: Option<i32>,
        grace_period: f64,
        process: &mut T,
    ) -> Result<(), String> {
        let sleep_seconds_per_retry = 0.04;
        let graceful_shutdown = |process: &mut T| -> Result<(), String> {
            if let (Some(signal), Some(pid)) = (graceful_signal, running_pid(process)?) {
                send_signal(pid, signal)?;
                let deadline = ocaml_unix::gettimeofday() + grace_period;
                while running_pid(process)?.is_some() && ocaml_unix::gettimeofday() < deadline {
                    std::thread::sleep(std::time::Duration::from_secs_f64(sleep_seconds_per_retry));
                }
            }
            Ok(())
        };
        let kill_and_reap = |process: &mut T| -> Result<(), String> {
            if let Some(pid) = running_pid(process)? {
                send_signal(pid, libc::SIGKILL)?;
                if let Lifecycle::LifecycleRunning(child) = &mut process.lifecycle {
                    let status = child
                        .wait()
                        .map_err(|e| ocaml_unix::unix_error_to_string(&e, "waitpid", ""))?;
                    process.lifecycle = Lifecycle::LifecycleExited(status);
                }
            }
            Ok(())
        };
        // `Utils.try_all`: every step runs; the first failure is raised.
        let mut first = None;
        for step in [
            &graceful_shutdown as &dyn Fn(&mut T) -> Result<(), String>,
            &kill_and_reap,
            &|p: &mut T| {
                p.stdin_fd = None;
                Ok(())
            },
            &|p: &mut T| {
                p.stdout_fd = None;
                Ok(())
            },
            &|p: &mut T| {
                p.stderr_fd = None;
                Ok(())
            },
        ] {
            if let Err(e) = step(process) {
                first.get_or_insert(e);
            }
        }
        match first {
            None => Ok(()),
            Some(e) => Err(e),
        }
    }
}

struct Prefetch {
    process: Mutex<process::T>,
    pattern_file: String,
    start_time: f64,
    count: isize,
}

enum ProcessStatus {
    Running,
    Finished {
        outcome: String,
        duration: Option<f64>,
    },
}

static ACTIVE_PREFETCHES: Mutex<Vec<Arc<Prefetch>>> = Mutex::new(vec![]);

fn active_prefetches() -> std::sync::MutexGuard<'static, Vec<Arc<Prefetch>>> {
    ACTIVE_PREFETCHES.lock().unwrap_or_else(|e| e.into_inner())
}

fn log_failure(operation: &str, message: &str) {
    hh_logger::log(&format!(
        "EdenFS prefetch {} failed: {}",
        operation, message
    ))
}

fn attempt_cleanup<A>(
    cleanup_failed_ref: &Cell<bool>,
    f: impl FnOnce() -> Result<A, String>,
) -> Option<A> {
    match f() {
        Ok(a) => Some(a),
        Err(exn) => {
            cleanup_failed_ref.set(true);
            log_failure("cleanup", &exn);
            None
        }
    }
}

fn duration_from_stderr(stderr: &str) -> Option<f64> {
    // `String.split_lines`: on "\n", without a trailing "\r".
    stderr.lines().find_map(|line| {
        let words: Vec<&str> = line.split(' ').collect();
        match words.as_slice() {
            ["time:", "real", seconds, "secs", ..] => {
                crate::rt::ocaml_arg::float_of_string_opt(seconds)
                    .filter(|seconds| seconds.is_finite() && *seconds >= 0.0)
            }
            _ => None,
        }
    })
}

fn read_finished_status(process: &mut process::T) -> ProcessStatus {
    let (outcome, stderr) = match process::read_and_wait_pid_exited(process) {
        Ok(stderr) => ("completed", Some(stderr)),
        Err(failure) => {
            log_failure("command", &process::failure_msg(&failure));
            let stderr = match failure {
                process::Failure::AbnormalExit { stderr, .. } => Some(stderr),
                process::Failure::PollExn(_) => None,
            };
            ("command_failed", stderr)
        }
    };
    ProcessStatus::Finished {
        outcome: outcome.to_string(),
        duration: stderr.as_deref().and_then(duration_from_stderr),
    }
}

fn make_telemetry(
    count: isize,
    outcome: &str,
    cleanup_failed: bool,
    timing: Option<(f64, &str)>,
) -> telemetry::T {
    let telemetry = telemetry::create();
    let telemetry = telemetry::int_("files", count, telemetry);
    let telemetry = telemetry::string_(None, "outcome", outcome, telemetry);
    let telemetry = telemetry::bool_("cleanup_failed", cleanup_failed, telemetry);
    match timing {
        None => telemetry,
        Some((seconds, source)) => {
            let telemetry = telemetry::float_("duration_sec", seconds, telemetry);
            telemetry::string_(None, "duration_source", source, telemetry)
        }
    }
}

fn cleanup(cleanup_failed_ref: &Cell<bool>, prefetch: &Arc<Prefetch>) -> telemetry::T {
    let Prefetch {
        process,
        pattern_file,
        start_time,
        count,
    } = &**prefetch;
    let mut process = process.lock().unwrap_or_else(|e| e.into_inner());
    let status = match attempt_cleanup(cleanup_failed_ref, || process::is_ready(&mut process)) {
        Some(true) => Some(read_finished_status(&mut process)),
        Some(false) => Some(ProcessStatus::Running),
        None => None,
    };
    let outcome = match &status {
        Some(ProcessStatus::Finished { outcome, .. }) => outcome.as_str(),
        Some(ProcessStatus::Running) | None => "stopped",
    };
    let stopped_at = attempt_cleanup(cleanup_failed_ref, || {
        // `Utils.try_all`
        let steps: [Box<dyn FnOnce() -> Result<(), String> + '_>; 3] = [
            Box::new(|| process::terminate(Some(libc::SIGTERM), 1.0, &mut process)),
            Box::new(|| path::remove(pattern_file).map_err(|e| e.to_string())),
            Box::new(|| {
                active_prefetches().retain(|active| !Arc::ptr_eq(active, prefetch));
                Ok(())
            }),
        ];
        let mut first = None;
        for step in steps {
            if let Err(e) = step() {
                first.get_or_insert(e);
            }
        }
        match first {
            None => Ok(()),
            Some(e) => Err(e),
        }
    })
    .map(|()| ocaml_unix::gettimeofday());
    let timing = match &status {
        Some(ProcessStatus::Running) => {
            stopped_at.map(|end_time| (end_time - start_time, "controller"))
        }
        Some(ProcessStatus::Finished { duration, .. }) => duration.map(|seconds| (seconds, "sl")),
        None => None,
    };
    let duration_message = match timing {
        None => String::new(),
        Some((seconds, _)) => format!("duration={:.3}s ", seconds),
    };
    hh_logger::log(&format!(
        "EdenFS prefetch: files={} {}outcome={} cleanup_failed={}",
        count,
        duration_message,
        outcome,
        cleanup_failed_ref.get()
    ));
    make_telemetry(*count, outcome, cleanup_failed_ref.get(), timing)
}

// Exit.exit and Stdlib.exit do not unwind try_finally, e.g. during SIGUSR2
// shutdown. Exit hooks clean up prefetch processes on those paths.
fn cleanup_on_exit() {
    let prefetches = active_prefetches().clone();
    for prefetch in &prefetches {
        let _ = cleanup(&Cell::new(false), prefetch);
    }
}

static EXIT_HOOKS_REGISTERED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

extern "C" fn cleanup_on_exit_c() {
    cleanup_on_exit()
}

fn register_exit_hooks() {
    use std::sync::atomic::Ordering;
    if !EXIT_HOOKS_REGISTERED.swap(true, Ordering::SeqCst) {
        exit::add_hook_upon_clean_exit(|_| cleanup_on_exit());
        // `Stdlib.at_exit cleanup_on_exit`
        // SAFETY: registers a function that takes no arguments.
        unsafe {
            libc::atexit(cleanup_on_exit_c);
        }
    }
}

/// `Filename.get_temp_dir_name ()`
fn get_temp_dir_name() -> String {
    std::env::var("TMPDIR").unwrap_or_else(|_| "/tmp".to_string())
}

fn write_pattern_file(
    cleanup_failed_ref: &Cell<bool>,
    files: &relative_path::set::T,
) -> Result<String, String> {
    let temp_dir = get_temp_dir_name();
    let (pattern_file, channel) =
        crate::rt::ocaml_filename::open_temp_file(&temp_dir, "hh_edenfs_prefetch_", ".patterns")
            .map_err(|e| SysError::of_io_error(&temp_dir, &e).to_string())?;
    let mut channel = std::io::BufWriter::new(channel);
    let write = |channel: &mut std::io::BufWriter<std::fs::File>| -> std::io::Result<()> {
        for file in files {
            channel.write_all(file_pattern(file).as_bytes())?;
            channel.write_all(b"\n")?;
        }
        channel.flush()
    };
    match write(&mut channel) {
        Ok(()) => {
            drop(channel);
            Ok(pattern_file)
        }
        Err(e) => {
            let exn = SysError::of_io_error(&pattern_file, &e).to_string();
            let _: Option<()> = attempt_cleanup(cleanup_failed_ref, || {
                drop(channel);
                path::remove(&pattern_file).map_err(|e| e.to_string())
            });
            Err(exn)
        }
    }
}

fn start(
    root: &path::T,
    files: &relative_path::set::T,
    workers: isize,
    cleanup_failed_ref: &Cell<bool>,
) -> Result<Option<Arc<Prefetch>>, String> {
    if files.is_empty() {
        Ok(None)
    } else {
        let count = files.len() as isize;
        let pattern_file = write_pattern_file(cleanup_failed_ref, files)?;
        register_exit_hooks();
        hh_logger::log(&format!("EdenFS prefetch: starting files={}", count));
        // [sl prefetch -r .] caches file contents at the current commit. In theory, we could filter
        // out locally modified files (no point to fetch their state as of the commit), but that would
        // just add too much complexity here.
        let start_time = ocaml_unix::gettimeofday();
        let process = match process::exec(
            // `Exec_command.Sl`
            "sl",
            &[
                "--cwd".to_string(),
                path::to_string(root),
                "--quiet".to_string(),
                "--time".to_string(),
                "--config".to_string(),
                format!("filewalk.concurrent-fetches={}", workers),
                "prefetch".to_string(),
                "-r".to_string(),
                ".".to_string(),
                "--include".to_string(),
                format!("listfile:{}", pattern_file),
            ],
        ) {
            Ok(process) => process,
            Err(exn) => {
                let _: Option<()> = attempt_cleanup(cleanup_failed_ref, || {
                    path::remove(&pattern_file).map_err(|e| e.to_string())
                });
                return Err(exn);
            }
        };
        let prefetch = Arc::new(Prefetch {
            process: Mutex::new(process),
            pattern_file,
            start_time,
            count,
        });
        active_prefetches().insert(0, Arc::clone(&prefetch));
        Ok(Some(prefetch))
    }
}

/// Start prefetching [files] with Sapling, then run [f] without waiting for
/// prefetch to finish. Stop and reap the prefetch process when [f] returns,
/// raises, or exits the server.
/// Prefetch failures are logged and do not change the result of [f].
///
/// Returns [f]'s result and prefetch telemetry, including duration when
/// available.
pub fn with_prefetch<A>(
    root: &path::T,
    files: &relative_path::set::T,
    workers: isize,
    f: impl FnOnce() -> A,
) -> (A, telemetry::T) {
    let telemetry = std::cell::RefCell::new(telemetry::create());
    let cleanup_failed_ref = Cell::new(false);
    let prefetch = match start(root, files, workers, &cleanup_failed_ref) {
        Ok(prefetch) => prefetch,
        Err(exn) => {
            log_failure("launch", &exn);
            *telemetry.borrow_mut() = make_telemetry(
                files.len() as isize,
                "launch_failed",
                cleanup_failed_ref.get(),
                None,
            );
            None
        }
    };
    let result = crate::utils::try_finally(f, || {
        if let Some(prefetch) = &prefetch {
            *telemetry.borrow_mut() = cleanup(&cleanup_failed_ref, prefetch);
        }
    });
    (result, telemetry.into_inner())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn duration_of_sl_time() {
        assert_eq!(
            duration_from_stderr("fetching\ntime: real 1.25 secs (user 0.1 + sys 0.2)\n"),
            Some(1.25)
        );
        assert_eq!(duration_from_stderr("time: real -1 secs\n"), None);
        assert_eq!(duration_from_stderr("time: real nan secs\n"), None);
        assert_eq!(duration_from_stderr("time: real 2 seconds\n"), None);
        assert_eq!(duration_from_stderr(""), None);
    }

    #[test]
    fn empty_fanout_does_not_start() {
        let (result, telemetry) =
            with_prefetch(&"/".to_string(), &relative_path::set::T::new(), 4, || 42);
        assert_eq!(result, 42);
        assert_eq!(telemetry, telemetry::create());
    }
}
