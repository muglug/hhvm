// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/sys/daemon.ml` (`Daemon.spawn`, `check_entry_point`,
//! `register_entry_point`, `null_fd`, `fd_of_path`): how `hh_server -d`
//! detaches its monitor and how the monitor starts the typechecker server.
//!
//! As in OCaml, a daemon is the same executable started again
//! (`create_process exe [| exe; name |]`) with `HH_SERVER_DAEMON` naming
//! its entry point and `HH_SERVER_DAEMON_PARAM` a temporary file
//! (`/tmp/daemon_param*.bin`) holding the parameter of the entry and the
//! numbers of the two descriptors of its channels; the child removes the
//! file. OCaml marshals the parameter (with closures); here it is `bincode`
//! of its `serde` (the file is read only by the child, of the same build).
//! The entry points are registered by name; `check_entry_point`, called at
//! the start of the program, runs the one the environment names.

use std::io;
use std::os::fd::FromRawFd;
use std::os::fd::OwnedFd;
use std::os::fd::RawFd;
use std::sync::Mutex;

use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::pid_log;

/// The function of an entry point: its parameter (still encoded: see
/// [`decode_param`]) and its channels `(ic, oc)` (the descriptors of the
/// child's ends).
pub type EntryFn = fn(param: &[u8], channels: (RawFd, RawFd));

/// `Entry.entry_points`
static ENTRY_POINTS: Mutex<Vec<(String, EntryFn)>> = Mutex::new(Vec::new());

/// `Daemon.register_entry_point name f`. Fails (panics) on a name already
/// registered, as OCaml's `failwith`.
///
/// Alternate entry points must be registered at toplevel, i.e. every call to
/// `Daemon.register_entry_point` must have been evaluated when
/// `Daemon.check_entry_point` is called at the beginning of
/// `Server_main.start`.
pub fn register_entry_point(name: &str, f: EntryFn) -> String {
    let mut entries = ENTRY_POINTS.lock().unwrap_or_else(|e| e.into_inner());
    if entries.iter().any(|(n, _)| n == name) {
        panic!(
            "Daemon.register_entry_point: duplicate entry point {}.",
            crate::rt::ocaml_printf::sprintf_s(name)
        );
    }
    entries.push((name.to_string(), f));
    name.to_string()
}

/// Whether an entry point of that name is registered.
pub fn is_registered(name: &str) -> bool {
    ENTRY_POINTS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .iter()
        .any(|(n, _)| n == name)
}

/// `Entry.find`
fn find(name: &str) -> EntryFn {
    let entries = ENTRY_POINTS.lock().unwrap_or_else(|e| e.into_inner());
    match entries.iter().find(|(n, _)| n == name) {
        Some((_, f)) => *f,
        None => panic!(
            "Unknown entry point {}",
            crate::rt::ocaml_printf::sprintf_s(name)
        ),
    }
}

/// The parameter of an entry, decoded.
pub fn decode_param<P: DeserializeOwned>(bytes: &[u8]) -> P {
    match crate::rt::protocol::wire::decode(bytes) {
        Ok(p) => p,
        Err(e) => panic!("Can't find daemon parameters: {}", e),
    }
}

/// `channel_mode`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChannelMode {
    Pipe,
    Socket,
}

/// `('in_, 'out) handle`: the parent's ends of the channels and the pid.
#[derive(Debug)]
pub struct Handle {
    /// `(ic, oc)`: the descriptors of the parent's ends (close-on-exec).
    pub channels: (RawFd, RawFd),
    pub pid: i32,
}

/// Close the typed channels associated to a 'spawned' child. (Here the
/// channels are file descriptors: `Unix.close`, ignoring errors.)
pub fn close(fd: RawFd) {
    // SAFETY: closing a descriptor number we own.
    unsafe {
        libc::close(fd);
    }
}

/// `fd_of_path path`: opens (creating, truncating) `path` read-write, mode
/// 0o666 under umask 0o111, making its directory. Not close-on-exec.
pub fn fd_of_path(path: &str) -> io::Result<RawFd> {
    use std::os::fd::IntoRawFd;
    let _ = crate::sys_utils::mkdir_p(&crate::rt::ocaml_filename::dirname(path));
    let f = crate::rt::ocaml_unix::openfile_with_umask(
        path,
        &[
            crate::rt::ocaml_unix::OpenFlag::ORdwr,
            crate::rt::ocaml_unix::OpenFlag::OCreat,
            crate::rt::ocaml_unix::OpenFlag::OTrunc,
        ],
        0o666,
        0o111,
    )?;
    let fd = f.into_raw_fd();
    crate::rt::ocaml_unix::clear_close_on_exec(fd);
    Ok(fd)
}

/// `null_fd ()`
pub fn null_fd() -> io::Result<RawFd> {
    fd_of_path("/dev/null")
}

/// `setup_channels channel_mode`: `((parent_in, child_out), (child_in,
/// parent_out))`, the parent's ends close-on-exec.
fn setup_channels(channel_mode: ChannelMode) -> io::Result<((RawFd, RawFd), (RawFd, RawFd))> {
    let mk = || match channel_mode {
        ChannelMode::Pipe => crate::rt::ocaml_unix::pipe(),
        ChannelMode::Socket => crate::rt::ocaml_unix::socketpair(),
    };
    let (parent_in, child_out) = mk()?;
    let (child_in, parent_out) = mk()?;
    crate::rt::ocaml_unix::set_close_on_exec(parent_in);
    crate::rt::ocaml_unix::set_close_on_exec(parent_out);
    Ok(((parent_in, child_out), (child_in, parent_out)))
}

/// What the parameter file holds: `(ic, oc, param)`.
#[derive(serde::Serialize, serde::Deserialize)]
struct Context {
    in_handle: RawFd,
    out_handle: RawFd,
    param: Vec<u8>,
}

/// `Daemon.spawn ?channel_mode ?name (stdin, stdout, stderr) entry param`.
/// `stdin`, `stdout`, `stderr` are descriptors; those other than 0, 1, 2
/// are closed once the child has them.
pub fn spawn<P: Serialize>(
    channel_mode: ChannelMode,
    name: Option<&str>,
    (stdin, stdout, stderr): (RawFd, RawFd, RawFd),
    entry: &str,
    param: &P,
) -> io::Result<Handle> {
    use std::io::Write;
    use std::os::unix::process::CommandExt;
    let ((parent_in, child_out), (child_in, parent_out)) = setup_channels(channel_mode)?;
    let name = name.unwrap_or(entry);
    // `Entry.set_context entry ~name param (child_in, child_out)`
    crate::rt::ocaml_unix::putenv("HH_SERVER_DAEMON", entry);
    let (file, mut param_oc) = crate::rt::ocaml_filename::open_temp_file(crate::sys_utils::TEMP_DIR_NAME, "daemon_param", ".bin")?;
    let context = Context {
        in_handle: child_in,
        out_handle: child_out,
        param: crate::rt::protocol::wire::encode(param),
    };
    param_oc.write_all(&crate::rt::protocol::wire::encode(&context))?;
    drop(param_oc);
    crate::rt::ocaml_unix::putenv("HH_SERVER_DAEMON_PARAM", &file);
    let exe = crate::sys_utils::executable_path();
    let stdio = |fd: RawFd, std: RawFd| -> io::Result<std::process::Stdio> {
        if fd == std {
            Ok(std::process::Stdio::inherit())
        } else {
            // SAFETY: `dup` of a descriptor the caller gave; the copy is
            // owned by the `Stdio`.
            let copy = unsafe { libc::dup(fd) };
            if copy < 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(std::process::Stdio::from(unsafe { OwnedFd::from_raw_fd(copy) }))
        }
    };
    let res = std::process::Command::new(&exe)
        .arg0(&exe)
        .arg(name)
        .stdin(stdio(stdin, 0)?)
        .stdout(stdio(stdout, 1)?)
        .stderr(stdio(stderr, 2)?)
        .spawn();
    // `Entry.clear_context ()`
    crate::rt::ocaml_unix::putenv("HH_SERVER_DAEMON", "");
    crate::rt::ocaml_unix::putenv("HH_SERVER_DAEMON_PARAM", "");
    close(child_in);
    close(child_out);
    if stdin != 0 {
        close(stdin);
    }
    if stdout != 1 {
        close(stdout);
    }
    if stderr != 2 && stderr != stdout {
        close(stderr);
    }
    let child = match res {
        Ok(child) => child,
        Err(e) => {
            let _ = std::fs::remove_file(&file);
            close(parent_in);
            close(parent_out);
            return Err(e);
        }
    };
    let pid = child.id() as i32;
    // The child is waited for by `waitpid` (the monitor's `wait_pid`), not
    // through `Child`.
    std::mem::forget(child);
    pid_log::log(Some(entry), Some(true), pid as isize);
    Ok(Handle {
        channels: (parent_in, parent_out),
        pid,
    })
}

/// `Daemon.check_entry_point ()`: in a process started by [`spawn`], runs
/// its entry point (and exits); otherwise returns.
///
/// In order for the Daemon infrastructure to work, the beginning of your
/// program (or very close to the beginning) must start with a call to
/// check_entry_point.
///
/// Details: Daemon.spawn essentially does a fork then exec of the currently
/// running program. Thus, the child process will just end up running the
/// exact same program as the parent if you forgot to start with a
/// check_entry_point. The parent process sees this as a NOOP when its
/// program starts, but a child process (from Daemon.spawn) will use this as
/// a GOTO to its entry point.
pub fn check_entry_point() {
    let entry = match std::env::var("HH_SERVER_DAEMON") {
        Ok(entry) if !entry.is_empty() => entry,
        _ => return,
    };
    let context = (|| -> Result<Context, String> {
        let file = std::env::var("HH_SERVER_DAEMON_PARAM").map_err(|e| e.to_string())?;
        if file.is_empty() {
            return Err("Not_found".to_string());
        }
        let bytes = std::fs::read(&file).map_err(|e| e.to_string())?;
        let _ = std::fs::remove_file(&file);
        crate::rt::protocol::wire::decode::<Context>(&bytes)
    })();
    let context = match context {
        Ok(context) => context,
        // `failwith ("Can't find daemon parameters: " ^ ...)`, which
        // `Monitor_start.start` turns into `Uncaught_exception`.
        Err(e) => crate::exit::exit(
            None,
            None,
            None,
            None,
            crate::exit_status::T::UncaughtException(crate::exception::wrap(Failure(format!(
                "Can't find daemon parameters: {}",
                e
            )))),
        ),
    };
    // `Entry.clear_context ()`
    crate::rt::ocaml_unix::putenv("HH_SERVER_DAEMON", "");
    crate::rt::ocaml_unix::putenv("HH_SERVER_DAEMON_PARAM", "");
    exec(&entry, &context.param, context.in_handle, context.out_handle)
}

/// `Failure msg`, as `Printexc.to_string` shows it.
struct Failure(String);

impl std::fmt::Debug for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failure({})", crate::rt::ocaml_printf::sprintf_s(&self.0))
    }
}

/// `exec entry param ic oc`
fn exec(entry: &str, param: &[u8], ic: RawFd, oc: RawFd) -> ! {
    crate::rt::ocaml_unix::set_close_on_exec(ic);
    crate::rt::ocaml_unix::set_close_on_exec(oc);
    let f = find(entry);
    match std::panic::catch_unwind(|| f(param, (ic, oc))) {
        Ok(()) => std::process::exit(0),
        Err(e) => {
            let msg = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "panic".to_string());
            eprintln!("{}", msg);
            std::process::exit(2)
        }
    }
}
