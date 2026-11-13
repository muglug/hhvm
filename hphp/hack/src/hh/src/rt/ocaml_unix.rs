// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The parts of OCaml's `Unix` library whose exact semantics the ported
//! modules rely on, and that `std` does not give:
//!
//! - [`lockf`]: `Unix.lockf`, which OCaml implements with POSIX record locks
//!   (`fcntl` `F_SETLK`/`F_SETLKW`/`F_GETLK`), not `flock`. The lock files
//!   under `/tmp/hh_server` keep these semantics: they are per process, a
//!   process never conflicts with itself, and closing *any* descriptor of the
//!   file releases the process's locks on it.
//! - [`kill`], [`getpid`], [`gettimeofday`].
//! - [`rev_convert_signal_number`]: OCaml's numbering of signals (`Sys.sigkill`
//!   is `-7`...), which `Unix.WSIGNALED` carries.
//! - [`unix_error_to_string`]: how an uncaught `Unix.Unix_error` prints
//!   (`Unix.Unix_error(Unix.ENOENT, "mkdir", "/x")`).
//! - [`openfile_with_umask`] and [`mkdir_with_umask`]: what OCaml does with
//!   `Sys_utils.with_umask umask (fun () -> Unix.openfile ... / Unix.mkdir
//!   ...)`. OCaml changes the process umask around the call; this process has
//!   many threads, and a temporary umask would apply to the files they create
//!   meanwhile (and two such calls interleaving can leave the umask wrong for
//!   good). So the file or directory is created and then given the mode the
//!   OCaml umask gives (`perm land (lnot umask)`), and the process umask is
//!   never changed. A file that already existed keeps its mode, as in OCaml.

use std::fs::File;
use std::fs::OpenOptions;
use std::fs::Permissions;
use std::io;
use std::os::fd::RawFd;
use std::os::unix::fs::DirBuilderExt;
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::fs::PermissionsExt;

use crate::rt::ocaml_printf::sprintf_S;

/// `Unix.gettimeofday ()`
pub fn gettimeofday() -> f64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_secs_f64(),
        Err(e) => -e.duration().as_secs_f64(),
    }
}

/// `Unix.getpid ()`
pub fn getpid() -> isize {
    std::process::id() as isize
}

/// `Unix.lock_command`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LockCommand {
    /// `F_ULOCK`: unlock a region
    FUlock,
    /// `F_LOCK`: lock a region for writing, and block if already locked
    FLock,
    /// `F_TLOCK`: lock a region for writing, or fail if already locked
    FTlock,
    /// `F_TEST`: test a region for other process locks
    FTest,
    /// `F_RLOCK`: lock a region for reading, and block if already locked
    FRlock,
    /// `F_TRLOCK`: lock a region for reading, or fail if already locked
    FTrlock,
}

/// `Unix.lockf fd cmd size`: `caml_unix_lockf` of OCaml's
/// `otherlibs/unix/lockf_unix.c`. The region starts at the current position
/// of `fd` and extends `size` bytes forward (backward if negative); `0` means
/// to the end of the file. `F_TEST` fails with `EACCES` when another process
/// holds a lock on the region.
pub fn lockf(fd: RawFd, cmd: LockCommand, size: i64) -> io::Result<()> {
    // SAFETY: `flock` is plain data.
    let mut l: libc::flock = unsafe { std::mem::zeroed() };
    l.l_whence = libc::SEEK_CUR as libc::c_short;
    if size < 0 {
        l.l_start = size as libc::off_t;
        l.l_len = -size as libc::off_t;
    } else {
        l.l_start = 0;
        l.l_len = size as libc::off_t;
    }
    // SAFETY: `fcntl` with a lock command reads (and for `F_GETLK` writes)
    // the `flock` we pass, which lives through the call.
    let ret = unsafe {
        match cmd {
            LockCommand::FUlock => {
                l.l_type = libc::F_UNLCK as libc::c_short;
                libc::fcntl(fd, libc::F_SETLK, &l)
            }
            LockCommand::FLock => {
                l.l_type = libc::F_WRLCK as libc::c_short;
                libc::fcntl(fd, libc::F_SETLKW, &l)
            }
            LockCommand::FTlock => {
                l.l_type = libc::F_WRLCK as libc::c_short;
                libc::fcntl(fd, libc::F_SETLK, &l)
            }
            LockCommand::FTest => {
                l.l_type = libc::F_WRLCK as libc::c_short;
                let ret = libc::fcntl(fd, libc::F_GETLK, &mut l);
                if ret != -1 {
                    if l.l_type == libc::F_UNLCK as libc::c_short {
                        0
                    } else {
                        return Err(io::Error::from_raw_os_error(libc::EACCES));
                    }
                } else {
                    ret
                }
            }
            LockCommand::FRlock => {
                l.l_type = libc::F_RDLCK as libc::c_short;
                libc::fcntl(fd, libc::F_SETLKW, &l)
            }
            LockCommand::FTrlock => {
                l.l_type = libc::F_RDLCK as libc::c_short;
                libc::fcntl(fd, libc::F_SETLK, &l)
            }
        }
    };
    if ret == -1 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

/// `Unix.kill pid signal`. As in OCaml (`caml_unix_kill`), the pid is
/// converted to a C `pid_t`. `signal` is a system signal number (`0` checks
/// that the process exists and may be signalled).
pub fn kill(pid: isize, signal: i32) -> io::Result<()> {
    // SAFETY: `kill` takes two integers.
    let ret = unsafe { libc::kill(pid as libc::pid_t, signal) };
    if ret == -1 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

/// `SIGPOLL`, where the system has it (`-1`, which no signal is, otherwise,
/// as in OCaml's `runtime/signals.c`).
#[cfg(any(target_os = "linux", target_os = "android"))]
const SIGPOLL: i32 = libc::SIGPOLL;
#[cfg(not(any(target_os = "linux", target_os = "android")))]
const SIGPOLL: i32 = -1;

/// `posix_signals` of OCaml's `runtime/signals.c`: the signals OCaml numbers
/// `-1`, `-2`, ... (`Sys.sigabrt` is `-1`).
const POSIX_SIGNALS: [i32; 28] = [
    libc::SIGABRT,
    libc::SIGALRM,
    libc::SIGFPE,
    libc::SIGHUP,
    libc::SIGILL,
    libc::SIGINT,
    libc::SIGKILL,
    libc::SIGPIPE,
    libc::SIGQUIT,
    libc::SIGSEGV,
    libc::SIGTERM,
    libc::SIGUSR1,
    libc::SIGUSR2,
    libc::SIGCHLD,
    libc::SIGCONT,
    libc::SIGSTOP,
    libc::SIGTSTP,
    libc::SIGTTIN,
    libc::SIGTTOU,
    libc::SIGVTALRM,
    libc::SIGPROF,
    libc::SIGBUS,
    SIGPOLL,
    libc::SIGSYS,
    libc::SIGTRAP,
    libc::SIGURG,
    libc::SIGXCPU,
    libc::SIGXFSZ,
];

/// `caml_rev_convert_signal_number`: the OCaml number of a system signal
/// (what `Unix.WSIGNALED` and `Unix.WSTOPPED` carry).
pub fn rev_convert_signal_number(signo: i32) -> isize {
    match POSIX_SIGNALS.iter().position(|s| *s == signo) {
        Some(i) => -(i as isize) - 1,
        None => signo as isize,
    }
}

/// The name of the `Unix.error` constructor for an OS error, as the printer
/// that `Unix` registers shows it: `ENOENT`, ..., or `EUNKNOWNERR <n>`.
pub fn error_name(err: &io::Error) -> String {
    let code = match err.raw_os_error() {
        Some(code) => code,
        None => return format!("EUNKNOWNERR {}", 0),
    };
    // `caml_unix_error_of_code`: `ENOTSUP` is reported as `EOPNOTSUPP` where
    // the two differ (macOS); on Linux they are the same number.
    let code = if code == libc::ENOTSUP { libc::EOPNOTSUPP } else { code };
    // In the order of `error_table` in `otherlibs/unix/unixsupport_unix.c`
    // (so `EAGAIN` wins over an equal `EWOULDBLOCK`).
    let table: &[(i32, &str)] = &[
        (libc::E2BIG, "E2BIG"),
        (libc::EACCES, "EACCES"),
        (libc::EAGAIN, "EAGAIN"),
        (libc::EBADF, "EBADF"),
        (libc::EBUSY, "EBUSY"),
        (libc::ECHILD, "ECHILD"),
        (libc::EDEADLK, "EDEADLK"),
        (libc::EDOM, "EDOM"),
        (libc::EEXIST, "EEXIST"),
        (libc::EFAULT, "EFAULT"),
        (libc::EFBIG, "EFBIG"),
        (libc::EINTR, "EINTR"),
        (libc::EINVAL, "EINVAL"),
        (libc::EIO, "EIO"),
        (libc::EISDIR, "EISDIR"),
        (libc::EMFILE, "EMFILE"),
        (libc::EMLINK, "EMLINK"),
        (libc::ENAMETOOLONG, "ENAMETOOLONG"),
        (libc::ENFILE, "ENFILE"),
        (libc::ENODEV, "ENODEV"),
        (libc::ENOENT, "ENOENT"),
        (libc::ENOEXEC, "ENOEXEC"),
        (libc::ENOLCK, "ENOLCK"),
        (libc::ENOMEM, "ENOMEM"),
        (libc::ENOSPC, "ENOSPC"),
        (libc::ENOSYS, "ENOSYS"),
        (libc::ENOTDIR, "ENOTDIR"),
        (libc::ENOTEMPTY, "ENOTEMPTY"),
        (libc::ENOTTY, "ENOTTY"),
        (libc::ENXIO, "ENXIO"),
        (libc::EPERM, "EPERM"),
        (libc::EPIPE, "EPIPE"),
        (libc::ERANGE, "ERANGE"),
        (libc::EROFS, "EROFS"),
        (libc::ESPIPE, "ESPIPE"),
        (libc::ESRCH, "ESRCH"),
        (libc::EXDEV, "EXDEV"),
        (libc::EWOULDBLOCK, "EWOULDBLOCK"),
        (libc::EINPROGRESS, "EINPROGRESS"),
        (libc::EALREADY, "EALREADY"),
        (libc::ENOTSOCK, "ENOTSOCK"),
        (libc::EDESTADDRREQ, "EDESTADDRREQ"),
        (libc::EMSGSIZE, "EMSGSIZE"),
        (libc::EPROTOTYPE, "EPROTOTYPE"),
        (libc::ENOPROTOOPT, "ENOPROTOOPT"),
        (libc::EPROTONOSUPPORT, "EPROTONOSUPPORT"),
        (libc::ESOCKTNOSUPPORT, "ESOCKTNOSUPPORT"),
        (libc::EOPNOTSUPP, "EOPNOTSUPP"),
        (libc::EPFNOSUPPORT, "EPFNOSUPPORT"),
        (libc::EAFNOSUPPORT, "EAFNOSUPPORT"),
        (libc::EADDRINUSE, "EADDRINUSE"),
        (libc::EADDRNOTAVAIL, "EADDRNOTAVAIL"),
        (libc::ENETDOWN, "ENETDOWN"),
        (libc::ENETUNREACH, "ENETUNREACH"),
        (libc::ENETRESET, "ENETRESET"),
        (libc::ECONNABORTED, "ECONNABORTED"),
        (libc::ECONNRESET, "ECONNRESET"),
        (libc::ENOBUFS, "ENOBUFS"),
        (libc::EISCONN, "EISCONN"),
        (libc::ENOTCONN, "ENOTCONN"),
        (libc::ESHUTDOWN, "ESHUTDOWN"),
        (libc::ETOOMANYREFS, "ETOOMANYREFS"),
        (libc::ETIMEDOUT, "ETIMEDOUT"),
        (libc::ECONNREFUSED, "ECONNREFUSED"),
        (libc::EHOSTDOWN, "EHOSTDOWN"),
        (libc::EHOSTUNREACH, "EHOSTUNREACH"),
        (libc::ELOOP, "ELOOP"),
        (libc::EOVERFLOW, "EOVERFLOW"),
    ];
    match table.iter().find(|(c, _)| *c == code) {
        Some((_, name)) => name.to_string(),
        None => format!("EUNKNOWNERR {}", code),
    }
}

/// `Printexc.to_string (Unix.Unix_error (err, fun_name, arg))`:
/// `Unix.Unix_error(Unix.ENOENT, "mkdir", "/x")` (the strings with `%S`).
pub fn unix_error_to_string(err: &io::Error, fun_name: &str, arg: &str) -> String {
    format!(
        "Unix.Unix_error(Unix.{}, {}, {})",
        error_name(err),
        sprintf_S(fun_name),
        sprintf_S(arg)
    )
}

/// `Unix.open_flag`, the flags [`openfile_with_umask`] understands.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpenFlag {
    ORdonly,
    OWronly,
    ORdwr,
    OAppend,
    OCreat,
    OTrunc,
    OExcl,
}

/// The mode a file or directory created with `perm` gets under `umask`;
/// applied after the creation (see the module documentation). It cannot fail
/// for the owner of a file it just created; if it does, the file keeps the
/// mode the process umask gave it.
fn set_mode_after_creation(set: impl FnOnce(Permissions) -> io::Result<()>, mode: u32) {
    let _ = set(Permissions::from_mode(mode));
}

/// `Sys_utils.with_umask umask (fun () -> Unix.openfile path flags perm)`,
/// without changing the process umask. The file is opened close-on-exec, as
/// `std` opens files (OCaml's `Unix.openfile` without `O_CLOEXEC` does not,
/// but nothing of this port runs `exec` with descriptors it relies on).
pub fn openfile_with_umask(
    path: &str,
    flags: &[OpenFlag],
    perm: u32,
    umask: u32,
) -> io::Result<File> {
    let has = |f: OpenFlag| flags.contains(&f);
    let mut opts = OpenOptions::new();
    let (read, write) = if has(OpenFlag::ORdwr) {
        (true, true)
    } else if has(OpenFlag::OWronly) {
        (false, true)
    } else {
        (true, false)
    };
    opts.read(read)
        .write(write)
        .append(has(OpenFlag::OAppend))
        .truncate(has(OpenFlag::OTrunc));
    if !has(OpenFlag::OCreat) {
        return opts.open(path);
    }
    let mode = perm & !umask;
    let create_new = |opts: &OpenOptions| -> io::Result<File> {
        let file = opts.clone().create_new(true).mode(perm).open(path)?;
        set_mode_after_creation(|p| file.set_permissions(p), mode);
        Ok(file)
    };
    if has(OpenFlag::OExcl) {
        return create_new(&opts);
    }
    // `O_CREAT` without `O_EXCL`: create it if it is not there (and then set
    // its mode), open it as it is otherwise.
    for _ in 0..3 {
        match create_new(&opts) {
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => match opts.open(path) {
                // It was removed in between, or it is a dangling symbolic
                // link: try again.
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                res => return res,
            },
            res => return res,
        }
    }
    // A dangling symbolic link: `O_CREAT` creates its target.
    let file = opts.clone().create(true).mode(perm).open(path)?;
    set_mode_after_creation(|p| file.set_permissions(p), mode);
    Ok(file)
}

/// `Sys_utils.with_umask umask (fun () -> Unix.mkdir path perm)`, without
/// changing the process umask. As `mkdir(2)` does, the special bits the
/// system gave the new directory (a set-group-ID inherited from its parent)
/// are kept.
pub fn mkdir_with_umask(path: &str, perm: u32, umask: u32) -> io::Result<()> {
    std::fs::DirBuilder::new().mode(perm).create(path)?;
    let special = match std::fs::symlink_metadata(path) {
        Ok(m) => m.permissions().mode() & 0o7000,
        Err(_) => 0,
    };
    set_mode_after_creation(
        |p| std::fs::set_permissions(path, p),
        special | (perm & !umask & 0o777),
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::os::fd::AsRawFd;
    use std::os::unix::fs::MetadataExt;

    use super::*;

    fn scratch_dir(name: &str) -> String {
        let dir = std::env::temp_dir().join(format!(
            "hh_ocaml_unix_test_{}_{}_{}",
            name,
            std::process::id(),
            gettimeofday().to_bits()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        dir.to_str().unwrap().to_string()
    }

    #[test]
    fn signals_are_numbered_as_in_ocaml() {
        assert_eq!(rev_convert_signal_number(libc::SIGABRT), -1);
        assert_eq!(rev_convert_signal_number(libc::SIGKILL), -7);
        assert_eq!(rev_convert_signal_number(libc::SIGTERM), -11);
        assert_eq!(rev_convert_signal_number(libc::SIGXFSZ), -28);
        // A signal OCaml does not name keeps its number.
        assert_eq!(rev_convert_signal_number(0), 0);
    }

    #[test]
    fn unix_errors_print_as_in_ocaml() {
        let e = io::Error::from_raw_os_error(libc::ENOENT);
        assert_eq!(
            unix_error_to_string(&e, "mkdir", "/x/\"y\""),
            r#"Unix.Unix_error(Unix.ENOENT, "mkdir", "/x/\"y\"")"#
        );
        assert_eq!(
            error_name(&io::Error::from_raw_os_error(libc::EAGAIN)),
            "EAGAIN"
        );
        assert_eq!(
            error_name(&io::Error::from_raw_os_error(100_000)),
            "EUNKNOWNERR 100000"
        );
        // `ENOTSUP` (45 on macOS, `EOPNOTSUPP` on Linux) is `EOPNOTSUPP`.
        assert_eq!(
            error_name(&io::Error::from_raw_os_error(libc::ENOTSUP)),
            "EOPNOTSUPP"
        );
    }

    #[test]
    fn modes_do_not_depend_on_the_process_umask() {
        let dir = scratch_dir("modes");
        let sub = format!("{}/sub", dir);
        mkdir_with_umask(&sub, 0o777, 0).unwrap();
        assert_eq!(
            std::fs::metadata(&sub).unwrap().mode() & 0o777,
            0o777,
            "mkdir under umask 0"
        );
        let e = mkdir_with_umask(&sub, 0o777, 0).unwrap_err();
        assert_eq!(e.raw_os_error(), Some(libc::EEXIST));

        let file = format!("{}/f", dir);
        let f = openfile_with_umask(
            &file,
            &[OpenFlag::OWronly, OpenFlag::OCreat, OpenFlag::OTrunc],
            0o666,
            0o111,
        )
        .unwrap();
        drop(f);
        assert_eq!(std::fs::metadata(&file).unwrap().mode() & 0o777, 0o666);
        // An existing file keeps its mode.
        std::fs::set_permissions(&file, Permissions::from_mode(0o600)).unwrap();
        let _f =
            openfile_with_umask(&file, &[OpenFlag::ORdwr, OpenFlag::OCreat], 0o666, 0).unwrap();
        assert_eq!(std::fs::metadata(&file).unwrap().mode() & 0o777, 0o600);
        // Without `O_CREAT`, a missing file is an error.
        let e = openfile_with_umask(&format!("{}/missing", dir), &[OpenFlag::ORdonly], 0, 0)
            .unwrap_err();
        assert_eq!(e.raw_os_error(), Some(libc::ENOENT));
        // `O_EXCL` on an existing file.
        let e = openfile_with_umask(
            &file,
            &[OpenFlag::OWronly, OpenFlag::OCreat, OpenFlag::OExcl],
            0o666,
            0,
        )
        .unwrap_err();
        assert_eq!(e.raw_os_error(), Some(libc::EEXIST));
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_process_does_not_conflict_with_its_own_locks() {
        let dir = scratch_dir("lockf");
        let file = format!("{}/lock", dir);
        let f = openfile_with_umask(&file, &[OpenFlag::ORdwr, OpenFlag::OCreat], 0o666, 0)
            .unwrap();
        let fd = f.as_raw_fd();
        lockf(fd, LockCommand::FTlock, 1).unwrap();
        lockf(fd, LockCommand::FTest, 1).unwrap();
        lockf(fd, LockCommand::FTlock, 1).unwrap();
        lockf(fd, LockCommand::FUlock, 1).unwrap();
        lockf(fd, LockCommand::FRlock, 0).unwrap();
        lockf(fd, LockCommand::FUlock, 0).unwrap();
        drop(f);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn kill_zero() {
        kill(getpid(), 0).unwrap();
        assert!(gettimeofday() > 1.6e9);
    }
}
