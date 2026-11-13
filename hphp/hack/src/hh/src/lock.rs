// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lock.ml`. See `hh/PORTING.md`.
//!
//! Basic lock operations.
//!
//! We use these for two reasons:
//! 1. making sure we are only running one instance of hh_server per person on a given dev box
//! 2. giving a way to hh_client to check if a server is running.
//!
//! The locks are OCaml's `Unix.lockf` locks (POSIX record locks on the first
//! byte of the file, `crate::rt::ocaml_unix::lockf`): a process holds them,
//! not a thread, and closing any descriptor of the file releases them, which
//! is why a lock file is opened once and its descriptor kept for the life of
//! the process.
//!
//! `Sys_utils.mkdir_no_fail` is not in `crate::sys_utils` yet: it is
//! transliterated below, private, and should move there.

use std::collections::BTreeMap;
use std::fs::File;
use std::os::fd::AsRawFd;
use std::os::fd::RawFd;
use std::os::unix::fs::MetadataExt;
use std::sync::Mutex;
use std::sync::MutexGuard;

use crate::rt::ocaml_filename;
use crate::rt::ocaml_unix;
use crate::rt::ocaml_unix::LockCommand;

/// The identity of a file in `Unix.stats` that `_operations` compares
/// (`st_dev`, `st_ino`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Stats {
    st_dev: u64,
    st_ino: u64,
}

/// `lock_fds : (Unix.file_descr * Unix.stats) S_map.t ref`: the open lock
/// files, by name. A file stays open (and in the map) for the life of the
/// process, as in OCaml.
fn lock_fds() -> MutexGuard<'static, BTreeMap<String, (File, Stats)>> {
    static LOCK_FDS: Mutex<BTreeMap<String, (File, Stats)>> = Mutex::new(BTreeMap::new());
    LOCK_FDS.lock().unwrap_or_else(|e| e.into_inner())
}

/// `Sys_utils.mkdir_no_fail dir`: `Unix.mkdir dir 0o777` under umask 0; a
/// directory that exists already is fine, any other error is raised.
fn mkdir_no_fail(dir: &str) -> std::io::Result<()> {
    match ocaml_unix::mkdir_with_umask(dir, 0o777, 0) {
        Err(e) if e.raw_os_error() == Some(libc::EEXIST) => Ok(()),
        res => res,
    }
}

/// `register_lock lock_file`: opens the lock file (`open_out`, under umask
/// `0o111`: mode `0o666`) and records it. Any error is an exception that
/// `_operations` turns into `false`.
fn register_lock(
    lock_fds: &mut BTreeMap<String, (File, Stats)>,
    lock_file: &str,
) -> std::io::Result<RawFd> {
    let _ = mkdir_no_fail(&ocaml_filename::dirname(lock_file))?;
    let file = ocaml_unix::openfile_with_umask(
        lock_file,
        &[
            ocaml_unix::OpenFlag::OWronly,
            ocaml_unix::OpenFlag::OCreat,
            ocaml_unix::OpenFlag::OTrunc,
        ],
        0o666,
        0o111,
    )?;
    let st = file.metadata()?;
    let fd = file.as_raw_fd();
    lock_fds.insert(
        lock_file.to_string(),
        (
            file,
            Stats {
                st_dev: st.dev(),
                st_ino: st.ino(),
            },
        ),
    );
    Ok(fd)
}

/// Grab or check if a file lock is available.
///
/// Returns true if the lock is/was available, false otherwise.
fn _operations(lock_file: &str, op: LockCommand) -> bool {
    let fd = {
        let mut lock_fds = lock_fds();
        match lock_fds.get(lock_file) {
            None => match register_lock(&mut lock_fds, lock_file) {
                Ok(fd) => fd,
                Err(_) => return false,
            },
            Some((file, st)) => {
                let identical_file = {
                    // Note: I'm carefully avoiding opening another fd to the
                    // lock_file when doing this check, because closing any file
                    // descriptor to a given file will release the locks on *all*
                    // file descriptors that point to that file. Fortunately, stat()
                    // gets us our information without opening a fd
                    match std::fs::metadata(lock_file) {
                        Ok(current_st) => {
                            st.st_dev == current_st.dev() && st.st_ino == current_st.ino()
                        }
                        Err(_) => false,
                    }
                };
                if !identical_file {
                    // Looks like someone (tmpwatch?) deleted the lock file; don't
                    // create another one, because our socket is probably gone too.
                    // We are dead in the water.
                    return false;
                } else {
                    file.as_raw_fd()
                }
            }
        }
    };
    // The file stays open in `lock_fds`, so `fd` stays valid; the map is not
    // held while a `F_LOCK` blocks.
    ocaml_unix::lockf(fd, op, 1).is_ok()
}

/// Grabs the file lock and returns true if it the lock was grabbed
pub fn grab(lock_file: &str) -> bool {
    _operations(lock_file, LockCommand::FTlock)
}

/// Releases a file lock.
pub fn release(lock_file: &str) -> bool {
    _operations(lock_file, LockCommand::FUlock)
}

pub fn blocking_grab_then_release(lock_file: &str) {
    let _ = _operations(lock_file, LockCommand::FLock);
    let _ = release(lock_file);
}

/// Gets the server instance-unique integral fd for a given lock file.
///
/// (The OCaml returns `Obj.magic` of the `(fd, stats)` pair it finds, not of
/// the descriptor: a meaningless number. This returns the descriptor, which
/// is what the comment says; nothing calls it.)
pub fn fd_of(lock_file: &str) -> isize {
    match lock_fds().get(lock_file) {
        None => -1,
        Some((file, _)) => file.as_raw_fd() as isize,
    }
}

/// Check if the file lock is available without grabbing it.
/// Returns true if the lock is free.
pub fn check(lock_file: &str) -> bool {
    _operations(lock_file, LockCommand::FTest)
}

#[cfg(test)]
mod tests {
    use std::io::BufRead;
    use std::io::Write;

    use super::*;

    /// The environment variable that turns [`lock_holder_child`] into the
    /// other process of [`contention_between_processes`].
    const HOLDER_ENV: &str = "HH_LOCK_TEST_HOLD";

    fn scratch_dir(name: &str) -> String {
        std::env::temp_dir()
            .join(format!(
                "hh_lock_test_{}_{}_{}",
                name,
                std::process::id(),
                ocaml_unix::gettimeofday().to_bits()
            ))
            .to_str()
            .unwrap()
            .to_string()
    }

    /// Not a test by itself: run by [`contention_between_processes`] in a
    /// child process, it grabs the lock named by `HH_LOCK_TEST_HOLD`, says
    /// `locked`, and holds it until its stdin is closed.
    #[test]
    fn lock_holder_child() {
        let Ok(lock_file) = std::env::var(HOLDER_ENV) else {
            return;
        };
        assert!(grab(&lock_file));
        println!("locked");
        std::io::stdout().flush().unwrap();
        let mut line = String::new();
        let _ = std::io::stdin().lock().read_line(&mut line);
    }

    #[test]
    fn contention_between_processes() {
        let dir = scratch_dir("contention");
        // The directory is made by `register_lock`.
        let lock_file = format!("{}/root.lock", dir);
        assert!(check(&lock_file), "a lock nobody holds is free");

        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "lock::tests::lock_holder_child",
                "--exact",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(HOLDER_ENV, &lock_file)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        let mut stdout = std::io::BufReader::new(child.stdout.take().unwrap());
        let mut line = String::new();
        loop {
            line.clear();
            assert!(stdout.read_line(&mut line).unwrap() > 0, "the child exited");
            // libtest prints `test lock::tests::lock_holder_child ... `
            // with no newline before the test runs (one test thread), so
            // the child's `locked` ends that line.
            if line.trim_end().ends_with("locked") {
                break;
            }
        }
        // Another process holds it.
        assert!(!check(&lock_file));
        assert!(!grab(&lock_file));
        // Let it go: its lock goes with it.
        drop(child.stdin.take());
        assert!(child.wait().unwrap().success());
        assert!(check(&lock_file));
        assert!(grab(&lock_file));
        // A process does not conflict with itself.
        assert!(check(&lock_file));
        assert!(grab(&lock_file));
        assert!(fd_of(&lock_file) >= 0);
        assert!(release(&lock_file));
        blocking_grab_then_release(&lock_file);

        // The lock file was replaced under our feet: dead in the water.
        std::fs::remove_file(&lock_file).unwrap();
        std::fs::write(&lock_file, "").unwrap();
        assert!(!grab(&lock_file));
        assert!(!check(&lock_file));
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn lock_file_mode_and_failures() {
        let dir = scratch_dir("mode");
        let lock_file = format!("{}/x.lock", dir);
        assert!(grab(&lock_file));
        assert_eq!(std::fs::metadata(&lock_file).unwrap().mode() & 0o777, 0o666);
        assert_eq!(fd_of("/nonexistent/never/registered"), -1);
        // A lock file that cannot be created.
        assert!(!grab("/nonexistent/hh_lock_test/a/b.lock"));
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
