// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The parts of OCaml's `Stdlib.Sys` that the programs of the server layer
//! need and `std` does not give in the same form: `Sys.argv` and
//! `Sys.set_signal`. See `hh/PORTING.md`, "The server layer".
//!
//! # `Sys.argv`
//!
//! [`argv`] is the command line, the program name first, as OCaml's
//! `Sys.argv` (the name as it was invoked, not resolved). An argument that is
//! not UTF-8 has its invalid bytes replaced by U+FFFD (an OCaml string would
//! keep them). A test can run code with another command line
//! ([`with_argv_FOR_TESTING`], per thread).
//!
//! # `Sys.set_signal`
//!
//! OCaml runs a signal handler (`Signal_handle f`) on the main thread at the
//! next safe point, and an exception it raises comes out of whatever the
//! program was doing (a blocking `read` is interrupted for it). A Rust signal
//! handler can do neither. Here the C handler only writes the signal number
//! to a pipe, and a thread of its own reads it and calls `f`, while the main
//! thread goes on. So a handler that OCaml uses to raise an exception (as
//! `hh_client`'s SIGINT handler raises `Exit_with Interrupted`) must do here
//! what catching that exception would end in, typically `Exit.exit`.
//! Handlers are installed with `SA_RESTART`, so the system calls the main
//! thread is blocked in are not interrupted (where OCaml's would return
//! `EINTR` and run the handler).

#![allow(non_snake_case)]

use std::cell::RefCell;
use std::os::fd::RawFd;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::OnceLock;

use crate::rt::ocaml_unix;

thread_local! {
    static ARGV_FOR_TESTING: RefCell<Option<Vec<String>>> = const { RefCell::new(None) };
}

/// `Sys.argv`
pub fn argv() -> Vec<String> {
    if let Some(argv) = ARGV_FOR_TESTING.with(|a| a.borrow().clone()) {
        return argv;
    }
    std::env::args_os()
        .map(|a| match a.into_string() {
            Ok(s) => s,
            Err(a) => a.to_string_lossy().into_owned(),
        })
        .collect()
}

/// Runs `f` with [`argv`] returning `argv` (on this thread).
pub fn with_argv_FOR_TESTING<A>(argv: Vec<String>, f: impl FnOnce() -> A) -> A {
    let saved = ARGV_FOR_TESTING.with(|a| a.replace(Some(argv)));
    struct Restore(Option<Vec<String>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let saved = self.0.take();
            ARGV_FOR_TESTING.with(|a| *a.borrow_mut() = saved);
        }
    }
    let _restore = Restore(saved);
    f()
}

/// A handler: it is given the OCaml number of the signal (`Sys.sigint` is
/// `-6`).
pub type Handler = Arc<dyn Fn(isize) + Send + Sync>;

/// `Sys.signal_behavior`
#[derive(Clone)]
pub enum SignalBehavior {
    SignalDefault,
    SignalIgnore,
    SignalHandle(Handler),
}

/// The handlers, by system signal number.
static HANDLERS: Mutex<Vec<(i32, Handler)>> = Mutex::new(Vec::new());

/// The write end of the pipe that the C handler writes signal numbers to.
static PIPE_WRITE: OnceLock<RawFd> = OnceLock::new();

extern "C" fn on_signal(signo: libc::c_int) {
    if let Some(fd) = PIPE_WRITE.get() {
        let byte = signo as u8;
        // SAFETY: `write` and `errno` are async-signal-safe; the byte lives
        // during the call. A full pipe drops the signal.
        unsafe {
            let errno = *errno_location();
            let _ = libc::write(*fd, &byte as *const u8 as *const libc::c_void, 1);
            *errno_location() = errno;
        }
    }
}

#[cfg(target_os = "macos")]
unsafe fn errno_location() -> *mut libc::c_int {
    // SAFETY: always valid for the calling thread.
    unsafe { libc::__error() }
}

#[cfg(not(target_os = "macos"))]
unsafe fn errno_location() -> *mut libc::c_int {
    // SAFETY: always valid for the calling thread.
    unsafe { libc::__errno_location() }
}

/// Makes the pipe and starts the thread that runs the handlers, once.
fn start_dispatcher() -> RawFd {
    *PIPE_WRITE.get_or_init(|| {
        let mut fds = [0 as libc::c_int; 2];
        // SAFETY: `fds` has room for the two descriptors `pipe` returns.
        let ret = unsafe { libc::pipe(fds.as_mut_ptr()) };
        if ret != 0 {
            panic!(
                "Sys_error: cannot make the pipe of signal handlers: {}",
                std::io::Error::last_os_error()
            );
        }
        let (read_fd, write_fd) = (fds[0], fds[1]);
        // SAFETY: the descriptors were just made.
        unsafe {
            libc::fcntl(read_fd, libc::F_SETFD, libc::FD_CLOEXEC);
            libc::fcntl(write_fd, libc::F_SETFD, libc::FD_CLOEXEC);
            let flags = libc::fcntl(write_fd, libc::F_GETFL);
            libc::fcntl(write_fd, libc::F_SETFL, flags | libc::O_NONBLOCK);
        }
        std::thread::Builder::new()
            .name("signal handlers".to_string())
            .spawn(move || {
                loop {
                    let mut byte = 0u8;
                    // SAFETY: reads one byte into `byte`.
                    let n = unsafe {
                        libc::read(read_fd, &mut byte as *mut u8 as *mut libc::c_void, 1)
                    };
                    if n == 1 {
                        let signo = byte as i32;
                        let handler = HANDLERS
                            .lock()
                            .unwrap()
                            .iter()
                            .find(|(s, _)| *s == signo)
                            .map(|(_, h)| h.clone());
                        if let Some(handler) = handler {
                            handler(ocaml_unix::rev_convert_signal_number(signo));
                        }
                    } else if n == 0
                        || std::io::Error::last_os_error().kind()
                            != std::io::ErrorKind::Interrupted
                    {
                        return;
                    }
                }
            })
            .expect("cannot start the thread of signal handlers");
        write_fd
    })
}

/// `Sys.set_signal`: set the behavior of the system on receipt of the given
/// signal (a system signal number, `libc::SIGINT`). Panics as OCaml raises
/// `Invalid_argument "Sys.signal"` when the signal cannot be handled.
pub fn set_signal(signal: i32, behavior: SignalBehavior) {
    let action = match &behavior {
        SignalBehavior::SignalDefault => libc::SIG_DFL,
        SignalBehavior::SignalIgnore => libc::SIG_IGN,
        SignalBehavior::SignalHandle(handler) => {
            start_dispatcher();
            let mut handlers = HANDLERS.lock().unwrap();
            handlers.retain(|(s, _)| *s != signal);
            handlers.push((signal, handler.clone()));
            on_signal as extern "C" fn(libc::c_int) as libc::sighandler_t
        }
    };
    // SAFETY: `sa` is fully initialised before `sigaction` reads it.
    let ret = unsafe {
        let mut sa: libc::sigaction = std::mem::zeroed();
        sa.sa_sigaction = action;
        sa.sa_flags = libc::SA_RESTART;
        libc::sigemptyset(&mut sa.sa_mask);
        libc::sigaction(signal, &sa, std::ptr::null_mut())
    };
    if ret != 0 {
        panic!("Invalid_argument: Sys.signal");
    }
    match behavior {
        SignalBehavior::SignalHandle(_) => {}
        SignalBehavior::SignalDefault | SignalBehavior::SignalIgnore => {
            HANDLERS.lock().unwrap().retain(|(s, _)| *s != signal);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::AtomicIsize;
    use std::sync::atomic::Ordering;

    use super::*;

    #[test]
    fn argv_for_testing() {
        let real = argv();
        with_argv_FOR_TESTING(vec!["a".to_string(), "b".to_string()], || {
            assert_eq!(argv(), vec!["a", "b"]);
        });
        assert_eq!(argv(), real);
    }

    #[test]
    fn handlers_run_on_their_thread() {
        static GOT: AtomicIsize = AtomicIsize::new(0);
        set_signal(
            libc::SIGUSR2,
            SignalBehavior::SignalHandle(Arc::new(|signo| GOT.store(signo, Ordering::SeqCst))),
        );
        // SAFETY: sends a signal to this process, which handles it.
        unsafe {
            libc::kill(libc::getpid(), libc::SIGUSR2);
        }
        let mut waited = 0;
        while GOT.load(Ordering::SeqCst) == 0 && waited < 500 {
            std::thread::sleep(std::time::Duration::from_millis(10));
            waited += 1;
        }
        // `Sys.sigusr2` is -13 in OCaml.
        assert_eq!(GOT.load(Ordering::SeqCst), -13);
        set_signal(libc::SIGUSR2, SignalBehavior::SignalIgnore);
    }
}
