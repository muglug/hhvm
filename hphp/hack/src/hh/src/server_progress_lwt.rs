// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/server_progress_lwt.ml`. See `hh/PORTING.md`.
//!
//! The errors that `hh_server` streams to the errors file (`errors.bin`) are
//! read with `Server_progress.ErrorsRead.read_next_errors fd`, after
//! `ErrorsRead.openfile fd`: the descriptor here is an [`ErrorsReader`],
//! which a `std::fs::File` of the errors file is (and tests script). The
//! decisions are OCaml's: poll every 0.2s while there is nothing yet and the
//! server is alive, end with `Killed` (and its finale data) when it has
//! died, end after a completion or an error.
//!
//! The `Lwt_stream.t` is a channel: [`watch_errors_file`] returns its
//! receiving end; `add None` (the end of the stream) is the sender going
//! away. The two long-running Lwt tasks (`watch`, `watch_pid`) are threads;
//! `Lwt.cancel pid_future` stops the second. As in OCaml, there's no way to
//! cancel the long-running task.

use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::mpsc;

use crate::exit_status;
use crate::format;
use crate::format::Formatter;
use crate::rt::ocaml_unix;
use crate::server_files;
use crate::server_progress;
use crate::server_progress::ErrorsFileReadError;
use crate::server_progress::errors_read::ReadResult;

pub enum WatchError {
    /// Hh_server was killed so we can't read errors.
    Killed(Option<exit_status::FinaleData>),
    ReadError(ErrorsFileReadError),
}

/// `pp_watch_error` (`[@@deriving show]`)
pub fn pp_watch_error(fmt: &mut Formatter, e: &WatchError) {
    // A constructor with an argument: "(@[<2>%s@ " ctor, the argument, "@])"
    let with_arg = |fmt: &mut Formatter, ctor: &str, arg: &dyn Fn(&mut Formatter)| {
        format::pp_print_string(fmt, "(");
        format::pp_open_box(fmt, 2);
        format::pp_print_string(fmt, ctor);
        format::pp_print_space(fmt);
        arg(fmt);
        format::pp_close_box(fmt);
        format::pp_print_string(fmt, ")");
    };
    match e {
        WatchError::Killed(a0) => with_arg(fmt, "Server_progress_lwt.Killed", &|fmt| match a0 {
            None => format::pp_print_string(fmt, "None"),
            Some(x) => {
                format::pp_print_string(fmt, "(Some ");
                exit_status::pp_finale_data(fmt, x);
                format::pp_print_string(fmt, ")");
            }
        }),
        WatchError::ReadError(a0) => with_arg(fmt, "Server_progress_lwt.Read_error", &|fmt| {
            server_progress::pp_errors_file_read_error(fmt, a0)
        }),
    }
}

pub fn show_watch_error(e: &WatchError) -> String {
    format::asprintf(|fmt| pp_watch_error(fmt, e))
}

impl std::fmt::Debug for WatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&show_watch_error(self))
    }
}

pub fn watch_error_short_description(e: &WatchError) -> &'static str {
    match e {
        WatchError::Killed(_) => "hh_server died",
        WatchError::ReadError(ErrorsFileReadError::Malformed) => "malformed error",
    }
}

/// What [`watch`] reads: the errors the server has written since the last
/// call, one at a time, as `Server_progress.ErrorsRead.read_next_errors fd`
/// reads them from the errors file (after `ErrorsRead.openfile`): `Ok None`
/// when there is nothing more yet, `RItem` for an item, `RCompleted` for the
/// end of a typecheck.
pub trait ErrorsReader: Send {
    fn read_next_errors(&mut self) -> Result<Option<ReadResult>, ErrorsFileReadError>;
}

impl<R: ErrorsReader + ?Sized> ErrorsReader for Box<R> {
    fn read_next_errors(&mut self) -> Result<Option<ReadResult>, ErrorsFileReadError> {
        (**self).read_next_errors()
    }
}

/// The errors file itself.
impl ErrorsReader for std::fs::File {
    fn read_next_errors(&mut self) -> Result<Option<ReadResult>, ErrorsFileReadError> {
        server_progress::errors_read::read_next_errors(self)
    }
}

/// `add`: a value for the stream, or `None` to end it.
type Add<'a> = dyn FnMut(Option<Result<ReadResult, WatchError>>) + 'a;

/// This long-lived Lwt routine will keep polling the file, and the
/// report it finds into the queue. If it gets an error then it sticks that
/// in the queue and terminates.
/// Exception: if it gets a NothingYet error, then it either continues polling
/// the file, or ends the queue with Server_progress.Killed, depending on whether
/// the producing PID is still alive.
///
/// (`pid_future` is whether `watch_pid` is still waiting: the server is
/// alive.)
fn watch(pid: isize, pid_future: &AtomicBool, fd: &mut dyn ErrorsReader, add: &mut Add<'_>) {
    loop {
        match fd.read_next_errors() {
            Err(err) => {
                add(Some(Err(WatchError::ReadError(err))));
                add(None);
                return;
            }
            Ok(None) => {
                if pid_future.load(Ordering::SeqCst) {
                    std::thread::sleep(std::time::Duration::from_millis(200));
                    continue;
                } else {
                    let server_finale_file = server_files::server_finale_file(pid);
                    let finale_data = exit_status::get_finale_data(&server_finale_file);
                    add(Some(Err(WatchError::Killed(finale_data))));
                    add(None);
                    return;
                }
            }
            Ok(Some(res)) => match res {
                ReadResult::RItem(_) => {
                    add(Some(Ok(res)));
                    continue;
                }
                ReadResult::RCompleted(..) => {
                    add(Some(Ok(res)));
                    add(None);
                    return;
                }
            },
        }
    }
}

/// This returns an Lwt future which will complete once <pid> dies.
/// It implements this by polling "SIGKILL 0" every 5s.
///
/// (The future is the flag, true while it is sleeping; `cancelled` is
/// `Lwt.cancel`.)
fn watch_pid(pid: isize, sleeping: Arc<AtomicBool>, cancelled: Arc<AtomicBool>) {
    loop {
        // `Lwt_unix.sleep 5.0`, which a cancel interrupts.
        for _ in 0..50 {
            if cancelled.load(Ordering::SeqCst) {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
        let is_alive = ocaml_unix::kill(pid, 0).is_ok();
        if !is_alive {
            sleeping.store(false, Ordering::SeqCst);
            return;
        }
    }
}

/// This function kicks off a long-running task which watches the errors.bin file that the
/// caller has already opened, and has already called openfile upon.
/// It returns a Lwt_stream.t as follows:
/// * The stream provides errors, telemetry and completion sentinels written to the file
/// * If the producing PID gets killed without a clean finish, then that too will
///   be detected and reported with "Error Killed" in the stream, albeit not quite so soon.
///   (It only performs this inter-process polling every 5s).
/// * There's no way to cancel the long-running task.
/// * The stream should terminate (i.e. return None) iff the previous message
///   was a completion sentinel or an error.
pub fn watch_errors_file(
    pid: isize,
    mut fd: impl ErrorsReader + 'static,
) -> mpsc::Receiver<Result<ReadResult, WatchError>> {
    let (q, rx) = mpsc::channel();
    let sleeping = Arc::new(AtomicBool::new(true));
    let cancelled = Arc::new(AtomicBool::new(false));
    {
        let sleeping = sleeping.clone();
        let cancelled = cancelled.clone();
        std::thread::spawn(move || watch_pid(pid, sleeping, cancelled));
    }
    let _watcher_future = std::thread::spawn(move || {
        let mut q = Some(q);
        let mut add = |x: Option<Result<ReadResult, WatchError>>| match x {
            Some(x) => {
                if let Some(q) = &q {
                    // A consumer that went away misses the rest.
                    let _ = q.send(x);
                }
            }
            None => q = None,
        };
        watch(pid, &sleeping, &mut fd, &mut add);
        // `|> Lwt.map (fun () -> Lwt.cancel pid_future)`
        cancelled.store(true, Ordering::SeqCst);
    });
    rx
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use super::*;
    use crate::server_progress::CompletionReason;
    use crate::server_progress::ErrorsFileItem;

    struct Scripted(VecDeque<Result<Option<ReadResult>, ErrorsFileReadError>>);

    impl ErrorsReader for Scripted {
        fn read_next_errors(&mut self) -> Result<Option<ReadResult>, ErrorsFileReadError> {
            self.0.pop_front().unwrap_or(Ok(None))
        }
    }

    fn telemetry_item() -> ReadResult {
        ReadResult::RItem(ErrorsFileItem::Telemetry(crate::telemetry::create()))
    }

    #[test]
    fn items_then_completion_end_the_stream() {
        let script = Scripted(
            vec![
                Ok(Some(telemetry_item())),
                Ok(None),
                Ok(Some(telemetry_item())),
                Ok(Some(ReadResult::RCompleted(
                    CompletionReason::Stopped,
                    "done".to_string(),
                ))),
                Ok(Some(telemetry_item())),
            ]
            .into(),
        );
        let rx = watch_errors_file(ocaml_unix::getpid(), script);
        let got: Vec<_> = rx.iter().collect();
        assert_eq!(got.len(), 3);
        assert!(matches!(got[0], Ok(ReadResult::RItem(_))));
        assert!(matches!(got[2], Ok(ReadResult::RCompleted(..))));
    }

    #[test]
    fn a_read_error_ends_the_stream() {
        let script = Scripted(vec![Err(ErrorsFileReadError::Malformed)].into());
        let rx = watch_errors_file(ocaml_unix::getpid(), script);
        let got: Vec<_> = rx.iter().collect();
        assert_eq!(got.len(), 1);
        match &got[0] {
            Err(e) => {
                assert_eq!(watch_error_short_description(e), "malformed error");
                assert_eq!(
                    show_watch_error(e),
                    "(Server_progress_lwt.Read_error Server_progress.Malformed)"
                );
            }
            Ok(_) => panic!("expected an error"),
        }
    }

    #[test]
    fn a_dead_server_is_killed() {
        crate::server_files::tests::testing_tmp();
        // A process that has exited (and been waited for).
        let mut child = std::process::Command::new("true").spawn().unwrap();
        let pid = child.id() as isize;
        child.wait().unwrap();
        let rx = watch_errors_file(pid, Scripted(VecDeque::new()));
        let got: Vec<_> = rx.iter().collect();
        assert_eq!(got.len(), 1);
        match &got[0] {
            Err(e @ WatchError::Killed(None)) => {
                assert_eq!(watch_error_short_description(e), "hh_server died");
                assert_eq!(show_watch_error(e), "(Server_progress_lwt.Killed None)");
            }
            _ => panic!("expected Killed None"),
        }
    }
}
