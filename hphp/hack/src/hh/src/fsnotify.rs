// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `fsnotify/fsnotify.ml` (Linux): the inotify watches of dfind
//! (`crate::dfind_lib`), on the `inotify` crate instead of the OCaml stubs
//! of `third-party/inotify`. On macOS dfind watches with FSEvents (the
//! `notify` crate) instead.
//!
//! `select` waits on the inotify descriptor and a descriptor that is closed
//! to stop dfind, in place of dfind's request pipe.

use std::collections::HashMap;
use std::os::fd::AsRawFd;
use std::os::fd::BorrowedFd;

use inotify::EventMask;
use inotify::Inotify;
use inotify::WatchDescriptor;
use inotify::WatchMask;

use crate::rt::ocaml_filename;

/// `Fsnotify.Error (reason, err)`
#[derive(Debug)]
pub struct Error {
    pub reason: String,
    pub err: std::io::Error,
}

/// What `wrap` makes of the `Unix.Unix_error (err, func, msg)` of `func`.
fn wrap(func: &str, msg: &str, err: std::io::Error) -> Error {
    // `Unix.error_message`: `strerror`.
    let message = match err.raw_os_error() {
        // SAFETY: `strerror` returns a static string for any errno.
        Some(errno) => unsafe { std::ffi::CStr::from_ptr(libc::strerror(errno)) }
            .to_string_lossy()
            .into_owned(),
        None => err.to_string(),
    };
    Error {
        reason: format!("{}: {}: {}", func, msg, message),
        err,
    }
}

/// A watch in this case refers to an inotify watch. Inotify watches are used
/// to subscribe to events on files in linux kernel.
/// Once a watch has been added to a file, the kernel notifies us every time
/// the file changes (by sending an event to a pipe, cf env.inotify).
/// We need to be able to compare watches because there could be multiple
/// paths that lead to the same watch (because of symlinks).
pub type Watch = WatchDescriptor;

pub struct Env {
    fd: Inotify,
    wpaths: HashMap<Watch, String>,
}

pub struct Event {
    /// The full path for the file/directory that changed
    pub path: String,
    /// The watched path that triggered this event
    pub wpath: String,
}

pub fn init(_roots: &[String]) -> Result<Env, Error> {
    Ok(Env {
        fd: Inotify::init().map_err(|e| wrap("inotify_init", "", e))?,
        wpaths: HashMap::new(),
    })
}

pub fn select_events() -> WatchMask {
    WatchMask::CREATE
        | WatchMask::DELETE
        | WatchMask::DELETE_SELF
        | WatchMask::MODIFY
        | WatchMask::MOVE_SELF
        | WatchMask::MOVED_FROM
        | WatchMask::MOVED_TO
        | WatchMask::ATTRIB
}

/// Returns None if we're already watching that path and Some watch otherwise
pub fn add_watch(env: &mut Env, path: &str) -> Result<Option<Watch>, Error> {
    let watch = env
        .fd
        .watches()
        .add(path, select_events())
        .map_err(|e| wrap("inotify_add_watch", path, e))?;
    if env.wpaths.get(&watch).is_some_and(|wpath| wpath == path) {
        Ok(None)
    } else {
        env.wpaths.insert(watch.clone(), path.to_string());
        Ok(Some(watch))
    }
}

/// Whether `path` is a watched path.
pub fn is_watched(env: &Env, path: &str) -> bool {
    env.wpaths.values().any(|wpath| wpath == path)
}

/// Why `read` gave no events.
pub enum ReadError {
    /// `Fsnotify.read` raised.
    Error(Error),
    /// `Inotify.Q_overflow`.
    Overflow,
}

/// `read env`, in the order of the kernel. The events without a name (those
/// of a watched directory itself) are dropped, as `process_event` drops
/// them, but for an overflow: `process_event` drops it with them before
/// `check_event_type` sees it, which loses changes silently; here it is
/// reported, and dfind dies as `check_event_type` means it to.
fn read(env: &mut Env, buffer: &mut [u8]) -> Result<Vec<Event>, ReadError> {
    let inotify_events = match env.fd.read_events(buffer) {
        Ok(events) => events,
        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => return Ok(vec![]),
        Err(e) => return Err(ReadError::Error(wrap("read", "", e))),
    };
    let mut events = vec![];
    for event in inotify_events {
        match event.name {
            None if event.mask.contains(EventMask::Q_OVERFLOW) => {
                return Err(ReadError::Overflow);
            }
            None => {}
            Some(filename) => {
                let wpath = match env.wpaths.get(&event.wd) {
                    Some(wpath) => wpath,
                    None => panic!("assert false"),
                };
                let path = ocaml_filename::concat(wpath, &filename.to_string_lossy());
                events.push(Event {
                    path,
                    wpath: wpath.clone(),
                });
            }
        }
    }
    Ok(events)
}

/// What `select` saw.
pub enum Select {
    /// The events read.
    Events(Vec<Event>),
    /// `stop` was closed.
    Stopped,
}

/// `select env ~read_fdl:[(stop, _)] ~timeout:(-1.0) callback`: waits for
/// events, or for `stop` to be closed (it is the read end of a pipe whose
/// write end is dropped to stop dfind). `Inotify.read` reads one event at a
/// time (a buffer of `sizeof(struct inotify_event) + NAME_MAX + 1`); here
/// `buffer` takes as many as fit, for fewer system calls.
pub fn select(env: &mut Env, stop: BorrowedFd<'_>, buffer: &mut [u8]) -> Result<Select, ReadError> {
    let mut fds = [
        libc::pollfd {
            fd: env.fd.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        },
        libc::pollfd {
            fd: stop.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        },
    ];
    loop {
        // SAFETY: `fds` is an array of two `pollfd`s.
        let n = unsafe { libc::poll(fds.as_mut_ptr(), fds.len() as libc::nfds_t, -1) };
        if n >= 0 {
            break;
        }
        let e = std::io::Error::last_os_error();
        if e.kind() != std::io::ErrorKind::Interrupted {
            return Err(ReadError::Error(wrap("select", "", e)));
        }
    }
    if fds[1].revents != 0 {
        return Ok(Select::Stopped);
    }
    if fds[0].revents != 0 {
        return read(env, buffer).map(Select::Events);
    }
    Ok(Select::Events(vec![]))
}
