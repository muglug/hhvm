// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/server_process.ml`.
//!
//! Owned by **MON** (plan §3.1).

use std::cell::Cell;
use std::collections::BTreeMap;
use std::os::fd::RawFd;

use crate::rt::protocol::monitor_rpc::PipeType;
use crate::server_command_types::ServerSpecificFiles;

/// `Unix.process_status`, with OCaml's signal numbers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProcessStatus {
    WEXITED(isize),
    WSIGNALED(isize),
    WSTOPPED(isize),
}

impl ProcessStatus {
    /// The status `waitpid` gives (`Unix.waitpid`'s conversion).
    pub fn of_raw(status: libc::c_int) -> ProcessStatus {
        use crate::rt::ocaml_unix::rev_convert_signal_number;
        if libc::WIFEXITED(status) {
            ProcessStatus::WEXITED(libc::WEXITSTATUS(status) as isize)
        } else if libc::WIFSTOPPED(status) {
            ProcessStatus::WSTOPPED(rev_convert_signal_number(libc::WSTOPSIG(status)))
        } else {
            ProcessStatus::WSIGNALED(rev_convert_signal_number(libc::WTERMSIG(status)))
        }
    }

    /// `Exit_status.unpack`
    pub fn unpack(self) -> (String, isize) {
        match self {
            ProcessStatus::WEXITED(n) => ("exit".to_string(), n),
            ProcessStatus::WSIGNALED(n) => ("signaled".to_string(), n),
            ProcessStatus::WSTOPPED(n) => ("stopped".to_string(), n),
        }
    }

    /// As the client receives it (`Prehandoff.exit_status.status`).
    pub fn to_prehandoff(self) -> crate::rt::protocol::prehandoff::ProcessStatus {
        use crate::rt::protocol::prehandoff::ProcessStatus as P;
        match self {
            ProcessStatus::WEXITED(n) => P::WEXITED(n),
            ProcessStatus::WSIGNALED(n) => P::WSIGNALED(n),
            ProcessStatus::WSTOPPED(n) => P::WSTOPPED(n),
        }
    }
}

#[derive(Debug)]
pub struct ProcessData {
    /// Process ID.
    pub pid: i32,
    pub server_specific_files: ServerSpecificFiles,
    pub start_t: f64,
    /// Get occasional updates about status/busyness from typechecker here.
    pub in_fd: RawFd,
    /// Send client's File Descriptors to the typechecker over this.
    pub out_fds: BTreeMap<PipeType, RawFd>,
    pub last_request_handoff: Cell<f64>,
}

#[derive(Debug)]
pub enum ServerProcess {
    NotYetStarted,
    Alive(ProcessData),
    /// When the server crashes, we want to track that it has crashed and report
    /// that crash info to the next hh_client that connects. We keep that info
    /// here.
    DiedUnexpectedly(ProcessStatus, bool),
    /// The problem we need to solve is this: when the Monitor wants to start
    /// a new Server instance, it might not be safe to do so because we might
    /// end up running the a version of the Server not meant for this state of
    /// the repo (as specified in the .hhconfig file).
    ///
    /// (See `server_process.ml` for the whole comment and the diagram of
    /// the transitions, which are centralized in
    /// `MonitorMain.kill_and_maybe_restart_server`.)
    DiedConfigChanged,
}

/// `%F` of OCaml's `Printf` (what `[@@deriving show]` prints a float with):
/// `%.12g`, with a `.` added when that looks like an integer.
fn ocaml_float(f: f64) -> String {
    let fmt = c"%.12g";
    let mut buf = vec![0u8; 64];
    // SAFETY: `buf` is writable for its length, which is passed; the format
    // takes one double.
    let n = unsafe {
        libc::snprintf(
            buf.as_mut_ptr() as *mut libc::c_char,
            buf.len(),
            fmt.as_ptr(),
            f,
        )
    };
    buf.truncate((n.max(0) as usize).min(buf.len() - 1));
    let s = String::from_utf8_lossy(&buf).into_owned();
    if s.bytes().all(|b| b == b'-' || b.is_ascii_digit()) {
        s + "."
    } else {
        s
    }
}

/// `show_server_process` (`[@@deriving show]`). OCaml's `Format` may break
/// a long record over lines; this is on one line (the logs only show it).
pub fn show_server_process(s: &ServerProcess) -> String {
    match s {
        ServerProcess::NotYetStarted => "Server_process.Not_yet_started".to_string(),
        ServerProcess::Alive(p) => format!(
            "(Server_process.Alive {{ Server_process.pid = {}; server_specific_files = <opaque>; start_t = {}; in_fd = <opaque>; out_fds = <opaque>; last_request_handoff = ref ({}) }})",
            p.pid,
            ocaml_float(p.start_t),
            ocaml_float(p.last_request_handoff.get())
        ),
        ServerProcess::DiedUnexpectedly(status, was_oom) => {
            let (how, code) = match status {
                ProcessStatus::WEXITED(c) => ("WEXITED", c),
                ProcessStatus::WSIGNALED(c) => ("WSIGNALED", c),
                ProcessStatus::WSTOPPED(c) => ("WSTOPPED", c),
            };
            format!(
                "(Server_process.Died_unexpectedly (<{} {}>, {}))",
                how, code, was_oom
            )
        }
        ServerProcess::DiedConfigChanged => "Server_process.Died_config_changed".to_string(),
    }
}
