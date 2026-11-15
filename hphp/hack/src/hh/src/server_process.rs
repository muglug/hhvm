// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/server_process.ml`.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::os::fd::RawFd;

use crate::monitor_rpc::PipeType;
use crate::rt::ocaml_unix::ProcessStatus;
use crate::server_command_types::ServerSpecificFiles;

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

/// `show_server_process` (`[@@deriving show]`). OCaml's `Format` may break
/// a long record over lines; this is on one line (the logs only show it).
pub fn show_server_process(s: &ServerProcess) -> String {
    match s {
        ServerProcess::NotYetStarted => "Server_process.Not_yet_started".to_string(),
        ServerProcess::Alive(p) => format!(
            "(Server_process.Alive {{ Server_process.pid = {}; server_specific_files = <opaque>; start_t = {}; in_fd = <opaque>; out_fds = <opaque>; last_request_handoff = ref ({}) }})",
            p.pid,
            crate::rt::ocaml_stdlib::string_of_float(p.start_t),
            crate::rt::ocaml_stdlib::string_of_float(p.last_request_handoff.get())
        ),
        ServerProcess::DiedUnexpectedly(status, was_oom) => {
            let (how, code) = match status {
                ProcessStatus::WExited(c) => ("WEXITED", c),
                ProcessStatus::WSignaled(c) => ("WSIGNALED", c),
                ProcessStatus::WStopped(c) => ("WSTOPPED", c),
            };
            format!(
                "(Server_process.Died_unexpectedly (<{} {}>, {}))",
                how, code, was_oom
            )
        }
        ServerProcess::DiedConfigChanged => "Server_process.Died_config_changed".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Unix.process_status` is shown with the OCaml constructor names.
    #[test]
    fn show_prints_the_ocaml_process_status() {
        assert_eq!(
            show_server_process(&ServerProcess::DiedUnexpectedly(
                ProcessStatus::WExited(3),
                false
            )),
            "(Server_process.Died_unexpectedly (<WEXITED 3>, false))"
        );
        assert_eq!(
            show_server_process(&ServerProcess::DiedUnexpectedly(
                ProcessStatus::WSignaled(9),
                true
            )),
            "(Server_process.Died_unexpectedly (<WSIGNALED 9>, true))"
        );
        assert_eq!(
            show_server_process(&ServerProcess::DiedUnexpectedly(
                ProcessStatus::WStopped(1),
                false
            )),
            "(Server_process.Died_unexpectedly (<WSTOPPED 1>, false))"
        );
    }
}
