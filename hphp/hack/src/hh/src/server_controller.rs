// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/server_controller.ml`: responsible for starting up a
//! Hack server process.

use std::collections::BTreeMap;

use crate::daemon;
use crate::exception;
use crate::exit_status;
use crate::hh_logger;
use crate::monitor_rpc::PipeType;
use crate::rt::ocaml_unix;
use crate::rt::ocaml_unix::ProcessStatus;
use crate::server_args;
use crate::server_command_types::ServerSpecificFiles;
use crate::server_files;
use crate::server_global_state;
use crate::server_main;
use crate::server_process::ProcessData;
use crate::server_progress;
use crate::sys_utils;

// ~~ Server_controller ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `start_server_daemon ~informant_managed options log_link daemon_entry`.
/// The error is the exception OCaml raises (`Unix_error` of the
/// socketpairs, or of `create_process`).
pub fn start_server_daemon(
    informant_managed: bool,
    options: &server_args::Options,
    log_link: &str,
    daemon_entry: &str,
) -> std::io::Result<ProcessData> {
    let in_fd = daemon::null_fd()?;
    let log_fds = if server_args::should_detach(options) {
        let rotate = || -> std::io::Result<()> {
            let old_log_name = |i: usize| format!("{}.{}.old", log_link, i);
            let max_n_log_files = 20;
            for i in (1..max_n_log_files).rev() {
                if crate::path::file_exists(&old_log_name(i)) {
                    std::fs::rename(old_log_name(i), old_log_name(i + 1))?;
                }
            }
            let old = format!("{}.old", log_link);
            if crate::path::file_exists(&old.to_string()) {
                std::fs::rename(&old, old_log_name(1))?;
            }
            if crate::path::file_exists(&log_link.to_string()) {
                std::fs::rename(log_link, &old)?;
            }
            Ok(())
        };
        let _ = rotate();
        let log_file = sys_utils::make_link_of_timestamped(log_link)?;
        hh_logger::log(&format!(
            "About to spawn typechecker daemon. Logs will go to {}\n",
            log_link
        ));
        let fd = daemon::fd_of_path(&log_file)?;
        (in_fd, fd, fd)
    } else {
        hh_logger::log("About to spawn typechecker daemon. Logs will go here.");
        (in_fd, 1, 2)
    };
    let start_t = ocaml_unix::gettimeofday().floor();
    let state = server_global_state::save();
    let monitor_pid = std::process::id() as i32;
    // Setting some additional channels between monitor and server
    let (parent_priority_fd, child_priority_fd) = crate::rt::ocaml_unix::socketpair()?;
    crate::rt::ocaml_unix::set_close_on_exec(parent_priority_fd);
    crate::rt::ocaml_unix::clear_close_on_exec(child_priority_fd);
    let (parent_force_dormant_start_only_fd, child_force_dormant_start_only_force_fd) =
        crate::rt::ocaml_unix::socketpair()?;
    crate::rt::ocaml_unix::set_close_on_exec(parent_force_dormant_start_only_fd);
    crate::rt::ocaml_unix::clear_close_on_exec(child_force_dormant_start_only_force_fd);
    let daemon::Handle {
        pid,
        channels: (ic, oc),
    } = daemon::spawn(
        daemon::ChannelMode::Socket,
        None,
        log_fds,
        daemon_entry,
        &server_main::Params {
            informant_managed,
            state,
            options: options.clone(),
            monitor_pid,
            priority_in_fd: child_priority_fd,
            force_dormant_start_only_in_fd: child_force_dormant_start_only_force_fd,
        },
    )?;
    daemon::close(child_priority_fd);
    daemon::close(child_force_dormant_start_only_force_fd);
    hh_logger::log(&format!(
        "Just started typechecker server with pid: {}.",
        pid
    ));

    // We'll write an initial progress message to guarantee that the client will
    // certainly be able to read the progress file as soon as it learns the progress filename.
    // There's a benign race as to whether our message is written first, or whether the server
    // started up quickly enough to write its initial message first. It's benign because
    // either message will communicate the right intent to the user, and in any case the server
    // will always have further progress updates to write.
    server_progress::write(None, None, "starting hh_server");

    let server = ProcessData {
        pid,
        server_specific_files: ServerSpecificFiles {
            server_finale_file: server_files::server_finale_file(pid as isize),
        },
        in_fd: ic,
        out_fds: BTreeMap::from([
            (PipeType::Default, oc),
            (PipeType::Priority, parent_priority_fd),
            (
                PipeType::ForceDormantStartOnly,
                parent_force_dormant_start_only_fd,
            ),
        ]),
        start_t,
        last_request_handoff: std::cell::Cell::new(ocaml_unix::gettimeofday().floor()),
    };
    Ok(server)
}

/// The entry point that the monitor starts servers with: the real one
/// ([`server_main::ENTRY`]); a test may start another.
pub fn start_hh_server(
    informant_managed: bool,
    options: &server_args::Options,
) -> std::io::Result<ProcessData> {
    let log_link = server_files::log_link(&server_args::root(options));
    start_server_daemon(informant_managed, options, &log_link, server_main::ENTRY)
}

pub type ServerStartOptions = server_args::Options;

fn is_sql_exit(c: isize) -> bool {
    use exit_status::T::*;
    c == exit_status::exit_code(&SqlAssertionFailure)
        || c == exit_status::exit_code(&SqlCantopen)
        || c == exit_status::exit_code(&SqlCorrupt)
        || c == exit_status::exit_code(&SqlMisuse)
}

/// Start the server. Optionally takes in the exit code of the previously
/// running server that exited.
pub fn start_server(
    informant_managed: bool,
    prior_exit_status: Option<isize>,
    options: &ServerStartOptions,
) -> std::io::Result<ProcessData> {
    match prior_exit_status {
        Some(c) if is_sql_exit(c) => start_hh_server(
            informant_managed,
            &server_args::set_no_load(options.clone(), true),
        ),
        _ => start_hh_server(informant_managed, options),
    }
}

pub fn kill_server(violently: bool, process: &ProcessData) {
    kill_server_pid(violently, process.pid)
}

/// [`kill_server`] of the process `pid`.
pub fn kill_server_pid(violently: bool, pid: i32) {
    if !violently {
        hh_logger::log(&format!("kill_server: sending SIGUSR2 to {}", pid));
        let _ = ocaml_unix::kill(pid as isize, libc::SIGUSR2);
    } else {
        hh_logger::log("Failed to send sigusr2 signal to server process. Trying violently");
        if let Err(e) = ocaml_unix::kill(pid as isize, libc::SIGKILL) {
            let e = exception::wrap(crate::monitor_utils::UnixError(e, "kill"));
            hh_logger::exception_(Some("Failed to violently kill server process: "), &e);
        }
    }
}

/// `wait_for_server_exit ~timeout_t process`: whether it exited by then.
/// The error is the `Unix_error` of `waitpid` (`ECHILD`, once reaped).
pub fn wait_for_server_exit(timeout_t: f64, process: &ProcessData) -> std::io::Result<bool> {
    loop {
        let now_t = ocaml_unix::gettimeofday();
        if now_t > timeout_t {
            return Ok(false);
        }
        match crate::rt::ocaml_unix::waitpid_nohang(process.pid)? {
            (0, _) => std::thread::sleep(std::time::Duration::from_secs(1)),
            _ => return Ok(true),
        }
    }
}

pub fn wait_pid(process: &ProcessData) -> std::io::Result<(i32, ProcessStatus)> {
    crate::rt::ocaml_unix::waitpid_nohang(process.pid)
}

pub fn is_saved_state_precomputed(options: &ServerStartOptions) -> bool {
    server_args::is_using_precomputed_saved_state(options)
}
