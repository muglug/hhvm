// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/server_controller.ml`: responsible for starting up a
//! Hack server process. Also the parameters of the server child
//! (`Server_main.params`), the global state it inherits
//! (`client_and_server/server_global_state.ml`), and the beginning of its
//! entry point (`Server_main.daemon_main` up to `daemon_main_exn`, which is
//! SRV's `server_main::daemon_main`).
//!
//! Owned by **MON** (plan §3.1).

use std::collections::BTreeMap;
use std::os::fd::RawFd;

use serde::Deserialize;
use serde::Serialize;

use crate::exception;
use crate::exit_status;
use crate::hh_logger;
use crate::relative_path;
use crate::rt::daemonize;
use crate::rt::ocaml_unix;
use crate::rt::protocol::monitor_rpc::PipeType;
use crate::server_args;
use crate::server_command_types::ServerSpecificFiles;
use crate::server_files;
use crate::server_process::ProcessData;
use crate::server_process::ProcessStatus;
use crate::server_progress;
use crate::sys_utils;

// ~~ Server_global_state ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Server_global_state.t`: what the server child gets of the monitor's
/// globals. (`logging_init` is `fun () -> ()` for the server;
/// `cgroup_initial_reading` has no counterpart; `no_load` is in the
/// options, there being no `Server_load_flag` here.)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GlobalState {
    pub saved_root: Option<String>,
    pub saved_hhi: Option<String>,
    pub saved_tmp: Option<String>,
    pub trace: bool,
    pub allowed_fixme_codes_strict: Vec<isize>,
    pub code_agnostic_fixme: bool,
    /// The sources of the regular expressions.
    pub paths_to_ignore: Vec<String>,
}

/// `Server_global_state.save`
pub fn save_global_state() -> GlobalState {
    let prefix = |p| relative_path::path_of_prefix(p).ok();
    GlobalState {
        saved_root: prefix(relative_path::Prefix::Root),
        saved_hhi: prefix(relative_path::Prefix::Hhi),
        saved_tmp: prefix(relative_path::Prefix::Tmp),
        trace: crate::typing_deps::trace.load(std::sync::atomic::Ordering::Relaxed),
        allowed_fixme_codes_strict: crate::diagnostics_state::allowed_fixme_codes_strict()
            .iter()
            .copied()
            .collect(),
        code_agnostic_fixme: crate::diagnostics_state::code_agnostic_fixme(),
        paths_to_ignore: crate::files_to_ignore::get_paths_to_ignore()
            .iter()
            .map(|r| r.as_str().to_string())
            .collect(),
    }
}

/// `Server_global_state.worker_id_str`
fn worker_id_str(worker_id: isize) -> String {
    if worker_id == 0 {
        "master".to_string()
    } else {
        format!("worker-{}", worker_id)
    }
}

/// `Server_global_state.restore state ~worker_id`
pub fn restore_global_state(state: &GlobalState, worker_id: isize) {
    hh_logger::set_id(&worker_id_str(worker_id));
    let set = |p, v: &Option<String>| {
        if let Some(v) = v {
            relative_path::set_path_prefix(p, std::path::Path::new(v));
        }
    };
    set(relative_path::Prefix::Root, &state.saved_root);
    set(relative_path::Prefix::Hhi, &state.saved_hhi);
    set(relative_path::Prefix::Tmp, &state.saved_tmp);
    crate::typing_deps::trace.store(state.trace, std::sync::atomic::Ordering::Relaxed);
    crate::diagnostics_state::set_allowed_fixme_codes_strict(
        state.allowed_fixme_codes_strict.iter().copied().collect(),
    );
    crate::diagnostics_state::set_code_agnostic_fixme(state.code_agnostic_fixme);
    crate::files_to_ignore::set_paths_to_ignore(
        state
            .paths_to_ignore
            .iter()
            .filter_map(|s| regex::Regex::new(s).ok())
            .collect(),
    );
    crate::diagnostics_state::set_allow_errors_in_default_path(false);
}

// ~~ Server_main.params and the entry of the server child ~~~~~~~~~~~~~~~~~~~

/// `Server_main.params`
#[derive(Serialize, Deserialize)]
pub struct Params {
    pub informant_managed: bool,
    pub state: GlobalState,
    pub options: server_args::Options,
    pub monitor_pid: i32,
    pub priority_in_fd: RawFd,
    pub force_dormant_start_only_in_fd: RawFd,
}

/// The name of the entry point of the server (`Server_main.entry`).
pub const SERVER_ENTRY: &str = "Server_main.daemon_main";

/// `Server_main.daemon_main params (default_ic, _default_oc)`, up to
/// `daemon_main_exn` (SRV's [`crate::server_main::daemon_main`]).
pub fn server_daemon_main(param: &[u8], (default_ic, _default_oc): (RawFd, RawFd)) {
    let Params {
        informant_managed: _,
        state,
        options,
        monitor_pid,
        priority_in_fd,
        force_dormant_start_only_in_fd,
    } = daemonize::decode_param(param);
    // Avoid leaking this fd further
    daemonize::set_close_on_exec(priority_in_fd);
    daemonize::set_close_on_exec(force_dormant_start_only_in_fd);
    let default_in_fd = default_ic;

    // Restore the root directory and other global states from monitor
    restore_global_state(&state, 0);

    crate::monitor_start::setup_hhi_root(&options);

    crate::server_main::daemon_main(
        options,
        Some(monitor_pid),
        (default_in_fd, priority_in_fd, force_dormant_start_only_in_fd),
    )
}

// ~~ Server_controller ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Sys.file_exists`
fn file_exists(p: &str) -> bool {
    std::path::Path::new(p).exists()
}

/// `start_server_daemon ~informant_managed options log_link daemon_entry`.
/// The error is the exception OCaml raises (`Unix_error` of the
/// socketpairs, or of `create_process`).
pub fn start_server_daemon(
    informant_managed: bool,
    options: &server_args::Options,
    log_link: &str,
    daemon_entry: &str,
) -> std::io::Result<ProcessData> {
    let in_fd = daemonize::null_fd()?;
    let log_fds = if server_args::should_detach(options) {
        let rotate = || -> std::io::Result<()> {
            let old_log_name = |i: usize| format!("{}.{}.old", log_link, i);
            let max_n_log_files = 20;
            for i in (1..max_n_log_files).rev() {
                if file_exists(&old_log_name(i)) {
                    std::fs::rename(old_log_name(i), old_log_name(i + 1))?;
                }
            }
            let old = format!("{}.old", log_link);
            if file_exists(&old) {
                std::fs::rename(&old, old_log_name(1))?;
            }
            if file_exists(log_link) {
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
        let fd = daemonize::fd_of_path(&log_file)?;
        (in_fd, fd, fd)
    } else {
        hh_logger::log("About to spawn typechecker daemon. Logs will go here.");
        (in_fd, 1, 2)
    };
    let start_t = ocaml_unix::gettimeofday().floor();
    let state = save_global_state();
    let monitor_pid = std::process::id() as i32;
    // Setting some additional channels between monitor and server
    let (parent_priority_fd, child_priority_fd) = daemonize::socketpair()?;
    daemonize::set_close_on_exec(parent_priority_fd);
    daemonize::clear_close_on_exec(child_priority_fd);
    let (parent_force_dormant_start_only_fd, child_force_dormant_start_only_force_fd) =
        daemonize::socketpair()?;
    daemonize::set_close_on_exec(parent_force_dormant_start_only_fd);
    daemonize::clear_close_on_exec(child_force_dormant_start_only_force_fd);
    let daemonize::Handle {
        pid,
        channels: (ic, oc),
    } = daemonize::spawn(
        daemonize::ChannelMode::Socket,
        None,
        log_fds,
        daemon_entry,
        &Params {
            informant_managed,
            state,
            options: options.clone(),
            monitor_pid,
            priority_in_fd: child_priority_fd,
            force_dormant_start_only_in_fd: child_force_dormant_start_only_force_fd,
        },
    )?;
    daemonize::close(child_priority_fd);
    daemonize::close(child_force_dormant_start_only_force_fd);
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
/// ([`SERVER_ENTRY`]); a test may start another.
pub fn start_hh_server(
    informant_managed: bool,
    options: &server_args::Options,
) -> std::io::Result<ProcessData> {
    let log_link = server_files::log_link(&server_args::root(options));
    start_server_daemon(informant_managed, options, &log_link, SERVER_ENTRY)
}

pub type ServerStartOptions = server_args::Options;

fn is_sql_exit(c: isize) -> bool {
    use exit_status::T::*;
    c == exit_status::exit_code(&SqlAssertionFailure)
        || c == exit_status::exit_code(&SqlCantopen)
        || c == exit_status::exit_code(&SqlCorrupt)
        || c == exit_status::exit_code(&SqlMisuse)
}

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
            let e = exception::wrap(crate::rt::protocol::monitor_utils::UnixError(e, "kill"));
            hh_logger::exception_(Some("Failed to violently kill server process: "), &e);
        }
    }
}

/// `Unix.waitpid [WNOHANG; WUNTRACED] pid` (retried on `EINTR`, which OCaml
/// would raise: a signal handler runs on its own thread here). The error is
/// `Unix_error (_, "waitpid", "")`.
pub fn waitpid_nohang(pid: i32) -> std::io::Result<(i32, ProcessStatus)> {
    loop {
        let mut status: libc::c_int = 0;
        // SAFETY: plain waitpid.
        let ret = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG | libc::WUNTRACED) };
        if ret < 0 {
            let e = std::io::Error::last_os_error();
            if e.raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            return Err(e);
        }
        if ret == 0 {
            return Ok((0, ProcessStatus::WEXITED(0)));
        }
        return Ok((ret, ProcessStatus::of_raw(status)));
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
        match waitpid_nohang(process.pid)? {
            (0, _) => std::thread::sleep(std::time::Duration::from_secs(1)),
            _ => return Ok(true),
        }
    }
}

pub fn wait_pid(process: &ProcessData) -> std::io::Result<(i32, ProcessStatus)> {
    waitpid_nohang(process.pid)
}

pub fn is_saved_state_precomputed(options: &ServerStartOptions) -> bool {
    server_args::is_using_precomputed_saved_state(options)
}
