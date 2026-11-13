// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_stop.ml`. See `hh/PORTING.md`.
//!
//! `type env` was ported by the `hh_client` command line (A3), the rest by
//! the client-connection assignment (D1).
//!
//! - `exception FailedToKill` is caught by the callers in this module: it is
//!   the `Err` of the functions that raise it. `nice_kill`'s `try ... with _`
//!   catches everything its body raises, `FailedToKill` included (so its
//!   messages are printed twice in those cases, as in OCaml): here the `Err`,
//!   the exception `connect_and_shut_down` returns (its outer `Err`, so that
//!   no panic message is printed for it), and any other panic.
//! - `Exit_status.Exit_with Kill_error`, which `do_kill` raises when both
//!   ways of killing fail, is the `Err(ExitWith(..))` of `do_kill`, `main`
//!   and `kill_server`.
//! - `Monitor_connection.connect_and_shut_down` and `server_exists` are
//!   `crate::rt::protocol::monitor_connection`'s (design 7.5): `SHUT_DOWN`
//!   asks the server itself to exit.
//! - `Sys_utils.terminate_process pid` (`Unix.kill pid Sys.sigkill`) is
//!   written out below. `Hack_event_logger.client_stop` is a no-op in the
//!   OSS build.

use std::panic::AssertUnwindSafe;

use crate::connection_tracker;
use crate::exit_status;
use crate::exit_status::ExitWith;
use crate::hh_logger;
use crate::path;
use crate::pid_log;
use crate::rt::ocaml_unix;
use crate::rt::protocol::monitor_connection as mc;
use crate::rt::protocol::monitor_utils;
use crate::rt::protocol::monitor_utils::ConnectToMonitorFailure;
use crate::rt::protocol::monitor_utils::ConnectionError;
use crate::server_files;

/// `exception FailedToKill`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FailedToKill;

/// `Client_stop.env`
#[derive(Clone, Debug, PartialEq)]
pub struct Env {
    pub root: path::T,
    pub from: String,
}

fn wait_for_death(root: &path::T, secs: isize) -> bool {
    let mut i = 0;
    while mc::server_exists(&server_files::lock_file(root)) {
        i += 1;
        if i < secs {
            std::thread::sleep(std::time::Duration::from_secs(1));
        } else {
            // `raise Exit`
            return false;
        }
    }
    true
}

fn nice_kill(env: &Env) -> Result<(), FailedToKill> {
    let root_s = path::to_string(&env.root);
    eprint!("Attempting to nicely kill server for {}\n", root_s);
    let tracker = connection_tracker::create();
    hh_logger::log(&format!(
        "[{}] ClientStop.nice_kill",
        connection_tracker::log_id(&tracker)
    ));
    let body = || -> Result<(), FailedToKill> {
        match mc::connect_and_shut_down(tracker, &env.root) {
            // An exception: the `with _` below.
            Err(_exn) => Err(FailedToKill),
            Ok(res) => match res {
                Ok(shutdown_result) => match shutdown_result {
                    monitor_utils::ShutdownResult::SHUTDOWN_VERIFIED => {
                        eprint!("Successfully killed server for {}\n", root_s);
                        Ok(())
                    }
                    monitor_utils::ShutdownResult::SHUTDOWN_UNVERIFIED => {
                        eprint!(
                            "Failed to kill server nicely for {} (Shutdown not verified)\n",
                            root_s
                        );
                        Err(FailedToKill)
                    }
                },
                Err(ConnectionError::BuildIdMismatchedMonitorWillTerminate(_)) => {
                    eprint!("Successfully killed server for {}\n", root_s);
                    Ok(())
                }
                Err(ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
                    server_exists: false,
                    ..
                })) => {
                    eprint!("No server to kill for {}\n", root_s);
                    Ok(())
                }
                Err(_) => {
                    eprint!("Failed to kill server nicely for {}\n", root_s);
                    Err(FailedToKill)
                }
            },
        }
    };
    match std::panic::catch_unwind(AssertUnwindSafe(body)) {
        Ok(Ok(())) => Ok(()),
        Ok(Err(FailedToKill)) | Err(_) => {
            eprint!("Failed to kill server nicely for {}\n", root_s);
            Err(FailedToKill)
        }
    }
}

/// `Sys_utils.terminate_process pid`: `Unix.kill pid Sys.sigkill`.
fn terminate_process(pid: isize) -> std::io::Result<()> {
    ocaml_unix::kill(pid, libc::SIGKILL)
}

fn mean_kill(env: &Env) -> Result<(), FailedToKill> {
    let root_s = path::to_string(&env.root);
    eprint!("Attempting to meanly kill server for {}\n", root_s);
    let pids = match pid_log::get_pids(&server_files::pids_file(&env.root)) {
        Ok(pids) => pids,
        Err(pid_log::FailedToGetPids) => {
            eprint!(
                "Unable to figure out pids of running Hack server. Try manually killing it with `pkill hh_server`\n"
            );
            return Err(FailedToKill);
        }
    };
    let success = (|| {
        for (pid, _reason) in &pids {
            match terminate_process(*pid) {
                Ok(()) => {}
                // no such process
                Err(e) if e.raw_os_error() == Some(libc::ESRCH) => {}
                Err(e) => {
                    // `with e -> print_endline (Exn.to_string e); false`
                    println!("{}", ocaml_unix::unix_error_to_string(&e, "kill", ""));
                    return false;
                }
            }
        }
        wait_for_death(&env.root, 3)
    })();
    if !success {
        eprint!(
            "Failed to kill server meanly for {}. Try manually killing it with `pkill hh_server`\n",
            root_s
        );
        Err(FailedToKill)
    } else {
        eprint!("Successfully killed server for {}\n", root_s);
        Ok(())
    }
}

fn do_kill(env: &Env) -> Result<(), ExitWith> {
    match nice_kill(env) {
        Ok(()) => Ok(()),
        Err(FailedToKill) => match mean_kill(env) {
            Ok(()) => Ok(()),
            Err(FailedToKill) => Err(ExitWith(exit_status::T::KillError)),
        },
    }
}

pub fn main(env: &Env) -> Result<exit_status::T, ExitWith> {
    // `Hack_event_logger.client_stop ()`: a no-op in the OSS build.
    do_kill(env)?;
    Ok(exit_status::T::NoError)
}

pub fn kill_server(root: &path::T, from: &str) -> Result<(), ExitWith> {
    do_kill(&Env {
        root: root.clone(),
        from: from.to_string(),
    })
}
