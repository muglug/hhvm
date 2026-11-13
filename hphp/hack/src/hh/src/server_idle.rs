// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_idle.ml`: the jobs the daemon runs when it is
//! idle (`Periodical` is `crate::periodical`).
//!
//! Owned by **SRV** (plan §3.1).
//!
//! The jobs with an effect are ported: the client-log rotation (every 5
//! minutes, beyond 1 MB), the exit after 7 days unused (checked daily),
//! the daily `Hhi.touch` and touch of the server's files in the tmp
//! directory. The others (`Gc.major_slice`, `Shared_mem.GC.collect`,
//! `Event_logger.recheck_disk_files`, `log_gc_stats`, `flush`) have no
//! counterpart here (plan §6 row 19) and are not registered.

#![allow(non_upper_case_globals)]

use std::sync::Mutex;

use crate::exit;
use crate::exit_status;
use crate::hhi_root;
use crate::path;
use crate::periodical;
use crate::periodical::Callback;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_files;
use crate::sys_utils;

/// `go = Periodical.check`
pub fn go(env: Env) -> Env {
    periodical::check(env)
}

/// `async f = Periodical.register_callback (Once (ref 0.0, f))`
pub fn async_(f: periodical::Job) {
    periodical::register_callback(Callback::Once(0.0, f))
}

/// We want to keep track of when the server was last used. Every few hours, we'll
/// check this variable. If the server hasn't been used for a few days, we exit.
/// (`last_client_connect = ref (Unix.time ())`, at the start of the
/// program: `None` until [`init_last_client_connect`] or a connection.)
static last_client_connect: Mutex<Option<f64>> = Mutex::new(None);

/// The value of `last_client_connect` at the start of the program.
pub fn init_last_client_connect() {
    let mut l = last_client_connect.lock().unwrap_or_else(|e| e.into_inner());
    if l.is_none() {
        *l = Some(periodical::time())
    }
}

pub fn stamp_connection() {
    *last_client_connect.lock().unwrap_or_else(|e| e.into_inner()) = Some(periodical::time())
}

/// Whether the server was last used more than a week ago.
pub fn is_unused() -> bool {
    init_last_client_connect();
    let last = last_client_connect
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .unwrap_or_else(periodical::time);
    let delta: f64 = periodical::time() - last;
    delta > periodical::one_week
}

pub fn exit_if_unused() {
    if is_unused() {
        eprintln!("Exiting server. Last used >7 days ago");
        exit::exit(None, None, None, exit_status::T::UnusedServer)
    }
}

/// We'll cycle the client-log if it gets bigger than 1Mb.
/// We do this cycling here in the server (rather than in the client)
/// to avoid races when multiple concurrent clients try to cycle it.
pub fn rotate_client_log(root: &path::T) {
    let client_log_fn = server_files::client_log(root);
    if let Ok(stat) = std::fs::metadata(&client_log_fn) {
        if stat.len() > 1024 * 1024 {
            let _ = std::fs::rename(&client_log_fn, format!("{}.old", client_log_fn));
        }
    }
}

/// Touch_existing{false} wraps Unix.lutimes, which doesn't open/close any fds, so we
/// won't lose our lock by doing this. We are only touching the top level
/// of files, however -- we don't want to do it recursively so that old
/// files under e.g. /tmp/hh_server/logs still get cleaned up.
pub fn touch_tmp_files(tmp_dir: &str, root: &path::T) {
    // (`Sys.readdir` raises when the directory cannot be read: the job
    // fails, which the OCaml does not catch; here it does nothing.)
    let Ok(entries) = std::fs::read_dir(tmp_dir) else {
        return;
    };
    for entry in entries.flatten() {
        let fn_ = crate::rt::ocaml_filename::concat(tmp_dir, &entry.file_name().to_string_lossy());
        if std::fs::metadata(&fn_).map(|m| m.is_dir()).unwrap_or(false)
            // We don't want to touch things like .watchman_failed
            || fn_.starts_with('.')
            || !server_files::is_of_root(root, &fn_)
        {
        } else {
            // `Sys_utils.try_touch`
            let _ = sys_utils::touch(
                sys_utils::TouchMode::TouchExisting {
                    follow_symlinks: false,
                },
                &fn_,
            );
        }
    }
}

/// The registered jobs (`init genv root`).
pub fn init(genv: &Genv, root: &path::T) {
    let _ = genv;
    init_last_client_connect();
    let jobs: Vec<(f64, periodical::Job)> = vec![
        (periodical::one_minute * 5., {
            let root = root.clone();
            Box::new(move |env| {
                rotate_client_log(&root);
                env
            })
        }),
        (
            periodical::one_day,
            Box::new(|env| {
                exit_if_unused();
                env
            }),
        ),
        (
            periodical::one_day,
            Box::new(|env| {
                hhi_root::touch();
                env
            }),
        ),
        (periodical::one_day, {
            let root = root.clone();
            Box::new(move |env| {
                touch_tmp_files(&crate::global_config::tmp_dir, &root);
                env
            })
        }),
    ];
    for (period, cb) in jobs {
        periodical::register_callback(Callback::Periodic(period, period, cb))
    }
}
