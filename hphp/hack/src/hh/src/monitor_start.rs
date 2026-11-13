// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/monitor_start.ml`. See `hh/PORTING.md`.
//!
//! Owned by **MON** (plan §3.1).
//!
//! This runs hh server in 1 of 3 ways:
//! 1) Runs hh server in-process (check mode)
//! 2) Runs a ServerMonitor in-process which will pass connections to a
//!    daemonized hh server (non-detached mode).
//! 3) Daemonizes a ServerMonitor which will pass connections to a daemonized
//!    hh_server (detached mode).
//!
//! The modes that save or load state (`--save-naming`, `--save-64bit`,
//! `--write-symbol-info`, `--with-mini-state`), and other hhi files
//! (`--custom-hhi-path`) in check mode, are not ported: for those [`not_ported`] says so on
//! stderr and exits with `Input_error` (10), before anything is done. The
//! telemetry (`Hack_event_logger`) is a no-op, as in the OSS build.

use std::time::Instant;

use crate::exception;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::informant;
use crate::lock;
use crate::monitor_main;
use crate::path;
use crate::random_id;
use crate::rt::daemonize;
use crate::rt::protocol::monitor_utils::MonitorConfig;
use crate::server_args;
use crate::server_args::ServerArgsError;
use crate::server_config;
use crate::server_controller;
use crate::server_files;
use crate::server_main;
use crate::server_progress;

/// What the port of `hh_server` does not have, of what `options` asks for.
pub fn not_ported(options: &server_args::Options) -> Option<&'static str> {
    if server_args::write_symbol_info(options).is_some() {
        Some("--write-symbol-info")
    } else if server_args::with_saved_state(options).is_some() {
        Some("--with-mini-state")
    } else if server_args::save_naming_filename(options).is_some() {
        Some("--save-naming")
    } else if server_args::save_64bit(options).is_some() {
        Some("--save-64bit")
    } else if server_args::check_mode(options) && server_args::custom_hhi_path(options).is_some() {
        // (The check reads the hhi files from the binary.)
        Some("--custom-hhi-path in check mode")
    } else {
        None
    }
}

/// Says that `what` is not ported, and exits with `Input_error`.
fn exit_not_ported(what: &str) -> ! {
    eprint!("hh_server: {} is not ported to Rust yet\n", what);
    exit::exit(None, None, None, exit_status::T::InputError)
}

/// An exception of OCaml that `start` catches with `exn ->`.
fn uncaught(e: impl std::fmt::Debug + Send + 'static) -> ! {
    exit::exit(
        None,
        None,
        None,
        exit_status::T::UncaughtException(exception::wrap(e)),
    )
}

/// `make_tmp_dir ()`: a new directory `files_XXXXXX` of
/// `Global_config.tmp_dir`, the `Tmp` prefix of `Relative_path`.
fn make_tmp_dir() {
    let tmpdir = path::make(&crate::tmp::temp_dir(&crate::global_config::tmp_dir, "files"));
    crate::relative_path::set_path_prefix(
        crate::relative_path::Prefix::Tmp,
        std::path::Path::new(&path::to_string(&tmpdir)),
    );
}

/// `Hhi.get_hhi_root ()` (`hhi/hhi.ml`): extracts the hhi files into a new
/// directory `hhi_XXXXXX` of `Global_config.tmp_dir` (`$HH_TMPDIR`, or
/// `/tmp/hh_server`), which names them (the `Hhi` prefix of
/// `Relative_path`, which the paths of the JSON output show). (The check
/// reads the hhi files from the binary, not from there.)
pub fn hhi_get_hhi_root() -> path::T {
    let tmpdir = path::make(&crate::tmp::temp_dir(&crate::global_config::tmp_dir, "hhi"));
    // (`Sys_utils.write_file` raises `Sys_error`.)
    if let Err(e) = hhi::write_hhi_files(std::path::Path::new(&path::to_string(&tmpdir))) {
        uncaught(crate::sys_utils::SysError(e.to_string()))
    }
    crate::relative_path::set_path_prefix(
        crate::relative_path::Prefix::Hhi,
        std::path::Path::new(&path::to_string(&tmpdir)),
    );
    tmpdir
}

/// The hhi root of `options`: `--custom-hhi-path` (`Hhi.set_custom_hhi_root`),
/// or a new one ([`hhi_get_hhi_root`]). As `Monitor_start` and
/// `Server_main.setup_hhi_root` do it. (The daemon's typechecker reads the
/// hhi files from the binary: SRV's.)
fn hhi_root_of_options(options: &server_args::Options) -> path::T {
    match server_args::custom_hhi_path(options) {
        None => hhi_get_hhi_root(),
        Some(p) => {
            let is_dir = std::path::Path::new(&p).is_dir();
            if is_dir {
                hh_logger::log(&format!("Custom hhi directory set to {}.", p));
                let root = path::make(&p);
                crate::relative_path::set_path_prefix(
                    crate::relative_path::Prefix::Hhi,
                    std::path::Path::new(&path::to_string(&root)),
                );
                root
            } else {
                hh_logger::log(&format!("Custom hhi directory {} not found.", p));
                exit::exit(None, None, None, exit_status::T::InputError)
            }
        }
    }
}

/// `Server_main.setup_hhi_root options`: restore hhi files every time the
/// server restarts in case the tmp folder changes.
pub fn setup_hhi_root(options: &server_args::Options) -> path::T {
    hhi_root_of_options(options)
}

/// `Sys_utils.redirect_stdout_and_stderr_to_file filename`: `freopen
/// filename "w" stdout`, then `dup2 stdout stderr`.
fn redirect_stdout_and_stderr_to_file(filename: &str) -> std::io::Result<()> {
    use std::io::Write;
    use std::os::fd::AsRawFd;
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
    let f = crate::rt::ocaml_unix::openfile_with_umask(
        filename,
        &[
            crate::rt::ocaml_unix::OpenFlag::OWronly,
            crate::rt::ocaml_unix::OpenFlag::OCreat,
            crate::rt::ocaml_unix::OpenFlag::OTrunc,
        ],
        0o666,
        0o022,
    )?;
    // SAFETY: `dup2` onto the standard descriptors.
    unsafe {
        if libc::dup2(f.as_raw_fd(), 1) < 0 {
            return Err(std::io::Error::last_os_error());
        }
        if libc::dup2(1, 2) < 0 {
            return Err(std::io::Error::last_os_error());
        }
    }
    Ok(())
}

/// Main method of the server monitor daemon. The daemon is responsible for
/// listening to socket requests from hh_client, checking Build ID, and relaying
/// requests to the typechecker process.
pub fn monitor_daemon_main(options: &server_args::Options, start: Instant) -> ! {
    if let Some(what) = not_ported(options) {
        exit_not_ported(what)
    }
    // (`Startup_initializer.init ()`: nothing to do.)
    let www_root = server_args::root(options);
    server_progress::set_root(www_root.clone());

    // Check mode: --check means we'll start up the server and it will do a typecheck
    // and then terminate; in the absence of that flag, (1) if a monitor was already running
    // then we will exit immediately, and avoid side-effects like cycling the logfile;
    // (2) otherwise we'll start up the server and it will continue to run
    // and handle requests.
    if !server_args::check_mode(options) {
        let lock_file = server_files::lock_file(&www_root);
        if !lock::grab(&lock_file) {
            eprint!("Monitor lock file already exists: {}\n", lock_file);
            exit::exit(None, None, None, exit_status::T::NoError)
        }
    }

    // Daemon mode (should_detach): --daemon means the caller already spawned
    // us in a new process, and it's now our responsibility to establish a logfile
    // and redirect stdout/err to it; in the absence of that flag, we'll just continue
    // to write to stdout/err as normal.
    if server_args::should_detach(options) {
        let log_link = server_files::monitor_log_link(&www_root);
        let _ = std::fs::rename(&log_link, format!("{}.old", log_link));
        let res = crate::sys_utils::make_link_of_timestamped(&log_link)
            .and_then(|log_file_path| redirect_stdout_and_stderr_to_file(&log_file_path));
        if let Err(e) = res {
            eprint!(
                "Can't write to logfile: {}\n",
                crate::rt::ocaml_unix::unix_error_to_string(&e, "open", "")
            );
        }
    }

    crate::relative_path::set_path_prefix(
        crate::relative_path::Prefix::Root,
        std::path::Path::new(&path::to_string(&www_root)),
    );
    // (`Server_load_flag.set_no_load`: the flag is read from the options.)
    let init_id = random_id::short_string();
    hh_logger::log(&format!("MonitorStart. Monitor init_id: {}", init_id));
    server_config::warn_on_invalid_config_keys(&server_args::config(options));
    let (config, local_config) = match server_config::load(
        false,
        &server_args::from(options),
        &server_args::config(options),
    ) {
        Ok(configs) => configs,
        Err(e) => uncaught(e),
    };
    // (`Hack_event_logger.init_monitor`, and the hook of `log_monitor_exit`
    // that logs to it: no-ops in OSS.)
    crate::rt::ocaml_sys::set_signal(
        libc::SIGPIPE,
        crate::rt::ocaml_sys::SignalBehavior::SignalHandle(std::sync::Arc::new(|i| {
            hh_logger::log(&format!("SIGPIPE({})", i))
        })),
    );

    // SAFETY: `setsid` takes no argument; its failure (already a group
    // leader) is ignored, as OCaml's `Unix_error`.
    unsafe {
        libc::setsid();
    }
    make_tmp_dir();

    let hhi_root = hhi_root_of_options(options);

    // Now that we've got an exclusive lock and all globals have been initialized:
    server_progress::write(None, None, "monitor initializing...");
    exit::add_hook_upon_clean_exit(|_finale_data| server_progress::try_delete());

    if server_args::check_mode(options) {
        hh_logger::log("Will run once in check mode then exit.");
        server_main::run_once(options, &config, &local_config, start, &hhi_root)
    } else {
        let current_version = server_config::version(&config);
        let waiting_client = server_args::waiting_client(options);
        let crate::server_local_config::watchman::T {
            debug_logging,
            subscribe: allow_subscriptions,
            ..
        } = local_config.watchman.clone();
        let informant_options = informant::Options {
            root: server_args::root(options),
            allow_subscriptions,
            use_dummy: local_config.use_dummy_informant,
            watchman_debug_logging: server_args::watchman_debug_logging(options) || debug_logging,
            use_eden: local_config.edenfs_informant_enabled,
            min_distance_restart: local_config.informant_min_distance_restart,
            ignore_hh_version: server_args::ignore_hh_version(options),
            is_saved_state_precomputed: matches!(
                server_args::with_saved_state(options),
                Some(server_args::SavedStateTarget::SavedStateTargetInfo(_))
            ),
        };
        let res = monitor_main::start_monitoring(
            current_version,
            waiting_client,
            local_config.max_purgatory_clients,
            options.clone(),
            &informant_options,
            MonitorConfig {
                socket_file: server_files::socket_file(&www_root),
                lock_file: server_files::lock_file(&www_root),
                server_log_file: server_files::log_link(&www_root),
                monitor_log_file: server_files::monitor_log_link(&www_root),
            },
        );
        // `~finally:Server_progress.try_delete`
        server_progress::try_delete();
        match res {
            Ok(never) => match never {},
            // `exn -> Exit.exit (Exit_status.Uncaught_exception ...)`
            Err(e) => uncaught(e),
        }
    }
}

/// The name of the entry point of the detached monitor
/// (`Monitor_start.daemon_entry`).
pub const MONITOR_ENTRY: &str = "monitor_daemon_main";

/// The detached monitor: `daemon_entry`'s function.
fn monitor_daemon_entry(param: &[u8], _channels: (std::os::fd::RawFd, std::os::fd::RawFd)) {
    let options: server_args::Options = daemonize::decode_param(param);
    monitor_daemon_main(&options, Instant::now())
}

/// Registers the entry points of `hh_server`: the detached monitor, and
/// `server_entry` for the typechecker server
/// ([`server_controller::server_daemon_main`]; a test gives another).
pub fn register_entry_points(server_entry: daemonize::EntryFn) {
    if !daemonize::is_registered(MONITOR_ENTRY) {
        daemonize::register_entry_point(MONITOR_ENTRY, monitor_daemon_entry);
    }
    if !daemonize::is_registered(server_controller::SERVER_ENTRY) {
        daemonize::register_entry_point(server_controller::SERVER_ENTRY, server_entry);
    }
}

/// `Monitor_start.start ()`: the toplevel of `hh_server`. Either starts a
/// monitor daemon (which will spawn a typechecker daemon), or just runs the
/// typechecker if detachment not enabled.
pub fn start() -> ! {
    start_with_server_entry(server_controller::server_daemon_main)
}

/// [`start`], where the typechecker server is `server_entry`.
pub fn start_with_server_entry(server_entry: daemonize::EntryFn) -> ! {
    let start = Instant::now();
    // This avoids dying if SIGUSR{1,2} is received by accident:
    unsafe {
        libc::signal(libc::SIGUSR1, libc::SIG_IGN);
        libc::signal(libc::SIGUSR2, libc::SIG_IGN);
    }
    // This call might not return:
    register_entry_points(server_entry);
    daemonize::check_entry_point();
    // (`Cgroup_profiler`, `Startup_initializer.init`, `Proc.get_proc_stack`:
    // for the telemetry only.)
    let options = match server_args::parse_options() {
        Ok(options) => options,
        // `Arg.Bad` of a malformed `--with-mini-state`, `Incorrect_format`,
        // what `Cli_args` and `Wwwroot` raise: `exn -> Exit.exit
        // (Exit_status.Uncaught_exception ...)`.
        Err(ServerArgsError::Bad(e)) => uncaught(e),
        Err(ServerArgsError::IncorrectFormat(e)) => uncaught(e),
        Err(ServerArgsError::CliArgs(e)) => uncaught(format!("{:?}", e)),
        Err(ServerArgsError::SysError(e)) => uncaught(e),
        #[cfg(test)]
        Err(e @ ServerArgsError::ArgParse(_)) => uncaught(format!("{:?}", e)),
    };
    if let Some(what) = not_ported(&options) {
        exit_not_ported(what)
    }
    if server_args::should_detach(&options) {
        let null = match daemonize::null_fd() {
            Ok(fd) => fd,
            Err(e) => uncaught(crate::rt::protocol::monitor_utils::UnixError(e, "open")),
        };
        if let Err(e) = daemonize::spawn(
            daemonize::ChannelMode::Pipe,
            None,
            (null, 1, 2),
            MONITOR_ENTRY,
            &options,
        ) {
            uncaught(crate::rt::protocol::monitor_utils::UnixError(e, "create_process"))
        }
        eprint!("Running in daemon mode\n");
        exit::exit(None, None, None, exit_status::T::NoError)
    } else {
        monitor_daemon_main(&options, start)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The modes the port does not have, and those it has.
    #[test]
    fn modes_not_ported() {
        let root = std::env::temp_dir().join(format!("hh_monitor_start_{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(root.join(".hhconfig"), "").unwrap();
        let root = root.to_string_lossy().into_owned();
        let not_ported_of = |args: &[&str]| {
            let argv: Vec<String> = std::iter::once("hh_server")
                .chain(args.iter().copied())
                .chain(std::iter::once(root.as_str()))
                .map(String::from)
                .collect();
            // (On a thread of its own: `Arg.current`, which `Arg.parse`
            // advances, is per thread.)
            let options = std::thread::spawn(move || {
                server_args::parse_options_of_argv(argv, "usage").unwrap()
            })
            .join()
            .unwrap();
            not_ported(&options)
        };
        assert_eq!(not_ported_of(&["--check"]), None);
        // `--json` implies `--check`.
        assert_eq!(not_ported_of(&["--json"]), None);
        assert_eq!(
            not_ported_of(&["--check", "--max-procs", "3", "--config", "a=b", "--from", "ci"]),
            None
        );
        assert_eq!(
            not_ported_of(&["--check", "--dump-fanout", "--no-load", "--preexisting-warnings"]),
            None
        );
        assert_eq!(not_ported_of(&[]), None);
        assert_eq!(not_ported_of(&["--daemon"]), None);
        assert!(not_ported_of(&["--write-symbol-info", "/tmp/x"]).is_some());
        assert!(not_ported_of(&["--check", "--save-naming", "/tmp/x"]).is_some());
        assert!(not_ported_of(&["--check", "--save-64bit", "/tmp/x"]).is_some());
        assert!(not_ported_of(&["--check", "--custom-hhi-path", "/tmp"]).is_some());
        assert_eq!(not_ported_of(&["--custom-hhi-path", "/tmp"]), None);
        std::fs::remove_dir_all(&root).unwrap();
    }
}
