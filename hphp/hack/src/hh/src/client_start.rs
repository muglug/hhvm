// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_start.ml`. See `hh/PORTING.md`.
//!
//! `type env` was ported by the `hh_client` command line (A3), the rest by
//! the client-connection assignment (D1).
//!
//! - `Unix.create_process` is `std::process::Command` (the program is
//!   looked up in `PATH` as `execvp` does, `argv.(0)` is the first
//!   argument). The pipe of `--waiting-client` is made with `pipe(2)`; its
//!   write end is inherited by the server (it is not close-on-exec), its
//!   read end is close-on-exec, as in OCaml.
//! - `Filename.quote` and `Sys_utils.null_path` are transliterated below,
//!   private (`Filename.quote` should move to `crate::rt::ocaml_filename`).
//! - `Hack_event_logger.client_start` and `invariant_violation_bug` are
//!   no-ops in the OSS build and are not made.
//! - `Monitor_connection.connect_once` is
//!   `crate::rt::protocol::monitor_connection::connect_once` (design 7.5).
//! - The exceptions that nothing catches before the catch-all handler of
//!   `hh_client` (a failed `Unix.pipe` or `open`, a protocol error, the
//!   `Exit_with Kill_error` of `Client_stop.kill_server`) are returned:
//!   [`ClientStartError`].

use std::io::BufRead;
use std::os::fd::FromRawFd;
use std::os::fd::OwnedFd;
use std::os::unix::process::CommandExt;

use crate::client_stop;
use crate::connection_tracker;
use crate::exit;
use crate::exit_status;
use crate::exit_status::ExitWith;
use crate::hh_logger;
use crate::path;
use crate::rt::protocol::UncaughtReadError;
use crate::rt::protocol::monitor_connection;
use crate::rt::protocol::monitor_rpc;
use crate::rt::protocol::monitor_utils;
use crate::rt::protocol::monitor_utils::ConnectToMonitorFailure;
use crate::rt::protocol::monitor_utils::ConnectionError;

/// `Sys_utils.null_path`
const NULL_PATH: &str = "/dev/null";

/// The exceptions that `main` lets through.
#[derive(Debug)]
pub enum ClientStartError {
    /// `Exit_status.Exit_with`
    ExitWith(ExitWith),
    /// A system or protocol error that nothing catches
    UncaughtReadError(UncaughtReadError),
}

impl From<ExitWith> for ClientStartError {
    fn from(e: ExitWith) -> Self {
        ClientStartError::ExitWith(e)
    }
}

impl From<UncaughtReadError> for ClientStartError {
    fn from(e: UncaughtReadError) -> Self {
        ClientStartError::UncaughtReadError(e)
    }
}

/// What is the path to the hh_server binary?
/// 1. If HH_SERVER_PATH environment variable is defined, use this (even if it doesn't exist on disk!)
/// 2. Otherwise, if "dirname(realpath(executable_name))/hh_server" exists then use this
/// 3. Otherwise, use unqualified "hh_server" (hence search on PATH).
///
/// The third case is currently what happens for "hh switch buck2"
///
/// Rust: the sibling is `hh_server` + the suffix of the running client
/// ([`crate::rt::exe_suffix`]: `hh_client_rust` looks for `hh_server_rust`).
/// A suffixed client whose sibling does not exist does not search `PATH`
/// (that could find the OCaml `hh_server`, or an `hh_server_rust` of another
/// installation): it returns the missing path, so starting the server fails
/// as the OCaml's does with no `hh_server` on `PATH` ("Server launched with
/// the following command:" naming that path, then "Could not start
/// hh_server!"). An unsuffixed client behaves exactly as the OCaml.
pub fn get_hhserver_path() -> String {
    get_hhserver_path_of(
        std::env::var("HH_SERVER_PATH").ok(),
        &path::executable_name(),
    )
}

/// [`get_hhserver_path`] for a given `$HH_SERVER_PATH` and
/// `Sys.executable_name`.
pub fn get_hhserver_path_of(hh_server_path: Option<String>, executable_name: &str) -> String {
    match hh_server_path {
        Some(p) => {
            hh_logger::log(&format!("For hh_server path, using HH_SERVER_PATH={}", p));
            p
        }
        None => {
            let suffix = crate::rt::exe_suffix::suffix_of_executable(executable_name);
            let exe_name = format!("hh_server{}", suffix);
            // Path.executable_name is an alias for Sys.executable_name. Its documentation is quite vague:
            // "This name may be absolute or relative to the current directory, depending on the platform
            // and whether the program was compiled to bytecode or a native executable." In my testing
            // on native ocaml binaries on CentOS, it produces the fully-qualified realpath of the executable,
            // i.e. it digs through symlinks.
            let server_next_to_client =
                crate::rt::exe_suffix::sibling_of(executable_name, "hh_server");
            if std::path::Path::new(&server_next_to_client).exists() {
                hh_logger::log(&format!(
                    "For hh_server path, found it adjacent to {}",
                    executable_name
                ));
                server_next_to_client
            } else if !suffix.is_empty() {
                hh_logger::log(&format!(
                    "For hh_server path, {} does not exist; not searching PATH for {}",
                    server_next_to_client, exe_name
                ));
                server_next_to_client
            } else {
                hh_logger::log(&format!(
                    "For hh_server path, will do unqualified search for {}",
                    exe_name
                ));
                exe_name
            }
        }
    }
}

/// `Client_start.env`
#[derive(Clone, Debug, PartialEq)]
pub struct Env {
    pub root: path::T,
    pub from: String,
    pub no_load: bool,
    pub watchman_debug_logging: bool,
    pub silent: bool,
    pub exit_on_failure: bool,
    pub ignore_hh_version: bool,
    pub save_64bit: Option<String>,
    pub save_human_readable_64bit_dep_map: Option<String>,
    pub saved_state_ignore_hhconfig: bool,
    pub prechecked: Option<bool>,
    pub mini_state: Option<String>,
    pub config: Vec<(String, String)>,
    pub custom_hhi_path: Option<String>,
    pub custom_telemetry_data: Vec<(String, String)>,
    pub allow_non_opt_build: bool,
    pub preexisting_warnings: bool,
}

/// `Unix.open_process_in cmd |> In_channel.input_line` (any exception is
/// `None`), and the status of `Unix.close_process_in`.
fn open_process_in_first_line(cmd: &str) -> (Option<String>, Option<std::process::ExitStatus>) {
    match std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg(cmd)
        .stdin(std::process::Stdio::inherit())
        .stdout(std::process::Stdio::piped())
        .spawn()
    {
        Err(_) => (None, None),
        Ok(mut child) => {
            let mut line = String::new();
            let first_line = match child.stdout.take() {
                None => None,
                Some(stdout) => {
                    let mut reader = std::io::BufReader::new(stdout);
                    match reader.read_line(&mut line) {
                        Ok(0) | Err(_) => None,
                        Ok(_) => {
                            if line.ends_with('\n') {
                                line.pop();
                            }
                            Some(line)
                        }
                    }
                }
            };
            let status = child.wait().ok();
            (first_line, status)
        }
    }
}

/// Sometimes systemd-run is available but we can't use it. For example, the
/// systemd might not have a proper working user session, so we might not be
/// able to run commands via systemd-run as a user process
fn can_run_systemd() -> bool {
    // Verify systemd-run is in the path
    let (systemd_binary, _) = open_process_in_first_line("which systemd-run 2> /dev/null");
    if systemd_binary.is_none() {
        false
    } else {
        // Use `timeout` in case it hangs mysteriously.
        // `--quiet` only suppresses stdout.
        let (_, status) = open_process_in_first_line(
            "timeout 1 systemd-run --scope --quiet --user -- true 2> /dev/null",
        );
        // If all goes right, `systemd-run` will return immediately with exit code 0
        // and run `true` asynchronously as a service. If it goes wrong, it will exit
        // with a non-zero exit code
        matches!(status.and_then(|s| s.code()), Some(0))
    }
}

/// `Filename.quote` (Unix): between single quotes, a single quote written
/// `'\''`.
fn filename_quote(s: &str) -> String {
    let mut b = String::with_capacity(s.len() + 20);
    b.push('\'');
    for c in s.chars() {
        if c == '\'' {
            b.push_str("'\\''");
        } else {
            b.push(c);
        }
    }
    b.push('\'');
    b
}

/// `Unix.pipe ()`: (read end, write end), neither close-on-exec.
fn unix_pipe() -> std::io::Result<(OwnedFd, OwnedFd)> {
    let mut fds = [0 as libc::c_int; 2];
    // SAFETY: `fds` has room for the two descriptors `pipe` writes.
    if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: both descriptors were just made, and are owned here only.
    Ok(unsafe { (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])) })
}

/// `Unix.set_close_on_exec`
fn set_close_on_exec(fd: &OwnedFd) {
    use std::os::fd::AsRawFd;
    // SAFETY: `fd` is a valid descriptor.
    unsafe {
        libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC);
    }
}

/// The failure of the `try` of `start_server` (or of its non-zero exit).
fn could_not_start(silent: bool, exit_on_failure: bool) {
    if !silent {
        eprint!("Could not start hh_server!\n");
    }
    if exit_on_failure {
        exit::exit(None, None, None, exit_status::T::ServerAlreadyExists)
    }
}

/// A failed `Unix.pipe` or `open` (`Unix.Unix_error`) is the `Err`.
pub fn start_server(env: &Env) -> Result<(), UncaughtReadError> {
    let Env {
        root,
        from,
        no_load,
        watchman_debug_logging,
        silent,
        exit_on_failure,
        ignore_hh_version,
        save_64bit,
        save_human_readable_64bit_dep_map,
        saved_state_ignore_hhconfig,
        prechecked,
        mini_state,
        config,
        custom_hhi_path,
        custom_telemetry_data,
        allow_non_opt_build,
        preexisting_warnings,
    } = env;
    // Create a pipe for synchronization with the server: we will wait
    // until the server finishes its initialisation phase.
    let (in_fd, out_fd) = match unix_pipe() {
        Ok(fds) => fds,
        Err(e) => {
            return Err(UncaughtReadError(
                crate::rt::ocaml_unix::unix_error_to_string(&e, "pipe", ""),
            ));
        }
    };
    set_close_on_exec(&in_fd);
    let ic = std::io::BufReader::new(std::fs::File::from(in_fd));
    let serialize_key_value_options = |option: &str, keyvalues: &[(String, String)]| {
        keyvalues
            .iter()
            .flat_map(|(key, value)| vec![option.to_string(), format!("{}={}", key, value)])
            .collect::<Vec<String>>()
    };
    let hh_server = get_hhserver_path();
    let out_fd_number = {
        use std::os::fd::AsRawFd;
        // `Sys_utils.fd_to_int_naughty`
        out_fd.as_raw_fd()
    };
    let hh_server_args: Vec<String> = [
        vec![hh_server.clone(), "-d".to_string(), path::to_string(root)],
        if from.is_empty() {
            vec![]
        } else {
            vec!["--from".to_string(), from.clone()]
        },
        match mini_state {
            None => vec![],
            Some(state) => vec!["--with-mini-state".to_string(), state.clone()],
        },
        if *no_load {
            vec!["--no-load".to_string()]
        } else {
            vec![]
        },
        if *watchman_debug_logging {
            vec!["--watchman-debug-logging".to_string()]
        } else {
            vec![]
        },
        // If the client starts up a server monitor process, the output of that
        // bootup is passed to this FD - so this FD needs to be threaded
        // through the server monitor process then to the typechecker process.
        //
        // Note: Yes, the FD is available in the monitor process as well, but
        // it doesn't, and shouldn't, use it.
        vec!["--waiting-client".to_string(), out_fd_number.to_string()],
        if *ignore_hh_version {
            vec!["--ignore-hh-version".to_string()]
        } else {
            vec![]
        },
        if *saved_state_ignore_hhconfig {
            vec!["--saved-state-ignore-hhconfig".to_string()]
        } else {
            vec![]
        },
        match save_64bit {
            None => vec![],
            Some(dest) => vec!["--save-64bit".to_string(), dest.clone()],
        },
        match save_human_readable_64bit_dep_map {
            None => vec![],
            Some(dest) => vec!["--save-human-readable-64bit-dep-map".to_string(), dest.clone()],
        },
        vec![],
        match prechecked {
            Some(true) => vec!["--prechecked".to_string()],
            _ => vec![],
        },
        match prechecked {
            Some(false) => vec!["--no-prechecked".to_string()],
            _ => vec![],
        },
        serialize_key_value_options("--config", config),
        match custom_hhi_path {
            None => vec![],
            Some(dest) => vec!["--custom-hhi-path".to_string(), dest.clone()],
        },
        serialize_key_value_options("--custom-telemetry-data", custom_telemetry_data),
        if *allow_non_opt_build {
            vec!["--allow-non-opt-build".to_string()]
        } else {
            vec![]
        },
        if *preexisting_warnings {
            vec!["--preexisting-warnings".to_string()]
        } else {
            vec![]
        },
    ]
    .concat();
    // (Outside the `try`: an error is not caught.)
    let (stdin, stdout, stderr): (std::process::Stdio, std::process::Stdio, std::process::Stdio) =
        if *silent {
            let nfd = (|| {
                let nfd = std::fs::OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(NULL_PATH)?;
                Ok::<_, std::io::Error>((nfd.try_clone()?, nfd.try_clone()?, nfd))
            })();
            match nfd {
                Ok((a, b, c)) => (a.into(), b.into(), c.into()),
                Err(e) => {
                    return Err(UncaughtReadError(
                        crate::rt::ocaml_unix::unix_error_to_string(&e, "open", NULL_PATH),
                    ));
                }
            }
        } else {
            (
                std::process::Stdio::inherit(),
                std::process::Stdio::inherit(),
                std::process::Stdio::inherit(),
            )
        };
    let res = (|| -> Result<std::process::ExitStatus, ()> {
        let (exe, args) = if can_run_systemd() {
            // launch command
            // systemd-run    (creates a transient cgroup)
            //    --scope     (allows synchronous execution of hh_server)
            //    --user      (specifies this to be a user instance)
            //    --quiet     (suppresses output to stdout)
            //    --slice=hack.slice   (puts created units under hack.slice)
            //    hh_server <hh_server args>
            let systemd_exe = "systemd-run";
            let systemd_args = [
                systemd_exe,
                "--scope",
                "--user",
                "--quiet",
                "--slice=hack.slice",
            ]
            .map(|s| s.to_string());
            (
                systemd_exe.to_string(),
                [systemd_args.to_vec(), hh_server_args.clone()].concat(),
            )
        } else {
            (hh_server.clone(), hh_server_args.clone())
        };
        if !*silent {
            eprint!(
                "Server launched with the following command:\n\t{}\n",
                args.iter()
                    .map(|a| filename_quote(a))
                    .collect::<Vec<_>>()
                    .join(" ")
            );
        }
        let mut child = std::process::Command::new(&exe)
            .arg0(&args[0])
            .args(&args[1..])
            .stdin(stdin)
            .stdout(stdout)
            .stderr(stderr)
            .spawn()
            .map_err(|_| ())?;
        // `Unix.close out_fd`
        drop(out_fd);
        // `Sys_utils.waitpid_non_intr [] server_pid`
        child.wait().map_err(|_| ())
    })();
    match res {
        Ok(status) => match status.code() {
            Some(0) => {
                // `assert (String.equal (Stdlib.input_line ic) Monitor_utils.ready)`:
                // an `End_of_file` or an `Assert_failure` goes to the `with _`.
                let mut ic = ic;
                let mut line = String::new();
                let ready = match ic.read_line(&mut line) {
                    Ok(0) | Err(_) => false,
                    Ok(_) => {
                        if line.ends_with('\n') {
                            line.pop();
                        }
                        line == monitor_utils::ready
                    }
                };
                if !ready {
                    could_not_start(*silent, *exit_on_failure)
                }
                // `Stdlib.close_in ic`
            }
            Some(i) => {
                if !*silent {
                    eprint!(
                        "Starting hh_server failed. Exited with status code: {}!\n",
                        i
                    );
                }
                if *exit_on_failure {
                    exit::exit(None, None, None, exit_status::T::ServerAlreadyExists)
                }
            }
            None => could_not_start(*silent, *exit_on_failure),
        },
        Err(()) => could_not_start(*silent, *exit_on_failure),
    }
    Ok(())
}

fn should_start(env: &Env) -> Result<bool, ClientStartError> {
    let root_s = path::to_string(&env.root);
    let handoff_options = monitor_rpc::HandoffOptions {
        force_dormant_start: false,
        pipe_type: monitor_rpc::PipeType::Default,
    };
    let tracker = connection_tracker::create();
    hh_logger::log(&format!(
        "[{}] ClientStart.should_start",
        connection_tracker::log_id(&tracker)
    ));
    Ok(match monitor_connection::connect_once(tracker, 3, true, &env.root, handoff_options)? {
        Ok(_conn) => false,
        Err(ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
            server_exists: false,
            ..
        }))
        | Err(ConnectionError::BuildIdMismatchedMonitorWillTerminate(_))
        | Err(ConnectionError::ServerDied) => true,
        Err(ConnectionError::BuildIdMismatchedClientMustTerminate(info))
            if monitor_utils::is_other_implementation(&info) =>
        {
            // (Not in the OCaml: the monitor of the other implementation,
            // which this client does not replace:
            // `monitor_utils::cross_implementation_policy`.)
            eprint!("{}", monitor_utils::other_implementation_message(&info, &root_s));
            return Err(ExitWith(exit_status::T::BuildIdMismatch).into());
        }
        Err(ConnectionError::BuildIdMismatchedClientMustTerminate(_)) => {
            // `Hack_event_logger.invariant_violation_bug "we requested
            // terminate_monitor_on_version_mismatch"`: a no-op in the OSS
            // build.
            eprint!("Internal error. Please try `hh stop`\n");
            false
        }
        Err(ConnectionError::ServerDormant) | Err(ConnectionError::ServerDormantOutOfRetries) => {
            eprint!("Server already exists but is dormant");
            false
        }
        Err(ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
            server_exists: true,
            ..
        })) => {
            eprint!("Replacing unresponsive server for {}\n", root_s);
            client_stop::kill_server(&env.root, &env.from)?;
            true
        }
    })
}

pub fn main(env: &Env) -> Result<exit_status::T, ClientStartError> {
    // `Hack_event_logger.client_start ()`: a no-op in the OSS build.

    // TODO(ljw): There are some race conditions here. (See `client_start.ml`:
    // two `hh start` at once; a `hh start` during another's short delay
    // before it listens; an LSP client that starts a server while `hh
    // restart` does.) The root problem is that should_start assumes an
    // invariant that "if hh_server monitor is busy then it has failed and
    // should be shut down." This invariant isn't true.
    Ok(if should_start(env)? {
        start_server(env)?;
        exit_status::T::NoError
    } else {
        if !env.silent {
            eprint!(
                "Error: Server already exists for {}\nUse hh_client restart if you want to kill it and start a new one\n",
                path::to_string(&env.root)
            );
        }
        exit_status::T::ServerAlreadyExists
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quote() {
        assert_eq!(filename_quote("a b"), "'a b'");
        assert_eq!(filename_quote("it's"), "'it'\\''s'");
        assert_eq!(filename_quote(""), "''");
    }

    /// A temp directory with fake executables (`#!/bin/sh` scripts) named
    /// `names`.
    fn bin_dir(name: &str, names: &[&str]) -> String {
        use std::os::unix::fs::PermissionsExt;
        let d = std::env::temp_dir().join(format!("hh_client_start_{}_{}", name, std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        for n in names {
            let f = d.join(n);
            std::fs::write(&f, "#!/bin/sh\nexit 0\n").unwrap();
            std::fs::set_permissions(&f, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        path::make(&d.to_string_lossy())
    }

    #[test]
    fn hhserver_path() {
        // HH_SERVER_PATH first, even if it does not exist.
        let d = bin_dir("env", &["hh_client_rust", "hh_server_rust"]);
        assert_eq!(
            get_hhserver_path_of(Some("/nonexistent/hh_server".to_string()), &format!("{d}/hh_client_rust")),
            "/nonexistent/hh_server"
        );
        // The suffixed sibling, not the OCaml one next to it.
        let d = bin_dir("both", &["hh_client", "hh_server", "hh_client_rust", "hh_server_rust"]);
        assert_eq!(get_hhserver_path_of(None, &format!("{d}/hh_client_rust")), format!("{d}/hh_server_rust"));
        assert_eq!(get_hhserver_path_of(None, &format!("{d}/hh_client")), format!("{d}/hh_server"));
        // Suffixed, sibling missing: the missing path, not `hh_server` nor a
        // PATH search.
        let d = bin_dir("missing", &["hh_client_rust", "hh_server"]);
        assert_eq!(get_hhserver_path_of(None, &format!("{d}/hh_client_rust")), format!("{d}/hh_server_rust"));
        // Unsuffixed, sibling missing: the OCaml's unqualified search.
        let d2 = bin_dir("unsuffixed", &["hh_client"]);
        assert_eq!(get_hhserver_path_of(None, &format!("{d2}/hh_client")), "hh_server");
        for d in [d, d2] {
            std::fs::remove_dir_all(&d).unwrap();
        }
    }
}
