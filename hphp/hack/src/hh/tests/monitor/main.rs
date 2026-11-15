// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Process tests of the monitor (plan §3.1, MON): the monitor of
//! `hh::monitor_main` with a fake typechecker server, driven by the real
//! `hh_client`.
//!
//! Owned by **MON**.
//!
//! This binary is three programs (`harness = false`):
//! - with `HH_SERVER_DAEMON` set (a daemon that `Daemon.spawn` started): the
//!   entry point it names, the real monitor or the fake server;
//! - with `HH_MON_TEST_AS_SERVER=1`: `hh_server` (`Monitor_start.start`)
//!   whose typechecker is the fake server. `hh_client` starts it through
//!   `HH_SERVER_PATH`;
//! - otherwise the tests (all, or those named on the command line).
//!
//! The fake server (`HH_FAKE_SERVER`): `serve` (the default) writes
//! `[DReady] ready`, takes the clients the monitor hands it (receipt file,
//! `Hello`, answers `CHECK_LIVENESS`), exits `Server_shutting_down_due_to_sigusr2`
//! on SIGUSR2 and `Lost_parent_monitor` when the monitor is gone;
//! `exit:N` exits with `N` at once; `exit_once:N` exits with `N` if the
//! file `$HH_TMPDIR/fake_exited` is not there (and makes it), else serves.

use std::io::Read;
use std::os::fd::FromRawFd;
use std::os::fd::RawFd;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;
use std::time::Instant;

use hh::rt::protocol;
use hh::monitor_rpc;
use hh::server_main;

// ~~ The fake server ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn fake_server(param: &[u8], (default_ic, _oc): (RawFd, RawFd)) {
    let server_main::Params {
        state,
        options,
        monitor_pid,
        priority_in_fd,
        force_dormant_start_only_in_fd,
        ..
    } = hh::daemon::decode_param(param);
    hh::rt::ocaml_unix::set_close_on_exec(priority_in_fd);
    hh::rt::ocaml_unix::set_close_on_exec(force_dormant_start_only_in_fd);
    hh::server_global_state::restore(&state, 0);
    let root = hh::server_args::root(&options);
    hh::server_progress::set_root(root.clone());
    hh::hh_logger::log(&format!(
        "Fake server starting (no_load={}).",
        hh::server_args::no_load(&options)
    ));
    hh::pid_log::init(&hh::server_files::pids_file(&root));
    hh::pid_log::log(Some("monitor"), None, monitor_pid as isize);
    hh::pid_log::log(Some("main"), None, std::process::id() as isize);
    let behaviour = std::env::var("HH_FAKE_SERVER").unwrap_or_else(|_| "serve".to_string());
    let exit_with = |code: i32| -> ! {
        hh::hh_logger::log(&format!("Fake server exits with {}.", code));
        std::process::exit(code)
    };
    if let Some(n) = behaviour.strip_prefix("exit:") {
        exit_with(n.parse().unwrap())
    }
    if let Some(n) = behaviour.strip_prefix("exit_once:") {
        let marker = format!("{}/fake_exited", hh::tmp::hh_server_tmp_dir());
        if !Path::new(&marker).exists() {
            std::fs::write(&marker, "").unwrap();
            exit_with(n.parse().unwrap())
        }
    }
    hh::rt::ocaml_sys::set_signal(
        libc::SIGUSR2,
        hh::rt::ocaml_sys::SignalBehavior::SignalHandle(std::sync::Arc::new(|_| {
            hh::hh_logger::log("Got sigusr2 signal. Going to shut down.");
            std::process::exit(hh::exit_status::exit_code(
                &hh::exit_status::T::ServerShuttingDownDueToSigusr2,
            ) as i32)
        })),
    );
    hh::server_progress::write(None, Some(hh::server_progress::Disposition::DReady), "ready");
    let fds = [default_ic, priority_in_fd, force_dormant_start_only_in_fd];
    loop {
        // `exit_if_parent_dead`
        if unsafe { libc::getppid() } != monitor_pid {
            hh::hh_logger::log("Lost parent monitor.");
            std::process::exit(
                hh::exit_status::exit_code(&hh::exit_status::T::LostParentMonitor) as i32,
            )
        }
        let mut pfds: Vec<libc::pollfd> = fds
            .iter()
            .map(|fd| libc::pollfd {
                fd: *fd,
                events: libc::POLLIN,
                revents: 0,
            })
            .collect();
        let n = unsafe { libc::poll(pfds.as_mut_ptr(), 3, 100) };
        if n <= 0 {
            continue;
        }
        for p in &pfds {
            if p.revents & (libc::POLLIN | libc::POLLHUP) != 0 {
                take_client(p.fd);
            }
        }
    }
}

/// `Server_client_provider.accept_client`, then a `CHECK_LIVENESS`.
fn take_client(fd: RawFd) {
    let mut pipe = std::mem::ManuallyDrop::new(unsafe { UnixStream::from_raw_fd(fd) });
    let msg: monitor_rpc::MonitorToServerHandoffMsg = match protocol::read_value(&mut *pipe) {
        Ok(msg) => msg,
        Err(e) => {
            hh::hh_logger::log(&format!("Fake server: monitor pipe: {:?}", e));
            std::process::exit(
                hh::exit_status::exit_code(&hh::exit_status::T::LostParentMonitor) as i32,
            )
        }
    };
    let socket = hh::libancillary::ancil_recv_fd(fd).unwrap();
    monitor_rpc::write_server_receipt_to_monitor_file(
        &hh::server_files::server_receipt_to_monitor_file(std::process::id() as isize),
        msg.m2s_sequence_number,
    );
    hh::hh_logger::log(&format!(
        "[{}] got FD#{} handoff from monitor",
        hh::connection_tracker::log_id(&msg.m2s_tracker),
        msg.m2s_sequence_number
    ));
    let ic = unsafe { UnixStream::from_raw_fd(socket) };
    let oc = match ic.try_clone() {
        Ok(oc) => oc,
        Err(_) => return,
    };
    let mut client = hh::server_client_provider::server_end::Client {
        ic,
        oc,
        tracker: msg.m2s_tracker,
        handoff_options: monitor_rpc::HandoffOptions {
            force_dormant_start: false,
            pipe_type: monitor_rpc::PipeType::Default,
            agent_session_id: msg.m2s_agent_session_id.clone(),
        },
        agent_session_id: msg.m2s_agent_session_id,
    };
    if hh::server_client_provider::server_end::read_connection_type(&mut client).is_err() {
        return;
    }
    if let Ok((_, hh::server_command_types::T::CheckLiveness)) =
        hh::server_client_provider::server_end::read_client_msg(&mut client)
    {
        let _ = hh::server_client_provider::server_end::send_response_to_client(
            &mut client,
            hh::server_command_types::CommandResult::CheckLiveness(()),
        );
    }
}

// ~~ Helpers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

const HH_CLIENT: &str = env!("CARGO_BIN_EXE_hh_client_rust");

struct Scratch {
    root: PathBuf,
    tmp: PathBuf,
    fakebin: PathBuf,
    fake_server: String,
    fake_dmesg: bool,
}

impl Scratch {
    fn new(name: &str) -> Scratch {
        let base = std::env::var_os("HH_MON_TEST_DIR")
            .map(PathBuf::from)
            // (Not `std::env::temp_dir()`: on macOS its paths make socket
            // paths longer than the 104 bytes a socket path may have.)
            .unwrap_or_else(|| PathBuf::from("/tmp/hh-monitor-tests"));
        let base = base.join(name);
        let _ = std::fs::remove_dir_all(&base);
        let root = base.join("root");
        let tmp = base.join("tmp");
        let fakebin = base.join("bin");
        std::fs::create_dir_all(&root).unwrap();
        std::fs::create_dir_all(&tmp).unwrap();
        std::fs::create_dir_all(&fakebin).unwrap();
        std::fs::write(root.join(".hhconfig"), "").unwrap();
        std::fs::write(root.join("a.php"), "<?hh\nfunction test_a(): void {}\n").unwrap();
        // A `dmesg` that succeeds (the real one needs privileges on macOS).
        let dmesg = fakebin.join("dmesg");
        std::fs::write(&dmesg, "#!/bin/sh\nexit 0\n").unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&dmesg, std::fs::Permissions::from_mode(0o755)).unwrap();
        let root = PathBuf::from(hh::sys_utils::realpath(&root.to_string_lossy()).unwrap());
        // (The real path: `Socket.make_valid_socket_path` resolves the path of
        // the socket only once it exists, so with a `/tmp` that is a link the
        // monitor's name and the client's could differ, as in the OCaml.)
        let tmp = PathBuf::from(hh::sys_utils::realpath(&tmp.to_string_lossy()).unwrap());
        Scratch {
            root,
            tmp,
            fakebin,
            fake_server: "serve".to_string(),
            fake_dmesg: true,
        }
    }

    fn root_s(&self) -> String {
        self.root.to_string_lossy().into_owned()
    }

    fn envs(&self, c: &mut Command) {
        let path = std::env::var("PATH").unwrap_or_default();
        let path = if self.fake_dmesg {
            format!("{}:{}", self.fakebin.display(), path)
        } else {
            path
        };
        c.env("HH_TMPDIR", &self.tmp)
            .env("HH_SERVER_PATH", std::env::current_exe().unwrap())
            .env("HH_MON_TEST_AS_SERVER", "1")
            .env("HH_FAKE_SERVER", &self.fake_server)
            .env("HH_LOCALCONF_PATH", self.tmp.join("no-etc"))
            .env("PATH", path)
            .env_remove("HH_SERVER_DAEMON")
            .env_remove("HH_SERVER_DAEMON_PARAM");
    }

    /// `hh_client ARGS...`: (exit code, stdout, stderr).
    fn hh(&self, args: &[&str]) -> (i32, String, String) {
        let mut c = Command::new(HH_CLIENT);
        c.args(args).current_dir(&self.root);
        self.envs(&mut c);
        let out = c.output().unwrap();
        let res = (
            out.status.code().unwrap_or(-1),
            String::from_utf8_lossy(&out.stdout).into_owned(),
            String::from_utf8_lossy(&out.stderr).into_owned(),
        );
        eprintln!("  $ hh_client {} -> {}\n{}", args.join(" "), res.0, indent(&res.2));
        res
    }

    /// `hh_server ARGS...` (this binary as `hh_server`), not detached.
    fn hh_server(&self, args: &[&str]) -> std::process::Child {
        let mut c = Command::new(std::env::current_exe().unwrap());
        c.args(args)
            .current_dir(&self.root)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());
        self.envs(&mut c);
        c.spawn().unwrap()
    }

    fn file(&self, ext: &str) -> String {
        format!(
            "{}/{}.{}",
            self.tmp.display(),
            hh::path::slash_escaped_string_of_path(&self.root_s()),
            ext
        )
    }

    fn monitor_log(&self) -> String {
        std::fs::read_to_string(self.file("monitor_log")).unwrap_or_default()
    }

    fn server_log(&self) -> String {
        std::fs::read_to_string(self.file("log")).unwrap_or_default()
    }

    fn pids(&self) -> Vec<(i32, String)> {
        std::fs::read_to_string(self.file("pids"))
            .unwrap_or_default()
            .lines()
            .filter_map(|l| {
                let (p, r) = l.split_once('\t')?;
                Some((p.parse().ok()?, r.to_string()))
            })
            .collect()
    }

    fn pid_of(&self, reason: &str) -> i32 {
        // (The server writes the file as it starts.)
        wait_until(&format!("{} in .pids", reason), 20., || {
            self.pids().iter().any(|(_, r)| r == reason)
        });
        self.pids()
            .into_iter()
            .rev()
            .find(|(_, r)| r == reason)
            .map(|(p, _)| p)
            .unwrap_or_else(|| panic!("no {} in .pids", reason))
    }

    /// The pids of the "Just started typechecker server with pid: N."
    /// lines of the monitor log.
    fn server_pids(&self) -> Vec<i32> {
        self.monitor_log()
            .lines()
            .filter_map(|l| l.split("Just started typechecker server with pid: ").nth(1))
            .filter_map(|s| s.trim_end_matches('.').parse().ok())
            .collect()
    }

    fn progress(&self) -> String {
        std::fs::read_to_string(self.file("progress.json")).unwrap_or_default()
    }

    /// Stops the server (`hh_client stop`) and checks that nothing of it is
    /// left running.
    fn stop(&self) {
        let pids: Vec<i32> = self.pids().into_iter().map(|(p, _)| p).collect();
        self.hh(&["stop", &self.root_s()]);
        for p in pids {
            wait_until(&format!("process {} gone", p), 10., || !alive(p));
        }
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        if self.root.join(".watchmanconfig").exists() {
            let _ = Command::new("watchman")
                .args(["watch-del", &self.root_s()])
                .output();
        }
        // Leave no process behind, whatever happened.
        for (p, _) in self.pids() {
            if alive(p) {
                unsafe {
                    libc::kill(p, libc::SIGKILL);
                }
            }
        }
    }
}

fn indent(s: &str) -> String {
    s.lines().map(|l| format!("    | {}\n", l)).collect()
}

fn alive(pid: i32) -> bool {
    // A zombie of ours is reaped first.
    unsafe {
        let mut status = 0;
        libc::waitpid(pid, &mut status, libc::WNOHANG);
    }
    let out = Command::new("ps")
        .args(["-o", "stat=", "-p", &pid.to_string()])
        .output()
        .unwrap();
    let stat = String::from_utf8_lossy(&out.stdout);
    let stat = stat.trim();
    !stat.is_empty() && !stat.starts_with('Z')
}

fn command_line(pid: i32) -> String {
    let out = Command::new("ps")
        .args(["-o", "command=", "-p", &pid.to_string()])
        .output()
        .unwrap();
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

fn wait_until(what: &str, timeout: f64, mut f: impl FnMut() -> bool) {
    let start = Instant::now();
    while !f() {
        if start.elapsed().as_secs_f64() > timeout {
            panic!("timeout waiting for {}", what)
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

fn assert_contains(haystack: &str, needle: &str) {
    assert!(
        haystack.contains(needle),
        "expected to find {:?} in:\n{}",
        needle,
        haystack
    );
}

fn wait_for_log(s: &Scratch, needle: &str) {
    wait_until(&format!("monitor log line {:?}", needle), 20., || {
        s.monitor_log().contains(needle)
    });
}

fn exit_code(s: hh::exit_status::T) -> i32 {
    hh::exit_status::exit_code(&s) as i32
}

/// A client of another version: the version handshake only. Returns the
/// connection state and the stream.
fn mismatched_client(
    s: &Scratch,
    terminate: bool,
) -> (hh::monitor_utils::ConnectionState, UnixStream) {
    let sock = hh::socket::make_valid_socket_path(&s.file("sock"));
    let mut c = UnixStream::connect(sock).unwrap();
    let payload = format!(
        r#"{{"client_version":"another-build-rust","tracker_id":"t#test","terminate_monitor_on_version_mismatch":false,"rust_terminate_monitor_on_version_mismatch":{}}}"#,
        terminate
    );
    protocol::ocaml_frame::write_version(&mut c, &payload).unwrap();
    let cstate = protocol::ocaml_frame::read_connection_state(&mut c).unwrap();
    (cstate, c)
}

// ~~ The tests ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `server_progress_tests.ml` `test_start_stop` (with the fake server), and
/// what `ps` and the tmp directory show of the two processes.
fn test_start_stop() {
    let s = Scratch::new("start_stop");
    let (code, stdout, stderr) = s.hh(&["start", "--no-load", &s.root_s()]);
    assert_eq!(code, 0);
    assert_eq!(stdout, "");
    assert_contains(&stderr, "Server launched with the following command:");
    wait_until("[DReady] ready", 20., || s.progress().contains("\"ready\""));
    let monitor = s.pid_of("monitor");
    let server = s.pid_of("main");
    assert!(command_line(monitor).ends_with(" monitor_daemon_main"), "{}", command_line(monitor));
    assert!(command_line(server).ends_with(" Server_main.daemon_main"), "{}", command_line(server));
    assert_eq!(s.server_pids(), vec![server]);
    for ext in ["lock", "sock", "log", "monitor_log", "pids", "progress.json"] {
        assert!(Path::new(&s.file(ext)).exists(), "{} missing", ext);
    }
    let log = s.monitor_log();
    for line in [
        "MonitorStart. Monitor init_id: ",
        "[progress] monitor initializing...",
        "Informant using dummy - resigning",
        "Starting first server",
        "About to spawn typechecker daemon. Logs will go to ",
        "[progress] starting hh_server",
    ] {
        assert_contains(&log, line);
    }
    // A second `start`: the server exists.
    let (code, _, stderr) = s.hh(&["start", &s.root_s()]);
    assert_eq!(code, exit_code(hh::exit_status::T::ServerAlreadyExists));
    assert_contains(&stderr, "Error: Server already exists for ");
    wait_for_log(&s, "Got default request for typechecker. Prior request ");
    wait_for_log(&s, "Handed off client socket to server (handoff #1)");
    wait_for_log(&s, "closing client socket from handoff #1 upon receipt of #1");
    let (code, _, stderr) = s.hh(&["stop", &s.root_s()]);
    assert_eq!(code, 0);
    assert_eq!(
        stderr,
        format!(
            "Attempting to nicely kill server for {}\nSuccessfully killed server for {}\n",
            s.root_s(),
            s.root_s()
        )
    );
    assert!(!alive(monitor) && !alive(server));
    wait_for_log(&s, "Got shutdown RPC. Shutting down.");
    assert_contains(&s.monitor_log(), &format!("kill_server: sending SIGUSR2 to {}", server));
    assert_contains(&s.monitor_log(), "typechecker has exited. Time since first signal: : ");
    // The progress file should be cleanly deleted
    assert!(!Path::new(&s.file("progress.json")).exists());
    let (code, _, stderr) = s.hh(&["stop", &s.root_s()]);
    assert_eq!(code, 0);
    assert_contains(&stderr, "No server to kill");
}

/// `test_kill_server`: the monitor stays, says "server stopped", and tells
/// the next client that the server died, then exits; the client starts a new
/// one.
fn test_kill_server() {
    let s = Scratch::new("kill_server");
    assert_eq!(s.hh(&["start", "--no-load", &s.root_s()]).0, 0);
    wait_until("ready", 20., || s.progress().contains("\"ready\""));
    let monitor = s.pid_of("monitor");
    let server = s.pid_of("main");
    unsafe { libc::kill(server, libc::SIGKILL) };
    // The monitor remains running, hence also the progress file
    wait_until("[DStopped] server stopped", 20., || {
        s.progress().contains("\"server stopped\"")
    });
    assert!(alive(monitor));
    let log = s.monitor_log();
    assert_contains(&log, &format!("[progress] writing crash log (pid: {}, hint: `hh --logname` OR `bunnylol coredumper`)", server));
    assert_contains(&log, &format!("TYPECHECKER_EXIT {{\"pid\":{},\"unix_exit_type\":\"signaled\",\"unix_exit_code\":-7,\"is_oom\":false}}", server));
    // The next client is told, and starts a new server.
    let (code, _, stderr) = s.hh(&["start", "--no-load", &s.root_s()]);
    assert_eq!(code, 0);
    assert_contains(&stderr, "Last server killed by signal: -7.");
    wait_until("old monitor gone", 10., || !alive(monitor));
    wait_until("a new server", 20., || s.pid_of("main") != server);
    s.stop();
}

/// `test_kill_server` where `dmesg` fails (as on macOS without privileges):
/// the OCaml's `check_dmesg_for_oom` asserts, the loop logs it, and the next
/// `waitpid` of the reaped server raises `ECHILD`: the monitor exits.
fn test_kill_server_dmesg_fails() {
    let mut s = Scratch::new("kill_server_dmesg");
    s.fake_dmesg = false;
    // (A `dmesg` that fails, wherever this runs.)
    std::fs::write(s.fakebin.join("dmesg"), "#!/bin/sh\nexit 1\n").unwrap();
    s.fake_dmesg = true;
    assert_eq!(s.hh(&["start", "--no-load", &s.root_s()]).0, 0);
    wait_until("ready", 20., || s.progress().contains("\"ready\""));
    let monitor = s.pid_of("monitor");
    let server = s.pid_of("main");
    unsafe { libc::kill(server, libc::SIGKILL) };
    wait_until("monitor gone", 20., || !alive(monitor));
    let log = s.monitor_log();
    assert_contains(
        &log,
        "check_and_run_loop_ threw with exception: File \"hack/src/utils/sys/sys_utils.ml\", line 159, characters 2-8: Assertion failed",
    );
    assert_contains(&log, "check_and_run_loop_ threw with Unix.ECHILD. Exiting. - ");
}

/// `test_kill_monitor`: the server goes when its monitor does; the progress
/// file stays, its writer dead.
fn test_kill_monitor() {
    let s = Scratch::new("kill_monitor");
    assert_eq!(s.hh(&["start", "--no-load", &s.root_s()]).0, 0);
    wait_until("ready", 20., || s.progress().contains("\"ready\""));
    let monitor = s.pid_of("monitor");
    let server = s.pid_of("main");
    unsafe { libc::kill(monitor, libc::SIGKILL) };
    wait_until("server gone", 20., || !alive(server));
    assert!(Path::new(&s.file("progress.json")).exists());
}

/// The restart table of `update_status` (`monitor_main.ml:735-905`): the
/// server exits once with each status; the monitor restarts it with the
/// OCaml's reason.
fn test_restart_table() {
    use hh::exit_status::T::*;
    let restarts: &[(hh::exit_status::T, &str)] = &[
        (WatchmanFailed, "Watchman died. Restarting hh_server (attempt: 1)"),
        (WatchmanFreshInstance, "Watchman died. Restarting hh_server (attempt: 1)"),
        (EdenfsWatcherFailed, "Edenfs_watcher died. Restarting hh_server (attempt: 1)"),
        (
            EdenfsWatcherEdenShuttingDown,
            "Edenfs_watcher died. Restarting hh_server (attempt: 1)",
        ),
        (EdenfsWatcherLostChanges, "Edenfs_watcher died. Restarting hh_server (attempt: 1)"),
        (DeclHeapElemsBug, "hh_server died due to Decl_heap_elems_bug. Restarting"),
        (WorkerNotFoundException, "hh_server died due to worker error. Restarting"),
        (WorkerBusy, "hh_server died due to worker error. Restarting"),
        (WorkerFailedToSendJob, "hh_server died due to worker error. Restarting"),
        (HhconfigChanged, "hh_server died from hh config change. Restarting"),
        (FileProviderStale, "Several large rebases caused shared heap to be stale. Restarting"),
        (DeclNotFound, "Several large rebases caused shared heap to be stale. Restarting"),
        (DepgraphUnavailable, "hh_server dependency graph became unavailable. Restarting"),
        (BigRebaseDetected, "Server exited because of big rebase. Restarting"),
        (SqlAssertionFailure, "Sql failed. Restarting hh_server in fresh mode (attempt: 1)"),
        (SqlCantopen, "Sql failed. Restarting hh_server in fresh mode (attempt: 1)"),
        (SqlCorrupt, "Sql failed. Restarting hh_server in fresh mode (attempt: 1)"),
        (SqlMisuse, "Sql failed. Restarting hh_server in fresh mode (attempt: 1)"),
    ];
    for (status, reason) in restarts {
        let code = hh::exit_status::exit_code(status) as i32;
        let mut s = Scratch::new(&format!("restart_{}", code));
        s.fake_server = format!("exit_once:{}", code);
        eprintln!("- {} ({})", hh::exit_status::show(status), code);
        assert_eq!(s.hh(&["start", &s.root_s()]).0, 0);
        wait_for_log(&s, &format!("MONITOR_UPDATE_STATUS {}", reason));
        wait_for_log(&s, "Unexpected Resigned informant without a server started, restarting server");
        wait_for_log(&s, "kill_and_maybe_restart_server (env.server=Server_process.Not_yet_started)");
        wait_for_log(&s, "MONITOR_UPDATE_STATUS Informant directed server restart. Restarting server.");
        wait_until("two servers", 20., || s.server_pids().len() == 2);
        let log = s.monitor_log();
        assert_contains(&log, &format!("\"unix_exit_type\":\"exit\",\"unix_exit_code\":{},", code));
        // `Server_controller.start_server` would restart the SQL failures in
        // fresh mode (`--no-load`), but the OCaml restarts in the next
        // iteration of the loop, when the server is `Not_yet_started` and
        // the exit status is `None`: never with `--no-load`.
        wait_until("the second server", 20., || s.server_log().contains("Fake server starting"));
        assert_contains(&s.server_log(), "Fake server starting (no_load=false).");
        s.stop();
    }
}

/// An exit that is not in the table: the monitor keeps the status, tells the
/// next client, exits.
fn test_no_restart() {
    let mut s = Scratch::new("no_restart");
    // (Not `Package_config_changed`: its code is 4, as `Hhconfig_changed`'s,
    // which the monitor restarts.)
    s.fake_server = format!("exit_once:{}", exit_code(hh::exit_status::T::InputError));
    assert_eq!(s.hh(&["start", &s.root_s()]).0, 0);
    let monitor = s.pid_of("monitor");
    wait_until("server stopped", 20., || s.progress().contains("\"server stopped\""));
    std::thread::sleep(Duration::from_millis(1500));
    assert_eq!(s.server_pids().len(), 1);
    assert!(!s.monitor_log().contains("MONITOR_UPDATE_STATUS"));
    let (code, _, stderr) = s.hh(&["start", &s.root_s()]);
    assert_eq!(code, 0);
    assert_contains(
        &stderr,
        &format!(
            "Last server exited with code: {}.",
            exit_code(hh::exit_status::T::InputError)
        ),
    );
    wait_until("old monitor gone", 10., || !alive(monitor));
    wait_until("new server", 20., || s.pids().iter().any(|(p, r)| r == "monitor" && *p != monitor));
    s.stop();
}

/// The watchman retries: three restarts, then the status is kept.
fn test_watchman_retries() {
    let mut s = Scratch::new("watchman_retries");
    s.fake_server = format!("exit:{}", exit_code(hh::exit_status::T::WatchmanFailed));
    assert_eq!(s.hh(&["start", &s.root_s()]).0, 0);
    for i in 1..=3 {
        wait_for_log(&s, &format!("MONITOR_UPDATE_STATUS Watchman died. Restarting hh_server (attempt: {})", i));
    }
    wait_until("four servers", 20., || s.server_pids().len() == 4);
    std::thread::sleep(Duration::from_millis(2500));
    assert_eq!(s.server_pids().len(), 4);
    let monitor = s.pid_of("monitor");
    let (_, _, stderr) = s.hh(&["stop", &s.root_s()]);
    let _ = stderr;
    wait_until("monitor gone", 10., || !alive(monitor));
}

/// Version mismatch, both values of `terminate_monitor_on_version_mismatch`.
fn test_version_mismatch() {
    use hh::monitor_utils::ConnectionState;
    let s = Scratch::new("version_mismatch");
    assert_eq!(s.hh(&["start", "--no-load", &s.root_s()]).0, 0);
    wait_until("ready", 20., || s.progress().contains("\"ready\""));
    let monitor = s.pid_of("monitor");
    let server = s.pid_of("main");
    // The client must terminate: the connection is closed, all stays up.
    let (cstate, mut c) = mismatched_client(&s, false);
    match cstate {
        ConnectionState::BuildIdMismatchV3(info, payload) => {
            assert_eq!(info.existing_version, hh::build_id::build_revision());
            assert_eq!(
                info.existing_argv,
                vec![
                    hh::sys_utils::executable_path(),
                    "monitor_daemon_main".to_string()
                ]
            );
            assert_eq!(payload, r#"{"monitor_will_terminate":false}"#);
        }
        c => panic!("{:?}", c),
    }
    let mut buf = [0u8; 1];
    assert_eq!(c.read(&mut buf).unwrap(), 0);
    wait_for_log(&s, "[t#test] read_version: start_wait=");
    wait_for_log(&s, "Closing client_fd");
    assert!(alive(monitor) && alive(server));
    // The monitor will terminate: it kills the server and exits, closing
    // the connection.
    let (cstate, mut c) = mismatched_client(&s, true);
    match cstate {
        ConnectionState::BuildIdMismatchV3(_, payload) => {
            assert_eq!(payload, r#"{"monitor_will_terminate":true}"#)
        }
        c => panic!("{:?}", c),
    }
    assert_eq!(c.read(&mut buf).unwrap(), 0);
    wait_until("monitor gone", 10., || !alive(monitor) && !alive(server));
    assert_contains(&s.monitor_log(), &format!("kill_server: sending SIGUSR2 to {}", server));
}

/// The exit statuses of a monitor in the foreground (`hh_server ROOT`):
/// version mismatch, lock stolen, signals, two monitors on a root.
fn test_foreground_exits() {
    let s = Scratch::new("foreground");
    let wait = |mut child: std::process::Child| -> (i32, String) {
        let status = child.wait().unwrap();
        let mut err = String::new();
        child.stderr.take().unwrap().read_to_string(&mut err).unwrap();
        (status.code().unwrap_or(-1), err)
    };
    let started = |child_err_file: &Scratch| {
        wait_until("ready", 20., || child_err_file.progress().contains("\"ready\""));
    };
    // Version mismatch, the monitor terminating.
    let child = s.hh_server(&[&s.root_s()]);
    started(&s);
    let (_, _c) = mismatched_client(&s, true);
    let (code, err) = wait(child);
    assert_eq!(code, exit_code(hh::exit_status::T::BuildIdMismatch));
    assert_contains(&err, "About to spawn typechecker daemon. Logs will go here.");
    // Two monitors on one root.
    let first = s.hh_server(&[&s.root_s()]);
    started(&s);
    let second = s.hh_server(&[&s.root_s()]);
    let (code, err) = wait(second);
    assert_eq!(code, 0);
    assert_eq!(err, format!("Monitor lock file already exists: {}\n", s.file("lock")));
    let detached = s.hh_server(&["-d", &s.root_s()]);
    let (code, err) = wait(detached);
    assert_eq!(code, 0);
    // (The detached monitor has the same stderr until it has the lock.)
    assert_eq!(
        err,
        format!(
            "Running in daemon mode\nMonitor lock file already exists: {}\n",
            s.file("lock")
        )
    );
    // SIGTERM: the server is killed, the monitor exits Interrupted.
    let server = s.pid_of("main");
    unsafe { libc::kill(first.id() as i32, libc::SIGTERM) };
    let (code, err) = wait(first);
    assert_eq!(code, exit_code(hh::exit_status::T::Interrupted));
    assert_contains(&err, "Got an exit signal. Killing server and exiting.");
    wait_until("server gone", 10., || !alive(server));
    // The lock file is removed: the monitor exits Lock_stolen.
    let first = s.hh_server(&[&s.root_s()]);
    std::thread::sleep(Duration::from_millis(200));
    wait_until("ready", 20., || s.progress().contains("\"ready\"") && s.pid_of("monitor") == first.id() as i32);
    let server = s.pid_of("main");
    std::fs::remove_file(s.file("lock")).unwrap();
    let (code, err) = wait(first);
    assert_eq!(code, exit_code(hh::exit_status::T::LockStolen));
    assert_contains(&err, "Lost lock; terminating.\n");
    wait_until("server gone", 10., || !alive(server));
}

/// `test_server_invalid_config_key`: the warning is in the monitor log, not
/// on the client's outputs.
fn test_server_invalid_config_key() {
    let s = Scratch::new("invalid_config_key");
    let (code, stdout, stderr) = s.hh(&[
        "start",
        "--no-load",
        "--config",
        "max_workers=1",
        "--config",
        "nonexistent_server_option=value",
        &s.root_s(),
    ]);
    assert_eq!(code, 0);
    assert!(!stdout.contains("Unrecognized --config config option"));
    assert!(!stderr.contains("Unrecognized --config config option"));
    wait_until("ready", 20., || s.progress().contains("\"ready\""));
    let log = s.monitor_log();
    assert_contains(&log, "Unrecognized --config config option: nonexistent_server_option");
    assert!(!log.contains("Unrecognized --config config option: max_workers"));
    s.stop();
}

/// `hh_client restart`: a new monitor and server.
fn test_restart() {
    let s = Scratch::new("restart");
    assert_eq!(s.hh(&["start", "--no-load", &s.root_s()]).0, 0);
    wait_until("ready", 20., || s.progress().contains("\"ready\""));
    let monitor = s.pid_of("monitor");
    let (code, _, _) = s.hh(&["restart", "--no-load", &s.root_s()]);
    assert_eq!(code, 0);
    assert!(!alive(monitor));
    wait_until("new monitor", 20., || s.pid_of("monitor") != monitor);
    // The logs rotate.
    assert!(Path::new(&format!("{}.old", s.file("log"))).exists());
    assert!(Path::new(&format!("{}.old", s.file("monitor_log"))).exists());
    s.stop();
}


// ~~ The two implementations (OCaml oracle) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The directory of the OCaml `hh_client`/`hh_server` (`HH_OCAML_BIN`), or
/// `None`: the cross-implementation tests are skipped.
fn ocaml_bin() -> Option<PathBuf> {
    match std::env::var("HH_OCAML_BIN") {
        Ok(d) => Some(PathBuf::from(d)),
        Err(_) => {
            eprintln!("  (skipped: HH_OCAML_BIN is not set)");
            None
        }
    }
}

impl Scratch {
    /// For the OCaml daemon on macOS: Watchman, no streaming errors (see
    /// notes.md), for both kinds (the Rust ones ignore what they need not).
    fn for_ocaml(name: &str) -> Scratch {
        let s = Scratch::new(name);
        std::fs::create_dir_all(s.tmp.join("no-etc")).unwrap();
        std::fs::write(
            s.tmp.join("no-etc/hh.conf"),
            "use_watchman = true\nproduce_streaming_errors = false\n",
        )
        .unwrap();
        // (kqueue: the FSEvents streams of this machine run out with the
        // watches of many roots.)
        std::fs::write(s.root.join(".watchmanconfig"), r#"{"watcher": "kqueue"}"#).unwrap();
        s
    }

    /// The OCaml `hh_client ARGS...` on this root and tmp directory.
    fn ocaml_hh(&self, bin: &Path, args: &[&str]) -> (i32, String, String) {
        let mut c = Command::new(bin.join("hh_client"));
        c.args(args).current_dir(&self.root);
        self.envs(&mut c);
        c.env_remove("HH_SERVER_PATH");
        let out = c.output().unwrap();
        let res = (
            out.status.code().unwrap_or(-1),
            String::from_utf8_lossy(&out.stdout).into_owned(),
            String::from_utf8_lossy(&out.stderr).into_owned(),
        );
        eprintln!("  $ ocaml hh_client {} -> {}\n{}", args.join(" "), res.0, indent(&res.2));
        res
    }

    fn lock_held(&self) -> bool {
        !hh::lock::check(&self.file("lock"))
    }

    /// Nothing left: no process of the `.pids`, the lock free.
    fn assert_nothing_left(&self) {
        for (p, _) in self.pids() {
            wait_until(&format!("process {} gone", p), 10., || !alive(p));
        }
        wait_until("lock free", 10., || !self.lock_held());
    }
}

/// The two first frames are the OCaml's: what the OCaml client sends decodes
/// and re-encodes to the same bytes, and it understands the Rust monitor's
/// `Build_id_mismatch_v3` (refused: "Error: version mismatch", exit 9, the
/// Rust server named).
fn test_ocaml_frames() {
    use hh::monitor_utils::ConnectionState;
    let Some(bin) = ocaml_bin() else { return };
    let s = Scratch::for_ocaml("ocaml_frames");
    let sock = hh::socket::make_valid_socket_path(&s.file("sock"));
    let _ = std::fs::remove_file(&sock);
    let listener = std::os::unix::net::UnixListener::bind(&sock).unwrap();
    let t = std::thread::spawn(move || {
        let (mut c, _) = listener.accept().unwrap();
        // The bytes, as they come.
        let mut raw = vec![0u8; 5];
        c.read_exact(&mut raw).unwrap();
        let n = u32::from_be_bytes([raw[1], raw[2], raw[3], raw[4]]) as usize;
        let mut rest = vec![0u8; n + 1];
        c.read_exact(&mut rest).unwrap();
        raw.extend_from_slice(&rest);
        let version = protocol::ocaml_frame::read_version(&mut &raw[..]).unwrap().unwrap();
        let mut again = vec![];
        protocol::ocaml_frame::write_version(&mut again, &version).unwrap();
        assert_eq!(raw, again, "the OCaml client's version message, re-encoded");
        let payload = hh::monitor_utils::version_payload::deserialize(&version).unwrap();
        assert!(!hh::build_id::is_rust_build_revision(&payload.client_version));
        assert_eq!(payload.rust_terminate_monitor_on_version_mismatch, None);
        let info = hh::monitor_utils::BuildMismatchInfo {
            existing_version: hh::build_id::build_revision(),
            existing_build_commit_time: "commit time".to_string(),
            existing_argv: vec!["/x/hh_server_rust".to_string(), "monitor_daemon_main".to_string()],
            existing_launch_time: 1794520000.5,
        };
        protocol::ocaml_frame::write_connection_state(
            &mut c,
            &ConnectionState::BuildIdMismatchV3(
                info,
                hh::monitor_utils::mismatch_payload::serialize(false),
            ),
        )
        .unwrap();
        // (As the Rust monitor: the client closes first.)
        let mut buf = [0u8; 1];
        let _ = c.read(&mut buf);
        payload.terminate_monitor_on_version_mismatch
    });
    let (code, _, stderr) = s.ocaml_hh(&bin, &["check", "--autostart-server", "false", &s.root_s()]);
    let asked_terminate = t.join().unwrap();
    assert!(!asked_terminate);
    assert_eq!(code, exit_code(hh::exit_status::T::BuildIdMismatch));
    assert_contains(&stderr, "Error: version mismatch.\nUse --autostart-server true if you want it to restart.\n  hh_server '/x/hh_server_rust monitor_daemon_main', version '");
    assert_contains(&stderr, &format!("version '{}'", hh::build_id::build_revision()));
    let _ = std::fs::remove_file(&sock);
}

/// An OCaml monitor and the Rust client: check and start refuse with the
/// message of `other_implementation_message` (exit 9) and leave the OCaml
/// server running; the OCaml monitor's reply re-encodes to its bytes; stop
/// stops it; restart replaces it with a Rust one.
fn test_ocaml_monitor_rust_client() {
    use hh::monitor_utils::ConnectionState;
    let Some(bin) = ocaml_bin() else { return };
    let s = Scratch::for_ocaml("ocaml_monitor");
    let (code, _, _) = s.ocaml_hh(&bin, &["start", &s.root_s()]);
    assert_eq!(code, 0);
    wait_until("ocaml ready", 60., || s.progress().contains("\"ready\""));
    let monitor = s.pid_of("monitor");
    // The OCaml monitor's reply to a Rust-framed version, byte for byte.
    {
        let sock = hh::socket::make_valid_socket_path(&s.file("sock"));
        let mut c = UnixStream::connect(sock).unwrap();
        let tracker = hh::connection_tracker::create();
        let payload = hh::monitor_utils::version_payload::serialize(&tracker, true, false);
        protocol::ocaml_frame::write_version(&mut c, &payload).unwrap();
        let mut raw = vec![];
        c.read_to_end(&mut raw).unwrap();
        let cstate = protocol::ocaml_frame::read_connection_state(&mut &raw[..]).unwrap();
        let mut again = vec![];
        protocol::ocaml_frame::write_connection_state(&mut again, &cstate).unwrap();
        assert_eq!(raw, again, "the OCaml monitor's connection_state, re-encoded");
        match cstate {
            ConnectionState::BuildIdMismatchV3(info, p) => {
                assert!(hh::monitor_utils::is_other_implementation(&info));
                assert_eq!(p, r#"{"monitor_will_terminate":false}"#);
            }
            c => panic!("{:?}", c),
        }
    }
    for args in [vec!["check"], vec!["start"]] {
        let mut a = args.clone();
        let root = s.root_s();
        a.push(&root);
        let (code, _, stderr) = s.hh(&a);
        assert_eq!(code, exit_code(hh::exit_status::T::BuildIdMismatch), "{:?}", args);
        assert_contains(&stderr, &format!("Error: an OCaml hh_server is running for {}; this hh_client is the Rust one and does not replace it.", s.root_s()));
        assert_contains(&stderr, "Stop it first (`hh_client stop ");
        assert!(alive(monitor), "the OCaml monitor stays");
    }
    // restart: the Rust stop stops the OCaml server, then a Rust one starts.
    let (code, _, stderr) = s.hh(&["restart", &s.root_s()]);
    assert_eq!(code, 0);
    assert_contains(&stderr, "Successfully killed server for ");
    wait_until("ocaml monitor gone", 10., || !alive(monitor));
    wait_until("rust ready", 20., || s.progress().contains("\"ready\"") && s.pid_of("monitor") != monitor);
    assert!(command_line(s.pid_of("monitor")).ends_with(" monitor_daemon_main"));
    s.stop();
    s.assert_nothing_left();
    // stop alone.
    assert_eq!(s.ocaml_hh(&bin, &["start", &s.root_s()]).0, 0);
    wait_until("ocaml ready", 60., || s.progress().contains("\"ready\""));
    let (code, _, stderr) = s.hh(&["stop", &s.root_s()]);
    assert_eq!(code, 0);
    assert_contains(&stderr, "Successfully killed server for ");
    s.assert_nothing_left();
}

/// A Rust monitor and the OCaml client: check refuses ("Error: version
/// mismatch", exit 9), start says the server exists (as an OCaml start does
/// on that answer), the Rust server stays; stop kills the pids of `.pids`
/// and the lock is free; restart replaces it with an OCaml one.
fn test_rust_monitor_ocaml_client() {
    let Some(bin) = ocaml_bin() else { return };
    let s = Scratch::for_ocaml("rust_monitor");
    assert_eq!(s.hh(&["start", "--no-load", &s.root_s()]).0, 0);
    wait_until("ready", 20., || s.progress().contains("\"ready\""));
    let monitor = s.pid_of("monitor");
    let server = s.pid_of("main");
    let (code, _, stderr) = s.ocaml_hh(&bin, &["check", &s.root_s()]);
    assert_eq!(code, exit_code(hh::exit_status::T::BuildIdMismatch));
    assert_contains(&stderr, "Error: version mismatch.\nUse --autostart-server true if you want it to restart.\n");
    assert_contains(&stderr, &format!("version '{}'", hh::build_id::build_revision()));
    assert_contains(&stderr, " monitor_daemon_main', version '");
    assert!(alive(monitor) && alive(server));
    wait_for_log(&s, "client of another implementation: monitor_will_terminate=false (cross-implementation policy Refuse)");
    let (code, _, stderr) = s.ocaml_hh(&bin, &["start", &s.root_s()]);
    assert_eq!(code, exit_code(hh::exit_status::T::ServerAlreadyExists));
    assert_contains(&stderr, "Error: Server already exists for ");
    assert!(alive(monitor) && alive(server));
    let (code, _, stderr) = s.ocaml_hh(&bin, &["stop", &s.root_s()]);
    assert_eq!(code, 0);
    assert_contains(&stderr, "Attempting to meanly kill server for ");
    assert_contains(&stderr, "Successfully killed server for ");
    s.assert_nothing_left();
    // restart: the OCaml stop (mean kill), then an OCaml server.
    assert_eq!(s.hh(&["start", "--no-load", &s.root_s()]).0, 0);
    wait_until("ready", 20., || s.progress().contains("\"ready\""));
    let monitor = s.pid_of("monitor");
    let (code, _, stderr) = s.ocaml_hh(&bin, &["restart", &s.root_s()]);
    assert_eq!(code, 0, "{}", stderr);
    wait_until("rust monitor gone", 10., || !alive(monitor));
    wait_until("ocaml ready", 60., || s.progress().contains("\"ready\"") && s.pid_of("monitor") != monitor);
    let (code, _, _) = s.ocaml_hh(&bin, &["stop", &s.root_s()]);
    assert_eq!(code, 0);
    s.assert_nothing_left();
}

// ~~ The log of check mode ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `hh_server_rust --check` (or the OCaml `hh_server --check` of `bin`) on
/// the root of `s`, with one worker: (exit code, the lines it logs from
/// `[progress] initializing...` on, without their timestamps, durations as
/// `T`, and without the `Cgroup:` lines, which only a Linux cgroup v2 gives).
fn check_mode_log(s: &Scratch, bin: Option<&Path>) -> (i32, Vec<String>) {
    let mut c = match bin {
        None => Command::new(env!("CARGO_BIN_EXE_hh_server_rust")),
        Some(bin) => Command::new(bin.join("hh_server")),
    };
    c.args(["--check", "--max-procs", "1", &s.root_s()]).current_dir(&s.root);
    s.envs(&mut c);
    c.env_remove("HH_SERVER_PATH").env_remove("HH_MON_TEST_AS_SERVER").env_remove("HH_FAKE_SERVER");
    let out = c.output().unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    let timestamp = regex::Regex::new(r"^\[\d{4}-\d\d-\d\d \d\d:\d\d:\d\d\.\d{3}\] ").unwrap();
    let duration = regex::Regex::new(r": \d+\.\d{6}$").unwrap();
    let mut lines = vec![];
    let mut cgroup = false;
    for line in stderr.lines() {
        let line = timestamp.replace(line, "");
        if line == "[progress] initializing..." {
            lines.clear();
        }
        // (The second line of a `Cgroup:` line: its previous measurement.)
        cgroup = line.starts_with("Cgroup: ") || (cgroup && line.starts_with("   >"));
        if !cgroup {
            lines.push(duration.replace(&line, ": T").into_owned());
        }
    }
    (out.status.code().unwrap_or(-1), lines)
}

/// The lines of `Server_init.init`'s full init in check mode, in the
/// OCaml's order and text (pinned from the OCaml's log); with `HH_OCAML_BIN`,
/// the OCaml `hh_server --check` logs the same lines on the same root (but
/// for its "Hashtable load factor" lines: its stores are always on the
/// shared heap, those of the Rust check mode are not by default).
fn test_check_mode_log() {
    let s = Scratch::new("check_mode_log");
    std::fs::write(s.root.join("b.php"), "<?hh\nfunction test_b(): int {\n  return \"b\";\n}\n").unwrap();
    std::fs::create_dir_all(s.tmp.join("no-etc")).unwrap();
    let (code, lines) = check_mode_log(&s, None);
    // (`Program.run_once_and_exit`: 1 when there are errors.)
    assert_eq!(code, 1, "{:#?}", lines);
    let files = regex::Regex::new(r"\b\d+ files\b").unwrap();
    let pinned: Vec<String> = lines.iter().map(|l| files.replace_all(l, "N files").into_owned()).collect();
    assert_eq!(
        pinned,
        [
            "[progress] initializing...",
            "Initing with approach: Local_config_saved_state_disabled",
            "ServerInit: init_approach=Server_init_types.Full_init",
            "full init",
            "[progress] full initialization",
            "[progress] indexing",
            "indexing lazy.nt.indexing: T",
            "[progress] parsing",
            "Parsing lazy.nt.parsing: T",
            "[progress] resolving symbol references",
            "Naming lazy.nt.do_naming.naming: T",
            "Streaming errors disabled for eager init",
            "[progress] typechecking",
            "Begin Filter N files [lazy.full.type_check]",
            "Filter N files [lazy.full.type_check]: T",
            "Begin type-check N files",
            "[progress] typechecking N files",
            "Multi_threaded_call.call_with_interrupt called with 1 workers",
            "1 errors in batch. Showing first 5:",
            "ERROR: b.php(3:10-3:12) [4110] Invalid return type",
            "type-check N files: T",
            "Waiting for daemon(s) to be ready...",
            "[progress] wrapping up init...",
            "Running in check mode",
        ]
    );
    // The hhi files are checked too: as many files as the hhi files and the
    // two of the root.
    let hhi_count = lines.iter().find_map(|l| l.strip_prefix("Begin type-check ")?.strip_suffix(" files"));
    assert!(hhi_count.unwrap().parse::<usize>().unwrap() > 2, "{:#?}", lines);
    let Some(bin) = ocaml_bin() else { return };
    let (ocaml_code, ocaml_lines) = check_mode_log(&s, Some(&bin));
    let ocaml_lines: Vec<String> =
        ocaml_lines.into_iter().filter(|l| !l.starts_with("Hashtable load factor: ")).collect();
    assert_eq!((code, lines), (ocaml_code, ocaml_lines));
}

const TESTS: &[(&str, fn())] = &[
    ("test_start_stop", test_start_stop),
    ("test_kill_server", test_kill_server),
    ("test_kill_server_dmesg_fails", test_kill_server_dmesg_fails),
    ("test_kill_monitor", test_kill_monitor),
    ("test_restart_table", test_restart_table),
    ("test_no_restart", test_no_restart),
    ("test_watchman_retries", test_watchman_retries),
    ("test_version_mismatch", test_version_mismatch),
    ("test_foreground_exits", test_foreground_exits),
    ("test_server_invalid_config_key", test_server_invalid_config_key),
    ("test_restart", test_restart),
    ("test_ocaml_frames", test_ocaml_frames),
    ("test_ocaml_monitor_rust_client", test_ocaml_monitor_rust_client),
    ("test_rust_monitor_ocaml_client", test_rust_monitor_ocaml_client),
    ("test_check_mode_log", test_check_mode_log),
];

fn main() {
    hh::monitor_start::register_entry_points(fake_server);
    hh::daemon::check_entry_point();
    if std::env::var("HH_MON_TEST_AS_SERVER").is_ok() {
        hh::monitor_start::start_with_server_entry(fake_server)
    }
    let args: Vec<String> = std::env::args().skip(1).filter(|a| !a.starts_with('-')).collect();
    let mut failed = vec![];
    for (name, test) in TESTS {
        if !args.is_empty() && !args.iter().any(|a| name.contains(a.as_str())) {
            continue;
        }
        eprintln!("=== {}", name);
        let res = std::panic::catch_unwind(test);
        match res {
            Ok(()) => eprintln!("--- {} ok", name),
            Err(_) => {
                eprintln!("--- {} FAILED", name);
                failed.push(*name)
            }
        }
    }
    if !failed.is_empty() {
        eprintln!("failed: {:?}", failed);
        std::process::exit(1)
    }
}
