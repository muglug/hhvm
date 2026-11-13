// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The tests of `Client_connect`, `Client_start`, `Client_stop` and
//! `Client_restart` against a small test server.
//!
//! Each test runs the client in a process of its own (this test binary,
//! started again on [`child`] with the scenario in [`SCENARIO`]), so that
//! what it prints on stderr, its exit status and its exit code can be
//! compared, and so that the lock the test server holds is held by another
//! process (`Lock.check` sees the locks of other processes only). The test
//! server is in the test itself: a thread that accepts on the root's socket
//! and plays the server's end of `crate::rt::protocol` (or misbehaves).
//!
//! The files of a root live under a temporary directory of these tests
//! ([`tmp`], canonical, so that the client and the server compute the same
//! socket path), not under `server_files`' global one: the client process
//! is given it with `set_tmp_FOR_TESTING_ONLY`, and the test server
//! computes the names itself ([`Files`]).

use std::io::Write as _;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixListener;
use std::os::unix::net::UnixStream;
use std::panic::AssertUnwindSafe;
use std::sync::Arc;
use std::sync::LazyLock;
use std::sync::Mutex;
use std::time::Duration;
use std::time::Instant;

use super::*;
use crate::client_restart;
use crate::client_stop;
use crate::lock;
use crate::rt::protocol::prehandoff;
use crate::rt::protocol::server_end;
use crate::server_command_types::T;
use crate::server_files;
use crate::socket;

/// The scenario the child process plays (see [`child`]).
const SCENARIO: &str = "HH_D1_TEST_SCENARIO";
const ROOT: &str = "HH_D1_TEST_ROOT";
const TMP: &str = "HH_D1_TEST_TMP";

/// The temporary directory of these tests: canonical (no symbolic link in
/// it), so that `Socket.make_valid_socket_path` gives the same path before
/// and after the socket exists.
fn tmp() -> String {
    static DIR: LazyLock<String> = LazyLock::new(|| {
        let base = std::fs::canonicalize("/tmp").unwrap();
        let dir = base.join(format!("hhd1_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o777)).unwrap();
        dir.to_str().unwrap().to_string()
    });
    DIR.clone()
}

/// The files of a root, as `Server_files` names them under [`tmp`].
struct Files {
    root: String,
    lock: String,
    sock: String,
    progress: String,
    pids: String,
}

impl Files {
    /// A new root (an existing directory, with a `.hhconfig`) for the test
    /// `name`.
    fn new(name: &str) -> Files {
        let root = format!("{}/roots/{}", tmp(), name);
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(format!("{}/.hhconfig", root), "").unwrap();
        let esc = path::slash_escaped_string_of_path(&root);
        let file = |ext: &str| format!("{}/{}{}", tmp(), esc, ext);
        Files {
            lock: file(".lock"),
            sock: socket::make_valid_socket_path(&file(".sock")),
            progress: file(".progress.json"),
            pids: file(".pids"),
            root,
        }
    }

    /// What `Server_progress.write` would leave there, from this (live)
    /// process.
    fn write_progress(&self, message: &str) {
        std::fs::write(
            &self.progress,
            format!(
                "{{\"pid\":{},\"disposition\":[\"DWorking\"],\"message\":\"{}\",\"timestamp\":1.0}}",
                std::process::id(),
                message
            ),
        )
        .unwrap();
    }

    fn finale_file(&self) -> String {
        format!("{}.fin", self.root)
    }

    fn server_specific_files(&self) -> ServerSpecificFiles {
        ServerSpecificFiles {
            server_finale_file: self.finale_file(),
        }
    }

    /// Takes the lock (the server "exists") and binds the socket.
    fn start(&self) -> UnixListener {
        assert!(lock::grab(&self.lock));
        socket::unix_socket(&self.sock)
    }

    /// What the exit of a server does: its socket and its lock go.
    fn stop(&self) {
        let _ = std::fs::remove_file(&self.sock);
        lock::release(&self.lock);
    }
}

/// `accept`, giving up (failing the test) after 30 seconds.
fn accept(listener: &UnixListener) -> UnixStream {
    listener.set_nonblocking(true).unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        match listener.accept() {
            Ok((conn, _)) => {
                // (A BSD socket inherits the listener's O_NONBLOCK.)
                conn.set_nonblocking(false).unwrap();
                return conn;
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                assert!(Instant::now() < deadline, "no client connected");
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(e) => panic!("accept: {}", e),
        }
    }
}

/// The server's end of a handshake that goes well: the client is handed to
/// the server, which says hello and reads the connection type.
fn handoff(conn: UnixStream, files: &Files) -> server_end::Client {
    match server_end::ack_and_handoff_client(conn, false, &files.server_specific_files()) {
        Ok(server_end::Handshake::Handoff(mut client)) => {
            match server_end::read_connection_type(&mut client) {
                Ok(ConnectionType::NonPersistent) => client,
                Err(e) => panic!("read_connection_type: {:?}", e),
            }
        }
        Ok(_) => panic!("expected HANDOFF_TO_SERVER"),
        Err(e) => panic!("ack_and_handoff_client: {}", e),
    }
}

/// Reads the client's command: the `CHECK_LIVENESS` of [`child`]'s `rpc`.
fn read_check_liveness(client: &mut server_end::Client) {
    match server_end::read_client_msg(client) {
        Ok((metadata, T::CHECKLIVENESS)) => assert_eq!(
            metadata,
            CmdMetadata {
                from: "d1".to_string(),
                desc: "d1-test".to_string(),
            }
        ),
        Ok((_, cmd)) => panic!("unexpected command {:?}", cmd),
        Err(e) => panic!("read_client_msg: {:?}", e),
    }
}

/// Serves one `CHECK_LIVENESS` in full, answering after `delay`.
fn serve_check_liveness(listener: &UnixListener, files: &Files, delay: Duration) {
    let mut client = handoff(accept(listener), files);
    read_check_liveness(&mut client);
    std::thread::sleep(delay);
    server_end::ping(&mut client).unwrap();
    server_end::send_response_to_client(&mut client, CommandResult::CHECKLIVENESS(())).unwrap();
}

/// A stand-in for `hh_server` (`HH_SERVER_PATH`): it writes its arguments
/// to `args`, waits for the file `go`, then exits with the code in it, after
/// writing `Monitor_utils.ready` to its `--waiting-client` descriptor if
/// that code is 0.
struct Stub {
    dir: String,
}

impl Stub {
    fn new(name: &str) -> Stub {
        let dir = format!("{}/stubs/{}", tmp(), name);
        std::fs::create_dir_all(&dir).unwrap();
        let script = format!(
            r#"#!/bin/sh
dir='{dir}'
echo "$@" >> "$dir/args"
while [ ! -e "$dir/go" ]; do sleep 0.05; done
code=$(cat "$dir/go")
if [ "$code" != "0" ]; then exit "$code"; fi
prev=""
for a in "$@"; do
  if [ "$prev" = "--waiting-client" ]; then fd="$a"; fi
  prev="$a"
done
printf 'ready\n' > "/dev/fd/$fd"
exit 0
"#
        );
        let path = format!("{}/hh_server", dir);
        std::fs::write(&path, script).unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        Stub { dir }
    }

    fn path(&self) -> String {
        format!("{}/hh_server", self.dir)
    }

    fn go(&self, code: i32) {
        std::fs::write(format!("{}/go", self.dir), code.to_string()).unwrap();
    }

    /// The arguments of each run so far, once there has been one.
    fn wait_for_run(&self) -> String {
        let deadline = Instant::now() + Duration::from_secs(30);
        loop {
            if let Ok(args) = std::fs::read_to_string(format!("{}/args", self.dir)) {
                return args;
            }
            assert!(Instant::now() < deadline, "the stub hh_server did not run");
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    fn args(&self) -> String {
        std::fs::read_to_string(format!("{}/args", self.dir)).unwrap_or_default()
    }
}

/// What the child process did.
struct Outcome {
    /// Its exit code.
    code: i32,
    /// The lines of stdout that [`child`] printed, without their `D1-`.
    report: Vec<String>,
    stderr: String,
}

impl Outcome {
    fn line(&self, key: &str) -> Option<String> {
        let prefix = format!("{} ", key);
        self.report
            .iter()
            .find_map(|l| l.strip_prefix(&prefix).map(|s| s.to_string()))
    }
}

/// Runs the client of `scenario` on `files.root` in a child process.
fn run_child(scenario: &str, files: &Files, env: &[(&str, String)]) -> Outcome {
    let mut cmd = std::process::Command::new(std::env::current_exe().unwrap());
    cmd.args([
        "client_connect::tests::child",
        "--exact",
        "--nocapture",
        "--test-threads=1",
        "-q",
    ])
    .env(SCENARIO, scenario)
    .env(ROOT, &files.root)
    .env(TMP, tmp())
    .env("RUST_BACKTRACE", "0")
    .env_remove("HH_SERVER_PATH");
    for (k, v) in env {
        cmd.env(k, v);
    }
    let output = cmd.output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    Outcome {
        code: output.status.code().unwrap_or(-1),
        report: stdout
            .lines()
            .filter_map(|l| l.strip_prefix("D1-").map(|s| s.to_string()))
            .collect(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    }
}

/// The `Client_connect.env` of the child's scenarios.
fn client_env(root: &str, autostart: bool, deadline: Option<f64>, cb: ProgressCallback) -> Env {
    Env {
        root: root.to_string(),
        from: "d1".to_string(),
        autostart,
        force_dormant_start: false,
        deadline,
        no_load: false,
        watchman_debug_logging: false,
        progress_callback: cb,
        do_post_handoff_handshake: true,
        ignore_hh_version: false,
        save_64bit: None,
        save_human_readable_64bit_dep_map: None,
        saved_state_ignore_hhconfig: false,
        mini_state: None,
        use_priority_pipe: false,
        prechecked: None,
        config: vec![],
        custom_hhi_path: None,
        custom_telemetry_data: vec![],
        allow_non_opt_build: false,
        preexisting_warnings: false,
    }
}

fn start_env(root: &str) -> client_start::Env {
    client_start::Env {
        root: root.to_string(),
        from: "".to_string(),
        no_load: false,
        watchman_debug_logging: false,
        silent: false,
        exit_on_failure: true,
        ignore_hh_version: false,
        save_64bit: None,
        save_human_readable_64bit_dep_map: None,
        saved_state_ignore_hhconfig: false,
        prechecked: None,
        mini_state: None,
        config: vec![],
        custom_hhi_path: None,
        custom_telemetry_data: vec![],
        allow_non_opt_build: false,
        preexisting_warnings: false,
    }
}

/// The client's half of each test, in the child process (does nothing in a
/// normal run). It reports on stdout, in lines that start with `D1-`: the
/// progress callbacks, the result, the `Exit_with` it raised, or the exit
/// status its `main` returned.
#[test]
fn child() {
    let Ok(scenario) = std::env::var(SCENARIO) else {
        return;
    };
    let root = std::env::var(ROOT).unwrap();
    server_files::set_tmp_FOR_TESTING_ONLY(std::env::var(TMP).unwrap());
    crate::server_progress::set_root(root.clone());
    hh_logger::level::set_min_level_stderr(hh_logger::level::T::Error);
    let calls: Arc<Mutex<Vec<Option<String>>>> = Arc::new(Mutex::new(vec![]));
    let record: ProgressCallback = {
        let calls = calls.clone();
        Arc::new(move |s| calls.lock().unwrap().push(s))
    };
    let rpc_check_liveness = |env: &Env| -> Result<(), ClientConnectError> {
        let conn = connect(env)?;
        let ((), _telemetry): ((), _) = rpc(&conn, "d1-test", T::CHECKLIVENESS)?;
        Ok(())
    };
    let res = std::panic::catch_unwind(AssertUnwindSafe(
        || -> Result<(), ClientConnectError> {
            match scenario.as_str() {
                "rpc" => {
                    rpc_check_liveness(&client_env(&root, false, None, record.clone()))?;
                    println!("D1-RESULT ok");
                }
                "rpc_deadline" => {
                    let deadline = ocaml_unix::gettimeofday() + 2.;
                    rpc_check_liveness(&client_env(&root, false, Some(deadline), record.clone()))?;
                    println!("D1-RESULT ok");
                }
                "autostart" => {
                    rpc_check_liveness(&client_env(&root, true, None, record.clone()))?;
                    println!("D1-RESULT ok");
                }
                "spinner" => {
                    let (res, captured) = crate::client_spinner::tests::with_captured_stderr(|| {
                        let spinner: ProgressCallback =
                            Arc::new(|s| crate::client_spinner::report(true, false, s));
                        rpc_check_liveness(&client_env(&root, false, None, spinner))
                    });
                    res?;
                    println!("D1-SPINNER {:?}", captured);
                    println!("D1-RESULT ok");
                }
                "start" => {
                    let es = client_start::main(&start_env(&root))?;
                    println!("D1-RETURN {}", exit_status::show(&es));
                }
                "stop" => {
                    let es = client_stop::main(&client_stop::Env {
                        root: root.clone(),
                        from: "".to_string(),
                    })?;
                    println!("D1-RETURN {}", exit_status::show(&es));
                }
                "restart" => {
                    let es = client_restart::main(&start_env(&root))?;
                    println!("D1-RETURN {}", exit_status::show(&es));
                }
                _ => panic!("unknown scenario {}", scenario),
            }
            Ok(())
        },
    ));
    println!("D1-CALLBACKS {:?}", calls.lock().unwrap());
    match res {
        Ok(Ok(())) => {}
        Ok(Err(ClientConnectError::ExitWith(e))) => println!(
            "D1-EXIT {} {}",
            exit_status::show(&e.0),
            exit_status::exit_code(&e.0)
        ),
        Ok(Err(ClientConnectError::UncaughtReadError(e))) => println!("D1-PANIC {:?}", e),
        Ok(Err(ClientConnectError::TwoRetriesInARow(_))) | Err(_) => println!("D1-PANIC other"),
    }
    let _ = std::io::stdout().flush();
}

/// Runs the test server `serve` on a thread while the client of `scenario`
/// runs.
fn with_server(
    scenario: &str,
    files: &Arc<Files>,
    env: &[(&str, String)],
    serve: impl FnOnce(&Files) + Send + 'static,
) -> Outcome {
    let server = {
        let files = files.clone();
        std::thread::spawn(move || serve(&files))
    };
    let outcome = run_child(scenario, files, env);
    if let Err(e) = server.join() {
        std::panic::resume_unwind(e)
    }
    outcome
}

fn callbacks(calls: &[Option<&str>]) -> String {
    format!(
        "{:?}",
        calls
            .iter()
            .map(|c| c.map(|s| s.to_string()))
            .collect::<Vec<_>>()
    )
}

#[test]
fn connects_and_gets_a_response() {
    let files = Arc::new(Files::new("ok"));
    let listener = files.start();
    files.write_progress("typechecking");
    let out = with_server("rpc", &files, &[], move |files| {
        // Long enough for one tick of the client's wait (1s).
        serve_check_liveness(&listener, files, Duration::from_millis(1300));
        files.stop();
    });
    assert_eq!(out.line("RESULT").as_deref(), Some("ok"), "{}", out.stderr);
    assert_eq!(out.stderr, "");
    assert_eq!(out.code, 0);
    // "connecting", hidden on Hello, "connected", the progress while
    // waiting, hidden on the response (a Ping shows nothing).
    assert_eq!(
        out.line("CALLBACKS").unwrap(),
        callbacks(&[
            Some("connecting"),
            None,
            Some("connected"),
            Some("typechecking"),
            None
        ])
    );
}

#[test]
fn the_spinner_shows_the_progress() {
    let files = Arc::new(Files::new("spinner"));
    let listener = files.start();
    files.write_progress("typechecking 3/5 files");
    let out = with_server("spinner", &files, &[], move |files| {
        serve_check_liveness(&listener, files, Duration::from_millis(1300));
        files.stop();
    });
    assert_eq!(out.line("RESULT").as_deref(), Some("ok"), "{}", out.stderr);
    let spinner = out.line("SPINNER").unwrap();
    assert!(
        spinner.starts_with(r#""hh_server is busy: [connecting] "#),
        "{}",
        spinner
    );
    assert!(
        spinner.contains(r#"\r\u{1b}[0Khh_server is busy: [typechecking 3/5 files] "#),
        "{}",
        spinner
    );
    // Hidden at the end.
    assert!(spinner.ends_with(r#"\r\u{1b}[0K""#), "{}", spinner);
}

#[test]
fn no_server_and_no_autostart() {
    let files = Arc::new(Files::new("none"));
    let out = run_child("rpc", &files, &[]);
    assert_eq!(
        out.stderr,
        "Error: no hh_server running. Either start hh_server yourself or run hh_client without --autostart-server false\n"
    );
    assert_eq!(
        out.line("EXIT").as_deref(),
        Some("Exit_status.No_server_running_should_retry 6")
    );
    assert_eq!(
        out.line("CALLBACKS").unwrap(),
        callbacks(&[Some("connecting"), None])
    );
}

#[test]
fn version_mismatch_without_autostart() {
    let files = Arc::new(Files::new("mismatch"));
    let listener = files.start();
    let out = with_server("rpc", &files, &[], move |files| {
        match server_end::ack_and_handoff_client_as(
            accept(&listener),
            "other-version-rust",
            false,
            &files.server_specific_files(),
        ) {
            // The client said it would not restart the server: it is told
            // so, and the connection is closed.
            Ok(server_end::Handshake::VersionMismatch {
                monitor_will_terminate: false,
                conn: None,
            }) => {}
            _ => panic!("expected a version mismatch"),
        }
        files.stop();
    });
    let expected_start = "Error: version mismatch.\nUse --autostart-server true if you want it to restart.\n  hh_server '";
    assert!(out.stderr.starts_with(expected_start), "{}", out.stderr);
    assert!(
        out.stderr.contains("', version 'other-version-rust', launched "),
        "{}",
        out.stderr
    );
    assert!(
        out.stderr.ends_with(&format!(
            "', version '{}', launched [just now]\n",
            crate::build_id::build_revision()
        )),
        "{}",
        out.stderr
    );
    assert!(out.stderr.contains("\n  hh_client '"), "{}", out.stderr);
    assert_eq!(out.line("EXIT").as_deref(), Some("Exit_status.Build_id_mismatch 9"));
}

#[test]
fn version_mismatch_with_autostart_restarts_the_server() {
    let files = Arc::new(Files::new("restart_on_mismatch"));
    let stub = Arc::new(Stub::new("restart_on_mismatch"));
    let listener = files.start();
    let out = with_server(
        "autostart",
        &files,
        &[("HH_SERVER_PATH", stub.path())],
        {
            let stub = stub.clone();
            move |files| {
                match server_end::ack_and_handoff_client_as(
                    accept(&listener),
                    "other-version-rust",
                    false,
                    &files.server_specific_files(),
                ) {
                    Ok(server_end::Handshake::VersionMismatch {
                        monitor_will_terminate: true,
                        conn: Some(conn),
                    }) => {
                        // The server exits: its socket and lock go, and then
                        // the connection closes.
                        drop(listener);
                        files.stop();
                        drop(conn);
                    }
                    _ => panic!("expected a version mismatch the server exits on"),
                }
                // The client starts a new server, which comes up.
                stub.wait_for_run();
                let listener = files.start();
                stub.go(0);
                serve_check_liveness(&listener, files, Duration::ZERO);
                files.stop();
            }
        },
    );
    assert_eq!(out.line("RESULT").as_deref(), Some("ok"), "{}", out.stderr);
    let (mismatch, launched) = out
        .stderr
        .split_once("Going to launch a new one.\n")
        .unwrap_or_else(|| panic!("{}", out.stderr));
    assert!(
        mismatch.starts_with("hh_server's version doesn't match the client's, so it will exit.\n  hh_server '"),
        "{}",
        mismatch
    );
    assert!(mismatch.contains("', version 'other-version-rust', launched "));
    // Once, with the client's `--from`.
    let args = stub.args();
    let fd = args
        .trim_end()
        .strip_prefix(&format!("-d {} --from d1 --waiting-client ", files.root))
        .unwrap_or_else(|| panic!("hh_server was run with {:?}", args));
    assert_eq!(
        launched,
        format!(
            "Server launched with the following command:\n\t'{}' '-d' '{}' '--from' 'd1' '--waiting-client' '{}'\n",
            stub.path(),
            files.root,
            fd
        )
    );
}

#[test]
fn a_server_that_hangs_up_might_have_crashed() {
    let files = Arc::new(Files::new("hang_up"));
    let listener = files.start();
    let out = with_server("rpc", &files, &[], move |files| {
        let mut client = handoff(accept(&listener), files);
        read_check_liveness(&mut client);
        files.stop();
        drop(client);
    });
    assert_eq!(
        out.stderr,
        "Hack server disconnected suddenly. It might have crashed.\n"
    );
    assert_eq!(
        out.line("EXIT").as_deref(),
        Some("Exit_status.Server_hung_up_should_retry 6")
    );
}

#[test]
fn a_server_that_hangs_up_with_a_finale_file() {
    let files = Arc::new(Files::new("hang_up_finale"));
    let listener = files.start();
    let out = with_server("rpc", &files, &[], move |files| {
        let mut client = handoff(accept(&listener), files);
        read_check_liveness(&mut client);
        crate::rt::finale::write(
            &files.finale_file(),
            &exit_status::FinaleData {
                exit_status: exit_status::T::FailedToLoadShouldAbort,
                msg: Some("the saved state is broken".to_string()),
                stack: utils::Callstack("".to_string()),
                telemetry: None,
            },
        )
        .unwrap();
        files.stop();
        drop(client);
    });
    assert_eq!(
        out.stderr,
        "Hack server disconnected suddenly [Exit_status.Failed_to_load_should_abort]\nthe saved state is broken\n"
    );
    assert_eq!(
        out.line("EXIT").as_deref(),
        Some("Exit_status.Server_hung_up_should_abort 220")
    );
}

#[test]
fn a_failed_handoff_is_a_busy_server() {
    let files = Arc::new(Files::new("handoff_failed"));
    let listener = files.start();
    let out = with_server("rpc", &files, &[], move |files| {
        match server_end::ack_and_handoff_client(
            accept(&listener),
            false,
            &files.server_specific_files(),
        ) {
            Ok(server_end::Handshake::Handoff(mut client)) => {
                protocol::write_value(
                    &mut client.oc,
                    &MessageType::<CommandResult>::MonitorFailedToHandoff,
                )
                .unwrap();
                let _ = protocol::read_frame(&mut client.ic);
            }
            _ => panic!("expected HANDOFF_TO_SERVER"),
        }
        files.stop();
    });
    assert_eq!(out.stderr, "Hack server is too busy.\n");
    assert_eq!(
        out.line("EXIT").as_deref(),
        Some("Exit_status.Server_hung_up_should_retry 6")
    );
}

#[test]
fn the_deadline_gives_up() {
    let files = Arc::new(Files::new("deadline"));
    let listener = files.start();
    files.write_progress("busy");
    let out = with_server("rpc_deadline", &files, &[], move |files| {
        let mut client = handoff(accept(&listener), files);
        read_check_liveness(&mut client);
        // Never answers: the client hangs up when its deadline passes.
        let _ = protocol::read_frame(&mut client.ic);
        files.stop();
    });
    assert_eq!(out.stderr, "\nError: hh_client hit timeout, giving up!\n");
    assert_eq!(out.line("EXIT").as_deref(), Some("Exit_status.Out_of_time 7"));
    // The progress was shown while waiting, and hidden before the message.
    let calls = out.line("CALLBACKS").unwrap();
    assert!(
        calls.starts_with(r#"[Some("connecting"), None, Some("connected"), Some("busy"), "#),
        "{}",
        calls
    );
    assert!(calls.ends_with(", None]"), "{}", calls);
}

#[test]
fn retries_until_the_server_listens() {
    let files = Arc::new(Files::new("retry"));
    // The lock is held, but nothing listens on the socket yet: connecting
    // is refused, and the client retries.
    drop(files.start());
    let out = with_server("rpc", &files, &[], move |files| {
        std::thread::sleep(Duration::from_millis(800));
        let listener = socket::unix_socket(&files.sock);
        serve_check_liveness(&listener, files, Duration::ZERO);
        files.stop();
    });
    assert_eq!(out.line("RESULT").as_deref(), Some("ok"), "{}", out.stderr);
    assert_eq!(out.stderr, "");
    // One "connecting" per attempt, each hidden when it fails.
    let calls = out.line("CALLBACKS").unwrap();
    assert!(
        calls.starts_with(r#"[Some("connecting"), None, Some("connecting"), None, "#),
        "{}",
        calls
    );
}

#[test]
fn a_dead_server_is_reported_then_retried() {
    let files = Arc::new(Files::new("server_died"));
    let listener = files.start();
    let out = with_server("rpc", &files, &[], move |files| {
        // What OCaml's monitor does when its server has died: the version
        // check, then `Server_died` instead of the `Sentinel`, and it exits.
        let mut conn = accept(&listener);
        let _version = protocol::ocaml_frame::read_version(&mut conn).unwrap();
        protocol::ocaml_frame::write_connection_state(&mut conn, &monitor_utils::ConnectionState::ConnectionOk).unwrap();
        let _cmd: monitor_rpc::Command = protocol::read_value(&mut conn).unwrap();
        protocol::write_value(
            &mut conn,
            &prehandoff::Msg::ServerDied(prehandoff::ExitStatus {
                status: prehandoff::ProcessStatus::WEXITED(3),
                was_oom: false,
            }),
        )
        .unwrap();
        drop(conn);
        // The next connection finds a live server.
        serve_check_liveness(&listener, files, Duration::ZERO);
        files.stop();
    });
    assert_eq!(out.line("RESULT").as_deref(), Some("ok"), "{}", out.stderr);
    assert_eq!(out.stderr, "Last server exited with code: 3.\n");
}

#[test]
fn stop_shuts_the_server_down() {
    let files = Arc::new(Files::new("stop"));
    let listener = files.start();
    let out = with_server("stop", &files, &[], move |files| {
        match server_end::ack_and_handoff_client(
            accept(&listener),
            false,
            &files.server_specific_files(),
        ) {
            Ok(server_end::Handshake::ShutDown(_tracker, conn)) => {
                files.stop();
                drop(conn);
            }
            _ => panic!("expected SHUT_DOWN"),
        }
    });
    assert_eq!(
        out.stderr,
        format!(
            "Attempting to nicely kill server for {r}\nSuccessfully killed server for {r}\n",
            r = files.root
        )
    );
    assert_eq!(out.line("RETURN").as_deref(), Some("Exit_status.No_error"));
}

#[test]
fn stop_without_a_server() {
    let files = Arc::new(Files::new("stop_none"));
    let out = run_child("stop", &files, &[]);
    assert_eq!(
        out.stderr,
        format!(
            "Attempting to nicely kill server for {r}\nNo server to kill for {r}\n",
            r = files.root
        )
    );
    assert_eq!(out.line("RETURN").as_deref(), Some("Exit_status.No_error"));
}

#[test]
fn start_when_a_server_is_running() {
    let files = Arc::new(Files::new("start_running"));
    let listener = files.start();
    let out = with_server("start", &files, &[], move |files| {
        match server_end::ack_and_handoff_client(
            accept(&listener),
            false,
            &files.server_specific_files(),
        ) {
            Ok(server_end::Handshake::Handoff(_client)) => {}
            _ => panic!("expected HANDOFF_TO_SERVER"),
        }
        files.stop();
    });
    assert_eq!(
        out.stderr,
        format!(
            "Error: Server already exists for {}\nUse hh_client restart if you want to kill it and start a new one\n",
            files.root
        )
    );
    assert_eq!(
        out.line("RETURN").as_deref(),
        Some("Exit_status.Server_already_exists")
    );
}

#[test]
fn start_runs_hh_server_and_waits_for_it() {
    let files = Arc::new(Files::new("start"));
    let stub = Stub::new("start");
    stub.go(0);
    let out = run_child("start", &files, &[("HH_SERVER_PATH", stub.path())]);
    assert_eq!(out.line("RETURN").as_deref(), Some("Exit_status.No_error"), "{}", out.stderr);
    let args = stub.args();
    let fd = args
        .trim_end()
        .strip_prefix(&format!("-d {} --waiting-client ", files.root))
        .unwrap_or_else(|| panic!("hh_server was run with {:?}", args));
    assert_eq!(
        out.stderr,
        format!(
            "Server launched with the following command:\n\t'{}' '-d' '{}' '--waiting-client' '{}'\n",
            stub.path(),
            files.root,
            fd
        )
    );
}

#[test]
fn start_when_hh_server_fails() {
    let files = Arc::new(Files::new("start_fails"));
    let stub = Stub::new("start_fails");
    stub.go(3);
    let out = run_child("start", &files, &[("HH_SERVER_PATH", stub.path())]);
    // `exit_on_failure`: `Exit.exit Server_already_exists`.
    assert_eq!(out.code, 77);
    assert!(
        out.stderr.ends_with("Starting hh_server failed. Exited with status code: 3!\n"),
        "{}",
        out.stderr
    );
    assert_eq!(out.line("RETURN"), None);
}

#[test]
fn start_when_hh_server_cannot_be_run() {
    let files = Arc::new(Files::new("start_missing"));
    let missing = format!("{}/stubs/does_not_exist/hh_server", tmp());
    let out = run_child("start", &files, &[("HH_SERVER_PATH", missing.clone())]);
    assert_eq!(out.code, 77);
    assert!(
        out.stderr.starts_with(&format!(
            "Server launched with the following command:\n\t'{}' '-d' '{}' '--waiting-client' '",
            missing, files.root
        )),
        "{}",
        out.stderr
    );
    assert!(
        out.stderr.ends_with("'\nCould not start hh_server!\n"),
        "{}",
        out.stderr
    );
}

#[test]
fn restart_without_a_server_starts_one() {
    let files = Arc::new(Files::new("restart"));
    let stub = Stub::new("restart");
    stub.go(0);
    let out = run_child("restart", &files, &[("HH_SERVER_PATH", stub.path())]);
    assert_eq!(out.line("RETURN").as_deref(), Some("Exit_status.No_error"), "{}", out.stderr);
    assert!(
        out.stderr.starts_with(&format!(
            "Warning: no server to restart for {}\nServer launched with the following command:\n\t'{}' '-d' '{}' '--waiting-client' '",
            files.root,
            stub.path(),
            files.root
        )),
        "{}",
        out.stderr
    );
}

#[test]
fn restart_stops_the_server_then_starts_one() {
    let files = Arc::new(Files::new("restart_running"));
    let stub = Arc::new(Stub::new("restart_running"));
    stub.go(0);
    let listener = files.start();
    let out = with_server(
        "restart",
        &files,
        &[("HH_SERVER_PATH", stub.path())],
        move |files| match server_end::ack_and_handoff_client(
            accept(&listener),
            false,
            &files.server_specific_files(),
        ) {
            Ok(server_end::Handshake::ShutDown(_tracker, conn)) => {
                files.stop();
                drop(conn);
            }
            _ => panic!("expected SHUT_DOWN"),
        },
    );
    assert_eq!(out.line("RETURN").as_deref(), Some("Exit_status.No_error"), "{}", out.stderr);
    assert!(
        out.stderr.starts_with(&format!(
            "Attempting to nicely kill server for {r}\nSuccessfully killed server for {r}\nServer launched with the following command:\n\t'{s}' '-d' '{r}' '--waiting-client' '",
            r = files.root,
            s = stub.path(),
        )),
        "{}",
        out.stderr
    );
}

/// A server that holds its lock but does not answer (its socket refuses
/// connections), and whose pids are unknown: `nice_kill` fails, and its
/// `with _` prints its message a second time; `mean_kill` cannot find the
/// pids.
#[test]
fn stop_an_unresponsive_server_without_pids() {
    let files = Arc::new(Files::new("stop_unresponsive"));
    drop(files.start());
    let out = run_child("stop", &files, &[]);
    files.stop();
    assert_eq!(
        out.stderr,
        format!(
            "Attempting to nicely kill server for {r}\n\
             Failed to kill server nicely for {r}\n\
             Failed to kill server nicely for {r}\n\
             Attempting to meanly kill server for {r}\n\
             Unable to figure out pids of running Hack server. Try manually killing it with `pkill hh_server`\n",
            r = files.root
        )
    );
    assert_eq!(out.line("EXIT").as_deref(), Some("Exit_status.Kill_error 1"));
    assert_eq!(out.line("RETURN"), None);
}

/// `hh_client start` on a server that holds its lock but does not answer:
/// it is replaced. `nice_kill` fails, `mean_kill` kills the pids of the
/// pids file (a process that stands for the server, whose death releases
/// the lock), then a new server is started.
#[test]
fn start_replaces_an_unresponsive_server() {
    let files = Arc::new(Files::new("start_unresponsive"));
    let stub = Stub::new("start_unresponsive");
    stub.go(0);
    drop(files.start());
    let mut server = std::process::Command::new("sleep").arg("60").spawn().unwrap();
    std::fs::write(&files.pids, format!("{}\tmonitor\n", server.id())).unwrap();
    let out = with_server(
        "start",
        &files,
        &[("HH_SERVER_PATH", stub.path())],
        move |files| {
            // The server's death releases its lock.
            let _ = server.wait();
            files.stop();
        },
    );
    assert_eq!(out.line("RETURN").as_deref(), Some("Exit_status.No_error"), "{}", out.stderr);
    let args = stub.args();
    let fd = args
        .trim_end()
        .strip_prefix(&format!("-d {} --waiting-client ", files.root))
        .unwrap_or_else(|| panic!("hh_server was run with {:?}", args));
    assert_eq!(
        out.stderr,
        format!(
            "Replacing unresponsive server for {r}\n\
             Attempting to nicely kill server for {r}\n\
             Failed to kill server nicely for {r}\n\
             Failed to kill server nicely for {r}\n\
             Attempting to meanly kill server for {r}\n\
             Successfully killed server for {r}\n\
             Server launched with the following command:\n\t'{s}' '-d' '{r}' '--waiting-client' '{fd}'\n",
            r = files.root,
            s = stub.path(),
            fd = fd,
        )
    );
}

/// A server that hangs up before it answers the version: `End_of_file`,
/// which `connect_and_shut_down` does not catch, but `nice_kill`'s `with _`
/// does, quietly (its message once, and no other output).
#[test]
fn stop_a_server_that_hangs_up_at_once() {
    let files = Arc::new(Files::new("stop_hang_up"));
    let listener = files.start();
    let out = with_server("stop", &files, &[], move |files| {
        let mut conn = accept(&listener);
        let _version = protocol::ocaml_frame::read_version(&mut conn).unwrap();
        drop(conn);
        drop(listener);
        files.stop();
    });
    assert_eq!(
        out.stderr,
        format!(
            "Attempting to nicely kill server for {r}\n\
             Failed to kill server nicely for {r}\n\
             Attempting to meanly kill server for {r}\n\
             Unable to figure out pids of running Hack server. Try manually killing it with `pkill hh_server`\n",
            r = files.root
        )
    );
    assert_eq!(out.line("EXIT").as_deref(), Some("Exit_status.Kill_error 1"));
}
