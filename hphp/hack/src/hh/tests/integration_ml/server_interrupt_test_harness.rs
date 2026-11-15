// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/server_interrupt_test_harness.ml`: a real
//! daemon (monitor + server) started and queried by the real `hh_client`,
//! on a temporary root.
//!
//! `hh_client` is `$HH_CLIENT_PATH` (as the OCaml, which requires it),
//! else the `hh_client` that cargo built with this test
//! (`CARGO_BIN_EXE_hh_client_rust`), which finds its `hh_server_rust` next to it.
//! Lwt is replaced by threads and polling (same timeouts). The temporary
//! directories (`Tempfile.mkdtemp`) are made in the test's directory.

use std::io::Read;
use std::path::Path;
use std::process::Child;
use std::process::Command;
use std::process::Stdio;
use std::sync::mpsc;
use std::time::Duration;
use std::time::Instant;

use hh::server_files;
use hh::server_progress;
use hh::server_progress::errors_read;
use hh::server_progress::errors_read::ReadResult;
use hh::server_progress::ErrorsFileItem;
use hh::server_progress_lwt;
use hh::server_progress_lwt::WatchError;

pub struct T {
    pub root: String,
    pub hhi: String,
    pub tmp: String,
}

pub struct ErrorsStream {
    #[allow(dead_code)]
    fd: std::fs::File,
    queue: mpsc::Receiver<Result<ReadResult, WatchError>>,
}

fn hh_client_path() -> String {
    match std::env::var("HH_CLIENT_PATH") {
        Ok(p) => p,
        Err(_) => env!("CARGO_BIN_EXE_hh_client_rust").to_string(),
    }
}

fn now() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs_f64()
}

/// `Lwt_utils.Process_failure.to_string` (the times as seconds).
fn process_failure_to_string(
    command_line: &str,
    status: Option<std::process::ExitStatus>,
    start_time: f64,
    end_time: f64,
    stdout: &str,
    stderr: &str,
) -> String {
    use std::os::unix::process::ExitStatusExt;
    let exit_code = match status {
        Some(s) => match (s.code(), s.signal()) {
            (Some(code), _) => format!(
                "WEXITED {} ({})",
                code,
                hh::exit_status::exit_code_to_string(code as isize)
            ),
            (None, Some(sig)) => format!(
                "WSIGNALLED {}{}",
                sig,
                if sig == libc::SIGKILL { " - this often indicates a timeout" } else { "" }
            ),
            (None, None) => "unknown".to_string(),
        },
        None => "WSIGNALLED (killed) - this often indicates a timeout".to_string(),
    };
    let stderr = if stderr.is_empty() { "<none>" } else { stderr };
    format!(
        "Process '{}' failed with\nExit code: {}\n{} -- {}\nException: <none>\nStderr: {}\nStdout: {}",
        command_line, exit_code, start_time, end_time, stderr, stdout
    )
}

/// `hh env args`: runs `hh_client args` in the root with `HH_TMPDIR`,
/// cancelled after 120 s; its stdout, or the failure as a string.
pub fn hh(env: &T, args: &[&str]) -> String {
    let hh_client_path = hh_client_path();
    let start_time = now();
    let mut child = Command::new(&hh_client_path)
        .args(args)
        .current_dir(&env.root)
        .env("HH_TMPDIR", &env.tmp)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn hh_client");
    let mut stdout_pipe = child.stdout.take().unwrap();
    let mut stderr_pipe = child.stderr.take().unwrap();
    let out = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stdout_pipe.read_to_string(&mut s);
        s
    });
    let err = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stderr_pipe.read_to_string(&mut s);
        s
    });
    let deadline = Instant::now() + Duration::from_secs(120);
    let status = loop {
        match child.try_wait().expect("wait hh_client") {
            Some(status) => break Some(status),
            None if Instant::now() > deadline => {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            None => std::thread::sleep(Duration::from_millis(20)),
        }
    };
    let stdout = out.join().unwrap();
    let stderr = err.join().unwrap();
    match status {
        Some(s) if s.success() => stdout,
        _ => process_failure_to_string(
            &format!("{} {}", hh_client_path, args.join(" ")),
            status,
            start_time,
            now(),
            &stdout,
            &stderr,
        ),
    }
}

/// `with_hh_process env args f`: `f` runs while `hh_client args` runs
/// (stdin closed); the process is then killed (`process#terminate`).
pub fn with_hh_process<A>(env: &T, args: &[&str], f: impl FnOnce(&mut Child) -> A) -> A {
    let hh_client_path = hh_client_path();
    let mut process = Command::new(&hh_client_path)
        .args(args)
        .current_dir(&env.root)
        .env("HH_TMPDIR", &env.tmp)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .spawn()
        .expect("spawn hh_client");
    struct Finally<'a>(&'a mut Child);
    impl Drop for Finally<'_> {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let guard = Finally(&mut process);
    f(guard.0)
}

/// `write_files env files`
pub fn write_files(env: &T, files: &[(String, String)]) {
    for (name, contents) in files {
        std::fs::write(Path::new(&env.root).join(name), contents).expect("write_file");
    }
}

/// `wait_for_errors_file ~deadline errors_file_path`
fn wait_for_errors_file(deadline: f64, errors_file_path: &str) -> std::fs::File {
    loop {
        match std::fs::File::open(errors_file_path) {
            Ok(fd) => return fd,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                if now() > deadline {
                    panic!("Timeout waiting for {}", errors_file_path)
                }
                std::thread::sleep(Duration::from_millis(100))
            }
            Err(e) => panic!("open {}: {}", errors_file_path, e),
        }
    }
}

/// `with_current_errors_stream env f`
pub fn with_current_errors_stream<A>(env: &T, f: impl FnOnce(&ErrorsStream) -> A) -> A {
    let errors_file_path = server_files::errors_file_path(&env.root);
    let fd = wait_for_errors_file(now() + 60.0, &errors_file_path);
    let errors_read::OpenSuccess { pid, .. } = match errors_read::openfile(&fd) {
        Ok(s) => s,
        Err(e) => panic!("Option.value_exn (ErrorsRead.openfile: {:?})", e),
    };
    let queue = server_progress_lwt::watch_errors_file(pid, fd.try_clone().expect("dup"));
    f(&ErrorsStream { fd, queue })
}

fn show_errors(
    errors: &hh::relative_path::map::T<Vec<(hh::diagnostics::FinalizedDiagnostic, isize)>>,
) -> String {
    let counts: Vec<String> = errors
        .iter()
        .map(|(path, errors)| format!("{}={}", hh::relative_path::suffix(path), errors.len()))
        .collect();
    format!("Errors [{}]", counts.join(","))
}

/// `Server_progress_test_helpers.show_read_result`
pub fn show_read_result(r: &ReadResult) -> String {
    match r {
        ReadResult::RCompleted(completion, msg) => format!(
            "{} [{}]",
            server_progress::completion_reason_short_description(completion),
            msg
        ),
        ReadResult::RItem(ErrorsFileItem::Errors { errors, .. }) => show_errors(errors),
        ReadResult::RItem(ErrorsFileItem::Telemetry(t)) => {
            let key = match hh::telemetry::to_yojson(t) {
                hh::yojson::safe::T::Assoc(elems) => {
                    let mut keys: Vec<String> = elems.into_iter().map(|(k, _)| k).collect();
                    keys.sort();
                    keys.into_iter().next().unwrap_or_else(|| "[]".to_string())
                }
                _ => "[primitive]".to_string(),
            };
            format!("Telemetry [{}]", key)
        }
    }
}

/// `wait_for_event ?(timeout = 60.0) stream ~description ~matches`
pub fn wait_for_event(
    timeout: Option<f64>,
    stream: &ErrorsStream,
    description: &str,
    matches: impl Fn(&str) -> bool,
) {
    let timeout = timeout.unwrap_or(60.0);
    let deadline = Instant::now() + Duration::from_secs_f64(timeout);
    let mut observations: Vec<String> = vec![];
    loop {
        let left = deadline.saturating_duration_since(Instant::now());
        match stream.queue.recv_timeout(left) {
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                panic!("Errors stream closed before {}", description)
            }
            Err(mpsc::RecvTimeoutError::Timeout) => panic!(
                "Timed out waiting for {}. Observed:\n{}",
                description,
                observations.join("\n")
            ),
            Ok(item) => {
                let observed = match &item {
                    Err(error) => server_progress_lwt::watch_error_short_description(error).to_string(),
                    Ok(result) => show_read_result(result),
                };
                let m = matches(&observed);
                observations.push(observed);
                if m {
                    return;
                }
            }
        }
    }
}

/// `server_log_offset env`
pub fn server_log_offset(env: &T) -> u64 {
    match std::fs::metadata(server_files::log_link(&env.root)) {
        Ok(m) => m.len(),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => 0,
        Err(e) => panic!("stat: {}", e),
    }
}

/// `server_log_since env ~offset`
pub fn server_log_since(env: &T, offset: u64) -> String {
    let contents = std::fs::read(server_files::log_link(&env.root)).expect("Sys_utils.cat");
    let contents = String::from_utf8_lossy(&contents).into_owned();
    // `String.drop_prefix`
    contents.get(offset as usize..).unwrap_or("").to_string()
}

/// `wait_for_server_log ?(timeout = 60.0) env ~offset ~description ~matches`
pub fn wait_for_server_log(
    timeout: Option<f64>,
    env: &T,
    offset: u64,
    description: &str,
    matches: impl Fn(&str) -> bool,
) {
    let deadline = now() + timeout.unwrap_or(60.0);
    loop {
        let log = server_log_since(env, offset);
        if matches(&log) {
            return;
        } else if now() > deadline {
            panic!("Timed out waiting for {}. Observed:\n{}", description, log)
        } else {
            std::thread::sleep(Duration::from_millis(100))
        }
    }
}

fn mkdtemp(name: &str) -> String {
    let dir = std::path::PathBuf::from(
        std::env::var_os("HH_INTEGRATION_ML_DIR").expect("HH_INTEGRATION_ML_DIR"),
    )
    .join(name);
    std::fs::create_dir_all(&dir).expect("mkdtemp");
    std::fs::canonicalize(&dir)
        .expect("realpath")
        .to_str()
        .unwrap()
        .to_string()
}

/// `with_server ~hhconfig ~files f`
pub fn with_server(hhconfig: &str, files: &[(String, String)], f: impl FnOnce(&T)) {
    let root = mkdtemp("root");
    let hhi = mkdtemp("hhi");
    let tmp = mkdtemp("tmp");
    let env = T { root, hhi, tmp };
    struct Finally<'a>(&'a T);
    impl Drop for Finally<'_> {
        fn drop(&mut self) {
            let env = self.0;
            let _ = hh(env, &["stop"]);
            // (Kept with `HH_INTEGRATION_ML_KEEP=1`, to look at the logs.)
            if std::env::var_os("HH_INTEGRATION_ML_KEEP").is_some_and(|v| v == "1") {
                return;
            }
            let _ = std::fs::remove_dir_all(&env.root);
            let _ = std::fs::remove_dir_all(&env.hhi);
            let _ = std::fs::remove_dir_all(&env.tmp);
        }
    }
    let guard = Finally(&env);
    std::fs::write(Path::new(&env.root).join(".hhconfig"), hhconfig).expect("write_file");
    std::fs::create_dir_all(Path::new(&env.root).join(".hg")).expect("mkdir_p");
    write_files(&env, files);
    server_progress::set_root(env.root.clone());
    server_files::set_tmp_for_testing_only(env.tmp.clone());
    f(guard.0);
}
