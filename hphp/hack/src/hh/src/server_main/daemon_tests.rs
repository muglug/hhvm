// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Tests of the daemon's loop (`serve_one_iteration` and what it calls),
//! with a fake recheck (instead of `Server_type_check.type_check`) and a
//! fake `Server_rpc.handle`. What each test expects is what the OCaml
//! daemon does in the same situation (`server_main.ml`; the order of the
//! log lines was checked against the OCaml daemon on a small root, see the
//! comments).

use std::cell::RefCell;
use std::sync::Mutex;

use crate::client_provider_sig::S;
use crate::server_command_types;
use crate::server_command_types::CommandResult;
use crate::server_command_types::ConnectionType;
use crate::server_command_types_utils;
use crate::test_client_provider;
use super::*;

thread_local! {
    /// What happened, in order.
    static EVENTS: RefCell<Vec<String>> = const { RefCell::new(vec![]) };
    /// How many rechecks to cancel (leave `Full_check_started`) before one
    /// completes.
    static CANCELS: RefCell<usize> = const { RefCell::new(0) };
}

fn event(s: &str) {
    EVENTS.with(|e| e.borrow_mut().push(s.to_string()))
}

fn take_events() -> Vec<String> {
    EVENTS.with(|e| std::mem::take(&mut *e.borrow_mut()))
}

fn tmp() -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("hh-server-main-unit-{}", std::process::id()));
    std::fs::create_dir_all(d.join("root")).unwrap();
    d
}

fn root() -> path::T {
    path::make(&tmp().join("root").to_string_lossy())
}

/// A recheck that takes all of `disk_needs_parsing` (or is cancelled, while
/// `CANCELS` says so, as an interrupted check leaves the environment).
fn fake_type_check(
    _genv: &Genv,
    mut env: server_env::Env,
    _start_time: f64,
) -> (server_env::Env, server_type_check::CheckStats, telemetry::T) {
    let n = env.disk_needs_parsing.len() as isize;
    let cancelled = CANCELS.with(|c| {
        let mut c = c.borrow_mut();
        if *c > 0 {
            *c -= 1;
            true
        } else {
            false
        }
    });
    event(&format!(
        "type_check {}{}",
        n,
        if cancelled { " cancelled" } else { "" }
    ));
    env.disk_needs_parsing = RPSet::new();
    if !cancelled {
        env.full_check_status = FullCheckStatus::FullCheckDone;
    }
    (
        env,
        server_type_check::CheckStats {
            reparse_count: n,
            total_rechecked_count: n.max(1),
            time_first_result: None,
        },
        telemetry::create(),
    )
}

fn fake_rpc(
    _genv: &Genv,
    env: server_env::Env,
    _is_stale: bool,
    _metadata: &server_command_types::CmdMetadata,
    cmd: server_command_types::T,
) -> (server_env::Env, CommandResult) {
    event(&format!(
        "rpc {} full_check_done={}",
        server_command_types_utils::debug_describe_t(&cmd),
        server_env::is_full_check_done(env.full_check_status)
    ));
    match cmd {
        server_command_types::T::CheckLiveness => (env, CommandResult::CheckLiveness(())),
        server_command_types::T::NoPrecheckedFiles => (env, CommandResult::NoPrecheckedFiles(())),
        _ => panic!("Server_rpc.handle: not in this test"),
    }
}

/// The changes the fake notifier reports, once each.
static CHANGES: Mutex<Vec<String>> = Mutex::new(vec![]);

fn set_changes(files: &[&str]) {
    let root = path::to_string(&root());
    *CHANGES.lock().unwrap() = files.iter().map(|f| format!("{}/{}", root, f)).collect();
}

fn genv() -> Genv {
    let root = root();
    let notifier = server_notifier::init_mock(
        || {
            let files = std::mem::take(&mut *CHANGES.lock().unwrap());
            server_notifier::Changes::AsyncChanges(files.into_iter().collect())
        },
        || {
            event("sync query");
            std::mem::take(&mut *CHANGES.lock().unwrap())
                .into_iter()
                .collect()
        },
    );
    Genv {
        notifier,
        ..server_env_build::default_genv()
    }
    .with_root(&root)
}

trait WithRoot {
    fn with_root(self, root: &path::T) -> Self;
}

impl WithRoot for Genv {
    fn with_root(mut self, root: &path::T) -> Genv {
        self.options = server_args::default_options(&path::to_string(root));
        self
    }
}

/// Sets up the globals and the hooks; the environment of a server that
/// finished its init (`Full_check_done`).
fn setup() -> (std::sync::MutexGuard<'static, ()>, Genv, server_env::Env) {
    // (The progress file's root and `Server_files`' tmp directory are
    // global: take turns with the tests of `server_progress`, and use the
    // tmp directory every test uses.)
    let guard = crate::server_progress::tests::serial();
    crate::server_files::tests::testing_tmp();
    let root = root();
    relative_path::set_path_prefix(
        relative_path::Prefix::Root,
        std::path::Path::new(&path::to_string(&root)),
    );
    server_progress::set_root(root.clone());
    TYPE_CHECK_FOR_TEST.with(|h| *h.borrow_mut() = Some(Box::new(fake_type_check)));
    crate::server_command::RPC_FOR_TEST.with(|h| *h.borrow_mut() = Some(fake_rpc));
    CANCELS.with(|c| *c.borrow_mut() = 0);
    CHANGES.lock().unwrap().clear();
    take_events();
    force_break_recheck_loop_for_test(false);
    periodical::set_time_for_test(None);
    let genv = genv();
    let env = server_env_build::make_env(
        "init",
        typing_deps::mode::T::InMemoryMode(None),
        None,
        &genv.config,
        std::path::Path::new(&path::to_string(&root)),
    );
    (guard, genv, env)
}

fn progress() -> (server_progress::Disposition, String) {
    let t = server_progress::read();
    (t.disposition, t.message)
}

fn client(cp: &mut test_client_provider::T, cmd: server_command_types::T) {
    cp.mock_new_client_type(ConnectionType::NonPersistent);
    cp.mock_client_request(cmd);
}

/// No client and no change: no recheck, "ready".
#[test]
fn idle_iteration_is_ready() {
    let (_g, genv, env) = setup();
    let mut cp = test_client_provider::T::default();
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(take_events(), Vec::<String>::new());
    assert!(server_env::is_full_check_done(env.full_check_status));
    assert_eq!(
        progress(),
        (server_progress::Disposition::DReady, "ready".to_string())
    );
    // The recheck id of the iteration is the one of the stats.
    assert_eq!(
        env.init_env.recheck_id.as_deref(),
        Some(env.last_recheck_loop_stats.recheck_id.as_str())
    );
    assert_eq!(env.last_recheck_loop_stats.per_batch_telemetry.len(), 1);
}

/// A change on disk without a client: an async query (the last one was
/// more than 0.5s ago), a full check, then the loop goes on until no
/// change is left (a second query finds none).
#[test]
fn file_change_without_client() {
    let (_g, genv, env) = setup();
    let mut cp = test_client_provider::T::default();
    set_changes(&["a.php", "b.php"]);
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(take_events(), vec!["type_check 2"]);
    assert_eq!(env.last_recheck_loop_stats.total_rechecked_count, 2);
    assert_eq!(env.last_recheck_loop_stats.total_changed_files_count, 2);
    // Two batches: the check, then the query that found nothing (the head
    // of the list is the last one).
    assert_eq!(env.last_recheck_loop_stats.per_batch_telemetry.len(), 2);
    assert!(env.last_recheck_loop_stats_for_actual_work.is_some());
    // The status was written at the start of the iteration (before the
    // changes were seen): "ready".
    assert_eq!(
        progress(),
        (server_progress::Disposition::DReady, "ready".to_string())
    );
    // The next iteration is idle: "ready", the stats of the actual work are
    // kept.
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(take_events(), Vec::<String>::new());
    assert_eq!(env.last_recheck_loop_stats.total_rechecked_count, 0);
    assert_eq!(
        env.last_recheck_loop_stats_for_actual_work
            .as_ref()
            .unwrap()
            .total_rechecked_count,
        2
    );
}

/// A client arrives while a change is pending (OCaml: the handoff is read
/// first, "got tracker #1 handoff from monitor", then the recheck runs,
/// then "Serving new client obtained from monitor handoff #1"): the query
/// is synchronous, the check runs to the end before the command, which sees
/// `Full_check_done`; the progress says "working".
#[test]
fn client_during_a_check() {
    let (_g, genv, env) = setup();
    let mut cp = test_client_provider::T::default();
    set_changes(&["a.php"]);
    client(&mut cp, server_command_types::T::CheckLiveness);
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(
        take_events(),
        vec![
            "sync query",
            "type_check 1",
            "sync query",
            "rpc CHECK_LIVENESS full_check_done=true"
        ]
    );
    assert!(matches!(
        cp.get_client_response(),
        Some(CommandResult::CheckLiveness(()))
    ));
    assert!(env.nonpersistent_client_pending_command_needs_full_check.is_none());
    // `Server_command.handle` wrote "<from>:<desc>", then " done", before
    // the command ran.
    assert_eq!(
        progress(),
        (server_progress::Disposition::DWorking, "test:cmd done".to_string())
    );
}

/// A command that needs a full check while the check was interrupted (the
/// tests break the loop after one check, `force_break_recheck_loop_for_test`):
/// it is parked with its client ("[...] typechecking"), and finished at the
/// end of the iteration whose check completes.
#[test]
fn needs_full_recheck_is_parked() {
    let (_g, genv, env) = setup();
    force_break_recheck_loop_for_test(true);
    CANCELS.with(|c| *c.borrow_mut() = 1);
    let mut cp = test_client_provider::T::default();
    set_changes(&["a.php"]);
    client(&mut cp, server_command_types::T::NoPrecheckedFiles);
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(take_events(), vec!["sync query", "type_check 1 cancelled"]);
    assert!(cp.get_client_response().is_none());
    let (_, reason, _) = env
        .nonpersistent_client_pending_command_needs_full_check
        .as_ref()
        .expect("parked");
    assert_eq!(reason, "NO_PRECHECKED_FILES --from test");
    assert_eq!(
        progress(),
        (
            server_progress::Disposition::DWorking,
            "test:cmd typechecking".to_string()
        )
    );
    // The next iteration: the client is gone from the provider; with a
    // parked default client only the priority pipe is selected, and the
    // check (started) completes, then the parked command runs.
    cp.clear();
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(
        take_events(),
        vec!["type_check 0", "rpc NO_PRECHECKED_FILES full_check_done=true"]
    );
    assert!(matches!(
        cp.get_client_response(),
        Some(CommandResult::NoPrecheckedFiles(()))
    ));
    assert!(env.nonpersistent_client_pending_command_needs_full_check.is_none());
    force_break_recheck_loop_for_test(false);
}

/// A provider that records the kinds of client it was asked for.
#[derive(Default)]
struct KindRecorder {
    inner: test_client_provider::T,
    kinds: Vec<ClientKind>,
}

impl client_provider_sig::S for KindRecorder {
    fn sleep_and_check(&mut self, idle_gc_slice: isize, kind: ClientKind) -> SelectOutcome {
        self.kinds.push(kind);
        self.inner.sleep_and_check(idle_gc_slice, kind)
    }
    fn priority_fd(&self) -> Option<RawFd> {
        None
    }
    fn track(
        &mut self,
        c: &mut Client,
        key: Key,
        time: Option<f64>,
        log: Option<bool>,
        msg: Option<&str>,
        long_delay_okay: Option<bool>,
    ) {
        self.inner.track(c, key, time, log, msg, long_delay_okay)
    }
    fn read_connection_type(
        &mut self,
        c: &mut Client,
    ) -> Result<ConnectionType, client_provider_sig::ClientError> {
        self.inner.read_connection_type(c)
    }
    fn send_response_to_client(
        &mut self,
        c: &mut Client,
        response: CommandResult,
    ) -> Result<(), client_provider_sig::ClientError> {
        self.inner.send_response_to_client(c, response)
    }
    fn read_client_msg(
        &mut self,
        c: &mut Client,
    ) -> Result<server_command_types::Command, client_provider_sig::ClientError> {
        self.inner.read_client_msg(c)
    }
    fn priority_to_string(&self, c: &Client) -> String {
        self.inner.priority_to_string(c)
    }
    fn agent_session_id(&self, c: &Client) -> Option<String> {
        self.inner.agent_session_id(c)
    }
    fn shutdown_client(&mut self, c: &mut Client) {
        self.inner.shutdown_client(c)
    }
    fn ping(&mut self, c: &mut Client) -> Result<(), client_provider_sig::ClientWentAway> {
        self.inner.ping(c)
    }
    fn clone_provider(&self) -> Box<dyn client_provider_sig::S + Send> {
        self.inner.clone_provider()
    }
}

/// While a default client is parked, only priority clients are accepted
/// (`` `Priority ``), and a priority client is served at once (before the
/// parked one, whose check is not done).
#[test]
fn priority_pipe_during_a_parked_default_client() {
    let (_g, genv, env) = setup();
    force_break_recheck_loop_for_test(true);
    CANCELS.with(|c| *c.borrow_mut() = 2);
    let mut cp = KindRecorder::default();
    set_changes(&["a.php"]);
    client(&mut cp.inner, server_command_types::T::NoPrecheckedFiles);
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(cp.kinds, vec![ClientKind::Any]);
    assert!(env.nonpersistent_client_pending_command_needs_full_check.is_some());
    take_events();
    // A priority client (CHECK_LIVENESS does not need a full check).
    cp.inner.clear();
    client(&mut cp.inner, server_command_types::T::CheckLiveness);
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(cp.kinds, vec![ClientKind::Any, ClientKind::Priority]);
    assert_eq!(
        take_events(),
        vec![
            "sync query",
            "type_check 0 cancelled",
            "rpc CHECK_LIVENESS full_check_done=false"
        ]
    );
    assert!(matches!(
        cp.inner.get_client_response(),
        Some(CommandResult::CheckLiveness(()))
    ));
    assert!(env.nonpersistent_client_pending_command_needs_full_check.is_some());
    // Then the check completes and the parked client is answered.
    cp.inner.clear();
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(
        cp.kinds,
        vec![ClientKind::Any, ClientKind::Priority, ClientKind::Priority]
    );
    assert_eq!(
        take_events(),
        vec!["type_check 0", "rpc NO_PRECHECKED_FILES full_check_done=true"]
    );
    assert!(env.nonpersistent_client_pending_command_needs_full_check.is_none());
    force_break_recheck_loop_for_test(false);
}

/// A command whose handling panics (an RPC that is not ported) is
/// `Nonfatal_rpc_exception`: the connection is shut down, the environment
/// from before the command goes on.
#[test]
fn rpc_panic_closes_the_connection() {
    let (_g, genv, env) = setup();
    let mut cp = test_client_provider::T::default();
    client(&mut cp, server_command_types::T::Stats);
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(take_events(), vec!["sync query", "rpc STATS full_check_done=true"]);
    assert!(cp.get_client_response().is_none());
    assert!(server_env::is_full_check_done(env.full_check_status));
}

/// `cancel_due_to_file_changes`: the first file and the count; more than 5
/// files end with "...".
#[test]
fn cancel_messages() {
    let (_g, _genv, _env) = setup();
    let files: RPSet = ["a.php", "b.php", "c.php", "d.php", "e.php", "f.php"]
        .iter()
        .map(|f| relative_path::create(relative_path::Prefix::Root, &format!("{}/{}", path::to_string(&root()), f)))
        .collect();
    match cancel_due_to_file_changes(&files, None) {
        InterruptResult::Cancel {
            user_message,
            log_message,
            ..
        } => {
            assert!(user_message.starts_with("Files have changed on disk! ["));
            assert!(user_message.ends_with("] a.php"));
            assert_eq!(
                log_message,
                "file change interrupt handler at clock [noclock]. 6 files changed. [a.php,b.php,c.php,d.php,e.php,...]"
            );
        }
        InterruptResult::Continue => panic!("expected a cancel"),
    }
}

/// The file-change interrupt handler: the changes go to
/// `disk_needs_parsing` and the check is cancelled; without changes it
/// continues.
#[test]
fn file_changes_interrupt() {
    let (_g, genv, env) = setup();
    let mut handler = file_changes_interrupt_handler(&genv);
    let (env, r) = handler(env);
    assert!(matches!(r, InterruptResult::Continue));
    set_changes(&["x.php"]);
    let (env, r) = handler(env);
    assert!(matches!(r, InterruptResult::Cancel { .. }));
    assert_eq!(env.disk_needs_parsing.len(), 1);
}

/// `setup_interrupts`: no handler without a notifier descriptor nor a
/// priority descriptor (the defaults of hh.conf are false anyway).
#[test]
fn interrupts_of_the_test_provider() {
    let (_g, genv, env) = setup();
    let env = setup_interrupts(env, &test_client_provider::T::default());
    assert!((env.interrupt_handlers)(&genv, &env).is_empty());
}

/// The idle jobs, with a fake clock: the client log is rotated beyond 1 MB
/// (every 5 minutes); the server is unused after 7 days; the daily touch
/// touches the files of the root at the top of the tmp directory.
#[test]
fn idle_jobs() {
    let (_g, genv, env) = setup();
    let root = root();
    periodical::clear_for_test();
    let t0 = 1_000_000.0;
    periodical::set_time_for_test(Some(t0));
    server_idle::stamp_connection();
    server_idle::init(&genv, &root);
    let client_log = server_files::client_log(&root);
    std::fs::write(&client_log, vec![b'x'; 1024 * 1024 + 1]).unwrap();
    let _ = std::fs::remove_file(format!("{}.old", client_log));
    // Before 5 minutes: nothing.
    periodical::set_time_for_test(Some(t0 + 299.0));
    let env = server_idle::go(env);
    assert!(std::path::Path::new(&client_log).exists());
    // After: rotated.
    periodical::set_time_for_test(Some(t0 + 301.0));
    let env = server_idle::go(env);
    assert!(!std::path::Path::new(&client_log).exists());
    assert!(std::path::Path::new(&format!("{}.old", client_log)).exists());
    // A small log stays.
    std::fs::write(&client_log, b"small").unwrap();
    periodical::set_time_for_test(Some(t0 + 602.0));
    let env = server_idle::go(env);
    assert!(std::path::Path::new(&client_log).exists());
    // Unused: more than a week since the last connection.
    assert!(!server_idle::is_unused());
    periodical::set_time_for_test(Some(t0 + periodical::ONE_WEEK + 1.0));
    assert!(server_idle::is_unused());
    server_idle::stamp_connection();
    assert!(!server_idle::is_unused());
    // The touch of the tmp files: those of the root only, not directories.
    let tmp_dir = std::path::PathBuf::from(server_files::get_tmp());
    let mine = server_files::pids_file(&root);
    std::fs::write(&mine, b"").unwrap();
    let other = tmp_dir.join("zSotherzSroot.pids");
    std::fs::write(&other, b"").unwrap();
    let old = std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000);
    for f in [std::path::PathBuf::from(&mine), other.clone()] {
        std::fs::File::options()
            .write(true)
            .open(&f)
            .unwrap()
            .set_modified(old)
            .unwrap();
    }
    server_idle::touch_tmp_files(&server_files::get_tmp(), &root);
    let mtime = |f: &std::path::Path| std::fs::metadata(f).unwrap().modified().unwrap();
    assert!(mtime(std::path::Path::new(&mine)) > old);
    assert_eq!(mtime(&other), old);
    let _ = env;
    periodical::clear_for_test();
    periodical::set_time_for_test(None);
}

/// `Periodical.check`: a `Once` callback is dropped after the first check,
/// run or not (`async` registers one with 0 seconds left, which runs only
/// once time has passed); a periodic one runs again after its period.
#[test]
fn periodical_callbacks() {
    let (_g, _genv, env) = setup();
    periodical::clear_for_test();
    periodical::set_time_for_test(Some(10.0));
    periodical::register_callback(crate::server_idle::Callback::Periodic(
        2.0,
        2.0,
        Box::new(|env| {
            event("periodic");
            env
        }),
    ));
    server_idle::async_(Box::new(|env| {
        event("once");
        env
    }));
    let env = periodical::check(env); // delta 0: nothing
    assert_eq!(take_events(), Vec::<String>::new());
    periodical::set_time_for_test(Some(13.0));
    let env = periodical::check(env);
    assert_eq!(take_events(), vec!["periodic"]);
    periodical::set_time_for_test(Some(14.0));
    let env = periodical::check(env);
    assert_eq!(take_events(), Vec::<String>::new());
    periodical::set_time_for_test(Some(16.0));
    let _env = periodical::check(env);
    assert_eq!(take_events(), vec!["periodic"]);
    periodical::clear_for_test();
    periodical::set_time_for_test(None);
}

/// A client handed off by the monitor on the priority pipe: the
/// `monitor_to_server_handoff_msg`, then the descriptor; the receipt file
/// has the sequence number; the client's socket is the one sent.
#[test]
fn monitor_pipes_handoff() {
    use std::io::Read;
    use std::os::fd::AsRawFd;
    use std::os::unix::net::UnixStream;
    let (_g, _genv, _env) = setup();
    let (default_m, default_s) = UnixStream::pair().unwrap();
    let (mut priority_m, priority_s) = UnixStream::pair().unwrap();
    let (_dormant_m, dormant_s) = UnixStream::pair().unwrap();
    let mut cp = server_client_provider::provider_from_file_descriptors(InFds {
        default: default_s.as_raw_fd(),
        priority: priority_s.as_raw_fd(),
        force_dormant_start_only: dormant_s.as_raw_fd(),
    });
    assert!(matches!(
        cp.sleep_and_check(0, ClientKind::Any),
        SelectOutcome::SelectNothing
    ));
    let (mut client_end, server_end_) = UnixStream::pair().unwrap();
    let tracker = crate::connection_tracker::create();
    crate::rt::protocol::write_value(
        &mut priority_m,
        &crate::monitor_rpc::MonitorToServerHandoffMsg {
            m2s_tracker: tracker.clone(),
            m2s_sequence_number: 7,
            m2s_agent_session_id: None,
        },
    )
    .unwrap();
    assert_eq!(crate::libancillary::ancil_send_fd(priority_m.as_raw_fd(), server_end_.as_raw_fd()), 0);
    drop(server_end_);
    // Only the default pipe is asked for: the priority client waits.
    assert!(matches!(
        cp.sleep_and_check(0, ClientKind::ForceDormantStartOnly),
        SelectOutcome::SelectNothing
    ));
    match cp.sleep_and_check(0, ClientKind::Any) {
        SelectOutcome::SelectNew(Handoff {
            mut client,
            m2s_sequence_number,
        }) => {
            assert_eq!(m2s_sequence_number, 7);
            assert_eq!(cp.priority_to_string(&client), "high");
            cp.ping(&mut client).unwrap();
            let mut buf = [0u8; 4];
            client_end.read_exact(&mut buf).unwrap();
            cp.shutdown_client(&mut client);
        }
        _ => panic!("expected a client"),
    }
    let receipt = std::fs::read_to_string(server_files::server_receipt_to_monitor_file(
        ocaml_unix::getpid(),
    ))
    .unwrap();
    assert_eq!(receipt, "{ \"sequence_number_high_water_mark\": 7 }");
    drop(default_m);
}

/// A panic outside the RPC while handling a client (here: reading a
/// command that is not there) is handled as the OCaml's
/// `handle_client_command_try` handles any exception: the connection is shut
/// down and the server goes on with the environment from before the
/// command, its parked command included.
#[test]
fn panic_outside_the_rpc_keeps_the_environment() {
    let (_g, genv, env) = setup();
    force_break_recheck_loop_for_test(true);
    CANCELS.with(|c| *c.borrow_mut() = 2);
    let mut cp = test_client_provider::T::default();
    set_changes(&["a.php"]);
    client(&mut cp, server_command_types::T::NoPrecheckedFiles);
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert!(env.nonpersistent_client_pending_command_needs_full_check.is_some());
    take_events();
    // A client whose command cannot be read.
    cp.clear();
    cp.mock_new_client_type(ConnectionType::NonPersistent);
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert!(cp.get_client_response().is_none());
    assert!(env.nonpersistent_client_pending_command_needs_full_check.is_some());
    assert_eq!(take_events(), vec!["sync query", "type_check 0 cancelled"]);
    // The parked command is still answered once the check completes.
    cp.clear();
    let env = serve_one_iteration(&genv, env, &mut cp);
    assert_eq!(
        take_events(),
        vec!["type_check 0", "rpc NO_PRECHECKED_FILES full_check_done=true"]
    );
    assert!(env.nonpersistent_client_pending_command_needs_full_check.is_none());
    force_break_recheck_loop_for_test(false);
}
