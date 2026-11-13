// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The monitor's handling of a client, in process: the server is a pair of
//! sockets of the test. (What ends in an exit of the monitor, the restart
//! table and the lifecycle are process tests: `hh/tests/monitor/`.)

use std::cell::Cell;
use std::collections::BTreeMap;
use std::os::fd::AsRawFd;
use std::os::fd::FromRawFd;

use super::*;
use crate::rt::protocol::monitor_rpc::HandoffOptions;
use crate::rt::protocol::monitor_rpc::PipeType;
use crate::server_command_types::ServerSpecificFiles;

fn options() -> server_controller::ServerStartOptions {
    let root = std::env::temp_dir().join(format!("hh_monitor_main_{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(root.join(".hhconfig"), "").unwrap();
    let root = root.to_string_lossy().into_owned();
    std::thread::spawn(move || {
        crate::server_args::parse_options_of_argv(vec!["hh_server".to_string(), root], "usage")
            .unwrap()
    })
    .join()
    .unwrap()
}

fn env(server: ServerProcess, max_purgatory_clients: isize) -> Env {
    Env {
        informant: informant::T::Resigned,
        server,
        server_start_options: options(),
        retries: 0,
        sql_retries: 0,
        watchman_retries: 0,
        edenfs_watcher_retries: 0,
        max_purgatory_clients,
        current_version: config_file::Version::OpaqueVersion(None),
        purgatory_clients: VecDeque::new(),
        ignore_hh_version: false,
    }
}

/// A server whose three pipes are the test's: the server's ends.
fn alive() -> (ServerProcess, BTreeMap<PipeType, UnixStream>) {
    let mut out_fds = BTreeMap::new();
    let mut server_ends = BTreeMap::new();
    for p in [
        PipeType::Default,
        PipeType::Priority,
        PipeType::ForceDormantStartOnly,
    ] {
        let (a, b) = UnixStream::pair().unwrap();
        out_fds.insert(p, std::os::fd::IntoRawFd::into_raw_fd(a));
        server_ends.insert(p, b);
    }
    let (in_a, _in_b) = UnixStream::pair().unwrap();
    (
        ServerProcess::Alive(ProcessData {
            pid: -1,
            server_specific_files: ServerSpecificFiles {
                server_finale_file: "/tmp/x.fin".to_string(),
            },
            start_t: 0.,
            in_fd: std::os::fd::IntoRawFd::into_raw_fd(in_a),
            out_fds,
            last_request_handoff: Cell::new(0.),
        }),
        server_ends,
    )
}

/// What a client sends, `version` being its build id: the version, then
/// the handoff command.
fn client(version: &str, terminate: bool, pipe_type: PipeType) -> (UnixStream, UnixStream) {
    let (mut c, m) = UnixStream::pair().unwrap();
    let tracker = connection_tracker::create();
    let payload = crate::yojson::safe::to_string(&crate::yojson::safe::T::Assoc(vec![
        (
            "client_version".to_string(),
            crate::yojson::safe::T::String(version.to_string()),
        ),
        (
            "tracker_id".to_string(),
            crate::yojson::safe::T::String(connection_tracker::log_id(&tracker)),
        ),
        (
            "terminate_monitor_on_version_mismatch".to_string(),
            crate::yojson::safe::T::Bool(terminate),
        ),
    ]));
    protocol::ocaml_frame::write_version(&mut c, &payload).unwrap();
    protocol::write_value(
        &mut c,
        &monitor_rpc::Command::HANDOFF_TO_SERVER(
            tracker,
            HandoffOptions {
                force_dormant_start: false,
                pipe_type,
            },
        ),
    )
    .unwrap();
    (c, m)
}

fn read<V: serde::de::DeserializeOwned>(c: &mut UnixStream) -> V {
    protocol::read_value(c).unwrap()
}

#[test]
fn handshake_and_handoff() {
    let (server, mut server_ends) = alive();
    let mut env = env(server, 400);
    let (mut c, m) = client(&crate::build_id::build_revision(), true, PipeType::Priority);
    assert!(matches!(ack_and_handoff_client(&mut env, m), Ok(Ok(()))));
    assert_eq!(protocol::ocaml_frame::read_connection_state(&mut c).unwrap(), ConnectionState::ConnectionOk);
    assert_eq!(
        read::<prehandoff::Msg>(&mut c),
        prehandoff::Msg::Sentinel(ServerSpecificFiles {
            server_finale_file: "/tmp/x.fin".to_string()
        })
    );
    // The server gets the tracker, then the client's fd, on the pipe asked for.
    let s = server_ends.get_mut(&PipeType::Priority).unwrap();
    let msg: monitor_rpc::MonitorToServerHandoffMsg = read(s);
    assert!(msg.m2s_sequence_number >= 1);
    let fd = fd_passing::ancil_recv_fd(s.as_raw_fd()).unwrap();
    let mut handed = unsafe { UnixStream::from_raw_fd(fd) };
    // The monitor keeps the fd until the receipt. (The collector is shared
    // by the tests that run at once: its count is not checked here.)
    sent_fds_collector::collect_fds(msg.m2s_sequence_number);
    // It is the client's connection.
    protocol::write_value(&mut handed, &MessageType::<CommandResult>::Hello).unwrap();
    assert!(matches!(
        read::<MessageType<CommandResult>>(&mut c),
        MessageType::Hello
    ));
    // Nothing on the other pipes.
    for p in [PipeType::Default, PipeType::ForceDormantStartOnly] {
        let e = &server_ends[&p];
        assert!(!poll_one(e.as_raw_fd(), libc::POLLIN, 0.).unwrap());
    }
}

#[test]
fn version_mismatch_client_terminates() {
    let (server, _server_ends) = alive();
    let mut env = env(server, 400);
    let (mut c, m) = client("another-version", false, PipeType::Default);
    assert!(matches!(
        ack_and_handoff_client_as(&mut env, m, "this-version"),
        Ok(Ok(()))
    ));
    match protocol::ocaml_frame::read_connection_state(&mut c).unwrap() {
        ConnectionState::BuildIdMismatchV3(info, payload) => {
            assert_eq!(info.existing_version, "this-version");
            assert_eq!(payload, r#"{"monitor_will_terminate":false}"#);
        }
        s => panic!("{:?}", s),
    }
    // The connection is closed (the command was not read).
    assert!(matches!(
        protocol::read_value::<prehandoff::Msg>(&mut c),
        Err(ReadError::EndOfFile)
    ));
    assert!(matches!(env.server, ServerProcess::Alive(_)));
}

/// A client of the other implementation (no Rust mark in its version) that
/// asks the monitor to terminate: refused (`cross_implementation_policy`).
#[test]
fn other_implementation_refused() {
    let (server, _server_ends) = alive();
    let mut env = env(server, 400);
    let (mut c, m) = client("7c6928b554a959a2f139efbcd4a20bffc4d30717", true, PipeType::Default);
    assert!(matches!(ack_and_handoff_client(&mut env, m), Ok(Ok(()))));
    match protocol::ocaml_frame::read_connection_state(&mut c).unwrap() {
        ConnectionState::BuildIdMismatchV3(info, payload) => {
            assert_eq!(info.existing_version, crate::build_id::build_revision());
            assert_eq!(payload, r#"{"monitor_will_terminate":false}"#);
        }
        s => panic!("{:?}", s),
    }
    assert!(matches!(env.server, ServerProcess::Alive(_)));
}

#[test]
fn ignore_hh_version() {
    let (server, mut server_ends) = alive();
    let mut env = env(server, 400);
    env.ignore_hh_version = true;
    let (mut c, m) = client("another-version", true, PipeType::Default);
    assert!(matches!(
        ack_and_handoff_client_as(&mut env, m, "this-version"),
        Ok(Ok(()))
    ));
    assert_eq!(protocol::ocaml_frame::read_connection_state(&mut c).unwrap(), ConnectionState::ConnectionOk);
    assert!(matches!(read::<prehandoff::Msg>(&mut c), prehandoff::Msg::Sentinel(_)));
    let s = server_ends.get_mut(&PipeType::Default).unwrap();
    let msg: monitor_rpc::MonitorToServerHandoffMsg = read(s);
    let _ = fd_passing::ancil_recv_fd(s.as_raw_fd()).unwrap();
    sent_fds_collector::collect_fds(msg.m2s_sequence_number);
}

#[test]
fn malformed_build_id() {
    let (server, _server_ends) = alive();
    let mut env = env(server, 400);
    let (mut c, m) = UnixStream::pair().unwrap();
    protocol::ocaml_frame::write_version(&mut c, "{not json").unwrap();
    assert_eq!(
        ack_and_handoff_client(&mut env, m).ok().unwrap(),
        Err("Malformed Build ID".to_string())
    );
    // A payload of the wrong type raises (it is not "Malformed Build ID").
    let (mut c, m) = UnixStream::pair().unwrap();
    protocol::ocaml_frame::write_version(&mut c, r#"{"client_version":3}"#).unwrap();
    match ack_and_handoff_client(&mut env, m) {
        Err(e) => assert_eq!(
            format!("{:?}", e),
            r#"Yojson.Safe.Util.Type_error("Expected string or null, got int", _)"#
        ),
        Ok(_) => panic!("expected an exception"),
    }
    // No newline after the version: also "Malformed Build ID".
    let (mut c, m) = UnixStream::pair().unwrap();
    protocol::ocaml_frame::write_value(
        &mut c,
        &crate::rt::ocaml_marshal::Value::string(b"v".to_vec()),
    )
    .unwrap();
    std::io::Write::write_all(&mut c, b"x").unwrap();
    assert_eq!(
        ack_and_handoff_client(&mut env, m).ok().unwrap(),
        Err("Malformed Build ID".to_string())
    );
    // A client that hangs up before it sends its version.
    let (c, m) = UnixStream::pair().unwrap();
    drop(c);
    match ack_and_handoff_client(&mut env, m) {
        Err(e) => assert_eq!(format!("{:?}", e), "End_of_file"),
        Ok(_) => panic!("expected End_of_file"),
    }
}

#[test]
fn purgatory() {
    let mut env = env(ServerProcess::NotYetStarted, 2);
    let mut clients = vec![];
    for _ in 0..3 {
        let (mut c, m) = client(&crate::build_id::build_revision(), true, PipeType::Default);
        assert!(matches!(ack_and_handoff_client(&mut env, m), Ok(Ok(()))));
        assert_eq!(protocol::ocaml_frame::read_connection_state(&mut c).unwrap(), ConnectionState::ConnectionOk);
        assert_eq!(
            read::<prehandoff::Msg>(&mut c),
            prehandoff::Msg::ServerNotAliveDormant(
                "Server killed by informant. Waiting for next server...".to_string()
            )
        );
        clients.push(c);
    }
    // The third is over the limit.
    assert_eq!(env.purgatory_clients.len(), 2);
    assert_eq!(
        read::<prehandoff::Msg>(&mut clients[2]),
        prehandoff::Msg::ServerDormantConnectionsLimitReached
    );
    // Not yet started: they wait.
    assert!(matches!(maybe_push_purgatory_clients(&mut env), Ok(Ok(()))));
    assert_eq!(env.purgatory_clients.len(), 2);
    // A server comes: they are handed off to it.
    let (server, mut server_ends) = alive();
    env.server = server;
    assert!(matches!(maybe_push_purgatory_clients(&mut env), Ok(Ok(()))));
    assert!(env.purgatory_clients.is_empty());
    for c in clients.iter_mut().take(2) {
        assert!(matches!(read::<prehandoff::Msg>(c), prehandoff::Msg::Sentinel(_)));
    }
    let s = server_ends.get_mut(&PipeType::Default).unwrap();
    let mut last = 0;
    for _ in 0..2 {
        let msg: monitor_rpc::MonitorToServerHandoffMsg = read(s);
        let fd = fd_passing::ancil_recv_fd(s.as_raw_fd()).unwrap();
        drop(unsafe { UnixStream::from_raw_fd(fd) });
        assert!(msg.m2s_sequence_number > last);
        last = msg.m2s_sequence_number;
    }
    sent_fds_collector::collect_fds(last);
}

#[test]
fn purgatory_config_changed() {
    let mut env = env(ServerProcess::NotYetStarted, 400);
    let (mut c, m) = client(&crate::build_id::build_revision(), true, PipeType::Default);
    assert!(matches!(ack_and_handoff_client(&mut env, m), Ok(Ok(()))));
    let _ = protocol::ocaml_frame::read_connection_state(&mut c).unwrap();
    let _: prehandoff::Msg = read(&mut c);
    env.server = ServerProcess::DiedConfigChanged;
    assert!(matches!(maybe_push_purgatory_clients(&mut env), Ok(Ok(()))));
    assert_eq!(
        read::<prehandoff::Msg>(&mut c),
        prehandoff::Msg::ServerDiedConfigChange
    );
    assert!(env.purgatory_clients.is_empty());
}

#[test]
fn purgatory_client_gone() {
    let mut env = env(ServerProcess::NotYetStarted, 400);
    let (mut c, m) = client(&crate::build_id::build_revision(), true, PipeType::Default);
    assert!(matches!(ack_and_handoff_client(&mut env, m), Ok(Ok(()))));
    let _ = protocol::ocaml_frame::read_connection_state(&mut c).unwrap();
    let _: prehandoff::Msg = read(&mut c);
    drop(c);
    let (server, _server_ends) = alive();
    env.server = server;
    // EPIPE on the Sentinel: dropped, logged.
    assert!(matches!(maybe_push_purgatory_clients(&mut env), Ok(Ok(()))));
    assert!(env.purgatory_clients.is_empty());
}

#[test]
fn handoff_to_a_dead_pipe() {
    let (server, server_ends) = alive();
    let mut env = env(server, 400);
    drop(server_ends);
    let (mut c, m) = client(&crate::build_id::build_revision(), true, PipeType::Default);
    assert!(matches!(ack_and_handoff_client(&mut env, m), Ok(Ok(()))));
    let _ = protocol::ocaml_frame::read_connection_state(&mut c).unwrap();
    assert!(matches!(read::<prehandoff::Msg>(&mut c), prehandoff::Msg::Sentinel(_)));
    // EPIPE: the client is told and its connection closed.
    assert!(matches!(
        read::<MessageType<CommandResult>>(&mut c),
        MessageType::MonitorFailedToHandoff
    ));
    assert!(matches!(
        protocol::read_value::<MessageType<CommandResult>>(&mut c),
        Err(ReadError::EndOfFile)
    ));
}

#[test]
fn oom_in_dmesg() {
    let lines = vec![
        "[1.0] Out of memory: Kill process 4083583 (hh_server) score 1".to_string(),
        "[2.0] Memory cgroup out of memory: Killed process 77 (hh_server)".to_string(),
    ];
    assert!(find_oom_in_dmesg_output(4083583, "hh_server", &lines));
    assert!(find_oom_in_dmesg_output(77, "hh_server", &lines));
    assert!(!find_oom_in_dmesg_output(78, "hh_server", &lines));
    assert!(!find_oom_in_dmesg_output(77, "hh_client", &lines));
}

#[test]
fn receipt_file() {
    let f = std::env::temp_dir().join(format!("hh_receipt_{}.json", std::process::id()));
    let f = f.to_string_lossy().into_owned();
    let _ = std::fs::remove_file(&f);
    assert_eq!(monitor_rpc::read_server_receipt_to_monitor_file(&f), None);
    monitor_rpc::write_server_receipt_to_monitor_file(&f, 12);
    assert_eq!(monitor_rpc::read_server_receipt_to_monitor_file(&f), Some(12));
    monitor_rpc::write_server_receipt_to_monitor_file(&f, 3);
    assert_eq!(monitor_rpc::read_server_receipt_to_monitor_file(&f), Some(3));
    assert_eq!(
        std::fs::read_to_string(&f).unwrap(),
        r#"{ "sequence_number_high_water_mark": 3 }"#
    );
    std::fs::write(&f, "[]").unwrap();
    assert_eq!(monitor_rpc::read_server_receipt_to_monitor_file(&f), None);
    std::fs::remove_file(&f).unwrap();
}

#[test]
fn show() {
    assert_eq!(
        show_server_process(&ServerProcess::NotYetStarted),
        "Server_process.Not_yet_started"
    );
    assert_eq!(
        show_server_process(&ServerProcess::DiedConfigChanged),
        "Server_process.Died_config_changed"
    );
    assert_eq!(
        show_server_process(&ServerProcess::DiedUnexpectedly(
            ProcessStatus::WEXITED(4),
            false
        )),
        "(Server_process.Died_unexpectedly (<WEXITED 4>, false))"
    );
}
