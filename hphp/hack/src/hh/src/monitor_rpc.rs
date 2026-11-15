// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/monitor_rpc.ml`: what the client asks for after
//! the version check, what the monitor sends the server with each client, and
//! the server's receipt file.

use serde::Deserialize;
use serde::Serialize;

use crate::connection_tracker;
use crate::hh_logger;
use crate::yojson::safe as yojson;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum PipeType {
    Default,
    Priority,
    ForceDormantStartOnly,
}

pub fn pipe_type_to_string(p: PipeType) -> &'static str {
    match p {
        PipeType::Default => "default",
        PipeType::Priority => "priority",
        PipeType::ForceDormantStartOnly => "force_dormant_start_only",
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HandoffOptions {
    /// If server is dormant because it is waiting for Informant to start one,
    /// set this to true to start a server anyway.
    pub force_dormant_start: bool,
    /// There can be multiple channels between server and monitor in order
    /// to prioritize some requests over others. Connecting code needs to specify
    /// which channel it wants to use.
    pub pipe_type: PipeType,
    /// The agent session responsible for this client request, if any.
    pub agent_session_id: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Command {
    HandoffToServer(connection_tracker::T, HandoffOptions),
    /// Shut down all servers and then the monitor.
    ShutDown(connection_tracker::T),
}

/// Sent by monitor in ServerMonitor, received by server in ServerClientProvider
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MonitorToServerHandoffMsg {
    pub m2s_tracker: connection_tracker::T,
    /// A unique number incremented for each client socket handoff from monitor to server.
    /// Useful to correlate monitor and server logs.
    pub m2s_sequence_number: isize,
    /// The agent session responsible for the handed-off client request, if any.
    pub m2s_agent_session_id: Option<String>,
}

const RECEIPT_KEY: &str = "sequence_number_high_water_mark";

/// `receipt_serialize`
pub fn receipt_serialize(i: isize) -> yojson::T {
    yojson::T::Assoc(vec![(RECEIPT_KEY.to_string(), yojson::T::Int(i))])
}

/// `receipt_deserialize`: `Err` is the `Failure` it raises.
pub fn receipt_deserialize(json: &yojson::T) -> Result<isize, String> {
    match json {
        yojson::T::Assoc(pairs) => match pairs.iter().find(|(k, _)| k == RECEIPT_KEY) {
            Some((_, yojson::T::Int(i))) => Ok(*i),
            _ => Err(format!("{} not found or not an int", RECEIPT_KEY)),
        },
        _ => Err("expected JSON object".to_string()),
    }
}

/// This writes to the specified file. Invariants maintained by callers:
/// (1) the file is deleted shortly after the server launches, if it already existed,
/// (2) after the server has first received a handoff then it writes to the file,
/// (3) after each successive handoff the server overwrites the file,
/// (4) each write is protected by a unix writer lock.
/// In case of failure, we log but don't raise exceptions, in the hope that a
/// future write will succeed.
pub fn write_server_receipt_to_monitor_file(
    server_receipt_to_monitor_file: &str,
    sequence_number_high_water_mark: isize,
) {
    // (A side effect of the world that the exit hook undoes: see
    // `exit::with_world`.)
    crate::exit::with_world(|| {
        write_server_receipt_to_monitor_file_unstopped(
            server_receipt_to_monitor_file,
            sequence_number_high_water_mark,
        )
    })
}

fn write_server_receipt_to_monitor_file_unstopped(
    server_receipt_to_monitor_file: &str,
    sequence_number_high_water_mark: isize,
) {
    let json = crate::yojson::safe::pretty_to_string(&receipt_serialize(
        sequence_number_high_water_mark,
    ));
    if let Err(e) = crate::sys_utils::protected_write_exn(server_receipt_to_monitor_file, &json) {
        hh_logger::log(&format!("SERVER_RECEIPT_TO_MONITOR(write) {:?}\n{}", e, ""));
        // `Hack_event_logger.server_receipt_to_monitor_write_exn`: a
        // no-op in the OSS build.
    }
}

/// This reads the specified file, under a unix reader lock.
/// There are legitimate scenarios where the file might not exist,
/// e.g. if the server has only recently started up and hasn't yet
/// written any receipts. In this case we return None.
/// If there are failures e.g. a malformed file content, then we write
/// a log and return None.
pub fn read_server_receipt_to_monitor_file(server_receipt_to_monitor_file: &str) -> Option<isize> {
    let content = match crate::sys_utils::protected_read_exn(server_receipt_to_monitor_file) {
        Ok(content) => content,
        Err(crate::sys_utils::ProtectedIoError::UnixError(e, _, _))
            if e.kind() == std::io::ErrorKind::NotFound =>
        {
            return None;
        }
        Err(e) => {
            hh_logger::log(&format!(
                "SERVER_RECEIPT_TO_MONITOR(read) {:?}\n{}\n{}",
                e, "", "[not yet read content]"
            ));
            return None;
        }
    };
    let res = match crate::yojson::safe::from_string(&content) {
        Ok(json) => receipt_deserialize(&json),
        Err(e) => Err(format!("Yojson.Json_error({})", crate::rt::ocaml_printf::sprintf_s(&e.0))),
    };
    match res {
        Ok(i) => Some(i),
        Err(msg) => {
            // `Hack_event_logger.server_receipt_to_monitor_read_exn`: a
            // no-op in the OSS build.
            hh_logger::log(&format!(
                "SERVER_RECEIPT_TO_MONITOR(read) {}\n{}\n{}",
                msg, "", content
            ));
            None
        }
    }
}
