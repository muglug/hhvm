// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/connection_tracker.ml`. See `hh/PORTING.md`.
//!
//! Ported in full by the client-connection assignment (D1), which needs it
//! (`Client_connect`, `Server_command_types.message_type`). A tracker
//! travels client -> server -> client in the socket protocol
//! (`crate::rt::protocol`), so it is `serde`.
//!
//! The deal with logging is that we normally don't want it verbose, but if something went
//! wrong then we wish it already had been verbose for a while! As a compromise here's what we'll do...
//! If any connection-tracker encounters an unfortunately slow track, then we'll turn on verbose
//! logging for EVERY SINGLE track for the next 30 seconds.
//! There's one subtlety. A tracker object is moved client -> monitor -> server -> client.
//! It is therefore easy to detect whether a cross-process delay took anomalously long,
//! e.g. the delay between client sending to monitor and monitor receiving it.
//! But it's not easy to turn on verbose logging across ALL processes in responses to that.
//! As a workaround, each tracker object itself will contain its own snapshot of its own
//! process's value of [verbose_until], and as trackers move from one process to another
//! then they'll share this as a high-water-mark.

#![allow(non_upper_case_globals)]

use std::sync::Mutex;

use serde::Deserialize;
use serde::Serialize;

use crate::hh_logger;
use crate::random_id;
use crate::rt::ocaml_unix;
use crate::telemetry;
use crate::utils;

/// `ref_verbose_until`
static ref_verbose_until: Mutex<f64> = Mutex::new(0.);

fn get_ref_verbose_until() -> f64 {
    *ref_verbose_until.lock().unwrap_or_else(|e| e.into_inner())
}

fn set_ref_verbose_until(v: f64) {
    *ref_verbose_until.lock().unwrap_or_else(|e| e.into_inner()) = v;
}

/// The connection events whose timestamps we want to track.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Key {
    /// Client starts connection to monitor
    ClientStartConnect,
    /// Has opened socket to monitor
    ClientOpenedSocket,
    /// Has sent version to the monitor
    ClientSentVersion,
    /// Has received cstate from monitor
    ClientGotCstate,
    /// Will now send the tracker to monitor
    ClientReadyToSendHandoff,
    /// The monitor received handoff from client
    MonitorReceivedHandoff,
    /// Monitor is now ready to do its work
    MonitorReady,
    /// Monitor has sent ack back to client
    MonitorSentAckToClient,
    /// Received ack from monitor
    ClientConnectedToMonitor,
    /// Server loops doing slices of major GC...
    ServerSleepAndCheck,
    /// ...until it detects data on monitor's FD
    ServerMonitorFdReady,
    /// Synchronously reads tracker from monitor
    ServerGotTracker,
    /// Synchronously reads the client FD from monitor
    ServerGotClientFd,
    /// serve_one_iteration is ready
    ServerStartRecheck,
    /// Finished processing all outstanding changes 1st
    ServerDoneRecheck,
    /// Sent diagnostics to persistent connection
    ServerSentDiagnostics,
    /// Now turns its attention to the client
    ServerStartHandleConnection,
    /// Has sent a hello message to the client
    ServerSentHello,
    /// Received "hello" from server
    ClientReceivedHello,
    /// Sent connection_type to server
    ClientSentConnectionType,
    /// Received connection_type from client
    ServerGotConnectionType,
    /// Ready to receive cmd from the client
    ServerWaitingForCmd,
    /// Someone invoked ClientConnect.rpc
    ClientReadyToSendCmd,
    /// Client has sent the rpc command to server
    ClientSentCmd,
    /// Received cmd from the client
    ServerGotCmd,
    /// Does another recheck if needed
    ServerDoneFullRecheck,
    /// Sent a ping; next up ServerRpc.handle
    ServerStartHandle,
    /// Has finished ServerRpc.handle
    ServerEndHandle,
    /// Received rpc response from server
    ClientReceivedResponse,
}

/// `equal_key` (`[@@deriving eq]`)
pub fn equal_key(a: Key, b: Key) -> bool {
    a == b
}

/// `show_key` (`[@@deriving show]`): `Connection_tracker.Client_start_connect`.
pub fn show_key(key: Key) -> String {
    let name = match key {
        Key::ClientStartConnect => "Client_start_connect",
        Key::ClientOpenedSocket => "Client_opened_socket",
        Key::ClientSentVersion => "Client_sent_version",
        Key::ClientGotCstate => "Client_got_cstate",
        Key::ClientReadyToSendHandoff => "Client_ready_to_send_handoff",
        Key::MonitorReceivedHandoff => "Monitor_received_handoff",
        Key::MonitorReady => "Monitor_ready",
        Key::MonitorSentAckToClient => "Monitor_sent_ack_to_client",
        Key::ClientConnectedToMonitor => "Client_connected_to_monitor",
        Key::ServerSleepAndCheck => "Server_sleep_and_check",
        Key::ServerMonitorFdReady => "Server_monitor_fd_ready",
        Key::ServerGotTracker => "Server_got_tracker",
        Key::ServerGotClientFd => "Server_got_client_fd",
        Key::ServerStartRecheck => "Server_start_recheck",
        Key::ServerDoneRecheck => "Server_done_recheck",
        Key::ServerSentDiagnostics => "Server_sent_diagnostics",
        Key::ServerStartHandleConnection => "Server_start_handle_connection",
        Key::ServerSentHello => "Server_sent_hello",
        Key::ClientReceivedHello => "Client_received_hello",
        Key::ClientSentConnectionType => "Client_sent_connection_type",
        Key::ServerGotConnectionType => "Server_got_connection_type",
        Key::ServerWaitingForCmd => "Server_waiting_for_cmd",
        Key::ClientReadyToSendCmd => "Client_ready_to_send_cmd",
        Key::ClientSentCmd => "Client_sent_cmd",
        Key::ServerGotCmd => "Server_got_cmd",
        Key::ServerDoneFullRecheck => "Server_done_full_recheck",
        Key::ServerStartHandle => "Server_start_handle",
        Key::ServerEndHandle => "Server_end_handle",
        Key::ClientReceivedResponse => "Client_received_response",
    };
    format!("Connection_tracker.{}", name)
}

/// Allow to record the timestamps on multiple connection events.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct T {
    id: String,
    /// All the (trackname, timestamp) that have been tracked, in reverse order
    rev_tracks: Vec<(Key, f64)>,
    /// each [t] will carry around a snapshot of its process's ref_verbose_until,
    /// so all the separate processes can learn about it.
    verbose_until: f64,
}

/// Create a connection tracker, which allows to record the timestamps
/// on multiple connection events.
pub fn create() -> T {
    T {
        id: random_id::short_string(),
        rev_tracks: vec![],
        verbose_until: get_ref_verbose_until(),
    }
}

/// Retrieve all the timestamps recorded so far.
pub fn get_telemetry(t: &T) -> telemetry::T {
    t.rev_tracks
        .iter()
        .fold(telemetry::create(), |telemetry, (key, value)| {
            telemetry::float_(&show_key(*key), *value, telemetry)
        })
}

/// Get the unique ID of the tracker.
pub fn log_id(t: &T) -> String {
    format!("t#{}", t.id)
}

/// Get the timestamp corresponding to last [Server_start_handle] event.
pub fn get_server_unblocked_time(t: &T) -> Option<f64> {
    t.rev_tracks.iter().find_map(|(key, time)| {
        if equal_key(*key, Key::ServerStartHandle) {
            Some(*time)
        } else {
            None
        }
    })
}

/// Add a timestamp to the tracker for event specified by [key].
/// If [log] then we'll also print this to Hh_logger.
/// If [msg] then the message will be provided to Hh_logger to.
/// Normally if this track comes a long time after the previous track then
/// we'll consider it anomalous and turn on verbose logging.
/// But in some tracks (involving the persistent connection) we'll use
/// [long_delay_okay] to indicate that a long delay is normal and shouldn't
/// activate logging.
///
/// (`log` and `long_delay_okay` default to `false`, `time` to now.)
pub fn track(
    key: Key,
    time: Option<f64>,
    log: Option<bool>,
    msg: Option<&str>,
    long_delay_okay: Option<bool>,
    t: T,
) -> T {
    let log = log.unwrap_or(false);
    let long_delay_okay = long_delay_okay.unwrap_or(false);
    let tnow = ocaml_unix::gettimeofday();
    let time = time.unwrap_or(tnow);
    set_ref_verbose_until(t.verbose_until.max(get_ref_verbose_until()));
    // If it's been more than 3s since the last track, let's turn on verbose logging for 30s
    match t.rev_tracks.first() {
        Some((_prev_key, prev_time)) if time - prev_time > 3. && !long_delay_okay => {
            set_ref_verbose_until(tnow + 30.);
            hh_logger::log(&format!(
                "[{}] Connection_tracker unfortunately slow: {:.1}s. Verbose until {}\n{}",
                log_id(&t),
                time - prev_time,
                utils::timestring(get_ref_verbose_until()),
                t.rev_tracks
                    .iter()
                    .rev()
                    .map(|(key, time)| format!(
                        "   >{} {}",
                        utils::timestring(*time),
                        show_key(*key)
                    ))
                    .collect::<Vec<_>>()
                    .join("\n")
            ));
        }
        _ => {}
    }
    let t = {
        let mut rev_tracks = t.rev_tracks;
        rev_tracks.insert(0, (key, time));
        T {
            rev_tracks,
            verbose_until: get_ref_verbose_until(),
            ..t
        }
    };
    if log || tnow < get_ref_verbose_until() {
        hh_logger::log(&format!(
            "[{}] {} {}{}",
            log_id(&t),
            show_key(key),
            msg.unwrap_or(""),
            if utils::timestring(tnow) == utils::timestring(time) {
                String::new()
            } else {
                format!(", was at {}", utils::timestring(time))
            }
        ));
    }
    t
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tracks_in_reverse_and_telemetry() {
        let t = create();
        assert!(log_id(&t).starts_with("t#"));
        let t = track(Key::ClientStartConnect, Some(10.), None, None, None, t);
        let t = track(Key::ServerStartHandle, Some(11.), None, None, None, t);
        let t = track(Key::ClientReceivedResponse, Some(12.), None, None, None, t);
        assert_eq!(get_server_unblocked_time(&t), Some(11.));
        // `List.fold` over the reversed tracks, each consed onto the
        // telemetry, which `to_yojson` reverses: the last tracked comes
        // first.
        assert_eq!(
            telemetry::to_string(None, &get_telemetry(&t)),
            r#"{"Connection_tracker.Client_received_response":12.0,"Connection_tracker.Server_start_handle":11.0,"Connection_tracker.Client_start_connect":10.0}"#
        );
        assert_eq!(get_server_unblocked_time(&create()), None);
    }
}
