// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/client_ide_daemon.ml`.
//!
//! Owned by **G1** (plan §7.3). Created empty by W0b.

use std::sync::mpsc;

use crate::client_ide_message;

/// `daemon_main args channels`: the daemon's main loop, on its own thread
/// (`Client_ide_service.make` starts it). `channels` are its input (the
/// requests) and its output (the responses and notifications).
pub fn daemon_main(
    args: client_ide_message::DaemonArgs,
    channels: (
        mpsc::Receiver<client_ide_message::TrackedT>,
        mpsc::Sender<client_ide_message::MessageFromDaemon>,
    ),
) {
    let _ = (args, channels);
    todo!("Client_ide_daemon.daemon_main: G1 in progress")
}
