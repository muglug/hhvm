// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/monitor_client_api/prehandoff.ml`: what the monitor sends
//! after `HANDOFF_TO_SERVER`, before the server's `Hello`.

use serde::Deserialize;
use serde::Serialize;

use crate::server_command_types::ServerSpecificFiles;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExitStatus {
    pub status: crate::rt::ocaml_unix::ProcessStatus,
    pub was_oom: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Msg {
    /// Last of the prehandoff messages; includes finale_file_name of server.
    Sentinel(ServerSpecificFiles),
    /// The monitor keeps a queue of connections that will need to be passed
    /// onto the next server instance. This queue has a size limit that has been
    /// reached.
    ServerDormantConnectionsLimitReached,
    /// Monitor is running but has no server - i.e. dormant. Connection has been
    /// placed on a queue to be sent to the next started server.
    ServerNotAliveDormant(String),
    /// Server process died. Connect another client to start another one.
    ServerDied(ExitStatus),
    /// Server died from a config change, and the Monitor didn't automatically
    /// start a new one because a version change in the config file.
    ServerDiedConfigChange,
}
