// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_rage.ml`. See `hh/PORTING.md`.

use crate::server_env;
use crate::server_rage_types;

pub fn go(_genv: &server_env::Genv, env: &server_env::Env) -> server_rage_types::Result {
    let data = format!(
        "hh_server pid={} ppid={}\ndisk_needs_parsing: {}\n",
        std::process::id(),
        std::os::unix::process::parent_id(),
        env.disk_needs_parsing
            .iter()
            .map(crate::relative_path::to_absolute)
            .collect::<Vec<_>>()
            .join(" ")
    );
    vec![server_rage_types::RageItem {
        title: "status".to_string(),
        data,
    }]
}
