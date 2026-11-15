// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_restart.ml`. See `hh/PORTING.md`.
//!
//! `Hack_event_logger.client_restart ~data` is a no-op in the OSS build, but
//! OCaml evaluates its argument (it reads `hh.conf` and `.hhconfig`, and can
//! fail): so does this. `Monitor_connection.server_exists` is
//! `crate::monitor_connection::server_exists`.

use crate::client_start;
use crate::client_stop;
use crate::config_file;
use crate::exit_status;
use crate::monitor_connection;
use crate::path;
use crate::server_files;
use crate::server_local_config_load;

/// What `Client_stop.kill_server` and `Client_start.start_server` let
/// through is the `Err`.
pub fn main(env: &client_start::Env) -> Result<exit_status::T, client_start::ClientStartError> {
    let _data = config_file::utils::parse_hhconfig_and_hh_conf_to_json(
        &env.root,
        &server_local_config_load::SYSTEM_CONFIG_PATH,
    );
    // `Hack_event_logger.client_restart ~data`
    if monitor_connection::server_exists(&server_files::lock_file(&env.root)) {
        client_stop::kill_server(&env.root, &env.from)?
    } else {
        eprint!(
            "Warning: no server to restart for {}\n",
            path::to_string(&env.root)
        );
    }
    client_start::start_server(env)?;
    Ok(exit_status::T::NoError)
}
