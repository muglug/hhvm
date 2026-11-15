// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_symbol_info.ml`. See `hh/PORTING.md`.

use crate::client_connect;
use crate::client_connect::ClientConnectError;
use crate::server_command_types;
use crate::yojson::safe as yojson;

pub fn go(
    conn: &client_connect::Conn,
    desc: &str,
    files: &str,
    expand_path: impl Fn(&str) -> String,
) -> Result<(), ClientConnectError> {
    let content;
    let file_list = match files {
        "-" => {
            content = {
                use std::io::Read;
                let mut s = String::new();
                let _ = std::io::stdin().read_to_string(&mut s);
                s
            };
            crate::rt::ocaml_str::split_literal("\n", &content)
        }
        _ => crate::rt::ocaml_str::split_literal(";", files),
    };
    // `List.rev_map`
    let expand_path_list: Vec<String> = file_list.iter().rev().map(|file_path| expand_path(file_path)).collect();
    let command = server_command_types::T::DumpSymbolInfo(expand_path_list);
    let (result, _telemetry): (server_command_types::symbol_info_service::Result, _) =
        client_connect::rpc(conn, desc, command)?;
    let result_json = server_command_types::symbol_info_service::to_json(&result);
    println!("{}", yojson::to_string(&result_json));
    Ok(())
}
