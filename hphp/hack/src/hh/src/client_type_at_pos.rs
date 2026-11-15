// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_type_at_pos.ml`.

use crate::infer_at_pos_service;
use crate::nuclide_rpc_message_printer;

pub fn go(result: infer_at_pos_service::Result, output_json: bool) {
    if output_json {
        let response = match result {
            None => (None, None),
            Some((str, json)) => (Some(str), Some(json)),
        };
        nuclide_rpc_message_printer::print_json(&nuclide_rpc_message_printer::infer_type_response_to_json(
            response,
        ))
    } else {
        match result {
            Some((str, _)) => println!("{}", str),
            None => println!("(unknown)"),
        }
    }
}
