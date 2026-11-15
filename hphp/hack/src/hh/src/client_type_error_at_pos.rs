// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_type_error_at_pos.ml`. See `hh/PORTING.md`.

use crate::infer_error_at_pos_service;
use crate::nuclide_rpc_message_printer;

pub fn print_json(result: infer_error_at_pos_service::Result) {
    nuclide_rpc_message_printer::print_json(&nuclide_rpc_message_printer::infer_type_error_response_to_json(
        match result {
            None => (None, None, None, None),
            Some(infer_error_at_pos_service::T {
                actual_ty_string,
                expected_ty_string,
                actual_ty_json,
                expected_ty_json,
            }) => (
                Some(actual_ty_string),
                Some(actual_ty_json),
                Some(expected_ty_string),
                Some(expected_ty_json),
            ),
        },
    ))
}

pub fn print_string(result: infer_error_at_pos_service::Result) {
    println!(
        "{}",
        match result {
            None => "(unknown)".to_string(),
            Some(infer_error_at_pos_service::T {
                actual_ty_string,
                expected_ty_string,
                ..
            }) => format!("actual: {}, expected: {}", actual_ty_string, expected_ty_string),
        }
    )
}

pub fn go(result: infer_error_at_pos_service::Result, output_json: bool) {
    if output_json { print_json(result) } else { print_string(result) }
}
