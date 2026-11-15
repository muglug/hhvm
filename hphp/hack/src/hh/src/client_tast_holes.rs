// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_tast_holes.ml`. See `hh/PORTING.md`.

use crate::nuclide_rpc_message_printer;
use crate::pos;
use crate::tast_holes_service;

/// Convert result type to tuple since it's not available to
/// Nuclide_rpc_message_printer
fn tast_holes_result_to_tuple(t: &tast_holes_service::T) -> (String, String, String, String, pos::Pos) {
    (
        t.actual_ty_string.clone(),
        t.actual_ty_json.clone(),
        t.expected_ty_string.clone(),
        t.expected_ty_json.clone(),
        t.pos.clone(),
    )
}

pub fn print_json(print_file: bool, result: &tast_holes_service::Result) {
    nuclide_rpc_message_printer::print_json(&nuclide_rpc_message_printer::tast_holes_response_to_json(
        print_file,
        &result.iter().map(tast_holes_result_to_tuple).collect::<Vec<_>>(),
    ))
}

pub fn print_string(print_file: bool, result: &tast_holes_service::Result) {
    let printer = |p: &pos::Pos| {
        if print_file {
            pos::string(&pos::to_absolute(p))
        } else {
            pos::string_no_file(p)
        }
    };
    match &result[..] {
        [] => println!("No TAST Holes"),
        _ => {
            for t in result {
                println!(
                    "{} actual type: {}, expected type: {}",
                    printer(&t.pos),
                    t.actual_ty_string,
                    t.expected_ty_string
                )
            }
        }
    }
}

pub fn go(result: &tast_holes_service::Result, print_file: bool, output_json: bool) {
    if output_json { print_json(print_file, result) } else { print_string(print_file, result) }
}
