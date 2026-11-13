// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_tast_holes.ml`. See `hh/PORTING.md`.

use crate::nuclide_rpc_message_printer;
use crate::tast_holes_service;

/// Convert result type to tuple since it's not available to
/// Nuclide_rpc_message_printer
fn tast_holes_result_to_tuple(
    hole: &tast_holes_service::T,
) -> (String, String, String, String, crate::pos::Pos) {
    let tast_holes_service::T {
        pos,
        actual_ty_string,
        expected_ty_string,
        actual_ty_json,
        expected_ty_json,
    } = hole;
    (
        actual_ty_string.clone(),
        actual_ty_json.clone(),
        expected_ty_string.clone(),
        expected_ty_json.clone(),
        pos.clone(),
    )
}

fn print_json(print_file: bool, result: &tast_holes_service::Result) {
    let holes: Vec<_> = result.iter().map(tast_holes_result_to_tuple).collect();
    nuclide_rpc_message_printer::print_json(&nuclide_rpc_message_printer::tast_holes_response_to_json(
        print_file, &holes,
    ))
}

fn print_string(print_file: bool, result: &tast_holes_service::Result) {
    let printer = |pos: &crate::pos::Pos| {
        if print_file {
            crate::pos::string(&crate::pos::to_absolute(pos))
        } else {
            crate::pos::string_no_file(pos)
        }
    };
    if result.is_empty() {
        println!("No TAST Holes")
    } else {
        for tast_holes_service::T {
            pos,
            actual_ty_string,
            expected_ty_string,
            ..
        } in result
        {
            println!(
                "{} actual type: {}, expected type: {}",
                printer(pos),
                actual_ty_string,
                expected_ty_string
            )
        }
    }
}

pub fn go(result: &tast_holes_service::Result, print_file: bool, output_json: bool) {
    if output_json {
        print_json(print_file, result)
    } else {
        print_string(print_file, result)
    }
}
