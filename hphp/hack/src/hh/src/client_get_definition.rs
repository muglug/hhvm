// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_get_definition.ml`. See `hh/PORTING.md`.
//!
//! Ported by **F1** (E1's `hh_client` printers call `go`).

use std::io::Write;

use crate::pos::Absolute;
use crate::symbol_definition;
use crate::symbol_occurrence;

pub fn print_json(
    res: &[(symbol_occurrence::T<Absolute>, Option<symbol_definition::T<Absolute>>)],
) {
    crate::nuclide_rpc_message_printer::print_json(
        &crate::nuclide_rpc_message_printer::identify_symbol_response_to_json(res),
    )
}

/// `print_readable ?short_pos x`, into a buffer.
pub fn print_readable_to_string(
    short_pos: Option<bool>,
    x: &[(symbol_occurrence::T<Absolute>, Option<symbol_definition::T<Absolute>>)],
) -> String {
    let short_pos = short_pos.unwrap_or(false);
    let mut out = String::new();
    for (occurrence, definition) in x {
        let symbol_occurrence::T {
            name,
            type_,
            pos,
            is_declaration,
            affects_prod_build,
        } = occurrence;
        out.push_str(&format!(
            "name: {}, kind: {}, span: {}, is_declaration: {}\n",
            name,
            symbol_occurrence::kind_to_string(type_),
            crate::pos::string_no_file(pos),
            is_declaration.is_some()
        ));
        out.push_str(&format!("affects_prod_build: {}\n", affects_prod_build));
        out.push_str("definition:");
        match definition {
            None => out.push_str(" None\n"),
            Some(definition) => {
                // `Out_channel.newline stdout`
                out.push('\n');
                out.push_str(&crate::file_outline::print_def_to_string(
                    Some(short_pos),
                    " ",
                    definition,
                ));
            }
        }
        out.push('\n');
    }
    out
}

pub fn print_readable(
    short_pos: Option<bool>,
    x: &[(symbol_occurrence::T<Absolute>, Option<symbol_definition::T<Absolute>>)],
) {
    let s = print_readable_to_string(short_pos, x);
    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(s.as_bytes());
}

pub fn go(
    res: &[(symbol_occurrence::T<Absolute>, Option<symbol_definition::T<Absolute>>)],
    output_json: bool,
) {
    if output_json {
        print_json(res)
    } else {
        print_readable(None, res)
    }
}
