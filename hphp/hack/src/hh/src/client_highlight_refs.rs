// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_highlight_refs.ml`. See `hh/PORTING.md`. Ported by
//! F5. The printers write to stdout; `print_readable_to_string` gives the same
//! text.

use std::io::Write as _;

use crate::ide_api_types;
use crate::nuclide_rpc_message_printer;

pub fn print_json(res: &[ide_api_types::Range]) {
    nuclide_rpc_message_printer::print_json(
        &nuclide_rpc_message_printer::highlight_references_response_to_json(res),
    )
}

fn print_result(out: &mut String, pos: &ide_api_types::Range) {
    out.push_str(&ide_api_types::range_to_string_single_line(pos));
    out.push('\n');
}

/// `print_readable res`, into a buffer.
pub fn print_readable_to_string(res: &[ide_api_types::Range]) -> String {
    let mut out = String::new();
    for pos in res {
        print_result(&mut out, pos)
    }
    out.push_str(&(res.len().to_string() + " total results"));
    out.push('\n');
    out
}

pub fn print_readable(res: &[ide_api_types::Range]) {
    let s = print_readable_to_string(res);
    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(s.as_bytes());
}

pub fn go(res: &[ide_api_types::Range], output_json: bool) {
    if output_json {
        print_json(res)
    } else {
        print_readable(res)
    }
}
