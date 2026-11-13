// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_outline.ml`. See `hh/PORTING.md`. Ported by F5.

use crate::file_outline;
use crate::nuclide_rpc_message_printer;
use crate::pos::Absolute;
use crate::symbol_definition;

pub fn print_json(res: &[symbol_definition::T<Absolute>]) {
    nuclide_rpc_message_printer::print_json(&nuclide_rpc_message_printer::outline_response_to_json(res))
}

pub fn go(res: &[symbol_definition::T<Absolute>], output_json: bool) {
    if output_json {
        print_json(res)
    } else {
        file_outline::print(None, res)
    }
}
