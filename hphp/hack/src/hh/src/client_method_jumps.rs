// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_method_jumps.ml`. See `hh/PORTING.md`.

use crate::pos::Absolute;
use crate::server_command_types::method_jumps;
use crate::yojson::safe as yojson;

fn pos_to_json(pos: &Absolute) -> yojson::T {
    let (line, start, end_) = crate::pos::info_pos(pos);
    yojson::T::Assoc(vec![
        ("file".to_string(), yojson::T::String(crate::pos::filename(pos))),
        ("line".to_string(), yojson::T::Int(line)),
        ("char_start".to_string(), yojson::T::Int(start)),
        ("char_end".to_string(), yojson::T::Int(end_)),
    ])
}

fn cls_or_mthd_to_json(name: &str, pos: &Absolute, p_name: &str) -> yojson::T {
    yojson::T::Assoc(vec![
        ("name".to_string(), yojson::T::String(crate::utils::strip_ns(name).to_string())),
        ("pos".to_string(), pos_to_json(pos)),
        (
            "parent_name".to_string(),
            yojson::T::String(crate::utils::strip_ns(p_name).to_string()),
        ),
    ])
}

pub fn to_json(input: &[method_jumps::Result]) -> yojson::T {
    yojson::T::List(
        input
            .iter()
            .map(|res| {
                yojson::T::Assoc(vec![
                    (
                        "origin".to_string(),
                        cls_or_mthd_to_json(&res.orig_name, &res.orig_pos, &res.orig_p_name),
                    ),
                    (
                        "destination".to_string(),
                        cls_or_mthd_to_json(&res.dest_name, &res.dest_pos, &res.dest_p_name),
                    ),
                ])
            })
            .collect(),
    )
}

fn print_json(res: &[method_jumps::Result]) {
    println!("{}", yojson::to_string(&to_json(res)))
}

pub fn go(res: &[method_jumps::Result], find_children: bool, output_json: bool) {
    if output_json {
        print_json(res)
    } else {
        method_jumps::print_readable(res, find_children)
    }
}
