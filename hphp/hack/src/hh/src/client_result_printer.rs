// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_result_printer.ml`. See `hh/PORTING.md`.
//!
//! `Make (Converter)` is [`go`] with the two functions of the converter.

use crate::yojson::safe as yojson;

fn to_json<T>(result: &Result<T, String>, converter_to_json: impl Fn(&T) -> yojson::T) -> yojson::T {
    let result = match result {
        Ok(result) => ("result".to_string(), converter_to_json(result)),
        Err(s) => ("error_message".to_string(), yojson::T::String(s.clone())),
    };
    yojson::T::Assoc(vec![result])
}

pub fn go<T>(
    res: &Result<T, String>,
    output_json: bool,
    converter_to_string: impl Fn(&T) -> String,
    converter_to_json: impl Fn(&T) -> yojson::T,
) {
    if output_json {
        println!("{}", yojson::to_string(&to_json(res, converter_to_json)))
    } else {
        match res {
            Ok(result) => print!("{}", converter_to_string(result)),
            Err(s) => {
                println!("Error: {}", s);
                {
                    use std::io::Write;
                    let _ = std::io::stdout().flush();
                }
                std::process::exit(1)
            }
        }
    }
}

/// `Unit_printer.go`
pub fn unit_printer_go(res: &Result<(), String>, output_json: bool) {
    go(res, output_json, |()| String::new(), |()| yojson::T::String("ok".to_string()))
}

/// `Int_printer.go`
pub fn int_printer_go(res: &Result<isize, String>, output_json: bool) {
    go(res, output_json, |i| i.to_string(), |i| yojson::T::Int(*i))
}
