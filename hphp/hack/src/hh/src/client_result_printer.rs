// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_result_printer.ml`. See `hh/PORTING.md`.
//!
//! The functor `Make (Converter)` is the trait [`ResultConverter`]: a
//! converter implements it, and the printer is the functions of this
//! module, generic over it. (Used by `hh_client --save-naming`.)

use crate::yojson::safe::T as Json;

/// `Result_converter`
pub trait ResultConverter {
    type T;
    fn to_string(t: &Self::T) -> String;
    fn to_json(t: &Self::T) -> Json;
}

/// `to_json result`
pub fn to_json<C: ResultConverter>(result: &Result<C::T, String>) -> Json {
    let result = match result {
        Ok(result) => ("result".to_string(), C::to_json(result)),
        Err(s) => ("error_message".to_string(), Json::String(s.clone())),
    };
    Json::Assoc(vec![result])
}

/// `print_json res`
pub fn print_json<C: ResultConverter>(res: &Result<C::T, String>) {
    println!("{}", crate::yojson::safe::to_string(&to_json::<C>(res)))
}

/// `print_readable`
pub fn print_readable<C: ResultConverter>(res: &Result<C::T, String>) {
    use std::io::Write;
    match res {
        Ok(result) => print!("{}", C::to_string(result)),
        Err(s) => {
            let msg = format!("Error: {}", s);
            println!("{}", msg);
            let _ = std::io::stdout().flush();
            std::process::exit(1)
        }
    }
}

/// `go res output_json`
pub fn go<C: ResultConverter>(res: &Result<C::T, String>, output_json: bool) {
    if output_json {
        print_json::<C>(res)
    } else {
        print_readable::<C>(res)
    }
}

/// `Unit_converter` (`Unit_printer`)
pub struct UnitConverter;

impl ResultConverter for UnitConverter {
    type T = ();
    fn to_string(_: &()) -> String {
        "".to_string()
    }
    fn to_json(_: &()) -> Json {
        Json::String("ok".to_string())
    }
}

/// `Int_converter` (`Int_printer`)
pub struct IntConverter;

impl ResultConverter for IntConverter {
    type T = isize;
    fn to_string(t: &isize) -> String {
        t.to_string()
    }
    fn to_json(t: &isize) -> Json {
        Json::Int(*t)
    }
}
