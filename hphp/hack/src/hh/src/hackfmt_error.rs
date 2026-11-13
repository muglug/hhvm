// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `hackfmt/error/hackfmt_error.ml`.
//!
//! Owned by **FMT** (plan §7.3).
//!
//! The three exceptions of the module are the variants of [`Exn`]; `Other`
//! stands for any other OCaml exception (the `_` of
//! `get_exception_exit_value`). The `hackfmt` executable has its own copy
//! (`hackfmt/rust/src/error.rs`); this one is what the IDE side uses to turn
//! the exit status of a `hackfmt` child process into a message.

/// `exception InvalidSyntax`, `exception InvalidCliArg of string`,
/// `exception InvalidDiff of string`, and any other exception.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exn {
    InvalidSyntax,
    InvalidCliArg(String),
    InvalidDiff(String),
    /// Any other exception (its `Printexc.to_string`).
    Other(String),
}

pub fn get_exception_exit_value(exn: &Exn) -> i32 {
    match exn {
        Exn::InvalidSyntax => 2,
        Exn::InvalidCliArg(_) => 3,
        Exn::InvalidDiff(_) => 4,
        Exn::Other(_) => 255,
    }
}

pub fn get_error_string_from_exit_value(v: i32) -> &'static str {
    match v {
        2 => "File failed to parse without errors",
        3 => "Invalid argument",
        4 => "Invalid diff",
        _ => "Internal Error",
    }
}

pub fn get_error_string_from_exn(exn: &Exn) -> &'static str {
    get_error_string_from_exit_value(get_exception_exit_value(exn))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_strings_of_exit_values() {
        assert_eq!(get_error_string_from_exit_value(2), "File failed to parse without errors");
        assert_eq!(get_error_string_from_exit_value(3), "Invalid argument");
        assert_eq!(get_error_string_from_exit_value(4), "Invalid diff");
        for v in [1, 5, 127, 255, -1] {
            assert_eq!(get_error_string_from_exit_value(v), "Internal Error");
        }
    }

    #[test]
    fn exit_values_of_exceptions() {
        assert_eq!(get_exception_exit_value(&Exn::InvalidSyntax), 2);
        assert_eq!(get_exception_exit_value(&Exn::InvalidCliArg("x".into())), 3);
        assert_eq!(get_exception_exit_value(&Exn::InvalidDiff("x".into())), 4);
        assert_eq!(get_exception_exit_value(&Exn::Other("Not_found".into())), 255);
        assert_eq!(get_error_string_from_exn(&Exn::InvalidDiff("x".into())), "Invalid diff");
        assert_eq!(get_error_string_from_exn(&Exn::Other("e".into())), "Internal Error");
    }
}
