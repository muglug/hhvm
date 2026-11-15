// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! hackfmt_error.ml, and the OCaml exceptions hackfmt can raise.
//!
//! OCaml hackfmt reports failures by raising exceptions, some of which are
//! caught on the way up (a parse error in one of several files, an
//! `Invalid_argument` turned into an invalid CLI argument, ...). Deep in the
//! formatter they are raised here as panics carrying an [`Exn`], and caught
//! with [`catch`] where hackfmt.ml has a handler.

use std::panic::AssertUnwindSafe;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exn {
    /// `Hackfmt_error.InvalidSyntax`
    InvalidSyntax,
    /// `Hackfmt_error.InvalidCliArg`
    InvalidCliArg(String),
    /// `Hackfmt_error.InvalidDiff`
    InvalidDiff(String),
    /// `Invalid_argument`
    InvalidArgument(String),
    /// `Failure`
    Failure(String),
    /// `Sys_error`
    SysError(String),
    /// Any other exception, as printed by `Exn.to_string`.
    Other(String),
}

impl Exn {
    /// `Hackfmt_error.get_exception_exit_value`
    pub fn exit_value(&self) -> i32 {
        match self {
            Exn::InvalidSyntax => 2,
            Exn::InvalidCliArg(_) => 3,
            Exn::InvalidDiff(_) => 4,
            _ => 255,
        }
    }

    /// `Hackfmt_error.get_error_string_from_exit_value`
    pub fn error_string(&self) -> &'static str {
        match self.exit_value() {
            2 => "File failed to parse without errors",
            3 => "Invalid argument",
            4 => "Invalid diff",
            _ => "Internal Error",
        }
    }

    /// `Exn.to_string` (a human-readable s-expression).
    pub fn to_sexp_string(&self) -> String {
        match self {
            Exn::InvalidSyntax => "Hackfmt_error.InvalidSyntax".into(),
            Exn::InvalidCliArg(s) => format!("(Hackfmt_error.InvalidCliArg {})", sexp_atom(s)),
            Exn::InvalidDiff(s) => format!("(Hackfmt_error.InvalidDiff {})", sexp_atom(s)),
            Exn::InvalidArgument(s) => format!("(Invalid_argument {})", sexp_atom(s)),
            Exn::Failure(s) => format!("(Failure {})", sexp_atom(s)),
            Exn::SysError(s) => format!("(Sys_error {})", sexp_atom(s)),
            Exn::Other(s) => s.clone(),
        }
    }

    /// The message hackfmt prints before exiting (see the end of
    /// hackfmt.ml).
    pub fn message(&self) -> String {
        let err_str = self.error_string();
        match self {
            Exn::InvalidSyntax => err_str.to_string(),
            Exn::InvalidCliArg(s) | Exn::InvalidDiff(s) => format!("{}: {}", err_str, s),
            _ => format!("{}: {}", err_str, self.to_sexp_string()),
        }
    }
}

/// Sexplib's quoting of an atom (`Sexp.to_string_hum`).
fn sexp_atom(s: &str) -> String {
    let must_escape = s.is_empty()
        || s.contains("#|")
        || s.contains("|#")
        || s.bytes().any(|c| {
            matches!(c, b'"' | b'(' | b')' | b';' | b'\\' | b' ' | b'\t' | b'\n' | b'\r' | 0x0c)
                || c < 32
                || c >= 127
        })
        || s.starts_with('#') && s.len() > 1 && s.as_bytes()[1] == b'|';
    if !must_escape {
        return s.to_string();
    }
    let mut out = String::from("\"");
    for c in s.bytes() {
        match c {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\t' => out.push_str("\\t"),
            b'\r' => out.push_str("\\r"),
            8 => out.push_str("\\b"),
            32..=126 => out.push(c as char),
            _ => out.push_str(&format!("\\{:03}", c)),
        }
    }
    out.push('"');
    out
}

/// Raise an OCaml exception.
pub fn raise(e: Exn) -> ! {
    std::panic::panic_any(e)
}

/// Run `f`, catching the exception it raises. Panics that are not OCaml
/// exceptions are reported as internal errors.
pub fn catch<T>(f: impl FnOnce() -> T) -> Result<T, Exn> {
    match std::panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(v) => Ok(v),
        Err(payload) => Err(exn_of_panic(payload)),
    }
}

pub fn exn_of_panic(payload: Box<dyn std::any::Any + Send>) -> Exn {
    match payload.downcast::<Exn>() {
        Ok(e) => *e,
        Err(payload) => {
            let msg = if let Some(s) = payload.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown panic".to_string()
            };
            Exn::Failure(msg)
        }
    }
}

/// Re-raise an exception caught with [`catch`].
pub fn reraise(e: Exn) -> ! {
    std::panic::resume_unwind(Box::new(e))
}

/// Install a panic hook that stays silent for OCaml exceptions (which are
/// reported by whoever catches them) and for other panics, which are
/// reported as internal errors by the top level.
pub fn install_panic_hook() {
    std::panic::set_hook(Box::new(|_| {}));
}
