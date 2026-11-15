// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! What a program built with Base prints for an exception that nothing
//! catches (`Base.Exn`'s uncaught-exception handler, `exn.ml`
//! `print_with_backtrace`), and the S-expressions it prints them as
//! (`Sexplib0.Sexp`: `pp_hum`, `to_string_hum`).
//!
//! The OCaml programs `hh_single_type_check` and `hh_single_complete` let
//! some exceptions escape: they print
//!
//! ```text
//! Uncaught exception:
//!
//!   (Failure "...")
//!
//! Raised at ... (the backtrace)
//! ```
//!
//! on stderr and exit with 2. [`Uncaught`] is such an exception as an error
//! value (its rendering: the sexp of `sexp_of_exn`, or `Printexc.to_string`
//! for an exception that has no sexp converter); [`message`] is the text the
//! handler prints before the backtrace. The backtrace is the OCaml's own
//! call stack: the port prints none (nothing reads it, and frames of the
//! OCaml cannot be made up).

use crate::format;
use crate::format::Formatter;

/// `Sexplib0.Sexp.t`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

/// `Sexp.Printing.default_indent`
const DEFAULT_INDENT: isize = 1;

fn must_escape(s: &[u8]) -> bool {
    let len = s.len();
    if len == 0 {
        return true;
    }
    let mut ix = len - 1;
    loop {
        match s[ix] {
            b'"' | b'(' | b')' | b';' | b'\\' => return true,
            b'|' => {
                if ix == 0 {
                    return false;
                }
                if s[ix - 1] == b'#' {
                    return true;
                }
                ix -= 1;
            }
            b'#' => {
                if ix == 0 {
                    return false;
                }
                if s[ix - 1] == b'|' {
                    return true;
                }
                ix -= 1;
            }
            0..=32 | 127..=255 => return true,
            _ => {
                if ix == 0 {
                    return false;
                }
                ix -= 1;
            }
        }
    }
}

/// `Sexp.Printing.escaped`
fn escaped(s: &[u8]) -> String {
    let mut out = String::with_capacity(s.len());
    for &c in s {
        match c {
            b'"' | b'\\' => {
                out.push('\\');
                out.push(c as char)
            }
            b'\n' => out.push_str("\\n"),
            b'\t' => out.push_str("\\t"),
            b'\r' => out.push_str("\\r"),
            8 => out.push_str("\\b"),
            b' '..=b'~' => out.push(c as char),
            c => out.push_str(&format!("\\{:03}", c)),
        }
    }
    out
}

fn esc_str(s: &[u8]) -> String {
    format!("\"{}\"", escaped(s))
}

fn is_one_line(s: &[u8]) -> bool {
    match s.iter().position(|&c| c == b'\n') {
        None => true,
        Some(index) => index + 1 == s.len(),
    }
}

fn pp_hum_maybe_esc_str(ppf: &mut Formatter, s: &str) {
    let b = s.as_bytes();
    if !must_escape(b) {
        format::pp_print_string(ppf, s)
    } else if is_one_line(b) {
        format::pp_print_string(ppf, &esc_str(b))
    } else {
        format::pp_open_box(ppf, 0);
        // the leading space is to line up the lines
        format::pp_print_string(ppf, " \"");
        let mut lines = b.split(|&c| c == b'\n').peekable();
        while let Some(line) = lines.next() {
            format::pp_print_string(ppf, &escaped(line));
            if lines.peek().is_some() {
                format::pp_print_string(ppf, "\\");
                format::pp_force_newline(ppf);
                format::pp_print_string(ppf, "\\n");
            }
        }
        format::pp_print_string(ppf, "\"");
        format::pp_close_box(ppf)
    }
}

fn pp_hum_indent(indent: isize, ppf: &mut Formatter, sexp: &Sexp) {
    match sexp {
        Sexp::Atom(s) => pp_hum_maybe_esc_str(ppf, s),
        Sexp::List(l) => match l.split_first() {
            None => format::pp_print_string(ppf, "()"),
            Some((h, t)) => {
                format::pp_open_box(ppf, indent);
                format::pp_print_string(ppf, "(");
                pp_hum_indent(indent, ppf, h);
                for x in t {
                    format::pp_print_space(ppf);
                    pp_hum_indent(indent, ppf, x);
                }
                format::pp_print_string(ppf, ")");
                format::pp_close_box(ppf)
            }
        },
    }
}

/// `Sexp.pp_hum`
pub fn pp_hum(ppf: &mut Formatter, sexp: &Sexp) {
    pp_hum_indent(DEFAULT_INDENT, ppf, sexp)
}

/// `Sexp.to_string_hum ?indent`
pub fn to_string_hum(indent: Option<isize>, sexp: &Sexp) -> String {
    match sexp {
        Sexp::Atom(s) if !s.contains('\n') => {
            if must_escape(s.as_bytes()) {
                esc_str(s.as_bytes())
            } else {
                s.clone()
            }
        }
        sexp => format::asprintf(|ppf| {
            pp_hum_indent(indent.unwrap_or(DEFAULT_INDENT), ppf, sexp);
            format::pp_print_flush(ppf)
        }),
    }
}

/// An OCaml exception that nothing catches, as the uncaught-exception
/// handler shows it (`Exn.pp`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Uncaught {
    /// `sexp_of_exn_opt exn = Some sexp`
    Sexp(Sexp),
    /// No sexp converter: `Printexc.to_string exn`.
    Printexc(String),
}

impl Uncaught {
    /// `Failure msg`
    pub fn failure(msg: impl Into<String>) -> Self {
        Self::Sexp(Sexp::List(vec![
            Sexp::Atom("Failure".to_string()),
            Sexp::Atom(msg.into()),
        ]))
    }

    /// `Sys_error msg`
    pub fn sys_error(msg: impl Into<String>) -> Self {
        Self::Sexp(Sexp::List(vec![
            Sexp::Atom("Sys_error".to_string()),
            Sexp::Atom(msg.into()),
        ]))
    }

    /// `Invalid_argument msg`
    pub fn invalid_argument(msg: impl Into<String>) -> Self {
        Self::Sexp(Sexp::List(vec![
            Sexp::Atom("Invalid_argument".to_string()),
            Sexp::Atom(msg.into()),
        ]))
    }

    /// `Stack_overflow`
    pub fn stack_overflow() -> Self {
        Self::Sexp(Sexp::Atom("Stack_overflow".to_string()))
    }

    /// `Not_found`
    pub fn not_found() -> Self {
        Self::Sexp(Sexp::Atom("Not_found".to_string()))
    }

    /// `Error.raise (Error.of_string msg)` (`Option.value_exn ~message`,
    /// `failwithf` of Base...): the exception's sexp is the message.
    pub fn error(msg: impl Into<String>) -> Self {
        Self::Sexp(Sexp::Atom(msg.into()))
    }

    /// `Arg.Bad msg`
    pub fn arg_bad(msg: impl Into<String>) -> Self {
        Self::Sexp(Sexp::List(vec![
            Sexp::Atom("Arg.Bad".to_string()),
            Sexp::Atom(msg.into()),
        ]))
    }

    /// `Exn.pp ppf exn`
    pub fn pp(&self, ppf: &mut Formatter) {
        match self {
            Self::Sexp(sexp) => pp_hum(ppf, sexp),
            Self::Printexc(s) => format::pp_print_string(ppf, s),
        }
    }
}

impl std::fmt::Display for Uncaught {
    /// `Exn.to_string` (as `Sexp.to_string_hum ~indent:2`).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sexp(sexp) => f.write_str(&to_string_hum(Some(2), sexp)),
            // (`sexp_of_exn` of an exception without a converter.)
            Self::Printexc(s) => f.write_str(&to_string_hum(
                Some(2),
                &Sexp::List(vec![Sexp::Atom(s.clone())]),
            )),
        }
    }
}

impl std::error::Error for Uncaught {}

/// `print_with_backtrace exc raw_backtrace` of `Base.Exn`, without the
/// backtrace (see the module documentation): `Format.eprintf
/// "@[<2>Uncaught exception:@\n@\n@[%a@]@]@\n@." pp exc` on `oc`.
pub fn print_with_backtrace(exn: &Uncaught, oc: &mut dyn std::io::Write) {
    let _ = oc.write_all(message(exn).as_bytes());
    let _ = oc.flush();
}

/// What [`print_with_backtrace`] prints.
pub fn message(exn: &Uncaught) -> String {
    format::asprintf(|ppf| {
        format::pp_open_box(ppf, 2);
        format::pp_print_string(ppf, "Uncaught exception:");
        format::pp_force_newline(ppf);
        format::pp_force_newline(ppf);
        format::pp_open_box(ppf, 0);
        exn.pp(ppf);
        format::pp_close_box(ppf);
        format::pp_close_box(ppf);
        format::pp_force_newline(ppf);
        format::pp_print_newline(ppf);
    })
}

/// A function that dies (`die str` of `hh_single_type_check.ml`: `str` on
/// stderr, then `exit 2`), as an error value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Die(pub String);

impl std::fmt::Display for Die {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Die {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_failure() {
        assert_eq!(
            message(&Uncaught::failure("Not a Hack file: a.php")),
            "Uncaught exception:\n  \n  (Failure \"Not a Hack file: a.php\")\n\n"
        );
        assert_eq!(
            message(&Uncaught::error("Could not find any occurrence of '^ at-caret' in source code")),
            "Uncaught exception:\n  \n  \"Could not find any occurrence of '^ at-caret' in source code\"\n\n"
        );
        assert_eq!(message(&Uncaught::not_found()), "Uncaught exception:\n  \n  Not_found\n\n");
        assert_eq!(
            message(&Uncaught::Printexc("Yojson.Json_error(\"Blank input data\")".to_string())),
            "Uncaught exception:\n  \n  Yojson.Json_error(\"Blank input data\")\n\n"
        );
    }

    /// As the OCaml prints `Failure` of a message of several lines (`hh
    /// single --find-local` of a file that is not a Hack file).
    #[test]
    fn multi_line_failure() {
        let msg = "Find locals service failed with error Not a Hack file: php.php:\nline 2 char 10\ncontent: \n<?php\nfunction f(): int { return /*range-start*/1/*range-end*/; }\n\n";
        assert_eq!(
            message(&Uncaught::failure(msg)),
            "Uncaught exception:\n  \n  (Failure\n    \"Find locals service failed with error Not a Hack file: php.php:\\\n   \\nline 2 char 10\\\n   \\ncontent: \\\n   \\n<?php\\\n   \\nfunction f(): int { return /*range-start*/1/*range-end*/; }\\\n   \\n\\\n   \\n\")\n\n"
        );
    }

    #[test]
    fn exn_to_string() {
        assert_eq!(Uncaught::failure("x y").to_string(), "(Failure \"x y\")");
        assert_eq!(Uncaught::not_found().to_string(), "Not_found");
    }

    /// `Exn.to_string`, against the OCaml (Base v0.16 `Exn.to_string` of
    /// these exceptions).
    #[test]
    fn exn_to_string_as_the_ocaml_at_the_margin() {
        let of_failure = |m: &str| Uncaught::failure(m).to_string();
        assert_eq!(of_failure("short message"), "(Failure \"short message\")");
        assert_eq!(of_failure("line one\nline two"), "(Failure  \"line one\\\n         \\nline two\")");
        assert_eq!(of_failure("has #| and |# inside"), "(Failure \"has #| and |# inside\")");
        assert_eq!(
            of_failure("a-very-long-message-without-spaces-that-goes-past-the-margin-of-format-for-sure-yes-indeed"),
            "(Failure\n  a-very-long-message-without-spaces-that-goes-past-the-margin-of-format-for-sure-yes-indeed)"
        );
        assert_eq!(
            of_failure("a long message with spaces that goes past the margin of format for sure yes indeed it does"),
            "(Failure\n  \"a long message with spaces that goes past the margin of format for sure yes indeed it does\")"
        );
        assert_eq!(of_failure(""), "(Failure \"\")");
        let of_unix_error = |m: &str| Uncaught::Printexc(m.to_string()).to_string();
        assert_eq!(
            of_unix_error("Unix.Unix_error(Unix.ENOENT, \"stat\", \"/x/new\\nline.sql\")"),
            "(\"Unix.Unix_error(Unix.ENOENT, \\\"stat\\\", \\\"/x/new\\\\nline.sql\\\")\")"
        );
        let long = "Unix.Unix_error(Unix.ENOENT, \"stat\", \"/a/very/long/path/that/goes/past/the/margin/of/format/for/sure/yes/indeed/x.sql\")";
        assert_eq!(of_unix_error(long), format!("({})", crate::rt::ocaml_printf::sprintf_s(long)));
    }
}
