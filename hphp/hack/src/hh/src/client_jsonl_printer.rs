// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_jsonl_printer.ml`. See `hh/PORTING.md`.
//!
//! Prints JSON Lines (one JSON object per line) to stdout for [hh_client --jsonl].
//! Used by both the streaming ([go_streaming]) and non-streaming ([go]) paths
//! in {!ClientCheckStatus}. Each line has a ["kind"] field: ["diagnostic"],
//! ["summary"], ["restarted"], or ["stopped"].
//!
//! `Printf.printf "%s\n%!"` writes to stdout and flushes; a write that fails
//! panics, as it raises `Sys_error`.

use std::io::Write;

use crate::diagnostics::Format;
use crate::extended_diagnostic_formatter;
use crate::hh_version;
use crate::pos::Absolute;
use crate::user_diagnostic;
use crate::yojson::safe as yojson;

/// `Diagnostics.finalized_diagnostic`
type FinalizedDiagnostic = user_diagnostic::T<Absolute, Absolute>;

/// `Printf.printf "%s\n%!" s`
fn print_line(s: &str) {
    let mut out = std::io::stdout().lock();
    if let Err(e) = writeln!(out, "{}", s).and_then(|()| out.flush()) {
        panic!("Sys_error: {}", e)
    }
}

fn human_formatter_for(
    error_format: Format,
) -> Option<&'static dyn Fn(&FinalizedDiagnostic) -> String> {
    match error_format {
        Format::Extended => Some(&extended_diagnostic_formatter::to_string),
        Format::Context
        | Format::Agent
        | Format::Raw
        | Format::Highlighted
        | Format::Plain
        | Format::PlainHighlighted => None,
    }
}

/// The line `print_diagnostic` prints (without its newline).
pub fn diagnostic_line(error_format: Format, e: &FinalizedDiagnostic) -> String {
    let human_formatter = human_formatter_for(error_format);
    let yojson = user_diagnostic::to_json(human_formatter, |s| s, e);
    let assoc = match yojson {
        yojson::T::Assoc(fields) => {
            let mut assoc = vec![(
                "kind".to_string(),
                yojson::T::String("diagnostic".to_string()),
            )];
            assoc.extend(fields);
            assoc
        }
        _ => vec![(
            "kind".to_string(),
            yojson::T::String("diagnostic".to_string()),
        )],
    };
    yojson::to_string(&yojson::T::Assoc(assoc))
}

pub fn print_diagnostic(error_format: Format, e: &FinalizedDiagnostic) {
    print_line(&diagnostic_line(error_format, e))
}

/// The line `print_summary` prints (without its newline).
fn summary_line(passed: bool, error_count: isize, warning_count: isize) -> String {
    let obj = yojson::T::Assoc(vec![
        ("kind".to_string(), yojson::T::String("summary".to_string())),
        ("passed".to_string(), yojson::T::Bool(passed)),
        (
            "version".to_string(),
            yojson::T::String(hh_version::version()),
        ),
        ("error_count".to_string(), yojson::T::Int(error_count)),
        ("warning_count".to_string(), yojson::T::Int(warning_count)),
    ]);
    yojson::to_string(&obj)
}

pub fn print_summary(passed: bool, error_count: isize, warning_count: isize) {
    print_line(&summary_line(passed, error_count, warning_count))
}

fn kind_message_line(kind: &str, message: &str) -> String {
    let obj = yojson::T::Assoc(vec![
        ("kind".to_string(), yojson::T::String(kind.to_string())),
        (
            "message".to_string(),
            yojson::T::String(message.to_string()),
        ),
    ]);
    yojson::to_string(&obj)
}

pub fn print_restarted(message: &str) {
    print_line(&kind_message_line("restarted", message))
}

pub fn print_stopped(message: &str) {
    print_line(&kind_message_line("stopped", message))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rt::diagnostic_fixtures as fx;

    #[test]
    fn lines() {
        let e = fx::warning(
            12001,
            fx::msg(fx::pos("/nonexistent/a.php", (1, 0), (1, 3)), "m"),
            vec![],
        );
        assert_eq!(
            diagnostic_line(Format::Raw, &e),
            "{\"kind\":\"diagnostic\",\"severity\":\"warning\",\"is_trusted\":true,\"message\":[{\"descr\":\"m\",\"path\":\"/nonexistent/a.php\",\"line\":1,\"start\":1,\"end\":3,\"code\":12001}],\"custom_messages\":[]}"
        );
        assert_eq!(
            summary_line(false, 2, 1),
            format!(
                "{{\"kind\":\"summary\",\"passed\":false,\"version\":{},\"error_count\":2,\"warning_count\":1}}",
                yojson::to_string(&yojson::T::String(hh_version::version()))
            )
        );
        assert_eq!(
            kind_message_line("restarted", "a \"b\""),
            "{\"kind\":\"restarted\",\"message\":\"a \\\"b\\\"\"}"
        );
        assert_eq!(
            kind_message_line("stopped", "x"),
            "{\"kind\":\"stopped\",\"message\":\"x\"}"
        );
    }
}
