// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `agent_diagnostic_formatter.ml`. See `hh/PORTING.md`.
//!
//! `Diagnostics.finalized_diagnostic` is `user_diagnostic::T<Absolute,
//! Absolute>`. Message texts are byte strings; bytes that are not UTF-8
//! become U+FFFD, as in `user_diagnostic::to_string`.

use bstr::ByteSlice;
use oxidized::message::Message;

use crate::pos::Absolute;
use crate::rt::ocaml_filename;
use crate::string_utils::lstrip;
use crate::user_diagnostic;
use crate::user_diagnostic::UserDiagnostic;
use crate::user_diagnostic::severity;

/// `Diagnostics.finalized_diagnostic`
type FinalizedDiagnostic = user_diagnostic::T<Absolute, Absolute>;

/// `Filename.concat (Sys.getcwd ()) ""`: the current directory, with a
/// trailing `/`. (`Sys.getcwd` raises `Sys_error` when it fails.)
fn getcwd_dir() -> String {
    let cwd = std::env::current_dir().unwrap_or_else(|e| panic!("Sys_error: {}", e));
    ocaml_filename::concat(&cwd.to_string_lossy(), "")
}

fn relative_path(path: &str) -> String {
    let cwd = getcwd_dir();
    lstrip(path, &cwd).to_string()
}

fn format_message(msg: &Message<Absolute>) -> String {
    let Message(pos, message) = msg;
    let (start_line, start_column, end_line, end_column_exclusive) =
        crate::pos::destruct_range_one_based(pos);
    let end_column = if crate::pos::length(pos) == 0 {
        start_column
    } else {
        end_column_exclusive - 1
    };
    format!(
        "{}:{}:{}-{}:{}: {}",
        relative_path(&crate::pos::filename(pos)),
        start_line,
        start_column,
        end_line,
        end_column,
        message.to_str_lossy()
    )
}

pub fn to_string(error: &FinalizedDiagnostic) -> String {
    let UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        custom_msgs,
        ..
    } = error;
    let mut buf = String::with_capacity(128);
    buf.push_str(&format!(
        "{}: {} ({})\n",
        severity::to_all_caps_string(severity),
        format_message(claim),
        user_diagnostic::error_code_to_string(*code)
    ));
    for reason in reasons {
        buf.push_str(&("  ".to_string() + &format_message(reason) + "\n"));
    }
    for message in custom_msgs {
        buf.push_str(&("  ".to_string() + message + "\n"));
    }
    buf.push('\n');
    buf
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rt::diagnostic_fixtures as fx;

    const SUITE: &str = "typecheck/agent_error_format";

    /// `typecheck/agent_error_format/multiline.php.exp`.
    #[test]
    fn multiline() {
        let out = fx::run_in_suite(module_path!(), "multiline", SUITE, false, || {
            let p = |start, end| fx::pos("multiline.php", start, end);
            let errors = vec![
                fx::err(
                    4110,
                    fx::msg(p((5, 9), (5, 16)), "Invalid return type"),
                    vec![
                        fx::msg(p((3, 25), (4, 6)), "Expected `dict<int, int>`"),
                        fx::msg(p((5, 9), (5, 16)), "But got `string`"),
                    ],
                ),
                fx::err(
                    4105,
                    fx::msg(
                        p((11, 2), (12, 6)),
                        "Too many positional arguments (expected 0 but got 2)",
                    ),
                    vec![fx::msg(p((8, 9), (8, 16)), "Definition is here")],
                ),
            ];
            fx::single_type_check_output(
                crate::diagnostics_state::Format::Agent,
                to_string,
                &errors,
            )
        });
        if let Some(out) = out {
            fx::assert_same_text(&out, &fx::expected(SUITE, "multiline.php.exp"));
        }
    }

    /// A zero-width position ends where it starts; custom messages are
    /// indented.
    #[test]
    fn zero_width_and_custom_messages() {
        let out = fx::run_in_suite(
            module_path!(),
            "zero_width_and_custom_messages",
            SUITE,
            false,
            || {
                let p = |start, end| fx::pos("multiline.php", start, end);
                to_string(&user_diagnostic::make_warning(
                    Some(false),
                    12001,
                    None,
                    None,
                    Some(vec!["first".to_string(), "second".to_string()]),
                    fx::msg(p((5, 9), (5, 9)), "zero width"),
                    vec![],
                ))
            },
        );
        if let Some(out) = out {
            fx::assert_same_text(
                &out,
                "WARN: multiline.php:5:10-5:10: zero width (Warn[12001])\n  first\n  second\n\n",
            );
        }
    }
}
