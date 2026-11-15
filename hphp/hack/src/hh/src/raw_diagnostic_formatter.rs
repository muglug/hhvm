// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `diagnostics/raw_diagnostic_formatter.ml`. See `hh/PORTING.md`.
//!
//! `Diagnostics.finalized_diagnostic` is `user_diagnostic::T<Absolute,
//! Absolute>` (`crate::diagnostics` does not define it). Message texts
//! are byte strings; bytes that are not UTF-8 become U+FFFD, as in
//! `user_diagnostic::to_string`.

use std::io::IsTerminal;

use bstr::ByteSlice;
use oxidized::message::Message;

use crate::pos::Absolute;
use crate::rt::ocaml_filename;
use crate::string_utils::lstrip;
use crate::tty;
use crate::tty::RawColor;
use crate::tty::Style;
use crate::user_diagnostic;
use crate::user_diagnostic::Severity;
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

fn format_msg(file_clr: Style, err_clr: Style, msg: &Message<Absolute>) -> Vec<(Style, String)> {
    let Message(p, s) = msg;
    let (line, start, end_) = crate::pos::info_pos(p);
    let file_path = if std::io::stdout().is_terminal() {
        let cwd = getcwd_dir();
        lstrip(&crate::pos::filename(p), &cwd).to_string()
    } else {
        crate::pos::filename(p)
    };
    let line_clr = Style::Normal(RawColor::Green);
    let col_clr = Style::Normal(RawColor::Cyan);
    let default_clr = Style::Normal(RawColor::Default);
    vec![
        (file_clr, file_path),
        (default_clr, ":".to_string()),
        (line_clr, line.to_string()),
        (default_clr, ":".to_string()),
        (col_clr, start.to_string()),
        (default_clr, ",".to_string()),
        (col_clr, end_.to_string()),
        (default_clr, ": ".to_string()),
        (err_clr, s.to_str_lossy().into_owned()),
    ]
}

fn format_error_code(code: isize) -> Vec<(Style, String)> {
    vec![
        (Style::Normal(RawColor::Default), " (".to_string()),
        (
            Style::Normal(RawColor::Green),
            user_diagnostic::error_code_to_string(code),
        ),
        (Style::Normal(RawColor::Default), ")".to_string()),
    ]
}

fn format_severity(severity: &Severity) -> Vec<(Style, String)> {
    vec![(
        Style::Bold(severity::tty_color(severity)),
        format!("{}: ", severity::to_all_caps_string(severity)),
    )]
}

pub fn to_string(error: &FinalizedDiagnostic) -> String {
    let UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        explanation: _,
        quickfixes: _,
        custom_msgs,
        is_fixmed: _,
        function_pos: _,
    } = error;
    let newline = (Style::Normal(RawColor::Default), "\n".to_string());
    let severity_txt = format_severity(severity);
    let color = severity::tty_color(severity);
    let claim = {
        let mut claim = format_msg(Style::Bold(color), Style::Bold(RawColor::Default), claim);
        claim.extend(format_error_code(*code));
        claim.push(newline.clone());
        claim
    };
    let reasons: Vec<(Style, String)> = {
        let indent = (Style::Normal(RawColor::Default), "  ".to_string());
        reasons
            .iter()
            .flat_map(|msg| {
                let mut l = vec![indent.clone()];
                l.extend(format_msg(
                    Style::Normal(color),
                    Style::Normal(RawColor::Default),
                    msg,
                ));
                l.push(newline.clone());
                l
            })
            .collect()
    };
    let custom_msgs: Vec<(Style, String)> = match custom_msgs.as_slice() {
        [] => vec![],
        msgs => {
            let indent = (Style::Normal(RawColor::Default), "  ".to_string());
            msgs.iter()
                .flat_map(|msg| {
                    vec![
                        indent.clone(),
                        (Style::Normal(RawColor::Default), msg.clone()),
                        newline.clone(),
                    ]
                })
                .collect()
        }
    };
    let to_print = severity_txt
        .into_iter()
        .chain(claim)
        .chain(reasons)
        .chain(custom_msgs);
    if std::io::stdout().is_terminal() {
        to_print
            .map(|(c, s)| tty::apply_color(None, c, &s))
            .collect::<Vec<_>>()
            .concat()
    } else {
        to_print.map(|(_, x)| x).collect::<Vec<_>>().concat()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rt::diagnostic_fixtures as fx;

    const SUITE: &str = "error_formatting_highlighted";

    /// The directory of the suite, as the child process sees it.
    fn suite_dir() -> String {
        let dir = std::fs::canonicalize(fx::test_dir().join(SUITE)).unwrap();
        format!("{}/", dir.display())
    }

    /// `hh_client --error-format raw` with stdout piped: no colours, and the
    /// paths are not made relative to the current directory. The
    /// diagnostics are those of the suite `error_formatting_highlighted`.
    #[test]
    fn piped() {
        let out = fx::run_in_suite(module_path!(), "piped", SUITE, false, || {
            let always_true = user_diagnostic::make_warning(
                None,
                12007,
                None,
                None,
                None,
                fx::msg(
                    fx::pos("always_true.php", (4, 6), (4, 19)),
                    "Invalid comparison: This expression will always return `true`.\nA value of type `null` can never be equal to a value of type `vec<int>`",
                ),
                vec![],
            );
            let mut big_file = fx::err(
                4105,
                fx::msg(
                    fx::pos("big_file.php", (1009, 2), (1009, 8)),
                    "Too many positional arguments (expected 0 but got 1)",
                ),
                vec![fx::msg(
                    fx::pos("big_file.php", (3, 9), (3, 12)),
                    "Definition is here",
                )],
            );
            big_file.custom_msgs = vec!["custom 1".to_string(), "custom 2".to_string()];
            // A zero-width position: characters 22-22, not 22-21.
            let zero_width = fx::err(
                1002,
                fx::msg(
                    fx::pos("zero_width_syntax_err.php", (3, 21), (3, 21)),
                    "A type specifier is expected here.",
                ),
                vec![],
            );
            [always_true, big_file, zero_width]
                .iter()
                .map(to_string)
                .collect::<Vec<_>>()
                .concat()
        });
        if let Some(out) = out {
            let d = suite_dir();
            fx::assert_same_text(
                &out,
                &format!(
                    "WARN: {d}always_true.php:4:7,19: Invalid comparison: This expression will always return `true`.\n\
                     A value of type `null` can never be equal to a value of type `vec<int>` (Warn[12007])\n\
                     ERROR: {d}big_file.php:1009:3,8: Too many positional arguments (expected 0 but got 1) (Typing[4105])\n\
                     \x20 {d}big_file.php:3:10,12: Definition is here\n\
                     \x20 custom 1\n\
                     \x20 custom 2\n\
                     ERROR: {d}zero_width_syntax_err.php:3:22,22: A type specifier is expected here. (Parsing[1002])\n"
                ),
            );
        }
    }

    /// `FORCE_ERROR_COLOR` does not colour the raw format: only a terminal
    /// does.
    #[test]
    fn piped_with_force_color() {
        let out = fx::run_in_suite(
            module_path!(),
            "piped_with_force_color",
            SUITE,
            true,
            || {
                let claim = fx::msg(fx::pos("always_true.php", (4, 6), (4, 19)), "claim");
                to_string(&fx::warning(12007, claim, vec![]))
            },
        );
        if let Some(out) = out {
            fx::assert_same_text(
                &out,
                &format!(
                    "WARN: {}always_true.php:4:7,19: claim (Warn[12007])\n",
                    suite_dir()
                ),
            );
        }
    }
}
