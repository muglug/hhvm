// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `contextual_diagnostic_formatter.ml`. See `hh/PORTING.md`.
//!
//! `Diagnostics.finalized_diagnostic` is `user_diagnostic::T<Absolute,
//! Absolute>`. Message texts are byte strings; bytes that are not UTF-8
//! become U+FFFD, as in `user_diagnostic::to_string`.
//!
//! `to_string` catches every exception of `format_error` (`try ... with _`).
//! The one that the OCaml can raise there, `Invalid_argument` from
//! `String.make` with a negative length, is an `Err` here; anything else
//! (a panic) is caught with `catch_unwind`, except a `todo!`: that is a
//! part of the port that is missing (`Diagnostics.read_lines` on a file
//! that cannot be read, for now), not an OCaml exception, and catching it
//! would print `Error could not be pretty-printed` where the OCaml prints
//! the context. It goes on unwinding.

use std::collections::BTreeMap;
use std::panic::AssertUnwindSafe;

use bstr::ByteSlice;
use oxidized::message::Message;

use crate::diagnostics_state;
use crate::markdown_lite;
use crate::pos::Absolute;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_list;
use crate::string_utils::lstrip;
use crate::tty;
use crate::tty::RawColor;
use crate::tty::Style;
use crate::user_diagnostic;
use crate::user_diagnostic::UserDiagnostic;
use crate::user_diagnostic::severity;

/// `Diagnostics.finalized_diagnostic`
type FinalizedDiagnostic = user_diagnostic::T<Absolute, Absolute>;

/// The exception `Invalid_argument` (of `String.make`).
#[derive(Debug)]
struct InvalidArgument(#[allow(dead_code)] String);

/// `String.make n c`, which raises `Invalid_argument` when `n < 0`.
fn string_make(n: isize, c: char) -> Result<String, InvalidArgument> {
    if n < 0 {
        Err(InvalidArgument("String.create".to_string()))
    } else {
        Ok(std::iter::repeat_n(c, n as usize).collect())
    }
}

/// `Filename.concat (Sys.getcwd ()) ""`. (`Sys.getcwd` raises `Sys_error`
/// when it fails.)
fn getcwd_dir() -> String {
    let cwd = std::env::current_dir().unwrap_or_else(|e| panic!("Sys_error: {}", e));
    ocaml_filename::concat(&cwd.to_string_lossy(), "")
}

/// `Printf.sprintf "%*d" width n`: right-justified in `width` columns
/// (left-justified in `-width` when `width` is negative).
fn sprintf_star_d(width: isize, n: isize) -> String {
    let w = width.unsigned_abs();
    if width < 0 {
        format!("{:<w$}", n)
    } else {
        format!("{:>w$}", n)
    }
}

fn column_width(line_number: isize) -> isize {
    std::cmp::max(3, diagnostics_state::num_digits(line_number))
}

fn line_margin(line_num: Option<isize>, col_width: isize) -> Result<String, InvalidArgument> {
    let padded_num = match line_num {
        Some(line_num) => sprintf_star_d(col_width, line_num),
        None => string_make(col_width, ' ')?,
    };
    Ok(tty::apply_color(
        None,
        Style::Normal(RawColor::Cyan),
        &(padded_num + " |"),
    ))
}

/// Get the lines of source code associated with this position.
fn load_context_lines(pos: &Absolute) -> Vec<String> {
    let path = crate::pos::filename(pos);
    let line = crate::pos::line(pos);
    let end_line = crate::pos::end_line(pos);

    let lines = diagnostics_state::read_lines(&path);
    // Line numbers are 1-indexed.
    lines
        .into_iter()
        .enumerate()
        .filter(|(i, _)| *i as isize + 1 >= line && *i as isize + 1 <= end_line)
        .map(|(_, l)| l)
        .collect()
}

fn format_context_lines(
    pos: &Absolute,
    lines: &[String],
    col_width: isize,
) -> Result<String, InvalidArgument> {
    let no_source;
    let lines = match lines {
        [] => {
            no_source = [tty::apply_color(
                None,
                Style::Dim(RawColor::Default),
                "No source found",
            )];
            &no_source[..]
        }
        ls => ls,
    };
    let line_num = crate::pos::line(pos);
    let format_line = |i: usize, line: &String| -> Result<String, InvalidArgument> {
        Ok(format!(
            "{} {}",
            line_margin(Some(line_num + i as isize), col_width)?,
            line
        ))
    };
    let formatted_lines = lines
        .iter()
        .enumerate()
        .map(|(i, line)| format_line(i, line))
        .collect::<Result<Vec<_>, _>>()?;
    // TODO: display all the lines, showing the underline on all of them.
    Ok(formatted_lines
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("List.hd_exn")))
}

fn format_filename(pos: &Absolute) -> String {
    let relative_path = |path: &str| -> String {
        let cwd = getcwd_dir();
        lstrip(path, &cwd).to_string()
    };
    let filename = relative_path(&crate::pos::filename(pos));
    format!(
        "   {} {}",
        tty::apply_color(None, Style::Normal(RawColor::Cyan), "-->"),
        tty::apply_color(None, Style::Normal(RawColor::Green), &filename)
    )
}

/// Format this message as "  ^^^ You did something wrong here".
fn format_substring_underline(
    pos: &Absolute,
    msg: &str,
    severity_color: RawColor,
    first_context_line: Option<&String>,
    is_first: bool,
    col_width: isize,
) -> Result<String, InvalidArgument> {
    let (start_line, start_column) = crate::pos::line_column_absolute(pos);
    let (end_line, end_column) = crate::pos::end_line_column_absolute(pos);
    let underline_width = match first_context_line {
        None => 4, // Arbitrary choice when source isn't available.
        Some(first_context_line) => {
            if start_line == end_line {
                end_column - start_column
            } else {
                first_context_line.len() as isize - start_column
            }
        }
    };
    let underline = string_make(std::cmp::max(underline_width, 1), '^')?;
    let underline_padding = if first_context_line.is_some() {
        string_make(start_column, ' ')?
    } else {
        "".to_string()
    };
    let color = if is_first {
        Style::Bold(severity_color)
    } else {
        Style::Dim(RawColor::Default)
    };
    Ok(format!(
        "{} {}{}",
        line_margin(None, col_width)?,
        underline_padding,
        tty::apply_color(
            None,
            color,
            &(if is_first {
                underline
            } else {
                underline + " " + msg
            })
        )
    ))
}

/// Format the line of code associated with this message, and the message itself.
fn format_message(
    msg: &str,
    pos: &Absolute,
    severity_color: RawColor,
    is_first: bool,
    col_width: Option<isize>,
) -> Result<(String, String), InvalidArgument> {
    let col_width = col_width.unwrap_or_else(|| column_width(crate::pos::line(pos)));
    let context_lines = load_context_lines(pos);
    let pretty_ctx = format_context_lines(pos, &context_lines, col_width)?;
    let pretty_msg = format_substring_underline(
        pos,
        msg,
        severity_color,
        context_lines.first(),
        is_first,
        col_width,
    )?;
    Ok((pretty_ctx, pretty_msg))
}

/// Work out the column width needed for each file. Files with many
/// lines need a wider column due to the higher line numbers.
fn col_widths(msgs: &[Message<Absolute>]) -> BTreeMap<String, isize> {
    // Find the longest line number for every file in msgs.
    let mut longest_lines: BTreeMap<String, isize> = BTreeMap::new();
    for Message(pos, _) in msgs {
        let filename = crate::pos::filename(pos);
        let current_max = longest_lines.get(&filename).copied().unwrap_or(0);
        longest_lines.insert(filename, std::cmp::max(current_max, crate::pos::line(pos)));
    }
    longest_lines
        .into_iter()
        .map(|(filename, line)| (filename, column_width(line)))
        .collect()
}

/// Format the list of messages in a given error with context.
/// The list may not be ordered, and multiple messages may occur on one line.
fn format_error(error: &FinalizedDiagnostic) -> Result<String, InvalidArgument> {
    let UserDiagnostic { severity, .. } = error;
    // Sort messages such that messages in the same file are together.
    // Does not reorder the files or messages within a file.
    let msgs = diagnostics_state::combining_sort(user_diagnostic::get_messages(error), |msg| {
        crate::pos::filename(&msg.0)
    });
    // The first message is the 'primary' message, so add a boolean to distinguish it.
    let label_first =
        |msgs: &[Message<Absolute>], is_first: bool| -> Vec<(Message<Absolute>, bool)> {
            msgs.iter()
                .enumerate()
                .map(|(i, msg)| (msg.clone(), i == 0 && is_first))
                .collect()
        };
    let labelled_msgs = label_first(&msgs, true);
    // Sort messages by line number, so we can display with context.
    let cmp = |(m1, _): &(Message<Absolute>, bool), (m2, _): &(Message<Absolute>, bool)| {
        match crate::pos::filename(&m1.0).cmp(&crate::pos::filename(&m2.0)) {
            std::cmp::Ordering::Equal => crate::pos::line(&m1.0).cmp(&crate::pos::line(&m2.0)),
            _ => std::cmp::Ordering::Equal,
        }
    };
    let sorted_msgs = ocaml_list::stable_sort(labelled_msgs, cmp);
    // For every message, show it alongside the relevant line. If there
    // are multiple messages associated with the line, only show it once.
    let col_widths = col_widths(&msgs);
    // `aux msgs prev`
    let mut out: Vec<String> = vec![];
    let mut prev: Option<(String, isize)> = None;
    for (msg, is_first) in sorted_msgs {
        let Message(pos, msg_str) = &msg;
        let filename = crate::pos::filename(pos);
        let line = crate::pos::line(pos);
        let col_width = col_widths.get(&filename).copied();
        let (pretty_ctx, pretty_msg) = format_message(
            &msg_str.to_str_lossy(),
            pos,
            severity::tty_color(severity),
            is_first,
            col_width,
        )?;
        let formatted: Vec<String> = match &prev {
            Some((prev_filename, prev_line))
                if *prev_filename == filename && *prev_line == line =>
            {
                // Previous message was on this line too, just show the message itself
                vec![pretty_msg]
            }
            Some((prev_filename, _)) if *prev_filename == filename => {
                // Previous message was this file, but an earlier line.
                vec![pretty_ctx, pretty_msg]
            }
            _ => vec![format_filename(pos), pretty_ctx, pretty_msg],
        };
        out.extend(formatted);
        prev = Some((filename, line));
    }
    Ok(out.join("\n") + "\n")
}

/// Whether a panic is a `todo!` (its message starts with `not yet
/// implemented`): a part of the port that is missing, which `to_string` must
/// not take for an OCaml exception.
fn is_todo(payload: &(dyn std::any::Any + Send)) -> bool {
    let message = match payload.downcast_ref::<String>() {
        Some(s) => s.as_str(),
        None => payload.downcast_ref::<&str>().copied().unwrap_or(""),
    };
    message.starts_with("not yet implemented")
}

/// Print errors as something like (with fancy coloring based on severity):
///
/// ```text
///   warning: Warn[12001] This expression is likely always `false`
///   --> path/to/hack_file.php
///   15 | function h(?int $a, ?string $b): bool {
///   |             ^^^ This is an int
///   |                      ^^^^^^ This is a string
///   17 |   return $a === $b;
///   |          ^^^^^^^^^
/// ```
///
/// `claim_color` defaults to the color of the severity.
pub fn to_string(claim_color: Option<RawColor>, error: &FinalizedDiagnostic) -> String {
    let UserDiagnostic {
        severity,
        code,
        claim: Message(_, claim_msg),
        reasons: _,
        explanation: _,
        custom_msgs,
        quickfixes: _,
        is_fixmed: _,
        function_pos: _,
    } = error;
    let mut buf = String::with_capacity(50);
    let color = claim_color.unwrap_or_else(|| severity::tty_color(severity));
    buf.push_str(&format!(
        "{}: {} {}\n",
        tty::apply_color(None, Style::Bold(color), &severity::to_string(severity)),
        tty::apply_color(
            None,
            Style::Bold(color),
            &user_diagnostic::error_code_to_string(*code)
        ),
        tty::apply_color(
            None,
            Style::Bold(RawColor::Default),
            &claim_msg.to_str_lossy()
        )
    ));
    match std::panic::catch_unwind(AssertUnwindSafe(|| format_error(error))) {
        Ok(Ok(s)) => buf.push_str(&s),
        Err(payload) if is_todo(payload.as_ref()) => std::panic::resume_unwind(payload),
        Ok(Err(InvalidArgument(_))) | Err(_) => {
            buf.push_str("Error could not be pretty-printed. Please file a bug.")
        }
    }
    buf.push('\n');
    if !custom_msgs.is_empty() {
        buf.push_str(
            &(error
                .custom_msgs
                .iter()
                .map(|msg| markdown_lite::render(Some(true), Some(RawColor::Default), msg))
                .collect::<Vec<_>>()
                .join("\n")
                + "\n"),
        );
    }
    buf
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rt::diagnostic_fixtures as fx;

    const SUITE: &str = "error_formatting";

    fn check(test: &str, exp: &str, errors: impl FnOnce() -> Vec<FinalizedDiagnostic>) {
        let out = fx::run_in_suite(module_path!(), test, SUITE, false, || {
            fx::single_type_check_output(
                diagnostics_state::Format::Context,
                |e| to_string(None, e),
                &errors(),
            )
        });
        if let Some(out) = out {
            fx::assert_same_text(&out, &fx::expected(SUITE, exp));
        }
    }

    #[test]
    fn always_true() {
        check("always_true", "always_true.php.exp", || {
            vec![fx::warning(
                12007,
                fx::msg(
                    fx::pos("always_true.php", (4, 6), (4, 19)),
                    "Invalid comparison: This expression will always return `true`.\nA value of type `null` can never be equal to a value of type `vec<int>`",
                ),
                vec![],
            )]
        })
    }

    #[test]
    fn big_file() {
        check("big_file", "big_file.php.exp", || {
            let p = |start, end| fx::pos("big_file.php", start, end);
            vec![
                fx::err(
                    4030,
                    fx::msg(p((1008, 9), (1008, 12)), "Was expecting a return type hint"),
                    vec![],
                ),
                fx::err(
                    4105,
                    fx::msg(
                        p((1009, 2), (1009, 8)),
                        "Too many positional arguments (expected 0 but got 1)",
                    ),
                    vec![fx::msg(p((3, 9), (3, 12)), "Definition is here")],
                ),
            ]
        })
    }

    #[test]
    fn messages_same_line() {
        check("messages_same_line", "messages_same_line.php.exp", || {
            let p = |start, end| fx::pos("messages_same_line.php", start, end);
            vec![
                fx::err(
                    4030,
                    fx::msg(p((3, 33), (3, 36)), "Was expecting a return type hint"),
                    vec![],
                ),
                fx::err(
                    4105,
                    fx::msg(
                        p((3, 41), (3, 47)),
                        "Too many positional arguments (expected 0 but got 1)",
                    ),
                    vec![fx::msg(p((3, 9), (3, 12)), "Definition is here")],
                ),
            ]
        })
    }

    #[test]
    fn zero_width_syntax_err() {
        check(
            "zero_width_syntax_err",
            "zero_width_syntax_err.php.exp",
            || {
                let p = || fx::pos("zero_width_syntax_err.php", (3, 18), (3, 18));
                vec![
                    fx::err(
                        1002,
                        fx::msg(p(), "A type specifier is expected here."),
                        vec![],
                    ),
                    fx::err(
                        1002,
                        fx::msg(
                            p(),
                            "Encountered unexpected text ``, was expecting a type hint.",
                        ),
                        vec![],
                    ),
                ]
            },
        )
    }

    /// With `FORCE_ERROR_COLOR`, as `Lints_core.to_contextual_string` calls
    /// it (with a `claim_color`), and with custom messages.
    #[test]
    fn colors_claim_color_and_custom_messages() {
        let out = fx::run_in_suite(
            module_path!(),
            "colors_claim_color_and_custom_messages",
            SUITE,
            true,
            || {
                let mut e = fx::warning(
                    5001,
                    fx::msg(fx::pos("always_true.php", (4, 6), (4, 10)), "lint"),
                    vec![fx::msg(fx::pos("always_true.php", (3, 9), (3, 12)), "here")],
                );
                e.custom_msgs = vec!["**custom**".to_string()];
                to_string(Some(RawColor::Default), &e)
            },
        );
        if let Some(out) = out {
            fx::assert_same_text(
                &out,
                "\x1b[0;1mwarning\x1b[0m: \x1b[0;1mLint[5001]\x1b[0m \x1b[0;1mlint\x1b[0m\n\
                 \x20  \x1b[36m-->\x1b[0m \x1b[32malways_true.php\x1b[0m\n\
                 \x1b[36m  3 |\x1b[0m function foo(varray<int> $arg): void {\n\
                 \x1b[36m    |\x1b[0m          \x1b[0;2m^^^ here\x1b[0m\n\
                 \x1b[36m  4 |\x1b[0m   if (null !== $arg) {\n\
                 \x1b[36m    |\x1b[0m       \x1b[33;1m^^^^\x1b[0m\n\
                 \n\
                 \x1b[0;1;3mcustom\x1b[0m\n",
            );
        }
    }

    /// Messages in two files: `combining_sort` puts the claim's file first,
    /// `List.stable_sort` with a comparison that says 0 between files orders
    /// the lines within a file (the reason on line 3 before the claim on
    /// line 4), and each new file gets its `-->` line. Only the claim's
    /// underline is bold and without its message.
    #[test]
    fn two_files() {
        let out = fx::run_in_suite(module_path!(), "two_files", SUITE, false, || {
            to_string(
                None,
                &fx::err(
                    4110,
                    fx::msg(fx::pos("always_true.php", (4, 6), (4, 10)), "claim"),
                    vec![
                        fx::msg(
                            fx::pos("messages_same_line.php", (3, 9), (3, 12)),
                            "elsewhere",
                        ),
                        fx::msg(fx::pos("always_true.php", (3, 9), (3, 12)), "here"),
                    ],
                ),
            )
        });
        if let Some(out) = out {
            fx::assert_same_text(
                &out,
                "error: Typing[4110] claim\n\
                 \x20  --> always_true.php\n\
                 \x20 3 | function foo(varray<int> $arg): void {\n\
                 \x20   |          ^^^ here\n\
                 \x20 4 |   if (null !== $arg) {\n\
                 \x20   |       ^^^^\n\
                 \x20  --> messages_same_line.php\n\
                 \x20 3 | function foo(): void {} function bar() { foo(1); }\n\
                 \x20   |          ^^^ elsewhere\n\
                 \n",
            );
        }
    }

    /// A position over two lines: only its first line is shown, underlined
    /// from the start column to the end of that line.
    #[test]
    fn multi_line_position() {
        let out = fx::run_in_suite(module_path!(), "multi_line_position", SUITE, false, || {
            to_string(
                None,
                &fx::err(
                    4110,
                    fx::msg(fx::pos("always_true.php", (3, 9), (4, 4)), "multi"),
                    vec![],
                ),
            )
        });
        if let Some(out) = out {
            // `function foo(varray<int> $arg): void {` has 38 bytes.
            fx::assert_same_text(
                &out,
                &format!(
                    "error: Typing[4110] multi\n   --> always_true.php\n  3 | function foo(varray<int> $arg): void {{\n    | {}{}\n\n",
                    " ".repeat(9),
                    "^".repeat(38 - 9)
                ),
            );
        }
    }

    /// `try ... with _` stands for OCaml exceptions; a `todo!` (a part of the
    /// port that is missing) is not one.
    #[test]
    fn todo_is_not_an_exception() {
        let todo = std::panic::catch_unwind(|| todo!("Module.function")).unwrap_err();
        assert!(is_todo(todo.as_ref()));
        let failure = std::panic::catch_unwind(|| panic!("Failure: x")).unwrap_err();
        assert!(!is_todo(failure.as_ref()));
        let static_str =
            std::panic::catch_unwind(|| std::panic::panic_any("not yet implemented")).unwrap_err();
        assert!(is_todo(static_str.as_ref()));
    }

    /// A position in a file that has no such line: `No source found`, and an
    /// underline of 4 without padding.
    #[test]
    fn no_source() {
        let out = fx::run_in_suite(module_path!(), "no_source", SUITE, false, || {
            to_string(
                None,
                &fx::err(
                    4110,
                    fx::msg(fx::pos("always_true.php", (7, 0), (7, 0)), "past the end"),
                    vec![],
                ),
            )
        });
        if let Some(out) = out {
            fx::assert_same_text(
                &out,
                "error: Typing[4110] past the end\n   --> always_true.php\n  7 | No source found\n    | ^^^^\n\n",
            );
        }
    }
}
