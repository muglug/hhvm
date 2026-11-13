// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `plain_highlighted_diagnostic_formatter.ml`. See `hh/PORTING.md`.
//!
//! A plain-text error format inspired by rustc/clang/gcc.
//!
//! It is the "highlighted" (default) format with the color removed: rather than
//! coloring the characters that belong to each numbered reference, it prints the
//! source line and then a row of '^' underlines beneath the span on the next
//! line, labelled with the matching marker.
//!
//! Like the highlighted format it shows a few lines of surrounding context and
//! coalesces nearby references into a single snippet. A reference whose span
//! covers several lines is underlined on every line it covers (matching what the
//! colored format highlights). Leading and trailing whitespace within a span is
//! excluded so the carets line up under code rather than indentation.
//!
//! No ANSI color is emitted, so the output is deterministic and suitable for use
//! in .exp snapshots.
//!
//! `Diagnostics.finalized_diagnostic` is `user_diagnostic::T<Absolute,
//! Absolute>`. Message texts are byte strings; bytes that are not UTF-8
//! become U+FFFD, as in `user_diagnostic::to_string`.

#![allow(non_upper_case_globals)]

use bstr::ByteSlice;
use oxidized::message::Message;

use crate::diagnostics_state;
use crate::pos::Absolute;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_list;
use crate::string_utils::lstrip;
use crate::user_diagnostic;
use crate::user_diagnostic::Severity;
use crate::user_diagnostic::UserDiagnostic;
use crate::user_diagnostic::severity;

/// `Diagnostics.finalized_diagnostic`
type FinalizedDiagnostic = user_diagnostic::T<Absolute, Absolute>;

#[derive(Clone, Debug)]
struct MarkedMessage {
    marker: isize,
    message: Message<Absolute>,
}

/// A set of references that are close enough together to share one code snippet,
/// together with the merged position spanning all of them.
#[derive(Clone, Debug)]
struct PositionGroup {
    aggregate_position: Absolute,
    messages: Vec<MarkedMessage>,
}

/// Number of context lines shown before and after each snippet.
const n_extra_lines: isize = 2;

/// Stand-in for a line a position runs onto just past the end of the file.
const out_of_bounds_char: &str = "_";

/// `String.make n c`, which raises `Invalid_argument` when `n < 0`.
fn string_make(n: isize, c: char) -> String {
    if n < 0 {
        panic!("Invalid_argument: String.make")
    }
    std::iter::repeat_n(c, n as usize).collect()
}

/// `Base.Char.is_whitespace`: space, `\t`, `\n`, `\r`, vertical tab and
/// form feed.
fn char_is_whitespace(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | b'\r' | b'\x0b' | b'\x0c')
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

/// `Printf.sprintf "%*s" width s`
fn sprintf_star_s(width: isize, s: &str) -> String {
    let w = width.unsigned_abs();
    if width < 0 {
        format!("{:<w$}", s)
    } else {
        format!("{:>w$}", s)
    }
}

/// Assign a marker to each message in the original error order (the claim first,
/// then each reason). Messages with identical positions reuse the same marker,
/// so the numbering matches the colored "highlighted" format.
fn mark_messages(msgl: Vec<Message<Absolute>>) -> Vec<MarkedMessage> {
    let mut next_marker: isize = 1;
    // The OCaml list `seen`, its head last.
    let mut seen: Vec<(isize, Absolute)> = vec![];
    msgl.into_iter()
        .map(|message| {
            let pos = message.0.clone();
            match seen
                .iter()
                .rev()
                .find(|(_, seen_pos)| crate::pos::equal_absolute(&pos, seen_pos))
            {
                Some((marker, _)) => MarkedMessage {
                    marker: *marker,
                    message,
                },
                None => {
                    let marker = next_marker;
                    next_marker += 1;
                    seen.push((marker, pos));
                    MarkedMessage { marker, message }
                }
            }
        })
        .collect()
}

fn relative_path(path: &str) -> String {
    let cwd = {
        let cwd = std::env::current_dir().unwrap_or_else(|e| panic!("Sys_error: {}", e));
        ocaml_filename::concat(&cwd.to_string_lossy(), "")
    };
    lstrip(path, &cwd).to_string()
}

/// The lines of source covering [start_line - before, end_line + after] for a
/// position, as (line_number, line_text option) pairs. Mirrors the window used
/// by the highlighted formatter, including its past-end-of-file sentinel.
fn load_context_lines(
    source: Option<&(String, String)>,
    before: isize,
    after: isize,
    pos: &Absolute,
) -> Vec<(isize, Option<String>)> {
    let path = crate::pos::filename(pos);
    let (start_line, _) = crate::pos::line_column_absolute(pos);
    let (end_line, end_col) = crate::pos::end_line_column_absolute(pos);
    // Internal errors can report the whole file; cap the window.
    let end_line = std::cmp::min(start_line + 1000, end_line);
    // The lines, and whether all of them are valid UTF-8.
    let (lines, valid) = match source {
        Some((source_path, content)) if path == *source_path => (
            // `String.split_lines`
            content.lines().map(|line| line.to_string()).collect(),
            true,
        ),
        Some(_) | None => diagnostics_state::read_lines_with_validity(&path),
    };
    match lines {
        lines if lines.is_empty() => (start_line..=end_line)
            .map(|line_num| (line_num, None))
            .collect(),
        _ if !valid => vec![],
        lines => {
            let numbered = lines
                .into_iter()
                .enumerate()
                .map(|(i, l)| (i as isize + 1, Some(l)));
            let mut window: Vec<(isize, Option<String>)> = numbered
                .filter(|(i, _)| *i >= start_line - before && *i <= end_line + after)
                .collect();
            let last_line = match window.last() {
                Some((n, _)) => *n,
                None => 0,
            };
            if end_line > last_line && end_col > 0 {
                window.push((end_line, Some(out_of_bounds_char.to_string())));
                window
            } else {
                window
            }
        }
    }
}

/// The columns [start, stop) of [pos] that fall on [line_num] (0-based, [stop]
/// exclusive), or None if the position covers no characters on that line.
fn span_on_line(pos: &Absolute, line_num: isize, line_len: isize) -> Option<(isize, isize)> {
    let (start_line, start_col) = crate::pos::line_column_absolute(pos);
    let (end_line, end_col) = crate::pos::end_line_column_absolute(pos);
    if line_num < start_line || line_num > end_line {
        None
    } else {
        let start = if line_num == start_line { start_col } else { 0 };
        let stop = if line_num == end_line {
            end_col
        } else {
            line_len
        };
        // On the final line of a multi-line span the end column is exclusive, so a
        // value of 0 means nothing on this line is actually covered.
        if line_num == end_line && start_line != end_line && end_col == 0 {
            None
        } else {
            Some((start, stop))
        }
    }
}

/// Right-aligned line-number gutter, e.g. " 12 |". When [line_num] is None the
/// number is blank, used for the underline row so it aligns with the source.
fn gutter(col_width: isize, line_num: Option<isize>) -> String {
    match line_num {
        // `Printf.sprintf "%*d |" col_width n`
        Some(n) => sprintf_star_d(col_width, n) + " |",
        // `Printf.sprintf "%*s |" col_width ""`
        None => sprintf_star_s(col_width, "") + " |",
    }
}

/// "  | <padding>^^^ [n]" for one marker's span on one line, excluding leading
/// and trailing whitespace within the span. Returns None when the covered range
/// is only whitespace (e.g. a blank line inside a multi-line span).
fn underline_row(
    col_width: isize,
    line: &str,
    marker: isize,
    (start, stop): (isize, isize),
) -> Option<String> {
    let line = line.as_bytes();
    let n = line.len() as isize;
    // `line.[!s]` raises `Invalid_argument "index out of bounds"` on a
    // negative index.
    let char_at = |i: isize| -> u8 {
        if i < 0 {
            panic!("Invalid_argument: index out of bounds")
        }
        line[i as usize]
    };
    let mut s = start;
    while s < stop && s < n && char_is_whitespace(char_at(s)) {
        s += 1;
    }
    let mut e = std::cmp::min(stop, n);
    while e > s && char_is_whitespace(char_at(e - 1)) {
        e -= 1;
    }
    let (caret_start, width) = if e > s {
        (s, e - s)
    } else if start == stop && n > 0 {
        // A genuine zero-width position: show a single caret at the point.
        (std::cmp::min(start, n), 1)
    } else {
        // Whitespace-only (or empty-line) coverage: nothing to underline.
        (0, 0)
    };
    if width <= 0 {
        None
    } else {
        Some(format!(
            "{} {}{} [{}]",
            gutter(col_width, None),
            string_make(std::cmp::max(caret_start, 0), ' '),
            string_make(width, '^'),
            marker
        ))
    }
}

/// All underline rows for [line_num]: one per marker whose span touches the
/// line, deduped (a marker maps to a single span) and ordered left-to-right.
fn underline_rows(
    col_width: isize,
    group: &PositionGroup,
    line_num: isize,
    line_text: Option<&str>,
) -> Vec<String> {
    match line_text {
        None => vec![],
        Some(line) => {
            let line_len = line.len() as isize;
            let spans: Vec<(isize, (isize, isize))> = group
                .messages
                .iter()
                .filter_map(|mm| {
                    span_on_line(&mm.message.0, line_num, line_len).map(|span| (mm.marker, span))
                })
                .collect();
            ocaml_list::dedup_and_sort(spans, |(m1, (s1, _)), (m2, (s2, _))| match s1.cmp(s2) {
                std::cmp::Ordering::Equal => m1.cmp(m2),
                c => c,
            })
            .into_iter()
            .filter_map(|(marker, span)| underline_row(col_width, line, marker, span))
            .collect()
        }
    }
}

/// Render one snippet: each source line, followed by any underline rows.
fn render_group(
    col_width: isize,
    lines: &[(isize, Option<String>)],
    group: &PositionGroup,
) -> String {
    lines
        .iter()
        .flat_map(|(line_num, line_text)| {
            let source = match line_text {
                Some(s) => s.as_str(),
                None => "No source found",
            };
            let source_row = format!("{} {}", gutter(col_width, Some(*line_num)), source);
            let mut rows = vec![source_row];
            rows.extend(underline_rows(
                col_width,
                group,
                *line_num,
                line_text.as_deref(),
            ));
            rows
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Group the references by file (preserving order) and, within a file, into
/// snippets of references that are close enough to share context.
fn position_groups_by_file(marked: Vec<MarkedMessage>) -> Vec<Vec<PositionGroup>> {
    let msg_pos = |mm: &MarkedMessage| -> Absolute { mm.message.0.clone() };
    let by_file: Vec<Vec<MarkedMessage>> = ocaml_list::group(marked, |a, b| {
        crate::pos::filename(&msg_pos(a)) != crate::pos::filename(&msg_pos(b))
    })
    .into_iter()
    .map(|msgs| {
        ocaml_list::stable_sort(msgs, |a, b| {
            crate::pos::line(&msg_pos(a)).cmp(&crate::pos::line(&msg_pos(b)))
        })
    })
    .collect();
    let close_enough = |prev_pos: &Absolute, curr_pos: &Absolute| -> bool {
        crate::pos::end_line(prev_pos) + n_extra_lines + 2
            >= crate::pos::line(curr_pos) - n_extra_lines
    };
    by_file
        .into_iter()
        .map(|msgs| {
            ocaml_list::group(msgs, |prev, curr| {
                !close_enough(&msg_pos(prev), &msg_pos(curr))
            })
            .into_iter()
            .map(|messages| PositionGroup {
                aggregate_position: messages
                    .iter()
                    .map(msg_pos)
                    .reduce(|x1, x2| crate::pos::merge_absolute(&x1, &x2))
                    .unwrap_or_else(|| panic!("List.reduce_exn")),
                messages,
            })
            .collect()
        })
        .collect()
}

/// "path:line:col" header for a file, anchored at its lowest-numbered marker.
fn file_header(groups: &[&PositionGroup]) -> String {
    let primary_pos = {
        let mms: Vec<&MarkedMessage> = groups.iter().flat_map(|g| g.messages.iter()).collect();
        let mm = ocaml_list::stable_sort(mms, |a, b| a.marker.cmp(&b.marker))
            .into_iter()
            .next()
            .unwrap_or_else(|| panic!("List.hd_exn"));
        mm.message.0.clone()
    };
    let (line, col) = crate::pos::line_column_absolute(&primary_pos);
    format!(
        "{}:{}:{}",
        relative_path(&crate::pos::filename_for_display(&primary_pos)),
        line,
        col + 1
    )
}

/// The numbered claim + reasons header, in the original error order.
fn format_header(severity: &Severity, code: isize, ordered: &[MarkedMessage]) -> String {
    match ordered {
        [] => "".to_string(),
        [claim_mm, reason_mms @ ..] => {
            let claim_row = format!(
                "{}: {} {} [{}]",
                severity::to_string(severity),
                user_diagnostic::error_code_to_string(code),
                claim_mm.message.1.to_str_lossy(),
                claim_mm.marker
            );
            let reason_rows = reason_mms
                .iter()
                .map(|mm| format!("-> {} [{}]", mm.message.1.to_str_lossy(), mm.marker));
            std::iter::once(claim_row)
                .chain(reason_rows)
                .collect::<Vec<_>>()
                .join("\n")
        }
    }
}

fn format(source: Option<&(String, String)>, error: &FinalizedDiagnostic) -> String {
    let UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        custom_msgs,
        explanation: _,
        quickfixes: _,
        is_fixmed: _,
        function_pos: _,
    } = error;
    // Markers are numbered in the original error order ...
    let ordered = {
        let mut msgl = vec![claim.clone()];
        msgl.extend(reasons.iter().cloned());
        mark_messages(msgl)
    };
    // ... but snippets are grouped by file for display.
    let by_file: Vec<Vec<(PositionGroup, Vec<(isize, Option<String>)>)>> =
        position_groups_by_file(diagnostics_state::combining_sort(ordered.clone(), |mm| {
            crate::pos::filename(&mm.message.0)
        }))
        .into_iter()
        .map(|groups| {
            groups
                .into_iter()
                .map(|g| {
                    let lines = load_context_lines(
                        source,
                        n_extra_lines,
                        n_extra_lines,
                        &g.aggregate_position,
                    );
                    (g, lines)
                })
                .collect()
        })
        .collect();
    let col_width = diagnostics_state::num_digits(
        by_file
            .iter()
            .flat_map(|groups| {
                groups
                    .iter()
                    .flat_map(|(_, lines)| lines.iter().map(|(n, _)| *n))
            })
            .max()
            .unwrap_or(1),
    );
    // Snippets within a file are separated by a lone ":" gutter line.
    let snippet_sep = "\n".to_string() + &string_make(col_width, ' ') + " :\n";
    let file_blocks: Vec<String> = by_file
        .iter()
        .map(|groups| {
            let header = file_header(&groups.iter().map(|(g, _)| g).collect::<Vec<_>>());
            let snippets: Vec<String> = groups
                .iter()
                .map(|(g, lines)| render_group(col_width, lines, g))
                .collect();
            header + "\n" + &snippets.join(&snippet_sep)
        })
        .collect();
    let mut buf = String::with_capacity(256);
    buf.push_str(&format_header(severity, *code, &ordered));
    buf.push_str("\n\n");
    buf.push_str(&file_blocks.join("\n\n"));
    buf.push_str("\n\n");
    if !custom_msgs.is_empty() {
        buf.push_str(&(custom_msgs.join("\n") + "\n"));
    }
    buf
}

pub fn to_string(error: &FinalizedDiagnostic) -> String {
    format(None, error)
}

pub fn to_string_with_source(source: Option<String>, error: &FinalizedDiagnostic) -> String {
    let path = crate::pos::filename(&error.claim.0);
    format(source.map(|source| (path, source)).as_ref(), error)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rt::diagnostic_fixtures as fx;

    const SUITE: &str = "typecheck/plain_highlighted_error_format";

    fn check(test: &str, exp: &str, errors: impl FnOnce() -> Vec<FinalizedDiagnostic>) {
        let out = fx::run_in_suite(module_path!(), test, SUITE, false, || {
            fx::single_type_check_output(
                diagnostics_state::Format::PlainHighlighted,
                to_string,
                &errors(),
            )
        });
        if let Some(out) = out {
            fx::assert_same_text(&out, &fx::expected(SUITE, exp));
        }
    }

    #[test]
    fn new_static2() {
        check("new_static2", "new_static2.php.exp", || {
            let p = |start, end| fx::pos("new_static2.php", start, end);
            let class_a = || p((13, 15), (13, 16));
            let t = || p((13, 17), (13, 18));
            let a_int = || p((22, 32), (22, 38));
            let int = || p((22, 34), (22, 37));
            let new_static = || p((23, 11), (23, 23));
            let invariant = "This type argument to `A` must match exactly (it is invariant)";
            vec![
                fx::err(
                    4053,
                    fx::msg(p((19, 8), (19, 11)), "No instance method `xxx` in `A`"),
                    vec![
                        fx::msg(p((15, 18), (15, 21)), "Did you mean `foo` instead?"),
                        fx::msg(class_a(), "This is why I think it is an object of type A"),
                        fx::msg(class_a(), "Declaration of `A` is here"),
                    ],
                ),
                fx::err(
                    4110,
                    fx::msg(new_static(), "Invalid return type"),
                    vec![
                        fx::msg(t(), "Expected `T`"),
                        fx::msg(int(), "But got `int`"),
                        fx::msg(int(), invariant),
                    ],
                ),
                fx::err(
                    4110,
                    fx::msg(new_static(), "Invalid return type"),
                    vec![
                        fx::msg(a_int(), "Expected `A<int>`"),
                        fx::msg(p((23, 15), (23, 21)), "But got `this as A<T>`"),
                    ],
                ),
                fx::err(
                    4110,
                    fx::msg(new_static(), "Invalid return type"),
                    vec![
                        fx::msg(int(), "Expected `int`"),
                        fx::msg(t(), "But got `T`"),
                        fx::msg(t(), invariant),
                    ],
                ),
                fx::err(
                    4110,
                    fx::msg(new_static(), "Invalid return type"),
                    vec![
                        fx::msg(int(), "Expected `int`"),
                        fx::msg(t(), "But got `mixed`"),
                        fx::msg(t(), invariant),
                        fx::msg(
                            t(),
                            "  by the definition of `T` arising from an implicit `as mixed` constraint on this type",
                        ),
                    ],
                ),
            ]
        })
    }

    #[test]
    fn shape_field_value_mismatch_position() {
        check(
            "shape_field_value_mismatch_position",
            "shape_field_value_mismatch_position.php.exp",
            || {
                let p = |start, end| fx::pos("shape_field_value_mismatch_position.php", start, end);
                vec![fx::err(
                    4110,
                    fx::msg(p((18, 9), (22, 3)), "Invalid return type"),
                    vec![
                        fx::msg(p((12, 9), (12, 15)), "Expected `string`"),
                        fx::msg(p((20, 11), (20, 12)), "But got `int`"),
                    ],
                )]
            },
        )
    }

    /// A zero-width position gets one caret; a position that covers only
    /// whitespace gets none; a line past the end of the file is `_`; the
    /// part of a multi-line span that starts at the end of a line counts as
    /// zero-width (`start = stop`) and gets a caret; custom messages are
    /// printed as they are.
    #[test]
    fn zero_width_whitespace_and_custom_messages() {
        let out = fx::run_in_suite(
            module_path!(),
            "zero_width_whitespace_and_custom_messages",
            SUITE,
            false,
            || {
                let p = |start, end| fx::pos("new_static2.php", start, end);
                let mut e = fx::err(
                    4110,
                    fx::msg(p((18, 4), (18, 4)), "zero"),
                    vec![
                        fx::msg(p((18, 0), (18, 4)), "blank"),
                        fx::msg(p((25, 1), (26, 1)), "past the end"),
                    ],
                );
                e.custom_msgs = vec!["`custom` 1".to_string(), "custom 2".to_string()];
                to_string(&e)
            },
        );
        if let Some(out) = out {
            fx::assert_same_text(
                &out,
                "error: Typing[4110] zero [1]\n\
                 -> blank [2]\n\
                 -> past the end [3]\n\
                 \n\
                 new_static2.php:18:5\n\
                 16 | \n\
                 17 |   public static function bar(): void {\n\
                 18 |     $x = new static();\n\
                 \x20  |     ^ [1]\n\
                 19 |     $x->xxx();\n\
                 20 |   }\n\
                 \x20  :\n\
                 23 |     return new static(); // Error - A<T> isn't subtype of A<int>\n\
                 24 |   }\n\
                 25 | }\n\
                 \x20  |  ^ [3]\n\
                 26 | _\n\
                 \x20  | ^ [3]\n\
                 \n\
                 `custom` 1\n\
                 custom 2\n",
            );
        }
    }
}
