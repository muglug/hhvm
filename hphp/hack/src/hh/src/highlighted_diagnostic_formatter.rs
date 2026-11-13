// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `highlighted_diagnostic_formatter.ml`. See `hh/PORTING.md`.
//!
//! `Diagnostics.finalized_diagnostic` is `user_diagnostic::T<Absolute,
//! Absolute>`. Message texts are byte strings; bytes that are not UTF-8
//! become U+FFFD, as in `user_diagnostic::to_string`.
//!
//! One difference with the OCaml, which a Rust `String` imposes:
//! `line_highlighted` colors a source line character by character, and OCaml
//! characters are bytes, so OCaml wraps each byte of a multi-byte UTF-8
//! character in its own escape sequences (which is not valid UTF-8). Here
//! such a character is colored as a whole, with the markers at its first
//! byte. Without colors (`FORCE_ERROR_COLOR` unset and no terminal), and for
//! ASCII text, the output is the same.

#![allow(non_upper_case_globals)]

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
use crate::user_diagnostic::Severity;
use crate::user_diagnostic::UserDiagnostic;
use crate::user_diagnostic::severity;

/// `Diagnostics.finalized_diagnostic`
type FinalizedDiagnostic = user_diagnostic::T<Absolute, Absolute>;

type ErrorCode = isize;

type Marker = (isize, RawColor);

#[derive(Clone, Debug)]
struct MarkedMessage {
    original_index: isize,
    marker: Marker,
    message: Message<Absolute>,
}

/// A position_group is a record composed of a position (we'll call
/// the aggregate_position) and a list of marked_message. Each
/// marked_message contains a position, and all of these positions are
/// closed enough together to be printed in one coalesced code context.
///
/// For example, say we have the following code:
///
/// ```text
///    1 | <?hh
///    2 |
///    3 | function f(): dict<int,
///    4 |   int>
///    5 | {
///    6 |   return "hello";
///    7 | }
///    8 |
/// ```
///
/// We would be given three individual positions (one corresponding to line 2
/// and two corresponding to lines 6), i.e.
///
/// ```text
///    Typing[4110] Invalid return type [1]
///    -> Expected dict<int, int> [2]
///    -> But got string [1]
/// ```
///
/// They are close enough together so that code only needs to be printed once
/// for all of them since their context overlaps. Thus the position_group would
/// be composed of a list of the three individual aforementioned positions, as
/// well as the aggregate_position whose first line is 1 and last line 7, and
/// the final output would look like this.
///
/// ```text
///    1 | <?hh
///    2 |
/// [2] 3 | function f(): dict<int,
/// [2] 4 |   int>
///    5 | {
/// [1] 6 |   return "hello";
///    7 | }
/// ```
#[derive(Clone, Debug)]
struct PositionGroup {
    aggregate_position: Absolute,
    messages: Vec<MarkedMessage>,
}

const n_extra_lines_hl: isize = 2;

/// 'char' because this is intended to be a string of length 1
const out_of_bounds_char: &str = "_";

fn background_highlighted(s: &str) -> String {
    tty::apply_color(None, Style::Dim(RawColor::Default), s)
}

fn default_highlighted(s: &str) -> String {
    s.to_string()
}

fn line_num_highlighted(line_num: isize) -> String {
    background_highlighted(&line_num.to_string())
}

/// `String.make n c`, which raises `Invalid_argument` when `n < 0`.
fn string_make(n: isize, c: char) -> String {
    if n < 0 {
        panic!("Invalid_argument: String.make")
    }
    std::iter::repeat_n(c, n as usize).collect()
}

/// `Filename.concat (Sys.getcwd ()) ""`. (`Sys.getcwd` raises `Sys_error`
/// when it fails.)
fn getcwd_dir() -> String {
    let cwd = std::env::current_dir().unwrap_or_else(|e| panic!("Sys_error: {}", e));
    ocaml_filename::concat(&cwd.to_string_lossy(), "")
}

/// Checks if a line (or line/col pair) is inside a position,
/// taking care to handle zero-width positions and positions
/// spanning multiple lines.
///
/// Some examples:
///
/// ```text
///                0         1         2
///                01234567890123456789012
///   Example 1: 1 class Foo extends    {}
///
///   Example 2: 1 function }
///
///   Example 3: 1 function {
///              2   return 3;
///              3 }
/// ```
///
/// In example 1, the error position is [1,21] - [1,21) with length 1;
///  column 21 of line 1 is within that error position.
/// In example 2, error position is [1,0] - [1,0) with length 0;
///  column 0 of line 1 is within that error position.
/// In Example 2, the error position is [1,10] - [2,0) with length 1;
///  column 10 of line 1 (but nothing in line 2) is within that error position.
fn pos_contains(pos: &Absolute, col_num: Option<isize>, line_num: isize) -> bool {
    let (first_line, first_col) = crate::pos::line_column_absolute(pos);
    let (last_line, last_col) = crate::pos::end_line_column_absolute(pos);
    let is_col_okay = |f: &dyn Fn(isize) -> bool| match col_num {
        None => true,
        Some(cn) => f(cn),
    };
    let last_col = match crate::pos::length(pos) {
        0 => last_col + 1,
        _ => last_col,
    };
    // A position's first line, first column, and last line
    // are all checked inclusively. The position's last column
    // is checked inclusively if the length of the position is zero,
    // and exclusively otherwise, in order to correctly highlight
    // zero-width positions. Line_num is 1-indexed, col_num is 0-indexed.
    if first_line == last_line {
        first_line == line_num && is_col_okay(&|cn| first_col <= cn && cn < last_col)
    } else if line_num == first_line {
        is_col_okay(&|cn| first_col <= cn)
    } else if line_num == last_line {
        // When only checking for a line's inclusion in a position
        // (i.e. when col_num = None), special care must be taken when
        // the line we're checking is the last line of the position:
        // since the end_column is exclusive, the end_column's value
        // must be non-zero signifying there is at least one character
        // on it to be highlighted.
        last_col > 0 && is_col_okay(&|cn| cn < last_col)
    } else {
        first_line < line_num && line_num < last_line
    }
}

/// Gets the list of unique marker/position tuples associated with a line.
fn markers_and_positions_for_line(
    position_group: &PositionGroup,
    line_num: isize,
) -> Vec<(Marker, Absolute)> {
    let mms: Vec<&MarkedMessage> = position_group
        .messages
        .iter()
        .filter(|mm| pos_contains(&mm.message.0, None, line_num))
        .collect();
    ocaml_list::dedup_and_sort(mms, |mm1, mm2| {
        let (mk1, _) = mm1.marker;
        let (mk2, _) = mm2.marker;
        mk1.cmp(&mk2)
    })
    .into_iter()
    .map(|mm| (mm.marker, mm.message.0.clone()))
    .collect()
}

/// Gets the string containing the markers that should be displayed next to this line,
/// e.g. something like "[1,4,5]"
///
/// `apply_color` defaults to `true`.
fn markers_string(
    position_group: &PositionGroup,
    apply_color: Option<bool>,
    line_num: isize,
) -> String {
    let apply_color = apply_color.unwrap_or(true);
    let add_color = |f: &dyn Fn(&str) -> String, s: &str| -> String {
        if apply_color { f(s) } else { s.to_string() }
    };
    let markers: Vec<Marker> = markers_and_positions_for_line(position_group, line_num)
        .into_iter()
        .map(|(marker, _)| marker)
        .collect();
    match markers.as_slice() {
        [] => "".to_string(),
        markers => {
            let ms: Vec<String> = markers
                .iter()
                .map(|(marker, color)| {
                    let marker_str = marker.to_string();
                    add_color(
                        &|s| tty::apply_color(None, Style::Normal(*color), s),
                        &marker_str,
                    )
                })
                .collect();
            let lbracket = add_color(&background_highlighted, "[");
            let rbracket = add_color(&background_highlighted, "]");
            let comma = add_color(&background_highlighted, ",");
            format!("{}{}{}", lbracket, ms.join(&comma), rbracket)
        }
    }
}

fn line_margin_highlighted(
    position_group: &PositionGroup,
    line_num: isize,
    col_width_raw: isize,
) -> String {
    // Separate the margin into several sections:
    // |markers|space(s)|line_num|space|vertical_bar|
    // i.e.
    // [1,2]  9 |
    // [3]   10 |
    // We need to do this because each has its own color and length
    let nspaces = {
        let markers_raw_len = markers_string(position_group, Some(false), line_num).len() as isize;
        let line_num_raw_len = line_num.to_string().len() as isize;
        std::cmp::max(col_width_raw - (markers_raw_len + line_num_raw_len), 1)
    };
    let markers_pretty = markers_string(position_group, None, line_num);
    let spaces = string_make(nspaces, ' ');
    let line_num_pretty = line_num_highlighted(line_num);
    format!(
        "{}{}{}{}",
        markers_pretty,
        spaces,
        line_num_pretty,
        background_highlighted(" |")
    )
}

/// line_num is 1-based
fn line_highlighted(position_group: &PositionGroup, line_num: isize, line: Option<&str>) -> String {
    match line {
        None => tty::apply_color(None, Style::Dim(RawColor::Default), "No source found"),
        Some(line) => match markers_and_positions_for_line(position_group, line_num).as_slice() {
            [] => default_highlighted(line),
            ms => {
                let get_markers_at_col = |col_num: isize| -> Vec<(Marker, Absolute)> {
                    ms.iter()
                        .filter(|(_, pos)| pos_contains(pos, Some(col_num), line_num))
                        .cloned()
                        .collect()
                };
                let color_column = |ms: Vec<(Marker, Absolute)>, c: &str| -> String {
                    // Prefer shorter smaller positions so the boundaries between overlapping
                    // positions are visible. Take the lowest-number (presumably more important)
                    // to break ties.
                    let ((_, color), _) =
                        ocaml_list::stable_sort(ms, |((m1, _), p1), ((m2, _), p2)| {
                            match crate::pos::length(p1).cmp(&crate::pos::length(p2)) {
                                std::cmp::Ordering::Equal => m1.cmp(m2),
                                v => v,
                            }
                        })
                        .into_iter()
                        .next()
                        .unwrap_or_else(|| panic!("List.hd_exn"));
                    tty::apply_color(None, Style::Normal(color), c)
                };
                // Not String.mapi because we don't want to return a char from each element
                // (By character rather than by byte: see the module documentation.)
                let highlighted_columns: Vec<String> = line
                    .char_indices()
                    .map(|(i, c)| {
                        let c = c.to_string();
                        match get_markers_at_col(i as isize).as_slice() {
                            [] => default_highlighted(&c),
                            ms => color_column(ms.to_vec(), &c),
                        }
                    })
                    .collect();
                // Add extra column when position spans multiple lines and we're on the last line. Handles
                // the case where a position exists for after file but there is no character to highlight
                let extra_column = {
                    let (end_line, end_col) =
                        crate::pos::end_line_column_absolute(&position_group.aggregate_position);
                    if line_num == end_line || (line_num + 1 == end_line && end_col == 0) {
                        match get_markers_at_col(line.len() as isize).as_slice() {
                            [] => "".to_string(),
                            ms => color_column(ms.to_vec(), out_of_bounds_char),
                        }
                    } else {
                        "".to_string()
                    }
                };
                highlighted_columns.concat() + &extra_column
            }
        },
    }
}

/// Prefixes each line with its corresponding formatted margin
fn format_context_lines_highlighted(
    position_group: &PositionGroup,
    lines: &[(isize, Option<String>)],
    col_width: isize,
) -> String {
    let format_line = |(line_num, line): &(isize, Option<String>)| {
        format!(
            "{} {}",
            line_margin_highlighted(position_group, *line_num, col_width),
            line_highlighted(position_group, *line_num, line.as_deref())
        )
    };
    let formatted_lines: Vec<String> = lines.iter().map(format_line).collect();
    formatted_lines.join("\n")
}

/// Gets lines from a position, including additional before/after
/// lines from the current position; line numbers are 1-indexed.
/// If the position references one extra line than actually
/// in the file, we append a line with a sentinel character ('_')
/// so that we have a line to highlight later.
fn load_context_lines_for_highlighted(
    before: isize,
    after: isize,
    pos: &Absolute,
) -> Vec<(isize, Option<String>)> {
    let path = crate::pos::filename(pos);
    let (start_line, _start_col) = crate::pos::line_column_absolute(pos);
    let (end_line, end_col) = crate::pos::end_line_column_absolute(pos);

    // Type checker internal errors report the whole file. Limit our
    // output to at most 1,000 lines.
    let end_line = std::cmp::min(start_line + 1000, end_line);

    let lines = diagnostics_state::read_lines_for_highlighted(&path);
    match lines {
        None => vec![],
        Some(lines) if lines.is_empty() => (start_line..=end_line)
            .map(|line_num| (line_num, None))
            .collect(),
        Some(lines) => {
            let numbered_lines = lines
                .into_iter()
                .enumerate()
                .map(|(i, l)| (i as isize + 1, Some(l)));
            let original_lines: Vec<(isize, Option<String>)> = numbered_lines
                .filter(|(i, _)| *i >= start_line - before && *i <= end_line + after)
                .collect();
            let additional_line = {
                let last_line = match original_lines.last() {
                    Some((last_line, _)) => *last_line,
                    None => 0,
                };
                if end_line > last_line && end_col > 0 {
                    Some((end_line, out_of_bounds_char))
                } else {
                    None
                }
            };
            match additional_line {
                None => original_lines,
                Some((line_num, additional)) => {
                    let mut original_lines = original_lines;
                    original_lines.push((line_num, Some(additional.to_string())));
                    original_lines
                }
            }
        }
    }
}

fn format_context_highlighted(col_width: isize, position_group: &PositionGroup) -> String {
    let lines = load_context_lines_for_highlighted(
        n_extra_lines_hl,
        n_extra_lines_hl,
        &position_group.aggregate_position,
    );
    format_context_lines_highlighted(position_group, &lines, col_width)
}

/// The column width will be the length of the largest prefix before
/// the " |", which is composed of the list of markers, a space, and
/// the line number. The column size will be the same for all messages
/// in this error, regardless of file, so that they are all aligned.
/// Returns the length of the raw (uncolored) prefix string.
///
/// For example:
///
/// ```text
///  overlap_pos.php:11:10
///         8 |
///         9 |
///  [2]   10 | function returns_int(): int {
///  [1,3] 11 |   return 'foo';
///        12 | }
///        13 |
/// ```
///
/// The length of the column is the length of "[1,3] 11" = 8
fn col_width_for_highlighted(position_groups: &[PositionGroup]) -> isize {
    let largest_line_length = {
        let message_positions = |messages: &[MarkedMessage]| -> Vec<Absolute> {
            messages.iter().map(|mm| mm.message.0.clone()).collect()
        };
        let line_nums: Vec<isize> = position_groups
            .iter()
            .flat_map(|pg| message_positions(&pg.messages))
            .map(|pos| crate::pos::end_line(&pos))
            .collect();
        diagnostics_state::num_digits(line_nums.into_iter().max().unwrap_or(0))
    };
    let max_marker_prefix_length = {
        let markers_strs = |pg: &PositionGroup| -> Vec<String> {
            let pos = &pg.aggregate_position;
            let start_line = crate::pos::line(pos);
            let end_line = crate::pos::end_line(pos);
            (start_line..end_line + 1)
                .map(|line_num| markers_string(pg, Some(false), line_num))
                .collect()
        };
        let marker_lens: Vec<isize> = position_groups
            .iter()
            .flat_map(markers_strs)
            .map(|s| s.len() as isize)
            .collect();
        marker_lens.into_iter().max().unwrap_or(0)
    };
    // +1 for the space between them
    max_marker_prefix_length + 1 + largest_line_length
}

/// Each list of position_groups in the returned list is from a different file.
/// The first position_group in the list will contain _at least_ the first (i.e. main)
/// message. The list of marked_messages in each position group is ordered by increasing
/// line number (so the main message isn't necessarily first).
fn position_groups_by_file(marker_and_msgs: Vec<MarkedMessage>) -> Vec<Vec<PositionGroup>> {
    let msgs_by_file: Vec<Vec<MarkedMessage>> = ocaml_list::group(marker_and_msgs, |mm1, mm2| {
        let p1 = &mm1.message.0;
        let p2 = &mm2.message.0;
        crate::pos::filename(p1) != crate::pos::filename(p2)
    })
    .into_iter()
    // Must make sure list of positions is ordered
    .map(|msgs| {
        ocaml_list::stable_sort(msgs, |mm1, mm2| {
            let p1 = &mm1.message.0;
            let p2 = &mm2.message.0;
            crate::pos::line(p1).cmp(&crate::pos::line(p2))
        })
    })
    .collect();
    let close_enough = |prev_pos: &Absolute, curr_pos: &Absolute| -> bool {
        let line1_end = crate::pos::end_line(prev_pos);
        let line2_begin = crate::pos::line(curr_pos);

        // Example:
        // line1_end = 10:
        // [3] 10 |   $z = 3 * $x;
        //     11 |   if ($z is int) {
        //     12 |     echo 'int';
        //
        // line2_begin = 16
        //     14 |     echo 'not int';
        //     15 |   }
        // [1] 16 |   return $z;
        //
        // Then they should be conjoined as such:
        // [3] 10 |   $z = 3 * $x;
        //     11 |   if ($z is int) {
        //     12 |     echo 'int';
        //     13 |   } else
        //     14 |     echo 'not int';
        //     15 |   }
        // [1] 16 |   return $z;
        //
        // If they were any farther away, the line
        //     13 |   } else
        // would be replaced with
        //        :
        // to signify more than one interposing line.
        line1_end + n_extra_lines_hl + 2 >= line2_begin - n_extra_lines_hl
    };
    // Group marked messages that are sufficiently close.
    let grouped_messages = |messages: Vec<MarkedMessage>| -> Vec<Vec<MarkedMessage>> {
        ocaml_list::group(messages, |prev_mm, curr_mm| {
            let prev_pos = &prev_mm.message.0;
            let curr_pos = &curr_mm.message.0;
            !close_enough(prev_pos, curr_pos)
        })
    };
    msgs_by_file
        .into_iter()
        .map(|mmsgl| {
            grouped_messages(mmsgl)
                .into_iter()
                .map(|messages| PositionGroup {
                    aggregate_position: messages
                        .iter()
                        .map(|mm| mm.message.0.clone())
                        .reduce(|x1, x2| crate::pos::merge_absolute(&x1, &x2))
                        .unwrap_or_else(|| panic!("List.reduce_exn")),
                    messages,
                })
                .collect()
        })
        .collect()
}

fn format_file_name_and_pos(pgl: &[PositionGroup]) -> String {
    let relative_path = |path: &str| -> String {
        let cwd = getcwd_dir();
        lstrip(path, &cwd).to_string()
    };
    // Primary position for the file is the one with the lowest-numbered
    // marker across all positions in each position_group of the list
    let primary_pos = {
        let mms: Vec<&MarkedMessage> = pgl.iter().flat_map(|pg| pg.messages.iter()).collect();
        let MarkedMessage { message, .. } = ocaml_list::stable_sort(mms, |mm1, mm2| {
            let (mk1, _) = mm1.marker;
            let (mk2, _) = mm2.marker;
            mk1.cmp(&mk2)
        })
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("List.hd_exn"));
        message.0.clone()
    };
    let filename = relative_path(&crate::pos::filename(&primary_pos));
    let (line, col) = crate::pos::line_column_absolute(&primary_pos);
    let dirname = {
        let dn = ocaml_filename::dirname(&filename);
        if ocaml_filename::current_dir_name() == dn {
            "".to_string()
        } else {
            background_highlighted(&(ocaml_filename::dirname(&filename) + "/"))
        }
    };
    let filename = default_highlighted(&ocaml_filename::basename(&filename));
    let pretty_filename = format!("{}{}", dirname, filename);
    let pretty_position = background_highlighted(&format!(":{}:{}", line, col + 1));
    pretty_filename + &pretty_position
}

fn format_all_contexts_highlighted(marker_and_msgs: Vec<MarkedMessage>) -> String {
    // Create a set of position_groups (set of positions that can be written in the same snippet)
    let position_groups = position_groups_by_file(marker_and_msgs);
    let col_width = col_width_for_highlighted(&position_groups.concat());
    let sep = format!(
        "\n{} {}\n",
        string_make(col_width, ' '),
        background_highlighted(":")
    );
    let contexts: Vec<String> = position_groups
        .iter()
        .map(|pgl| {
            // Each position_groups list (pgl) is for a single file, so separate each with ':'
            let fn_pos = format_file_name_and_pos(pgl);
            let ctx_strs: Vec<String> = pgl
                .iter()
                .map(|pg| format_context_highlighted(col_width, pg))
                .collect();
            fn_pos + "\n" + &ctx_strs.join(&sep)
        })
        .collect();
    contexts.join("\n\n") + "\n\n"
}

fn single_marker_highlighted(marker: Marker) -> String {
    let (n, color) = marker;
    let lbracket = background_highlighted("[");
    let rbracket = background_highlighted("]");
    let npretty = tty::apply_color(None, Style::Normal(color), &n.to_string());
    lbracket + &npretty + &rbracket
}

fn format_claim_highlighted(
    severity: &Severity,
    error_code: ErrorCode,
    marker: (ErrorCode, RawColor),
    msg: &str,
) -> String {
    let suffix = single_marker_highlighted(marker);
    let (_, color) = marker;
    let pretty_severity =
        tty::apply_color(None, Style::Bold(color), &severity::to_string(severity));
    let pretty_error_code = tty::apply_color(
        None,
        Style::Bold(color),
        &user_diagnostic::error_code_to_string(error_code),
    );
    // The color of any highlighted text in the message itself should match
    // the marker color, unless it's a Lint message (Yellow), in which case
    // making it Red is fine because Red is not a color available on the color
    // wheel for subsequent reason messages (in addition, Lint messages don't
    // typically have subsequent reason messages anyway)
    let color = match color {
        RawColor::Yellow => RawColor::Red,
        _ => color,
    };
    let pretty_msg = markdown_lite::render(Some(true), Some(color), msg);
    format!(
        "{}: {} {} {}",
        pretty_severity, pretty_error_code, pretty_msg, suffix
    )
}

fn format_reason_highlighted(marked_msg: &MarkedMessage) -> String {
    let suffix = single_marker_highlighted(marked_msg.marker);
    let pretty_arrow = background_highlighted("->");
    let pretty_msg = markdown_lite::render(
        None,
        Some(marked_msg.marker.1),
        &marked_msg.message.1.to_str_lossy(),
    );
    format!("{} {} {}", pretty_arrow, pretty_msg, suffix)
}

fn make_marker(n: isize, severity: &Severity) -> Marker {
    let color_wheel = [
        RawColor::Cyan,
        RawColor::Green,
        RawColor::Magenta,
        RawColor::Blue,
    ];
    let color = if n <= 1 {
        severity::tty_color(severity)
    } else {
        let ix = (n - 2) % color_wheel.len() as isize;
        color_wheel[ix as usize]
    };
    (n, color)
}

/// Convert a list of messages tuples into marked_message structs,
/// by assigning each their original index in the list and a marker.
/// Any messages that have the same position (meaning exact location
/// and size) share the same marker.
fn mark_messages(severity: &Severity, msgl: Vec<Message<Absolute>>) -> Vec<MarkedMessage> {
    let mut next_marker_n: isize = 1;
    // The OCaml list, its head last.
    let mut existing_markers: Vec<(Marker, Absolute)> = vec![];
    msgl.into_iter()
        .enumerate()
        .map(|(original_index, message)| {
            let marker = {
                let curr_msg_pos = message.0.clone();
                match existing_markers
                    .iter()
                    .rev()
                    .find(|(_, pos)| crate::pos::equal_absolute(&curr_msg_pos, pos))
                {
                    None => {
                        let marker = make_marker(next_marker_n, severity);
                        next_marker_n += 1;
                        existing_markers.push((marker, curr_msg_pos));
                        marker
                    }
                    Some((marker, _)) => *marker,
                }
            };
            MarkedMessage {
                original_index: original_index as isize,
                marker,
                message,
            }
        })
        .collect()
}

pub fn to_string(error: &FinalizedDiagnostic) -> String {
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
    // Assign messages markers according to order of original error list
    // and then sort these marked messages such that messages in the same
    // file are together. Does not reorder the files or messages within a file.
    let marked_messages = {
        let mut msgl = vec![claim.clone()];
        msgl.extend(reasons.iter().cloned());
        diagnostics_state::combining_sort(mark_messages(severity, msgl), |mm| {
            crate::pos::filename(&mm.message.0)
        })
    };

    // Typing[4110] Invalid return type [1]   <claim>
    //  -> Expected int [2]                   <reasons>
    //  -> But got string [1]                 <reasons>
    let (claim, reasons) = {
        // Present the reasons in _exactly_ the order given in the error,
        // not in the marked_messages order, which is by file
        let mms = ocaml_list::stable_sort(marked_messages.clone(), |mm1, mm2| {
            mm1.original_index.cmp(&mm2.original_index)
        });
        match mms.split_first() {
            Some((mm, msgs)) => {
                // This very vitally assumes that the first message in the error is the main one
                (
                    format_claim_highlighted(
                        severity,
                        *code,
                        mm.marker,
                        &mm.message.1.to_str_lossy(),
                    ),
                    msgs.iter()
                        .map(format_reason_highlighted)
                        .collect::<Vec<_>>(),
                )
            }
            None => panic!("Impossible: an error always has non-empty list of messages"),
        }
    };

    // overlap_pos.php:4:10
    //       1 | <?hh
    //       2 |
    //   [2] 3 | function returns_int(): int {
    //   [1] 4 |   return 'foo';
    //       5 | }
    let all_contexts = format_all_contexts_highlighted(marked_messages);
    let mut buf = String::with_capacity(50);
    buf.push_str(&(claim + "\n"));
    if !reasons.is_empty() {
        buf.push_str(&(reasons.join("\n") + "\n"));
    }
    buf.push('\n');
    buf.push_str(&all_contexts);
    if !custom_msgs.is_empty() {
        buf.push_str(
            &(custom_msgs
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

    const SUITE: &str = "error_formatting_highlighted";
    const RAW_COLOR: &str = "error_formatting_highlighted_raw_color";

    /// The output of `hh_single_type_check` for these errors, compared with
    /// `exp` of `suite` (run with `FORCE_ERROR_COLOR=force_color`).
    fn check(
        test: &str,
        suite: &str,
        exp: &str,
        force_color: bool,
        errors: impl FnOnce() -> Vec<FinalizedDiagnostic>,
    ) {
        let out = fx::run_in_suite(module_path!(), test, suite, force_color, || {
            fx::single_type_check_output(
                diagnostics_state::Format::Highlighted,
                to_string,
                &errors(),
            )
        });
        if let Some(out) = out {
            fx::assert_same_text(&out, &fx::expected(suite, exp));
        }
    }

    fn always_true_warning() -> FinalizedDiagnostic {
        fx::warning(
            12007,
            fx::msg(
                fx::pos("always_true.php", (4, 6), (4, 19)),
                "Invalid comparison: This expression will always return `true`.\nA value of type `null` can never be equal to a value of type `vec<int>`",
            ),
            vec![],
        )
    }

    #[test]
    fn always_true() {
        check("always_true", SUITE, "always_true.php.exp", false, || {
            vec![always_true_warning()]
        })
    }

    #[test]
    fn raw_color_always_true() {
        check(
            "raw_color_always_true",
            RAW_COLOR,
            "always_true.php.raw_color.exp",
            true,
            || vec![always_true_warning()],
        )
    }

    #[test]
    fn raw_color_required_field_optional() {
        check(
            "raw_color_required_field_optional",
            RAW_COLOR,
            "required_field_optional.php.raw_color.exp",
            true,
            || vec![required_field_optional_error()],
        )
    }

    fn required_field_optional_error() -> FinalizedDiagnostic {
        let p = |start, end| fx::pos("required_field_optional.php", start, end);
        fx::err(
            4163,
            fx::msg(p((13, 9), (13, 11)), "Invalid return type"),
            vec![
                fx::msg(p((10, 2), (12, 3)), "The field `y` is **optional**"),
                fx::msg(
                    p((8, 26), (8, 34)),
                    "The field `y` is defined as **required**",
                ),
                fx::msg(p((5, 9), (5, 13)), "`y` is defined here"),
            ],
        )
    }

    #[test]
    fn required_field_optional() {
        check(
            "required_field_optional",
            SUITE,
            "required_field_optional.php.exp",
            false,
            || vec![required_field_optional_error()],
        )
    }

    #[test]
    fn return_type() {
        check("return_type", SUITE, "return_type.php.exp", false, || {
            let p = |start, end| fx::pos("return_type.php", start, end);
            vec![fx::err(
                4110,
                fx::msg(p((4, 9), (4, 16)), "Invalid return type"),
                vec![
                    fx::msg(p((3, 14), (3, 17)), "Expected `int`"),
                    fx::msg(p((4, 9), (4, 16)), "But got `string`"),
                ],
            )]
        })
    }

    #[test]
    fn mul_union() {
        check("mul_union", SUITE, "mul_union.php.exp", false, || {
            let p = |start, end| fx::pos("mul_union.php", start, end);
            vec![fx::err(
                4110,
                fx::msg(p((16, 9), (16, 11)), "Invalid return type"),
                vec![
                    fx::msg(p((4, 26), (4, 29)), "Expected `int`"),
                    fx::msg(
                        p((10, 7), (10, 13)),
                        "But got `float` because this is the result of an arithmetic operation with a `num` as the second argument, and no floats.",
                    ),
                    fx::msg(
                        p((6, 9), (6, 10)),
                        "Here is why I think the argument is a `num`: this is a `num`",
                    ),
                ],
            )]
        })
    }

    #[test]
    fn big_file() {
        check("big_file", SUITE, "big_file.php.exp", false, || {
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
        check(
            "messages_same_line",
            SUITE,
            "messages_same_line.php.exp",
            false,
            || {
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
            },
        )
    }

    #[test]
    fn zero_width_syntax_err() {
        check(
            "zero_width_syntax_err",
            SUITE,
            "zero_width_syntax_err.php.exp",
            false,
            || {
                let p = || fx::pos("zero_width_syntax_err.php", (3, 21), (3, 21));
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

    #[test]
    fn pos_across_multiple_lines() {
        check(
            "pos_across_multiple_lines",
            SUITE,
            "pos_across_multiple_lines.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("pos_across_multiple_lines.php", start, end);
                vec![
                    fx::err(
                        4110,
                        fx::msg(p((6, 9), (6, 16)), "Invalid return type"),
                        vec![
                            fx::msg(p((3, 14), (4, 6)), "Expected `dict<int, int>`"),
                            fx::msg(p((6, 9), (6, 16)), "But got `string`"),
                        ],
                    ),
                    fx::err(
                        4105,
                        fx::msg(
                            p((15, 2), (17, 4)),
                            "Too many positional arguments (expected 0 but got 3)",
                        ),
                        vec![fx::msg(p((9, 9), (9, 10)), "Definition is here")],
                    ),
                ]
            },
        )
    }

    #[test]
    fn pos_across_multiple_lines2() {
        check(
            "pos_across_multiple_lines2",
            SUITE,
            "pos_across_multiple_lines2.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("pos_across_multiple_lines2.php", start, end);
                vec![fx::err(
                    4105,
                    fx::msg(
                        p((8, 2), (10, 4)),
                        "Too many positional arguments (expected 0 but got 3)",
                    ),
                    vec![fx::msg(p((2, 9), (2, 10)), "Definition is here")],
                )]
            },
        )
    }

    #[test]
    fn error_pos_outside_range1() {
        check(
            "error_pos_outside_range1",
            SUITE,
            "error_pos_outside_range1.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("error_pos_outside_range1.php", start, end);
                vec![
                    fx::err(
                        1002,
                        fx::msg(
                            p((3, 10), (3, 11)),
                            "A name or `__construct` keyword is expected here.",
                        ),
                        vec![],
                    ),
                    fx::err(
                        1002,
                        fx::msg(
                            p((4, 2), (4, 8)),
                            "Encountered unexpected text `return`, was expecting a type hint.",
                        ),
                        vec![],
                    ),
                    fx::err(
                        4030,
                        fx::msg(p((3, 9), (3, 10)), "Was expecting a return type hint"),
                        vec![],
                    ),
                ]
            },
        )
    }

    #[test]
    fn error_pos_outside_range2() {
        check(
            "error_pos_outside_range2",
            SUITE,
            "error_pos_outside_range2.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("error_pos_outside_range2.php", start, end);
                vec![
                    fx::err(
                        1002,
                        fx::msg(p((1, 0), (1, 8)), "A .php file must begin with `<?hh`."),
                        vec![],
                    ),
                    fx::err(
                        1002,
                        fx::msg(
                            p((2, 0), (2, 1)),
                            "Encountered unexpected text ``, was expecting a function parameter.",
                        ),
                        vec![],
                    ),
                    fx::err(
                        4030,
                        fx::msg(p((1, 9), (1, 10)), "Was expecting a return type hint"),
                        vec![],
                    ),
                ]
            },
        )
    }

    #[test]
    fn error_pos_outside_range3() {
        check(
            "error_pos_outside_range3",
            SUITE,
            "error_pos_outside_range3.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("error_pos_outside_range3.php", start, end);
                vec![
                    fx::err(
                        1002,
                        fx::msg(
                            p((6, 4), (6, 5)),
                            "A right parenthesis `)` is expected here.",
                        ),
                        vec![],
                    ),
                    fx::err(
                        1002,
                        fx::msg(
                            p((7, 0), (7, 1)),
                            "Encountered unexpected text ``, was expecting a expression.",
                        ),
                        vec![],
                    ),
                    fx::err(
                        2049,
                        fx::msg(p((5, 2), (5, 3)), "Unbound name: `g` (a global function)"),
                        vec![],
                    ),
                    fx::err(
                        4107,
                        fx::msg(p((5, 2), (5, 3)), "Unbound name (typing): `g`"),
                        vec![],
                    ),
                ]
            },
        )
    }

    #[test]
    fn error_pos_outside_range4() {
        check(
            "error_pos_outside_range4",
            SUITE,
            "error_pos_outside_range4.php.exp",
            false,
            || {
                vec![fx::err(
                    1002,
                    fx::msg(
                        fx::pos("error_pos_outside_range4.php", (3, 20), (3, 21)),
                        "A right brace `}` is expected here.",
                    ),
                    vec![],
                )]
            },
        )
    }

    #[test]
    fn message_order() {
        check(
            "message_order",
            SUITE,
            "message_order.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("message_order.php", start, end);
                vec![
                    fx::err(
                        1002,
                        fx::msg(
                            p((4, 6), (4, 8)),
                            "Local variables cannot have type annotations in Hack.",
                        ),
                        vec![],
                    ),
                    fx::err(
                        2049,
                        fx::msg(p((4, 2), (4, 5)), "Unbound name: `int` (a global constant)"),
                        vec![],
                    ),
                    fx::err(
                        4106,
                        fx::msg(p((4, 2), (4, 5)), "Unbound global constant (Typing)"),
                        vec![],
                    ),
                ]
            },
        )
    }

    #[test]
    fn message_order2() {
        check(
            "message_order2",
            SUITE,
            "message_order2.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("message_order2.php", start, end);
                vec![
                    fx::err(
                        4110,
                        fx::msg(p((7, 15), (7, 16)), "Invalid argument"),
                        vec![
                            fx::msg(p((4, 22), (4, 28)), "Expected `string`"),
                            fx::msg(p((7, 15), (7, 16)), "But got `int`"),
                        ],
                    ),
                    fx::err(
                        4105,
                        fx::msg(
                            p((8, 2), (8, 23)),
                            "Too many positional arguments (expected 1 but got 2)",
                        ),
                        vec![fx::msg(p((3, 9), (3, 22)), "Definition is here")],
                    ),
                ]
            },
        )
    }

    #[test]
    fn two_pos_embedded_in_larger_pos() {
        check(
            "two_pos_embedded_in_larger_pos",
            SUITE,
            "two_pos_embedded_in_larger_pos.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("two_pos_embedded_in_larger_pos.php", start, end);
                vec![
                    fx::warning(
                        12007,
                        fx::msg(
                            p((4, 9), (4, 18)),
                            "Invalid comparison: This expression will always return `false`.\nA value of type `string` can never be equal to a value of type `int`",
                        ),
                        vec![],
                    ),
                    fx::warning(
                        12001,
                        fx::msg(
                            p((4, 9), (4, 18)),
                            "This expression is likely always `false`",
                        ),
                        vec![
                            fx::msg(p((4, 9), (4, 12)), "This is a string"),
                            fx::msg(p((4, 17), (4, 18)), "This is an int"),
                        ],
                    ),
                ]
            },
        )
    }

    #[test]
    fn position_within_position() {
        check(
            "position_within_position",
            SUITE,
            "position_within_position.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("position_within_position.php", start, end);
                vec![fx::err(
                    4110,
                    fx::msg(
                        p((4, 2), (4, 10)),
                        "`await` can only operate on an `Awaitable`",
                    ),
                    vec![
                        fx::msg(p((4, 2), (4, 10)), "Expected `Awaitable<nothing>`"),
                        fx::msg(p((4, 8), (4, 10)), "But got `int`"),
                    ],
                )]
            },
        )
    }

    /// Three errors in one file; the third has its reason on the line
    /// before its claim.
    #[test]
    fn abstract_private_method() {
        check(
            "abstract_private_method",
            SUITE,
            "abstract_private_method.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("abstract_private_method.php", start, end);
                vec![
                    fx::err(
                        1002,
                        fx::msg(
                            p((3, 6), (3, 7)),
                            "Class E contains an abstract method and must therefore be declared abstract",
                        ),
                        vec![],
                    ),
                    fx::err(
                        1002,
                        fx::msg(
                            p((4, 2), (4, 38)),
                            "Cannot declare abstract method E::f private",
                        ),
                        vec![],
                    ),
                    fx::err(
                        4465,
                        fx::msg(
                            p((4, 28), (4, 29)),
                            "Method f is abstract but the class is concrete. Either provide an implementation here.",
                        ),
                        vec![fx::msg(p((3, 6), (3, 7)), "Or make the class abstract.")],
                    ),
                ]
            },
        )
    }

    /// The code `Other[0000]`, and a position over two lines that marks
    /// both.
    #[test]
    fn const_late_init_property() {
        check(
            "const_late_init_property",
            SUITE,
            "const_late_init_property.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("const_late_init_property.php", start, end);
                vec![
                    fx::err(
                        0,
                        fx::msg(
                            p((3, 6), (3, 7)),
                            "Cannot use experimental feature: The __Const attribute is not supported.",
                        ),
                        vec![],
                    ),
                    fx::err(
                        1002,
                        fx::msg(
                            p((4, 2), (5, 19)),
                            "__Const properties may not also be __LateInit",
                        ),
                        vec![],
                    ),
                    fx::err(
                        4277,
                        fx::msg(
                            p((5, 13), (5, 15)),
                            "A late-initialized property cannot have a default value",
                        ),
                        vec![],
                    ),
                ]
            },
        )
    }

    #[test]
    fn extend_final_class() {
        check(
            "extend_final_class",
            SUITE,
            "extend_final_class.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("extend_final_class.php", start, end);
                vec![fx::err(
                    4035,
                    fx::msg(p((5, 6), (5, 7)), "You cannot extend final class _Foo_"),
                    vec![fx::msg(p((3, 12), (3, 17)), "Declaration is here")],
                )]
            },
        )
    }

    /// A `Naming` code.
    #[test]
    fn magic_class_outside_class() {
        check(
            "magic_class_outside_class",
            SUITE,
            "magic_class_outside_class.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("magic_class_outside_class.php", start, end);
                vec![fx::err(
                    2021,
                    fx::msg(
                        p((4, 20), (4, 29)),
                        "Using __CLASS__ outside a class or trait",
                    ),
                    vec![],
                )]
            },
        )
    }

    #[test]
    fn mixed_method_access() {
        check(
            "mixed_method_access",
            SUITE,
            "mixed_method_access.php.exp",
            false,
            || {
                let p = |start, end| fx::pos("mixed_method_access.php", start, end);
                vec![fx::err(
                    4064,
                    fx::msg(
                        p((4, 8), (4, 11)),
                        "You are trying to access the method `bar` but this is a mixed value. Use a specific class or interface name.",
                    ),
                    vec![fx::msg(p((3, 22), (3, 32)), "Definition is here")],
                )]
            },
        )
    }

    /// With colors: a zero-width position, a position just past the end of
    /// a line, and the markers of overlapping positions (the shorter one
    /// wins); messages in two files (the second one in a subdirectory, whose
    /// name is dimmed), and custom messages.
    #[test]
    fn colors_two_files_and_custom_messages() {
        let out = fx::run_in_suite(
            module_path!(),
            "colors_two_files_and_custom_messages",
            "error_formatting_highlighted_raw_color/..",
            true,
            || {
                let p = |file, start, end| fx::pos(file, start, end);
                let mut e = fx::err(
                    4110,
                    fx::msg(
                        p(
                            "error_formatting_highlighted/always_true.php",
                            (4, 6),
                            (4, 10),
                        ),
                        "claim",
                    ),
                    vec![
                        fx::msg(
                            p(
                                "error_formatting_highlighted/always_true.php",
                                (4, 6),
                                (4, 19),
                            ),
                            "wider",
                        ),
                        fx::msg(
                            p(
                                "error_formatting/zero_width_syntax_err.php",
                                (3, 18),
                                (3, 18),
                            ),
                            "zero",
                        ),
                    ],
                );
                e.custom_msgs = vec!["see `this`".to_string()];
                to_string(&e)
            },
        );
        if let Some(out) = out {
            let dim = |s: &str| format!("\x1b[0;2m{s}\x1b[0m");
            let red = |s: &str| format!("\x1b[31m{s}\x1b[0m");
            let cyan = |s: &str| format!("\x1b[36m{s}\x1b[0m");
            let green = |s: &str| format!("\x1b[32m{s}\x1b[0m");
            let marker = |n: &str, c: &dyn Fn(&str) -> String| dim("[") + &c(n) + &dim("]");
            // Highlighted text is colored character by character.
            let chars = |s: &str, c: &dyn Fn(&str) -> String| -> String {
                s.chars().map(|ch| c(&ch.to_string())).collect()
            };
            // The exact layout is checked line by line below.
            let lines: Vec<&str> = out.split('\n').collect();
            assert_eq!(
                lines[0],
                format!(
                    "\x1b[31;1merror\x1b[0m: \x1b[31;1mTyping[4110]\x1b[0m \x1b[0;1mclaim\x1b[0m {}",
                    marker("1", &red)
                )
            );
            assert_eq!(
                lines[1],
                format!("{} wider {}", dim("->"), marker("2", &cyan))
            );
            assert_eq!(
                lines[2],
                format!("{} zero {}", dim("->"), marker("3", &green))
            );
            assert_eq!(lines[3], "");
            assert_eq!(
                lines[4],
                format!(
                    "{}always_true.php{}",
                    dim("error_formatting_highlighted/"),
                    dim(":4:7")
                )
            );
            // col_width: "[1,2]" and 1 digit: 7.
            assert_eq!(lines[5], format!("      {}{} ", dim("2"), dim(" |")));
            assert_eq!(
                lines[6],
                format!(
                    "      {}{} function foo(varray<int> $arg): void {{",
                    dim("3"),
                    dim(" |")
                )
            );
            assert_eq!(
                lines[7],
                format!(
                    "{} {}{} {}{}{}) {{",
                    dim("[") + &red("1") + &dim(",") + &cyan("2") + &dim("]"),
                    dim("4"),
                    dim(" |"),
                    "  if (",
                    chars("null", &red),
                    chars(" !== $arg", &cyan)
                )
            );
            assert_eq!(lines[8], format!("      {}{}   }}", dim("5"), dim(" |")));
            assert_eq!(lines[9], format!("      {}{} }}", dim("6"), dim(" |")));
            assert_eq!(lines[10], "");
            assert_eq!(
                lines[11],
                format!(
                    "{}zero_width_syntax_err.php{}",
                    dim("error_formatting/"),
                    dim(":3:19")
                )
            );
            assert_eq!(lines[12], format!("      {}{} <?hh", dim("1"), dim(" |")));
            assert_eq!(lines[13], format!("      {}{} ", dim("2"), dim(" |")));
            assert_eq!(
                lines[14],
                format!(
                    "{}   {}{} class Foo extends {}}}",
                    marker("3", &green),
                    dim("3"),
                    dim(" |"),
                    green("{")
                )
            );
            assert_eq!(lines[15], "");
            assert_eq!(lines[16], "\x1b[0;1msee \x1b[0m\x1b[0;1;4mthis\x1b[0m");
            assert_eq!(lines[17], "");
            assert_eq!(lines.len(), 18);
        }
    }
}
