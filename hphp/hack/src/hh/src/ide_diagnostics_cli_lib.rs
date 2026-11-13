// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/ide_diagnostics_cli_lib.ml` (the
//! `--ide-diagnostics` mode of `hh single`). See `hh/PORTING.md`.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::client_ide_message;
use crate::code_actions::code_actions_utils as cu;
use crate::diagnostics_state;
use crate::full_fidelity_source_text as source_text;
use crate::pos::Absolute;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::user_diagnostic;

/// (`Server_rename_types.patch`: see [`cu::Patch`].)
fn apply_patches_to_string(old_content: &[u8], patches: Vec<cu::Patch>) -> Vec<u8> {
    cu::apply_patches_to_string(old_content, patches)
}

/// Represents the range to underline for a line in a source file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Underline {
    /// 1-indexed, inclusive
    ul_start_column: isize,
    /// 1-indexed, exclusive
    ul_end_column: isize,
}

/// `underline list I_map.t`
type UnderlinesPerLine = BTreeMap<isize, Vec<Underline>>;

/// Watch it! ChatGPT wrote this code.
///
/// It's a classic implementation for merging half-open intervals.
fn merge_underlines(underlines: Vec<Underline>) -> Vec<Underline> {
    let compare = |u1: &Underline, u2: &Underline| {
        u1.ul_start_column
            .cmp(&u2.ul_start_column)
            .then(u1.ul_end_column.cmp(&u2.ul_end_column))
    };
    let sorted_intervals = crate::rt::ocaml_list::stable_sort(underlines, compare);
    let mut iter = sorted_intervals.into_iter();
    match iter.next() {
        None => vec![],
        Some(hd) => {
            // `merge_acc [] hd tl`
            let mut merged_list = vec![];
            let mut current_interval = hd;
            for Underline {
                ul_start_column: x,
                ul_end_column: y,
            } in iter
            {
                let Underline {
                    ul_start_column: prev_x,
                    ul_end_column: prev_y,
                } = current_interval;
                if x <= prev_y {
                    current_interval = Underline {
                        ul_start_column: prev_x,
                        ul_end_column: std::cmp::max(y, prev_y),
                    }
                } else {
                    merged_list.push(current_interval);
                    current_interval = Underline {
                        ul_start_column: x,
                        ul_end_column: y,
                    }
                }
            }
            merged_list.push(current_interval);
            merged_list.reverse();
            crate::rt::ocaml_list::stable_sort(merged_list, compare)
        }
    }
}

fn pos_to_underlines(st: &source_text::T, pos: &Absolute) -> UnderlinesPerLine {
    let (start_line, start_col, end_line, end_col) = crate::pos::destruct_range_one_based(pos);

    // For each line, we'll have to calculate where to put the underline
    let num_lines = end_line - start_line + 1;
    let mut underlines_per_line = UnderlinesPerLine::new();
    for line_index in 0..num_lines {
        let line_number = start_line + line_index;
        let line_len = source_text::line_text(st, line_number).len() as isize;
        let ul_start_column = if line_index == 0 { start_col } else { 0 };
        let ul_end_column = if line_index == num_lines - 1 { end_col } else { line_len };
        underlines_per_line.entry(line_number).or_default().insert(
            0,
            Underline {
                ul_start_column,
                ul_end_column,
            },
        );
    }
    underlines_per_line
}

/// `String.make n c`
fn string_make(n: isize, c: char) -> String {
    if n < 0 {
        panic!("Invalid_argument(\"String.make\")")
    }
    std::iter::repeat(c).take(n as usize).collect()
}

fn underlines_for_line_to_patches(uls: Vec<Underline>) -> String {
    let uls = merge_underlines(uls);
    let mut text = String::new();
    // columns start at 1!
    let mut previous_end_column = 1;
    for Underline {
        ul_start_column,
        ul_end_column,
    } in uls
    {
        let prefix = string_make(std::cmp::max(0, ul_start_column - previous_end_column), ' ');
        let underline = string_make(ul_end_column - ul_start_column, '~');
        text.push_str(&prefix);
        text.push_str(&underline);
        previous_end_column = ul_end_column;
    }
    text.push('\n');
    text
}

fn underlines_to_patches(
    filename: &RelativePath,
    st: &source_text::T,
    underlines_per_line: UnderlinesPerLine,
) -> Vec<cu::Patch> {
    underlines_per_line
        .into_iter()
        .map(|(line_number, uls)| {
            let text = underlines_for_line_to_patches(uls);
            let insert_offset = source_text::position_to_offset(st, (line_number + 1, 1));
            let insert_pos = source_text::relative_pos(filename, st, insert_offset, insert_offset);
            cu::Patch::Replace { pos: insert_pos, text }
        })
        .collect()
}

fn diagnostic_to_underlines(st: &source_text::T, diagnostic: &client_ide_message::Diagnostic) -> Vec<UnderlinesPerLine> {
    let client_ide_message::Diagnostic {
        diagnostic_error,
        diagnostic_related_hints,
        ..
    } = diagnostic;
    let hint_uls = diagnostic_related_hints.iter().map(|pos| pos_to_underlines(st, pos));
    let error_uls = pos_to_underlines(st, &user_diagnostic::get_pos(diagnostic_error));
    std::iter::once(error_uls).chain(hint_uls).collect()
}

fn diagnostics_to_underlines(st: &source_text::T, diagnostics: &[client_ide_message::Diagnostic]) -> UnderlinesPerLine {
    let mut acc = UnderlinesPerLine::new();
    for diagnostic in diagnostics {
        for m in diagnostic_to_underlines(st, diagnostic) {
            for (key, ys) in m {
                // `Some (xs @ ys)`
                acc.entry(key).or_default().extend(ys)
            }
        }
    }
    acc
}

fn run_exn(ctx: &provider_context::T, entry: &Arc<provider_context::Entry>, errors: diagnostics_state::T) {
    let errors = diagnostics_state::get_sorted_diagnostic_list(None, errors);
    let error_hashes: Vec<_> = errors
        .iter()
        .map(|err| {
            (
                user_diagnostic::to_absolute(err),
                user_diagnostic::hash_diagnostic_for_saved_state(err),
            )
        })
        .collect();
    let diagnostics = crate::ide_diagnostics::convert(ctx, entry, error_hashes);
    let path = &entry.path;
    // `entry.Provider_context.source_text |> Option.value_exn`
    let st = crate::ast_provider::compute_source_text(entry);
    let underlines = diagnostics_to_underlines(&st, &diagnostics);
    let patches = underlines_to_patches(path, &st, underlines);
    let source_text = match crate::sys_utils::cat(&crate::relative_path::to_absolute(path)) {
        Ok(source_text) => source_text,
        Err(e) => panic!("{:?}", e),
    };
    let rewritten = apply_patches_to_string(&source_text, patches);
    use std::io::Write;
    let _ = std::io::stdout().write_all(&rewritten);
}

pub fn run(ctx: &provider_context::T, entry: &Arc<provider_context::Entry>, errors: diagnostics_state::T) {
    // `| exception exn -> print_endline @@ Exn.to_string exn`
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_exn(ctx, entry, errors))) {
        Ok(()) => {}
        Err(payload) => {
            let msg = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "exception".to_string());
            println!("{}", msg)
        }
    }
}
