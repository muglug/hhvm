// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! boundaries.ml

use crate::chunk::ChunkGroup;
use crate::error::Exn;
use crate::error::raise;
use crate::interval::Interval;

/// `String_utils.split_on_newlines`: split on '\n', without an entry for the
/// line after a trailing newline (and no lines at all for the empty string).
pub fn split_on_newlines(text: &[u8]) -> Vec<&[u8]> {
    if text.is_empty() {
        return vec![];
    }
    let mut lines: Vec<&[u8]> = text.split(|c| *c == b'\n').collect();
    if lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    lines
}

/// `Boundaries.get_line_boundaries`
pub fn get_line_boundaries(text: &[u8]) -> Vec<Interval> {
    let mut bytes_seen = 0;
    split_on_newlines(text)
        .into_iter()
        .map(|line| {
            let line_start = bytes_seen;
            let line_end = line_start + line.len() as isize + 1;
            bytes_seen = line_end;
            (line_start, line_end)
        })
        .collect()
}

/// `Boundaries.expand_to_line_boundaries`
pub fn expand_to_line_boundaries(
    ranges: Option<&[Interval]>,
    source_text: &[u8],
    range: Interval,
) -> Interval {
    let (start_offset, end_offset) = range;
    // Ensure that 0 <= start_offset <= end_offset <= source_text length
    let start_offset = std::cmp::max(start_offset, 0);
    let end_offset = std::cmp::max(start_offset, end_offset);
    let end_offset = std::cmp::min(end_offset, source_text.len() as isize);
    let start_offset = std::cmp::min(start_offset, end_offset);
    // Ensure that start_offset and end_offset fall on line boundaries
    let owned;
    let ranges = match ranges {
        Some(r) => r,
        None => {
            owned = get_line_boundaries(source_text);
            &owned
        }
    };
    let mut st = start_offset;
    let mut ed = end_offset;
    for &(line_start, line_end) in ranges {
        if st > line_start && st < line_end {
            st = line_start;
        }
        if ed > line_start && ed < line_end {
            ed = line_end;
        }
    }
    (st, ed)
}

/// `Boundaries.line_interval_to_offset_range`; raises `Invalid_argument`.
pub fn line_interval_to_offset_range(line_boundaries: &[Interval], (start_line, end_line): Interval) -> Interval {
    if start_line > end_line {
        raise(Exn::InvalidArgument(format!(
            "Illegal line interval: {},{}",
            start_line, end_line
        )));
    }
    let n = line_boundaries.len() as isize;
    if start_line < 1 || start_line > n || end_line < 1 || end_line > n {
        raise(Exn::InvalidArgument(format!(
            "Can't format line interval {},{} in file with {} lines",
            start_line, end_line, n
        )));
    }
    let (start_offset, _) = line_boundaries[(start_line - 1) as usize];
    let (_, end_offset) = line_boundaries[(end_line - 1) as usize];
    (start_offset, end_offset)
}

/// `Boundaries.get_atom_boundaries`
pub fn get_atom_boundaries(chunk_groups: &[ChunkGroup<'_>]) -> Vec<Interval> {
    chunk_groups
        .iter()
        .flat_map(|g| &g.chunks)
        .flat_map(|c| &c.atoms)
        .map(|a| a.range)
        .collect()
}

/// `Boundaries.expand_to_atom_boundaries`
pub fn expand_to_atom_boundaries(boundaries: &[Interval], (r_st, r_ed): Interval) -> Interval {
    let st = match boundaries.iter().rev().find(|(b_st, _)| *b_st <= r_st) {
        Some(bound) => bound.0,
        None => r_st,
    };
    let ed = match boundaries.iter().find(|(_, b_ed)| *b_ed >= r_ed) {
        Some(bound) => bound.1,
        None => r_ed,
    };
    (st, ed)
}
