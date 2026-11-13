// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! subchunk.ml
//!
//! A subchunk represents a substring of the final string representation of a
//! chunk in the formatted output. This representation is a convenient
//! intermediate step because it allows us to trim whitespace and trailing
//! commas at the edges of formatted ranges as needed.

use crate::format_env::Env;
use crate::interval::Interval;
use crate::solve_state::SolveState;

#[derive(Clone, Debug)]
pub enum Subchunk<'a> {
    Atom { text: &'a [u8], range: Interval },
    Comma,
    Space,
    Newline,
    Indent(isize),
}

pub fn string_of_subchunks(env: &Env, subchunks: &[Subchunk<'_>]) -> Vec<u8> {
    let mut buf = Vec::with_capacity(200);
    for sc in subchunks {
        match sc {
            Subchunk::Atom { text, .. } => buf.extend_from_slice(text),
            Subchunk::Comma => buf.push(b','),
            Subchunk::Space => buf.push(b' '),
            Subchunk::Newline => buf.push(b'\n'),
            Subchunk::Indent(indent) => {
                let n = if env.indent_with_tabs {
                    *indent
                } else {
                    *indent * env.indent_width
                };
                let c = if env.indent_with_tabs { b'\t' } else { b' ' };
                if n < 0 {
                    // String.make raises on a negative length.
                    crate::error::raise(crate::error::Exn::InvalidArgument("String.create".into()));
                }
                buf.extend(std::iter::repeat_n(c, n as usize));
            }
        }
    }
    buf
}

pub fn subchunks_in_range<'a>(
    include_leading_whitespace: bool,
    include_trailing_whitespace: bool,
    subchunks: Vec<Subchunk<'a>>,
    range: Interval,
) -> Vec<Subchunk<'a>> {
    let (range_start, range_end) = range;
    // Filter to the atoms which overlap with the range, including the leading
    // and trailing non-Atom subchunks.
    let end = subchunks
        .iter()
        .position(|sc| match sc {
            Subchunk::Atom { range: (st, ed), .. } => {
                !(*st < range_end || (*st == range_end && *ed == range_end))
            }
            _ => false,
        })
        .unwrap_or(subchunks.len());
    let start = subchunks[..end]
        .iter()
        .rposition(|sc| match sc {
            Subchunk::Atom { range: (st, ed), .. } => {
                !(*ed > range_start || (*st == range_start && *ed == range_start))
            }
            _ => false,
        })
        .map_or(0, |i| i + 1);
    let mut start = start;
    let mut end = end;
    // Drop trailing spaces and indentation
    while end > start && matches!(subchunks[end - 1], Subchunk::Space | Subchunk::Indent(_)) {
        end -= 1;
    }
    // When omitting trailing whitespace, drop trailing newlines
    if !include_trailing_whitespace {
        while end > start && matches!(subchunks[end - 1], Subchunk::Newline) {
            end -= 1;
        }
    }
    // Drop leading newline. Also drop leading Commas. Comma represents a
    // trailing comma that was added because its associated split was broken
    // on. Since we don't have source mapping information for Commas, we only
    // want to print them when the atom preceding the trailing comma is
    // printed.
    while start < end
        && matches!(
            subchunks[start],
            Subchunk::Newline | Subchunk::Space | Subchunk::Comma
        )
    {
        start += 1;
    }
    // When omitting leading whitespace, drop leading indentation
    if !include_leading_whitespace {
        while start < end && matches!(subchunks[start], Subchunk::Indent(_)) {
            start += 1;
        }
    }
    subchunks[start..end].to_vec()
}

pub fn subchunks_of_solve_state<'a>(state: &SolveState<'_, 'a>) -> Vec<Subchunk<'a>> {
    let mut subchunks = vec![];
    for chunk in state.chunks() {
        if state.has_split_before_chunk(chunk) {
            subchunks.push(Subchunk::Newline);
            if !chunk.is_empty() && chunk.indentable {
                subchunks.push(Subchunk::Indent(state.get_indent_level(chunk)));
            }
        } else if chunk.space_if_not_split {
            subchunks.push(Subchunk::Space);
        }
        for atom in &chunk.atoms {
            if atom.leading_space {
                subchunks.push(Subchunk::Space);
            }
            subchunks.push(Subchunk::Atom {
                text: atom.text,
                range: atom.range,
            });
        }
        if state.has_comma_after_chunk(chunk) {
            match chunk.comma.and_then(|(_, range)| range) {
                Some(range) => subchunks.push(Subchunk::Atom { text: b",", range }),
                None => subchunks.push(Subchunk::Comma),
            }
        }
    }
    // Every chunk group has a newline trailing it, but chunks are associated
    // with the split preceding them. In order to ensure that we print
    // trailing newlines and not leading newlines, we always add a newline
    // here, and strip leading newlines below.
    subchunks.push(Subchunk::Newline);
    let first = subchunks
        .iter()
        .position(|sc| !matches!(sc, Subchunk::Newline))
        .unwrap_or(subchunks.len());
    subchunks.split_off(first)
}
