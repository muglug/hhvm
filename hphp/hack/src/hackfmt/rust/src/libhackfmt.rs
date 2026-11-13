// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! libhackfmt.ml

use bumpalo::Bump;
use parser_core_types::syntax_kind::SyntaxKind;

use crate::boundaries::expand_to_atom_boundaries;
use crate::boundaries::expand_to_line_boundaries;
use crate::boundaries::get_atom_boundaries;
use crate::boundaries::get_line_boundaries;
use crate::boundaries::line_interval_to_offset_range;
use crate::chunk::ChunkGroup;
use crate::chunk_builder;
use crate::doc::Doc;
use crate::error::Exn;
use crate::error::raise;
use crate::format_env::Env;
use crate::hack_format;
use crate::interval;
use crate::interval::Interval;
use crate::line_splitter;
use crate::noformat::get_suppressed_formatting_ranges;
use crate::syntax;
use crate::syntax::SyntaxTree;

/// `Libhackfmt.env_from_config`
pub fn env_from_config(config: Option<&Env>) -> Env {
    let env = config.cloned().unwrap_or_default();
    if env.indent_width < 0 {
        raise(Exn::InvalidArgument("Invalid indent width".into()));
    }
    if env.line_width < 0 {
        raise(Exn::InvalidArgument("Invalid line width".into()));
    }
    env
}

fn byte_at(text: &[u8], i: isize) -> u8 {
    match usize::try_from(i).ok().and_then(|i| text.get(i)) {
        Some(c) => *c,
        None => raise(Exn::InvalidArgument("index out of bounds".into())),
    }
}

fn text_with_formatted_ranges(
    range: Option<Interval>,
    text: &[u8],
    formatted_ranges: &[(Interval, Vec<u8>)],
) -> Vec<u8> {
    let (start_offset, end_offset) = match range {
        Some(r) => r,
        None => (0, text.len() as isize),
    };
    let mut buf = Vec::with_capacity((end_offset - start_offset + 256).max(0) as usize);
    let mut bytes_seen = start_offset;
    for ((st, ed), formatted) in formatted_ranges {
        let mut i = bytes_seen;
        while i <= st - 1 {
            buf.push(byte_at(text, i));
            i += 1;
        }
        buf.extend_from_slice(formatted);
        bytes_seen = *ed;
    }
    let mut i = bytes_seen;
    while i <= end_offset - 1 {
        buf.push(byte_at(text, i));
        i += 1;
    }
    buf
}

/// Transform and build the chunk groups of a tree.
pub fn chunk_groups<'a>(env: &Env, arena: &'a Bump, tree: &SyntaxTree<'a>) -> (Doc<'a>, Vec<ChunkGroup<'a>>) {
    let doc = hack_format::transform(env, arena, &tree.root);
    let chunk_groups = chunk_builder::build(env, &doc);
    (doc, chunk_groups)
}

/// `Libhackfmt.format_tree`
pub fn format_tree(config: Option<&Env>, tree: &SyntaxTree<'_>) -> Vec<u8> {
    let text = tree.text;
    let env = env_from_config(config);
    let arena = Bump::new();
    let (_, chunk_groups) = chunk_groups(&env, &arena, tree);
    let line_boundaries = get_line_boundaries(text);
    let noformat_ranges = get_suppressed_formatting_ranges(&env, &line_boundaries, tree);
    let whole_file = [(0, text.len() as isize)];
    let ranges = interval::diff_sorted_lists(&whole_file, &noformat_ranges);
    let formatted_ranges: Vec<(Interval, Vec<u8>)> = ranges
        .into_iter()
        .map(|range| {
            (
                range,
                line_splitter::solve(&env, Some(range), true, true, Some(text), &chunk_groups),
            )
        })
        .collect();
    text_with_formatted_ranges(None, text, &formatted_ranges)
}

/// `Libhackfmt.format_range`
pub fn format_range(config: Option<&Env>, range: Interval, tree: &SyntaxTree<'_>) -> Vec<u8> {
    let text = tree.text;
    let env = env_from_config(config);
    let arena = Bump::new();
    let (_, chunk_groups) = chunk_groups(&env, &arena, tree);
    let line_boundaries = get_line_boundaries(text);
    let noformat_ranges = get_suppressed_formatting_ranges(&env, &line_boundaries, tree);
    let ranges = interval::diff_sorted_lists(&[range], &noformat_ranges);
    let formatted_ranges: Vec<(Interval, Vec<u8>)> = ranges
        .into_iter()
        .map(|range| {
            (
                range,
                line_splitter::solve(&env, Some(range), true, true, Some(text), &chunk_groups),
            )
        })
        .collect();
    text_with_formatted_ranges(Some(range), text, &formatted_ranges)
}

/// `Libhackfmt.format_intervals`: the intervals are 1-based, inclusive line
/// intervals. Raises `Invalid_argument` for intervals out of bounds.
pub fn format_intervals(config: Option<&Env>, intervals: &[Interval], tree: &SyntaxTree<'_>) -> Vec<u8> {
    let text = tree.text;
    let env = env_from_config(config);
    let arena = Bump::new();
    let (_, chunk_groups) = chunk_groups(&env, &arena, tree);
    let line_boundaries = get_line_boundaries(text);
    let atom_boundaries = get_atom_boundaries(&chunk_groups);
    let mut ranges: Vec<Interval> = intervals
        .iter()
        .map(|i| line_interval_to_offset_range(&line_boundaries, *i))
        // If we get a range which starts or ends exactly at an atom boundary,
        // expand it to the NEXT atom boundary so that we get the whitespace
        // surrounding the formatted range.
        .map(|(st, ed)| (st - 1, ed + 1))
        .map(|r| expand_to_atom_boundaries(&atom_boundaries, r))
        .collect();
    ranges.sort_by(|a, b| interval::compare(*a, *b));
    let ranges = interval::union_consecutive_overlapping(&ranges);
    let noformat_ranges = get_suppressed_formatting_ranges(&env, &line_boundaries, tree);
    let ranges = interval::diff_sorted_lists(&ranges, &noformat_ranges);
    let formatted_ranges: Vec<(Interval, Vec<u8>)> = ranges
        .into_iter()
        .map(|range| {
            let include_leading_whitespace = !atom_boundaries.iter().any(|(st, _)| range.0 == *st);
            let include_trailing_whitespace = !atom_boundaries.iter().any(|(_, ed)| range.1 == *ed);
            (
                range,
                line_splitter::solve(
                    &env,
                    Some(range),
                    include_leading_whitespace,
                    include_trailing_whitespace,
                    Some(text),
                    &chunk_groups,
                ),
            )
        })
        .collect();
    let mut buf = text_with_formatted_ranges(None, text, &formatted_ranges);
    // Dirty hack: Since we don't print the whitespace surrounding formatted
    // ranges, we don't print the trailing newline at the end of the file if
    // the last line in the file was modified. Add it here manually.
    if !buf.is_empty() && *buf.last().unwrap() != b'\n' {
        buf.push(b'\n');
    }
    buf
}

/// `Libhackfmt.format_at_offset`: format the node which is the direct parent
/// of the token at the given offset (raises `Invalid_argument`).
pub fn format_at_offset(config: Option<&Env>, tree: &SyntaxTree<'_>, offset: isize) -> (Interval, Vec<u8>) {
    let text = tree.text;
    let env = env_from_config(config);
    let arena = Bump::new();
    let (_, chunk_groups) = chunk_groups(&env, &arena, tree);
    // Grab the node which is the direct parent of the token at offset. If the
    // direct parent is a CompoundStatement, skip it and get the grandparent
    // (so we format entire IfStatements or MethodishDeclarations when
    // formatting at the closing brace).
    let parents = syntax::parentage(&tree.root, offset);
    let ((token, token_start), (node, node_start)) = match parents.as_slice() {
        [token, parent, grandparent, ..]
            if parent.0.kind == SyntaxKind::CompoundStatement
                && grandparent.0.kind != SyntaxKind::SyntaxList =>
        {
            (*token, *grandparent)
        }
        [token, parent, ..] => (*token, *parent),
        _ => raise(Exn::InvalidArgument("Invalid offset".into())),
    };
    // PS.end_offset token: the last character of the token.
    let token_start_offset = token_start + syntax::trivia_width(token.leading_trivia()) as isize;
    let token_end_offset = token_start_offset + token.inner_width().saturating_sub(1) as isize;
    // Only format at the end of a token.
    if offset != token_end_offset {
        raise(Exn::InvalidArgument(
            "Offset must point to the last character of a token".into(),
        ));
    }
    // Our ranges are half-open, so the range end is the token end offset + 1.
    let ed = offset + 1;
    // Take a half-open range which starts at the beginning of the parent node
    let node_start_offset = node_start + syntax::trivia_width(node.leading_trivia()) as isize;
    let range = (node_start_offset, ed);
    // Expand the start offset to the nearest line boundary in the original
    // source, since we want to add a leading newline before the node we're
    // formatting if one should be there and isn't already present.
    let range = (expand_to_line_boundaries(None, text, range).0, ed);
    // Expand the start offset to the nearest atom boundary in the original
    // source, so that all whitespace preceding the formatted atoms is included
    // in the range.
    let atom_boundaries = get_atom_boundaries(&chunk_groups);
    let range = (expand_to_atom_boundaries(&atom_boundaries, range).0, ed);
    let formatted = line_splitter::solve(&env, Some(range), false, false, Some(text), &chunk_groups);
    (range, formatted)
}
