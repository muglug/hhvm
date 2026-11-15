// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! noformat.ml

use parser_core_types::trivia_kind::TriviaKind;

use crate::boundaries::expand_to_line_boundaries;
use crate::format_env::Env;
use crate::interval;
use crate::interval::Interval;
use crate::syntax::Node;
use crate::syntax::SyntaxTree;
use crate::syntax::Trivia;

const GENERATED_TAG: &[u8] = b"@generated";
const PARTIALLY_GENERATED_TAG: &[u8] = b"@partially-generated";
const BEGIN_MANUAL_SECTION: &[u8] = b"/* BEGIN MANUAL SECTION ";
const END_MANUAL_SECTION_TAG: &[u8] = b"/* END MANUAL SECTION */";
const LINT_IGNORE_TAG: &[u8] = b"@lint-ignore";

pub fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    find(haystack, needle, 0).is_some()
}

fn find(haystack: &[u8], needle: &[u8], from: usize) -> Option<usize> {
    if needle.is_empty() {
        return Some(from);
    }
    if haystack.len() < needle.len() {
        return None;
    }
    (from..=haystack.len() - needle.len()).find(|&i| &haystack[i..i + needle.len()] == needle)
}

pub fn is_generated_file(text: &[u8]) -> bool {
    contains(text, GENERATED_TAG)
}

pub fn is_partially_generated_file(text: &[u8]) -> bool {
    contains(text, PARTIALLY_GENERATED_TAG)
}

/// A match of `/\* BEGIN MANUAL SECTION [^*]*\*/` anywhere in the text.
fn is_begin_manual_section_tag(text: &[u8]) -> bool {
    let mut from = 0;
    while let Some(p) = find(text, BEGIN_MANUAL_SECTION, from) {
        let rest = &text[p + BEGIN_MANUAL_SECTION.len()..];
        if let Some(star) = rest.iter().position(|c| *c == b'*') {
            if rest.get(star + 1) == Some(&b'/') {
                return true;
            }
        }
        from = p + 1;
    }
    false
}

fn is_end_manual_section_tag(text: &[u8]) -> bool {
    text == END_MANUAL_SECTION_TAG
}

fn is_lint_ignore(text: &[u8]) -> bool {
    contains(text, LINT_IGNORE_TAG)
}

enum ManualTag {
    Begin(isize),
    End(isize),
}

fn add_fixme_range(fixmes: &mut Vec<Interval>, trivium: &Trivia<'_>) {
    let range = (
        trivium.start_offset() as isize,
        trivium.start_offset() as isize + trivium.width() as isize - 1,
    );
    match trivium.kind {
        TriviaKind::FixMe | TriviaKind::Ignore | TriviaKind::IgnoreError => fixmes.push(range),
        TriviaKind::DelimitedComment | TriviaKind::SingleLineComment
            if is_lint_ignore(trivium.text) =>
        {
            fixmes.push(range)
        }
        _ => {}
    }
}

fn add_manual_tag(manual_tags: &mut Vec<ManualTag>, trivium: &Trivia<'_>) {
    if trivium.kind == TriviaKind::DelimitedComment {
        if is_begin_manual_section_tag(trivium.text) {
            manual_tags.push(ManualTag::Begin(
                trivium.start_offset() as isize + trivium.width() as isize - 1,
            ));
        } else if is_end_manual_section_tag(trivium.text) {
            manual_tags.push(ManualTag::End(trivium.start_offset() as isize));
        }
    }
}

/// Return the start and end offsets of every fixme comment and every manual
/// section (of partially-generated files), sorted by order of appearance in
/// the file.
fn get_fixme_ranges_and_manual_sections(root: &Node<'_>) -> (Vec<Interval>, Vec<Interval>) {
    let mut fixmes = vec![];
    let mut manual_tags = vec![];
    root.for_each_token(&mut |t| {
        for tr in &t.leading {
            add_fixme_range(&mut fixmes, tr);
            add_manual_tag(&mut manual_tags, tr);
        }
        for tr in &t.trailing {
            add_fixme_range(&mut fixmes, tr);
            add_manual_tag(&mut manual_tags, tr);
        }
    });
    let mut manual_sections = vec![];
    let mut section_start = None;
    for tag in manual_tags {
        match (section_start, tag) {
            (None, ManualTag::Begin(start_offset)) => section_start = Some(start_offset),
            (Some(start_offset), ManualTag::End(end_offset)) => {
                manual_sections.push((start_offset, end_offset));
                section_start = None;
            }
            // Malformed: multiple BEGIN tags in a row. Ignore the earlier.
            (Some(_), ManualTag::Begin(start_offset)) => section_start = Some(start_offset),
            // Malformed: an END tag with no BEGIN. Ignore it.
            (None, ManualTag::End(_)) => {}
        }
    }
    (fixmes, manual_sections)
}

/// `List.merge`: a stable merge of two sorted lists.
fn merge(a: &[Interval], b: &[Interval]) -> Vec<Interval> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        if interval::compare(a[i], b[j]) == std::cmp::Ordering::Greater {
            out.push(b[j]);
            j += 1;
        } else {
            out.push(a[i]);
            i += 1;
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// Return the start and end offsets of every range in which formatting is
/// suppressed, sorted by order of appearance in the file. Formatting is
/// suppressed around HH_FIXME/HH_IGNORE_ERROR comments, in generated sections
/// of partially-generated files, and in generated files.
pub fn get_suppressed_formatting_ranges(
    env: &Env,
    line_boundaries: &[Interval],
    tree: &SyntaxTree<'_>,
) -> Vec<Interval> {
    let text = tree.text;
    let (fixme_ranges, manual_sections) = get_fixme_ranges_and_manual_sections(&tree.root);
    let expand = |r: Interval| expand_to_line_boundaries(Some(line_boundaries), text, r);
    // Expand each range to contain the entire line the fixme is on, then add
    // one to the range end and expand again to include the next line, since
    // the fixme suppresses errors on both the line in which it appears and the
    // line following it.
    let fixme_ranges: Vec<Interval> = fixme_ranges
        .into_iter()
        .map(expand)
        .map(|(st, ed)| (st, ed + 1))
        .map(expand)
        .collect();
    if env.format_generated_code {
        interval::union_consecutive_overlapping(&fixme_ranges)
    } else {
        let whole_file = [(0, text.len() as isize)];
        let generated_sections = if is_generated_file(text) {
            whole_file.to_vec()
        } else if is_partially_generated_file(text) {
            interval::diff_sorted_lists(&whole_file, &manual_sections)
                .into_iter()
                .map(expand)
                .collect()
        } else {
            vec![]
        };
        interval::union_consecutive_overlapping(&merge(&fixme_ranges, &generated_sections))
    }
}
