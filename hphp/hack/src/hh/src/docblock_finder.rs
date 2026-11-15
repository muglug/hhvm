// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `parser/docblock_finder.ml`.
//!
//! This is a simple data structure that allows querying for the docblock
//! given a line in the source code. Rough description:
//!
//! 1. Find the last comment preceding the line of the definition.
//!    We also make sure this doesn't overlap with the preceding definition.
//!    If the last comment is more than 1 line away, it is ignored.
//!
//! 2. If the last comment is a block-style comment (/* */) just return it.
//!
//! 3. Otherwise (if it is a line style comment //) attempt to merge it with
//!    preceding line comments, if they exist.
//!      NOTE: We also enforce that line comments must be on the definition's
//!            immediately preceding line.
//!
//! The OCaml's positioned syntax carries its source text; here
//! [`get_docblock`] takes it as an argument.

use oxidized::pos::Pos;
use oxidized::prim_defs;
use parser_core_types::lexable_trivia::LexableTrivium;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::source_text::SourceText;
use parser_core_types::trivia_kind::TriviaKind;

use crate::pos;
use crate::string_utils;
use crate::utils;

/// line, string, is_line_comment
type Comment = (isize, String, bool);

/// `finder`
pub struct Finder {
    comments: Vec<Comment>,
}

/// `Prim_defs.string_of_comment`, `Prim_defs.is_line_comment`
fn comment_parts(cmt: &prim_defs::Comment) -> (&str, bool) {
    match cmt {
        prim_defs::Comment::CmtLine(s) => (s, true),
        prim_defs::Comment::CmtBlock(s) => (s, false),
    }
}

pub fn make_docblock_finder(comments: &[(Pos, prim_defs::Comment)]) -> Finder {
    // The Hack parser produces comments in reverse but sorted order.
    let comments = comments
        .iter()
        .rev()
        .map(|(pos, cmt)| {
            let (str, is_line_comment) = comment_parts(cmt);
            (pos::end_line(pos), str.to_string(), is_line_comment)
        })
        .collect();
    Finder { comments }
}

/// Merge all consecutive line comments preceding prev_line.
/// Stop when we reach last_line.
fn merge_line_comments(
    finder: &Finder,
    mut idx: isize,
    last_line: isize,
    mut prev_line: isize,
) -> Vec<String> {
    let mut acc = vec![];
    while idx >= 0 {
        let (line, str, is_line_comment) = &finder.comments[idx as usize];
        if *is_line_comment && *line > last_line && *line == prev_line - 1 {
            acc.push(format!("//{}", str));
            idx -= 1;
            prev_line = *line;
        } else {
            break;
        }
    }
    // `acc` was built by consing, i.e. in reverse.
    acc.reverse();
    acc
}

fn find_last_comment_index(finder: &Finder, line: isize) -> Option<usize> {
    utils::infimum(&finder.comments, &line, |(comment_line, _, _), line| {
        comment_line - line
    })
}

/// `Stdlib.String.trim`: drops ' ', '\012', '\n', '\r', '\t' at both ends.
pub(crate) fn stdlib_string_trim(s: &str) -> &str {
    s.trim_matches(|c| matches!(c, ' ' | '\x0c' | '\n' | '\r' | '\t'))
}

/// `Str.replace_first (Str.regexp "^/\\*\\(\\*?\\) *") ""`: the comment
/// starts with `/*` (or the match is at the start of a later line).
fn strip_open_multiline(s: &str) -> String {
    // `^` matches at the start of the string or after a '\n'.
    let starts = std::iter::once(0).chain(s.match_indices('\n').map(|(i, _)| i + 1));
    for start in starts {
        let rest = &s[start..];
        if let Some(after) = rest.strip_prefix("/*") {
            let after = after.strip_prefix('*').unwrap_or(after);
            let after = after.trim_start_matches(' ');
            let end = s.len() - after.len();
            return format!("{}{}", &s[..start], &s[end..]);
        }
    }
    s.to_string()
}

/// `Str.replace_first (Str.regexp " *\\*/$") ""`: the leftmost match, where
/// `$` is the end of the string or before a '\n'.
fn strip_close_multiline(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        // A match starts at `i`: spaces, then `*/`, then end of line.
        let mut j = i;
        while j < bytes.len() && bytes[j] == b' ' {
            j += 1;
        }
        if bytes[j..].starts_with(b"*/") && (j + 2 == bytes.len() || bytes[j + 2] == b'\n') {
            return format!("{}{}", &s[..i], &s[j + 2..]);
        }
        i += 1;
    }
    s.to_string()
}

/// Tidies up a delimited comment.
///
/// 1. Strip the leading `/*` and trailing `*/`.
/// 2. Remove leading whitespace equal to the least amount of whitespace
///    before any comment lines after the first (since the first line is on
///    the same line as the opening `/*`, it will almost always have only a
///    single leading space).
///
///    We remove leading whitespace equal to the least amount rather than
///    removing all leading whitespace in order to preserve manual indentation
///    of text in the doc block.
///
/// 3. Remove leading `*` characters to properly handle box-style multiline
///    doc blocks. Without this they would be formatted as Markdown lists.
///
/// Known failure cases:
///   1. A doc block which is legitimately just a list of items will need at
///      least one non-list item which is under-indented compared to the list in
///      order to not strip all of the whitespace from the list items. The
///      easiest way to do this is to write a little one line summary before the
///      list and place it on its own line instead of directly after the `/*`.
fn tidy_delimited_comment(comment: &str) -> String {
    let comment = strip_close_multiline(&strip_open_multiline(comment));
    let lines = string_utils::split_into_lines(&comment);
    let trimmed: Vec<String> = match lines.as_slice() {
        [] | [_] => lines.iter().map(|l| stdlib_string_trim(l).to_string()).collect(),
        [_hd, tail @ ..] => {
            // `String_utils.index_not_opt x " "`
            let counts = tail.iter().filter_map(|x| x.find(|c| c != ' '));
            let min = counts.min().unwrap_or(0);
            let prefix = " ".repeat(min);
            // `Str.replace_first (Str.regexp "^<min spaces>\\(\\* ?\\)?") ""`:
            // the lines have no '\n', so `^` is the start of the line.
            lines
                .iter()
                .map(|line| match line.strip_prefix(prefix.as_str()) {
                    Some(rest) => match rest.strip_prefix('*') {
                        Some(rest) => rest.strip_prefix(' ').unwrap_or(rest).to_string(),
                        None => rest.to_string(),
                    },
                    None => line.clone(),
                })
                .collect()
        }
    };
    trimmed.join("\n")
}

pub fn find_docblock(finder: &Finder, last_line: isize, line: isize) -> Option<String> {
    match find_last_comment_index(finder, line) {
        Some(comment_index) => {
            let (comment_line, str, is_line_comment) = &finder.comments[comment_index];
            if *is_line_comment {
                match merge_line_comments(finder, comment_index as isize, last_line, line).as_slice() {
                    [] => None,
                    lines => Some(stdlib_string_trim(&lines.concat()).to_string()),
                }
            } else if *comment_line > last_line && *comment_line >= line - 2 {
                Some(format!("/*{}*/", str))
            } else {
                None
            }
        }
        None => None,
    }
}

/// Find the last comment on `line` if it exists.
pub fn find_inline_comment(finder: &Finder, line: isize) -> Option<String> {
    match find_last_comment_index(finder, line + 1) {
        Some(last_comment_index) => {
            let (comment_line, str, is_line_comment) = &finder.comments[last_comment_index];
            if *comment_line == line {
                if *is_line_comment {
                    Some(stdlib_string_trim(&format!("//{}", str)).to_string())
                } else {
                    Some(format!("/*{}*/", str))
                }
            } else {
                None
            }
        }
        None => None,
    }
}

/// `Str.replace_first (Str.regexp "^\\(//\\|#\\) ?") ""` on one comment
/// (a single-line comment has no '\n').
fn strip_line_comment_prefix(s: &str) -> &str {
    let rest = if let Some(rest) = s.strip_prefix("//") {
        rest
    } else if let Some(rest) = s.strip_prefix('#') {
        rest
    } else {
        return s;
    };
    rest.strip_prefix(' ').unwrap_or(rest)
}

/// `Syntax.leading_trivia node`: the leading trivia of the node's first token.
fn leading_trivia(node: &PositionedSyntax) -> &[parser_core_types::positioned_trivia::PositionedTrivium] {
    match node.leading_token() {
        Some(token) => &token.leading,
        None => &[],
    }
}

fn trivium_text(source_text: &SourceText<'_>, t: &parser_core_types::positioned_trivia::PositionedTrivium) -> String {
    String::from_utf8_lossy(source_text.sub(t.offset, t.width())).into_owned()
}

/// Extract a // comment docblock that is directly before this node.
///
/// ```text
///     // A function.
///     // It is useful.
///     function foo(): void {}
/// ```
///
/// In this example, we return "A function.\nIt is useful."
pub fn get_single_lines_docblock(source_text: &SourceText<'_>, node: &PositionedSyntax) -> Option<String> {
    let mut acc: Vec<String> = vec![];
    let mut seen_newline = false;
    for hd in leading_trivia(node).iter().rev() {
        match hd.kind() {
            TriviaKind::SingleLineComment => {
                acc.push(trivium_text(source_text, hd));
                seen_newline = false;
            }
            // Step over whitespace.
            TriviaKind::WhiteSpace => {}
            TriviaKind::EndOfLine => {
                // Stop if we've seen consecutive newlines, as that means
                // we've reached a blank line.
                if seen_newline {
                    break;
                }
                seen_newline = true;
            }
            // Step over HH_FIXME comments.
            TriviaKind::FixMe | TriviaKind::Ignore | TriviaKind::IgnoreError => seen_newline = false,
            // Stop if we see a /* ... */ comment, a FALLTHROUGH
            // comment, or a syntax error.
            TriviaKind::DelimitedComment | TriviaKind::FallThrough | TriviaKind::ExtraTokenError => break,
        }
    }
    // `acc` was built by consing over the reversed trivia: it is in source order.
    acc.reverse();
    match acc.as_slice() {
        [] => None,
        comment_lines => {
            let joined = comment_lines
                .iter()
                .map(|l| strip_line_comment_prefix(l))
                .collect::<Vec<_>>()
                .join("\n");
            Some(stdlib_string_trim(&joined).to_string())
        }
    }
}

/// Extract a /* ... */ comment docblock that is before this node,
/// even if there are blank lines present.
pub fn get_delimited_docblock(source_text: &SourceText<'_>, node: &PositionedSyntax) -> Option<String> {
    for hd in leading_trivia(node).iter().rev() {
        match hd.kind() {
            // We've found the comment.
            TriviaKind::DelimitedComment => {
                return Some(tidy_delimited_comment(&trivium_text(source_text, hd)));
            }
            // Step over whitespace and HH_FIXME comments.
            TriviaKind::WhiteSpace
            | TriviaKind::EndOfLine
            | TriviaKind::FixMe
            | TriviaKind::Ignore
            | TriviaKind::IgnoreError => {}
            // Give up if we have a // comment.
            TriviaKind::SingleLineComment => return None,
            // Give up if we have a // FALLTHROUGH comment or syntax error.
            TriviaKind::FallThrough | TriviaKind::ExtraTokenError => return None,
        }
    }
    None
}

/// Returns the docblock for the passed in syntax node.
pub fn get_docblock(source_text: &SourceText<'_>, node: &PositionedSyntax) -> Option<String> {
    get_single_lines_docblock(source_text, node).or_else(|| get_delimited_docblock(source_text, node))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tidy() {
        assert_eq!(tidy_delimited_comment("/** Hello */"), "Hello");
        assert_eq!(
            tidy_delimited_comment("/**\n   * Line one\n   *   indented\n   */"),
            "\nLine one\n  indented\n"
        );
        assert_eq!(tidy_delimited_comment("/* a\n  b\n    c */"), "a\nb\n  c");
    }

    #[test]
    fn line_prefix() {
        assert_eq!(strip_line_comment_prefix("// foo"), "foo");
        assert_eq!(strip_line_comment_prefix("#foo"), "foo");
        assert_eq!(strip_line_comment_prefix("//  foo"), " foo");
    }
}
