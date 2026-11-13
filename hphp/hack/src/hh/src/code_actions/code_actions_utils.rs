// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Functions of OCaml modules that the code actions call and that are not
//! (yet) in the Rust modules of those names, which other assignments own
//! (no OCaml counterpart of its own; owned by **F7**):
//!
//! - `Full_fidelity_source_text.{sub_of_pos, offset_to_position}`;
//! - `Full_fidelity_positioned_syntax.{parentage, start_offset, end_offset,
//!   leading_start_position, start_position, text, leading_trivia}` over the
//!   Rust `PositionedSyntax`;
//! - `Server_rename_types.{compare_result, write_patches_to_buffer}` (F6's
//!   `server_rename_types.rs` has only the types).
//!
//! The owners may move them into their modules; the code actions then call
//! theirs.

use bstr::BString;
use parser_core_types::lexable_token::LexablePositionedToken;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::positioned_token::PositionedToken;
use parser_core_types::positioned_trivia::PositionedTrivium;
use parser_core_types::syntax_trait::SyntaxTrait;

use crate::full_fidelity_source_text as source_text;
use crate::pos::Pos;

/// `Full_fidelity_source_text.sub_of_pos source_text pos` (no `?length`)
pub fn sub_of_pos(st: &source_text::T, pos: &Pos) -> BString {
    let offset = {
        let (first_line, first_col) = crate::pos::line_column(pos);
        source_text::position_to_offset(st, (first_line, first_col + 1))
    };
    let length = crate::pos::length(pos);
    source_text::sub(st, offset, length)
}

/// `Full_fidelity_source_text.offset_to_position`: (line, column), both
/// one-based.
pub fn offset_to_position(st: &source_text::T, offset: isize) -> (isize, isize) {
    let indexed = parser_core_types::indexed_source_text::IndexedSourceText::new(
        source_text::source_text(st),
    );
    indexed.offset_to_position(offset)
}

/// Bytes to an OCaml string used as text (`String`): lossless for UTF-8.
pub fn to_string(b: BString) -> String {
    match String::from_utf8(b.into()) {
        Ok(s) => s,
        Err(e) => String::from_utf8_lossy(e.as_bytes()).into_owned(),
    }
}

/// `Full_fidelity_positioned_syntax.parentage node position`: the nodes
/// that contain the offset `position`, innermost first.
pub fn parentage(node: &PositionedSyntax, position: isize) -> Vec<&PositionedSyntax> {
    fn aux<'a>(
        nodes: impl Iterator<Item = &'a PositionedSyntax>,
        mut position: isize,
        acc: &mut Vec<&'a PositionedSyntax>,
    ) {
        for h in nodes {
            let width = h.full_width() as isize;
            if position < width {
                acc.push(h);
                return aux(h.iter_children(), position, acc);
            } else {
                position -= width
            }
        }
    }
    let mut acc = vec![];
    aux(std::iter::once(node), position, &mut acc);
    acc.reverse();
    acc
}

/// `start_offset node = leading_start_offset node + leading_width node`
pub fn start_offset(node: &PositionedSyntax) -> isize {
    (node.leading_start_offset() + node.leading_width()) as isize
}

/// `end_offset`: the offset of the last character (`start_offset` for an
/// empty node).
pub fn end_offset(node: &PositionedSyntax) -> isize {
    let w = node.width() as isize - 1;
    let w = if w < 0 { 0 } else { w };
    start_offset(node) + w
}

pub fn leading_start_offset(node: &PositionedSyntax) -> isize {
    node.leading_start_offset() as isize
}

/// `leading_start_position node`: (line, column), one-based.
pub fn leading_start_position(st: &source_text::T, node: &PositionedSyntax) -> (isize, isize) {
    offset_to_position(st, leading_start_offset(node))
}

/// `start_position node`: (line, column), one-based.
pub fn start_position(st: &source_text::T, node: &PositionedSyntax) -> (isize, isize) {
    offset_to_position(st, start_offset(node))
}

/// `text node`
pub fn text(st: &source_text::T, node: &PositionedSyntax) -> String {
    to_string(source_text::sub(st, start_offset(node), node.width() as isize))
}

/// `Syntax.leading_token node`
pub fn leading_token(node: &PositionedSyntax) -> Option<&PositionedToken> {
    node.leading_token()
}

/// `Syntax.trailing_token node`
pub fn trailing_token(node: &PositionedSyntax) -> Option<&PositionedToken> {
    node.trailing_token()
}

/// `Syntax.leading_trivia node`: the leading trivia of the leading token.
pub fn leading_trivia(node: &PositionedSyntax) -> &[PositionedTrivium] {
    match node.leading_token() {
        None => &[],
        Some(t) => t.positioned_leading(),
    }
}

/// `Token.offset`: the start of the leading trivia.
pub fn token_offset(t: &PositionedToken) -> isize {
    t.offset as isize
}

pub fn token_leading_width(t: &PositionedToken) -> isize {
    t.leading_width as isize
}

pub fn token_width(t: &PositionedToken) -> isize {
    t.width as isize
}

/// `Server_rename_types.patch` over relative positions (the cli library
/// patches the text with them; the OCaml converts to absolute positions,
/// which keep the same offsets).
#[derive(Clone, Debug)]
pub enum Patch {
    Insert { pos: Pos, text: String },
    Remove(Pos),
    Replace { pos: Pos, text: String },
}

/// `Server_rename_types.get_pos`
pub fn get_pos(p: &Patch) -> &Pos {
    match p {
        Patch::Insert { pos, .. } | Patch::Replace { pos, .. } => pos,
        Patch::Remove(p) => p,
    }
}

/// `Server_rename_types.compare_pos`
fn compare_pos(pos1: &Pos, pos2: &Pos) -> isize {
    let (char_start1, char_end1) = crate::pos::info_raw(pos1);
    let (char_start2, char_end2) = crate::pos::info_raw(pos2);
    if char_end1 <= char_start2 {
        -1
    } else if char_end2 <= char_start1 {
        1
    } else {
        0
    }
}

/// `Server_rename_types.compare_result`
pub fn compare_result(res1: &Patch, res2: &Patch) -> isize {
    compare_pos(get_pos(res1), get_pos(res2))
}

fn is_whitespace(c: u8) -> bool {
    matches!(c, b'\n' | b' ' | b'\x0c' | b'\r' | b'\t')
}

/// `Server_rename_types.write_patches_to_buffer`
pub fn write_patches_to_buffer(buf: &mut Vec<u8>, original_content: &[u8], patch_list: &[Patch]) {
    let len = original_content.len() as isize;
    let advance_skip_whitespaces = |mut i: isize| -> isize {
        while i < len && is_whitespace(original_content[i as usize]) {
            i += 1
        }
        i
    };
    // Takes the substring of original_content between `i` and `j`
    // and add it to the `buf` buffer.
    // Advance cursor `i` to `j`.
    let add_original_content = |buf: &mut Vec<u8>, i: isize, j: isize| -> isize {
        if j <= i {
            i
        } else {
            let size = j - i;
            let size = std::cmp::min(std::cmp::max(0, std::cmp::max(len - i, 0)), size);
            buf.extend_from_slice(&original_content[i as usize..(i + size) as usize]);
            i + size
        }
    };
    let mut i = 0;
    for patch in patch_list {
        let pos = get_pos(patch);
        let (char_start, char_end) = crate::pos::info_raw(pos);
        i = add_original_content(buf, i, char_start);
        i = match patch {
            Patch::Insert { text, .. } => {
                buf.extend_from_slice(text.as_bytes());
                i
            }
            Patch::Replace { text, .. } => {
                buf.extend_from_slice(text.as_bytes());
                char_end
            }
            Patch::Remove(_) => advance_skip_whitespaces(char_end),
        };
    }
    let _i = add_original_content(buf, i, len);
}

/// `List.sort ~compare` (a stable merge sort, as OCaml's) with an OCaml
/// comparison function.
pub fn list_sort<A>(v: Vec<A>, compare: impl Fn(&A, &A) -> isize) -> Vec<A> {
    crate::rt::ocaml_list::stable_sort(v, |a, b| compare(a, b).cmp(&0))
}

/// `apply_patches_to_string` of `Code_actions_cli_lib` and
/// `Classish_positions_cli_lib`
pub fn apply_patches_to_string(old_content: &[u8], patches: Vec<Patch>) -> Vec<u8> {
    let mut buf = Vec::with_capacity(old_content.len());
    let patches = list_sort(patches, compare_result);
    write_patches_to_buffer(&mut buf, old_content, &patches);
    buf
}
