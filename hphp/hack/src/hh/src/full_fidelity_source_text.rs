// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `parser/full_fidelity_source_text.ml` (the functions the
//! providers need). See `hh/PORTING.md`.
//!
//! The Rust parser has its own source text,
//! `parser_core_types::source_text::SourceText`, which borrows its text and
//! is not `Send`. `Full_fidelity_source_text.t` owns its text and is kept by
//! a `Provider_context.entry`, so it is this type, which owns its text
//! (shared, as OCaml shares a string) and gives the parser's view of it
//! ([`source_text`]). The line-break map (`offset_map`) is that of
//! `parser_core_types::indexed_source_text::IndexedSourceText`, made when it
//! is needed.

use std::sync::Arc;

use bstr::BString;
use oxidized::pos::Pos;
use parser_core_types::indexed_source_text::IndexedSourceText;
use relative_path::RelativePath;

/// `Full_fidelity_source_text.t`
#[derive(Clone, Debug)]
pub struct T {
    file_path: Arc<RelativePath>,
    /// `text` (and `length`, its length).
    text: Arc<[u8]>,
}

pub fn make(file_path: &RelativePath, content: &[u8]) -> T {
    T {
        file_path: Arc::new(file_path.clone()),
        text: Arc::from(content),
    }
}

pub fn empty() -> T {
    make(&crate::relative_path::default, b"")
}

pub fn file_path(source_text: &T) -> &RelativePath {
    &source_text.file_path
}

pub fn length(source_text: &T) -> isize {
    source_text.text.len() as isize
}

pub fn text(t: &T) -> &[u8] {
    &t.text
}

pub fn get(source_text: &T, index: isize) -> u8 {
    if index < length(source_text) {
        source_text.text[index as usize]
    } else {
        b'\x00'
    }
}

pub fn sub(source_text: &T, start: isize, length: isize) -> BString {
    let len = self::length(source_text);
    if start >= len {
        BString::from("")
    } else if start + length > len {
        BString::from(&source_text.text[start as usize..len as usize])
    } else {
        BString::from(&source_text.text[start as usize..(start + length) as usize])
    }
}

/// The text of the line `line_number` (one-based), without its newline;
/// empty if the line (or the start of the next one) is outside the file.
pub fn line_text(source_text: &T, line_number: isize) -> BString {
    let bolmap = line_break_map_make(&source_text.text);
    let len = bolmap.len() as isize;
    // `OffsetMap.position_to_offset (line, 1)`, `Not_found` outside the map
    let line_start = |line: isize| -> Option<isize> {
        if line - 1 >= 0 && line - 1 < len {
            Some(bolmap[(line - 1) as usize])
        } else {
            None
        }
    };
    match (line_start(line_number), line_start(line_number + 1)) {
        (Some(offset_start), Some(offset_end)) => {
            // Strip off the newline if one exists. If we're getting the very last line of the file, and
            // the very last line doesn't end in a newline, this won't be a \n char.
            let offset_end = if offset_end >= 1 && source_text.text.get((offset_end - 1) as usize) == Some(&b'\n') {
                offset_end - 1
            } else {
                offset_end
            };
            sub(source_text, offset_start, offset_end - offset_start)
        }
        // If the line was outside the boundaries of the file, just return a blank string
        _ => BString::from(""),
    }
}

/// Create a Pos.t from two offsets in a source_text (given a path)
pub fn relative_pos(
    pos_file: &RelativePath,
    source_text: &T,
    start_offset: isize,
    end_offset: isize,
) -> Pos {
    let indexed = IndexedSourceText::new(self::source_text(source_text));
    // `OffsetMap.offset_to_file_pos_triple`
    let pos = indexed.relative_pos(start_offset as usize, end_offset as usize);
    Pos::from_lnum_bol_offset(Arc::new(pos_file.clone()), pos.start, pos.end)
}

/// The Rust parser's view of `source_text`.
pub fn source_text(source_text: &T) -> parser_core_types::source_text::SourceText<'_> {
    parser_core_types::source_text::SourceText::make(
        Arc::clone(&source_text.file_path),
        &source_text.text,
    )
}

/// `Line_break_map.make` (the `offset_map` of a source text): the offset of
/// the beginning of each line, starting with 0 and ending with the length
/// of the text. (Added by F4.)
fn line_break_map_make(text: &[u8]) -> Vec<isize> {
    let len = text.len();
    let mut result: Vec<isize> = vec![0];
    for i in 1..=len {
        let prev = text[i - 1];
        if (prev == b'\r' && (i == len || text[i] != b'\n')) || prev == b'\n' {
            result.push(i as isize);
        }
    }
    if *result.last().unwrap() != len as isize {
        result.push(len as isize);
    }
    result
}

/// `Line_break_map.Position_not_found`: the payload of the panic that
/// raises it (nothing in the OCaml catches it but generic handlers).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PositionNotFound {
    pub line: isize,
    pub column: isize,
    pub num_lines_in_file: isize,
}

/// `position_to_offset source_text (line, column)` (`OffsetMap.position_to_offset`,
/// i.e. `Line_break_map.position_to_offset ~existing:false`): the offset of
/// a one-based line and column. (Added by F4.)
pub fn position_to_offset(source_text: &T, (line, column): (isize, isize)) -> isize {
    let bolmap = line_break_map_make(&source_text.text);
    let len = bolmap.len() as isize;
    // Treat all file_line errors the same: Not_found
    let line_start = if line - 1 >= 0 && line - 1 < len {
        bolmap[(line - 1) as usize]
    } else {
        std::panic::panic_any(PositionNotFound {
            line,
            column,
            num_lines_in_file: len,
        })
    };
    line_start + column - 1
}

#[cfg(test)]
mod tests {
    use relative_path::Prefix;

    use super::*;

    #[test]
    fn sub_and_get() {
        let path = RelativePath::make(Prefix::Root, "a.php".into());
        let st = make(&path, b"<?hh\nfunction f() {}\n");
        assert_eq!(length(&st), 21);
        assert_eq!(file_path(&st), &path);
        assert_eq!(get(&st, 0), b'<');
        assert_eq!(get(&st, 21), 0);
        assert_eq!(sub(&st, 5, 8), "function");
        assert_eq!(sub(&st, 19, 10), "}\n");
        assert_eq!(sub(&st, 30, 1), "");
        let pos = relative_pos(&path, &st, 14, 15);
        assert_eq!(pos.info_pos(), (2, 10, 10));
        assert_eq!(source_text(&st).text(), text(&st));
        assert_eq!(length(&empty()), 0);
    }
}
