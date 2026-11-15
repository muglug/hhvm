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
//! ([`source_text`]). The line-break map (`offset_map`) is that of the OCaml
//! for the functions that the OCaml writes with `OffsetMap`, except
//! `relative_pos`, which uses that of
//! `parser_core_types::indexed_source_text::IndexedSourceText`.

use std::sync::Arc;
use std::sync::OnceLock;

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
    /// `offset_map` (see [`offset_map`]). The OCaml makes it in `make`, for
    /// every source text; here it is made the first time it is needed
    /// (most source texts, those of the files that a check parses, never
    /// need it), then shared by the clones.
    offset_map: Arc<OnceLock<Vec<isize>>>,
}

/// create a new source_text.t with a path and contents
pub fn make(file_path: &RelativePath, content: &[u8]) -> T {
    T {
        file_path: Arc::new(file_path.clone()),
        text: Arc::from(content),
        offset_map: Arc::new(OnceLock::new()),
    }
}

/// empty source_text.t located nowhere
pub fn empty() -> T {
    make(&crate::relative_path::DEFAULT, b"")
}

/// get the relative path
pub fn file_path(source_text: &T) -> &RelativePath {
    &source_text.file_path
}

/// get the length of the contents
pub fn length(source_text: &T) -> isize {
    source_text.text.len() as isize
}

/// get the contents as a string
pub fn text(t: &T) -> &[u8] {
    &t.text
}

/// get the ith character
pub fn get(source_text: &T, index: isize) -> u8 {
    if index < length(source_text) {
        source_text.text[index as usize]
    } else {
        b'\x00'
    }
}

/// `Invalid_argument "String.sub / Bytes.sub"`: the payload of the panic
/// with which [`sub`] raises it (a negative start or length).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StringSubInvalidArgument;

/// get a substring start at the ith char and continuing for length
pub fn sub(source_text: &T, start: isize, length: isize) -> BString {
    let len = self::length(source_text);
    if start >= len {
        BString::from("")
    } else if start + length > len {
        if start < 0 {
            std::panic::panic_any(StringSubInvalidArgument)
        }
        BString::from(&source_text.text[start as usize..len as usize])
    } else {
        if start < 0 || length < 0 {
            std::panic::panic_any(StringSubInvalidArgument)
        }
        BString::from(&source_text.text[start as usize..(start + length) as usize])
    }
}

/// get just one line as a string
///
/// The text of the line `line_number` (one-based), without its newline;
/// empty if the line (or the start of the next one) is outside the file.
pub fn line_text(source_text: &T, line_number: isize) -> BString {
    let bolmap = offset_map(source_text);
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

/// `offset_map` (the field: `Line_break_map.make text`): the offset of the
/// beginning of each line, starting with 0, and the length of the text at
/// the end unless the text has no line break at all (then only `[0]`: the
/// OCaml adds the length only after the last line break it found).
pub fn offset_map(source_text: &T) -> &[isize] {
    source_text.offset_map.get_or_init(|| line_break_map_make(&source_text.text))
}

/// `Line_break_map.make`
fn line_break_map_make(text: &[u8]) -> Vec<isize> {
    let len = text.len();
    let mut result: Vec<isize> = vec![];
    for i in 1..=len {
        let prev = text[i - 1];
        if (prev == b'\r' && (i == len || text[i] != b'\n')) || prev == b'\n' {
            result.push(i as isize);
        }
    }
    match result.last() {
        Some(r) if *r != len as isize => result.push(len as isize),
        _ => {}
    }
    result.insert(0, 0);
    result
}

/// `Line_break_map.offsets_to_line_lengths`: the length of each line of an
/// [`offset_map`] (one fewer than its offsets).
pub fn offsets_to_line_lengths(bolmap: &[isize]) -> Vec<isize> {
    bolmap.windows(2).map(|w| w[1] - w[0]).collect()
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
/// a one-based line and column.
pub fn position_to_offset(source_text: &T, (line, column): (isize, isize)) -> isize {
    let bolmap = offset_map(source_text);
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

    #[test]
    fn offset_map_of_the_ocaml() {
        let path = RelativePath::make(Prefix::Root, "a.php".into());
        // No line break: `[0]`, so line 1 has no end and line 2 no start.
        let one = make(&path, b"<?hh");
        assert_eq!(offset_map(&one), &[0]);
        assert_eq!(line_text(&one, 1), "");
        assert_eq!(position_to_offset(&one, (1, 3)), 2);
        let not_found = std::panic::catch_unwind(|| position_to_offset(&one, (2, 1)));
        assert_eq!(
            not_found.unwrap_err().downcast_ref::<PositionNotFound>(),
            Some(&PositionNotFound { line: 2, column: 1, num_lines_in_file: 1 })
        );
        // The length is added after the last line break.
        let two = make(&path, b"<?hh\r\nf();");
        assert_eq!(offset_map(&two), &[0, 6, 10]);
        assert_eq!(line_text(&two, 1), "<?hh\r");
        assert_eq!(line_text(&two, 2), "f();");
        assert_eq!(line_text(&two, 3), "");
        assert_eq!(offset_map(&make(&path, b"a\nb\n")), &[0, 2, 4]);
    }
}
