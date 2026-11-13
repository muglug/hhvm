// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Pos` (`utils/pos.ml`). See `hh/PORTING.md`.
//!
//! The type is `oxidized::pos::Pos`, re-exported here with the rest of
//! `oxidized::pos`. This module has the functions of `pos.ml` that `oxidized`
//! lacks and that the port has needed so far.
//!
//! Where OCaml makes a `Pos_large` (`as_large_pos`), these functions go
//! through `Pos::to_raw_span` and `Pos::from_raw_span`: the result is the
//! same position, in its compressed representation. Like every accessor of
//! `oxidized::pos::Pos`, they do not support `Pos_from_reason`.

use oxidized::file_pos_large::FilePosLarge;
pub use oxidized::pos::*;
use oxidized::pos_span_raw::PosSpanRaw;

/// `File_pos_large.set_column`
fn set_column(c: isize, p: FilePosLarge) -> FilePosLarge {
    let (lnum, bol, _) = p.line_beg_offset();
    FilePosLarge::from_lnum_bol_offset(lnum, bol, (bol as isize + c) as usize)
}

/// `File_pos_large.line_column`
fn file_pos_line_column(p: FilePosLarge) -> (isize, isize) {
    let (lnum, bol, offset) = p.line_beg_offset();
    (lnum as isize, offset as isize - bol as isize)
}

/// The line (starting at 1) and the column (starting at 0) of the start.
pub fn line_column(p: &Pos) -> (isize, isize) {
    file_pos_line_column(p.to_raw_span().start)
}

/// The line (starting at 1) and the column (starting at 0) of the end.
pub fn end_line_column(p: &Pos) -> (isize, isize) {
    file_pos_line_column(p.to_raw_span().end)
}

/// `inside_one_based p line_one_based char_pos_one_based`
pub fn inside_one_based(p: &Pos, line_one_based: isize, char_pos_one_based: isize) -> bool {
    let (first_line, first_col) = line_column(p);
    let (last_line, last_col) = end_line_column(p);
    // `pos` has one-based line numbers, zero-based character numbers
    let line = line_one_based;
    let char_pos = char_pos_one_based - 1;
    if first_line == last_line {
        first_line == line && first_col <= char_pos && char_pos < last_col
    } else if line == first_line {
        first_col <= char_pos
    } else if line == last_line {
        char_pos < last_col
    } else {
        line > first_line && line < last_line
    }
}

pub fn set_col_start(pos_cnum: isize, pos: &Pos) -> Pos {
    let PosSpanRaw { start, end } = pos.to_raw_span();
    let start = set_column(pos_cnum, start);
    pos.with_raw_span(PosSpanRaw { start, end })
}

pub fn set_col_end(pos_cnum: isize, pos: &Pos) -> Pos {
    let PosSpanRaw { start, end } = pos.to_raw_span();
    let end = set_column(pos_cnum, end);
    pos.with_raw_span(PosSpanRaw { start, end })
}

pub fn shrink_to_start(pos: &Pos) -> Pos {
    let PosSpanRaw { start, end: _ } = pos.to_raw_span();
    pos.with_raw_span(PosSpanRaw { start, end: start })
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::Arc;

    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    /// `File "a.php", line <line>, characters <start>-<end>`, on a line that
    /// starts at offset `bol`.
    fn pos(line: usize, bol: usize, start: usize, end: usize) -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, PathBuf::from("a.php")));
        Pos::from_lnum_bol_offset(file, (line, bol, bol + start - 1), (line, bol, bol + end))
    }

    #[test]
    fn columns() {
        // Small enough for the tiny representation, and too large for it.
        for bol in [100, 1 << 40] {
            let p = pos(34, bol, 20, 30);
            assert_eq!(line_column(&p), (34, 19));
            assert_eq!(end_line_column(&p), (34, 30));
            // `$x->foo`: the `->` before characters 20-30.
            let arrow = set_col_end(19, &set_col_start(17, &p));
            assert_eq!(arrow, pos(34, bol, 18, 19));
            assert_eq!(arrow.info_pos(), (34, 18, 19));
            assert_eq!(arrow.filename(), p.filename());
            let start = shrink_to_start(&p);
            assert_eq!(start.info_raw(), (bol + 19, bol + 19));
            assert_eq!(line_column(&start), (34, 19));
            assert_eq!(end_line_column(&start), (34, 19));
        }
    }
}

// The other functions of `pos.ml` that the typechecker uses (`make_from`,
// `print_verbose_relative`, `to_absolute`, `btw`, `merge`...), the type
// `Absolute` and the modules `map` and `set`: see `pos/rest.rs`.
mod rest;
pub use rest::map;
pub use rest::*;
