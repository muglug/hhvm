// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The functions of `Pos` (`utils/pos.ml`) that are not in `pos.rs`: all the
//! ones the typechecker uses. `pos.rs` re-exports them, so they are
//! `crate::pos::<name>`.
//!
//! # How this differs from `pos.ml`
//!
//! - `oxidized::pos::Pos` always holds a position in its compressed form
//!   (`Pos.compress`), and there is no way to make another one. Where OCaml
//!   returns a `Pos_large` that is not compressed (`shrink_to_end`,
//!   `advance_one` of a `Pos_large`...), these functions return the same
//!   position, compressed. Line, column and offset are the same.
//! - `Pos_from_reason` cannot be made (so there is no `set_from_reason`), and
//!   the accessors of `oxidized::pos::Pos` do not support it.
//! - `'a pos` is `Pos` (`Relative_path.t pos`) or [`Absolute`] (`string
//!   pos`). The functions that OCaml has for any `'a pos` and that only read
//!   the position take either ([`APos`]); the ones that build a position take
//!   a `Pos`.
//! - Integers are `isize`, as in OCaml: the offset and the column of the
//!   dummy position are -1 (`oxidized` has `usize::MAX`).

#![allow(non_upper_case_globals)]

use std::cmp::Ordering;
use std::sync::Arc;

use oxidized::file_pos_large::FilePosLarge;
use oxidized::pos::Pos;
use oxidized::pos_span_raw::PosSpanRaw;

use crate::relative_path;
use crate::relative_path::Prefix;
use crate::relative_path::RelativePath;
use crate::yojson::safe as yojson;

pub type T = Pos;

/// `Pos.absolute`: a position in a file given by its path (`string pos`).
#[derive(Clone, Debug)]
pub struct Absolute {
    pos_file: String,
    pos_start: FilePosLarge,
    pos_end: FilePosLarge,
}

/// `'a pos`, for the functions that only read a position.
pub trait APos {
    /// `'a`
    type File;

    fn pos_file(&self) -> Self::File;

    /// `pos_start` and `pos_end` (`as_large_pos`).
    fn raw_span(&self) -> PosSpanRaw;
}

impl APos for Pos {
    type File = RelativePath;

    fn pos_file(&self) -> RelativePath {
        self.filename().clone()
    }

    fn raw_span(&self) -> PosSpanRaw {
        self.to_raw_span()
    }
}

impl APos for Absolute {
    type File = String;

    fn pos_file(&self) -> String {
        self.pos_file.clone()
    }

    fn raw_span(&self) -> PosSpanRaw {
        PosSpanRaw {
            start: self.pos_start,
            end: self.pos_end,
        }
    }
}

pub const none: Pos = Pos::NONE;

/// `File_pos_large.line_beg_offset`
fn file_pos_line_beg_offset(p: FilePosLarge) -> (isize, isize, isize) {
    let (lnum, bol, offset) = p.line_beg_offset();
    (lnum as isize, bol as isize, offset as isize)
}

/// `File_pos_large.of_lnum_bol_offset`
fn file_pos_of_lnum_bol_offset((lnum, bol, offset): (isize, isize, isize)) -> FilePosLarge {
    FilePosLarge::from_lnum_bol_offset(lnum as usize, bol as usize, offset as usize)
}

/// `File_pos_large.column`: the column of `File_pos_large.line_column`, which
/// is in `pos.rs`.
fn file_pos_column(p: FilePosLarge) -> isize {
    super::file_pos_line_column(p).1
}

/// `File_pos_large.set_column`, which is in `pos.rs`.
fn file_pos_set_column(c: isize, p: FilePosLarge) -> FilePosLarge {
    super::set_column(c, p)
}

/// `File_pos_large.pp`
fn file_pos_pp(fmt: &mut dyn std::fmt::Write, p: FilePosLarge) -> std::fmt::Result {
    let (lnum, bol, offset) = file_pos_line_beg_offset(p);
    write!(fmt, "{}:{}", lnum, offset - bol + 1)
}

/// The position in the same file with this span, compressed.
fn with_span(pos: &Pos, start: FilePosLarge, end: FilePosLarge) -> Pos {
    pos.with_raw_span(PosSpanRaw { start, end })
}

pub fn pp(fmt: &mut dyn std::fmt::Write, pos: &Pos) -> std::fmt::Result {
    // `equal pos none`
    if pos.is_none() {
        fmt.write_str("[Pos.none]")
    } else {
        let PosSpanRaw { start, end } = pos.to_raw_span();
        fmt.write_str("[")?;
        file_pos_pp(fmt, start)?;
        fmt.write_str("-")?;
        if start.line() == end.line() {
            write!(fmt, "{}", file_pos_column(end) + 1)?
        } else {
            file_pos_pp(fmt, end)?
        }
        fmt.write_str("]")
    }
}

pub fn filename<P: APos>(p: &P) -> P::File {
    p.pos_file()
}

/// This returns `(line, start_column, end_column)`.
/// `start_column` and `end_column` form a closed interval that's incorrect
/// for multi-line spans. For compatibility with IDE positions, the column
/// numbers are one-based.
pub fn info_pos<P: APos>(p: &P) -> (isize, isize, isize) {
    let PosSpanRaw {
        start: pos_start,
        end: pos_end,
    } = p.raw_span();
    let (line, bol, start_offset) = file_pos_line_beg_offset(pos_start);
    let start = start_offset - bol;
    let (_, _, end_offset) = file_pos_line_beg_offset(pos_end);
    let end_ = end_offset - bol;
    // We do `start = start + 1` to convert from zero-based to one-based.
    // For `end_`, we'd do `+ 1` to convert from zero-based to one-based,
    // but then `- 1` to make the interval closed, so there's no need to do
    // anything
    let start = start + 1;
    // To represent the empty interval, pos_start and pos_end are equal because
    // end_offset is exclusive. Here, it's best for error messages to the user
    // if we print characters N to N (highlighting a single character) rather
    // than characters N to (N-1), which is very unintuitive.
    let end_ = if start == end_ + 1 { start } else { end_ };
    (line, start, end_)
}

/// Return start line, end line, start column and end column.
/// This returns a closed interval.
pub fn info_pos_extended<P: APos>(p: &P) -> (isize, isize, isize, isize) {
    let (line_begin, start, end_) = info_pos(p);
    let line_end = p.raw_span().end.line() as isize;
    (line_begin, line_end, start, end_)
}

/// Return start character number and end character number.
pub fn info_raw<P: APos>(p: &P) -> (isize, isize) {
    (start_offset(p), end_offset(p))
}

pub fn length<P: APos>(p: &P) -> isize {
    end_offset(p) - start_offset(p)
}

pub fn start_offset<P: APos>(p: &P) -> isize {
    file_pos_line_beg_offset(p.raw_span().start).2
}

pub fn end_offset<P: APos>(p: &P) -> isize {
    file_pos_line_beg_offset(p.raw_span().end).2
}

pub fn line<P: APos>(p: &P) -> isize {
    p.raw_span().start.line() as isize
}

pub fn end_line<P: APos>(p: &P) -> isize {
    p.raw_span().end.line() as isize
}

/// `Printf`'s `%S`: the string as an OCaml string literal
/// (`String.escaped`, in double quotes).
#[allow(non_snake_case)]
fn sprintf_S(s: &str) -> String {
    let mut res = String::with_capacity(s.len() + 2);
    res.push('"');
    for c in s.bytes() {
        match c {
            b'"' => res.push_str("\\\""),
            b'\\' => res.push_str("\\\\"),
            b'\n' => res.push_str("\\n"),
            b'\t' => res.push_str("\\t"),
            b'\r' => res.push_str("\\r"),
            0x08 => res.push_str("\\b"),
            b' '..=b'~' => res.push(c as char),
            _ => res.push_str(&format!("\\{:03}", c)),
        }
    }
    res.push('"');
    res
}

/// This returns a closed interval.
pub fn string(t: &Absolute) -> String {
    let (line, start, end_) = info_pos(t);
    let path = filename(t);

    // .hhi path hasn't been set (e.g. when running tests).
    let hhi_path = relative_path::path_of_prefix(Prefix::Hhi).unwrap_or_default();
    // Strip temporary .hhi directories from the path shown.
    let path = match path.strip_prefix(&hhi_path) {
        Some(file_path) => file_path,
        None => &path,
    };
    format!(
        "File {}, line {}, characters {}-{}:",
        sprintf_S(path),
        line,
        start,
        end_
    )
}

/// Some positions, like those in buffers sent by IDE/created by unit tests
/// might not have a file specified.
/// This returns a closed interval.
pub fn string_no_file<P: APos>(t: &P) -> String {
    let (line, start, end_) = info_pos(t);
    format!("line {}, characters {}-{}", line, start, end_)
}

/// This returns a closed interval.
pub fn json(pos: &Absolute) -> yojson::T {
    let (line, start, end_) = info_pos(pos);
    let fn_ = filename(pos);
    yojson::T::Assoc(vec![
        ("filename".to_string(), yojson::T::String(fn_)),
        ("line".to_string(), yojson::T::Int(line)),
        ("char_start".to_string(), yojson::T::Int(start)),
        ("char_end".to_string(), yojson::T::Int(end_)),
    ])
}

/// `line_column` and `end_line_column` (in `pos.rs`, for a `Pos`), for any
/// `'a pos`.
fn line_column_of<P: APos>(p: &P) -> ((isize, isize), (isize, isize)) {
    let PosSpanRaw { start, end } = p.raw_span();
    (
        super::file_pos_line_column(start),
        super::file_pos_line_column(end),
    )
}

pub fn contains(pos_container: &Pos, pos: &Pos) -> bool {
    let (cstart, cend) = info_raw(pos_container);
    let (pstart, pend) = info_raw(pos);
    pos_container.filename() == pos.filename() && pstart >= cstart && pend <= cend
}

/// Does first position strictly overlap the second position?
pub fn overlaps(pos1: &Pos, pos2: &Pos) -> bool {
    let (start1, end1) = info_raw(pos1);
    let (start2, end2) = info_raw(pos2);
    pos1.filename() == pos2.filename() && end1 > start2 && start1 < end2
}

/// `pos = Pos.none`, as `Pos.equal` (`*pos == Pos::NONE`) computes it, but
/// looking at the prefix of the file first: positions whose file is of
/// another prefix are not equal to it, which the comparison of `oxidized`
/// (`Ordering::then`, eager) only finds out after comparing the paths.
pub fn equal_none(pos: &Pos) -> bool {
    pos.filename().prefix() == Pos::NONE.filename().prefix() && *pos == Pos::NONE
}

pub fn is_hhi(pos: &Pos) -> bool {
    relative_path::is_hhi(pos.filename().prefix())
}

pub fn make_from(file: RelativePath) -> Pos {
    Pos::from_raw_span(Arc::new(file), PosSpanRaw::make_dummy())
}

pub fn btw_nocheck(x1: &Pos, x2: &Pos) -> Pos {
    with_span(x1, x1.to_raw_span().start, x2.to_raw_span().end)
}

pub fn to_absolute(p: &Pos) -> Absolute {
    let PosSpanRaw { start, end } = p.to_raw_span();
    Absolute {
        pos_file: relative_path::to_absolute(p.filename()),
        pos_start: start,
        pos_end: end,
    }
}

/// The `Pos.absolute` of a file and a span (for `Server_progress`, which
/// reads absolute positions back from the errors file).
pub fn make_absolute(pos_file: String, pos_start: FilePosLarge, pos_end: FilePosLarge) -> Absolute {
    Absolute {
        pos_file,
        pos_start,
        pos_end,
    }
}

pub fn to_relative(p: &Absolute) -> Pos {
    Pos::from_raw_span(
        Arc::new(relative_path::create_detect_prefix(&p.pos_file)),
        p.raw_span(),
    )
}

/// Fill in the gap "between" first position and second position.
/// Not valid if from different files or second position precedes first
pub fn btw(x1: &Pos, x2: &Pos) -> Pos {
    // (The files are interned: the same file is usually the same object.)
    if !std::ptr::eq(x1.filename(), x2.filename()) && x1.filename() != x2.filename() {
        panic!("Position in separate files");
    }
    if end_offset(x1) > end_offset(x2) {
        panic!(
            "btw: invalid positions {} and {}",
            string(&to_absolute(x1)),
            string(&to_absolute(x2))
        );
    }
    btw_nocheck(x1, x2)
}

/// Symmetric version of above: order doesn't matter
pub fn merge(x1: &Pos, x2: &Pos) -> Pos {
    Pos::merge_without_checking_filename(x1, x2)
}

/// [`merge`] for an [`Absolute`] (`merge : 'a pos -> 'a pos -> 'a pos`):
/// the file of `x1`, the first start and the last end, a dummy start or end
/// giving way to the other one.
pub fn merge_absolute(x1: &Absolute, x2: &Absolute) -> Absolute {
    let pos_start = if x1.pos_start.is_dummy() {
        x2.pos_start
    } else if x2.pos_start.is_dummy() {
        x1.pos_start
    } else if start_offset(x1) < start_offset(x2) {
        x1.pos_start
    } else {
        x2.pos_start
    };
    let pos_end = if x1.pos_end.is_dummy() {
        x2.pos_end
    } else if x2.pos_end.is_dummy() {
        x1.pos_end
    } else if end_offset(x1) < end_offset(x2) {
        x2.pos_end
    } else {
        x1.pos_end
    };
    Absolute {
        pos_file: x1.pos_file.clone(),
        pos_start,
        pos_end,
    }
}

/// `line_column` (in `pos.rs`, for a `Pos`) for an [`Absolute`]: the line
/// (starting at 1) and the column (starting at 0) of the start.
pub fn line_column_absolute(p: &Absolute) -> (isize, isize) {
    line_column_of(p).0
}

/// `end_line_column` (in `pos.rs`, for a `Pos`) for an [`Absolute`].
pub fn end_line_column_absolute(p: &Absolute) -> (isize, isize) {
    line_column_of(p).1
}

pub fn to_relative_string(p: &Pos) -> Absolute {
    let PosSpanRaw { start, end } = p.to_raw_span();
    Absolute {
        pos_file: relative_path::suffix(p.filename()),
        pos_start: start,
        pos_end: end,
    }
}

/// (`String.sub`: the bytes of `content` from the start offset to the end
/// offset. It raises when they are not in `content`.)
pub fn get_text_from_pos<P: APos>(content: &str, pos: &P) -> String {
    let pos_length = length(pos);
    let offset = start_offset(pos);
    if offset < 0 || pos_length < 0 || (offset + pos_length) as usize > content.len() {
        panic!(
            "Invalid_argument: pos + len past end: {} + {} > {}",
            offset,
            pos_length,
            content.len()
        );
    }
    content[offset as usize..(offset + pos_length) as usize].to_string()
}

/// Compare by filename, then tie-break by start position, and finally by the
/// end position
pub fn compare_pos<P: APos>(
    compare_files: impl Fn(&P::File, &P::File) -> Ordering,
    x: &P,
    y: &P,
) -> Ordering {
    let r = compare_files(&filename(x), &filename(y));
    if r != Ordering::Equal {
        r
    } else {
        let (xstart, xend) = info_raw(x);
        let (ystart, yend) = info_raw(y);
        let r = xstart.cmp(&ystart);
        if r != Ordering::Equal {
            r
        } else {
            xend.cmp(&yend)
        }
    }
}

pub fn compare(x: &Pos, y: &Pos) -> Ordering {
    compare_pos(relative_path::compare, x, y)
}

pub fn compare_absolute(x: &Absolute, y: &Absolute) -> Ordering {
    // `String.compare`: by bytes.
    compare_pos(|a: &String, b: &String| a.as_bytes().cmp(b.as_bytes()), x, y)
}

/// The same span in another file. (For a `'a pos` whose file is not a
/// `Relative_path.t`, use `to_absolute` or `to_relative_string`.)
pub fn set_file<P: APos>(pos_file: RelativePath, pos: &P) -> Pos {
    Pos::from_raw_span(Arc::new(pos_file), pos.raw_span())
}

/// The same file and the same start and end: line, beginning of line and
/// offset.
pub fn equal(x: &Pos, y: &Pos) -> bool {
    x.filename() == y.filename() && x.to_raw_span() == y.to_raw_span()
}

pub fn equal_absolute(x: &Absolute, y: &Absolute) -> bool {
    x.pos_file == y.pos_file && x.raw_span() == y.raw_span()
}

impl PartialEq for Absolute {
    fn eq(&self, other: &Self) -> bool {
        compare_absolute(self, other) == Ordering::Equal
    }
}

impl Eq for Absolute {}

impl PartialOrd for Absolute {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// `compare_absolute`, like `AbsolutePosMap`.
impl Ord for Absolute {
    fn cmp(&self, other: &Self) -> Ordering {
        compare_absolute(self, other)
    }
}

/// Return start line, start column, end line and end column, as 1-based
/// indices. This returns a half-open interval.
pub fn destruct_range_one_based<P: APos>(p: &P) -> (isize, isize, isize, isize) {
    let ((line_start, col_start_minus1), (line_end, col_end_minus1)) = line_column_of(p);
    (
        line_start,
        col_start_minus1 + 1,
        line_end,
        col_end_minus1 + 1,
    )
}

/// Advance the ending position by one character
pub fn advance_one(p: &Pos) -> Pos {
    let PosSpanRaw { start, end } = p.to_raw_span();
    let end_column = file_pos_column(end);
    with_span(p, start, file_pos_set_column(end_column + 1, end))
}

/// This function is used when we have captured a position that includes
/// outside boundary characters like apostrophes.  If we need to remove these
/// apostrophes, this function shrinks by one character in each direction.
pub fn shrink_by_one_char_both_sides(p: &Pos) -> Pos {
    let PosSpanRaw { start, end } = p.to_raw_span();
    let new_pos_start = file_pos_set_column(file_pos_column(start) + 1, start);
    let new_pos_end = file_pos_set_column(file_pos_column(end) - 1, end);
    with_span(p, new_pos_start, new_pos_end)
}

/// `Base.String.strip`
fn strip(s: &str) -> &str {
    s.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\u{b}' | '\u{c}' | '\r'))
}

/// This returns a half-open interval.
pub fn multiline_string(t: &Absolute) -> String {
    let (line_start, char_start, line_end, char_end) = destruct_range_one_based(t);
    format!(
        "File {}, line {}, character {} - line {}, character {}:",
        sprintf_S(strip(&filename(t))),
        line_start,
        char_start,
        line_end,
        char_end - 1
    )
}

/// This returns a half-open interval.
pub fn multiline_string_no_file<P: APos>(t: &P) -> String {
    let (line_start, char_start, line_end, char_end) = destruct_range_one_based(t);
    format!(
        "line {}, character {} - line {}, character {}",
        line_start,
        char_start,
        line_end,
        char_end - 1
    )
}

/// This returns a half-open interval.
pub fn multiline_json(t: &Absolute) -> yojson::T {
    let (line_start, char_start, line_end, char_end) = destruct_range_one_based(t);
    let fn_ = filename(t);
    yojson::T::Assoc(vec![
        ("filename".to_string(), yojson::T::String(fn_)),
        ("line_start".to_string(), yojson::T::Int(line_start)),
        ("char_start".to_string(), yojson::T::Int(char_start)),
        ("line_end".to_string(), yojson::T::Int(line_end)),
        ("char_end".to_string(), yojson::T::Int(char_end - 1)),
    ])
}

pub fn multiline_json_no_filename<P: APos>(t: &P) -> yojson::T {
    let (line_start, char_start, line_end, char_end) = destruct_range_one_based(t);
    yojson::T::Assoc(vec![
        ("line_start".to_string(), yojson::T::Int(line_start)),
        ("char_start".to_string(), yojson::T::Int(char_start)),
        ("line_end".to_string(), yojson::T::Int(line_end)),
        ("char_end".to_string(), yojson::T::Int(char_end - 1)),
    ])
}

/// Return line number, beginning of line character number and character
/// number of start position.
pub fn line_beg_offset<P: APos>(p: &P) -> (isize, isize, isize) {
    file_pos_line_beg_offset(p.raw_span().start)
}

pub fn end_line_beg_offset<P: APos>(p: &P) -> (isize, isize, isize) {
    file_pos_line_beg_offset(p.raw_span().end)
}

pub fn make_from_lnum_bol_offset(
    pos_file: RelativePath,
    pos_start: (isize, isize, isize),
    pos_end: (isize, isize, isize),
) -> Pos {
    Pos::from_raw_span(
        Arc::new(pos_file),
        PosSpanRaw {
            start: file_pos_of_lnum_bol_offset(pos_start),
            end: file_pos_of_lnum_bol_offset(pos_end),
        },
    )
}

/// Advance the ending position by consuming the string
pub fn advance_string(s: &str, p: &Pos) -> Pos {
    let split: Vec<&str> = s.split('\n').collect();
    let (last, lines) = split.split_last().expect("split is not empty");
    // Each line but the last, and its newline.
    let add_bol: isize = lines.iter().map(|hd| hd.len() as isize + 1).sum();
    let num_lines = (split.len() as isize - 1).max(0);
    let (end_line, end_bol, end_offset) = end_line_beg_offset(p);
    let end_line = end_line + num_lines;
    let end_bol = end_bol + add_bol;
    let end_offset = if num_lines == 0 {
        end_offset + last.len() as isize
    } else {
        end_bol + last.len() as isize
    };
    make_from_lnum_bol_offset(
        filename(p),
        line_beg_offset(p),
        (end_line, end_bol, end_offset),
    )
}

/// Return a zero-width position that occurs at the end of input position.
pub fn shrink_to_end(pos: &Pos) -> Pos {
    let end = pos.to_raw_span().end;
    with_span(pos, end, end)
}

// hack for test cases

pub fn print_verbose_absolute(p: &Absolute) -> String {
    let (a, b, c) = line_beg_offset(p);
    let (d, e, f) = end_line_beg_offset(p);
    format!(
        "Pos('{}', <{},{},{}>, <{},{},{}>)",
        filename(p),
        a,
        b,
        c,
        d,
        e,
        f
    )
}

pub fn print_verbose_relative(p: &Pos) -> String {
    print_verbose_absolute(&to_absolute(p))
}

/// `Pos.Map`. The keys are in the order of `Pos`'s `Ord`, which is
/// [`compare`] except that it has the dummy span last in its file (OCaml has
/// it first).
pub mod map {
    pub use oxidized::pos::map::*;

    pub type T<A> = im::OrdMap<oxidized::pos::Pos, A>;
}

/// `Pos.Set`. See [`map`] for the order.
pub mod set {
    pub type T = im::OrdSet<oxidized::pos::Pos>;
}

/// `Pos.AbsolutePosMap`
pub mod absolute_pos_map {
    pub type T<A> = im::OrdMap<super::Absolute, A>;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn file(name: &str) -> RelativePath {
        RelativePath::make(Prefix::Root, name.into())
    }

    /// From `(line, bol, offset)` to `(line, bol, offset)` in `a.php`.
    fn pos(start: (isize, isize, isize), end: (isize, isize, isize)) -> Pos {
        make_from_lnum_bol_offset(file("a.php"), start, end)
    }

    /// Positions of each representation: tiny, small (too wide to be tiny)
    /// and large (too far in the file to be small).
    fn positions() -> Vec<Pos> {
        vec![
            pos((3, 20, 25), (3, 20, 30)),
            pos((3, 20, 25), (3, 20, 225)),
            pos((3, 1 << 40, (1 << 40) + 5), (3, 1 << 40, (1 << 40) + 10)),
        ]
    }

    fn show(p: &Pos) -> String {
        let mut s = String::new();
        pp(&mut s, p).unwrap();
        s
    }

    #[test]
    fn accessors() {
        let p = pos((3, 20, 25), (3, 20, 30));
        assert_eq!(line(&p), 3);
        assert_eq!(end_line(&p), 3);
        assert_eq!(start_offset(&p), 25);
        assert_eq!(end_offset(&p), 30);
        assert_eq!(info_raw(&p), (25, 30));
        assert_eq!(length(&p), 5);
        assert_eq!(line_beg_offset(&p), (3, 20, 25));
        assert_eq!(end_line_beg_offset(&p), (3, 20, 30));
        // One-based columns, and a closed interval.
        assert_eq!(info_pos(&p), (3, 6, 10));
        assert_eq!(info_pos_extended(&p), (3, 3, 6, 10));
        // One-based columns, and a half-open interval.
        assert_eq!(destruct_range_one_based(&p), (3, 6, 3, 11));
        assert_eq!(string_no_file(&p), "line 3, characters 6-10");
        assert_eq!(
            multiline_string_no_file(&p),
            "line 3, character 6 - line 3, character 10"
        );
        assert_eq!(filename(&p), file("a.php"));
        assert_eq!(show(&p), "[3:6-11]");
        // The same in every representation.
        for p in positions() {
            assert_eq!(info_pos(&p).0, 3);
            assert_eq!(info_pos(&p).1, 6);
            assert_eq!(line_beg_offset(&p).0, 3);
            assert_eq!(start_offset(&p) - line_beg_offset(&p).1, 5);
            // As `oxidized` has it.
            let (l, s, e) = p.info_pos();
            assert_eq!(info_pos(&p), (l as isize, s as isize, e as isize));
        }
    }

    #[test]
    fn empty_and_multiline() {
        // An empty span shows one character.
        let p = pos((3, 20, 25), (3, 20, 25));
        assert_eq!(info_pos(&p), (3, 6, 6));
        assert_eq!(show(&p), "[3:6-6]");
        // The end column of a multi-line span is from the start of the
        // first line.
        let p = pos((3, 20, 25), (5, 60, 62));
        assert_eq!(info_pos(&p), (3, 6, 42));
        assert_eq!(info_pos_extended(&p), (3, 5, 6, 42));
        assert_eq!(destruct_range_one_based(&p), (3, 6, 5, 3));
        assert_eq!(
            multiline_string_no_file(&p),
            "line 3, character 6 - line 5, character 2"
        );
        assert_eq!(show(&p), "[3:6-5:3]");
    }

    #[test]
    fn dummy() {
        assert_eq!(show(&none), "[Pos.none]");
        assert_eq!(info_pos(&none), (0, 0, 0));
        assert_eq!(info_raw(&none), (-1, -1));
        assert_eq!(length(&none), 0);
        assert_eq!(line_beg_offset(&none), (0, 0, -1));
        assert_eq!(filename(&none), relative_path::default);
        // `make_from`: the dummy span, in a file.
        let p = make_from(file("a.php"));
        assert!(!equal(&p, &none));
        assert_eq!(filename(&p), file("a.php"));
        assert_eq!(info_pos(&p), (0, 0, 0));
        assert_eq!(show(&p), "[0:0-0]");
        assert!(equal(&make_from(relative_path::default), &none));
        // The dummy span is before the others of its file.
        let q = pos((1, 0, 0), (1, 0, 1));
        assert_eq!(compare(&p, &q), Ordering::Less);
        assert_eq!(compare(&q, &p), Ordering::Greater);
        assert_eq!(compare(&p, &p), Ordering::Equal);
    }

    #[test]
    fn order() {
        let a = pos((1, 0, 3), (1, 0, 9));
        let b = pos((1, 0, 3), (1, 0, 10));
        let c = pos((1, 0, 4), (1, 0, 5));
        let other = make_from_lnum_bol_offset(file("b.php"), (1, 0, 0), (1, 0, 1));
        assert_eq!(compare(&a, &b), Ordering::Less);
        assert_eq!(compare(&b, &c), Ordering::Less);
        assert_eq!(compare(&c, &other), Ordering::Less);
        // Without the files (`classish_positions.ml`'s `compare_pos (fun _ _ -> 0)`).
        assert_eq!(compare_pos(|_, _| Ordering::Equal, &other, &c), Ordering::Less);
        assert_eq!(compare_pos(|_, _| Ordering::Equal, &a, &a), Ordering::Equal);
        // `set_file`: the same span in another file.
        let moved = set_file(file("b.php"), &a);
        assert_eq!(filename(&moved), file("b.php"));
        assert_eq!(info_raw(&moved), info_raw(&a));
        assert_eq!(line_beg_offset(&moved), line_beg_offset(&a));
        assert!(equal(&a, &a.clone()));
        assert!(!equal(&a, &b));
        assert!(contains(&b, &a) && !contains(&a, &b));
        assert!(contains(&a, &c) && !contains(&c, &a));
        assert!(contains(&a, &a));
        // Not in another file.
        assert!(!contains(
            &make_from_lnum_bol_offset(file("b.php"), (1, 0, 3), (1, 0, 9)),
            &a
        ));
        assert!(overlaps(&a, &c) && overlaps(&c, &a));
        // Touching is not overlapping, and neither is another file.
        assert!(!overlaps(&pos((1, 0, 0), (1, 0, 3)), &a));
        assert!(!overlaps(
            &make_from_lnum_bol_offset(file("b.php"), (1, 0, 3), (1, 0, 9)),
            &a
        ));
        assert!(!is_hhi(&a));
        let hhi_pos = make_from(RelativePath::make(Prefix::Hhi, "x.hhi".into()));
        assert!(is_hhi(&hhi_pos));
    }

    #[test]
    fn between_and_merge() {
        let a = pos((1, 0, 3), (1, 0, 9));
        let b = pos((2, 20, 24), (2, 20, 30));
        let ab = pos((1, 0, 3), (2, 20, 30));
        assert!(equal(&btw(&a, &b), &ab));
        assert!(equal(&btw_nocheck(&a, &b), &ab));
        assert!(equal(&merge(&a, &b), &ab));
        assert!(equal(&merge(&b, &a), &ab));
        // The dummy position is neutral.
        assert!(equal(&merge(&a, &make_from(file("a.php"))), &a));
        assert!(equal(&merge(&make_from(file("a.php")), &a), &a));
        for p in positions() {
            assert!(equal(&btw(&p, &p), &p));
            assert!(equal(&merge(&p, &p), &p));
        }
    }

    #[test]
    #[should_panic(expected = "Position in separate files")]
    fn between_files() {
        let a = pos((1, 0, 3), (1, 0, 9));
        let b = make_from_lnum_bol_offset(file("b.php"), (1, 0, 3), (1, 0, 9));
        btw(&a, &b);
    }

    #[test]
    fn shrink_and_advance() {
        for p in positions() {
            let (l, bol, start) = line_beg_offset(&p);
            let (_, _, end) = end_line_beg_offset(&p);
            let q = shrink_to_end(&p);
            assert_eq!(line_beg_offset(&q), (l, bol, end));
            assert_eq!(end_line_beg_offset(&q), (l, bol, end));
            let q = advance_one(&p);
            assert_eq!(line_beg_offset(&q), (l, bol, start));
            assert_eq!(end_line_beg_offset(&q), (l, bol, end + 1));
            let q = shrink_by_one_char_both_sides(&p);
            assert_eq!(line_beg_offset(&q), (l, bol, start + 1));
            assert_eq!(end_line_beg_offset(&q), (l, bol, end - 1));
            assert_eq!(filename(&q), filename(&p));
        }
    }

    #[test]
    fn advance_by_string() {
        let p = pos((3, 20, 25), (3, 20, 30));
        // On the same line.
        let q = advance_string("abc", &p);
        assert_eq!(line_beg_offset(&q), (3, 20, 25));
        assert_eq!(end_line_beg_offset(&q), (3, 20, 33));
        assert!(equal(&advance_string("", &p), &p));
        // Over two newlines: `ab\n`, `cde\n` and `f`. The beginning of the
        // last line is the beginning of the line of the end, plus the lines.
        let q = advance_string("ab\ncde\nf", &p);
        assert_eq!(line_beg_offset(&q), (3, 20, 25));
        assert_eq!(end_line_beg_offset(&q), (5, 27, 28));
        let q = advance_string("\n", &p);
        assert_eq!(end_line_beg_offset(&q), (4, 21, 21));
    }

    #[test]
    fn text() {
        let content = "0123456789\nabcdefghij\n";
        let p = pos((2, 11, 13), (2, 11, 16));
        assert_eq!(get_text_from_pos(content, &p), "cde");
        assert_eq!(get_text_from_pos(content, &shrink_to_end(&p)), "");
    }

    #[test]
    fn absolute() {
        relative_path::set_prefixes_for_tests();
        let p = pos((3, 20, 25), (3, 20, 30));
        let abs = to_absolute(&p);
        assert_eq!(filename(&abs), "/data/www/a.php");
        assert_eq!(
            string(&abs),
            r#"File "/data/www/a.php", line 3, characters 6-10:"#
        );
        assert_eq!(
            multiline_string(&abs),
            r#"File "/data/www/a.php", line 3, character 6 - line 3, character 10:"#
        );
        assert_eq!(
            print_verbose_absolute(&abs),
            "Pos('/data/www/a.php', <3,20,25>, <3,20,30>)"
        );
        assert_eq!(
            print_verbose_relative(&p),
            "Pos('/data/www/a.php', <3,20,25>, <3,20,30>)"
        );
        assert_eq!(
            print_verbose_relative(&make_from(file("a.php"))),
            "Pos('/data/www/a.php', <0,0,-1>, <0,0,-1>)"
        );
        assert_eq!(
            yojson::to_string(&json(&abs)),
            r#"{"filename":"/data/www/a.php","line":3,"char_start":6,"char_end":10}"#
        );
        assert_eq!(
            yojson::to_string(&multiline_json(&abs)),
            r#"{"filename":"/data/www/a.php","line_start":3,"char_start":6,"line_end":3,"char_end":10}"#
        );
        assert!(equal(&to_relative(&abs), &p));
        assert!(equal_absolute(&abs, &to_absolute(&p)));
        assert_eq!(line(&abs), 3);
        assert_eq!(info_pos(&abs), (3, 6, 10));

        // The directory of the hhi files is not shown.
        let hhi_pos = make_from_lnum_bol_offset(
            RelativePath::make(Prefix::Hhi, "x.hhi".into()),
            (1, 0, 0),
            (1, 0, 4),
        );
        assert_eq!(
            string(&to_absolute(&hhi_pos)),
            r#"File "x.hhi", line 1, characters 1-4:"#
        );

        let rel = to_relative_string(&p);
        assert_eq!(filename(&rel), "a.php");
        assert_eq!(string(&rel), r#"File "a.php", line 3, characters 6-10:"#);
        assert_eq!(compare_absolute(&rel, &abs), Ordering::Greater);
    }

    #[test]
    fn ocaml_string_literals() {
        assert_eq!(sprintf_S("a.php"), r#""a.php""#);
        assert_eq!(sprintf_S("a \"b\"\\c"), r#""a \"b\"\\c""#);
        assert_eq!(sprintf_S("\n\t\r\u{8}"), r#""\n\t\r\b""#);
        assert_eq!(sprintf_S("\u{1}\u{7f}"), r#""\001\127""#);
        // Bytes: the two bytes of `é`.
        assert_eq!(sprintf_S("é"), r#""\195\169""#);
    }
}
