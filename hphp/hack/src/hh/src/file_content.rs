// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `file_content.ml`. See `hh/PORTING.md`.
//!
//! OCaml strings are bytes: offsets are byte offsets here too, and a column
//! counts UTF-8 characters (see [`get_char_length`]).
//!
//! The exceptions: `get_offset`, `get_offsets`, `offset_to_position` and
//! `get_char` raise `Invalid_argument "index out of bounds"` (a position
//! after the end of the content) or `Failure` (an offset after the end, a
//! byte that cannot start a UTF-8 character); here they panic with the
//! message (`Invalid_argument: ...` for `Invalid_argument`). `edit_file`
//! catches them: there the functions it calls return them as an
//! [`Exn`], whose `Debug` is what `Printexc.to_string` gives in OCaml.

use crate::exception;
use crate::yojson::safe as yojson;

pub mod position {
    use crate::yojson::safe as yojson;

    /// (The derived `ord` compares the line, then the column.)
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct T {
        /// 1-based
        line: isize,
        /// 1-based
        column: isize,
    }

    /// `[@@deriving eq]`
    pub fn equal(a: &T, b: &T) -> bool {
        a == b
    }

    /// `[@@deriving ord]`
    pub fn compare(a: &T, b: &T) -> isize {
        a.cmp(b) as isize
    }

    /// `[@@deriving show]`: `pp`
    pub fn pp(fmt: &mut crate::format::Formatter, x: &T) {
        use crate::format::*;
        // "@[<2>{ "
        pp_open_box(fmt, 2);
        pp_print_string(fmt, "{ ");
        // "@[%s =@ " "File_content.Position.line"; "%d"; "@]"
        pp_open_box(fmt, 0);
        pp_print_string(fmt, "File_content.Position.line");
        pp_print_string(fmt, " =");
        pp_print_space(fmt);
        pp_print_string(fmt, &x.line.to_string());
        pp_close_box(fmt);
        // ";@ "
        pp_print_string(fmt, ";");
        pp_print_space(fmt);
        // "@[%s =@ " "column"; "%d"; "@]"
        pp_open_box(fmt, 0);
        pp_print_string(fmt, "column");
        pp_print_string(fmt, " =");
        pp_print_space(fmt);
        pp_print_string(fmt, &x.column.to_string());
        pp_close_box(fmt);
        // "@ }@]"
        pp_print_space(fmt);
        pp_print_string(fmt, "}");
        pp_close_box(fmt);
    }

    /// `[@@deriving show]`: `show`
    pub fn show(x: &T) -> String {
        crate::format::asprintf(|fmt| pp(fmt, x))
    }

    /// `[@@deriving yojson_of]`
    pub fn yojson_of_t(x: &T) -> yojson::T {
        yojson::T::Assoc(vec![
            ("line".to_string(), yojson::T::Int(x.line)),
            ("column".to_string(), yojson::T::Int(x.column)),
        ])
    }

    const FIRST_LINE: isize = 1;

    const FIRST_COLUMN: isize = 1;

    /// `first_line`
    #[allow(dead_code)]
    fn first_line() -> isize {
        FIRST_LINE
    }

    /// `first_column`
    #[allow(dead_code)]
    fn first_column() -> isize {
        FIRST_COLUMN
    }

    const BEGINNING_OF_FILE: T = T {
        line: FIRST_LINE,
        column: FIRST_COLUMN,
    };

    /// `beginning_of_file` (a value in OCaml).
    pub fn beginning_of_file() -> T {
        BEGINNING_OF_FILE
    }

    pub fn from_one_based(line: isize, column: isize) -> T {
        T { line, column }
    }

    pub fn from_zero_based(line: isize, column: isize) -> T {
        T {
            line: line + 1,
            column: column + 1,
        }
    }

    pub fn line_column_one_based(T { line, column }: &T) -> (isize, isize) {
        (*line, *column)
    }

    pub fn line_column_zero_based(T { line, column }: &T) -> (isize, isize) {
        (line - 1, column - 1)
    }

    pub fn beginning_of_line(T { line, column: _ }: &T) -> T {
        T {
            line: *line,
            column: FIRST_COLUMN,
        }
    }

    pub fn beginning_of_next_line(T { line, column: _ }: &T) -> T {
        T {
            line: line + 1,
            column: FIRST_COLUMN,
        }
    }

    pub fn is_beginning_of_line(T { line: _, column }: &T) -> bool {
        *column == FIRST_COLUMN
    }

    pub fn next_char(T { line, column }: &T) -> T {
        T {
            line: *line,
            column: column + 1,
        }
    }

    pub fn to_string_one_based(T { line, column }: &T) -> String {
        format!("{}:{}", line, column)
    }

    pub fn move_back(T { line, column }: &T, n: isize) -> T {
        T {
            line: *line,
            column: column - n,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub st: position::T,
    pub ed: position::T,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextEdit {
    pub range: Option<Range>,
    pub text: String,
}

/// The exceptions that the functions `edit_file` calls raise, which it
/// catches. `Debug` gives what `Printexc.to_string` gives in OCaml.
#[derive(Clone, PartialEq, Eq)]
pub enum Exn {
    Failure(String),
    InvalidArgument(String),
}

impl std::fmt::Debug for Exn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Exn::Failure(s) => write!(f, "Failure({})", ocaml_string_literal(s)),
            Exn::InvalidArgument(s) => {
                write!(f, "Invalid_argument({})", ocaml_string_literal(s))
            }
        }
    }
}

/// Where OCaml lets the exception propagate.
fn raise(e: Exn) -> ! {
    match e {
        Exn::Failure(s) => panic!("{}", s),
        Exn::InvalidArgument(s) => panic!("Invalid_argument: {}", s),
    }
}

/// `%S`: the string as an OCaml string literal (`String.escaped`).
fn ocaml_string_literal(s: &str) -> String {
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

/// UTF-8 encoding character lengths.
///
/// NOTE: at the moment, edit commands are the only place where we count
/// UTF-8 encoded characters as opposed to ASCII bytes - in all of the other
/// places (column numbers in errors, positions in IDE commands) we still use the
/// latter.
///
/// We make an exception here because that's the way Nuclide counts characters,
/// and the consequences of mishandling it are much more dire than in other
/// places - we'll not only fail the current single request, but diverge
/// the synchronized state forever.
pub fn get_char_length(c: u8) -> isize {
    match try_get_char_length(c) {
        Ok(n) => n,
        Err(e) => raise(e),
    }
}

fn try_get_char_length(c: u8) -> Result<isize, Exn> {
    let c = c as isize;
    if c >> 7 == 0b0 {
        Ok(1)
    } else if c >> 5 == 0b110 {
        Ok(2)
    } else if c >> 4 == 0b1110 {
        Ok(3)
    } else if c >> 3 == 0b11110 {
        Ok(4)
    } else {
        Err(Exn::Failure(format!("Invalid UTF-8 leading byte: {}", c)))
    }
}

pub fn is_target(t: &position::T, line: isize, column: isize) -> bool {
    position::equal(t, &position::from_one_based(line, column))
}

/// The byte at `offset` (an OCaml `char`).
pub fn get_char(content: &str, offset: isize) -> u8 {
    match try_get_char(content, offset) {
        Ok(c) => c,
        Err(e) => raise(e),
    }
}

fn try_get_char(content: &str, offset: isize) -> Result<u8, Exn> {
    // sentinel newline to make things easier
    if offset == content.len() as isize {
        Ok(b'\n')
    } else if offset < 0 || offset > content.len() as isize {
        // `content.[offset]`
        Err(Exn::InvalidArgument("index out of bounds".to_string()))
    } else {
        Ok(content.as_bytes()[offset as usize])
    }
}

/// The recursive `get_offsets` that the exported one calls (OCaml defines
/// both with the same name), as a loop.
fn get_offsets_loop(
    content: &str,
    queries: (&position::T, &position::T),
    line: isize,
    column: isize,
    offset: isize,
    acc: (Option<isize>, Option<isize>),
) -> Result<(Option<isize>, Option<isize>), Exn> {
    let (mut line, mut column, mut offset, mut acc) = (line, column, offset, acc);
    loop {
        match acc {
            (Some(_), Some(_)) => return Ok(acc),
            (None, r2) if is_target(queries.0, line, column) => acc = (Some(offset), r2),
            (r1 @ Some(_), None) if is_target(queries.1, line, column) => {
                acc = (r1, Some(offset))
            }
            _ => {
                let (line_, column_, offset_) = match try_get_char(content, offset)? {
                    b'\n' => (line + 1, 1, offset + 1),
                    c => (line, column + 1, offset + try_get_char_length(c)?),
                };
                line = line_;
                column = column_;
                offset = offset_;
            }
        }
    }
}

pub fn invalid_position(p: &position::T) -> ! {
    raise(invalid_position_exn(p))
}

fn invalid_position_exn(p: &position::T) -> Exn {
    Exn::Failure(format!(
        "Invalid position: {}",
        yojson::to_string(&position::yojson_of_t(p))
    ))
}

/// this returns 0-based offsets
pub fn get_offsets(content: &str, queries: (&position::T, &position::T)) -> (isize, isize) {
    match try_get_offsets(content, queries) {
        Ok(r) => r,
        Err(e) => raise(e),
    }
}

fn try_get_offsets(
    content: &str,
    queries: (&position::T, &position::T),
) -> Result<(isize, isize), Exn> {
    match get_offsets_loop(content, queries, 1, 1, 0, (None, None))? {
        (Some(r1), Some(r2)) => Ok((r1, r2)),
        (None, _) => Err(invalid_position_exn(queries.0)),
        (_, None) => Err(invalid_position_exn(queries.1)),
    }
}

/// This returns a 0-based offset. If you need to get two offsets, use
/// `get_offsets` instead.
pub fn get_offset(content: &str, position: &position::T) -> isize {
    get_offsets(content, (position, position)).0
}

/// This takes 0-based offsets and returns 1-based positions.
/// It gives the position of the character *immediately after* this offset,
/// e.g. "offset_to_position s 0" gives the 1-based position {line=1,col=1}.
/// It sounds confusing but is natural when you work with half-open ranges!
/// It is okay to ask for the position of the offset of the end of the file.
/// In case of multi-byte characters, if you give an offset inside a character,
/// it still gives the position immediately after.
pub fn offset_to_position(content: &str, offset: isize) -> position::T {
    let helper = |p: position::T, index: isize| -> position::T {
        let (mut p, mut index) = (p, index);
        loop {
            if index >= offset {
                return p;
            }
            let c = get_char(content, index);
            let clen = get_char_length(c);
            if c == b'\n' {
                p = position::beginning_of_next_line(&p);
            } else {
                p = position::next_char(&p);
            }
            index += clen;
        }
    };
    if offset > content.len() as isize {
        panic!("Invalid offset: {}", offset)
    } else {
        helper(position::beginning_of_file(), 0)
    }
}

/// `Str.string_before s n`, `Str.string_after s n`: `String.sub`, which
/// raises `Invalid_argument` out of the string. (The offsets that
/// `get_offsets` gives are at the start of a UTF-8 character.)
fn string_sub(s: &str, start: isize, len: isize) -> Result<&str, Exn> {
    if start < 0 || len < 0 || start + len > s.len() as isize {
        return Err(Exn::InvalidArgument("String.sub / Bytes.sub".to_string()));
    }
    let (start, len) = (start as usize, len as usize);
    s.get(start..start + len)
        .ok_or_else(|| Exn::InvalidArgument("String.sub / Bytes.sub".to_string()))
}

pub fn apply_edit(content: &str, edit: &TextEdit) -> String {
    match try_apply_edit(content, edit) {
        Ok(r) => r,
        Err(e) => raise(e),
    }
}

fn try_apply_edit(content: &str, TextEdit { range, text }: &TextEdit) -> Result<String, Exn> {
    match range {
        None => Ok(text.clone()),
        Some(Range { st, ed }) => {
            let (start_offset, end_offset) = try_get_offsets(content, (st, ed))?;
            let prefix = string_sub(content, 0, start_offset)?;
            let suffix = string_sub(
                content,
                end_offset,
                content.len() as isize - end_offset,
            )?;
            Ok(format!("{}{}{}", prefix, text, suffix))
        }
    }
}

pub fn print_edit(b: &mut String, edit: &TextEdit) {
    let range = match &edit.range {
        None => "None".to_string(),
        Some(range) => format!(
            "{} - {}",
            position::to_string_one_based(&range.st),
            position::to_string_one_based(&range.ed)
        ),
    };
    b.push_str(&format!("range = {}\n text = \n{}\n", range, edit.text))
}

pub fn edit_file(content: &str, edits: &[TextEdit]) -> Result<String, (String, exception::T)> {
    let apply_all = || -> Result<String, Exn> {
        let mut content = content.to_string();
        for edit in edits {
            content = try_apply_edit(&content, edit)?;
        }
        Ok(content)
    };
    match apply_all() {
        Ok(r) => Ok(r),
        Err(exn) => {
            let e = exception::wrap(exn);
            let mut b = String::with_capacity(1024);
            b.push_str(&format!("Invalid edit: {}\n", exception::get_ctor_string(&e)));
            b.push_str(&format!("Original content:\n{}\n", content));
            b.push_str("Edits:\n");
            for edit in edits {
                print_edit(&mut b, edit)
            }
            Err((b, e))
        }
    }
}

pub fn edit_file_unsafe(fc: &str, edits: &[TextEdit]) -> String {
    match edit_file(fc, edits) {
        Ok(r) => r,
        Err((e, _stack)) => {
            eprint!("{}", e);
            panic!("{}", e)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::position::*;
    use super::*;

    fn edit(st: (isize, isize), ed: (isize, isize), text: &str) -> TextEdit {
        TextEdit {
            range: Some(Range {
                st: from_one_based(st.0, st.1),
                ed: from_one_based(ed.0, ed.1),
            }),
            text: text.to_string(),
        }
    }

    #[test]
    fn positions() {
        let p = from_zero_based(2, 4);
        assert_eq!(line_column_one_based(&p), (3, 5));
        assert_eq!(line_column_zero_based(&p), (2, 4));
        assert_eq!(to_string_one_based(&p), "3:5");
        assert!(is_beginning_of_line(&beginning_of_line(&p)));
        assert_eq!(beginning_of_next_line(&p), from_one_based(4, 1));
        assert_eq!(move_back(&p, 2), from_one_based(3, 3));
        assert_eq!(compare(&from_one_based(1, 9), &from_one_based(2, 1)), -1);
        assert_eq!(show(&p), "{ File_content.Position.line = 3; column = 5 }");
        assert_eq!(
            yojson::to_string(&yojson_of_t(&p)),
            r#"{"line":3,"column":5}"#
        );
    }

    #[test]
    fn offsets() {
        let s = "ab\n\u{e9}c\n";
        assert_eq!(get_offset(s, &from_one_based(1, 1)), 0);
        assert_eq!(get_offset(s, &from_one_based(1, 3)), 2);
        assert_eq!(get_offset(s, &from_one_based(2, 1)), 3);
        // A column counts characters, an offset bytes.
        assert_eq!(get_offset(s, &from_one_based(2, 2)), 5);
        assert_eq!(get_offset(s, &from_one_based(3, 1)), 7);
        assert_eq!(
            get_offsets(s, (&from_one_based(1, 2), &from_one_based(2, 3))),
            (1, 6)
        );
        assert_eq!(offset_to_position(s, 0), from_one_based(1, 1));
        assert_eq!(offset_to_position(s, 4), from_one_based(2, 2));
        assert_eq!(offset_to_position(s, 5), from_one_based(2, 2));
        assert_eq!(offset_to_position(s, 7), from_one_based(3, 1));
        assert_eq!(get_char(s, 7), b'\n');
        assert_eq!(get_char(s, 0), b'a');
    }

    #[test]
    fn edits() {
        let s = "hello\nworld\n";
        assert_eq!(
            edit_file(s, &[edit((1, 1), (1, 6), "bye"), edit((2, 1), (2, 1), ">")]).unwrap(),
            "bye\n>world\n"
        );
        assert_eq!(
            edit_file(
                s,
                &[TextEdit {
                    range: None,
                    text: "x".to_string()
                }]
            )
            .unwrap(),
            "x"
        );
        let (msg, _) = edit_file(s, &[edit((9, 1), (9, 1), "z")]).unwrap_err();
        assert_eq!(
            msg,
            "Invalid edit: Invalid_argument(\"index out of bounds\")\nOriginal content:\nhello\nworld\n\nEdits:\nrange = 9:1 - 9:1\n text = \nz\n"
        );
        // The end is looked for after the start only.
        assert!(edit_file(s, &[edit((2, 1), (1, 1), "")]).is_err());
        assert_eq!(
            format!("{:?}", invalid_position_exn(&from_one_based(1, 2))),
            "Failure(\"Invalid position: {\\\"line\\\":1,\\\"column\\\":2}\")"
        );
    }
}
