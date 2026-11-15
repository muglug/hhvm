// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `ide_rpc/ide_api_types.ml`. See `hh/PORTING.md`.

use crate::file_content;
use crate::file_content::position;
use crate::format;
use crate::pos;

/// `range`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub st: position::T,
    pub ed: position::T,
}

/// `[@@deriving show]`: `pp_range`
pub fn pp_range(fmt: &mut format::Formatter, x: &Range) {
    use crate::format::*;
    // "@[<2>{ "
    pp_open_box(fmt, 2);
    pp_print_string(fmt, "{ ");
    // "@[%s =@ " "Ide_api_types.st"; pp; "@]"
    pp_open_box(fmt, 0);
    pp_print_string(fmt, "Ide_api_types.st");
    pp_print_string(fmt, " =");
    pp_print_space(fmt);
    position::pp(fmt, &x.st);
    pp_close_box(fmt);
    // ";@ "
    pp_print_string(fmt, ";");
    pp_print_space(fmt);
    // "@[%s =@ " "ed"; pp; "@]"
    pp_open_box(fmt, 0);
    pp_print_string(fmt, "ed");
    pp_print_string(fmt, " =");
    pp_print_space(fmt);
    position::pp(fmt, &x.ed);
    pp_close_box(fmt);
    // "@ }@]"
    pp_print_space(fmt);
    pp_print_string(fmt, "}");
    pp_close_box(fmt);
}

/// `[@@deriving show]`: `show_range`
pub fn show_range(x: &Range) -> String {
    format::asprintf(|fmt| pp_range(fmt, x))
}

/// `file_position`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FilePosition {
    pub filename: String,
    pub position: position::T,
}

/// `file_range`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileRange {
    pub range_filename: String,
    pub file_range: Range,
}

/// `text_edit`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextEdit {
    pub range: Option<Range>,
    pub text: String,
}

/// `[@@deriving show]`: `pp_text_edit`
pub fn pp_text_edit(fmt: &mut format::Formatter, x: &TextEdit) {
    use crate::format::*;
    pp_open_box(fmt, 2);
    pp_print_string(fmt, "{ ");
    pp_open_box(fmt, 0);
    pp_print_string(fmt, "Ide_api_types.range");
    pp_print_string(fmt, " =");
    pp_print_space(fmt);
    // `function None -> "None" | Some x -> "(Some " pp x ")"`
    match &x.range {
        None => pp_print_string(fmt, "None"),
        Some(r) => {
            pp_print_string(fmt, "(Some ");
            pp_range(fmt, r);
            pp_print_string(fmt, ")");
        }
    }
    pp_close_box(fmt);
    pp_print_string(fmt, ";");
    pp_print_space(fmt);
    pp_open_box(fmt, 0);
    pp_print_string(fmt, "text");
    pp_print_string(fmt, " =");
    pp_print_space(fmt);
    pp_print_string(fmt, &crate::rt::ocaml_printf::sprintf_s(&x.text));
    pp_close_box(fmt);
    pp_print_space(fmt);
    pp_print_string(fmt, "}");
    pp_close_box(fmt);
}

/// `[@@deriving show]`: `show_text_edit`
pub fn show_text_edit(x: &TextEdit) -> String {
    format::asprintf(|fmt| pp_text_edit(fmt, x))
}

pub fn ide_range_from_fc(file_content::Range { st, ed }: &file_content::Range) -> Range {
    Range { st: *st, ed: *ed }
}

pub fn ide_range_to_fc(Range { st, ed }: &Range) -> file_content::Range {
    file_content::Range { st: *st, ed: *ed }
}

pub fn pos_to_range<P: pos::APos>(x: &P) -> Range {
    let (st_line, st_column, ed_line, ed_column) = pos::destruct_range_one_based(x);
    Range {
        st: position::from_one_based(st_line, st_column),
        ed: position::from_one_based(ed_line, ed_column),
    }
}

pub fn pos_to_file_range(x: &pos::Absolute) -> FileRange {
    FileRange {
        range_filename: pos::filename(x),
        file_range: pos_to_range(x),
    }
}

pub fn range_to_string_single_line(Range { st, ed }: &Range) -> String {
    let (line, start_c) = position::line_column_one_based(st);
    let (_, end_c) = position::line_column_one_based(ed);
    format!("line {}, characters {}-{}", line, start_c, end_c)
}
