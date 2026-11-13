// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/autocomplete_types.ml`. See `hh/PORTING.md`.
//!
//! The token is used by the typechecker too (`Typing.Expr.dispatch_call`
//! recognises it); the types are those of the IDE services (owned by **F3**,
//! plan §7.3).
//!
//! `char_at_pos` is an OCaml `char` (a byte): a `u8` here.

#![allow(non_upper_case_globals)]

use crate::file_info::SiKind;
use crate::ide_api_types;
use crate::pos;

/// `snippet_with_fallback`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnippetWithFallback {
    pub snippet: String,
    pub fallback: String,
}

/// `insert_text`: whether the insert text is to be inserted literally or as
/// an LSP snippet (`insertTextFormat`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InsertText {
    InsertLiterally(String),
    InsertAsSnippet(SnippetWithFallback),
}

/// `autocomplete_item`
#[derive(Clone, Debug)]
pub struct AutocompleteItem {
    /// The position of the declaration we're returning.
    pub res_decl_pos: pos::Absolute,
    /// The position in the opened file that we're replacing with
    /// res_insert_text.
    pub res_replace_pos: ide_api_types::Range,
    /// If we're autocompleting a method, store the class name of the variable
    /// we're calling the method on (for doc block fallback in autocomplete
    /// resolution).
    pub res_base_class: Option<String>,
    /// These strings correspond to the LSP fields in CompletionItem.
    pub res_label: String,
    pub res_insert_text: InsertText,
    pub res_detail: String,
    pub res_sort_text: Option<String>,
    pub res_filter_text: Option<String>,
    pub res_additional_edits: Vec<(String, ide_api_types::Range)>,
    /// res_fullname is res_label without trimming the namespace.
    pub res_fullname: String,
    pub res_kind: SiKind,
    /// documentation (in markdown); if absent, then it will be resolved
    /// on-demand later
    pub res_documentation: Option<String>,
}

/// `ide_result`: the type returned to the client
#[derive(Clone, Debug)]
pub struct IdeResult {
    pub completions: Vec<AutocompleteItem>,
    pub char_at_pos: u8,
    pub is_complete: bool,
}

/// `result`
pub type Result = Vec<AutocompleteItem>;

/// `Str.regexp_case_fold ".*do_not_use.*"` matched at 0: `.` does not match
/// a newline, so the text is searched up to the first newline; case folding
/// is `Char.lowercase_ascii`.
fn matches_do_not_use(label: &str) -> bool {
    let line = match label.find('\n') {
        Some(i) => &label[..i],
        None => label,
    };
    line.to_ascii_lowercase().contains("do_not_use")
}

/// `sort_text`
pub fn sort_text(result: &AutocompleteItem) -> String {
    let raw_sort_text = match &result.res_sort_text {
        Some(sort_text) if !sort_text.is_empty() => sort_text.as_str(),
        Some(_) | None => result.res_label.as_str(),
    };
    let label = &result.res_label;
    let should_downrank =
        (label.len() > 2 && label.as_bytes()[..2] == *b"__") || matches_do_not_use(label);
    if should_downrank {
        format!("~{}", raw_sort_text)
    } else {
        raw_sort_text.to_string()
    }
}

/// `legacy_autocomplete_context`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LegacyAutocompleteContext {
    pub is_manually_invoked: bool,
    pub is_after_single_colon: bool,
    pub is_after_double_right_angle_bracket: bool,
    pub is_after_open_square_bracket: bool,
    pub is_after_quote: bool,
    pub is_before_apostrophe: bool,
    pub is_open_curly_without_equals: bool,
    pub char_at_pos: u8,
}

/// Autocomplete token
pub const autocomplete_token: &str = "AUTO332";

/// Autocomplete token length
pub const autocomplete_token_length: isize = 7;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_is_the_ocaml_one() {
        let ml = include_str!("../../client_and_server/autocomplete_types.ml");
        assert!(ml.contains(&format!(
            "let autocomplete_token = \"{}\"",
            autocomplete_token
        )));
        assert!(ml.contains(&format!(
            "let autocomplete_token_length = {}",
            autocomplete_token_length
        )));
    }

    fn item(label: &str, sort: Option<&str>) -> AutocompleteItem {
        let p = crate::file_content::position::from_one_based(1, 1);
        AutocompleteItem {
            res_decl_pos: pos::to_absolute(&pos::Pos::NONE),
            res_replace_pos: ide_api_types::Range { st: p, ed: p },
            res_base_class: None,
            res_label: label.to_string(),
            res_insert_text: InsertText::InsertLiterally(label.to_string()),
            res_detail: String::new(),
            res_sort_text: sort.map(|s| s.to_string()),
            res_filter_text: None,
            res_additional_edits: vec![],
            res_fullname: label.to_string(),
            res_kind: SiKind::SIClass,
            res_documentation: None,
        }
    }

    #[test]
    fn sort_texts() {
        assert_eq!(sort_text(&item("foo", None)), "foo");
        assert_eq!(sort_text(&item("foo", Some(""))), "foo");
        assert_eq!(sort_text(&item("foo", Some("0001"))), "0001");
        assert_eq!(sort_text(&item("__construct", None)), "~__construct");
        assert_eq!(sort_text(&item("__", None)), "__");
        assert_eq!(sort_text(&item("x_DO_NOT_USE", Some("a"))), "~a");
    }
}
