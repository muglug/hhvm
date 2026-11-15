// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_auto_complete.ml`: code for
//! auto-completion. See `hh/PORTING.md`.
//!
//! File contents are bytes; `File_content` works on `&str`: contents that are
//! not UTF-8 are read lossily (as everywhere `File_content` is used).

use std::sync::Arc;

use bstr::BString;
use bstr::ByteSlice;

use crate::autocomplete_service;
use crate::autocomplete_types;
use crate::autocomplete_types::LegacyAutocompleteContext;
use crate::file_content;
use crate::naming_table;
use crate::provider_context;
use crate::search_utils::SiEnv;
use crate::string_utils;
use crate::tast_env;
use crate::utils;
use crate::utils::with_complete_flag;

/// The regexps of the module, as `Str` reads them: matched at 0 (`^`), `.`
/// does not match a newline, `$` matches at the end of the text or before a
/// newline.
mod regexps {
    use std::sync::LazyLock;

    use regex::bytes::Regex;

    /// For identifying case statements from text context
    pub static CONTEXT_AFTER_SINGLE_COLON_REGEX: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r#"^.*[a-zA-Z_0-9"']:(?m:$)"#).unwrap());

    /// For identifying user attributes (`A-z` is the range of the `.ml`)
    pub static CONTEXT_AFTER_DOUBLE_RIGHT_ANGLE_BRACKET_REGEX: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r#"^.*[a-zA-z_0-9"' ,)]>>(?m:$)"#).unwrap());

    /// For identifying shape keys
    pub static CONTEXT_AFTER_QUOTE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r#"^.*['"](?m:$)"#).unwrap());

    /// For identifying instances of { that are not part of an XHP attribute
    /// value.
    pub static CONTEXT_AFTER_OPEN_CURLY_BRACE_WITHOUT_EQUALS_REGEX: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r#"^.*[^=][ ]*\{(?m:$)"#).unwrap());
}

pub fn get_signature(ctx: &provider_context::T, name: &str) -> Option<String> {
    let tast_env = tast_env::empty(Arc::clone(ctx));
    match tast_env::get_fun(&tast_env, &utils::add_ns(name)) {
        crate::decl_entry::T::NotYetAvailable | crate::decl_entry::T::DoesNotExist => None,
        crate::decl_entry::T::Found(fe) => Some(
            autocomplete_service::rstrip(
                string_utils::lstrip(&tast_env::print_decl_ty(None, &tast_env, &fe.ty), "("),
                ")",
            )
            .to_string(),
        ),
    }
}

pub fn get_autocomplete_context(
    file_content: &[u8],
    pos: &file_content::position::T,
    is_manually_invoked: bool,
) -> LegacyAutocompleteContext {
    // This function retrieves the current line of text up to the position,
    // and determines whether it's something like "<nt:te" or "->:attr".
    // This is a dumb implementation. Would be better to replace it with FFP.
    if file_content::position::is_beginning_of_line(pos) {
        LegacyAutocompleteContext {
            is_manually_invoked,
            is_after_single_colon: false,
            is_after_double_right_angle_bracket: false,
            is_after_open_square_bracket: false,
            is_after_quote: false,
            is_before_apostrophe: false,
            is_open_curly_without_equals: false,
            char_at_pos: b' ',
        }
    } else {
        let pos_start = file_content::position::beginning_of_line(pos);
        let content = file_content.to_str_lossy();
        let (offset_start, offset) = file_content::get_offsets(&content, (&pos_start, pos));
        let content = content.as_bytes();
        let leading_text = &content[offset_start as usize..offset as usize];
        // text is the text from the start of the line up to the caret position
        let is_after_single_colon = regexps::CONTEXT_AFTER_SINGLE_COLON_REGEX.is_match(leading_text);
        let is_after_double_right_angle_bracket =
            regexps::CONTEXT_AFTER_DOUBLE_RIGHT_ANGLE_BRACKET_REGEX.is_match(leading_text);
        let is_after_open_square_bracket = leading_text.last() == Some(&b'[');
        let is_after_quote = regexps::CONTEXT_AFTER_QUOTE.is_match(leading_text);
        // Detect what comes next
        let char_at_pos = *content
            .get((offset + autocomplete_types::AUTOCOMPLETE_TOKEN_LENGTH) as usize)
            .unwrap_or(&b' ');
        let is_before_apostrophe = char_at_pos == b'\'';
        let is_open_curly_without_equals =
            regexps::CONTEXT_AFTER_OPEN_CURLY_BRACE_WITHOUT_EQUALS_REGEX.is_match(leading_text);
        LegacyAutocompleteContext {
            is_manually_invoked,
            is_after_single_colon,
            is_after_double_right_angle_bracket,
            is_after_open_square_bracket,
            is_after_quote,
            is_before_apostrophe,
            is_open_curly_without_equals,
            char_at_pos,
        }
    }
}

/// Call this function if you have an edited text file that ALREADY INCLUDES
/// "AUTO332"
pub fn go_at_auto332_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    sienv_ref: &mut SiEnv,
    autocomplete_context: &LegacyAutocompleteContext,
    naming_table: &naming_table::T,
) -> with_complete_flag::T<Vec<autocomplete_types::AutocompleteItem>> {
    // Be sure to fix tcopt on all entry points of this file
    let ctx = provider_context::with_tcopt_for_autocomplete(ctx);
    autocomplete_service::go_ctx(&ctx, entry, autocomplete_context, sienv_ref, naming_table)
}

/// Call this function if you have a raw text file that DOES NOT have
/// "AUTO332" in it
pub fn go_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    sienv_ref: &mut SiEnv,
    naming_table: &naming_table::T,
    is_manually_invoked: bool,
    pos: &file_content::position::T,
) -> autocomplete_types::IdeResult {
    // Be sure to fix tcopt on all entry points of this file
    let ctx = provider_context::with_tcopt_for_autocomplete(ctx);
    // We have to edit the file content to add the text AUTO332.
    // TODO: Switch to FFP Autocomplete to avoid doing this file edit
    let file_content = provider_context::read_file_contents_exn(entry);
    let edits = [file_content::TextEdit {
        range: Some(file_content::Range { st: *pos, ed: *pos }),
        text: autocomplete_types::AUTOCOMPLETE_TOKEN.to_string(),
    }];
    let auto332_content = file_content::edit_file_unsafe(&file_content.to_str_lossy(), &edits);
    let (modified_auto332_context, modified_auto332_entry) =
        provider_context::add_or_overwrite_entry_contents(
            &ctx,
            entry.path.clone(),
            BString::from(auto332_content.clone()),
        );
    let autocomplete_context =
        get_autocomplete_context(auto332_content.as_bytes(), pos, is_manually_invoked);
    let result = go_at_auto332_ctx(
        &modified_auto332_context,
        &modified_auto332_entry,
        sienv_ref,
        &autocomplete_context,
        naming_table,
    );
    autocomplete_types::IdeResult {
        completions: result.value,
        char_at_pos: autocomplete_context.char_at_pos,
        is_complete: result.is_complete,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ctx_of(text: &str, line: isize, column: isize) -> LegacyAutocompleteContext {
        get_autocomplete_context(
            text.as_bytes(),
            &file_content::position::from_one_based(line, column),
            false,
        )
    }

    #[test]
    fn contexts() {
        let c = ctx_of("<?hh\ncase X:AUTO332'\n", 2, 8);
        assert!(c.is_after_single_colon);
        assert_eq!(c.char_at_pos, b'\'');
        assert!(c.is_before_apostrophe);
        let c = ctx_of("<<__Foo>>AUTO332", 1, 10);
        assert!(c.is_after_double_right_angle_bracket);
        let c = ctx_of("$x['AUTO332", 1, 5);
        assert!(c.is_after_quote);
        let c = ctx_of("$x[AUTO332", 1, 4);
        assert!(c.is_after_open_square_bracket);
        let c = ctx_of("if (x) {AUTO332", 1, 9);
        assert!(c.is_open_curly_without_equals);
        let c = ctx_of("<a b={AUTO332", 1, 7);
        assert!(!c.is_open_curly_without_equals);
        let c = ctx_of("AUTO332", 1, 1);
        assert_eq!(c.char_at_pos, b' ');
    }
}
