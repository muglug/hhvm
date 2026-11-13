// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lsp_helpers.ml`. See `hh/PORTING.md`.
//!
//! A few helpful wrappers around LSP
//!
//! `sym_occ_kind_to_lsp_sym_info_kind` needs `Symbol_occurrence`, which has
//! no Rust module yet: it is compiled with the `port` feature only. The
//! functions on a `'a Pos.pos` take a `crate::pos::APos` (`Pos.t` or
//! `Pos.absolute`).
//!
//! The `Lsp.Error.LspException` of a URI that is not a file URL is the `Err`
//! of `lsp_uri_to_path` and of the functions that call it.

#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

use std::sync::atomic::AtomicIsize;

use crate::exception;
use crate::file_content;
use crate::file_url;
use crate::jsonrpc;
use crate::lsp::*;
use crate::lsp_fmt::*;
use crate::relative_path;
use crate::relative_path::Prefix;
use crate::relative_path::RelativePath;
use crate::yojson::safe as yojson;

static PROGRESS_AND_ACTION_REQUIRED_COUNTER: AtomicIsize = AtomicIsize::new(0);

/// `progress_and_actionRequired_counter` (an `int ref`)
pub fn progress_and_actionRequired_counter() -> &'static AtomicIsize {
    &PROGRESS_AND_ACTION_REQUIRED_COUNTER
}

// ~~ Conversions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

const URL_SCHEME_REGEX: &str = "^\\([a-zA-Z][a-zA-Z0-9+.-]+\\):";

/// `url_scheme_regex`: the `Str` regular expression, as its source. It is
/// matched by hand ([`url_scheme_regex_match`]).
///
/// this requires schemes with 2+ characters, so "c:\path" isn't considered a scheme
pub fn url_scheme_regex() -> &'static str {
    URL_SCHEME_REGEX
}

/// `Str.string_match url_scheme_regex s 0`, and `Str.matched_group 1 s`.
fn url_scheme_regex_match(s: &str) -> Option<&str> {
    let b = s.as_bytes();
    if !b.first().is_some_and(u8::is_ascii_alphabetic) {
        return None;
    }
    let len = 1 + b[1..]
        .iter()
        .take_while(|c| c.is_ascii_alphanumeric() || matches!(c, b'+' | b'.' | b'-'))
        .count();
    // `[a-zA-Z0-9+.-]+`, then `:` (which the set does not have, so the
    // longest run is the only candidate).
    if len >= 2 && b.get(len) == Some(&b':') {
        Some(&s[..len])
    } else {
        None
    }
}

pub fn lsp_uri_to_path(uri: &DocumentUri) -> Result<String, error::LspException> {
    let uri = string_of_uri(uri);
    match url_scheme_regex_match(&uri) {
        Some(scheme) => {
            if scheme == "file" {
                Ok(file_url::parse(&uri))
            } else {
                Err(error::LspException(error::T {
                    code: error::InvalidParams,
                    message: format!("Not a valid file url '{}'", uri),
                    data: None,
                }))
            }
        }
        None => Ok(uri),
    }
}

/// prefer [path_to_lsp_uri]
pub fn path_string_to_lsp_uri(path: &str, default_path: &str) -> DocumentUri {
    if path.is_empty() {
        // (A no-op in the OSS build.)
        crate::hack_event_logger::invariant_violation_bug(None, None, None, None, None, "missing path");
        crate::hh_logger::log(&format!(
            "missing path {}",
            exception::clean_stack(&exception::get_current_callstack_string(99))
        ));
        uri_of_string(&file_url::create(default_path))
    } else {
        uri_of_string(&file_url::create(path))
    }
}

/// If given a relative path with a dummy prefix, the file
/// uri will include a fake prefix like '/dummy_from_path_to_lsp_uri/'
pub fn path_to_lsp_uri(path: &RelativePath) -> DocumentUri {
    match relative_path::prefix(path) {
        Prefix::Root | Prefix::Hhi | Prefix::Tmp => {
            let absolute = relative_path::to_absolute(path);
            path_string_to_lsp_uri(&absolute, &absolute)
        }
        Prefix::Dummy => {
            // This is bad, we're saying something is a file path when it's not.
            // A particular case where we reach here is via `hh_single_type_check --ide-code-actions.
            // This is a symptom of overusing LSP types in internals of our language server.
            // TODO(T168350458): try to make this unreachable or behave more reasonably
            document_uri::Uri(relative_path::to_absolute(path))
        }
    }
}

pub fn lsp_textDocumentIdentifier_to_filename(
    identifier: &text_document_identifier::T,
) -> Result<String, error::LspException> {
    lsp_uri_to_path(&identifier.uri)
}

pub fn lsp_position_to_fc(Position { line, character }: &Position) -> file_content::position::T {
    file_content::position::from_zero_based(*line, *character)
}

pub fn lsp_range_to_fc(range: &Range) -> file_content::Range {
    file_content::Range {
        st: lsp_position_to_fc(&range.start),
        ed: lsp_position_to_fc(&range.end_),
    }
}

pub fn lsp_range_to_pos(
    line_to_offset: impl Fn(isize) -> isize,
    path: &RelativePath,
    range: &Range,
) -> crate::pos::T {
    let triple_of_endpoint = |Position { line, character }: &Position| {
        let bol = line_to_offset(*line);
        (*line, bol, bol + character)
    };
    // (OCaml evaluates the arguments from the last.)
    let pos_end = triple_of_endpoint(&range.end_);
    let pos_start = triple_of_endpoint(&range.start);
    crate::pos::make_from_lnum_bol_offset(path.clone(), pos_start, pos_end)
}

pub fn lsp_edit_to_fc(edit: &did_change::TextDocumentContentChangeEvent) -> file_content::TextEdit {
    file_content::TextEdit {
        range: edit.range.as_ref().map(lsp_range_to_fc),
        text: edit.text.clone(),
    }
}

pub fn apply_changes(
    text: &str,
    contentChanges: &[did_change::TextDocumentContentChangeEvent],
) -> Result<String, (String, exception::T)> {
    let edits: Vec<file_content::TextEdit> = contentChanges.iter().map(lsp_edit_to_fc).collect();
    file_content::edit_file(text, &edits)
}

/// The byte (an OCaml `char`) at the position.
pub fn get_char_from_lsp_position(content: &str, position: &Position) -> u8 {
    let fc_position = lsp_position_to_fc(position);
    file_content::get_char(content, file_content::get_offset(content, &fc_position))
}

pub fn apply_changes_unsafe(
    text: &str,
    contentChanges: &[did_change::TextDocumentContentChangeEvent],
) -> String {
    match apply_changes(text, contentChanges) {
        Ok(r) => r,
        Err((e, _stack)) => panic!("{}", e),
    }
}

pub fn sym_occ_kind_to_lsp_sym_info_kind(
    sym_occ_kind: &crate::symbol_occurrence::Kind,
) -> symbol_information::SymbolKind {
    use crate::symbol_occurrence::Kind;
    use symbol_information::SymbolKind;
    match sym_occ_kind {
        Kind::Class(..) => SymbolKind::Class,
        Kind::BuiltInType(..) => SymbolKind::Class,
        Kind::Function => SymbolKind::Function,
        Kind::Method(..) => SymbolKind::Method,
        Kind::LocalVar => SymbolKind::Variable,
        Kind::TypeVar => SymbolKind::TypeParameter,
        Kind::Property(..) => SymbolKind::Property,
        Kind::XhpLiteralAttr(..) => SymbolKind::Property,
        Kind::ClassConst(..) => SymbolKind::TypeParameter,
        Kind::Typeconst(..) => SymbolKind::TypeParameter,
        Kind::GConst => SymbolKind::Constant,
        Kind::Attribute(..) => SymbolKind::Class,
        Kind::EnumClassLabel(..) => SymbolKind::EnumMember,
        Kind::Keyword(..) => SymbolKind::Null,
        Kind::PureFunctionContext => SymbolKind::Null,
        Kind::BestEffortArgument(..) => SymbolKind::Null,
        Kind::HhFixme => SymbolKind::Null,
        Kind::HhIgnore => SymbolKind::Null,
        Kind::Module => SymbolKind::Module,
    }
}

/// Correctly handles our various positions:
/// - real positions
/// - .hhconfig error positions, which have dummy start/ends
/// - and [Pos.none]
///
/// Special handling is required, as the LSP
/// specification requires line and character >= 0, and VSCode silently
/// drops diagnostics that violate the spec in this way
///
/// (`Pos.equal_pos equal pos (Pos.make_from (Pos.filename pos))`: the files
/// are equal by `equal`, and the span is the dummy one. A position is always
/// compressed here, so the span alone says what the OCaml representation
/// says.)
pub fn hack_pos_to_lsp_range<P: crate::pos::APos>(
    equal: impl Fn(&P::File, &P::File) -> bool,
    pos: &P,
) -> Range {
    // .hhconfig errors are Positions with a filename, but dummy start/end
    // positions. Handle that case - and Pos.none - specially, as the LSP
    // specification requires line and character >= 0, and VSCode silently
    // drops diagnostics that violate the spec in this way
    let file = crate::pos::filename(pos);
    if equal(&file, &file) && pos.raw_span() == oxidized::pos_span_raw::PosSpanRaw::make_dummy() {
        Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end_: Position {
                line: 0,
                character: 0,
            },
        }
    } else {
        let (line1, col1, line2, col2) = crate::pos::destruct_range_one_based(pos);
        Range {
            start: Position {
                line: line1 - 1,
                character: col1 - 1,
            },
            end_: Position {
                line: line2 - 1,
                character: col2 - 1,
            },
        }
    }
}

/// You probably want [hack_pos_to_lsp_range].
/// Equivalent to `[hack_pos_to_lsp_range] sans handling of special positions and with the following transformation:
/// {r with start = {line = r.start.line + 1; character = r.start.character + 1}; end_ = {r.end_ with line = r.end_.line + 1}}
/// where `r` is a range produced by [hack_pos_to_lsp_range]
pub fn hack_pos_to_lsp_range_adjusted<P: crate::pos::APos>(p: &P) -> Range {
    let (line_start, line_end, character_start, character_end) = crate::pos::info_pos_extended(p);
    let start_position = Position {
        line: line_start,
        character: character_start,
    };
    let end_position = Position {
        line: line_end,
        character: character_end,
    };
    Range {
        start: start_position,
        end_: end_position,
    }
}

// ~~ Range calculations ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// We need to do intersection and other calculations on ranges.
/// The functions in the following module all assume LSP 0-based ranges,
/// and assume without testing that a range's start is equal to or before
/// its end.
pub fn pos_compare(p1: &Position, p2: &Position) -> isize {
    if p1.line < p2.line {
        -1
    } else if p1.line > p2.line {
        1
    } else {
        p1.character - p2.character
    }
}

/// Given a "selection" range A..B and a "squiggle" range a..b, how do they overlap?
/// There are 12 ways to order the four letters ABab, of which six
/// satisfy both A<=B and a<=b. Here they are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeOverlap {
    /// ABab
    SelectionBeforeStartOfSquiggle,
    /// AaBb
    SelectionOverlapsStartOfSquiggle,
    /// AabB
    SelectionCoversWholeSquiggle,
    /// aABb
    SelectionInMiddleOfSquiggle,
    /// aAbB
    SelectionOverlapsEndOfSquiggle,
    /// abAB
    SelectionAfterEndOfSquiggle,
}

/// Computes how two ranges "selection" and "squiggle" overlap
pub fn get_range_overlap(selection: &Range, squiggle: &Range) -> RangeOverlap {
    use RangeOverlap::*;
    let selStart_leq_squiggleStart = pos_compare(&selection.start, &squiggle.start) <= 0;
    let selStart_leq_squiggleEnd = pos_compare(&selection.start, &squiggle.end_) <= 0;
    let selEnd_lt_squiggleStart = pos_compare(&selection.end_, &squiggle.start) < 0;
    let selEnd_lt_squiggleEnd = pos_compare(&selection.end_, &squiggle.end_) < 0;
    // Q. Why does it test "<=" for the first two and "<" for the last two?
    // Intuitively you can trust that it has something to do with how ranges are
    // inclusive at their start and exclusive at their end. But the real reason
    // is just that I did an exhaustive case analysis to look at all cases where
    // A,B,a,b might be equal, and decided which outcome I wanted for each of them
    // because of how I'm going to treat them in other functions, and retrofitted
    // those answers into this function. For instance, if squiggleStart==selEnd,
    // I'll want to handle it in the same way as squiggleStart<selEnd<squiggleEnd.
    // The choices of "leq" and "lt" in this function embody those answers.
    match (
        selStart_leq_squiggleStart,
        selStart_leq_squiggleEnd,
        selEnd_lt_squiggleStart,
        selEnd_lt_squiggleEnd,
    ) {
        (true, true, true, true) => SelectionBeforeStartOfSquiggle,
        (true, true, false, true) => SelectionOverlapsStartOfSquiggle,
        (true, true, false, false) => SelectionCoversWholeSquiggle,
        (false, true, false, true) => SelectionInMiddleOfSquiggle,
        (false, true, false, false) => SelectionOverlapsEndOfSquiggle,
        (false, false, false, false) => SelectionAfterEndOfSquiggle,
        (true, false, _, _) => panic!("sel.start proves squiggle.start > squiggle.end_"),
        (_, _, true, false) => panic!("sel.end proves squiggle.start > squiggle.end_"),
        (false, _, true, _) => panic!("squiggle.start proves sel.start > sel.end_"),
        (_, false, _, true) => panic!("squiggle.end_ proves sel.start > sel.end_"),
    }
}

/// this structure models a change where a certain range is replaced with
/// a block of text. For instance, if you merely insert a single character,
/// then remove_range.start==remove_range.end_ and insert_lines=0
/// and insert_chars_on_final_line=1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RangeReplace {
    pub remove_range: Range,
    pub insert_lines: isize,
    pub insert_chars_on_final_line: isize,
}

/// If you have a position "p", and some range before this point is replaced with
/// text of a certain number of lines, the last line having a certain number of characters,
/// then how will the position be shifted?
/// Note: this function assumes but doesn't verify that the range ends on or before
/// the position.
pub fn update_pos_due_to_prior_replace(p: &Position, replace: &RangeReplace) -> Position {
    if replace.remove_range.end_.line < p.line {
        // The replaced range doesn't touch the position, so position merely gets shifted up/down
        let line = p.line - (replace.remove_range.end_.line - replace.remove_range.start.line)
            + replace.insert_lines;
        Position { line, ..*p }
    } else if replace.insert_lines > 0 {
        // The position is on the final line and multiple lines were inserted
        let line = p.line - (replace.remove_range.end_.line - replace.remove_range.start.line)
            + replace.insert_lines;
        let character =
            replace.insert_chars_on_final_line + (p.character - replace.remove_range.end_.character);
        Position { line, character }
    } else {
        // The position is on the line where a few characters were inserted
        let line = p.line - (replace.remove_range.end_.line - replace.remove_range.start.line);
        let character = replace.remove_range.start.character
            + replace.insert_chars_on_final_line
            + (p.character - replace.remove_range.end_.character);
        Position { line, character }
    }
}

/// If you have a squiggle, and some range in the document is replaced with a block
/// some lines long and with insert_chars on the final line, then what's the new
/// range of the squiggle?
pub fn update_range_due_to_replace(squiggle: &Range, replace: &RangeReplace) -> Option<Range> {
    use RangeOverlap::*;
    match get_range_overlap(&replace.remove_range, squiggle) {
        SelectionBeforeStartOfSquiggle => {
            let start = update_pos_due_to_prior_replace(&squiggle.start, replace);
            let end_ = update_pos_due_to_prior_replace(&squiggle.end_, replace);
            Some(Range { start, end_ })
        }
        SelectionOverlapsStartOfSquiggle => {
            let line = replace.remove_range.start.line + replace.insert_lines;
            let character = if replace.insert_lines == 0 {
                replace.remove_range.start.character + replace.insert_chars_on_final_line
            } else {
                replace.insert_chars_on_final_line
            };
            let start = Position { line, character };
            let end_ = update_pos_due_to_prior_replace(&squiggle.end_, replace);
            Some(Range { start, end_ })
        }
        SelectionCoversWholeSquiggle => None,
        SelectionInMiddleOfSquiggle => {
            let start = squiggle.start;
            let end_ = update_pos_due_to_prior_replace(&squiggle.end_, replace);
            Some(Range { start, end_ })
        }
        SelectionOverlapsEndOfSquiggle => {
            let start = squiggle.start;
            let end_ = replace.remove_range.start;
            Some(Range { start, end_ })
        }
        SelectionAfterEndOfSquiggle => Some(*squiggle),
    }
}

/// Moves all diagnostics in response to an LSP change.
/// The change might insert text before a diagnostic squiggle (so the squiggle
/// has to be moved down or to the right); it might delete text before the squiggle;
/// it might modify text inside the squiggle; it might replace text that overlaps
/// the squiggle in which case the squiggle gets truncated/moved; it might replace
/// the squiggle in its entirety in which case the squiggle gets removed.
/// Note that an LSP change is actually a set of changes, applied in order.
pub fn update_diagnostics_due_to_change(
    diagnostics: &[publish_diagnostics::Diagnostic],
    change: &did_change::Params,
) -> Vec<publish_diagnostics::Diagnostic> {
    let replace_of_change = |change: &did_change::TextDocumentContentChangeEvent| match change
        .range
    {
        None => None,
        Some(remove_range) => {
            let offset = change.text.len() as isize;
            let pos = file_content::offset_to_position(&change.text, offset);
            let (insert_lines, insert_chars_on_final_line) =
                file_content::position::line_column_zero_based(&pos);
            Some(RangeReplace {
                remove_range,
                insert_lines,
                insert_chars_on_final_line,
            })
        }
    };
    let apply_replace = |diagnostic_opt: Option<publish_diagnostics::Diagnostic>,
                         replace_opt: &Option<RangeReplace>| {
        match (diagnostic_opt, replace_opt) {
            (Some(diagnostic), Some(replace)) => {
                let range = update_range_due_to_replace(&diagnostic.range, replace);
                range.map(|range| publish_diagnostics::Diagnostic {
                    range,
                    ..diagnostic
                })
            }
            _ => None,
        }
    };
    let replaces: Vec<Option<RangeReplace>> =
        change.contentChanges.iter().map(replace_of_change).collect();
    let apply_all_replaces = |diagnostic: &publish_diagnostics::Diagnostic| {
        replaces
            .iter()
            .fold(Some(diagnostic.clone()), apply_replace)
    };
    diagnostics.iter().filter_map(apply_all_replaces).collect()
}

// ~~ Accessors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn get_root(p: &initialize::Params) -> Result<String, error::LspException> {
    match (&p.rootUri, &p.rootPath) {
        (Some(uri), _) => lsp_uri_to_path(uri),
        (None, Some(path)) => Ok(path.clone()),
        (None, None) => panic!("Initialize params missing root"),
    }
}

pub fn supports_status(p: &initialize::Params) -> bool {
    p.client_capabilities.window.status
}

pub fn supports_snippets(p: &initialize::Params) -> bool {
    p.client_capabilities
        .textDocument
        .completion
        .completionItem
        .snippetSupport
}

pub fn supports_connectionStatus(p: &initialize::Params) -> bool {
    p.client_capabilities.telemetry.connectionStatus
}

// ~~ Wrappers for some LSP methods ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn telemetry(
    writer: &jsonrpc::Writer<'_>,
    type_: message_type::T,
    extras: Vec<(String, yojson::T)>,
    message: &str,
) {
    let params = log_message::LogMessageParams {
        type_,
        message: message.to_string(),
    };
    let notification = LspNotification::TelemetryNotification(params, extras);
    writer(print_lsp_notification(&notification))
}

/// `extras` defaults to `[]`.
pub fn telemetry_error(
    writer: &jsonrpc::Writer<'_>,
    extras: Option<Vec<(String, yojson::T)>>,
    message: &str,
) {
    let extras = extras.unwrap_or_default();
    telemetry(writer, message_type::ErrorMessage, extras, message)
}

/// `extras` defaults to `[]`.
pub fn telemetry_log(
    writer: &jsonrpc::Writer<'_>,
    extras: Option<Vec<(String, yojson::T)>>,
    message: &str,
) {
    let extras = extras.unwrap_or_default();
    telemetry(writer, message_type::LogMessage, extras, message)
}

pub fn log(writer: &jsonrpc::Writer<'_>, type_: message_type::T, message: &str) {
    let params = log_message::LogMessageParams {
        type_,
        message: message.to_string(),
    };
    let notification = LspNotification::LogMessageNotification(params);
    writer(print_lsp_notification(&notification))
}

pub fn log_error(writer: &jsonrpc::Writer<'_>, message: &str) {
    log(writer, message_type::ErrorMessage, message)
}

pub fn log_warning(writer: &jsonrpc::Writer<'_>, message: &str) {
    log(writer, message_type::WarningMessage, message)
}

pub fn log_info(writer: &jsonrpc::Writer<'_>, message: &str) {
    log(writer, message_type::InfoMessage, message)
}

pub fn showMessage(writer: &jsonrpc::Writer<'_>, type_: message_type::T, message: &str) {
    let params = show_message::ShowMessageParams {
        type_,
        message: message.to_string(),
    };
    let notification = LspNotification::ShowMessageNotification(params);
    writer(print_lsp_notification(&notification))
}

pub fn showMessage_info(writer: &jsonrpc::Writer<'_>, message: &str) {
    showMessage(writer, message_type::InfoMessage, message)
}

pub fn showMessage_warning(writer: &jsonrpc::Writer<'_>, message: &str) {
    showMessage(writer, message_type::WarningMessage, message)
}

pub fn showMessage_error(writer: &jsonrpc::Writer<'_>, message: &str) {
    showMessage(writer, message_type::ErrorMessage, message)
}

pub fn title_of_command_or_action<A>(x: &code_action::CommandOrAction_<A>) -> String {
    match x {
        code_action::CommandOrAction_::Command(command::T { title, .. }) => title.clone(),
        code_action::CommandOrAction_::Action(code_action::T { title, .. }) => title.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pos(line: isize, character: isize) -> Position {
        Position { line, character }
    }

    fn range(a: (isize, isize), b: (isize, isize)) -> Range {
        Range {
            start: pos(a.0, a.1),
            end_: pos(b.0, b.1),
        }
    }

    fn diagnostic(r: Range) -> publish_diagnostics::Diagnostic {
        publish_diagnostics::Diagnostic {
            range: r,
            severity: None,
            code: publish_diagnostics::DiagnosticCode::NoCode,
            source: None,
            message: "m".to_string(),
            relatedInformation: vec![],
            relatedLocations: vec![],
            data: None,
        }
    }

    #[test]
    fn uris() {
        assert_eq!(lsp_uri_to_path(&uri_of_string("file:///a/b%20c")).unwrap(), "/a/b c");
        assert_eq!(lsp_uri_to_path(&uri_of_string("c:\\x")).unwrap(), "c:\\x");
        assert_eq!(lsp_uri_to_path(&uri_of_string("/plain")).unwrap(), "/plain");
        let e = lsp_uri_to_path(&uri_of_string("http://x")).unwrap_err().0;
        assert_eq!(e.code, error::InvalidParams);
        assert_eq!(e.message, "Not a valid file url 'http://x'");
        assert_eq!(
            path_string_to_lsp_uri("/a b", "/d"),
            uri_of_string("file:///a%20b")
        );
        assert_eq!(path_string_to_lsp_uri("", "/d"), uri_of_string("file:///d"));
        assert_eq!(
            path_to_lsp_uri(&relative_path::create(Prefix::Dummy, "x/y.php")),
            uri_of_string("x/y.php")
        );
        assert_eq!(url_scheme_regex_match("ab:x"), Some("ab"));
        assert_eq!(url_scheme_regex_match("a+b.c-d:"), Some("a+b.c-d"));
        assert_eq!(url_scheme_regex_match("1a:"), None);
    }

    #[test]
    fn hack_positions() {
        // (A `Dummy` path needs no prefix to be set.)
        let file = relative_path::create(Prefix::Dummy, "a.php");
        // Line 3, bytes 4 to 7 (half open) of the line, which starts at 20.
        let p = crate::pos::make_from_lnum_bol_offset(file.clone(), (3, 20, 24), (3, 20, 27));
        assert_eq!(hack_pos_to_lsp_range(relative_path::equal, &p), range((2, 4), (2, 7)));
        // Start one-based, end closed.
        assert_eq!(hack_pos_to_lsp_range_adjusted(&p), range((3, 5), (3, 7)));
        // `Pos.none`, and the dummy span that .hhconfig errors have.
        assert_eq!(
            hack_pos_to_lsp_range(relative_path::equal, &crate::pos::none),
            range((0, 0), (0, 0))
        );
        assert_eq!(
            hack_pos_to_lsp_range(relative_path::equal, &crate::pos::make_from(file.clone())),
            range((0, 0), (0, 0))
        );
        let absolute = crate::pos::to_absolute(&crate::pos::make_from(relative_path::create(
            Prefix::Dummy,
            "/r/.hhconfig",
        )));
        assert_eq!(
            hack_pos_to_lsp_range(|a: &String, b: &String| a == b, &absolute),
            range((0, 0), (0, 0))
        );
        // The line given to `line_to_offset` is the LSP (0-based) one, and so
        // is the line of the position, as in OCaml.
        let back = lsp_range_to_pos(|line| line * 10, &file, &range((2, 4), (2, 7)));
        assert!(crate::pos::equal(
            &back,
            &crate::pos::make_from_lnum_bol_offset(file, (2, 20, 24), (2, 20, 27))
        ));
    }

    #[test]
    fn overlaps() {
        use RangeOverlap::*;
        let sel = range((1, 5), (1, 8));
        assert_eq!(get_range_overlap(&sel, &range((1, 9), (1, 10))), SelectionBeforeStartOfSquiggle);
        assert_eq!(get_range_overlap(&sel, &range((1, 6), (1, 10))), SelectionOverlapsStartOfSquiggle);
        assert_eq!(get_range_overlap(&sel, &range((1, 5), (1, 8))), SelectionCoversWholeSquiggle);
        assert_eq!(get_range_overlap(&sel, &range((1, 0), (1, 10))), SelectionInMiddleOfSquiggle);
        assert_eq!(get_range_overlap(&sel, &range((1, 0), (1, 6))), SelectionOverlapsEndOfSquiggle);
        assert_eq!(get_range_overlap(&sel, &range((0, 0), (1, 1))), SelectionAfterEndOfSquiggle);
        // A squiggle that starts where the selection ends overlaps its start.
        assert_eq!(get_range_overlap(&sel, &range((1, 8), (1, 9))), SelectionOverlapsStartOfSquiggle);
    }

    #[test]
    fn diagnostics_follow_changes() {
        let ds = vec![
            diagnostic(range((2, 4), (2, 6))),
            diagnostic(range((0, 0), (0, 3))),
            diagnostic(range((5, 0), (5, 1))),
        ];
        let change = did_change::DidChangeTextDocumentParams {
            textDocument: versioned_text_document_identifier::T {
                uri: uri_of_string("file:///a"),
                version: 2,
            },
            contentChanges: vec![
                // Insert a line and two characters at the start of line 1.
                did_change::TextDocumentContentChangeEvent {
                    range: Some(range((1, 0), (1, 0))),
                    rangeLength: None,
                    text: "x\nyz".to_string(),
                },
                // Delete the whole of the first squiggle's new line.
                did_change::TextDocumentContentChangeEvent {
                    range: Some(range((5, 0), (7, 0))),
                    rangeLength: None,
                    text: "".to_string(),
                },
            ],
        };
        let updated = update_diagnostics_due_to_change(&ds, &change);
        assert_eq!(
            updated.iter().map(|d| d.range).collect::<Vec<_>>(),
            vec![range((3, 4), (3, 6)), range((0, 0), (0, 3))]
        );
        // A change without a range removes every diagnostic.
        let full = did_change::DidChangeTextDocumentParams {
            contentChanges: vec![did_change::TextDocumentContentChangeEvent {
                range: None,
                rangeLength: None,
                text: "".to_string(),
            }],
            ..change
        };
        assert!(update_diagnostics_due_to_change(&ds, &full).is_empty());
    }

    #[test]
    fn changes() {
        let change = did_change::TextDocumentContentChangeEvent {
            range: Some(range((0, 1), (0, 2))),
            rangeLength: None,
            text: "XY".to_string(),
        };
        assert_eq!(apply_changes_unsafe("abc", &[change]), "aXYc");
        assert_eq!(get_char_from_lsp_position("ab\ncd", &pos(1, 1)), b'd');
    }

    #[test]
    fn writers() {
        let out = std::cell::RefCell::new(vec![]);
        let writer = |j: yojson::T| out.borrow_mut().push(yojson::to_string(&j));
        let writer: &jsonrpc::Writer<'_> = &writer;
        telemetry_error(writer, None, "oops");
        telemetry_log(
            writer,
            Some(vec![("k".to_string(), yojson::T::Int(1))]),
            "hi",
        );
        log_warning(writer, "w");
        showMessage_info(writer, "i");
        assert_eq!(
            out.borrow().clone(),
            vec![
                r#"{"jsonrpc":"2.0","method":"telemetry/event","params":{"type":1,"message":"oops"}}"#,
                r#"{"jsonrpc":"2.0","method":"telemetry/event","params":{"type":4,"message":"hi","k":1}}"#,
                r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":2,"message":"w"}}"#,
                r#"{"jsonrpc":"2.0","method":"window/showMessage","params":{"type":3,"message":"i"}}"#,
            ]
        );
    }
}
