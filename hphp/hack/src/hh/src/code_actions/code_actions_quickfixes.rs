// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `code_actions_quickfixes.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F7** (plan §7.3).
//!
//! The quickfixes are those the typechecker attaches to its diagnostics
//! (`User_diagnostic.quickfixes`, `oxidized::quickfix::Quickfix`), and the
//! refactors that `Quickfixes_from_refactors` offers for some diagnostics.

use std::rc::Rc;
use std::sync::Arc;

use super::code_action_types as cat;
use super::code_actions_edits_add_attribute;
use super::quickfixes_from_refactors;
use crate::classish_positions;
use crate::diagnostics_state;
use crate::diagnostics_state::Diagnostic;
use crate::hack_event_logger;
use crate::pos::Pos;
use crate::provider_context;
use crate::quickfix;
use crate::relative_path::RelativePath;
use crate::tast_provider;
use crate::user_diagnostic;

fn text_edits(
    ctx: &provider_context::T,
    entry: &provider_context::Entry,
    classish_positions: &classish_positions::T<Pos>,
    quickfix: &quickfix::Quickfix<Pos>,
) -> Vec<cat::Edit> {
    match &quickfix.edits {
        quickfix::Edits::Eager(eager_edits) => eager_edits
            .iter()
            .map(|(text, pos)| cat::Edit {
                pos: pos.clone(),
                text: text.clone(),
            })
            .collect(),
        quickfix::Edits::ClassishEnd {
            new_text: classish_end_new_text,
            name: classish_end_name,
        } => {
            match classish_positions::find(
                &classish_positions::CPos::ClassishEndOfBody(classish_end_name.clone()),
                classish_positions,
            ) {
                Some(classish_end) => vec![cat::Edit {
                    pos: classish_end,
                    text: classish_end_new_text.clone(),
                }],
                None => {
                    hack_event_logger::invariant_violation_bug(
                        None,
                        None,
                        Some(classish_end_name),
                        None,
                        None,
                        "Could not find class position for quickfix",
                    );
                    vec![]
                }
            }
        }
        quickfix::Edits::AddFunctionAttribute {
            function_pos,
            attribute_name,
        } => code_actions_edits_add_attribute::create(ctx, entry, function_pos, attribute_name),
    }
}

fn convert_quickfix<'a>(
    ctx: &'a provider_context::T,
    entry: &'a provider_context::Entry,
    path: &RelativePath,
    classish_positions: &Rc<classish_positions::T<Pos>>,
    quickfix: quickfix::Quickfix<Pos>,
) -> cat::Quickfix<'a> {
    let classish_positions = Rc::clone(classish_positions);
    let title = quickfix.title.clone();
    let path = path.clone();
    let edits: cat::LazyEdits<'a> = Box::new(move || {
        cat::singleton(path, text_edits(ctx, entry, &classish_positions, &quickfix))
    });
    cat::Quickfix(cat::EditData {
        title,
        edits,
        selection: None,
        trigger_inline_suggest: false,
    })
}

fn quickfix_positions_for_error(
    classish_positions: &classish_positions::T<Pos>,
    error: &Diagnostic,
) -> Vec<Pos> {
    let quickfixes = user_diagnostic::quickfixes(error);
    let hint_styles = quickfixes.iter().flat_map(|q| q.hint_styles.iter());
    let available_positions = hint_styles.filter_map(|h| match h {
        quickfix::HintStyle::HintStyleSilent(p) | quickfix::HintStyle::HintStyleHint(p) => {
            classish_positions::find(p, classish_positions)
        }
    });
    let mut result = vec![user_diagnostic::get_pos(error)];
    result.extend(available_positions);
    result
}

fn errors_to_quickfixes<'a>(
    ctx: &'a provider_context::T,
    entry: &'a Arc<provider_context::Entry>,
    errors: diagnostics_state::T,
    path: &RelativePath,
    classish_positions: &Rc<classish_positions::T<Pos>>,
    selection: &Pos,
) -> Vec<cat::Quickfix<'a>> {
    let errors = diagnostics_state::get_diagnostic_list(Some(false), errors);
    let errors_here: Vec<&Diagnostic> = errors
        .iter()
        .filter(|e| {
            let available_positions = quickfix_positions_for_error(classish_positions, e);
            available_positions
                .iter()
                .any(|p| crate::pos::contains(p, selection))
        })
        .collect();
    let quickfixes = errors_here
        .iter()
        .flat_map(|e| user_diagnostic::quickfixes(e));
    let mut standard_quickfixes: Vec<cat::Quickfix<'a>> = quickfixes
        .map(|q| convert_quickfix(ctx, entry, path, classish_positions, q))
        .collect();
    let quickfixes_from_refactors = errors_here
        .iter()
        .flat_map(|e| quickfixes_from_refactors::find(ctx, entry, e));
    standard_quickfixes.extend(quickfixes_from_refactors);
    standard_quickfixes
}

/// The classish positions of the entry (`Classish_positions.extract`).
fn classish_positions_of(entry: &provider_context::Entry) -> classish_positions::T<Pos> {
    let (source_text, tree) = crate::identify_symbol_service::compute_cst(entry);
    // `match entry.source_text with Some .. -> extract | None -> empty`:
    // `compute_cst` computes (and caches) the source text, so it is `Some`.
    classish_positions::extract(&tree, &source_text, &entry.path)
}

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    pos: &Pos,
    ctx: &'a provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
) -> Vec<cat::Quickfix<'a>> {
    // (Shared with the lazy edits, which close over them as in OCaml.)
    let classish_positions = Rc::new(classish_positions_of(entry));
    let tast_provider::ComputeTastAndErrors { diagnostics, .. } =
        tast_provider::compute_tast_and_errors_quarantined(ctx, entry, error_filter);
    let path = &entry.path;
    errors_to_quickfixes(ctx, entry, diagnostics, path, &classish_positions, pos)
}
