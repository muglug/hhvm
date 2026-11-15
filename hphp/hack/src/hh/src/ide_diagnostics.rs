// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/ide_diagnostics.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use crate::classish_positions;
use crate::client_ide_message;
use crate::client_ide_message::FinalizedDiagnostic;
use crate::pos::Absolute;
use crate::provider_context;
use crate::quickfix::HintStyle;
use crate::user_diagnostic;

fn convert_error(
    classish_positions: &classish_positions::T<Absolute>,
    (error, diagnostic_hash): (FinalizedDiagnostic, isize),
) -> client_ide_message::Diagnostic {
    let quickfixes = user_diagnostic::quickfixes(&error);
    let related_hints: Vec<Absolute> = quickfixes
        .iter()
        .flat_map(|quickfix| quickfix.hint_styles.iter())
        .filter_map(|hint_style| match hint_style {
            HintStyle::HintStyleSilent(_) => None,
            HintStyle::HintStyleHint(p) => classish_positions::find(p, classish_positions),
        })
        .collect();
    client_ide_message::Diagnostic {
        diagnostic_error: error,
        diagnostic_related_hints: related_hints,
        diagnostic_hash,
    }
}

/// Convert a list of [Diagnostics.finalized_diagnostic] to [ClientIdeMessage.diagnostic]
pub fn convert(
    _ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    errors: Vec<(FinalizedDiagnostic, isize)>,
) -> Vec<client_ide_message::Diagnostic> {
    // `Ast_provider.compute_cst ~ctx ~entry` (it sets the source text of the
    // entry, so the positions are always extracted).
    let (source_text, tree) = crate::ast_provider::compute_cst(entry);
    let classish_positions = classish_positions::extract(&tree, &source_text, &entry.path);
    let classish_positions = classish_positions::map(crate::pos::to_absolute, &classish_positions);
    errors
        .into_iter()
        .map(|error| convert_error(&classish_positions, error))
        .collect()
}
