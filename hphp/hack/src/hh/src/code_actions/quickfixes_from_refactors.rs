// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `quickfixes_from_refactors.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F7** (plan §7.3).
//!
//! Make sure to write tests any time you match against an error here
//! as correct behavior is dependent on matching specific strings and error codes (which can change).

use std::sync::Arc;

use super::await_expression;
use super::code_action_types as cat;
use super::extract_variable;
use crate::diagnostics_state::Diagnostic;
use crate::error_codes;
use crate::provider_context;
use crate::user_diagnostic;

fn select_refactoring_from_parse_error(e: &Diagnostic) -> Option<cat::FindRefactor> {
    let msg_str = &e.claim.1;
    match error_codes::parsing::of_enum(e.code) {
        Some(error_codes::parsing::T::ParsingError) => {
            if msg_str.as_slice()
                == b"`await` cannot be used as an expression in this location because it's conditionally executed."
            {
                Some(extract_variable::find)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn select_refactoring_from_type_error(e: &Diagnostic) -> Option<cat::FindRefactor> {
    match error_codes::typing::of_enum(e.code) {
        Some(error_codes::typing::T::DiscardedAwaitable) => Some(await_expression::find),
        _ => None,
    }
}

fn select_refactoring(e: &Diagnostic) -> Option<cat::FindRefactor> {
    match select_refactoring_from_parse_error(e) {
        Some(f) => Some(f),
        None => select_refactoring_from_type_error(e),
    }
}

fn quickfix_from_refactor(cat::Refactor(edit_data): cat::Refactor<'_>) -> cat::Quickfix<'_> {
    cat::Quickfix(edit_data)
}

pub fn find<'a>(
    ctx: &'a provider_context::T,
    entry: &'a Arc<provider_context::Entry>,
    e: &Diagnostic,
) -> Vec<cat::Quickfix<'a>> {
    match select_refactoring(e) {
        Some(find_refactors) => {
            let e_pos = user_diagnostic::get_pos(e);
            let refactors = find_refactors(entry, &e_pos, ctx);
            refactors.into_iter().map(quickfix_from_refactor).collect()
        }
        None => vec![],
    }
}
