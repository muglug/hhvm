// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/code_actions_refactors.ml`.
//! See `hh/PORTING.md`.
//!
//! The registry of the refactors, in the OCaml's order.

use std::sync::Arc;

use super::add_doc_comment;
use super::await_expression;
use super::code_action_types as cat;
use super::extract_classish;
use super::extract_method;
use super::extract_shape_type;
use super::extract_variable;
use super::flip_around_comma;
use super::inline_method;
use super::inline_variable;
use super::override_method;
use crate::pos::Pos;
use crate::provider_context;

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    pos: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    let variable_actions = {
        let actions = inline_variable::find(entry, pos, ctx);
        if actions.is_empty() {
            extract_variable::find(entry, pos, ctx)
        } else {
            actions
        }
    };
    // (`@` is right-associative and OCaml evaluates the operands of an
    // application from the last: the `find`s run from the last to the
    // first. Their only effects are the caches of the entry, so the order
    // is not observable; they run here in the order of the list.)
    let mut result = await_expression::find(entry, pos, ctx);
    result.extend(override_method::find(entry, pos, ctx));
    result.extend(variable_actions);
    result.extend(inline_method::find(entry, pos, ctx));
    result.extend(extract_method::find(entry, pos, ctx));
    result.extend(extract_classish::find(entry, pos, ctx));
    result.extend(extract_shape_type::find(entry, pos, ctx));
    result.extend(flip_around_comma::find(entry, pos, ctx));
    result.extend(add_doc_comment::find(entry, pos, ctx));
    result
}
