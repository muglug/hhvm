// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/code_actions_edits_add_attribute.ml`.
//! See `hh/PORTING.md`.

use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;

use super::code_action_types as cat;
use super::code_actions_utils as cu;
use crate::full_fidelity_source_text as source_text;
use crate::pos::Pos;
use crate::provider_context;

fn find_function_at_pos<'t>(root: &'t PositionedSyntax, function_pos: &Pos) -> Option<&'t PositionedSyntax> {
    let (start_offset, _end_offset) = crate::pos::info_raw(function_pos);
    let nodes = cu::parentage(root, start_offset);
    nodes.into_iter().find(|node| {
        matches!(
            node.syntax,
            SyntaxVariant::MethodishDeclaration(_) | SyntaxVariant::FunctionDeclaration(_)
        )
    })
}

fn get_attribute_insert_info(function_node: &PositionedSyntax) -> (Option<isize>, bool) {
    let get_insert_info_from_attribute_spec = |attribute_spec: &PositionedSyntax| match &attribute_spec.syntax {
        SyntaxVariant::Missing => {
            let offset = cu::start_offset(function_node);
            (Some(offset), false)
        }
        SyntaxVariant::OldAttributeSpecification(x) => match &x.old_attribute_specification_attributes.syntax {
            SyntaxVariant::SyntaxList(attrs) => match attrs.last() {
                Some(last_attr) => {
                    // end_offset points to the last character; +1 to insert after it
                    let offset = cu::end_offset(last_attr) + 1;
                    (Some(offset), true)
                }
                // Empty attribute list `<<>>` doesn't parse, so this is unreachable
                None => (None, false),
            },
            _ => (None, false),
        },
        _ => (None, false),
    };
    match &function_node.syntax {
        SyntaxVariant::MethodishDeclaration(x) => get_insert_info_from_attribute_spec(&x.methodish_attribute),
        SyntaxVariant::FunctionDeclaration(x) => get_insert_info_from_attribute_spec(&x.function_attribute_spec),
        _ => (None, false),
    }
}

fn create_attribute_text(attribute_name: &str, has_existing_attrs: bool, indent: &str) -> String {
    if has_existing_attrs {
        format!(", {}", attribute_name)
    } else {
        format!("<<{}>>\n{}", attribute_name, indent)
    }
}

/// Generates text edits for adding attributes to functions and methods.
/// Used by quickfixes that need to insert attributes like __NeedsConcrete.
pub fn create(
    _ctx: &provider_context::T,
    entry: &provider_context::Entry,
    function_pos: &Pos,
    attribute_name: &str,
) -> Vec<cat::Edit> {
    let (source_text, root) = crate::ast_provider::compute_cst(entry);
    let path = &entry.path;
    // (`entry.source_text` is set by `compute_cst`.)
    match find_function_at_pos(&root, function_pos) {
        None => vec![],
        Some(function_node) => match get_attribute_insert_info(function_node) {
            (Some(offset), has_existing_attrs) => {
                let indent = if has_existing_attrs {
                    String::new()
                } else {
                    let (_line, col) = cu::start_position(&source_text, function_node);
                    // col is 1-indexed, subtract 1 for 0-indexed indentation width
                    " ".repeat((col - 1).max(0) as usize)
                };
                let text = create_attribute_text(attribute_name, has_existing_attrs, &indent);
                let pos = source_text::relative_pos(path, &source_text, offset, offset);
                vec![cat::Edit { pos, text }]
            }
            (None, _) => vec![],
        },
    }
}
