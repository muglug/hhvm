// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/add_doc_comment.ml`.
//! See `hh/PORTING.md`.

use std::sync::Arc;

use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::token_kind::TokenKind;

use super::code_action_types as cat;
use super::code_actions_utils as cu;
use crate::ast_provider;
use crate::full_fidelity_source_text as source_text;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;

fn edits_of_candidate(
    path: &RelativePath,
    line_to_offset: &dyn Fn(isize) -> isize,
    (line_minus_1, character_plus_1): (isize, isize),
) -> cat::Edits {
    let line = line_minus_1 + 1;
    let character = character_plus_1 - 1;
    let edit = {
        let text = "/**\n * ${0:}\n */\n".to_string();
        let pos = {
            let offset = line_to_offset(line);
            let pos_start = (line, offset, offset + character);
            crate::pos::make_from_lnum_bol_offset(path.clone(), pos_start, pos_start)
        };
        cat::Edit { pos, text }
    };
    cat::singleton(path.clone(), vec![edit])
}

fn find_candidate<'t>(pos: &Pos, st: &source_text::T, root: &'t PositionedSyntax) -> Option<&'t PositionedSyntax> {
    let (line, start, _) = crate::pos::info_pos(pos);
    let offset = source_text::position_to_offset(st, (line, start + 1));
    let nodes = cu::parentage(root, offset);
    let nodes_and_kinds: Vec<(&PositionedSyntax, TokenKind)> = nodes
        .into_iter()
        .filter_map(|node| cu::leading_token(node).map(|token| (node, token.kind)))
        .collect();
    match &nodes_and_kinds[..] {
        [
            (_, TokenKind::Name),
            (
                named_node,
                TokenKind::Function
                | TokenKind::Class
                | TokenKind::Interface
                | TokenKind::Enum
                | TokenKind::Newtype
                | TokenKind::Type
                | TokenKind::Trait,
            ),
            ..,
        ] => {
            let has_doc_comment =
                crate::docblock_finder::get_docblock(&source_text::source_text(st), named_node).is_some();
            if !has_doc_comment { Some(named_node) } else { None }
        }
        // (`(_, Name) :: (_, <every other kind>) :: _ -> None`)
        _ => None,
    }
}

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    pos: &Pos,
    _ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    let source_text = ast_provider::compute_source_text(entry);
    let path = entry.path.clone();
    let (_, positioned_tree) = crate::ast_provider::compute_cst(entry);
    match find_candidate(pos, &source_text, &positioned_tree) {
        None => vec![],
        Some(candidate) => {
            // (The lazy edits need only the leading start position of the
            // candidate.)
            let leading_start_position = cu::leading_start_position(&source_text, candidate);
            let edits: cat::LazyEdits<'a> = Box::new(move || {
                let line_to_offset = |line: isize| source_text::position_to_offset(&source_text, (line, 0));
                edits_of_candidate(&path, &line_to_offset, leading_start_position)
            });
            vec![cat::Refactor(cat::EditData {
                title: "Add doc comment".to_string(),
                edits,
                selection: None,
                trigger_inline_suggest: false,
            })]
        }
    }
}
