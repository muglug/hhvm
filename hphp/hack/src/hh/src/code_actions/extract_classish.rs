// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/extract_classish/`:
//! `extract_classish_types.ml`, `extract_classish_find_candidate.ml`,
//! `extract_classish_to_refactors.ml` and `extract_classish.ml`, in that
//! order. See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::aast;
use oxidized::ast_defs;

use super::code_action_types as cat;
use super::code_actions_utils as cu;
use crate::ast_provider;
use crate::full_fidelity_source_text as source_text;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_provider;

// ---- extract_classish_types.ml ----

struct Candidate {
    class_: tast::Class_,
    selected_methods: Vec<tast::Method_>,
}

// ---- extract_classish_find_candidate.ml ----

fn class_kind_supports_extraction(kind: &ast_defs::ClassishKind) -> bool {
    use ast_defs::Abstraction;
    use ast_defs::ClassishKind;
    match kind {
        ClassishKind::Cclass(Abstraction::Concrete) => true,
        // could handle with more logic
        ClassishKind::Cclass(Abstraction::Abstract) => false,
        ClassishKind::Cinterface | ClassishKind::Ctrait | ClassishKind::Cenum | ClassishKind::CenumClass(_) => false,
    }
}

fn find_candidate(selection: &Pos, entry: &Arc<provider_context::Entry>, ctx: &provider_context::T) -> Option<Candidate> {
    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);

    tast.under_normal_assumptions.iter().find_map(|def| match def {
        aast::Def::Class(class_)
            if crate::pos::contains(&class_.span, selection) && class_kind_supports_extraction(&class_.kind) =>
        {
            let selected_methods: Vec<tast::Method_> = class_
                .methods
                .iter()
                .filter(|meth| crate::pos::contains(selection, &meth.span))
                .cloned()
                .collect();
            if selected_methods.is_empty() {
                None
            } else {
                Some(Candidate {
                    class_: (**class_).clone(),
                    selected_methods,
                })
            }
        }
        _ => None,
    })
}

// ---- extract_classish_to_refactors.ml ----

const PLACEHOLDER_NAME: &str = "Placeholder_";

/// `Char.is_whitespace`
fn is_whitespace(ch: char) -> bool {
    matches!(ch, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r')
}

fn interface_body_of_methods(st: &source_text::T, candidate: &Candidate) -> String {
    let abstractify_one = |meth: &tast::Method_| -> String {
        let stmts = &meth.body.fb_ast;
        let remove_async_modifier = |s: String| -> String {
            match meth.fun_kind {
                ast_defs::FunKind::FSync | ast_defs::FunKind::FGenerator => s,
                ast_defs::FunKind::FAsync | ast_defs::FunKind::FAsyncGenerator => s.replacen("async ", "", 1),
            }
        };
        match stmts.first() {
            Some(aast::Stmt(stmt_pos, _)) if !crate::pos::equal(stmt_pos, &Pos::NONE) => {
                let body_until_first_statement_length =
                    crate::pos::start_offset(stmt_pos) - crate::pos::start_offset(&meth.span);
                let x = cu::sub_of_pos_length(st, body_until_first_statement_length, &meth.span);
                let x = x.trim_end_matches(|ch| is_whitespace(ch) || ch == '{');
                remove_async_modifier(format!("{};", x))
            }
            Some(_) | None => {
                let x = cu::to_string(cu::sub_of_pos(st, &meth.span));
                let x = x.trim_end_matches(|ch| is_whitespace(ch) || ch == '}');
                let x = x.trim_end_matches(|ch| is_whitespace(ch) || ch == '{');
                remove_async_modifier(format!("{};", x))
            }
        }
    };
    candidate
        .selected_methods
        .iter()
        .map(abstractify_one)
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_classish(path: &RelativePath, body: &str) -> String {
    let classish = format!("interface {} {{\n{}\n}}", PLACEHOLDER_NAME, body);
    let prefixed = format!("<?hh\n{}", classish);
    let strip_prefix = |s: &str| -> String { s.lines().skip(1).collect::<Vec<_>>().join("\n") };
    // `Full_fidelity_source_text.make path |> PositionedTree.make`: the
    // default parser environment.
    let tree = hackfmt::parse(prefixed.as_bytes(), &crate::relative_path::suffix(path), false, false);
    let formatted = cu::to_string(hackfmt::format_tree(None, &tree).into());
    format!("{}\n\n", strip_prefix(&formatted))
}

fn extracted_classish_text_edit(st: &source_text::T, path: &RelativePath, candidate: &Candidate) -> cat::Edit {
    let pos_of_extracted = crate::pos::shrink_to_start(&candidate.class_.span);

    let body = interface_body_of_methods(st, candidate);
    let text = format_classish(path, &body);
    cat::Edit {
        pos: pos_of_extracted,
        text,
    }
}

fn update_implements_text_edit(class_: &tast::Class_) -> cat::Edit {
    match class_.implements.last() {
        Some(aast::Hint(pos, _)) => {
            let pos = crate::pos::shrink_to_end(pos);
            let text = format!(", {}", PLACEHOLDER_NAME);
            cat::Edit { pos, text }
        }
        None => {
            let pos = {
                let extends_pos_opt = class_.extends.first().map(|aast::Hint(pos, _)| pos);
                let c_name_pos = &class_.name.0;
                crate::pos::shrink_to_end(extends_pos_opt.unwrap_or(c_name_pos))
            };
            let text = format!("\n  implements {}", PLACEHOLDER_NAME);
            cat::Edit { pos, text }
        }
    }
}

fn edits_of_candidate(st: &source_text::T, path: &RelativePath, candidate: &Candidate) -> cat::Edits {
    let edits = {
        let extracted_edit = extracted_classish_text_edit(st, path, candidate);
        let reference_edit = update_implements_text_edit(&candidate.class_);
        vec![reference_edit, extracted_edit]
    };
    cat::singleton(path.clone(), edits)
}

fn to_refactor<'a>(st: source_text::T, path: RelativePath, candidate: Candidate) -> cat::Refactor<'a> {
    let edits: cat::LazyEdits<'a> = Box::new(move || edits_of_candidate(&st, &path, &candidate));
    cat::Refactor(cat::EditData {
        title: "Extract interface".to_string(),
        edits,
        selection: None,
        trigger_inline_suggest: false,
    })
}

fn to_refactors<'a>(st: source_text::T, path: RelativePath, candidate: Candidate) -> Vec<cat::Refactor<'a>> {
    vec![to_refactor(st, path, candidate)]
}

// ---- extract_classish.ml ----

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    pos: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    if crate::pos::length(pos) > 0 {
        let source_text = ast_provider::compute_source_text(entry);
        let path = entry.path.clone();
        match find_candidate(pos, entry, ctx) {
            Some(candidate) => to_refactors(source_text, path, candidate),
            None => vec![],
        }
    } else {
        vec![]
    }
}
