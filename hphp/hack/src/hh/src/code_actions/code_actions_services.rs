// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/code_actions_services.ml`.
//! See `hh/PORTING.md`.
//!
//! For LSP "textDocument/codeAction" response, we do not compute the edit for the action.
//! For LSP "codeAction/resolve" response, we compute the edit.
//! We never use commands on the server side of the code action flow: afaict that's a legacy technique
//! from before "codeAction/resolve" was introduced.
//!
//! See [CodeAction.edit_or_command] in lsp.ml for more on the code action flow.
//!
//! The lazy edit of an action (`resolved_marker edit_and_or_command Lazy.t`)
//! is a [`LazyAction`]: a closure, forced (called) by [`resolve`].

use std::collections::BTreeSet;
use std::sync::Arc;

use super::code_action_types as cat;
use super::code_actions_commands;
use super::code_actions_quickfixes;
use super::code_actions_refactors;
use crate::ast_provider;
use crate::file_content;
use crate::full_fidelity_source_text as source_text;
use crate::ide_api_types;
use crate::lsp;
use crate::lsp::code_action;
use crate::lsp::code_action_kind;
use crate::lsp_extra_commands;
use crate::lsp_helpers;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast_provider;

/// `Lsp.CodeAction.resolved_marker Lsp.CodeAction.edit_and_or_command Lazy.t`
pub type LazyAction<'a> =
    Box<dyn FnOnce() -> code_action::EditAndOrCommand<code_action::ResolvedMarker> + 'a>;

/// `Lsp.CodeAction.command_or_action_` with the lazy edits of
/// [`edit_to_code_action`].
pub type LazyCommandOrAction<'a> = code_action::CommandOrAction_<LazyAction<'a>>;

pub fn lsp_range_of_ide_range(ide_range: &ide_api_types::Range) -> lsp::Range {
    let lsp_pos_of_ide_pos = |ide_pos: &file_content::position::T| {
        // Explanation for WTF: Lsp.position is zero-based, so theoretically this should be
        // `File_content.Position.line_column_zero_based`.
        // Yet we fail to show code actions correctly if we switch to zero-based.
        // There is likely a bug somewhere else that this compensates.
        // Good (current behavior, using one-based): https://pxl.cl/6rGmJ
        // Bad: https://pxl.cl/6rGmz
        // Relevant tests: https://www.internalfb.com/code/fbsource/[01c48061456e]/fbcode/hphp/hack/test/ide_code_actions/extract_method
        let (line, character) = file_content::position::line_column_one_based(ide_pos);
        lsp::Position { line, character }
    };
    lsp::Range {
        start: lsp_pos_of_ide_pos(&ide_range.st),
        end_: lsp_pos_of_ide_pos(&ide_range.ed),
    }
}

/// Example: in "${0:placeholder}" extracts "placeholder"
/// (`Str.regexp {|\${[0-9]+:\([^}]*\)}|}`)
fn snippet_regexp() -> &'static regex::Regex {
    static RE: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    RE.get_or_init(|| regex::Regex::new(r"\$\{[0-9]+:([^}]*)\}").unwrap())
}

pub fn remove_snippets(
    lsp::workspace_edit::T { changes }: lsp::workspace_edit::T,
) -> lsp::workspace_edit::T {
    let un_snippet_string = |s: &str| snippet_regexp().replace_all(s, "${1}").into_owned();
    let un_snippet_text_edit = |text_edit: lsp::text_edit::T| lsp::text_edit::T {
        new_text: un_snippet_string(&text_edit.new_text),
        ..text_edit
    };
    let changes = changes
        .into_iter()
        .map(|(uri, edits)| {
            (
                uri,
                edits.into_iter().map(un_snippet_text_edit).collect::<Vec<_>>(),
            )
        })
        .collect();
    lsp::workspace_edit::T { changes }
}

pub fn workspace_edit_of_code_action_edits(code_action_edit_map: cat::Edits) -> lsp::workspace_edit::T {
    let changes = code_action_edit_map
        .into_iter()
        .map(|(path, code_action_edits): (RelativePath, Vec<cat::Edit>)| {
            let uri = lsp_helpers::path_to_lsp_uri(&path);
            let lsp_edits = code_action_edits
                .into_iter()
                .map(|cat::Edit { pos, text }| {
                    let range = lsp_helpers::hack_pos_to_lsp_range(
                        |a: &RelativePath, b: &RelativePath| a == b,
                        &pos,
                    );
                    lsp::text_edit::T {
                        range,
                        new_text: text,
                    }
                })
                .collect::<Vec<_>>();
            (uri, lsp_edits)
        })
        // `Lsp.DocumentUri.Map.of_seq`: a later binding replaces an earlier one.
        .collect();
    lsp::workspace_edit::T { changes }
}

fn edit_to_code_action<'a>(
    cat::EditData {
        title,
        edits,
        selection,
        trigger_inline_suggest,
    }: cat::EditData<'a>,
    kind: code_action_kind::T,
) -> LazyCommandOrAction<'a> {
    let trigger_inline_suggest_command = if trigger_inline_suggest {
        Some(lsp_extra_commands::trigger_inline_suggest())
    } else {
        None
    };
    let set_selection_command = match selection {
        None => None,
        Some(selection) => {
            let range = lsp_helpers::hack_pos_to_lsp_range(
                |a: &RelativePath, b: &RelativePath| a == b,
                &selection,
            );
            Some(lsp_extra_commands::set_selection(
                &range,
                trigger_inline_suggest_command.as_ref(),
            ))
        }
    };
    let command = set_selection_command.or(trigger_inline_suggest_command);
    // `Lazy.map edits ~f:workspace_edit_of_code_action_edits`
    let action: LazyAction<'a> = match command {
        None => Box::new(move || {
            code_action::EditAndOrCommand::EditOnly(workspace_edit_of_code_action_edits(edits()))
        }),
        Some(command) => Box::new(move || {
            code_action::EditAndOrCommand::BothEditThenCommand((
                workspace_edit_of_code_action_edits(edits()),
                command,
            ))
        }),
    };
    code_action::CommandOrAction_::Action(code_action::T {
        title,
        kind,
        diagnostics: vec![],
        action: code_action::EditAndOrCommand::UnresolvedEdit(action),
        is_ai: None,
    })
}

fn command_to_code_action<'a>(
    cat::Command {
        title,
        command_args,
    }: cat::Command,
) -> LazyCommandOrAction<'a> {
    let command = match command_args {
        cat::CommandArgs::ShowInlineChat(command_args) => lsp::command::T {
            title: title.clone(),
            command: "code-compose.show-inline-chat".to_string(),
            arguments: vec![cat::show_inline_chat_command_args::to_json(&command_args)],
        },
        cat::CommandArgs::ShowSidebarChat(command_args) => lsp::command::T {
            title: title.clone(),
            command: "code-compose.chat.prompt".to_string(),
            arguments: vec![cat::show_sidebar_chat_command_args::to_json(&command_args)],
        },
    };
    // We include an empty map of edits so the client does not send us a follow-up
    // codeAction/resolve request to as for edits
    // https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_codeAction
    let edit = lsp::workspace_edit::T {
        changes: Default::default(),
    };
    let action = code_action::T {
        title,
        kind: code_action_kind::quickfix(),
        diagnostics: vec![],
        action: code_action::EditAndOrCommand::BothEditThenCommand((edit, command)),
        is_ai: Some(true),
    };
    code_action::CommandOrAction_::Action(action)
}

fn to_action(code_action: cat::T<'_>) -> LazyCommandOrAction<'_> {
    match code_action {
        cat::T::RefactorAction(edit) => edit_to_code_action(edit, code_action_kind::refactor()),
        cat::T::QuickfixAction(edit) => edit_to_code_action(edit, code_action_kind::quickfix()),
        cat::T::CommandAction(command) => command_to_code_action(command),
    }
}

pub fn find<'a>(
    ctx: &'a provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
    entry: &'a Arc<provider_context::Entry>,
    range: &lsp::Range,
) -> Vec<cat::T<'a>> {
    let pos: Pos = {
        let source_text = ast_provider::compute_source_text(entry);
        let line_to_offset = |line: isize| source_text::position_to_offset(&source_text, (line, 0));
        let path = &entry.path;
        lsp_helpers::lsp_range_to_pos(line_to_offset, path, range)
    };
    let quickfixes = code_actions_quickfixes::find(entry, &pos, ctx, error_filter);
    let mut quickfix_titles = BTreeSet::new();
    let quickfixes: Vec<cat::T<'a>> = quickfixes
        .into_iter()
        .map(|cat::Quickfix(edit)| {
            quickfix_titles.insert(edit.title.clone());
            cat::T::QuickfixAction(edit)
        })
        .collect();
    // OCaml conses the refactors, then the commands, onto the list of
    // quickfixes and reverses the whole: the quickfixes come first (in
    // reverse order), then the refactors, then the commands.
    let mut result: Vec<cat::T<'a>> = quickfixes.into_iter().rev().collect();
    // Accumulate refactors
    for cat::Refactor(edit) in code_actions_refactors::find(entry, &pos, ctx) {
        // Ensure no duplicates with quickfixes generated from Quickfixes_to_refactors_config.
        if !quickfix_titles.contains(&edit.title) {
            result.push(cat::T::RefactorAction(edit))
        }
    }
    // Accumulate commands then reverse the entire list so that quickfixes come first, then refactors, the commands
    for command in code_actions_commands::find(entry, &pos, ctx, error_filter) {
        result.push(cat::T::CommandAction(command))
    }
    result
}

/// `map_edit_and_or_command ~f`
fn map_edit_and_or_command(
    e: code_action::EditAndOrCommand<code_action::ResolvedMarker>,
    f: impl FnOnce(lsp::workspace_edit::T) -> lsp::workspace_edit::T,
) -> code_action::EditAndOrCommand<code_action::ResolvedMarker> {
    use code_action::EditAndOrCommand::*;
    match e {
        EditOnly(e) => EditOnly(f(e)),
        CommandOnly(c) => CommandOnly(c),
        BothEditThenCommand((e, c)) => BothEditThenCommand((f(e), c)),
        UnresolvedEdit(m) => match m {},
    }
}

/// `update_edit ~f`
fn update_edit<A, B>(
    c: code_action::CommandOrAction_<A>,
    f: impl FnOnce(A) -> code_action::EditAndOrCommand<B>,
) -> code_action::CommandOrAction_<B> {
    use code_action::EditAndOrCommand::*;
    match c {
        code_action::CommandOrAction_::Command(c) => code_action::CommandOrAction_::Command(c),
        code_action::CommandOrAction_::Action(a) => {
            let code_action::T {
                title,
                kind,
                diagnostics,
                action,
                is_ai,
            } = a;
            let action = match action {
                // Currently only [UnresolvedEdit] is used, since all code actions involve lazy edits
                UnresolvedEdit(lazy_edit) => f(lazy_edit),
                EditOnly(e) => EditOnly(e),
                CommandOnly(c) => CommandOnly(c),
                BothEditThenCommand(ca) => BothEditThenCommand(ca),
            };
            code_action::CommandOrAction_::Action(code_action::T {
                title,
                kind,
                diagnostics,
                action,
                is_ai,
            })
        }
    }
}

pub fn go(
    ctx: &provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
    entry: &Arc<provider_context::Entry>,
    range: &ide_api_types::Range,
) -> code_action::Result {
    let strip = |c: LazyCommandOrAction<'_>| {
        update_edit(c, |_| code_action::EditAndOrCommand::UnresolvedEdit(()))
    };
    find(ctx, error_filter, entry, &lsp_range_of_ide_range(range))
        .into_iter()
        .map(to_action)
        .map(strip)
        .collect()
}

pub fn content_modified() -> lsp::error::T {
    lsp::error::T {
        code: lsp::error::ContentModified,
        message: "Expected the code action requested with codeAction/resolve to be findable.
Note: This error message may be caused by the source text changing between
when the code action menu pops up and when the user selects the code action.
In such cases we may not be able to find a code action at the same location with
the same title, so cannot resolve the code action.
        "
        .to_string(),
        data: None,
    }
}

pub fn code_action_title<'t>(t: &'t cat::T<'_>) -> &'t str {
    match t {
        cat::T::RefactorAction(cat::EditData { title, .. })
        | cat::T::QuickfixAction(cat::EditData { title, .. })
        | cat::T::CommandAction(cat::Command { title, .. }) => title,
    }
}

pub fn resolve(
    ctx: &provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
    entry: &Arc<provider_context::Entry>,
    range: &ide_api_types::Range,
    resolve_title: &str,
    use_snippet_edits: bool,
) -> lsp::code_action_resolve::Result {
    let transform_command_or_action = |c: LazyCommandOrAction<'_>| -> code_action::ResolvedCommandOrAction {
        update_edit(c, |edit_and_or_command: LazyAction<'_>| {
            map_edit_and_or_command(edit_and_or_command(), |edit| {
                if use_snippet_edits {
                    edit
                } else {
                    remove_snippets(edit)
                }
            })
        })
    };
    find(ctx, error_filter, entry, &lsp_range_of_ide_range(range))
        .into_iter()
        .find(|code_action| code_action_title(code_action) == resolve_title)
        // When we can't find a matching code action, ContentModified is the right error
        // per https://github.com/microsoft/language-server-protocol/issues/1738
        .ok_or_else(content_modified)
        .map(|ca| transform_command_or_action(to_action(ca)))
}
