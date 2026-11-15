// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/code_actions_cli_lib/code_actions_cli_lib.ml`
//! (`hh single --ide-code-actions`).

use std::sync::Arc;

use super::code_actions_services;
use super::code_actions_utils::Patch;
use crate::full_fidelity_source_text as source_text;
use crate::ide_api_types;
use crate::lsp;
use crate::lsp::code_action;
use crate::lsp_extra_commands;
use crate::lsp_fmt;
use crate::lsp_helpers;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast_provider;

fn apply_patches_to_string(old_content: &[u8], patches: Vec<Patch>) -> Vec<u8> {
    super::code_actions_utils::apply_patches_to_string(old_content, patches)
}

fn lsp_range_to_pos(source_text: &source_text::T, path: &RelativePath, range: &lsp::Range) -> Pos {
    let line_to_offset = |line: isize| source_text::position_to_offset(source_text, (line, 0));
    // Correct for inconsistencies in 0-vs-1-indexing elsewhere.
    // TODO(T154897774): fix off-by-ones in conversion functions and remove this adaptor
    let range = lsp::Range {
        start: lsp::Position {
            line: range.start.line + 1,
            character: range.start.character + 1,
        },
        end_: lsp::Position {
            line: range.end_.line + 1,
            character: range.end_.character + 1,
        },
    };
    // (`|> Pos.to_absolute`: the patches keep the offsets, which are all
    // that is used here.)
    lsp_helpers::lsp_range_to_pos(line_to_offset, path, &range)
}

fn extract_cursor_position_for_code_action(
    source_text: &source_text::T,
    path: &RelativePath,
    code_action: &code_action::ResolvedCommandOrAction,
) -> Result<Option<Pos>, String> {
    match code_action {
        code_action::CommandOrAction_::Action(code_action::T {
            action: code_action::EditAndOrCommand::BothEditThenCommand((_, c)),
            ..
        }) => lsp_extra_commands::parse_set_selection(c)
            .map(|r| r.map(|r| lsp_range_to_pos(source_text, path, &r))),
        _ => Ok(None),
    }
}

fn patched_text_of_command_or_action(
    source_text: &source_text::T,
    path: &RelativePath,
    code_action: &code_action::ResolvedCommandOrAction,
) -> Result<Option<Vec<u8>>, String> {
    let changes = match code_action {
        code_action::CommandOrAction_::Action(code_action::T {
            action: code_action::EditAndOrCommand::EditOnly(lsp::workspace_edit::T { changes }),
            ..
        })
        | code_action::CommandOrAction_::Action(code_action::T {
            action: code_action::EditAndOrCommand::BothEditThenCommand((lsp::workspace_edit::T { changes }, _)),
            ..
        }) => changes,
        code_action::CommandOrAction_::Action(_) | code_action::CommandOrAction_::Command(_) => {
            return Ok(None);
        }
    };
    let to_patch = |lsp::text_edit::T { range, new_text: text }: &lsp::text_edit::T| {
        let pos = lsp_range_to_pos(source_text, path, range);
        Patch::Replace {
            pos,
            text: text.clone(),
        }
    };
    let patches: Vec<Patch> = changes
        .values()
        .flat_map(|edits| edits.iter().map(to_patch))
        .collect();
    // The new cursor position is relative to the content *after* patching.
    // So first patch...
    let source_text = match std::fs::read(crate::relative_path::to_absolute(path)) {
        Ok(s) => s,
        // `Sys_utils.cat` raises `Sys_error`, which `run` prints.
        Err(e) => std::panic::panic_any(SysError(format!(
            "{}: {}",
            crate::relative_path::to_absolute(path),
            e
        ))),
    };
    let rewritten_contents = apply_patches_to_string(&source_text, patches);
    // ... and only then indicate the cursor position
    let cursor_position = extract_cursor_position_for_code_action(
        &source_text::make(path, &rewritten_contents),
        path,
        code_action,
    )?;
    let rewritten_contents = match cursor_position {
        None => rewritten_contents,
        Some(selection) => {
            let patches = vec![
                Patch::Replace {
                    pos: crate::pos::shrink_to_start(&selection),
                    text: ">|".to_string(),
                },
                Patch::Replace {
                    pos: crate::pos::shrink_to_end(&selection),
                    text: "|<".to_string(),
                },
            ];
            apply_patches_to_string(&rewritten_contents, patches)
        }
    };
    Ok(Some(rewritten_contents))
}

/// `Sys_error` of `Sys_utils.cat`, raised to [`run`].
struct SysError(String);

/// `Str.global_replace (Str.regexp "\".+?.php\"") "\"FILE.php\""`: in `Str`,
/// `+?` is `+` then an optional `?` (a literal `?` cannot follow: `?` is a
/// postfix operator), so this is the greedy `".+.php"` with an optional
/// repetition marker, i.e. `".+.php"` as a greedy match on each line (`.`
/// does not match a newline).
fn hermeticize_paths(s: &str) -> String {
    static RE: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    let re = RE.get_or_init(|| regex::Regex::new(r#""(?:.+)?.php""#).unwrap());
    re.replace_all(s, "\"FILE.php\"").into_owned()
}

fn run_exn(
    ctx: &provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
    entry: &Arc<provider_context::Entry>,
    range: &ide_api_types::Range,
    title_prefix: &str,
    use_snippet_edits: bool,
) {
    let commands_or_actions = code_actions_services::go(ctx, error_filter, entry, range);
    if commands_or_actions.is_empty() {
        print!("No commands or actions found\n")
    } else {
        let description_triples: Vec<(String, String, bool)> = commands_or_actions
            .iter()
            .map(|c| match c {
                code_action::CommandOrAction_::Action(code_action::T { title, kind, .. }) => {
                    let kind_str = format!(
                        "CodeActionKind: \"{}\"",
                        lsp::code_action_kind::string_of_kind(kind)
                    );
                    let is_selected = title.starts_with(title_prefix);
                    (title.clone(), kind_str, is_selected)
                }
                code_action::CommandOrAction_::Command(lsp::command::T { title, .. }) => {
                    let is_selected = title.starts_with(title_prefix);
                    (title.clone(), "Command".to_string(), is_selected)
                }
            })
            .collect();
        let separator = "\n------------------------------------------\n";
        print!("Code actions available:{}", separator);
        for (title, kind_str, is_selected) in &description_triples {
            let selected_str = if *is_selected { " SELECTED" } else { "" };
            print!("{} ({}){}\n", title, kind_str, selected_str);
        }
        let selected_titles: Vec<&String> = description_triples
            .iter()
            .filter_map(|(title, _, is_selected)| if *is_selected { Some(title) } else { None })
            .collect();
        let output_code_action = |selected_title: &str| {
            let resolved = match code_actions_services::resolve(
                ctx,
                error_filter,
                entry,
                range,
                selected_title,
                use_snippet_edits,
            ) {
                Ok(r) => r,
                // `Result.ok_or_failwith`
                Err(e) => std::panic::panic_any(Failure(crate::yojson::safe::pretty_to_string(&lsp_fmt::print_error(&e)))),
            };
            let source_text = entry
                .source_text
                .lock()
                .unwrap()
                .clone()
                .expect("Option.value_exn");
            let text_of_selected = {
                let patched_opt = patched_text_of_command_or_action(&source_text, &entry.path, &resolved);
                match patched_opt {
                    Ok(Some(patched)) => {
                        let is_noop = source_text::text(&source_text) == &patched[..];
                        if is_noop {
                            b"\nThe code action edit was a no-op".to_vec()
                        } else {
                            let mut s = format!("\nApplied edit for code action:{}", separator).into_bytes();
                            s.extend(patched);
                            s
                        }
                    }
                    Ok(None) => b"\nThe command_or_action cannot be converted into patches.\n".to_vec(),
                    Err(error) => format!(
                        "\nError while converting the command_or_action into patches: {}",
                        error
                    )
                    .into_bytes(),
                }
            };
            print!("\nJSON for selected code action:{}", separator);
            let json = lsp_fmt::print_code_action_resolve_result(&Ok(resolved));
            print!("{}\n", hermeticize_paths(&crate::yojson::safe::pretty_to_string(&json)));
            use std::io::Write;
            let mut out = std::io::stdout().lock();
            let _ = out.write_all(&text_of_selected);
            let _ = out.write_all(b"\n");
        };
        match &selected_titles[..] {
            [selected_title] => output_code_action(selected_title),
            [_, ..] => {
                print!("\nMultiple code action titles match prefix: '{}'\n", title_prefix);
                for selected_title in &selected_titles {
                    print!("\nCode action title: {}\n", selected_title);
                    output_code_action(selected_title)
                }
            }
            [] => print!("\nNo code action titles match prefix: {}\n", title_prefix),
        }
    }
}

/// `Failure` raised by `Result.ok_or_failwith`.
struct Failure(String);

/// The message of a panic that stands for `failwith msg` (a panic with a
/// message; not that of a `todo!`).
fn failwith_message(payload: &(dyn std::any::Any + Send)) -> Option<&str> {
    let msg = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())?;
    if msg.starts_with("not yet implemented") || msg.starts_with("not implemented") {
        None
    } else {
        Some(msg)
    }
}

/// `run`: any exception of `run_exn` is printed (`Exn.to_string`). The
/// exceptions caught here are the `Failure` and `Sys_error` that `run_exn`
/// raises itself, the `failwith` of the services it calls (a panic with a
/// message, e.g. `Full_fidelity_ast`'s "Not a Hack file") and libhackfmt's
/// exceptions; any other panic is a bug of the port and propagates.
pub fn run(
    ctx: &provider_context::T,
    error_filter: tast_provider::ErrorFilter,
    entry: &Arc<provider_context::Entry>,
    range: ide_api_types::Range,
    title_prefix: &str,
    use_snippet_edits: bool,
) {
    // (The panics printed below are not printed by the panic hook.)
    let reported = |payload: &(dyn std::any::Any + Send)| {
        payload.is::<Failure>()
            || failwith_message(payload).is_some()
            || payload.is::<SysError>()
            || payload.is::<super::code_actions_utils::InvalidArgument>()
            || payload.is::<source_text::StringSubInvalidArgument>()
            || payload.is::<source_text::PositionNotFound>()
            || payload.is::<hackfmt::error::Exn>()
    };
    let result = crate::rt::quiet_panic::catch_reported(reported, || {
        run_exn(ctx, &error_filter, entry, &range, title_prefix, use_snippet_edits)
    });
    if let Err(payload) = result {
        if let Some(Failure(msg)) = payload.downcast_ref::<Failure>() {
            println!("{}", crate::rt::ocaml_exn::Uncaught::failure(msg.as_str()))
        } else if let Some(msg) = failwith_message(&*payload) {
            println!("{}", crate::rt::ocaml_exn::Uncaught::failure(msg))
        } else if let Some(SysError(msg)) = payload.downcast_ref::<SysError>() {
            println!("(Sys_error {:?})", msg)
        } else if let Some(super::code_actions_utils::InvalidArgument(msg)) = payload.downcast_ref() {
            println!("(Invalid_argument {:?})", msg)
        } else if let Some(source_text::StringSubInvalidArgument) = payload.downcast_ref() {
            println!("(Invalid_argument \"String.sub / Bytes.sub\")")
        } else if let Some(source_text::PositionNotFound {
            line,
            column,
            num_lines_in_file,
        }) = payload.downcast_ref()
        {
            // An exception without a sexp converter: `Exn.to_string` gives
            // `Printexc.to_string` as a string atom.
            println!(
                "(\"Line_break_map.Position_not_found({}, {}, {})\")",
                line, column, num_lines_in_file
            )
        } else if let Some(e) = payload.downcast_ref::<hackfmt::error::Exn>() {
            // The exceptions of libhackfmt (the refactors format their
            // edits with it): `Exn.to_string` puts a constant constructor
            // in parentheses too.
            match e {
                hackfmt::error::Exn::InvalidSyntax => println!("(Hackfmt_error.InvalidSyntax)"),
                e => println!("{}", e.to_sexp_string()),
            }
        } else {
            std::panic::resume_unwind(payload)
        }
    }
}
