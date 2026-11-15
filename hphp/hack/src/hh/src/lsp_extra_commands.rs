// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/lsp/lsp_extra_commands.ml`. See `hh/PORTING.md`.
//!
//! This module exposes constructors for additional commands implemented in
//! the nuclide.hack language extension

use crate::lsp;
use crate::lsp_fmt;
use crate::yojson::safe as yojson;

pub mod command {
    use super::*;

    pub struct T {
        pub title: &'static str,
        pub command: &'static str,
    }

    pub fn to_lsp(t: &T, arguments: Vec<yojson::T>) -> lsp::command::T {
        lsp::command::T {
            title: t.title.to_string(),
            command: t.command.to_string(),
            arguments,
        }
    }

    pub fn from_lsp<A>(
        t: &T,
        f: impl FnOnce(&[yojson::T]) -> Result<A, String>,
        lsp_cmd: &lsp::command::T,
    ) -> Result<Option<A>, String> {
        if t.command == lsp_cmd.command {
            f(&lsp_cmd.arguments).map(Some).map_err(|error| {
                format!(
                    "could not parse arguments for command {}: {}",
                    t.command, error
                )
            })
        } else {
            Ok(None)
        }
    }

    pub const SET_SELECTION: T = T {
        title: "Set Cursor Selection",
        command: "hack.setSelection",
    };

    pub const TRIGGER_INLINE_SUGGEST: T = T {
        title: "Trigger Inline Suggest",
        command: "editor.action.inlineSuggest.trigger",
    };
}

/// Command to select the given range in the editor.
///
/// Optionally, the specified command is executed after the range is selected.
pub fn set_selection(range: &lsp::Range, command: Option<&lsp::command::T>) -> lsp::command::T {
    let command_arg = match command {
        None => vec![],
        Some(command) => vec![lsp_fmt::print_command(command)],
    };
    let mut args = vec![lsp_fmt::print_range(range)];
    args.extend(command_arg);
    command::to_lsp(&command::SET_SELECTION, args)
}

/// Parse a [set_selection] command into the given range.
///
/// - Returns [None] if the given command wasn't a [set_selection] command.
/// - Returns [Error] if the command name matched, but the arguments of the
///   command could not be parsed.
pub fn parse_set_selection(c: &lsp::command::T) -> Result<Option<lsp::Range>, String> {
    command::from_lsp(
        &command::SET_SELECTION,
        |args| match args {
            [range] | [range, _ /* command */] => match lsp_fmt::parse_range_exn(Some(range)) {
                Ok(r) => Ok(r),
                Err(lsp_fmt::LspFmtError::Parse(error)) => {
                    Err(format!("parse_range_exn: Jget: {}", jget_parse_message(&error)))
                }
                // `parse_range_exn` raises only `Jget.Parse`.
                Err(e) => panic!("{:?}", e),
            },
            xs => Err(format!(
                "expected one or two arguments, but got {}",
                xs.len()
            )),
        },
        c,
    )
}

/// The string carried by `Hh_json_helpers.Jget.Parse`.
fn jget_parse_message(e: &crate::hh_json_helpers::jget::Parse) -> String {
    e.0.clone()
}

/// Instruct VS Code to trigger inline suggestions
pub fn trigger_inline_suggest() -> lsp::command::T {
    command::to_lsp(&command::TRIGGER_INLINE_SUGGEST, vec![])
}
