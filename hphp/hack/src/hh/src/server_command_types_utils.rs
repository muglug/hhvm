// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_command_types_utils.ml`. See
//! `hh/PORTING.md`.
//!
//! `Client_connect` uses `debug_describe_message_type`.

use crate::server_command_types::CmdMetadata;
use crate::server_command_types::Command;
use crate::server_command_types::MessageType;
use crate::server_command_types::T;

pub fn debug_describe_t(t: &T) -> &'static str {
    match t {
        T::Status { .. } => "STATUS",
        T::StatusSingle { .. } => "STATUS_SINGLE",
        T::LogErrors { .. } => "LOG_ERRORS",
        T::InferType(..) => "INFER_TYPE",
        T::InferDynamic(..) => "INFER_DYNAMIC",
        T::EnforcementAtPosBatch(_) => "ENFORCEMENT_AT_POS_BATCH",
        T::InferTypeBatch(_) => "INFER_TYPE_BATCH",
        T::InferTypeError(..) => "INFER_TYPE_ERROR",
        T::IsSubtype(_) => "IS_SUBTYPE",
        T::TastHoles(..) => "TAST_HOLES",
        T::TastHolesBatch(_) => "TAST_HOLES_BATCH",
        T::IdentifyFunction(..) => "IDENTIFY_FUNCTION",
        T::IdentifySymbol(_) => "IDENTIFY_SYMBOL",
        T::MethodJump(_) => "METHOD_JUMP",
        T::MethodJumpBatch(_) => "METHOD_JUMP_BATCH",
        T::FindRefs(_) => "FIND_REFS",
        T::GoToImpl(_) => "GO_TO_IMPL",
        T::IdeFindRefsBySymbol(_) => "IDE_FIND_REFS_BY_SYMBOL",
        T::IdeGoToImplBySymbol(_) => "IDE_GO_TO_IMPL_BY_SYMBOL",
        T::Rename(_) => "RENAME",
        T::IdeRenameBySymbol(..) => "IDE_RENAME_BY_SYMBOL",
        T::DumpSymbolInfo(_) => "DUMP_SYMBOL_INFO",
        T::RemoveDeadFixmes(_) => "REMOVE_DEAD_FIXMES",
        T::RemoveDeadUnsafeCasts => "REMOVE_DEAD_UNSAFE_CASTS",
        T::RewriteLambdaParameters(_) => "REWRITE_LAMBDA_PARAMETERS",
        T::CheckLiveness => "CHECK_LIVENESS",
        T::Pause => "PAUSE",
        T::Lint(_) => "LINT",
        T::LintStdin(_) => "LINT_STDIN",
        T::LintAll(_) => "LINT_ALL",
        T::InMemoryDepTableSize => "IN_MEMORY_DEP_TABLE_SIZE",
        T::SaveNaming(_) => "SAVE_NAMING",
        T::Stats => "STATS",
        T::DumpFullFidelityParse(_) => "DUMP_FULL_FIDELITY_PARSE",
        T::Rage => "RAGE",
        T::CstSearch(_) => "CST_SEARCH",
        T::NoPrecheckedFiles => "NO_PRECHECKED_FILES",
        T::FunDepsBatch(_) => "FUN_DEPS_BATCH",
        T::ListFilesWithErrors => "LIST_FILES_WITH_ERRORS",
        T::FileDependents(_) => "FILE_DEPENDENTS",
        T::FindIsolatableClusters(_) => "FIND_ISOLATABLE_CLUSTERS",
        T::ValidateIsolation(_) => "VALIDATE_ISOLATION",
        T::Verbose(_) => "VERBOSE",
        T::DepsOutBatch(_) => "DEPS_OUT_BATCH",
        T::DepsInBatch(_) => "DEPS_IN_BATCH",
        T::FindMyTests(_) => "FIND_MY_TESTS",
        T::PackageLint(_) => "PACKAGE_LINT",
        T::PackageLintFull(_) => "PACKAGE_LINT_FULL",
    }
}

pub fn debug_describe_cmd(command: &Command) -> String {
    let (CmdMetadata { from, .. }, rpc) = command;
    format!(
        "{}{}",
        debug_describe_t(rpc),
        if from.is_empty() {
            String::new()
        } else {
            format!(" --from {}", from)
        }
    )
}

/// This returns a string that's shown "hh_server is busy [STATUS]".
/// The intent is that users understand what command hh_server is currently busy with.
/// For command-line commands, we show the "--" option that the user used, e.g. --type-at-pos.
/// For IDE commands like hover, we show a description like "hover".
pub fn status_describe_cmd(command: &Command) -> String {
    let (CmdMetadata { from, desc }, _rpc) = command;
    format!(
        "{}{}",
        if from.is_empty() {
            String::new()
        } else {
            format!("{}:", from)
        },
        desc
    )
}

pub fn debug_describe_message_type<A>(m: &MessageType<A>) -> &'static str {
    match m {
        MessageType::Hello => "Hello",
        MessageType::MonitorFailedToHandoff => "Monitor_failed_to_handoff",
        MessageType::Ping => "Ping",
        MessageType::Response(..) => "Response",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::server_command_types::CommandResult;

    #[test]
    fn descriptions() {
        let cmd = (
            CmdMetadata {
                from: "vim".to_string(),
                desc: "check".to_string(),
            },
            T::ListFilesWithErrors,
        );
        assert_eq!(debug_describe_cmd(&cmd), "LIST_FILES_WITH_ERRORS --from vim");
        assert_eq!(status_describe_cmd(&cmd), "vim:check");
        let cmd = (
            CmdMetadata {
                from: String::new(),
                desc: "check".to_string(),
            },
            T::Stats,
        );
        assert_eq!(debug_describe_cmd(&cmd), "STATS");
        assert_eq!(status_describe_cmd(&cmd), "check");
        assert_eq!(
            debug_describe_message_type::<CommandResult>(&MessageType::MonitorFailedToHandoff),
            "Monitor_failed_to_handoff"
        );
        // Every command has the name of its result.
        assert_eq!(
            debug_describe_t(&T::DepsInBatch(vec![])),
            crate::server_command_types::command_result_name(&CommandResult::DepsInBatch(vec![]))
        );
    }

    /// The commands are named by their OCaml constructors (`STATUS_SINGLE`),
    /// not by the Rust variants (`StatusSingle`).
    #[test]
    fn debug_describe_t_prints_the_ocaml_constructor_names() {
        for (t, name) in [
            (T::InferDynamic(String::new(), false), "INFER_DYNAMIC"),
            (T::EnforcementAtPosBatch(vec![]), "ENFORCEMENT_AT_POS_BATCH"),
            (T::InferTypeBatch(vec![]), "INFER_TYPE_BATCH"),
            (T::IsSubtype(String::new()), "IS_SUBTYPE"),
            (T::TastHolesBatch(vec![]), "TAST_HOLES_BATCH"),
            (T::IdentifySymbol(String::new()), "IDENTIFY_SYMBOL"),
            (T::RemoveDeadUnsafeCasts, "REMOVE_DEAD_UNSAFE_CASTS"),
            (T::CheckLiveness, "CHECK_LIVENESS"),
            (T::InMemoryDepTableSize, "IN_MEMORY_DEP_TABLE_SIZE"),
            (T::Rage, "RAGE"),
            (T::NoPrecheckedFiles, "NO_PRECHECKED_FILES"),
            (T::FunDepsBatch(vec![]), "FUN_DEPS_BATCH"),
            (T::ListFilesWithErrors, "LIST_FILES_WITH_ERRORS"),
            (T::ValidateIsolation(vec![]), "VALIDATE_ISOLATION"),
            (T::Verbose(true), "VERBOSE"),
            (T::DepsOutBatch(vec![]), "DEPS_OUT_BATCH"),
            (T::DepsInBatch(vec![]), "DEPS_IN_BATCH"),
        ] {
            assert_eq!(debug_describe_t(&t), name);
        }
    }
}
