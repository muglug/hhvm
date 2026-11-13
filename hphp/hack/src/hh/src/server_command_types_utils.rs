// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_command_types_utils.ml`. See
//! `hh/PORTING.md`.
//!
//! Ported in full by the client-connection assignment (D1), which needs
//! `debug_describe_message_type` (`Client_connect`).

use crate::server_command_types::CmdMetadata;
use crate::server_command_types::Command;
use crate::server_command_types::MessageType;
use crate::server_command_types::T;

pub fn debug_describe_t(t: &T) -> &'static str {
    match t {
        T::STATUS { .. } => "STATUS",
        T::STATUSSINGLE { .. } => "STATUS_SINGLE",
        T::LOGERRORS { .. } => "LOG_ERRORS",
        T::INFERTYPE(..) => "INFER_TYPE",
        T::INFERDYNAMIC(..) => "INFER_DYNAMIC",
        T::ENFORCEMENTATPOSBATCH(_) => "ENFORCEMENT_AT_POS_BATCH",
        T::INFERTYPEBATCH(_) => "INFER_TYPE_BATCH",
        T::INFERTYPEERROR(..) => "INFER_TYPE_ERROR",
        T::ISSUBTYPE(_) => "IS_SUBTYPE",
        T::TASTHOLES(..) => "TAST_HOLES",
        T::TASTHOLESBATCH(_) => "TAST_HOLES_BATCH",
        T::IDENTIFYFUNCTION(..) => "IDENTIFY_FUNCTION",
        T::IDENTIFYSYMBOL(_) => "IDENTIFY_SYMBOL",
        T::METHODJUMP(_) => "METHOD_JUMP",
        T::METHODJUMPBATCH(_) => "METHOD_JUMP_BATCH",
        T::FINDREFS(_) => "FIND_REFS",
        T::GOTOIMPL(_) => "GO_TO_IMPL",
        T::IDEFINDREFSBYSYMBOL(_) => "IDE_FIND_REFS_BY_SYMBOL",
        T::IDEGOTOIMPLBYSYMBOL(_) => "IDE_GO_TO_IMPL_BY_SYMBOL",
        T::RENAME(_) => "RENAME",
        T::IDERENAMEBYSYMBOL(..) => "IDE_RENAME_BY_SYMBOL",
        T::DUMPSYMBOLINFO(_) => "DUMP_SYMBOL_INFO",
        T::REMOVEDEADFIXMES(_) => "REMOVE_DEAD_FIXMES",
        T::REMOVEDEADUNSAFECASTS => "REMOVE_DEAD_UNSAFE_CASTS",
        T::REWRITELAMBDAPARAMETERS(_) => "REWRITE_LAMBDA_PARAMETERS",
        T::CHECKLIVENESS => "CHECK_LIVENESS",
        T::LINT(_) => "LINT",
        T::LINTSTDIN(_) => "LINT_STDIN",
        T::LINTALL(_) => "LINT_ALL",
        T::INMEMORYDEPTABLESIZE => "IN_MEMORY_DEP_TABLE_SIZE",
        T::SAVENAMING(_) => "SAVE_NAMING",
        T::STATS => "STATS",
        T::DUMPFULLFIDELITYPARSE(_) => "DUMP_FULL_FIDELITY_PARSE",
        T::RAGE => "RAGE",
        T::CSTSEARCH(_) => "CST_SEARCH",
        T::NOPRECHECKEDFILES => "NO_PRECHECKED_FILES",
        T::FUNDEPSBATCH(_) => "FUN_DEPS_BATCH",
        T::LISTFILESWITHERRORS => "LIST_FILES_WITH_ERRORS",
        T::FILEDEPENDENTS(_) => "FILE_DEPENDENTS",
        T::FINDISOLATABLECLUSTERS => "FIND_ISOLATABLE_CLUSTERS",
        T::VERBOSE(_) => "VERBOSE",
        T::DEPSOUTBATCH(_) => "DEPS_OUT_BATCH",
        T::DEPSINBATCH(_) => "DEPS_IN_BATCH",
        T::FINDMYTESTS(_) => "FIND_MY_TESTS",
        T::PACKAGELINT(_) => "PACKAGE_LINT",
        T::PACKAGELINTFULL(_) => "PACKAGE_LINT_FULL",
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
            T::LISTFILESWITHERRORS,
        );
        assert_eq!(debug_describe_cmd(&cmd), "LIST_FILES_WITH_ERRORS --from vim");
        assert_eq!(status_describe_cmd(&cmd), "vim:check");
        let cmd = (
            CmdMetadata {
                from: String::new(),
                desc: "check".to_string(),
            },
            T::STATS,
        );
        assert_eq!(debug_describe_cmd(&cmd), "STATS");
        assert_eq!(status_describe_cmd(&cmd), "check");
        assert_eq!(
            debug_describe_message_type::<CommandResult>(&MessageType::MonitorFailedToHandoff),
            "Monitor_failed_to_handoff"
        );
        // Every command has the name of its result.
        assert_eq!(
            debug_describe_t(&T::DEPSINBATCH(vec![])),
            crate::server_command_types::command_result_name(&CommandResult::DEPSINBATCH(vec![]))
        );
    }
}
