// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_env.ml`. See `hh/PORTING.md`.
//!
//! The constructors of `client_mode` are the UpperCamelCase of the OCaml
//! names (`MODE_STATUS_FILES` is `ModeStatusFiles`), and their lists are
//! `Vec`s in the order of the OCaml lists (head first).
//! `[@@deriving variants]` gives `Variants_of_client_mode`, of which
//! [`variants_of_client_mode::to_name`] (the OCaml names) and `to_rank` are
//! ported.

use crate::diagnostics;
use crate::filter_diagnostics;
use crate::find_refs_wire_format;
use crate::path;
use crate::server_isolation_types;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RenameMode {
    Function,
    Class,
    Method,
    Unspecified,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatusFiles {
    pub filenames: Vec<String>,
    pub show_tast: bool,
    pub preexisting_warnings: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogErrorsParams {
    pub log_file: Option<String>,
    pub preexisting_warnings: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ClientMode {
    ModeCstSearch(Option<Vec<String>>),
    ModeDumpSymbolInfo(String),
    ModeFindClassRefs(String),
    ModeFindRefs(String),
    ModeFindMyTests(String),
    ModeFullFidelityParse(String),
    ModeFullFidelitySchema,
    ModeGoToImplClass(String),
    ModeGoToImplMethod(String),
    ModeHackToNotebook,
    ModeIdeFindRefsBySymbol(find_refs_wire_format::cli_args::T),
    ModeIdeGoToImplBySymbol(find_refs_wire_format::cli_args::T),
    ModeIdeRenameBySymbol(String),
    ModeIdentifySymbol1(String),
    ModeIdentifySymbol2(String),
    ModeIdentifySymbol3(String),
    ModeIdentifySymbol(String),
    ModeInMemoryDepTableSize,
    ModeLint,
    ModeLintAll(isize),
    ModeLintStdin(String),
    ModeListFiles,
    ModeMethodJumpAncestors(String, String),
    ModeMethodJumpAncestorsBatch(Vec<String>, String),
    ModeMethodJumpChildren(String),
    ModeNotebookToHack {
        notebook_number: String,
        notebook_header: String,
    },
    ModeOutline,
    ModeOutline2,
    ModeOutlineForAgents(String),
    ModePause,
    ModeRename(RenameMode, String, String),
    ModeRemoveDeadFixmes(Vec<isize>),
    ModeRemoveDeadUnsafeCasts,
    ModeRewriteDeclarations,
    ModeRewriteLambdaParameters(Vec<String>),
    ModeSaveNaming(String),
    ModeSearch(String),
    ModeServerRage,
    ModeStats,
    ModeStatus,
    ModeStatusFiles(StatusFiles),
    ModeLogErrors(LogErrorsParams),
    ModeTypeAtPos(String),
    ModeInferDynamic(String, bool),
    ModeEnforcementAtPosBatch(Vec<String>),
    ModeTypeAtPosBatch(Vec<String>),
    ModeTypeErrorAtPos(String),
    ModeIsSubtype,
    ModeTastHoles(String),
    ModeTastHolesBatch(String),
    ModeFunDepsAtPosBatch(Vec<String>),
    ModeFileLevelDependencies,
    ModeIsolation(server_isolation_types::Options),
    ModeValidateIsolation(String),
    ModeVerbose(bool),
    ModeDepsOutAtPosBatch(Vec<String>),
    ModeDepsInAtPosBatch(Vec<String>),
    ModePackageLint(String),
    ModePackageLintFull((String, Vec<String>)),
}

/// `Variants_of_client_mode` (`[@@deriving variants]`)
pub mod variants_of_client_mode {
    use super::ClientMode;
    use super::ClientMode::*;

    /// The OCaml name of the constructor (`"MODE_STATUS"`).
    pub fn to_name(t: &ClientMode) -> &'static str {
        match t {
            ModeCstSearch(_) => "MODE_CST_SEARCH",
            ModeDumpSymbolInfo(_) => "MODE_DUMP_SYMBOL_INFO",
            ModeFindClassRefs(_) => "MODE_FIND_CLASS_REFS",
            ModeFindRefs(_) => "MODE_FIND_REFS",
            ModeFindMyTests(_) => "MODE_FIND_MY_TESTS",
            ModeFullFidelityParse(_) => "MODE_FULL_FIDELITY_PARSE",
            ModeFullFidelitySchema => "MODE_FULL_FIDELITY_SCHEMA",
            ModeGoToImplClass(_) => "MODE_GO_TO_IMPL_CLASS",
            ModeGoToImplMethod(_) => "MODE_GO_TO_IMPL_METHOD",
            ModeHackToNotebook => "MODE_HACK_TO_NOTEBOOK",
            ModeIdeFindRefsBySymbol(_) => "MODE_IDE_FIND_REFS_BY_SYMBOL",
            ModeIdeGoToImplBySymbol(_) => "MODE_IDE_GO_TO_IMPL_BY_SYMBOL",
            ModeIdeRenameBySymbol(_) => "MODE_IDE_RENAME_BY_SYMBOL",
            ModeIdentifySymbol1(_) => "MODE_IDENTIFY_SYMBOL1",
            ModeIdentifySymbol2(_) => "MODE_IDENTIFY_SYMBOL2",
            ModeIdentifySymbol3(_) => "MODE_IDENTIFY_SYMBOL3",
            ModeIdentifySymbol(_) => "MODE_IDENTIFY_SYMBOL",
            ModeInMemoryDepTableSize => "MODE_IN_MEMORY_DEP_TABLE_SIZE",
            ModeLint => "MODE_LINT",
            ModeLintAll(_) => "MODE_LINT_ALL",
            ModeLintStdin(_) => "MODE_LINT_STDIN",
            ModeListFiles => "MODE_LIST_FILES",
            ModeMethodJumpAncestors(..) => "MODE_METHOD_JUMP_ANCESTORS",
            ModeMethodJumpAncestorsBatch(..) => "MODE_METHOD_JUMP_ANCESTORS_BATCH",
            ModeMethodJumpChildren(_) => "MODE_METHOD_JUMP_CHILDREN",
            ModeNotebookToHack { .. } => "MODE_NOTEBOOK_TO_HACK",
            ModeOutline => "MODE_OUTLINE",
            ModeOutline2 => "MODE_OUTLINE2",
            ModeOutlineForAgents(_) => "MODE_OUTLINE_FOR_AGENTS",
            ModePause => "MODE_PAUSE",
            ModeRename(..) => "MODE_RENAME",
            ModeRemoveDeadFixmes(_) => "MODE_REMOVE_DEAD_FIXMES",
            ModeRemoveDeadUnsafeCasts => "MODE_REMOVE_DEAD_UNSAFE_CASTS",
            ModeRewriteDeclarations => "MODE_REWRITE_DECLARATIONS",
            ModeRewriteLambdaParameters(_) => "MODE_REWRITE_LAMBDA_PARAMETERS",
            ModeSaveNaming(_) => "MODE_SAVE_NAMING",
            ModeSearch(_) => "MODE_SEARCH",
            ModeServerRage => "MODE_SERVER_RAGE",
            ModeStats => "MODE_STATS",
            ModeStatus => "MODE_STATUS",
            ModeStatusFiles(_) => "MODE_STATUS_FILES",
            ModeLogErrors(_) => "MODE_LOG_ERRORS",
            ModeTypeAtPos(_) => "MODE_TYPE_AT_POS",
            ModeInferDynamic(..) => "MODE_INFER_DYNAMIC",
            ModeEnforcementAtPosBatch(_) => "MODE_ENFORCEMENT_AT_POS_BATCH",
            ModeTypeAtPosBatch(_) => "MODE_TYPE_AT_POS_BATCH",
            ModeTypeErrorAtPos(_) => "MODE_TYPE_ERROR_AT_POS",
            ModeIsSubtype => "MODE_IS_SUBTYPE",
            ModeTastHoles(_) => "MODE_TAST_HOLES",
            ModeTastHolesBatch(_) => "MODE_TAST_HOLES_BATCH",
            ModeFunDepsAtPosBatch(_) => "MODE_FUN_DEPS_AT_POS_BATCH",
            ModeFileLevelDependencies => "MODE_FILE_LEVEL_DEPENDENCIES",
            ModeIsolation(_) => "MODE_ISOLATION",
            ModeValidateIsolation(_) => "MODE_VALIDATE_ISOLATION",
            ModeVerbose(_) => "MODE_VERBOSE",
            ModeDepsOutAtPosBatch(_) => "MODE_DEPS_OUT_AT_POS_BATCH",
            ModeDepsInAtPosBatch(_) => "MODE_DEPS_IN_AT_POS_BATCH",
            ModePackageLint(_) => "MODE_PACKAGE_LINT",
            ModePackageLintFull(_) => "MODE_PACKAGE_LINT_FULL",
        }
    }

    /// The position of the constructor in the type definition, from 0.
    pub fn to_rank(t: &ClientMode) -> isize {
        match t {
            ModeCstSearch(_) => 0,
            ModeDumpSymbolInfo(_) => 1,
            ModeFindClassRefs(_) => 2,
            ModeFindRefs(_) => 3,
            ModeFindMyTests(_) => 4,
            ModeFullFidelityParse(_) => 5,
            ModeFullFidelitySchema => 6,
            ModeGoToImplClass(_) => 7,
            ModeGoToImplMethod(_) => 8,
            ModeHackToNotebook => 9,
            ModeIdeFindRefsBySymbol(_) => 10,
            ModeIdeGoToImplBySymbol(_) => 11,
            ModeIdeRenameBySymbol(_) => 12,
            ModeIdentifySymbol1(_) => 13,
            ModeIdentifySymbol2(_) => 14,
            ModeIdentifySymbol3(_) => 15,
            ModeIdentifySymbol(_) => 16,
            ModeInMemoryDepTableSize => 17,
            ModeLint => 18,
            ModeLintAll(_) => 19,
            ModeLintStdin(_) => 20,
            ModeListFiles => 21,
            ModeMethodJumpAncestors(..) => 22,
            ModeMethodJumpAncestorsBatch(..) => 23,
            ModeMethodJumpChildren(_) => 24,
            ModeNotebookToHack { .. } => 25,
            ModeOutline => 26,
            ModeOutline2 => 27,
            ModeOutlineForAgents(_) => 28,
            ModePause => 29,
            ModeRename(..) => 30,
            ModeRemoveDeadFixmes(_) => 31,
            ModeRemoveDeadUnsafeCasts => 32,
            ModeRewriteDeclarations => 33,
            ModeRewriteLambdaParameters(_) => 34,
            ModeSaveNaming(_) => 35,
            ModeSearch(_) => 36,
            ModeServerRage => 37,
            ModeStats => 38,
            ModeStatus => 39,
            ModeStatusFiles(_) => 40,
            ModeLogErrors(_) => 41,
            ModeTypeAtPos(_) => 42,
            ModeInferDynamic(..) => 43,
            ModeEnforcementAtPosBatch(_) => 44,
            ModeTypeAtPosBatch(_) => 45,
            ModeTypeErrorAtPos(_) => 46,
            ModeIsSubtype => 47,
            ModeTastHoles(_) => 48,
            ModeTastHolesBatch(_) => 49,
            ModeFunDepsAtPosBatch(_) => 50,
            ModeFileLevelDependencies => 51,
            ModeIsolation(_) => 52,
            ModeValidateIsolation(_) => 53,
            ModeVerbose(_) => 54,
            ModeDepsOutAtPosBatch(_) => 55,
            ModeDepsInAtPosBatch(_) => 56,
            ModePackageLint(_) => 57,
            ModePackageLintFull(_) => 58,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ClientCheckEnv {
    pub autostart: bool,
    pub config: Vec<(String, String)>,
    pub custom_hhi_path: Option<String>,
    pub custom_telemetry_data: Vec<(String, String)>,
    pub error_format: Option<diagnostics::Format>,
    pub force_dormant_start: bool,
    pub from: String,
    pub show_spinner: bool,
    pub ignore_hh_version: bool,
    pub saved_state_ignore_hhconfig: bool,
    pub paths: Vec<String>,
    pub max_errors: Option<isize>,
    /// Whether to show preexisint warnings in typechecked files
    pub preexisting_warnings: bool,
    pub reason: Option<String>,
    pub mode: ClientMode,
    pub no_load: bool,
    pub save_64bit: Option<String>,
    pub save_human_readable_64bit_dep_map: Option<String>,
    pub output_json: bool,
    pub output_jsonl: bool,
    pub prechecked: Option<bool>,
    pub mini_state: Option<String>,
    pub root: path::T,
    pub sort_results: bool,
    pub stdin_name: Option<String>,
    pub deadline: Option<f64>,
    pub watchman_debug_logging: bool,
    pub allow_non_opt_build: bool,
    /// desc is a human-readable string description, to appear in "hh_server busy [desc]"
    pub desc: String,
    /// Determined based on the --from option. Affects UI behaviour in a
    /// number of places, e.g., error formatting and spinners.
    pub is_interactive: bool,
    pub warning_switches: Vec<filter_diagnostics::Switch>,
    pub dump_config: bool,
}

pub fn string_to_rename_mode(s: &str) -> RenameMode {
    match s {
        "Function" => RenameMode::Function,
        "Class" => RenameMode::Class,
        "Method" => RenameMode::Method,
        _ => {
            use std::io::Write;
            eprint!(
                "Error: please provide one of the following rename modes: Function, Class, or Method. \n"
            );
            let _ = std::io::stderr().flush();
            crate::rt::ocaml_arg::stdlib_exit(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn variant_names() {
        assert_eq!(
            variants_of_client_mode::to_name(&ClientMode::ModeStatusFiles(StatusFiles {
                filenames: vec![],
                show_tast: false,
                preexisting_warnings: false
            })),
            "MODE_STATUS_FILES"
        );
        assert_eq!(
            variants_of_client_mode::to_rank(&ClientMode::ModePackageLintFull((
                String::new(),
                vec![]
            ))),
            58
        );
        assert_eq!(
            variants_of_client_mode::to_rank(&ClientMode::ModeValidateIsolation(String::new())),
            53
        );
        assert_eq!(string_to_rename_mode("Method"), RenameMode::Method);
    }

    /// `to_name` gives the OCaml constructor names (`MODE_IN_MEMORY_DEP_TABLE_SIZE`),
    /// not the Rust variants (`ModeInMemoryDepTableSize`).
    #[test]
    fn to_name_prints_the_ocaml_constructor_names() {
        use ClientMode::*;
        for (t, name) in [
            (ModeCstSearch(None), "MODE_CST_SEARCH"),
            (ModeFullFidelitySchema, "MODE_FULL_FIDELITY_SCHEMA"),
            (ModeHackToNotebook, "MODE_HACK_TO_NOTEBOOK"),
            (ModeIdentifySymbol1(String::new()), "MODE_IDENTIFY_SYMBOL1"),
            (ModeInMemoryDepTableSize, "MODE_IN_MEMORY_DEP_TABLE_SIZE"),
            (ModeLint, "MODE_LINT"),
            (ModeListFiles, "MODE_LIST_FILES"),
            (ModeOutline2, "MODE_OUTLINE2"),
            (ModeRemoveDeadUnsafeCasts, "MODE_REMOVE_DEAD_UNSAFE_CASTS"),
            (ModeRewriteDeclarations, "MODE_REWRITE_DECLARATIONS"),
            (ModeServerRage, "MODE_SERVER_RAGE"),
            (ModeStatus, "MODE_STATUS"),
            (ModeTypeAtPosBatch(vec![]), "MODE_TYPE_AT_POS_BATCH"),
            (ModeIsSubtype, "MODE_IS_SUBTYPE"),
            (ModeFileLevelDependencies, "MODE_FILE_LEVEL_DEPENDENCIES"),
            (ModeValidateIsolation(String::new()), "MODE_VALIDATE_ISOLATION"),
            (ModeDepsInAtPosBatch(vec![]), "MODE_DEPS_IN_AT_POS_BATCH"),
        ] {
            assert_eq!(variants_of_client_mode::to_name(&t), name);
        }
    }
}
