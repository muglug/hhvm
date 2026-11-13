// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_env.ml`. See `hh/PORTING.md`.
//!
//! The constructors of `client_mode` are named as `hh_oxidize` names
//! constructors (`MODE_STATUS_SINGLE` is `MODESTATUSSINGLE`), and their lists
//! are `Vec`s in the order of the OCaml lists (head first).
//! `[@@deriving variants]` gives `Variants_of_client_mode`, of which
//! [`variants_of_client_mode::to_name`] and `to_rank` are ported.

#![allow(non_camel_case_types)]

use crate::diagnostics_state;
use crate::filter_diagnostics;
use crate::find_refs_wire_format;
use crate::path;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RenameMode {
    Function,
    Class,
    Method,
    Unspecified,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatusSingle {
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
    MODECSTSEARCH(Option<Vec<String>>),
    MODEDUMPSYMBOLINFO(String),
    MODEFINDCLASSREFS(String),
    MODEFINDREFS(String),
    MODEFINDMYTESTS(String),
    MODEFULLFIDELITYPARSE(String),
    MODEFULLFIDELITYSCHEMA,
    MODEGOTOIMPLCLASS(String),
    MODEGOTOIMPLMETHOD(String),
    MODEHACKTONOTEBOOK,
    MODEIDEFINDREFSBYSYMBOL(find_refs_wire_format::cli_args::T),
    MODEIDEGOTOIMPLBYSYMBOL(find_refs_wire_format::cli_args::T),
    MODEIDERENAMEBYSYMBOL(String),
    MODEIDENTIFYSYMBOL1(String),
    MODEIDENTIFYSYMBOL2(String),
    MODEIDENTIFYSYMBOL3(String),
    MODEIDENTIFYSYMBOL(String),
    MODEINMEMORYDEPTABLESIZE,
    MODELINT,
    MODELINTALL(isize),
    MODELINTSTDIN(String),
    MODELISTFILES,
    MODEMETHODJUMPANCESTORS(String, String),
    MODEMETHODJUMPANCESTORSBATCH(Vec<String>, String),
    MODEMETHODJUMPCHILDREN(String),
    MODENOTEBOOKTOHACK {
        notebook_number: String,
        notebook_header: String,
    },
    MODEOUTLINE,
    MODEOUTLINE2,
    MODEOUTLINEFORAGENTS(String),
    MODERENAME(RenameMode, String, String),
    MODEREMOVEDEADFIXMES(Vec<isize>),
    MODEREMOVEDEADUNSAFECASTS,
    MODEREWRITEDECLARATIONS,
    MODEREWRITELAMBDAPARAMETERS(Vec<String>),
    MODESAVENAMING(String),
    MODESEARCH(String),
    MODESERVERRAGE,
    MODESTATS,
    MODESTATUS,
    MODESTATUSSINGLE(StatusSingle),
    MODELOGERRORS(LogErrorsParams),
    MODETYPEATPOS(String),
    MODEINFERDYNAMIC(String, bool),
    MODEENFORCEMENTATPOSBATCH(Vec<String>),
    MODETYPEATPOSBATCH(Vec<String>),
    MODETYPEERRORATPOS(String),
    MODEISSUBTYPE,
    MODETASTHOLES(String),
    MODETASTHOLESBATCH(String),
    MODEFUNDEPSATPOSBATCH(Vec<String>),
    MODEFILELEVELDEPENDENCIES,
    MODEFINDISOLATABLECLUSTERS,
    MODEVERBOSE(bool),
    MODEDEPSOUTATPOSBATCH(Vec<String>),
    MODEDEPSINATPOSBATCH(Vec<String>),
    MODEPACKAGELINT(String),
    MODEPACKAGELINTFULL((String, Vec<String>)),
}

/// `Variants_of_client_mode` (`[@@deriving variants]`)
pub mod variants_of_client_mode {
    use super::ClientMode;
    use super::ClientMode::*;

    /// The OCaml name of the constructor (`"MODE_STATUS"`).
    pub fn to_name(t: &ClientMode) -> &'static str {
        match t {
            MODECSTSEARCH(_) => "MODE_CST_SEARCH",
            MODEDUMPSYMBOLINFO(_) => "MODE_DUMP_SYMBOL_INFO",
            MODEFINDCLASSREFS(_) => "MODE_FIND_CLASS_REFS",
            MODEFINDREFS(_) => "MODE_FIND_REFS",
            MODEFINDMYTESTS(_) => "MODE_FIND_MY_TESTS",
            MODEFULLFIDELITYPARSE(_) => "MODE_FULL_FIDELITY_PARSE",
            MODEFULLFIDELITYSCHEMA => "MODE_FULL_FIDELITY_SCHEMA",
            MODEGOTOIMPLCLASS(_) => "MODE_GO_TO_IMPL_CLASS",
            MODEGOTOIMPLMETHOD(_) => "MODE_GO_TO_IMPL_METHOD",
            MODEHACKTONOTEBOOK => "MODE_HACK_TO_NOTEBOOK",
            MODEIDEFINDREFSBYSYMBOL(_) => "MODE_IDE_FIND_REFS_BY_SYMBOL",
            MODEIDEGOTOIMPLBYSYMBOL(_) => "MODE_IDE_GO_TO_IMPL_BY_SYMBOL",
            MODEIDERENAMEBYSYMBOL(_) => "MODE_IDE_RENAME_BY_SYMBOL",
            MODEIDENTIFYSYMBOL1(_) => "MODE_IDENTIFY_SYMBOL1",
            MODEIDENTIFYSYMBOL2(_) => "MODE_IDENTIFY_SYMBOL2",
            MODEIDENTIFYSYMBOL3(_) => "MODE_IDENTIFY_SYMBOL3",
            MODEIDENTIFYSYMBOL(_) => "MODE_IDENTIFY_SYMBOL",
            MODEINMEMORYDEPTABLESIZE => "MODE_IN_MEMORY_DEP_TABLE_SIZE",
            MODELINT => "MODE_LINT",
            MODELINTALL(_) => "MODE_LINT_ALL",
            MODELINTSTDIN(_) => "MODE_LINT_STDIN",
            MODELISTFILES => "MODE_LIST_FILES",
            MODEMETHODJUMPANCESTORS(..) => "MODE_METHOD_JUMP_ANCESTORS",
            MODEMETHODJUMPANCESTORSBATCH(..) => "MODE_METHOD_JUMP_ANCESTORS_BATCH",
            MODEMETHODJUMPCHILDREN(_) => "MODE_METHOD_JUMP_CHILDREN",
            MODENOTEBOOKTOHACK { .. } => "MODE_NOTEBOOK_TO_HACK",
            MODEOUTLINE => "MODE_OUTLINE",
            MODEOUTLINE2 => "MODE_OUTLINE2",
            MODEOUTLINEFORAGENTS(_) => "MODE_OUTLINE_FOR_AGENTS",
            MODERENAME(..) => "MODE_RENAME",
            MODEREMOVEDEADFIXMES(_) => "MODE_REMOVE_DEAD_FIXMES",
            MODEREMOVEDEADUNSAFECASTS => "MODE_REMOVE_DEAD_UNSAFE_CASTS",
            MODEREWRITEDECLARATIONS => "MODE_REWRITE_DECLARATIONS",
            MODEREWRITELAMBDAPARAMETERS(_) => "MODE_REWRITE_LAMBDA_PARAMETERS",
            MODESAVENAMING(_) => "MODE_SAVE_NAMING",
            MODESEARCH(_) => "MODE_SEARCH",
            MODESERVERRAGE => "MODE_SERVER_RAGE",
            MODESTATS => "MODE_STATS",
            MODESTATUS => "MODE_STATUS",
            MODESTATUSSINGLE(_) => "MODE_STATUS_SINGLE",
            MODELOGERRORS(_) => "MODE_LOG_ERRORS",
            MODETYPEATPOS(_) => "MODE_TYPE_AT_POS",
            MODEINFERDYNAMIC(..) => "MODE_INFER_DYNAMIC",
            MODEENFORCEMENTATPOSBATCH(_) => "MODE_ENFORCEMENT_AT_POS_BATCH",
            MODETYPEATPOSBATCH(_) => "MODE_TYPE_AT_POS_BATCH",
            MODETYPEERRORATPOS(_) => "MODE_TYPE_ERROR_AT_POS",
            MODEISSUBTYPE => "MODE_IS_SUBTYPE",
            MODETASTHOLES(_) => "MODE_TAST_HOLES",
            MODETASTHOLESBATCH(_) => "MODE_TAST_HOLES_BATCH",
            MODEFUNDEPSATPOSBATCH(_) => "MODE_FUN_DEPS_AT_POS_BATCH",
            MODEFILELEVELDEPENDENCIES => "MODE_FILE_LEVEL_DEPENDENCIES",
            MODEFINDISOLATABLECLUSTERS => "MODE_FIND_ISOLATABLE_CLUSTERS",
            MODEVERBOSE(_) => "MODE_VERBOSE",
            MODEDEPSOUTATPOSBATCH(_) => "MODE_DEPS_OUT_AT_POS_BATCH",
            MODEDEPSINATPOSBATCH(_) => "MODE_DEPS_IN_AT_POS_BATCH",
            MODEPACKAGELINT(_) => "MODE_PACKAGE_LINT",
            MODEPACKAGELINTFULL(_) => "MODE_PACKAGE_LINT_FULL",
        }
    }

    /// The position of the constructor in the type definition, from 0.
    pub fn to_rank(t: &ClientMode) -> isize {
        match t {
            MODECSTSEARCH(_) => 0,
            MODEDUMPSYMBOLINFO(_) => 1,
            MODEFINDCLASSREFS(_) => 2,
            MODEFINDREFS(_) => 3,
            MODEFINDMYTESTS(_) => 4,
            MODEFULLFIDELITYPARSE(_) => 5,
            MODEFULLFIDELITYSCHEMA => 6,
            MODEGOTOIMPLCLASS(_) => 7,
            MODEGOTOIMPLMETHOD(_) => 8,
            MODEHACKTONOTEBOOK => 9,
            MODEIDEFINDREFSBYSYMBOL(_) => 10,
            MODEIDEGOTOIMPLBYSYMBOL(_) => 11,
            MODEIDERENAMEBYSYMBOL(_) => 12,
            MODEIDENTIFYSYMBOL1(_) => 13,
            MODEIDENTIFYSYMBOL2(_) => 14,
            MODEIDENTIFYSYMBOL3(_) => 15,
            MODEIDENTIFYSYMBOL(_) => 16,
            MODEINMEMORYDEPTABLESIZE => 17,
            MODELINT => 18,
            MODELINTALL(_) => 19,
            MODELINTSTDIN(_) => 20,
            MODELISTFILES => 21,
            MODEMETHODJUMPANCESTORS(..) => 22,
            MODEMETHODJUMPANCESTORSBATCH(..) => 23,
            MODEMETHODJUMPCHILDREN(_) => 24,
            MODENOTEBOOKTOHACK { .. } => 25,
            MODEOUTLINE => 26,
            MODEOUTLINE2 => 27,
            MODEOUTLINEFORAGENTS(_) => 28,
            MODERENAME(..) => 29,
            MODEREMOVEDEADFIXMES(_) => 30,
            MODEREMOVEDEADUNSAFECASTS => 31,
            MODEREWRITEDECLARATIONS => 32,
            MODEREWRITELAMBDAPARAMETERS(_) => 33,
            MODESAVENAMING(_) => 34,
            MODESEARCH(_) => 35,
            MODESERVERRAGE => 36,
            MODESTATS => 37,
            MODESTATUS => 38,
            MODESTATUSSINGLE(_) => 39,
            MODELOGERRORS(_) => 40,
            MODETYPEATPOS(_) => 41,
            MODEINFERDYNAMIC(..) => 42,
            MODEENFORCEMENTATPOSBATCH(_) => 43,
            MODETYPEATPOSBATCH(_) => 44,
            MODETYPEERRORATPOS(_) => 45,
            MODEISSUBTYPE => 46,
            MODETASTHOLES(_) => 47,
            MODETASTHOLESBATCH(_) => 48,
            MODEFUNDEPSATPOSBATCH(_) => 49,
            MODEFILELEVELDEPENDENCIES => 50,
            MODEFINDISOLATABLECLUSTERS => 51,
            MODEVERBOSE(_) => 52,
            MODEDEPSOUTATPOSBATCH(_) => 53,
            MODEDEPSINATPOSBATCH(_) => 54,
            MODEPACKAGELINT(_) => 55,
            MODEPACKAGELINTFULL(_) => 56,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ClientCheckEnv {
    pub autostart: bool,
    pub config: Vec<(String, String)>,
    pub custom_hhi_path: Option<String>,
    pub custom_telemetry_data: Vec<(String, String)>,
    pub error_format: Option<diagnostics_state::Format>,
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
    /// desc is a human-readable string description, to appear in "hh_server busy [desc]"
    pub allow_non_opt_build: bool,
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
            variants_of_client_mode::to_name(&ClientMode::MODESTATUSSINGLE(StatusSingle {
                filenames: vec![],
                show_tast: false,
                preexisting_warnings: false
            })),
            "MODE_STATUS_SINGLE"
        );
        assert_eq!(
            variants_of_client_mode::to_rank(&ClientMode::MODEPACKAGELINTFULL((
                String::new(),
                vec![]
            ))),
            56
        );
        assert_eq!(string_to_rename_mode("Method"), RenameMode::Method);
    }
}
