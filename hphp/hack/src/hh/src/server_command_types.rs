// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server_command_types.ml`. See `hh/PORTING.md`.
//!
//! # The GADT
//!
//! `type _ t` (an RPC command, indexed by the type of its result) is two
//! enums with the same variant names (the OCaml constructors, in the style of
//! `crate::client_env`: `STATUS_SINGLE` is `STATUSSINGLE`):
//!
//! - [`T`], the command and its arguments (`'a t`);
//! - [`CommandResult`], the result of each command (the `'a`), which the
//!   server answers with.
//!
//! [`ResultOf`] gives a command's result its OCaml type back: a caller of
//! `Client_connect.rpc` names the type it expects, as OCaml's type checker
//! infers it (`let (status, telemetry): (server_status::T, _) = rpc(..)`).
//!
//! Both enums cross the socket (`crate::rt::protocol`), so they are
//! `serde`. The types of other modules that have no `serde` of their own get
//! it in `crate::rt::protocol::wire`, except two that cannot (see there):
//! `Filter_diagnostics.Filter.t` (private fields; a `todo!`), and what needs
//! the typing port (`Tast` in `STATUS_SINGLE`'s result, `Lints_core.t` in
//! the lint results).
//!
//! # Not ported
//!
//! - The printers that `[@@deriving show]` gives `Method_jumps.filter`,
//!   `Find_my_tests` (`member`, `action_kind`, `action`, `version`,
//!   `config`), `Symbol_type.t`, `Symbol_info_service.target_type` and
//!   `symbol_fun_call`, `Ide_rename_type.t`, `Tast_hole.filter`,
//!   `file_input`, `lint_stdin_input`, `cst_search_input`, `errors` and
//!   `diagnostic_errors`: nothing calls them (the OCaml neither).
//! - The converters that `[@@deriving yojson]` gives `Find_my_tests`
//!   (`provenance`, `reason_count`, ..., `config`, `json_input`), which only
//!   `hh_client --find-my-tests` (Meta-only, design 5.3) uses. The explicit
//!   `yojson_of_version` and `version_of_yojson` are ported.
//! - `Rename.arguments_to_string_exn` and `string_to_args` are ported up to
//!   OCaml's `Marshal` of the `Symbol_definition.t` (and its base64), which
//!   has no Rust implementation yet (`crate::rt::ocaml_marshal`, design 7.8):
//!   a `todo!`.
//!
//! `Lwt` is gone (`Done_or_retry.call` takes a closure that returns the
//! result). `Diagnostics.finalized_diagnostic` is
//! `crate::server_progress::FinalizedDiagnostic`.

#![allow(non_camel_case_types)]

use std::cmp::Ordering;

use oxidized::pos::Pos;
use serde::Deserialize;
use serde::Serialize;

use crate::connection_tracker;
use crate::exit_status;
use crate::exit_status::ExitWith;
use crate::file_content;
use crate::filter_diagnostics;
use crate::find_refs_wire_format;
use crate::infer_at_pos_service;
use crate::infer_error_at_pos_service;
use crate::pos::Absolute;
use crate::s_map;
use crate::save_state_service_types;
use crate::server_lint_types;
use crate::server_notifier_types;
use crate::server_progress::FinalizedDiagnostic;
use crate::server_rage_types;
use crate::server_rename_types;
use crate::stats;
use crate::string_utils;
use crate::symbol_definition;
use crate::symbol_occurrence;
use crate::tast_holes_service;
use crate::telemetry;
use crate::user_diagnostic;
use crate::utils;
use crate::yojson::safe as yojson;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConnectionType {
    NonPersistent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConnectionResponse {
    Connected,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StatusLiveness {
    StaleStatus,
    LiveStatus,
}

/// `Server_command_types.Server_status`
pub mod server_status {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct T {
        pub liveness: StatusLiveness,
        pub error_list: Vec<FinalizedDiagnostic>,
        pub dropped_count: isize,
        pub last_recheck_stats: Option<telemetry::T>,
        pub file_watcher_clock: Option<server_notifier_types::Clock>,
    }
}

/// `Server_command_types.Identify_symbol`
pub mod identify_symbol {
    use super::*;

    pub type SingleResult = (
        symbol_occurrence::T<Absolute>,
        Option<symbol_definition::T<Absolute>>,
    );

    pub type Result = Vec<SingleResult>;
}

/// `Server_command_types.Method_jumps`
pub mod method_jumps {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct Result {
        pub orig_name: String,
        pub orig_pos: Absolute,
        pub dest_name: String,
        pub dest_pos: Absolute,
        pub orig_p_name: String,
        /// Used for methods to find their parent class
        pub dest_p_name: String,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum Filter {
        NoFilter,
        Class,
        Interface,
        Trait,
    }

    pub fn readable_place(name: &str, pos: &Absolute, p_name: &str) -> String {
        let readable = crate::pos::string(pos);
        if !p_name.is_empty() {
            format!(
                "{} {}::{}",
                readable,
                utils::strip_ns(p_name),
                utils::strip_ns(name)
            )
        } else {
            format!("{} {}", readable, utils::strip_ns(name))
        }
    }

    pub fn print_readable(res: &[Result], find_children: bool) {
        for res in res {
            let origin_readable = readable_place(&res.orig_name, &res.orig_pos, &res.orig_p_name);
            let dest_readable = readable_place(&res.dest_name, &res.dest_pos, &res.dest_p_name);
            let extended = format!("inherited {}", if find_children { "by" } else { "from" });
            println!("{}\n    {} {}", origin_readable, extended, dest_readable);
        }
    }
}

/// `Server_command_types.Done_or_retry`
///
/// This is an ugly hack to support following case:
/// - client issues a command that requires full recheck. Server knows not to
///   accept it until full check is completed .
/// - while processing the command, it turns out that we need to recheck even
///   more files for full check to be "good enough" for this command
///
/// This can happen when combining prechecked files and find references.
/// We could store the client with its command somwhere, and come back to it
/// after this additional rechecking is done, but in practice this is ugly to
/// implement in current atchitecture. What is easier to do instead, is to
/// return a special "Retry" response to the client, which will cause it to
/// re-issue the same request (which will once again not be accepted until full
/// check is completed. Since command is the same, its second execution should
/// not add even more files to recheck, hence a limit of only two attempts.
///
/// In other words: the goal of this is to avoid implementing even more
/// server-side client queing mechanisms, but re-use an existing "clients waiting
/// for full check" queue.
pub mod done_or_retry {
    use super::*;

    /// `exception Two_retries_in_a_row` (OCaml's `Lwt.fail`, which nothing
    /// catches before `hh_client`'s toplevel): the `Err` of [`call`], which
    /// passes on what `f` returns as its `Err` too.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Two_retries_in_a_row;

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub enum T<A> {
        Done(A),
        Retry,
    }

    /// Note: this is designed to work with calls that always will succeed on second try
    /// (the reason for retrying is a one time event that is resolved during first call).
    /// If this ends up throwing, it's a bug in hh_server.
    fn call_depth<A, E: From<Two_retries_in_a_row>>(
        f: &mut dyn FnMut() -> Result<T<A>, E>,
        depth: isize,
    ) -> Result<A, E> {
        if depth == 2 {
            return Err(Two_retries_in_a_row.into());
        }
        let result = f()?;
        match result {
            T::Done(x) => Ok(x),
            T::Retry => call_depth(f, depth + 1),
        }
    }

    /// Call the function returning Done_or_retry.t with at most one retry, expecting
    /// that this is enough to yield a non-Retry value, which is returned
    pub fn call<A, E: From<Two_retries_in_a_row>>(
        mut f: impl FnMut() -> Result<T<A>, E>,
    ) -> Result<A, E> {
        call_depth(&mut f, 0)
    }

    /// Helper function useful when mapping over results from functions that (in addition
    /// to Done_or_retry.t result) thread through some kind of environment.
    pub fn map_env<Env, A, B>(f: impl FnOnce(A) -> B, (env, x): (Env, T<A>)) -> (Env, T<B>) {
        match x {
            T::Done(x) => (env, T::Done(f(x))),
            T::Retry => (env, T::Retry),
        }
    }
}

/// `Server_command_types.Find_refs` (`include Search_types.Find_refs`)
pub mod find_refs {
    pub use crate::search_types::find_refs::*;

    use super::done_or_retry;

    pub type ServerResult = Vec<crate::search_types::find_refs::T>;

    pub type Result = Vec<crate::search_types::find_refs::Absolute>;

    pub type ServerResultOrRetry = done_or_retry::T<ServerResult>;

    pub type ResultOrRetry = done_or_retry::T<Result>;
}

/// `Server_command_types.Package_lint`
pub mod package_lint {
    use super::*;

    pub type Result = Vec<(find_refs::Action, find_refs::Result)>;

    pub type ResultOrRetry = done_or_retry::T<Result>;

    pub type FastResult = crate::relative_path::set::T;
}

/// `Server_command_types.Find_my_tests`
pub mod find_my_tests {
    use super::*;
    use crate::rt::yojson_conv;

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct Member {
        pub class_name: String,
        pub member_name: String,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum ActionKind {
        Class { class_name: String },
        Typedef { name: String },
        Method(Member),
        Typeconst(Member),
        ClassConst(Member),
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct Action {
        pub kind: ActionKind,
        /// Silently drop this root if the symbol does not exist.
        /// For top-level definitions (classes, typedefs), the symbol must be
        /// declared. For class members, it is sufficient for the member to be
        /// defined on the class, even if only inherited (not declared in the
        /// class itself).
        pub soft: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct Provenance {
        pub root_indices: Vec<isize>,
    }

    /// Count for one edge-reason key in a reason-provenance multiset. The
    /// [edge_key] records the reason used by an edge, together with its source and
    /// target kinds, as "source_kind[root=...]|reason|target_kind".
    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct ReasonCount {
        pub edge_key: String,
        pub count: isize,
    }

    /// One minimal multiset of edge-reason keys occurring on paths from a root to a
    /// selected test (used for reason provenance).
    pub type ReasonMultiset = Vec<ReasonCount>;

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct SelectedCldpMember {
        pub member_name: String,
        /// Wall-clock seconds from the start of selection to when this CLDP test
        /// member was first selected.
        pub selected_after_secs: f64,
        /// Indices into [result_data.reason_provenance] for this CLDP test member.
        /// [None] when reason provenance is not requested.
        pub reason_provenance_indices: Option<Vec<isize>>,
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct SelectedTestMethod {
        pub method_name: String,
        /// Wall-clock seconds from the start of selection to when this test
        /// method was first selected.
        pub selected_after_secs: f64,
        pub uses_cldp: Option<bool>,
        pub cldp_members: Option<Vec<SelectedCldpMember>>,
        /// Indices into [result_data.reason_provenance] for this test method.
        pub reason_provenance_indices: Option<Vec<isize>>,
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct SelectedTestClass {
        pub class_name: String,
        /// Wall-clock seconds from the start of selection to when this test
        /// class was first selected.
        pub selected_after_secs: f64,
        pub methods: Vec<SelectedTestMethod>,
        /// Indices into [result_data.reason_provenance] for this test class.
        pub reason_provenance_indices: Option<Vec<isize>>,
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct SelectedTestFile {
        pub file_path: String,
        pub distance: isize,
        /// Wall-clock seconds from the start of selection to when this test was
        /// first selected (i.e. when its node was first added to the graph).
        pub selected_after_secs: f64,
        pub provenance: Option<Provenance>,
        pub test_classes: Option<Vec<SelectedTestClass>>,
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct ResultData {
        pub selected_test_files: Vec<SelectedTestFile>,
        pub out_of_time: bool,
        /// Interned pool of minimal multisets referenced by the
        /// [reason_provenance_indices] fields throughout the result. [None]
        /// when reason provenance is not requested.
        pub reason_provenance: Option<Vec<ReasonMultiset>>,
    }

    pub type Result = std::result::Result<ResultData, String>;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum Version {
        V2,
        Staging,
    }

    pub fn yojson_of_version(v: Version) -> yojson::T {
        match v {
            Version::V2 => yojson::T::String("v2".to_string()),
            Version::Staging => yojson::T::String("staging".to_string()),
        }
    }

    /// Raises `Of_yojson_error` (returns it) on anything else, as
    /// `Ppx_yojson_conv_lib.Yojson_conv.of_yojson_error`.
    pub fn version_of_yojson(
        json: &yojson::T,
    ) -> std::result::Result<Version, yojson_conv::OfYojsonError> {
        match json {
            yojson::T::String(s) if s == "v2" => Ok(Version::V2),
            yojson::T::String(s) if s == "staging" => Ok(Version::Staging),
            json => yojson_conv::of_yojson_error("invalid FindMyTests version", json),
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct Config {
        pub max_distance: isize,
        pub max_test_files: Option<isize>,
        pub root_provenance: bool,
        /// Track, per selected test, the minimal multisets of edge-type reasons
        /// on paths from a root that caused its selection.
        pub reason_provenance: bool,
        pub time_limit_secs: Option<isize>,
        /// Elapsed-time checkpoints (in seconds) at which to record the number of selected test files.
        pub test_count_checkpoint_secs: Vec<isize>,
        /// Record elapsed time whenever this many symbol nodes have been constructed.
        pub symbol_node_count_checkpoint_interval: Option<isize>,
        /// Record elapsed time whenever this many test file nodes have been constructed.
        pub test_file_node_count_checkpoint_interval: Option<isize>,
        pub max_method_parent_steps: Option<isize>,
        pub max_class_parent_steps: Option<isize>,
        /// If a symbol is obtained from parent walking and its fanout is larger than this number
        /// of files, we skip searching  those files for references entirely.
        pub parent_max_fanout_files: Option<isize>,
        /// If a symbol is NOT obtained from parent walking and its fanout is larger than this number
        /// of files, we skip searching those files for references entirely.
        pub non_parent_max_fanout_files: Option<isize>,
        /// Should we go from any method to the enclosing class, or just for root methods?
        pub enclosing_class_all_methods: bool,
        pub cldp_member_selection: bool,
    }

    pub fn default_config() -> Config {
        Config {
            max_distance: 1,
            max_test_files: None,
            root_provenance: false,
            reason_provenance: false,
            time_limit_secs: None,
            test_count_checkpoint_secs: vec![20, 30, 40],
            symbol_node_count_checkpoint_interval: None,
            test_file_node_count_checkpoint_interval: None,
            max_method_parent_steps: None,
            max_class_parent_steps: None,
            parent_max_fanout_files: None,
            non_parent_max_fanout_files: None,
            enclosing_class_all_methods: true,
            cldp_member_selection: false,
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct JsonInput {
        pub roots: Vec<String>,
        pub config: Config,
        pub version: Version,
    }
}

/// `Server_command_types.Rename`
pub mod rename {
    use super::*;

    pub type IdeResult = std::result::Result<Vec<server_rename_types::Patch>, String>;

    pub type Result = Vec<server_rename_types::Patch>;

    pub type IdeResultOrRetry = done_or_retry::T<IdeResult>;

    pub type ResultOrRetry = done_or_retry::T<Result>;

    /// Returns a string in the form of
    /// NEW_NAME|COMMA_SEPARATED_FIND_REFS_ACTION|OCaml_marshalled_SymbolDefinition.T
    pub fn arguments_to_string_exn(
        new_name: &str,
        action: &find_refs::Action,
        _symbol_def: &symbol_definition::T<Pos>,
    ) -> std::result::Result<String, ExitWith> {
        let _symbol_and_action =
            find_refs_wire_format::cli_args::to_string(&find_refs_wire_format::cli_args::T {
                symbol_name: new_name.to_string(),
                action: action.clone(),
                stream_file: None,
                hint_suffixes: vec![],
            })?;
        // `let marshalled_def = Marshal.to_string symbol_def [] in let
        // encoded = Base64.encode_exn marshalled_def in Printf.sprintf "%s|%s"
        // symbol_and_action encoded`
        todo!(
            "Server_command_types.Rename.arguments_to_string_exn: OCaml's Marshal of a Symbol_definition.t (crate::rt::ocaml_marshal, design 7.8) does not exist yet"
        )
    }

    /// Expects a string in the form of
    /// NEW_NAME|COMMA_SEPARATED_FIND_REFS_ACTION|OCaml_marshalled_SymbolDefinition.T
    /// For example, a valid entry is
    /// HackTypecheckerQueryBase::WWWDir|Member,\HackTypecheckerQueryBase,Method,getWWWDir|<byte_string>
    pub fn string_to_args(
        arg: &str,
    ) -> std::result::Result<(String, find_refs::Action, symbol_definition::T<Pos>), ExitWith>
    {
        let split_arg = string_utils::split('|', arg);
        let (symbol_name, action_arg, _marshalled_def) = match split_arg.as_slice() {
            [symbol_name, action_arg, marshalled_def] => {
                (symbol_name.clone(), action_arg.clone(), marshalled_def.clone())
            }
            _ => {
                eprint!("Invalid input\n");
                return Err(ExitWith(exit_status::T::InputError));
            }
        };
        let str = format!("{}|{}", symbol_name, action_arg);
        let find_refs_wire_format::cli_args::T {
            symbol_name: _new_name,
            action: _action,
            ..
        } = find_refs_wire_format::cli_args::from_string_exn(&str)?;
        // `let decoded_str = Base64.decode_exn marshalled_def in let
        // symbol_definition = Marshal.from_string decoded_str 0 in (new_name,
        // action, symbol_definition)`
        todo!(
            "Server_command_types.Rename.string_to_args: OCaml's Marshal of a Symbol_definition.t (crate::rt::ocaml_marshal, design 7.8) does not exist yet"
        )
    }
}

/// `Server_command_types.Symbol_type`
pub mod symbol_type {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct T {
        pub pos: Absolute,
        pub type_: String,
        pub ident_: isize,
    }
}

/// `Server_command_types.Symbol_info_service`
pub mod symbol_info_service {
    use super::*;

    #[derive(
        Clone,
        Copy,
        Debug,
        PartialEq,
        Eq,
        PartialOrd,
        Ord,
        Serialize,
        Deserialize
    )]
    pub enum TargetType {
        Function,
        Method,
        Constructor,
    }

    /// `compare_target_type` (`[@@deriving ord]`): by constructor.
    pub fn compare_target_type(a: TargetType, b: TargetType) -> Ordering {
        a.cmp(&b)
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct SymbolFunCall {
        pub name: String,
        pub type_: TargetType,
        pub pos: Absolute,
        pub caller: String,
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct Result {
        pub fun_calls: Vec<SymbolFunCall>,
        pub symbol_types: Vec<symbol_type::T>,
    }

    pub fn fun_call_to_json(fun_call_results: &[SymbolFunCall]) -> Vec<yojson::T> {
        fun_call_results
            .iter()
            .map(|item| {
                let item_type = match item.type_ {
                    TargetType::Function => "Function",
                    TargetType::Method => "Method",
                    TargetType::Constructor => "Constructor",
                };
                yojson::T::Assoc(vec![
                    ("name".to_string(), yojson::T::String(item.name.clone())),
                    ("type".to_string(), yojson::T::String(item_type.to_string())),
                    ("pos".to_string(), crate::pos::json(&item.pos)),
                    ("caller".to_string(), yojson::T::String(item.caller.clone())),
                ])
            })
            .collect()
    }

    pub fn symbol_type_to_json(symbol_type_results: &[symbol_type::T]) -> Vec<yojson::T> {
        // `List.rev_map`
        symbol_type_results
            .iter()
            .rev()
            .map(|item| {
                yojson::T::Assoc(vec![
                    ("pos".to_string(), crate::pos::json(&item.pos)),
                    ("type".to_string(), yojson::T::String(item.type_.clone())),
                    ("ident".to_string(), yojson::T::Int(item.ident_)),
                ])
            })
            .collect()
    }

    pub fn to_json(result: &Result) -> yojson::T {
        let fun_call_json = fun_call_to_json(&result.fun_calls);
        let symbol_type_json = symbol_type_to_json(&result.symbol_types);
        yojson::T::Assoc(vec![
            ("function_calls".to_string(), yojson::T::List(fun_call_json)),
            ("symbol_types".to_string(), yojson::T::List(symbol_type_json)),
        ])
    }
}

/// `Server_command_types.Outline`
pub mod outline {
    use super::*;

    pub type Outline = Vec<symbol_definition::T<Absolute>>;
}

/// `Server_command_types.Infer_return_type`
pub mod infer_return_type {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum T {
        Function(String),
        Method(String, String),
    }

    pub type Result = std::result::Result<String, String>;
}

/// `Server_command_types.Ide_rename_type`
pub mod ide_rename_type {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct T {
        pub filename: crate::relative_path::RelativePath,
        pub line: isize,
        pub char: isize,
        pub new_name: String,
    }
}

/// `Server_command_types.Go_to_definition`
pub mod go_to_definition {
    use super::*;

    pub type Result = Vec<(
        symbol_occurrence::T<Absolute>,
        symbol_definition::T<Absolute>,
    )>;
}

/// `Server_command_types.Go_to_type_definition`
pub mod go_to_type_definition {
    use super::*;

    pub type Result = Vec<(Absolute, String)>;
}

/// `Server_command_types.Tast_hole`
pub mod tast_hole {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum Filter {
        Typing,
        Cast,
        Any,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FileInput {
    FileName(String),
    FileContent(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LintStdinInput {
    pub filename: String,
    pub contents: String,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CstSearchInput {
    pub sort_results: bool,
    pub input: yojson::T,
    /// if None, search all files
    pub files_to_search: Option<Vec<String>>,
}

/// `` [ `Ok of Server_rename_types.patch list | `Error of string ] ``, the
/// result of `REMOVE_DEAD_FIXMES` and `REMOVE_DEAD_UNSAFE_CASTS`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum PatchesOrError {
    Ok(Vec<server_rename_types::Patch>),
    Error(String),
}

/// `Tast.program Tast_with_dynamic.t Relative_path.Map.t`, the TASTs that
/// `STATUS_SINGLE` returns when `return_expanded_tast` is set.
pub type Tasts = crate::relative_path::map::T<
    crate::tast_with_dynamic::T<crate::tast::Program>,
>;

/// The result of `STATUS_SINGLE`.
pub type StatusSingleResult = ((Vec<FinalizedDiagnostic>, isize), Option<Tasts>);

/// The following datatypes can be interpreted as follows:
/// MESSAGE_TAG : Argument type (sent from client to server) -> return type t
///
/// (`type _ t`: the command; its result is the variant of the same name of
/// [`CommandResult`].)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum T {
    /// -> `Server_status.t`
    STATUS {
        max_errors: Option<isize>,
        error_filter: filter_diagnostics::filter::T,
    },
    /// -> [`StatusSingleResult`]
    STATUSSINGLE {
        file_names: Vec<FileInput>,
        max_errors: Option<isize>,
        error_filter: filter_diagnostics::filter::T,
        return_expanded_tast: bool,
        /// Whether to show preexisting warnings
        /// (the ones that were there prior to saved state revision)
        preexisting_warnings: bool,
    },
    /// -> `unit`
    LOGERRORS {
        files: Vec<String>,
        log_file: Option<String>,
        error_filter: filter_diagnostics::filter::T,
        preexisting_warnings: bool,
    },
    /// -> `Infer_at_pos_service.result`
    INFERTYPE(FileInput, file_content::position::T),
    /// -> `Yojson.Safe.t`
    INFERDYNAMIC(String, bool),
    /// -> `string list`
    ENFORCEMENTATPOSBATCH(Vec<(String, file_content::position::T)>),
    /// -> `string list`
    INFERTYPEBATCH(
        Vec<(
            String,
            file_content::position::T,
            Option<file_content::position::T>,
        )>,
    ),
    /// -> `Infer_error_at_pos_service.result`
    INFERTYPEERROR(FileInput, isize, isize),
    /// -> `(string, string) result`
    ISSUBTYPE(String),
    /// -> `Tast_holes_service.result`
    TASTHOLES(FileInput, tast_hole::Filter),
    /// -> `Tast_holes_service.result`
    TASTHOLESBATCH(Vec<String>),
    /// -> `string Symbol_definition.t list`
    IDENTIFYSYMBOL(String),
    /// -> `Identify_symbol.result`
    IDENTIFYFUNCTION(String, FileInput, file_content::position::T),
    /// -> `Method_jumps.result list`
    METHODJUMP((String, method_jumps::Filter, bool)),
    /// -> `Method_jumps.result list`
    METHODJUMPBATCH((Vec<String>, method_jumps::Filter)),
    /// -> `Find_refs.result_or_retry`
    FINDREFS(find_refs::Action),
    /// -> `Find_refs.result_or_retry`
    GOTOIMPL(find_refs::Action),
    /// -> `Find_refs.result_or_retry`
    IDEFINDREFSBYSYMBOL(find_refs_wire_format::cli_args::T),
    /// -> `Find_refs.result_or_retry`
    IDEGOTOIMPLBYSYMBOL(find_refs_wire_format::cli_args::T),
    /// -> `Rename.result_or_retry`
    RENAME(server_rename_types::Action),
    /// -> `Rename.ide_result_or_retry`
    IDERENAMEBYSYMBOL(find_refs::Action, String, symbol_definition::T<Pos>),
    /// -> `Symbol_info_service.result`
    DUMPSYMBOLINFO(Vec<String>),
    /// -> [`PatchesOrError`]
    REMOVEDEADFIXMES(Vec<isize>),
    /// -> [`PatchesOrError`]
    REMOVEDEADUNSAFECASTS,
    /// -> `Server_rename_types.patch list`
    REWRITELAMBDAPARAMETERS(Vec<String>),
    /// -> `(int, string) result`
    INMEMORYDEPTABLESIZE,
    /// -> `(Save_state_service_types.save_naming_result, string) result`
    SAVENAMING(String),
    /// -> `unit`
    CHECKLIVENESS,
    /// -> `unit`
    ///
    /// Pause automatic rechecks until the next client connection. This uses
    /// the default pipe so that ongoing typechecking finishes first.
    PAUSE,
    /// -> `Server_lint_types.result`
    LINT(Vec<String>),
    /// -> `Server_lint_types.result`
    LINTSTDIN(LintStdinInput),
    /// -> `Server_lint_types.result`
    LINTALL(isize),
    /// -> `Stats.t`
    STATS,
    /// -> `string`
    DUMPFULLFIDELITYPARSE(String),
    /// -> `Server_rage_types.result`
    RAGE,
    /// -> `(Yojson.Safe.t, string) result`
    CSTSEARCH(CstSearchInput),
    /// -> `unit`
    NOPRECHECKEDFILES,
    /// -> `string list`
    FUNDEPSBATCH(Vec<(String, isize, isize)>),
    /// -> `string list`
    LISTFILESWITHERRORS,
    /// -> `string list`
    FILEDEPENDENTS(Vec<String>),
    /// -> `string list`
    FINDISOLATABLECLUSTERS,
    /// -> `unit`
    VERBOSE(bool),
    /// -> `string list`
    DEPSOUTBATCH(Vec<(String, isize, isize)>),
    /// -> `Find_refs.result_or_retry list`
    DEPSINBATCH(Vec<(String, isize, isize)>),
    /// -> `Find_my_tests.result`
    FINDMYTESTS(
        (
            find_my_tests::Version,
            find_my_tests::Config,
            Vec<find_my_tests::Action>,
        ),
    ),
    /// -> `Package_lint.fast_result`
    PACKAGELINT(String),
    /// -> `Package_lint.fast_result`
    PACKAGELINTFULL((String, Vec<String>)),
}

/// The `'a` of `'a t`: the result of each command, in the variant of the
/// command's name (not in OCaml, where the type checker knows it). The server
/// answers a [`T`] with the variant of the same name.
#[derive(Serialize, Deserialize)]
pub enum CommandResult {
    STATUS(server_status::T),
    STATUSSINGLE(
        #[serde(with = "crate::rt::protocol::wire::status_single_result")] StatusSingleResult,
    ),
    LOGERRORS(()),
    INFERTYPE(infer_at_pos_service::Result),
    INFERDYNAMIC(yojson::T),
    ENFORCEMENTATPOSBATCH(Vec<String>),
    INFERTYPEBATCH(Vec<String>),
    INFERTYPEERROR(infer_error_at_pos_service::Result),
    ISSUBTYPE(std::result::Result<String, String>),
    TASTHOLES(tast_holes_service::Result),
    TASTHOLESBATCH(tast_holes_service::Result),
    IDENTIFYSYMBOL(Vec<symbol_definition::T<Absolute>>),
    IDENTIFYFUNCTION(identify_symbol::Result),
    METHODJUMP(Vec<method_jumps::Result>),
    METHODJUMPBATCH(Vec<method_jumps::Result>),
    FINDREFS(find_refs::ResultOrRetry),
    GOTOIMPL(find_refs::ResultOrRetry),
    IDEFINDREFSBYSYMBOL(find_refs::ResultOrRetry),
    IDEGOTOIMPLBYSYMBOL(find_refs::ResultOrRetry),
    RENAME(rename::ResultOrRetry),
    IDERENAMEBYSYMBOL(rename::IdeResultOrRetry),
    DUMPSYMBOLINFO(symbol_info_service::Result),
    REMOVEDEADFIXMES(PatchesOrError),
    REMOVEDEADUNSAFECASTS(PatchesOrError),
    REWRITELAMBDAPARAMETERS(Vec<server_rename_types::Patch>),
    INMEMORYDEPTABLESIZE(std::result::Result<isize, String>),
    SAVENAMING(std::result::Result<save_state_service_types::SaveNamingResult, String>),
    CHECKLIVENESS(()),
    PAUSE(()),
    LINT(server_lint_types::Result),
    LINTSTDIN(server_lint_types::Result),
    LINTALL(server_lint_types::Result),
    STATS(stats::T),
    DUMPFULLFIDELITYPARSE(String),
    RAGE(server_rage_types::Result),
    CSTSEARCH(std::result::Result<yojson::T, String>),
    NOPRECHECKEDFILES(()),
    FUNDEPSBATCH(Vec<String>),
    LISTFILESWITHERRORS(Vec<String>),
    FILEDEPENDENTS(Vec<String>),
    FINDISOLATABLECLUSTERS(Vec<String>),
    VERBOSE(()),
    DEPSOUTBATCH(Vec<String>),
    DEPSINBATCH(Vec<find_refs::ResultOrRetry>),
    FINDMYTESTS(find_my_tests::Result),
    PACKAGELINT(#[serde(with = "crate::rt::protocol::wire::ord_set")] package_lint::FastResult),
    PACKAGELINTFULL(
        #[serde(with = "crate::rt::protocol::wire::ord_set")] package_lint::FastResult,
    ),
}

impl std::fmt::Debug for CommandResult {
    /// The variant (its payload may be a TAST, which has no `Debug` here).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CommandResult::{}", command_result_name(self))
    }
}

/// The name of the command a result answers: the OCaml constructor, as
/// `Server_command_types_utils.debug_describe_t` gives it for the command.
pub fn command_result_name(r: &CommandResult) -> &'static str {
    match r {
        CommandResult::STATUS(_) => "STATUS",
        CommandResult::STATUSSINGLE(_) => "STATUS_SINGLE",
        CommandResult::LOGERRORS(_) => "LOG_ERRORS",
        CommandResult::INFERTYPE(_) => "INFER_TYPE",
        CommandResult::INFERDYNAMIC(_) => "INFER_DYNAMIC",
        CommandResult::ENFORCEMENTATPOSBATCH(_) => "ENFORCEMENT_AT_POS_BATCH",
        CommandResult::INFERTYPEBATCH(_) => "INFER_TYPE_BATCH",
        CommandResult::INFERTYPEERROR(_) => "INFER_TYPE_ERROR",
        CommandResult::ISSUBTYPE(_) => "IS_SUBTYPE",
        CommandResult::TASTHOLES(_) => "TAST_HOLES",
        CommandResult::TASTHOLESBATCH(_) => "TAST_HOLES_BATCH",
        CommandResult::IDENTIFYSYMBOL(_) => "IDENTIFY_SYMBOL",
        CommandResult::IDENTIFYFUNCTION(_) => "IDENTIFY_FUNCTION",
        CommandResult::METHODJUMP(_) => "METHOD_JUMP",
        CommandResult::METHODJUMPBATCH(_) => "METHOD_JUMP_BATCH",
        CommandResult::FINDREFS(_) => "FIND_REFS",
        CommandResult::GOTOIMPL(_) => "GO_TO_IMPL",
        CommandResult::IDEFINDREFSBYSYMBOL(_) => "IDE_FIND_REFS_BY_SYMBOL",
        CommandResult::IDEGOTOIMPLBYSYMBOL(_) => "IDE_GO_TO_IMPL_BY_SYMBOL",
        CommandResult::RENAME(_) => "RENAME",
        CommandResult::IDERENAMEBYSYMBOL(_) => "IDE_RENAME_BY_SYMBOL",
        CommandResult::DUMPSYMBOLINFO(_) => "DUMP_SYMBOL_INFO",
        CommandResult::REMOVEDEADFIXMES(_) => "REMOVE_DEAD_FIXMES",
        CommandResult::REMOVEDEADUNSAFECASTS(_) => "REMOVE_DEAD_UNSAFE_CASTS",
        CommandResult::REWRITELAMBDAPARAMETERS(_) => "REWRITE_LAMBDA_PARAMETERS",
        CommandResult::INMEMORYDEPTABLESIZE(_) => "IN_MEMORY_DEP_TABLE_SIZE",
        CommandResult::SAVENAMING(_) => "SAVE_NAMING",
        CommandResult::CHECKLIVENESS(_) => "CHECK_LIVENESS",
        CommandResult::PAUSE(_) => "PAUSE",
        CommandResult::LINT(_) => "LINT",
        CommandResult::LINTSTDIN(_) => "LINT_STDIN",
        CommandResult::LINTALL(_) => "LINT_ALL",
        CommandResult::STATS(_) => "STATS",
        CommandResult::DUMPFULLFIDELITYPARSE(_) => "DUMP_FULL_FIDELITY_PARSE",
        CommandResult::RAGE(_) => "RAGE",
        CommandResult::CSTSEARCH(_) => "CST_SEARCH",
        CommandResult::NOPRECHECKEDFILES(_) => "NO_PRECHECKED_FILES",
        CommandResult::FUNDEPSBATCH(_) => "FUN_DEPS_BATCH",
        CommandResult::LISTFILESWITHERRORS(_) => "LIST_FILES_WITH_ERRORS",
        CommandResult::FILEDEPENDENTS(_) => "FILE_DEPENDENTS",
        CommandResult::FINDISOLATABLECLUSTERS(_) => "FIND_ISOLATABLE_CLUSTERS",
        CommandResult::VERBOSE(_) => "VERBOSE",
        CommandResult::DEPSOUTBATCH(_) => "DEPS_OUT_BATCH",
        CommandResult::DEPSINBATCH(_) => "DEPS_IN_BATCH",
        CommandResult::FINDMYTESTS(_) => "FIND_MY_TESTS",
        CommandResult::PACKAGELINT(_) => "PACKAGE_LINT",
        CommandResult::PACKAGELINTFULL(_) => "PACKAGE_LINT_FULL",
    }
}

/// A result type of commands (the `'a` of an `'a t`): taken out of the
/// [`CommandResult`] of a command that has it. `None` for a result of
/// another type.
pub trait ResultOf: Sized {
    fn of_command_result(r: CommandResult) -> Option<Self>;
}

macro_rules! result_of {
    ($ty:ty, $($variant:ident),+) => {
        impl ResultOf for $ty {
            fn of_command_result(r: CommandResult) -> Option<Self> {
                match r {
                    $(CommandResult::$variant(x) => Some(x),)+
                    _ => None,
                }
            }
        }
    };
}

result_of!(server_status::T, STATUS);
result_of!(StatusSingleResult, STATUSSINGLE);
result_of!(
    (),
    LOGERRORS,
    CHECKLIVENESS,
    PAUSE,
    NOPRECHECKEDFILES,
    VERBOSE
);
result_of!(infer_at_pos_service::Result, INFERTYPE);
result_of!(yojson::T, INFERDYNAMIC);
result_of!(
    Vec<String>,
    ENFORCEMENTATPOSBATCH,
    INFERTYPEBATCH,
    FUNDEPSBATCH,
    LISTFILESWITHERRORS,
    FILEDEPENDENTS,
    FINDISOLATABLECLUSTERS,
    DEPSOUTBATCH
);
result_of!(infer_error_at_pos_service::Result, INFERTYPEERROR);
result_of!(std::result::Result<String, String>, ISSUBTYPE);
result_of!(tast_holes_service::Result, TASTHOLES, TASTHOLESBATCH);
result_of!(Vec<symbol_definition::T<Absolute>>, IDENTIFYSYMBOL);
result_of!(identify_symbol::Result, IDENTIFYFUNCTION);
result_of!(Vec<method_jumps::Result>, METHODJUMP, METHODJUMPBATCH);
result_of!(
    find_refs::ResultOrRetry,
    FINDREFS,
    GOTOIMPL,
    IDEFINDREFSBYSYMBOL,
    IDEGOTOIMPLBYSYMBOL
);
result_of!(rename::ResultOrRetry, RENAME);
result_of!(rename::IdeResultOrRetry, IDERENAMEBYSYMBOL);
result_of!(symbol_info_service::Result, DUMPSYMBOLINFO);
result_of!(PatchesOrError, REMOVEDEADFIXMES, REMOVEDEADUNSAFECASTS);
result_of!(Vec<server_rename_types::Patch>, REWRITELAMBDAPARAMETERS);
result_of!(std::result::Result<isize, String>, INMEMORYDEPTABLESIZE);
result_of!(
    std::result::Result<save_state_service_types::SaveNamingResult, String>,
    SAVENAMING
);
result_of!(server_lint_types::Result, LINT, LINTSTDIN, LINTALL);
result_of!(stats::T, STATS);
result_of!(String, DUMPFULLFIDELITYPARSE);
result_of!(server_rage_types::Result, RAGE);
result_of!(std::result::Result<yojson::T, String>, CSTSEARCH);
result_of!(Vec<find_refs::ResultOrRetry>, DEPSINBATCH);
result_of!(find_my_tests::Result, FINDMYTESTS);
result_of!(package_lint::FastResult, PACKAGELINT, PACKAGELINTFULL);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CmdMetadata {
    pub from: String,
    /// a short human-readable string, used in "hh_server is busy [desc]"
    pub desc: String,
}

/// `type 'a command = cmd_metadata * 'a t`
pub type Command = (CmdMetadata, T);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Streamed {
    SHOW(String),
    LISTMODES,
}

pub type Errors = Vec<FinalizedDiagnostic>;

/// `Diagnostics.FinalizedErrorSet.of_list` of both, then `equal`: the same
/// diagnostics up to order and repetition (`FinalizedError.compare`, which is
/// `User_diagnostic.compare`).
pub fn equal_errors(errors1: &Errors, errors2: &Errors) -> bool {
    fn of_list(errors: &Errors) -> Vec<&FinalizedDiagnostic> {
        let mut errors: Vec<&FinalizedDiagnostic> = errors.iter().collect();
        errors.sort_by(|a, b| user_diagnostic::compare(*a, *b));
        errors.dedup_by(|a, b| user_diagnostic::compare(*a, *b) == Ordering::Equal);
        errors
    }
    let errors1 = of_list(errors1);
    let errors2 = of_list(errors2);
    errors1.len() == errors2.len()
        && errors1
            .iter()
            .zip(errors2.iter())
            .all(|(a, b)| user_diagnostic::compare(a, b) == Ordering::Equal)
}

pub type DiagnosticErrors = s_map::T<Errors>;

/// `equal_diagnostic_errors` (`[@@deriving eq]`): the same keys, and
/// [`equal_errors`] for each.
pub fn equal_diagnostic_errors(a: &DiagnosticErrors, b: &DiagnosticErrors) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b.iter())
            .all(|((ka, va), (kb, vb))| ka == kb && equal_errors(va, vb))
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum MessageType<A> {
    /// Hello is the first message sent to the client by the server
    Hello,
    /// However, if the handoff failed, this will be sent instead of Hello, and the connection terminated.
    MonitorFailedToHandoff,
    /// Server sometimes sends these, after Hello and before Response, to check if client fd is still open
    Ping,
    /// Response message is the response to an RPC. The server will close fd after this.
    Response(A, connection_tracker::T),
}

/// Timeout on reading the command from the client - client probably frozen.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Read_command_timeout;

/// Invariant: The server_finale_file is created by Exit.exit and left there.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ServerSpecificFiles {
    /// just before exit, server will write here
    pub server_finale_file: String,
}

/// Some client commands require full check to be run in order to update global
/// state that they depend on
pub fn rpc_command_needs_full_check(msg: &T) -> bool {
    match msg {
        // global error list is not updated during small checks
        T::STATUS { .. } => true,
        T::LISTFILESWITHERRORS | T::REMOVEDEADFIXMES(_) | T::REMOVEDEADUNSAFECASTS => {
            true // need same information as STATUS
        }
        T::REWRITELAMBDAPARAMETERS(_) => true,
        // Finding references/implementations uses global dependency table
        T::FINDREFS(_) => true,
        T::GOTOIMPL(_) => true,
        T::IDEFINDREFSBYSYMBOL(_) => true,
        T::IDEGOTOIMPLBYSYMBOL(_) => true,
        T::METHODJUMP((_, _, find_children)) => *find_children, // uses find refs
        T::FINDMYTESTS(_) => true,
        T::SAVENAMING(_) => false,
        // Codebase-wide rename, uses find references
        T::RENAME(_) => true,
        T::IDERENAMEBYSYMBOL(..) => true,
        // Same case as Ai commands
        T::INMEMORYDEPTABLESIZE => true,
        T::NOPRECHECKEDFILES => true,
        T::STATS => false,
        T::STATUSSINGLE { .. } => false,
        T::LOGERRORS { .. } => false,
        T::INFERTYPE(..) => false,
        T::INFERDYNAMIC(..) => false,
        T::ENFORCEMENTATPOSBATCH(_) => false,
        T::INFERTYPEBATCH(_) => false,
        T::INFERTYPEERROR(..) => false,
        T::ISSUBTYPE(_) => false,
        T::TASTHOLES(..) => false,
        T::TASTHOLESBATCH(_) => false,
        T::IDENTIFYFUNCTION(..) => false,
        T::IDENTIFYSYMBOL(_) => false,
        T::METHODJUMPBATCH(_) => false,
        T::DUMPSYMBOLINFO(_) => false,
        T::LINT(_) => false,
        T::LINTSTDIN(_) => false,
        T::LINTALL(_) => false,
        T::DUMPFULLFIDELITYPARSE(_) => false,
        T::RAGE => false,
        T::CSTSEARCH(_) => false,
        T::CHECKLIVENESS => false,
        T::PAUSE => true,
        T::FUNDEPSBATCH(_) => false,
        T::DEPSOUTBATCH(_) => false,
        T::FILEDEPENDENTS(_) => true,
        T::FINDISOLATABLECLUSTERS => true,
        T::VERBOSE(_) => false,
        T::DEPSINBATCH(_) => true,
        T::PACKAGELINT(_) => true,
        T::PACKAGELINTFULL(_) => true,
    }
}

pub fn use_priority_pipe(command: &T) -> bool {
    !rpc_command_needs_full_check(command)
}

/// `handle_after_send : type a. a t -> (a * unit t) option`: for `LOG_ERRORS`,
/// the result to send at once (`()`) and the command to run after sending
/// it.
pub fn handle_after_send(cmd: &T) -> Option<(CommandResult, T)> {
    match cmd {
        T::LOGERRORS { .. } => Some((CommandResult::LOGERRORS(()), cmd.clone())),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn filter() -> filter_diagnostics::filter::T {
        filter_diagnostics::filter::make(true, vec![], vec![])
    }

    #[test]
    fn needs_full_check() {
        assert!(rpc_command_needs_full_check(&T::STATUS {
            max_errors: None,
            error_filter: filter(),
        }));
        assert!(!rpc_command_needs_full_check(&T::CHECKLIVENESS));
        assert!(rpc_command_needs_full_check(&T::METHODJUMP((
            "C".to_string(),
            method_jumps::Filter::NoFilter,
            true
        ))));
        assert!(!rpc_command_needs_full_check(&T::METHODJUMP((
            "C".to_string(),
            method_jumps::Filter::NoFilter,
            false
        ))));
        assert!(use_priority_pipe(&T::STATS));
        assert!(!use_priority_pipe(&T::LISTFILESWITHERRORS));
        assert!(handle_after_send(&T::STATS).is_none());
        let log = T::LOGERRORS {
            files: vec![],
            log_file: None,
            error_filter: filter(),
            preexisting_warnings: false,
        };
        match handle_after_send(&log) {
            Some((CommandResult::LOGERRORS(()), T::LOGERRORS { .. })) => {}
            _ => panic!("LOG_ERRORS is answered before it is handled"),
        }
    }

    #[test]
    fn done_or_retry_calls_at_most_twice() {
        let mut n = 0;
        let x = done_or_retry::call(|| {
            n += 1;
            Ok::<_, done_or_retry::Two_retries_in_a_row>(if n == 1 {
                done_or_retry::T::Retry
            } else {
                done_or_retry::T::Done(n)
            })
        });
        assert_eq!(x, Ok(2));
        assert_eq!(
            done_or_retry::call(|| Ok(done_or_retry::T::<()>::Retry)),
            Err(done_or_retry::Two_retries_in_a_row)
        );
        assert_eq!(
            done_or_retry::map_env(|x: i32| x + 1, ("env", done_or_retry::T::Done(1))),
            ("env", done_or_retry::T::Done(2))
        );
        assert_eq!(
            done_or_retry::map_env(|x: i32| x + 1, ("env", done_or_retry::T::Retry)),
            ("env", done_or_retry::T::Retry)
        );
    }

    #[test]
    fn result_of_checks_the_variant() {
        assert_eq!(
            <Vec<String>>::of_command_result(CommandResult::LISTFILESWITHERRORS(vec![
                "a".to_string()
            ])),
            Some(vec!["a".to_string()])
        );
        assert_eq!(
            <Vec<String>>::of_command_result(CommandResult::DUMPFULLFIDELITYPARSE("x".into())),
            None
        );
        assert_eq!(
            command_result_name(&CommandResult::IDEFINDREFSBYSYMBOL(done_or_retry::T::Retry)),
            "IDE_FIND_REFS_BY_SYMBOL"
        );
    }

    #[test]
    fn find_my_tests_versions() {
        use find_my_tests::*;
        assert_eq!(yojson::to_string(&yojson_of_version(Version::V2)), r#""v2""#);
        assert_eq!(
            version_of_yojson(&yojson::T::String("staging".to_string())),
            Ok(Version::Staging)
        );
        assert!(version_of_yojson(&yojson::T::Null).is_err());
        assert_eq!(default_config().test_count_checkpoint_secs, vec![20, 30, 40]);
    }

    #[test]
    fn symbol_info_json() {
        use symbol_info_service::*;
        let pos = crate::pos::to_absolute(&Pos::NONE);
        let r = Result {
            fun_calls: vec![SymbolFunCall {
                name: "f".to_string(),
                type_: TargetType::Method,
                pos: pos.clone(),
                caller: "g".to_string(),
            }],
            symbol_types: vec![
                symbol_type::T {
                    pos: pos.clone(),
                    type_: "int".to_string(),
                    ident_: 1,
                },
                symbol_type::T {
                    pos,
                    type_: "string".to_string(),
                    ident_: 2,
                },
            ],
        };
        let json = yojson::to_string(&to_json(&r));
        assert!(json.starts_with(r#"{"function_calls":[{"name":"f","type":"Method","pos":{"#));
        // `List.rev_map`: the last symbol type first.
        let i2 = json.find(r#""ident":2"#).unwrap();
        let i1 = json.find(r#""ident":1"#).unwrap();
        assert!(i2 < i1);
        assert_eq!(
            compare_target_type(TargetType::Function, TargetType::Constructor),
            Ordering::Less
        );
    }

    #[test]
    fn rename_string_to_args_rejects_bad_input() {
        match rename::string_to_args("a|b") {
            Err(e) => assert_eq!(exit_status::show(&e.0), "Exit_status.Input_error"),
            Ok(_) => panic!("expected Exit_with Input_error"),
        }
    }

    #[test]
    fn equal_errors_ignores_order_and_repetition() {
        use crate::rt::diagnostic_fixtures::chars;
        use crate::rt::diagnostic_fixtures::err;
        use crate::rt::diagnostic_fixtures::msg;
        let a = err(4110, msg(chars("a.php", 1, 1, 2), "a"), vec![]);
        let b = err(4110, msg(chars("b.php", 2, 1, 2), "b"), vec![]);
        assert!(equal_errors(
            &vec![a.clone(), b.clone(), a.clone()],
            &vec![b.clone(), a.clone()]
        ));
        assert!(!equal_errors(&vec![a.clone()], &vec![b.clone()]));
        let mut m1 = s_map::T::new();
        m1.insert("x".to_string(), vec![a.clone(), b.clone()]);
        let mut m2 = s_map::T::new();
        m2.insert("x".to_string(), vec![b, a]);
        assert!(equal_diagnostic_errors(&m1, &m2));
    }
}
