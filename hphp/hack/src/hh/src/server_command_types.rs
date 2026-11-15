// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server_command_types.ml`. See `hh/PORTING.md`.
//!
//! # The GADT
//!
//! `type _ t` (an RPC command, indexed by the type of its result) is two
//! enums with the same variant names (the UpperCamelCase of the OCaml
//! constructors: `STATUS_SINGLE` is `StatusSingle`;
//! [`crate::server_command_types_utils::debug_describe_t`] and
//! [`command_result_name`] give the OCaml names):
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
//! `serde` (`bincode`: by variant index, not by name). The types of other modules that have no `serde` of their own get
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
//! `crate::diagnostics::FinalizedDiagnostic`.

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
use crate::server_isolation_types;
use crate::server_lint_types;
use crate::server_notifier_types;
use crate::diagnostics::FinalizedDiagnostic;
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
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct TwoRetriesInARow;

    /// Prints the OCaml constructor's name, `Two_retries_in_a_row` (the text of the
    /// exception: `exception::wrap` takes it from `Debug`).
    impl std::fmt::Debug for TwoRetriesInARow {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("Two_retries_in_a_row")
        }
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub enum T<A> {
        Done(A),
        Retry,
    }

    /// Note: this is designed to work with calls that always will succeed on second try
    /// (the reason for retrying is a one time event that is resolved during first call).
    /// If this ends up throwing, it's a bug in hh_server.
    fn call_depth<A, E: From<TwoRetriesInARow>>(
        f: &mut dyn FnMut() -> Result<T<A>, E>,
        depth: isize,
    ) -> Result<A, E> {
        if depth == 2 {
            return Err(TwoRetriesInARow.into());
        }
        let result = f()?;
        match result {
            T::Done(x) => Ok(x),
            T::Retry => call_depth(f, depth + 1),
        }
    }

    /// Call the function returning Done_or_retry.t with at most one retry, expecting
    /// that this is enough to yield a non-Retry value, which is returned
    pub fn call<A, E: From<TwoRetriesInARow>>(
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

/// `Server_command_types.Isolation_validation`
pub mod isolation_validation {
    use super::*;

    /// A package boundary the candidate would violate, of which there are two
    /// kinds. A file outside it references in — the case the candidate exists to
    /// rule out. Or the candidate reaches into its own excluded path: strict
    /// isolation switches off the exemption that normally lets a package use its
    /// own [__tests__], so [referrer] is then inside the candidate too.
    ///
    /// The second is the common one in practice, and the reason this is not
    /// described as an inbound reference.
    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct Violation {
        pub referrer: String,
        pub line: isize,
        pub message: String,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct Result {
        /// Why the command declined to run at all, if it did. The server it was
        /// asked of is not one this can run on — decl repackaging switched off,
        /// or a backend that keeps its own copy of the package configuration.
        /// Reported rather than raised: the caller learns what to change, and
        /// the server it asked stays up. Everything below is empty when this is
        /// set.
        pub refused: Option<String>,
        /// No package boundary was violated among the files checked, and the
        /// candidate was one this command could construct in full.
        pub isolatable: bool,
        /// How many files were typechecked against the synthesized package.
        /// The verdict is only as good as this number.
        pub files_checked: isize,
        pub violations: Vec<Violation>,
        /// Candidate paths the naming table does not know, so nothing was
        /// checked on their behalf.
        pub unknown_files: Vec<String>,
        /// Candidate paths that name a package of their own with
        /// [<<file: __PackageOverride(...)>>]. An override beats include-path
        /// matching, so the synthesized package never claims the file and the
        /// candidate asked about is not the one that could be checked.
        pub overridden_files: Vec<String>,
    }
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

    /// A concrete selection-graph edge. Symbol identities and expansion
    /// strategies are separate; test targets have no expansion strategy.
    /// [edge_key] uses the same normalization as reason provenance.
    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct PathEdge {
        pub source_symbol: String,
        pub source_strategy: String,
        pub target_symbol: String,
        pub target_strategy: Option<String>,
        pub reason: String,
        pub edge_key: String,
    }

    /// Ordered edges from a root symbol to a selected test node.
    pub type SelectionPath = Vec<PathEdge>;

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct SelectedCldpMember {
        pub member_name: String,
        /// Wall-clock seconds from the start of selection to when this CLDP test
        /// member was first selected.
        pub selected_after_secs: f64,
        /// Indices into [result_data.reason_provenance] for this CLDP test member.
        /// [None] when reason provenance is not requested.
        pub reason_provenance_indices: Option<Vec<isize>>,
        /// Indices into [result_data.path_provenance] for this CLDP test member.
        pub path_provenance_indices: Option<Vec<isize>>,
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
        pub path_provenance_indices: Option<Vec<isize>>,
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
        pub path_provenance_indices: Option<Vec<isize>>,
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
        /// Interned pool of concrete paths whose reason multisets are minimal.
        /// Distinct paths with equal multisets are retained.
        pub path_provenance: Option<Vec<SelectionPath>>,
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
        /// Return every concrete path attaining a minimal reason multiset.
        pub path_provenance: bool,
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
            path_provenance: false,
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
    ///
    /// (Deviation, internal: the third field is the base64 of the JSON of
    /// the definition (serde), not of its OCaml `Marshal`: the string goes
    /// from the Rust LSP to the Rust `hh_client` only.)
    pub fn arguments_to_string_exn(
        new_name: &str,
        action: &find_refs::Action,
        symbol_def: &symbol_definition::T<Pos>,
    ) -> std::result::Result<String, ExitWith> {
        let symbol_and_action =
            find_refs_wire_format::cli_args::to_string(&find_refs_wire_format::cli_args::T {
                symbol_name: new_name.to_string(),
                action: action.clone(),
                stream_file: None,
                hint_suffixes: vec![],
            })?;
        let marshalled_def = serde_json::to_vec(symbol_def).expect("Marshal.to_string");
        let encoded = base64_encode(&marshalled_def);
        Ok(format!("{}|{}", symbol_and_action, encoded))
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
        let (symbol_name, action_arg, marshalled_def) = match split_arg.as_slice() {
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
            symbol_name: new_name,
            action,
            ..
        } = find_refs_wire_format::cli_args::from_string_exn(&str)?;
        // `Base64.decode_exn` (raises `Invalid_argument`) and
        // `Marshal.from_string` (see `arguments_to_string_exn`).
        let decoded_str = match base64_decode(&marshalled_def) {
            Some(d) => d,
            None => panic!("Invalid_argument(\"Base64.decode_exn\")"),
        };
        let symbol_definition: symbol_definition::T<Pos> =
            serde_json::from_slice(&decoded_str).expect("Marshal.from_string");
        Ok((new_name, action, symbol_definition))
    }

    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

    /// `Base64.encode_exn` (the standard alphabet, padded)
    pub fn base64_encode(input: &[u8]) -> String {
        let mut out = String::with_capacity(input.len().div_ceil(3) * 4);
        for chunk in input.chunks(3) {
            let b = [chunk[0], *chunk.get(1).unwrap_or(&0), *chunk.get(2).unwrap_or(&0)];
            let n = ((b[0] as u32) << 16) | ((b[1] as u32) << 8) | b[2] as u32;
            for i in 0..4 {
                if i <= chunk.len() {
                    out.push(ALPHABET[((n >> (18 - 6 * i)) & 63) as usize] as char)
                } else {
                    out.push('=')
                }
            }
        }
        out
    }

    /// `Base64.decode` (padded, the standard alphabet)
    pub fn base64_decode(input: &str) -> Option<Vec<u8>> {
        let bytes = input.as_bytes();
        if bytes.len() % 4 != 0 {
            return None;
        }
        let mut out = vec![];
        for chunk in bytes.chunks(4) {
            let mut n: u32 = 0;
            let mut pad = 0;
            for &c in chunk {
                let v = if c == b'=' {
                    pad += 1;
                    0
                } else {
                    if pad > 0 {
                        return None;
                    }
                    ALPHABET.iter().position(|&a| a == c)? as u32
                };
                n = (n << 6) | v;
            }
            let b = [(n >> 16) as u8, (n >> 8) as u8, n as u8];
            out.extend_from_slice(&b[..3 - pad.min(2)]);
        }
        Some(out)
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
pub type StatusSingleResult = ((Vec<FinalizedDiagnostic>, isize), Option<ShownTasts>);

/// The `tasts` of `STATUS_SINGLE` as `hh_client --show-tast` prints them
/// (`crate::typing_show::show_tasts`): the TASTs do not cross the socket
/// (`crate::rt::protocol`), what the client prints of them does.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShownTasts {
    /// The JSON of the TAST hashes, pretty-printed.
    pub hashes: String,
    /// `Relative_path.Map.show (Tast_with_dynamic.pp Tast.pp_program) tasts`
    pub tasts: String,
}

/// The following datatypes can be interpreted as follows:
/// MESSAGE_TAG : Argument type (sent from client to server) -> return type t
///
/// (`type _ t`: the command; its result is the variant of the same name of
/// [`CommandResult`].)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum T {
    /// -> `Server_status.t`
    Status {
        max_errors: Option<isize>,
        error_filter: filter_diagnostics::filter::T,
    },
    /// -> [`StatusSingleResult`]
    StatusSingle {
        file_names: Vec<FileInput>,
        max_errors: Option<isize>,
        error_filter: filter_diagnostics::filter::T,
        return_expanded_tast: bool,
        /// Whether to show preexisting warnings
        /// (the ones that were there prior to saved state revision)
        preexisting_warnings: bool,
    },
    /// -> `unit`
    LogErrors {
        files: Vec<String>,
        log_file: Option<String>,
        error_filter: filter_diagnostics::filter::T,
        preexisting_warnings: bool,
    },
    /// -> `Infer_at_pos_service.result`
    InferType(FileInput, file_content::position::T),
    /// -> `Yojson.Safe.t`
    InferDynamic(String, bool),
    /// -> `string list`
    EnforcementAtPosBatch(Vec<(String, file_content::position::T)>),
    /// -> `string list`
    InferTypeBatch(
        Vec<(
            String,
            file_content::position::T,
            Option<file_content::position::T>,
        )>,
    ),
    /// -> `Infer_error_at_pos_service.result`
    InferTypeError(FileInput, isize, isize),
    /// -> `(string, string) result`
    IsSubtype(String),
    /// -> `Tast_holes_service.result`
    TastHoles(FileInput, tast_hole::Filter),
    /// -> `Tast_holes_service.result`
    TastHolesBatch(Vec<String>),
    /// -> `string Symbol_definition.t list`
    IdentifySymbol(String),
    /// -> `Identify_symbol.result`
    IdentifyFunction(String, FileInput, file_content::position::T),
    /// -> `Method_jumps.result list`
    MethodJump((String, method_jumps::Filter, bool)),
    /// -> `Method_jumps.result list`
    MethodJumpBatch((Vec<String>, method_jumps::Filter)),
    /// -> `Find_refs.result_or_retry`
    FindRefs(find_refs::Action),
    /// -> `Find_refs.result_or_retry`
    GoToImpl(find_refs::Action),
    /// -> `Find_refs.result_or_retry`
    IdeFindRefsBySymbol(find_refs_wire_format::cli_args::T),
    /// -> `Find_refs.result_or_retry`
    IdeGoToImplBySymbol(find_refs_wire_format::cli_args::T),
    /// -> `Rename.result_or_retry`
    Rename(server_rename_types::Action),
    /// -> `Rename.ide_result_or_retry`
    IdeRenameBySymbol(find_refs::Action, String, symbol_definition::T<Pos>),
    /// -> `Symbol_info_service.result`
    DumpSymbolInfo(Vec<String>),
    /// -> [`PatchesOrError`]
    RemoveDeadFixmes(Vec<isize>),
    /// -> [`PatchesOrError`]
    RemoveDeadUnsafeCasts,
    /// -> `Server_rename_types.patch list`
    RewriteLambdaParameters(Vec<String>),
    /// -> `(int, string) result`
    InMemoryDepTableSize,
    /// -> `(Save_state_service_types.save_naming_result, string) result`
    SaveNaming(String),
    /// -> `unit`
    CheckLiveness,
    /// -> `unit`
    ///
    /// Pause automatic rechecks until the next client connection. This uses
    /// the default pipe so that ongoing typechecking finishes first.
    Pause,
    /// -> `Server_lint_types.result`
    Lint(Vec<String>),
    /// -> `Server_lint_types.result`
    LintStdin(LintStdinInput),
    /// -> `Server_lint_types.result`
    LintAll(isize),
    /// -> `Stats.t`
    Stats,
    /// -> `string`
    DumpFullFidelityParse(String),
    /// -> `Server_rage_types.result`
    Rage,
    /// -> `(Yojson.Safe.t, string) result`
    CstSearch(CstSearchInput),
    /// -> `unit`
    NoPrecheckedFiles,
    /// -> `string list`
    FunDepsBatch(Vec<(String, isize, isize)>),
    /// -> `string list`
    ListFilesWithErrors,
    /// -> `string list`
    FileDependents(Vec<String>),
    /// -> `Server_isolation_types.result`
    FindIsolatableClusters(server_isolation_types::Options),
    /// -> `Isolation_validation.result`
    ValidateIsolation(Vec<String>),
    /// -> `unit`
    Verbose(bool),
    /// -> `string list`
    DepsOutBatch(Vec<(String, isize, isize)>),
    /// -> `Find_refs.result_or_retry list`
    DepsInBatch(Vec<(String, isize, isize)>),
    /// -> `Find_my_tests.result`
    FindMyTests(
        (
            find_my_tests::Version,
            find_my_tests::Config,
            Vec<find_my_tests::Action>,
        ),
    ),
    /// -> `Package_lint.fast_result`
    PackageLint(String),
    /// -> `Package_lint.fast_result`
    PackageLintFull((String, Vec<String>)),
}

/// The `'a` of `'a t`: the result of each command, in the variant of the
/// command's name (not in OCaml, where the type checker knows it). The server
/// answers a [`T`] with the variant of the same name.
#[derive(Serialize, Deserialize)]
pub enum CommandResult {
    Status(server_status::T),
    StatusSingle(
        StatusSingleResult,
    ),
    LogErrors(()),
    InferType(infer_at_pos_service::Result),
    InferDynamic(yojson::T),
    EnforcementAtPosBatch(Vec<String>),
    InferTypeBatch(Vec<String>),
    InferTypeError(infer_error_at_pos_service::Result),
    IsSubtype(std::result::Result<String, String>),
    TastHoles(tast_holes_service::Result),
    TastHolesBatch(tast_holes_service::Result),
    IdentifySymbol(Vec<symbol_definition::T<Absolute>>),
    IdentifyFunction(identify_symbol::Result),
    MethodJump(Vec<method_jumps::Result>),
    MethodJumpBatch(Vec<method_jumps::Result>),
    FindRefs(find_refs::ResultOrRetry),
    GoToImpl(find_refs::ResultOrRetry),
    IdeFindRefsBySymbol(find_refs::ResultOrRetry),
    IdeGoToImplBySymbol(find_refs::ResultOrRetry),
    Rename(rename::ResultOrRetry),
    IdeRenameBySymbol(rename::IdeResultOrRetry),
    DumpSymbolInfo(symbol_info_service::Result),
    RemoveDeadFixmes(PatchesOrError),
    RemoveDeadUnsafeCasts(PatchesOrError),
    RewriteLambdaParameters(Vec<server_rename_types::Patch>),
    InMemoryDepTableSize(std::result::Result<isize, String>),
    SaveNaming(std::result::Result<save_state_service_types::SaveNamingResult, String>),
    CheckLiveness(()),
    Pause(()),
    Lint(server_lint_types::Result),
    LintStdin(server_lint_types::Result),
    LintAll(server_lint_types::Result),
    Stats(stats::T),
    DumpFullFidelityParse(String),
    Rage(server_rage_types::Result),
    CstSearch(std::result::Result<yojson::T, String>),
    NoPrecheckedFiles(()),
    FunDepsBatch(Vec<String>),
    ListFilesWithErrors(Vec<String>),
    FileDependents(Vec<String>),
    FindIsolatableClusters(server_isolation_types::Result),
    ValidateIsolation(isolation_validation::Result),
    Verbose(()),
    DepsOutBatch(Vec<String>),
    DepsInBatch(Vec<find_refs::ResultOrRetry>),
    FindMyTests(find_my_tests::Result),
    PackageLint(#[serde(with = "crate::rt::protocol::wire::ord_set")] package_lint::FastResult),
    PackageLintFull(
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
        CommandResult::Status(_) => "STATUS",
        CommandResult::StatusSingle(_) => "STATUS_SINGLE",
        CommandResult::LogErrors(_) => "LOG_ERRORS",
        CommandResult::InferType(_) => "INFER_TYPE",
        CommandResult::InferDynamic(_) => "INFER_DYNAMIC",
        CommandResult::EnforcementAtPosBatch(_) => "ENFORCEMENT_AT_POS_BATCH",
        CommandResult::InferTypeBatch(_) => "INFER_TYPE_BATCH",
        CommandResult::InferTypeError(_) => "INFER_TYPE_ERROR",
        CommandResult::IsSubtype(_) => "IS_SUBTYPE",
        CommandResult::TastHoles(_) => "TAST_HOLES",
        CommandResult::TastHolesBatch(_) => "TAST_HOLES_BATCH",
        CommandResult::IdentifySymbol(_) => "IDENTIFY_SYMBOL",
        CommandResult::IdentifyFunction(_) => "IDENTIFY_FUNCTION",
        CommandResult::MethodJump(_) => "METHOD_JUMP",
        CommandResult::MethodJumpBatch(_) => "METHOD_JUMP_BATCH",
        CommandResult::FindRefs(_) => "FIND_REFS",
        CommandResult::GoToImpl(_) => "GO_TO_IMPL",
        CommandResult::IdeFindRefsBySymbol(_) => "IDE_FIND_REFS_BY_SYMBOL",
        CommandResult::IdeGoToImplBySymbol(_) => "IDE_GO_TO_IMPL_BY_SYMBOL",
        CommandResult::Rename(_) => "RENAME",
        CommandResult::IdeRenameBySymbol(_) => "IDE_RENAME_BY_SYMBOL",
        CommandResult::DumpSymbolInfo(_) => "DUMP_SYMBOL_INFO",
        CommandResult::RemoveDeadFixmes(_) => "REMOVE_DEAD_FIXMES",
        CommandResult::RemoveDeadUnsafeCasts(_) => "REMOVE_DEAD_UNSAFE_CASTS",
        CommandResult::RewriteLambdaParameters(_) => "REWRITE_LAMBDA_PARAMETERS",
        CommandResult::InMemoryDepTableSize(_) => "IN_MEMORY_DEP_TABLE_SIZE",
        CommandResult::SaveNaming(_) => "SAVE_NAMING",
        CommandResult::CheckLiveness(_) => "CHECK_LIVENESS",
        CommandResult::Pause(_) => "PAUSE",
        CommandResult::Lint(_) => "LINT",
        CommandResult::LintStdin(_) => "LINT_STDIN",
        CommandResult::LintAll(_) => "LINT_ALL",
        CommandResult::Stats(_) => "STATS",
        CommandResult::DumpFullFidelityParse(_) => "DUMP_FULL_FIDELITY_PARSE",
        CommandResult::Rage(_) => "RAGE",
        CommandResult::CstSearch(_) => "CST_SEARCH",
        CommandResult::NoPrecheckedFiles(_) => "NO_PRECHECKED_FILES",
        CommandResult::FunDepsBatch(_) => "FUN_DEPS_BATCH",
        CommandResult::ListFilesWithErrors(_) => "LIST_FILES_WITH_ERRORS",
        CommandResult::FileDependents(_) => "FILE_DEPENDENTS",
        CommandResult::FindIsolatableClusters(_) => "FIND_ISOLATABLE_CLUSTERS",
        CommandResult::ValidateIsolation(_) => "VALIDATE_ISOLATION",
        CommandResult::Verbose(_) => "VERBOSE",
        CommandResult::DepsOutBatch(_) => "DEPS_OUT_BATCH",
        CommandResult::DepsInBatch(_) => "DEPS_IN_BATCH",
        CommandResult::FindMyTests(_) => "FIND_MY_TESTS",
        CommandResult::PackageLint(_) => "PACKAGE_LINT",
        CommandResult::PackageLintFull(_) => "PACKAGE_LINT_FULL",
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

result_of!(server_status::T, Status);
result_of!(StatusSingleResult, StatusSingle);
result_of!(
    (),
    LogErrors,
    CheckLiveness,
    Pause,
    NoPrecheckedFiles,
    Verbose
);
result_of!(infer_at_pos_service::Result, InferType);
result_of!(yojson::T, InferDynamic);
result_of!(
    Vec<String>,
    EnforcementAtPosBatch,
    InferTypeBatch,
    FunDepsBatch,
    ListFilesWithErrors,
    FileDependents,
    DepsOutBatch
);
result_of!(server_isolation_types::Result, FindIsolatableClusters);
result_of!(isolation_validation::Result, ValidateIsolation);
result_of!(infer_error_at_pos_service::Result, InferTypeError);
result_of!(std::result::Result<String, String>, IsSubtype);
result_of!(tast_holes_service::Result, TastHoles, TastHolesBatch);
result_of!(Vec<symbol_definition::T<Absolute>>, IdentifySymbol);
result_of!(identify_symbol::Result, IdentifyFunction);
result_of!(Vec<method_jumps::Result>, MethodJump, MethodJumpBatch);
result_of!(
    find_refs::ResultOrRetry,
    FindRefs,
    GoToImpl,
    IdeFindRefsBySymbol,
    IdeGoToImplBySymbol
);
result_of!(rename::ResultOrRetry, Rename);
result_of!(rename::IdeResultOrRetry, IdeRenameBySymbol);
result_of!(symbol_info_service::Result, DumpSymbolInfo);
result_of!(PatchesOrError, RemoveDeadFixmes, RemoveDeadUnsafeCasts);
result_of!(Vec<server_rename_types::Patch>, RewriteLambdaParameters);
result_of!(std::result::Result<isize, String>, InMemoryDepTableSize);
result_of!(
    std::result::Result<save_state_service_types::SaveNamingResult, String>,
    SaveNaming
);
result_of!(server_lint_types::Result, Lint, LintStdin, LintAll);
result_of!(stats::T, Stats);
result_of!(String, DumpFullFidelityParse);
result_of!(server_rage_types::Result, Rage);
result_of!(std::result::Result<yojson::T, String>, CstSearch);
result_of!(Vec<find_refs::ResultOrRetry>, DepsInBatch);
result_of!(find_my_tests::Result, FindMyTests);
result_of!(package_lint::FastResult, PackageLint, PackageLintFull);

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
    Show(String),
    ListModes,
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
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ReadCommandTimeout;

/// Prints the OCaml constructor's name, `Read_command_timeout` (the text of the
/// exception: `exception::wrap` takes it from `Debug`).
impl std::fmt::Debug for ReadCommandTimeout {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Read_command_timeout")
    }
}

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
        T::Status { .. } => true,
        T::ListFilesWithErrors | T::RemoveDeadFixmes(_) | T::RemoveDeadUnsafeCasts => {
            true // need same information as STATUS
        }
        T::RewriteLambdaParameters(_) => true,
        // Finding references/implementations uses global dependency table
        T::FindRefs(_) => true,
        T::GoToImpl(_) => true,
        T::IdeFindRefsBySymbol(_) => true,
        T::IdeGoToImplBySymbol(_) => true,
        T::MethodJump((_, _, find_children)) => *find_children, // uses find refs
        T::FindMyTests(_) => true,
        T::SaveNaming(_) => false,
        // Codebase-wide rename, uses find references
        T::Rename(_) => true,
        T::IdeRenameBySymbol(..) => true,
        // Same case as Ai commands
        T::InMemoryDepTableSize => true,
        T::NoPrecheckedFiles => true,
        T::Stats => false,
        T::StatusSingle { .. } => false,
        T::LogErrors { .. } => false,
        T::InferType(..) => false,
        T::InferDynamic(..) => false,
        T::EnforcementAtPosBatch(_) => false,
        T::InferTypeBatch(_) => false,
        T::InferTypeError(..) => false,
        T::IsSubtype(_) => false,
        T::TastHoles(..) => false,
        T::TastHolesBatch(_) => false,
        T::IdentifyFunction(..) => false,
        T::IdentifySymbol(_) => false,
        T::MethodJumpBatch(_) => false,
        T::DumpSymbolInfo(_) => false,
        T::Lint(_) => false,
        T::LintStdin(_) => false,
        T::LintAll(_) => false,
        T::DumpFullFidelityParse(_) => false,
        T::Rage => false,
        T::CstSearch(_) => false,
        T::CheckLiveness => false,
        T::Pause => true,
        T::FunDepsBatch(_) => false,
        T::DepsOutBatch(_) => false,
        T::FileDependents(_) => true,
        T::FindIsolatableClusters(_) => true,
        // Reads the dependency graph to decide which files could reference the
        // candidate, and the graph is only guaranteed current after a full check.
        T::ValidateIsolation(_) => true,
        T::Verbose(_) => false,
        T::DepsInBatch(_) => true,
        T::PackageLint(_) => true,
        T::PackageLintFull(_) => true,
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
        T::LogErrors { .. } => Some((CommandResult::LogErrors(()), cmd.clone())),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The exceptions' texts (`exception::wrap` takes them from `Debug`) are
    /// the OCaml constructors' names.
    #[test]
    fn exceptions_print_their_ocaml_names() {
        assert_eq!(format!("{:?}", done_or_retry::TwoRetriesInARow), "Two_retries_in_a_row");
        assert_eq!(format!("{:?}", ReadCommandTimeout), "Read_command_timeout");
        assert_eq!(
            crate::exception::get_ctor_string(&crate::exception::wrap(done_or_retry::TwoRetriesInARow)),
            "Two_retries_in_a_row"
        );
    }

    fn filter() -> filter_diagnostics::filter::T {
        filter_diagnostics::filter::make(true, vec![], vec![])
    }

    #[test]
    fn needs_full_check() {
        assert!(rpc_command_needs_full_check(&T::Status {
            max_errors: None,
            error_filter: filter(),
        }));
        assert!(!rpc_command_needs_full_check(&T::CheckLiveness));
        assert!(rpc_command_needs_full_check(&T::MethodJump((
            "C".to_string(),
            method_jumps::Filter::NoFilter,
            true
        ))));
        assert!(!rpc_command_needs_full_check(&T::MethodJump((
            "C".to_string(),
            method_jumps::Filter::NoFilter,
            false
        ))));
        assert!(use_priority_pipe(&T::Stats));
        assert!(!use_priority_pipe(&T::ListFilesWithErrors));
        assert!(handle_after_send(&T::Stats).is_none());
        let log = T::LogErrors {
            files: vec![],
            log_file: None,
            error_filter: filter(),
            preexisting_warnings: false,
        };
        match handle_after_send(&log) {
            Some((CommandResult::LogErrors(()), T::LogErrors { .. })) => {}
            _ => panic!("LOG_ERRORS is answered before it is handled"),
        }
    }

    #[test]
    fn done_or_retry_calls_at_most_twice() {
        let mut n = 0;
        let x = done_or_retry::call(|| {
            n += 1;
            Ok::<_, done_or_retry::TwoRetriesInARow>(if n == 1 {
                done_or_retry::T::Retry
            } else {
                done_or_retry::T::Done(n)
            })
        });
        assert_eq!(x, Ok(2));
        assert_eq!(
            done_or_retry::call(|| Ok(done_or_retry::T::<()>::Retry)),
            Err(done_or_retry::TwoRetriesInARow)
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
            <Vec<String>>::of_command_result(CommandResult::ListFilesWithErrors(vec![
                "a".to_string()
            ])),
            Some(vec!["a".to_string()])
        );
        assert_eq!(
            <Vec<String>>::of_command_result(CommandResult::DumpFullFidelityParse("x".into())),
            None
        );
        assert_eq!(
            command_result_name(&CommandResult::IdeFindRefsBySymbol(done_or_retry::T::Retry)),
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

    /// `Rename.arguments_to_string_exn` and `string_to_args` are inverse
    /// (base64 as RFC 4648).
    #[test]
    fn rename_arguments_round_trip() {
        assert_eq!(rename::base64_encode(b""), "");
        assert_eq!(rename::base64_encode(b"f"), "Zg==");
        assert_eq!(rename::base64_encode(b"fo"), "Zm8=");
        assert_eq!(rename::base64_encode(b"foobar"), "Zm9vYmFy");
        for s in [&b""[..], b"f", b"fo", b"foo", b"foob", b"fooba", b"foobar", &[0u8, 255, 128, 7][..]] {
            assert_eq!(rename::base64_decode(&rename::base64_encode(s)).unwrap(), s);
        }
        assert!(rename::base64_decode("Zg=").is_none());
        let def = symbol_definition::T {
            kind: symbol_definition::Kind::Function,
            name: "\\f".to_string(),
            pos: Pos::NONE,
            span: Pos::NONE,
            modifiers: vec![],
            params: Some(vec![]),
            docblock: Some("a|b".to_string()),
            detail: None,
        };
        let action = find_refs::Action::Function("\\f".to_string());
        let s = rename::arguments_to_string_exn("g", &action, &def).unwrap();
        let (new_name, action2, def2) = rename::string_to_args(&s).unwrap();
        assert_eq!(new_name, "g");
        assert_eq!(action2, action);
        assert_eq!(def2, def);
    }
}
