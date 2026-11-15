// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `search/utils/search_utils.ml`. See `hh/PORTING.md`.
//!
//! - `si_env` is [`SiEnv`]: a value that the OCaml copies with `{ sienv with
//!   ... }`, so its collections are persistent (`im`) and `Clone` is cheap.
//!   Its fields keep their OCaml names (they share no single prefix).
//!   `sie_fuzzy_search_mode` is a `bool ref` shared by the copies: an
//!   `Arc<AtomicBool>`.
//! - `si_fullitem` is [`SiFullitem`] (fields without the prefix `sif_`).
//!   `sif_filepath` is the same string for every item of a file, so it is
//!   shared (`Arc<str>`); nothing outside the process sees the difference.
//! - `module type Searchable` is a signature that nothing in the tree
//!   implements: not ported.
//! - `Tombstone` and `Tombstone_set`: `i64` and `im::OrdSet<i64>`
//!   (`Int64.compare` is the order of `i64`).

use std::sync::Arc;
use std::sync::atomic::AtomicBool;

use crate::file_info;
use crate::file_info::SiKind;
use crate::format;
use crate::format::Formatter;
use crate::glean;
use crate::pos;
use crate::search_types::AutocompleteType;
use crate::search_types::SiItem;

/// `mock_on_find`: `query_text:string -> context:autocomplete_type ->
/// kind_filter:si_kind option -> si_item list`.
pub type MockOnFind =
    Arc<dyn Fn(&str, AutocompleteType, Option<SiKind>) -> Vec<SiItem> + Send + Sync>;

/// Known search providers
#[derive(Clone)]
pub enum SearchProvider {
    CustomIndex,
    NoIndex,
    /// used in testing and debugging
    MockIndex {
        mock_on_find: MockOnFind,
    },
    LocalIndex,
}

/// `[@@deriving show]` (`mock_on_find` is `[@opaque]`).
pub fn pp_search_provider(fmt: &mut Formatter, x: &SearchProvider) {
    match x {
        SearchProvider::CustomIndex => format::pp_print_string(fmt, "Search_utils.CustomIndex"),
        SearchProvider::NoIndex => format::pp_print_string(fmt, "Search_utils.NoIndex"),
        SearchProvider::MockIndex { mock_on_find: _ } => {
            // "@[<2>Search_utils.MockIndex {@," "@[%s =@ " "<opaque>" "@]" "@]}"
            format::pp_open_box(fmt, 2);
            format::pp_print_string(fmt, "Search_utils.MockIndex {");
            format::pp_print_cut(fmt);
            format::pp_open_box(fmt, 0);
            format::pp_print_string(fmt, "mock_on_find =");
            format::pp_print_space(fmt);
            format::pp_print_string(fmt, "<opaque>");
            format::pp_close_box(fmt);
            format::pp_close_box(fmt);
            format::pp_print_string(fmt, "}");
        }
        SearchProvider::LocalIndex => format::pp_print_string(fmt, "Search_utils.LocalIndex"),
    }
}

pub fn show_search_provider(x: &SearchProvider) -> String {
    format::asprintf(|fmt| pp_search_provider(fmt, x))
}

impl std::fmt::Debug for SearchProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&show_search_provider(self))
    }
}

/// Convert a string to a provider
pub fn provider_of_string(provider_str: &str) -> SearchProvider {
    match provider_str {
        "NoIndex" => SearchProvider::NoIndex,
        "MockIndex" => panic!("unsupported provider {}", provider_str),
        "CustomIndex" => SearchProvider::CustomIndex,
        "LocalIndex" => SearchProvider::LocalIndex,
        _ => panic!("invalid search-provider: {}", provider_str),
    }
}

/// Convert a string to a human readable description of the provider
pub fn descriptive_name_of_provider(provider: &SearchProvider) -> &'static str {
    match provider {
        SearchProvider::CustomIndex => "Custom symbol index",
        SearchProvider::NoIndex => "Symbol index disabled",
        SearchProvider::MockIndex { .. } => "Mock index",
        SearchProvider::LocalIndex => "Local file index only",
    }
}

/// The results we'll return to the client
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term<A, B> {
    pub name: String,
    pub pos: A,
    pub result_type: B,
}

pub fn to_absolute<B: Clone>(t: &Term<oxidized::pos::Pos, B>) -> Term<pos::Absolute, B> {
    Term {
        name: t.name.clone(),
        pos: pos::to_absolute(&t.pos),
        result_type: t.result_type.clone(),
    }
}

pub fn is_si_class(kind: SiKind) -> bool {
    matches!(kind, SiKind::SIClass)
}

pub fn is_si_trait(kind: SiKind) -> bool {
    matches!(kind, SiKind::SITrait)
}

/// Individual result object as known by the autocomplete system
pub type Symbol = Term<pos::Absolute, SiKind>;

/// Used by some legacy APIs
pub type LegacySymbol = Term<file_info::Pos, SiKind>;

/// Collected results as known by the autocomplete system
pub type Result = Vec<Symbol>;

/// Determine the best "ty" string for an item
pub fn kind_to_string(kind: SiKind) -> &'static str {
    match kind {
        SiKind::SIClass => "class",
        SiKind::SIInterface => "interface",
        SiKind::SIEnum => "enum",
        SiKind::SITrait => "trait",
        SiKind::SIUnknown => "unknown",
        SiKind::SIMixed => "mixed",
        SiKind::SIFunction => "function",
        SiKind::SITypedef => "type alias",
        SiKind::SIGlobalConstant => "constant",
        SiKind::SIXHP => "XHP class",
        SiKind::SINamespace => "namespace",
        SiKind::SIClassMethod => "class method",
        SiKind::SILiteral => "literal",
        SiKind::SIClassConstant => "class constant",
        SiKind::SIProperty => "class property",
        SiKind::SILocalVariable => "local variable",
        SiKind::SIKeyword => "keyword",
        SiKind::SIConstructor => "constructor",
    }
}

/// Sigh, yet another string to enum conversion
pub fn string_to_kind(type_: &str) -> Option<SiKind> {
    match type_ {
        "class" => Some(SiKind::SIClass),
        "interface" => Some(SiKind::SIInterface),
        "enum" => Some(SiKind::SIEnum),
        "trait" => Some(SiKind::SITrait),
        "unknown" => Some(SiKind::SIUnknown),
        "mixed" => Some(SiKind::SIMixed),
        "function" => Some(SiKind::SIFunction),
        // Compatibility with strings used by Hack Search Service as well as ty_string
        "typedef" | "type alias" => Some(SiKind::SITypedef),
        "constant" => Some(SiKind::SIGlobalConstant),
        "xhp" => Some(SiKind::SIXHP),
        "namespace" => Some(SiKind::SINamespace),
        "class method" => Some(SiKind::SIClassMethod),
        "literal" => Some(SiKind::SILiteral),
        "class constant" => Some(SiKind::SIClassConstant),
        "property" | "class property" => Some(SiKind::SIProperty),
        "local variable" => Some(SiKind::SILocalVariable),
        "keyword" => Some(SiKind::SIKeyword),
        "constructor" => Some(SiKind::SIConstructor),
        _ => None,
    }
}

/// More complete representation of a symbol index item
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SiFullitem {
    /// NOTE: this is expected to have its leading backslash stripped. See [Utils.strip_ns]
    pub name: String,
    pub kind: SiKind,
    pub filepath: Arc<str>,
    pub is_abstract: bool,
    pub is_final: bool,
}

/// Fully captured information from a scan of WWW
pub type SiCapture = Vec<SiFullitem>;

/// Which system notified us of a file changed?
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileSource {
    Init,
    TypeChecker,
}

/// Keep track of file hash tombstones
pub mod tombstone {
    pub type T = i64;

    pub fn compare(a: &T, b: &T) -> std::cmp::Ordering {
        a.cmp(b)
    }

    pub fn to_string(t: &T) -> String {
        t.to_string()
    }
}

pub mod tombstone_set {
    pub type T = im::OrdSet<super::tombstone::T>;
}

/// Context information for the current symbol index
#[derive(Clone)]
pub struct SiEnv {
    pub sie_provider: SearchProvider,
    pub sie_quiet_mode: bool,
    pub sie_fuzzy_search_mode: Arc<AtomicBool>,
    pub sie_log_timings: bool,
    // Setting the "resolve" parameters to true slows down autocomplete
    // but increases precision for answers.
    //
    // sie_resolve_signatures: When a result appears in autocomplete,
    // look up the full declaration and include parameters.  Uses extra
    // memory.
    //
    // sie_resolve_positions: When a result appears in autocomplete,
    // look up the exact position of the symbol from the naming table.
    // Slows down autocomplete.
    //
    // sie_resolve_local_decl: When a file changes on disk, the local
    // search index digs through its decls and saves exact class
    // information.  Uses more memory and slows down processing of
    // changed files.
    pub sie_resolve_signatures: bool,
    pub sie_resolve_positions: bool,
    pub sie_resolve_local_decl: bool,
    pub sie_namespace_map: Vec<(String, String)>,
    // MockIndex
    pub mock_on_find: MockOnFind,
    // LocalSearchService
    /// (Each file's items are shared: copying a node of the persistent map
    /// then copies no item.)
    pub lss_fullitems: crate::relative_path::map::T<Arc<SiCapture>>,
    /// files that have been locally modified
    pub lss_tombstones: crate::relative_path::set::T,
    /// hashes of suffixes of files that have been locally modified -
    /// this only exists for compatibility with stores (sql, www.autocomplete)
    /// that use filehashes, and won't be needed once we move solely
    /// to stures that use paths (local, www.hack.light).
    pub lss_tombstone_hashes: tombstone_set::T,
    // CustomSearchService
    pub glean_reponame: String,
    pub glean_handle: Option<glean::Handle>,
}

impl std::fmt::Debug for SiEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SiEnv")
            .field("sie_provider", &self.sie_provider)
            .field("sie_quiet_mode", &self.sie_quiet_mode)
            .field("lss_fullitems", &self.lss_fullitems.len())
            .field("lss_tombstones", &self.lss_tombstones.len())
            .finish_non_exhaustive()
    }
}

/// Default provider with no functionality
pub fn default_si_env() -> SiEnv {
    SiEnv {
        sie_provider: SearchProvider::NoIndex,
        sie_quiet_mode: false,
        sie_fuzzy_search_mode: Arc::new(AtomicBool::new(false)),
        sie_log_timings: false,
        sie_resolve_signatures: false,
        sie_resolve_positions: false,
        sie_resolve_local_decl: false,
        sie_namespace_map: vec![],
        // MockIndex
        mock_on_find: Arc::new(|_query_text, _context, _kind_filter| vec![]),
        // LocalSearchService
        lss_fullitems: Default::default(),
        lss_tombstones: Default::default(),
        lss_tombstone_hashes: Default::default(),
        // CustomSearchService
        glean_reponame: String::new(),
        glean_handle: None,
    }
}

/// Default provider, but no logging
pub fn quiet_si_env() -> SiEnv {
    SiEnv {
        sie_quiet_mode: true,
        sie_log_timings: false,
        ..default_si_env()
    }
}
