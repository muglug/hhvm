// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/lsp/lsp.ml`. See `hh/PORTING.md`.
//!
//! This file is an OCaml representation of the Language Server Protocol
//! https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md
//! based on the current v3.
//!
//! Changes to make it more natural in OCaml:
//! - We don't represent the common base types of Requests/Errors/Notifications
//!   because base types don't naturally mix with abstract data types, and
//!   because code for these things is done more naturally at the JSON layer
//! - We avoid option types where we can. The idea is to follow the internet
//!   "robustness" rule of being liberal in what we accept, conservative in
//!   what we emit: if we're parsing a message and it lacks a field, and if
//!   the spec tells us how to interpret absence, then we do that interpretation
//!   at the JSON->LSP parsing level (so long as the interpretation is lossless).
//!   On the emitting side, we might as well emit all fields.
//! - Most datatypes go in modules since there are so many name-clashes in
//!   the protocol and OCaml doesn't like name-clashes. Only exceptions are
//!   the really primitive types like location and DocumentUri.t.
//!   The few places where we still had to rename fields to avoid OCaml name
//!   clashes I've noted in the comments with the word "wire" to indicate the
//!   over-the-wire form of the name.
//! - Names have been translated from jsonConvention into ocaml convention
//!   only where necessary, e.g. because ocaml uses lowercase for types.
//! - The spec has space for extra fields like "experimental". It obviously
//!   doesn't make sense to encode them in a type system. I've omitted them
//!   entirely.
//!
//! # In Rust
//!
//! - Record fields keep their OCaml names (`textDocument`, `newText`...),
//!   except that the prefix that all the fields of a record share is dropped
//!   (`want_openClose` is `openClose`, `can_willSave` is `willSave`,
//!   `parinfo_label` is `label`), as `oxidized` does.
//!   Single-field records keep their field's name (`codeAction_valueSet`).
//! - `[@@deriving eq]` and `[@@deriving ord]` are `PartialEq`/`Eq` and
//!   `PartialOrd`/`Ord`; `[@@deriving enum]` gives `<type>_to_enum` and
//!   `<type>_of_enum` (`to_enum`/`of_enum` for a type `t`).
//! - `exception LspException of t` is [`error::LspException`], the `Err` of
//!   the functions that raise it (or a variant of their module's error, as
//!   `lsp_fmt::LspFmtError`): it is caught far from where it is raised (the
//!   main loop of `Client_lsp`), and the functions in between pass it on with
//!   `?`.
//! - The callbacks of [`LspHandler`] take the state as `&mut A` instead of
//!   returning it.

use crate::rt::yojson_conv;
use crate::yojson::safe as yojson;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LspId {
    NumberId(isize),
    StringId(String),
}

pub use LspId::NumberId;
pub use LspId::StringId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialResultToken(pub String);

/// Note: this datatype provides no invariants that the string is well-formed.
pub mod document_uri {
    use crate::rt::yojson_conv;
    use crate::yojson::safe as yojson;

    /// (The derived `ord` compares the strings, like `String.compare`.)
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum T {
        Uri(String),
    }

    pub use T::Uri;

    /// `[@@deriving eq]`
    pub fn equal(a: &T, b: &T) -> bool {
        a == b
    }

    /// `[@@deriving ord]`
    pub fn compare(a: &T, b: &T) -> isize {
        a.cmp(b) as isize
    }

    pub fn t_of_yojson(t: &yojson::T) -> Result<T, yojson_conv::OfYojsonError> {
        match t {
            yojson::T::String(s) => Ok(Uri(s.clone())),
            _ => yojson_conv::of_yojson_error("Expected string", t),
        }
    }

    /// `module Map = Wrapped_map.Make (M)`
    pub mod map {
        pub use crate::wrapped_map::*;

        pub type T<A> = im::OrdMap<super::T, A>;

        pub type Key = super::T;
    }
}

/// `DocumentUri.t`, the type most of the protocol uses.
pub type DocumentUri = document_uri::T;

pub fn uri_of_string(s: &str) -> document_uri::T {
    document_uri::Uri(s.to_string())
}

pub fn string_of_uri(document_uri::Uri(s): &document_uri::T) -> String {
    s.clone()
}

/// A position is between two characters like an 'insert' cursor in a editor
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Position {
    /// line position in a document [zero-based]
    pub line: isize,
    /// character offset on a line in a document [zero-based]
    pub character: isize,
}

const LSP_ML: &str = "hack/src/utils/lsp/lsp.ml";

/// `[@@deriving of_yojson]`
pub fn position_of_yojson(yojson: &yojson::T) -> Result<Position, yojson_conv::OfYojsonError> {
    let mut line = None;
    let mut character = None;
    yojson_conv::record_of_yojson(
        &format!("{}.position", LSP_ML),
        yojson,
        &mut [
            ("line", &mut |j| {
                line = Some(yojson_conv::int_of_yojson(j)?);
                Ok(())
            }),
            ("character", &mut |j| {
                character = Some(yojson_conv::int_of_yojson(j)?);
                Ok(())
            }),
        ],
    )?;
    Ok(Position {
        line: line.unwrap(),
        character: character.unwrap(),
    })
}

/// A range is comparable to a selection in an editor
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Range {
    /// the range's start position
    pub start: Position,
    /// the range's end position [exclusive]
    pub end_: Position,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TextDocumentSaveReason {
    Manual,
    AfterDelay,
    FocusOut,
}

pub fn text_document_save_reason_to_enum(x: TextDocumentSaveReason) -> isize {
    match x {
        TextDocumentSaveReason::Manual => 1,
        TextDocumentSaveReason::AfterDelay => 2,
        TextDocumentSaveReason::FocusOut => 3,
    }
}

pub fn text_document_save_reason_of_enum(i: isize) -> Option<TextDocumentSaveReason> {
    match i {
        1 => Some(TextDocumentSaveReason::Manual),
        2 => Some(TextDocumentSaveReason::AfterDelay),
        3 => Some(TextDocumentSaveReason::FocusOut),
        _ => None,
    }
}

/// Represents a location inside a resource, such as a line inside a text file
pub mod location {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub uri: super::DocumentUri,
        pub range: super::Range,
    }
}

/// Represents a location inside a resource which also wants to display a
/// friendly name to the user.
pub mod definition_location {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub location: super::location::T,
        pub title: Option<String>,
    }
}

/// markedString can be used to render human readable text. It is either a
/// markdown string or a code-block that provides a language and a code snippet.
/// Note that markdown strings will be sanitized by the client - including
/// escaping html
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MarkedString {
    MarkedString(String),
    /// lang, value
    MarkedCode(String, String),
}

/// `[@@deriving show]`: `pp_markedString`, as `ppx_deriving` writes it.
pub fn pp_marked_string(fmt: &mut crate::format::Formatter, x: &MarkedString) {
    use crate::format::*;
    match x {
        MarkedString::MarkedString(a0) => {
            // "(@[<2>Lsp.MarkedString@ " "%S" "@])"
            pp_print_string(fmt, "(");
            pp_open_box(fmt, 2);
            pp_print_string(fmt, "Lsp.MarkedString");
            pp_print_space(fmt);
            pp_print_string(fmt, &crate::rt::ocaml_printf::sprintf_s(a0));
            pp_close_box(fmt);
            pp_print_string(fmt, ")");
        }
        MarkedString::MarkedCode(a0, a1) => {
            // "(@[<2>Lsp.MarkedCode (@," "%S" ",@ " "%S" "@,))@]"
            pp_print_string(fmt, "(");
            pp_open_box(fmt, 2);
            pp_print_string(fmt, "Lsp.MarkedCode (");
            pp_print_cut(fmt);
            pp_print_string(fmt, &crate::rt::ocaml_printf::sprintf_s(a0));
            pp_print_string(fmt, ",");
            pp_print_space(fmt);
            pp_print_string(fmt, &crate::rt::ocaml_printf::sprintf_s(a1));
            pp_print_cut(fmt);
            pp_print_string(fmt, "))");
            pp_close_box(fmt);
        }
    }
}

/// `[@@deriving show]`: `show_markedString`
pub fn show_marked_string(x: &MarkedString) -> String {
    crate::format::asprintf(|fmt| pp_marked_string(fmt, x))
}

/// Represents a reference to a command. Provides a title which will be used to
/// represent a command in the UI. Commands are identitifed using a string
/// identifier and the protocol currently doesn't specify a set of well known
/// commands. So executing a command requires some tool extension code.
pub mod command {
    use crate::yojson::safe as yojson;

    #[derive(Clone, Debug, PartialEq)]
    pub struct T {
        /// title of the command, like `save`
        pub title: String,
        /// the identifier of the actual command handler
        pub command: String,
        /// wire: it can be omitted
        pub arguments: Vec<yojson::T>,
    }
}

/// A textual edit applicable to a text document. If n textEdits are applied
/// to a text document all text edits describe changes to the initial document
/// version. Execution wise text edits should applied from the bottom to the
/// top of the text document. Overlapping text edits are not supported.
pub mod text_edit {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        /// to insert text, use a range where start = end
        pub range: super::Range,
        /// for delete operations, use an empty string
        pub new_text: String,
    }
}

/// Text documents are identified using a URI.
pub mod text_document_identifier {
    use crate::rt::yojson_conv;
    use crate::yojson::safe as yojson;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub uri: super::DocumentUri,
    }

    /// `[@@deriving of_yojson]`
    pub fn t_of_yojson(yojson: &yojson::T) -> Result<T, yojson_conv::OfYojsonError> {
        let mut uri = None;
        yojson_conv::record_of_yojson(
            &format!("{}.TextDocumentIdentifier.t", super::LSP_ML),
            yojson,
            &mut [("uri", &mut |j| {
                uri = Some(super::document_uri::t_of_yojson(j)?);
                Ok(())
            })],
        )?;
        Ok(T { uri: uri.unwrap() })
    }
}

/// An identifier to denote a specific version of a text document.
pub mod versioned_text_document_identifier {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub uri: super::DocumentUri,
        pub version: isize,
    }
}

/// Describes textual changes on a single text document. The text document is
/// referred to as a VersionedTextDocumentIdentifier to allow clients to check
/// the text document version before an edit is applied.
pub mod text_document_edit {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub text_document: super::versioned_text_document_identifier::T,
        pub edits: Vec<super::text_edit::T>,
    }
}

/// A workspace edit represents changes to many resources managed in the
/// workspace. A workspace edit consists of a mapping from a URI to an
/// array of TextEdits to be applied to the document with that URI.
pub mod workspace_edit {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        /// holds changes to existing docs
        pub changes: super::document_uri::map::T<Vec<super::text_edit::T>>,
    }
}

/// An item to transfer a text document from the client to the server. The
/// version number strictly increases after each change, including undo/redo.
pub mod text_document_item {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub uri: super::DocumentUri,
        pub language_id: String,
        pub version: isize,
        pub text: String,
    }
}

/// A code lens represents a command that should be shown along with
/// source text, like the number of references, a way to run tests, etc.
///
/// A code lens is _unresolved_ when no command is associated to it. For performance
/// reasons the creation of a code lens and resolving should be done in two stages.
pub mod code_lens {
    use crate::yojson::safe as yojson;

    #[derive(Clone, Debug, PartialEq)]
    pub struct T {
        pub range: super::Range,
        pub command: super::command::T,
        pub data: Option<yojson::T>,
    }
}

/// A parameter literal used in requests to pass a text document and a position
/// inside that document.
pub mod text_document_position_params {
    use crate::rt::yojson_conv;
    use crate::yojson::safe as yojson;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub text_document: super::text_document_identifier::T,
        pub position: super::Position,
    }

    /// `[@@deriving of_yojson]`
    pub fn t_of_yojson(yojson: &yojson::T) -> Result<T, yojson_conv::OfYojsonError> {
        let mut text_document = None;
        let mut position = None;
        yojson_conv::record_of_yojson(
            &format!("{}.TextDocumentPositionParams.t", super::LSP_ML),
            yojson,
            &mut [
                ("textDocument", &mut |j| {
                    text_document = Some(super::text_document_identifier::t_of_yojson(j)?);
                    Ok(())
                }),
                ("position", &mut |j| {
                    position = Some(super::position_of_yojson(j)?);
                    Ok(())
                }),
            ],
        )?;
        Ok(T {
            text_document: text_document.unwrap(),
            position: position.unwrap(),
        })
    }
}

/// A document filter denotes a document through properties like language,
/// schema or pattern. E.g. language:"typescript",scheme:"file"
/// or language:"json",pattern:"**/package.json"
pub mod document_filter {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        /// a language id, like "typescript"
        pub language: Option<String>,
        /// a uri scheme, like "file" or "untitled"
        pub scheme: Option<String>,
        /// a glob pattern, like "*.{ts,js}"
        pub pattern: Option<String>,
    }
}

/// A document selector is the combination of one or many document filters.
pub mod document_selector {
    pub type T = Vec<super::document_filter::T>;
}

/// Represents information about programming constructs like variables etc.
pub mod symbol_information {
    /// These numbers should match
    /// https://microsoft.github.io/language-server-protocol/specifications/specification-3-17/#symbolKind
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum SymbolKind {
        File,
        Module,
        Namespace,
        Package,
        Class,
        Method,
        Property,
        Field,
        Constructor,
        Enum,
        Interface,
        Function,
        Variable,
        Constant,
        String,
        Number,
        Boolean,
        Array,
        Object,
        Key,
        Null,
        EnumMember,
        Struct,
        Event,
        Operator,
        TypeParameter,
    }

    const SYMBOL_KINDS: [SymbolKind; 26] = [
        SymbolKind::File,
        SymbolKind::Module,
        SymbolKind::Namespace,
        SymbolKind::Package,
        SymbolKind::Class,
        SymbolKind::Method,
        SymbolKind::Property,
        SymbolKind::Field,
        SymbolKind::Constructor,
        SymbolKind::Enum,
        SymbolKind::Interface,
        SymbolKind::Function,
        SymbolKind::Variable,
        SymbolKind::Constant,
        SymbolKind::String,
        SymbolKind::Number,
        SymbolKind::Boolean,
        SymbolKind::Array,
        SymbolKind::Object,
        SymbolKind::Key,
        SymbolKind::Null,
        SymbolKind::EnumMember,
        SymbolKind::Struct,
        SymbolKind::Event,
        SymbolKind::Operator,
        SymbolKind::TypeParameter,
    ];

    /// `[@value 1]` to `[@value 26]`, in order.
    pub fn symbol_kind_to_enum(x: SymbolKind) -> isize {
        SYMBOL_KINDS.iter().position(|k| *k == x).unwrap() as isize + 1
    }

    pub fn symbol_kind_of_enum(i: isize) -> Option<SymbolKind> {
        if (1..=26).contains(&i) {
            Some(SYMBOL_KINDS[i as usize - 1])
        } else {
            None
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub name: String,
        pub kind: SymbolKind,
        /// the span of the symbol including its contents
        pub location: super::location::T,
        pub detail: Option<String>,
        /// the symbol containing this symbol
        pub container_name: Option<String>,
    }
}

/// Represents an item in the Call Hieararchy
pub mod call_hierarchy_item {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub name: String,
        pub kind: super::symbol_information::SymbolKind,
        pub detail: Option<String>,
        pub uri: super::DocumentUri,
        pub range: super::Range,
        pub selection_range: super::Range,
    }
}

/// Represents a parameter for a CallHierarchyIncomingCallsRequest or CallHierarchyOutgoingCallsRequest
pub mod call_hierarchy_calls_request_param {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub item: super::call_hierarchy_item::T,
    }
}

/// For showing messages (not diagnostics) in the user interface.
pub mod message_type {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum T {
        ErrorMessage,
        WarningMessage,
        InfoMessage,
        LogMessage,
    }

    pub use T::*;

    /// `[@@deriving eq]`
    pub fn equal(a: &T, b: &T) -> bool {
        a == b
    }

    pub fn to_enum(x: T) -> isize {
        match x {
            ErrorMessage => 1,
            WarningMessage => 2,
            InfoMessage => 3,
            LogMessage => 4,
        }
    }

    pub fn of_enum(i: isize) -> Option<T> {
        match i {
            1 => Some(ErrorMessage),
            2 => Some(WarningMessage),
            3 => Some(InfoMessage),
            4 => Some(LogMessage),
            _ => None,
        }
    }
}

/// The kind of a code action.
/// Kinds are a hierarchical list of identifiers separated by `.`, e.g.
/// `"refactor.extract.function"`.
/// The set of kinds is open and client needs to announce the kinds it supports
/// to the server during initialization.
/// Module CodeAction below also references this module as Kind.
pub mod code_action_kind {
    /// CodeActionKind.t uses a pair to represent a non-empty list
    /// and we provide utility functions for creation, membership, printing.
    pub type T = (String, Vec<String>);

    /// is x of kind k?
    pub fn is_kind((k, ks): &T, (x, xs): &T) -> bool {
        fn is_prefix_of(ks: &[String], xs: &[String]) -> bool {
            match (ks, xs) {
                ([], _) => true,
                ([k, ks @ ..], [x, xs @ ..]) if k == x => is_prefix_of(ks, xs),
                (_, _) => false,
            }
        }
        k == x && is_prefix_of(ks, xs)
    }

    /// does `ks` contain kind `k`
    pub fn contains_kind(k: &T, ks: &[T]) -> bool {
        ks.iter().any(|x| is_kind(k, x))
    }

    /// does an optional list of kinds `ks` contain kind `k`
    pub fn contains_kind_opt(default: bool, k: &T, ks: Option<&[T]>) -> bool {
        match ks {
            Some(ks) => contains_kind(k, ks),
            None => default,
        }
    }

    /// Create a kind from a string that follows the spec
    pub fn kind_of_string(s: &str) -> T {
        let mut parts = s.split('.').map(|s| s.to_string());
        match parts.next() {
            None => panic!("split_on_char does not return an empty list"),
            Some(k) => (k, parts.collect()),
        }
    }

    /// Create the equivalent string that the spec would have required
    pub fn string_of_kind((k, ks): &T) -> String {
        let mut parts = vec![k.as_str()];
        parts.extend(ks.iter().map(|s| s.as_str()));
        parts.join(".")
    }

    /// Create a new sub-kind of an existing kind
    pub fn sub_kind((k, ks): &T, s: &str) -> T {
        let cons_to_end = |ss: &[String], s: &str| {
            let mut ss = ss.to_vec();
            ss.push(s.to_string());
            ss
        };
        (k.clone(), cons_to_end(ks, s))
    }

    // -- Constants defined by the spec --

    /// Base kind for quickfix actions: 'quickfix'.
    pub fn quickfix() -> T {
        kind_of_string("quickfix")
    }

    /// Base kind for refactoring actions: 'refactor'.
    pub fn refactor() -> T {
        kind_of_string("refactor")
    }

    /// Base kind for refactoring extraction actions: 'refactor.extract'.
    pub fn refactor_extract() -> T {
        kind_of_string("refactor.extract")
    }

    /// Base kind for refactoring inline actions: 'refactor.inline'.
    pub fn refactor_inline() -> T {
        kind_of_string("refactor.inline")
    }

    /// Base kind for refactoring rewrite actions: 'refactor.rewrite'.
    pub fn refactor_rewrite() -> T {
        kind_of_string("refactor.rewrite")
    }

    /// Document-wide code actions
    pub fn source() -> T {
        kind_of_string("source")
    }

    /// Base kind for an organize imports source action: `source.organizeImports`.
    pub fn source_organize_imports() -> T {
        kind_of_string("source.organizeImports")
    }

    /// Base kind for a 'fix all' source action: `source.fixAll`.
    ///
    /// 'Fix all' actions automatically fix errors that have a clear fix that
    /// do not require user input. They should not suppress errors or perform
    /// unsafe fixes such as generating new types or classes.
    pub fn source_fix_all() -> T {
        kind_of_string("source.fixAll")
    }

    /// Empty kind
    pub fn empty() -> T {
        kind_of_string("")
    }
}

/// Cancellation notification, method="$/cancelRequest"
pub mod cancel_request {
    pub type Params = CancelParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CancelParams {
        /// the request id to cancel
        pub id: super::LspId,
    }
}

/// SetTraceNotification, method="$/setTraceNotification"
pub mod set_trace_notification {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Params {
        Verbose,
        Off,
    }
}

/// Initialize request, method="initialize"
pub mod initialize {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum TextDocumentSyncKind {
        /// docs should not be synced at all. Wire "None"
        NoSync,
        /// synced by always sending full content. Wire "Full"
        FullSync,
        IncrementalSync,
    }

    pub fn text_document_sync_kind_to_enum(x: TextDocumentSyncKind) -> isize {
        match x {
            TextDocumentSyncKind::NoSync => 0,
            TextDocumentSyncKind::FullSync => 1,
            TextDocumentSyncKind::IncrementalSync => 2,
        }
    }

    pub fn text_document_sync_kind_of_enum(i: isize) -> Option<TextDocumentSyncKind> {
        match i {
            0 => Some(TextDocumentSyncKind::NoSync),
            1 => Some(TextDocumentSyncKind::FullSync),
            2 => Some(TextDocumentSyncKind::IncrementalSync),
            _ => None,
        }
    }

    pub mod code_action_options {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct T {
            pub resolve_provider: bool,
        }
    }

    pub mod completion_options {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct T {
            /// server resolves extra info on demand
            pub resolve_provider: bool,
            /// wire "triggerCharacters"
            pub completion_trigger_characters: Vec<String>,
        }
    }

    pub mod server_experimental_capabilities {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct T {
            /// see ClientExperimentalCapabilities.snippetTextEdit
            pub snippet_text_edit: bool,
            pub auto_close_jsx: bool,
        }
    }

    pub mod client_experimental_capabilities {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct T {
            /// A client that supports this capability accepts snippet text edits like `${0:foo}`.
            /// https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#snippet_syntax
            pub snippet_text_edit: bool,
            pub auto_close_jsx: bool,
        }
    }

    /// These are hack-specific options. They're all optional in initialize request,
    /// and we pick a default if necessary while parsing.
    #[derive(Clone, Debug, PartialEq)]
    pub struct InitializationOptions {
        /// used for test scenarios where we pass a naming-table sqlite file,
        /// rather than leaving clientIdeDaemon to find and download one itself.
        pub naming_table_saved_state_path: Option<String>,
        /// used for test scenarios where we've passed
        /// a naming-sqlite file and so clientIdeDaemon completes instantly, but we still want
        /// a little bit of a delay before it reports readiness so as to exercise race conditions.
        /// This is the delay in seconds.
        pub naming_table_saved_state_test_delay: f64,
        /// used for test scenarios where we want clientLsp to delay receiving any
        /// further LSP requests until clientIdeDaemon has done its init.
        pub delay_until_done_init: bool,
        /// `true` iff formatting is to be done on the LSP client,
        /// rather than provided by the LSP server.
        pub skip_lsp_server_on_type_formatting: bool,
    }

    #[derive(Clone, Debug, PartialEq)]
    pub struct Params {
        /// pid of parent process
        pub process_id: Option<isize>,
        /// deprecated
        pub root_path: Option<String>,
        /// the root URI of the workspace
        pub root_uri: Option<super::DocumentUri>,
        pub initialization_options: InitializationOptions,
        /// "capabilities" over wire
        pub client_capabilities: ClientCapabilities,
        /// the initial trace setting, default="off"
        pub trace: Trace,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Result {
        /// "capabilities" over wire
        pub server_capabilities: ServerCapabilities,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ErrorData {
        /// should client retry the initialize request
        pub retry: bool,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Trace {
        Off,
        Messages,
        Verbose,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ClientCapabilities {
        pub workspace: WorkspaceClientCapabilities,
        pub text_document: TextDocumentClientCapabilities,
        pub window: WindowClientCapabilities,
        /// omitted: experimental
        pub telemetry: TelemetryClientCapabilities,
        pub client_experimental: client_experimental_capabilities::T,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct WorkspaceClientCapabilities {
        /// client supports appling batch edits
        pub apply_edit: bool,
        pub workspace_edit: WorkspaceEdit,
        /// omitted: other dynamic-registration fields
        pub did_change_watched_files: DynamicRegistration,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DynamicRegistration {
        /// client supports dynamic registration for this capability
        pub dynamic_registration: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct WorkspaceEdit {
        /// client supports versioned doc changes
        pub document_changes: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct TextDocumentClientCapabilities {
        pub synchronization: Synchronization,
        /// textDocument/completion
        pub completion: Completion,
        pub code_action: CodeAction,
        pub definition: Definition,
        pub type_definition: TypeDefinition,
        pub declaration: Declaration,
        pub implementation: Implementation,
    }

    /// synchronization capabilities say what messages the client is capable
    /// of sending, should be be so asked by the server.
    /// We use the "can_" prefix for OCaml naming reasons; it's absent in LSP
    /// (and in these fields).
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Synchronization {
        /// `can_willSave`: client can send textDocument/willSave
        pub will_save: bool,
        /// `can_willSaveWaitUntil`: textDoc.../willSaveWaitUntil
        pub will_save_wait_until: bool,
        /// `can_didSave`: textDocument/didSave
        pub did_save: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Completion {
        pub completion_item: CompletionItem,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CompletionItem {
        /// client can do snippets as insert text
        pub snippet_support: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CodeAction {
        /// wire: dynamicRegistraction
        /// Whether code action supports dynamic registration.
        pub code_action_dynamic_registration: bool,
        /// The client support code action literals as a valid
        /// response of the `textDocument/codeAction` request.
        pub code_action_literal_support: Option<CodeActionliteralSupport>,
    }

    /// The code action kind values the client supports. When this
    /// property exists the client also guarantees that it will
    /// handle values outside its set gracefully and falls back
    /// to a default value when unknown.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CodeActionliteralSupport {
        /// wire: valueSet
        pub code_action_value_set: Vec<super::code_action_kind::T>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Definition {
        pub definition_link_support: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct TypeDefinition {
        pub type_definition_link_support: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Declaration {
        pub declaration_link_support: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Implementation {
        pub implementation_link_support: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct WindowClientCapabilities {
        /// Nuclide-specific: client supports window/showStatusRequest
        pub status: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct TelemetryClientCapabilities {
        /// Nuclide-specific: client supports telemetry/connectionStatus
        pub connection_status: bool,
    }

    /// What capabilities the server provides
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ServerCapabilities {
        /// how to sync
        pub text_document_sync: TextDocumentSyncOptions,
        pub hover_provider: bool,
        pub completion_provider: Option<completion_options::T>,
        pub signature_help_provider: Option<SignatureHelpOptions>,
        pub definition_provider: bool,
        pub type_definition_provider: bool,
        pub references_provider: bool,
        pub call_hierarchy_provider: bool,
        pub document_highlight_provider: bool,
        /// ie. document outline
        pub document_symbol_provider: bool,
        /// ie. find-symbol-in-project
        pub workspace_symbol_provider: bool,
        pub code_action_provider: Option<code_action_options::T>,
        pub code_lens_provider: Option<CodeLensOptions>,
        pub document_formatting_provider: bool,
        pub document_range_formatting_provider: bool,
        pub document_on_type_formatting_provider: Option<DocumentOnTypeFormattingOptions>,
        pub rename_provider: bool,
        pub document_link_provider: Option<DocumentLinkOptions>,
        pub execute_command_provider: Option<ExecuteCommandOptions>,
        pub implementation_provider: bool,
        /// Nuclide-specific feature
        pub rage_provider_fb: bool,
        pub server_experimental: Option<server_experimental_capabilities::T>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct SignatureHelpOptions {
        pub sighelp_trigger_characters: Vec<String>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CodeLensOptions {
        /// wire "resolveProvider"
        pub codelens_resolve_provider: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DocumentOnTypeFormattingOptions {
        pub first_trigger_character: String,
        /// e.g. "}"
        pub more_trigger_character: Vec<String>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DocumentLinkOptions {
        /// wire "resolveProvider"
        pub doclink_resolve_provider: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ExecuteCommandOptions {
        /// the commands to be executed on the server
        pub commands: Vec<String>,
    }

    /// text document sync options say what messages the server requests the
    /// client to send. We use the "want_" prefix for OCaml naming reasons;
    /// this prefix is absent in LSP (and in these fields).
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct TextDocumentSyncOptions {
        /// `want_openClose`: textDocument/didOpen+didClose
        pub open_close: bool,
        /// `want_change`
        pub change: TextDocumentSyncKind,
        /// `want_willSave`: textDocument/willSave
        pub will_save: bool,
        /// `want_willSaveWaitUntil`: textDoc.../willSaveWaitUntil
        pub will_save_wait_until: bool,
        /// `want_didSave`: textDocument/didSave
        pub did_save: Option<SaveOptions>,
    }

    /// full only on open. Wire "Incremental"
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct SaveOptions {
        /// the client should include content on save
        pub include_text: bool,
    }
}

/// ErrorResponse
pub mod error {
    use crate::yojson::safe as yojson;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum Code {
        ParseError,
        InvalidRequest,
        MethodNotFound,
        InvalidParams,
        InternalError,
        ServerErrorStart,
        ServerErrorEnd,
        ServerNotInitialized,
        UnknownErrorCode,
        RequestCancelled,
        ContentModified,
    }

    pub use Code::*;

    pub fn code_to_enum(x: Code) -> isize {
        match x {
            ParseError => -32700,
            InvalidRequest => -32600,
            MethodNotFound => -32601,
            InvalidParams => -32602,
            InternalError => -32603,
            ServerErrorStart => -32099,
            ServerErrorEnd => -32000,
            ServerNotInitialized => -32002,
            UnknownErrorCode => -32001,
            RequestCancelled => -32800,
            ContentModified => -32801,
        }
    }

    pub fn code_of_enum(i: isize) -> Option<Code> {
        match i {
            -32700 => Some(ParseError),
            -32600 => Some(InvalidRequest),
            -32601 => Some(MethodNotFound),
            -32602 => Some(InvalidParams),
            -32603 => Some(InternalError),
            -32099 => Some(ServerErrorStart),
            -32000 => Some(ServerErrorEnd),
            -32002 => Some(ServerNotInitialized),
            -32001 => Some(UnknownErrorCode),
            -32800 => Some(RequestCancelled),
            -32801 => Some(ContentModified),
            _ => None,
        }
    }

    /// `[@@deriving show { with_path = false }]`: the name of the
    /// constructor.
    pub fn show_code(x: Code) -> String {
        format!("{:?}", x)
    }

    #[derive(Clone, Debug, PartialEq)]
    pub struct T {
        pub code: Code,
        pub message: String,
        pub data: Option<yojson::T>,
    }

    /// For methods which want to return exceptions, and they also want to decide
    /// how the exception gets serialized over LSP, they should throw this one.
    #[derive(Clone, PartialEq)]
    pub struct LspException(pub T);

    impl std::fmt::Debug for LspException {
        /// `Printexc.to_string`: the argument is a record, printed `_`.
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("Lsp.Error.LspException(_)")
        }
    }
}

/// Rage request, method="telemetry/rage"
pub mod rage_fb {
    pub type Result = Vec<RageItem>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct RageItem {
        pub title: Option<String>,
        pub data: String,
    }
}

/// Code Lens resolve request, method="codeLens/resolve"
pub mod code_lens_resolve {
    pub type Params = super::code_lens::T;

    pub type Result = super::code_lens::T;
}

/// Hover request, method="textDocument/hover"
pub mod hover {
    pub type Params = super::text_document_position_params::T;

    pub type Result = Option<HoverResult>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct HoverResult {
        /// wire: either a single one or an array
        pub contents: Vec<super::MarkedString>,
        pub range: Option<super::Range>,
    }
}

/// PublishDiagnostics notification, method="textDocument/PublishDiagnostics"
pub mod publish_diagnostics {
    use crate::yojson::safe as yojson;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum DiagnosticSeverity {
        Error,
        Warning,
        Information,
        Hint,
    }

    /// `[@@deriving eq]`
    pub fn equal_diagnostic_severity(a: &DiagnosticSeverity, b: &DiagnosticSeverity) -> bool {
        a == b
    }

    pub fn diagnostic_severity_to_enum(x: DiagnosticSeverity) -> isize {
        match x {
            DiagnosticSeverity::Error => 1,
            DiagnosticSeverity::Warning => 2,
            DiagnosticSeverity::Information => 3,
            DiagnosticSeverity::Hint => 4,
        }
    }

    pub fn diagnostic_severity_of_enum(i: isize) -> Option<DiagnosticSeverity> {
        match i {
            1 => Some(DiagnosticSeverity::Error),
            2 => Some(DiagnosticSeverity::Warning),
            3 => Some(DiagnosticSeverity::Information),
            4 => Some(DiagnosticSeverity::Hint),
            _ => None,
        }
    }

    pub type Params = PublishDiagnosticsParams;

    #[derive(Clone, Debug, PartialEq)]
    pub struct PublishDiagnosticsParams {
        pub uri: super::DocumentUri,
        pub diagnostics: Vec<Diagnostic>,
        /// FB-specific extension, for diagnostics used only to show status
        pub is_status_fb: bool,
    }

    /// (`[@@deriving eq]` ignores `data`: `[@equal (fun _ _ -> true)]`.)
    #[derive(Clone, Debug)]
    pub struct Diagnostic {
        /// the range at which the message applies
        pub range: super::Range,
        /// if omitted, client decides
        pub severity: Option<DiagnosticSeverity>,
        pub code: DiagnosticCode,
        /// human-readable string, eg. typescript/lint
        pub source: Option<String>,
        /// the diagnostic's message
        pub message: String,
        pub related_information: Vec<DiagnosticRelatedInformation>,
        /// legacy FB extension
        pub related_locations: Vec<RelatedLocation>,
        pub data: Option<yojson::T>,
    }

    impl PartialEq for Diagnostic {
        fn eq(&self, other: &Self) -> bool {
            self.range == other.range
                && self.severity == other.severity
                && self.code == other.code
                && self.source == other.source
                && self.message == other.message
                && self.related_information == other.related_information
                && self.related_locations == other.related_locations
        }
    }

    /// `[@@deriving eq]`
    pub fn equal_diagnostic(a: &Diagnostic, b: &Diagnostic) -> bool {
        a == b
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum DiagnosticCode {
        IntCode(isize),
        StringCode(String),
        NoCode,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DiagnosticRelatedInformation {
        /// wire: just "location"
        pub related_location: super::location::T,
        /// wire: just "message"
        pub related_message: String,
    }

    /// legacy FB extension
    pub type RelatedLocation = DiagnosticRelatedInformation;
}

/// DidOpenTextDocument notification, method="textDocument/didOpen"
pub mod did_open {
    pub type Params = DidOpenTextDocumentParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DidOpenTextDocumentParams {
        /// the document that was opened
        pub text_document: super::text_document_item::T,
    }
}

/// DidCloseTextDocument notification, method="textDocument/didClose"
pub mod did_close {
    pub type Params = DidCloseTextDocumentParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DidCloseTextDocumentParams {
        /// the doc that was closed
        pub text_document: super::text_document_identifier::T,
    }
}

/// DidSaveTextDocument notification, method="textDocument/didSave"
pub mod did_save {
    pub type Params = DidSaveTextDocumentParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DidSaveTextDocumentParams {
        /// the doc that was saved
        pub text_document: super::text_document_identifier::T,
        /// content when saved; depends on includeText
        pub text: Option<String>,
    }
}

/// DidChangeTextDocument notification, method="textDocument/didChange"
pub mod did_change {
    pub type Params = DidChangeTextDocumentParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DidChangeTextDocumentParams {
        pub text_document: super::versioned_text_document_identifier::T,
        pub content_changes: Vec<TextDocumentContentChangeEvent>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct TextDocumentContentChangeEvent {
        /// the range of the document that changed
        pub range: Option<super::Range>,
        /// the length that got replaced
        pub range_length: Option<isize>,
        /// the new text of the range/document
        pub text: String,
    }
}

/// WillSaveWaitUntilTextDocument request, method="textDocument/willSaveWaitUntil"
pub mod will_save_wait_until {
    pub type Params = WillSaveWaitUntilTextDocumentParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct WillSaveWaitUntilTextDocumentParams {
        pub text_document: super::text_document_identifier::T,
        pub reason: super::TextDocumentSaveReason,
    }

    pub type Result = Vec<super::text_edit::T>;
}

pub mod top_level_def_name_at_pos {
    use crate::rt::yojson_conv;
    use crate::yojson::safe as yojson;

    pub type Params = super::text_document_position_params::T;

    /// `[@@deriving of_yojson]`
    pub fn params_of_yojson(
        yojson: &yojson::T,
    ) -> std::result::Result<Params, yojson_conv::OfYojsonError> {
        super::text_document_position_params::t_of_yojson(yojson)
    }

    pub type Result = Option<String>;

    /// `[@@deriving yojson_of]`
    pub fn yojson_of_result(v: &Result) -> yojson::T {
        yojson_conv::yojson_of_option(|s: &String| yojson_conv::yojson_of_string(s), v)
    }
}

/// Watched files changed notification, method="workspace/didChangeWatchedFiles"
pub mod did_change_watched_files {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct RegisterOptions {
        pub watchers: Vec<FileSystemWatcher>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct FileSystemWatcher {
        pub glob_pattern: String,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum FileChangeType {
        Created,
        Updated,
        Deleted,
    }

    pub fn file_change_type_to_enum(x: FileChangeType) -> isize {
        match x {
            FileChangeType::Created => 1,
            FileChangeType::Updated => 2,
            FileChangeType::Deleted => 3,
        }
    }

    pub fn file_change_type_of_enum(i: isize) -> Option<FileChangeType> {
        match i {
            1 => Some(FileChangeType::Created),
            2 => Some(FileChangeType::Updated),
            3 => Some(FileChangeType::Deleted),
            _ => None,
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Params {
        pub changes: Vec<FileEvent>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct FileEvent {
        pub uri: super::DocumentUri,
        pub type_: FileChangeType,
    }
}

/// Goto Definition request, method="textDocument/definition"
pub mod definition {
    pub type Params = super::text_document_position_params::T;

    /// wire: either a single one or an array
    pub type Result = Vec<super::definition_location::T>;
}

/// Goto TypeDefinition request, method="textDocument/typeDefinition"
pub mod type_definition {
    pub type Params = super::text_document_position_params::T;

    pub type Result = Vec<super::definition_location::T>;
}

/// Go To Implementation request, method="textDocument/implementation"
pub mod implementation {
    pub type Params = super::text_document_position_params::T;

    pub type Result = Vec<super::location::T>;
}

/// A code action represents a change that can be performed in code, e.g. to fix a problem or
/// to refactor code.
///
/// textDocument/codeAction and codeAction/resolve
pub mod code_action {
    /// Note: For "textDocument/codeAction" requests we return a `data` field containing
    /// the original request params, then when the client sends "codeAction/resolve"
    /// we read the `data` param to re-calculate the requested code action. This
    /// adding of the "data" field is done in our serialization step, to avoid passing
    /// extra state around and enforce that `data` is all+only the original request params.
    /// See [EditAndOrCommand] for more information on the resolution flow.
    #[derive(Clone, Debug, PartialEq)]
    pub struct T<A> {
        /// A short, human-readable, title for this code action.
        pub title: String,
        /// The kind of the code action. Used to filter code actions.
        pub kind: super::code_action_kind::T,
        /// The diagnostics that this code action resolves.
        pub diagnostics: Vec<super::publish_diagnostics::Diagnostic>,
        /// A CodeAction must set either `edit`, a `command` (or neither iff only resolved lazily)
        /// If both are supplied, the `edit` is applied first, then the `command` is executed.
        /// If neither is supplied, the client requests 'edit' be resolved using "codeAction/resolve"
        pub action: EditAndOrCommand<A>,
        /// Marks this as an AI code action
        pub is_ai: Option<bool>,
    }

    /// 'resolution_phase is used to follow the protocol in a type-safe and prescribed manner:
    /// LSP protocol:
    /// 1. The client sends server "textDocument/codeAction"
    /// 2. The server can send back an unresolved code action (neither "edit" nor "command" fields)
    /// 3. If the code action is unresolved, the client sends "codeAction/resolve"
    ///
    /// Our implementation flow:
    ///   - create a representation of a code action which includes a lazily-computed edit
    ///     - if the request is "textDocument/codeAction", we do not compute an edit
    ///     - if the request is "codeAction/resolve", we have access to the original
    ///     request params via the `data` field (see [T] comments above) and perform
    ///     the same calculation as for "textDocument/codeAction" and then compute the edit.
    #[derive(Clone, Debug, PartialEq)]
    pub enum EditAndOrCommand<A> {
        EditOnly(super::workspace_edit::T),
        CommandOnly(super::command::T),
        BothEditThenCommand((super::workspace_edit::T, super::command::T)),
        /// UnresolvedEdit is for this flow:
        /// client --textDocument/codeAction --> server --response_with_unresolved_fields-->
        /// client --codeAction/resolve --> server --response_with_all_fields--> client
        UnresolvedEdit(A),
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum CommandOrAction_<A> {
        Command(super::command::T),
        Action(T<A>),
    }

    /// `type resolved_marker = |`
    #[derive(Clone, Debug, PartialEq)]
    pub enum ResolvedMarker {}

    pub type ResolvedCommandOrAction = CommandOrAction_<ResolvedMarker>;

    pub type CommandOrAction = CommandOrAction_<()>;

    pub type Result = Vec<CommandOrAction>;
}

/// Code Action Request, method="textDocument/codeAction"
pub mod code_action_request {
    #[derive(Clone, Debug, PartialEq)]
    pub struct Params {
        /// The document in which the command was invoked.
        pub text_document: super::text_document_identifier::T,
        /// The range for which the command was invoked.
        pub range: super::Range,
        /// Context carrying additional information.
        pub context: CodeActionContext,
    }

    /// Contains additional diagnostic information about the context in which
    /// a code action is run.
    #[derive(Clone, Debug, PartialEq)]
    pub struct CodeActionContext {
        pub diagnostics: Vec<super::publish_diagnostics::Diagnostic>,
        pub only: Option<Vec<super::code_action_kind::T>>,
    }
}

/// Completion request, method="textDocument/completion"
pub mod code_action_resolve {
    pub type Result =
        std::result::Result<super::code_action::ResolvedCommandOrAction, super::error::T>;
}

/// method="codeAction/resolve"
pub mod code_action_resolve_request {
    /// The client sends a partially-resolved [CodeAction] with an additional [data] field.
    /// We don't bother parsing all the fields from the partially-resolved [CodeAction] because
    /// [data] and [title] are all we need and so we don't have to duplicate the entire
    /// [CodeAction.command_or_action] shape here
    #[derive(Clone, Debug, PartialEq)]
    pub struct Params {
        pub data: super::code_action_request::Params,
        /// From LSP spec: "A data entry field that is preserved on a code action between
        /// a `textDocument/codeAction` and a `codeAction/resolve` request"
        /// We commit to a single representation for simplicity and type-safety
        pub title: String,
    }
}

/// Completion request, method="textDocument/completion"
pub mod completion {
    use crate::yojson::safe as yojson;

    /// These numbers should match
    /// https://microsoft.github.io/language-server-protocol/specification#textDocument_completion
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum CompletionItemKind {
        Text,
        Method,
        Function,
        Constructor,
        Field,
        Variable,
        Class,
        Interface,
        Module,
        Property,
        Unit,
        Value,
        Enum,
        Keyword,
        Snippet,
        Color,
        File,
        Reference,
        Folder,
        MemberOf,
        Constant,
        Struct,
        Event,
        Operator,
        TypeParameter,
    }

    const COMPLETION_ITEM_KINDS: [CompletionItemKind; 25] = [
        CompletionItemKind::Text,
        CompletionItemKind::Method,
        CompletionItemKind::Function,
        CompletionItemKind::Constructor,
        CompletionItemKind::Field,
        CompletionItemKind::Variable,
        CompletionItemKind::Class,
        CompletionItemKind::Interface,
        CompletionItemKind::Module,
        CompletionItemKind::Property,
        CompletionItemKind::Unit,
        CompletionItemKind::Value,
        CompletionItemKind::Enum,
        CompletionItemKind::Keyword,
        CompletionItemKind::Snippet,
        CompletionItemKind::Color,
        CompletionItemKind::File,
        CompletionItemKind::Reference,
        CompletionItemKind::Folder,
        CompletionItemKind::MemberOf,
        CompletionItemKind::Constant,
        CompletionItemKind::Struct,
        CompletionItemKind::Event,
        CompletionItemKind::Operator,
        CompletionItemKind::TypeParameter,
    ];

    /// `[@value 1]` to `[@value 25]`, in order.
    pub fn completion_item_kind_to_enum(x: CompletionItemKind) -> isize {
        COMPLETION_ITEM_KINDS.iter().position(|k| *k == x).unwrap() as isize + 1
    }

    pub fn completion_item_kind_of_enum(i: isize) -> Option<CompletionItemKind> {
        if (1..=25).contains(&i) {
            Some(COMPLETION_ITEM_KINDS[i as usize - 1])
        } else {
            None
        }
    }

    /// These numbers should match
    /// https://microsoft.github.io/language-server-protocol/specification#textDocument_completion
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum InsertTextFormat {
        /// the insertText/textEdits are just plain strings
        PlainText,
        /// wire: just "Snippet"
        SnippetFormat,
    }

    pub fn insert_text_format_to_enum(x: InsertTextFormat) -> isize {
        match x {
            InsertTextFormat::PlainText => 1,
            InsertTextFormat::SnippetFormat => 2,
        }
    }

    pub fn insert_text_format_of_enum(i: isize) -> Option<InsertTextFormat> {
        match i {
            1 => Some(InsertTextFormat::PlainText),
            2 => Some(InsertTextFormat::SnippetFormat),
            _ => None,
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum CompletionTriggerKind {
        Invoked,
        TriggerCharacter,
        TriggerForIncompleteCompletions,
    }

    pub fn completion_trigger_kind_to_enum(x: CompletionTriggerKind) -> isize {
        match x {
            CompletionTriggerKind::Invoked => 1,
            CompletionTriggerKind::TriggerCharacter => 2,
            CompletionTriggerKind::TriggerForIncompleteCompletions => 3,
        }
    }

    pub fn completion_trigger_kind_of_enum(i: isize) -> Option<CompletionTriggerKind> {
        match i {
            1 => Some(CompletionTriggerKind::Invoked),
            2 => Some(CompletionTriggerKind::TriggerCharacter),
            3 => Some(CompletionTriggerKind::TriggerForIncompleteCompletions),
            _ => None,
        }
    }

    pub fn is_invoked(x: CompletionTriggerKind) -> bool {
        match x {
            CompletionTriggerKind::Invoked => true,
            CompletionTriggerKind::TriggerCharacter
            | CompletionTriggerKind::TriggerForIncompleteCompletions => false,
        }
    }

    pub type Params = CompletionParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CompletionParams {
        pub loc: super::text_document_position_params::T,
        pub context: Option<CompletionContext>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CompletionContext {
        pub trigger_kind: CompletionTriggerKind,
        pub trigger_character: Option<String>,
    }

    pub type Result = CompletionList;

    /// wire: can also be 'completionItem list'
    #[derive(Clone, Debug, PartialEq)]
    pub struct CompletionList {
        /// further typing should result in recomputing
        pub is_incomplete: bool,
        pub items: Vec<CompletionItem>,
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum CompletionDocumentation {
        MarkedStringsDocumentation(Vec<super::MarkedString>),
        UnparsedDocumentation(yojson::T),
    }

    #[derive(Clone, Debug, PartialEq)]
    pub struct CompletionItem {
        /// the label in the UI
        pub label: String,
        /// tells editor which icon to use
        pub kind: Option<CompletionItemKind>,
        /// human-readable string like type/symbol info
        pub detail: Option<String>,
        /// human-readable doc-comment
        pub documentation: Option<CompletionDocumentation>,
        /// used for sorting; if absent, uses label
        pub sort_text: Option<String>,
        /// used for filtering; if absent, uses label
        pub filter_text: Option<String>,
        /// used for inserting; if absent, uses label
        pub insert_text: Option<String>,
        pub insert_text_format: Option<InsertTextFormat>,
        pub text_edit: Option<super::text_edit::T>,
        /// wire: split into hd and tl
        pub additional_text_edits: Vec<super::text_edit::T>,
        /// if present, is executed after completion
        pub command: Option<super::command::T>,
        pub data: Option<yojson::T>,
    }
}

/// Completion Item Resolve request, method="completionItem/resolve"
pub mod completion_item_resolve {
    pub type Params = super::completion::CompletionItem;

    pub type Result = super::completion::CompletionItem;
}

/// Workspace Symbols request, method="workspace/symbol"
pub mod workspace_symbol {
    pub type Params = WorkspaceSymbolParams;

    pub type Result = Vec<super::symbol_information::T>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct WorkspaceSymbolParams {
        /// a non-empty query string
        pub query: String,
    }
}

/// Document Symbols request, method="textDocument/documentSymbol"
pub mod document_symbol {
    pub type Params = DocumentSymbolParams;

    pub type Result = Vec<super::symbol_information::T>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DocumentSymbolParams {
        pub text_document: super::text_document_identifier::T,
    }
}

/// Find References request, method="textDocument/references"
pub mod find_references {
    pub type Params = ReferenceParams;

    pub type Result = Vec<super::location::T>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ReferenceParams {
        /// wire: loc's members are part of referenceParams
        pub loc: super::text_document_position_params::T,
        pub context: ReferenceContext,
        pub partial_result_token: Option<super::PartialResultToken>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ReferenceContext {
        /// include declaration of current symbol
        pub include_declaration: bool,
        pub include_indirect_references: bool,
    }
}

pub mod prepare_call_hierarchy {
    pub type Params = super::text_document_position_params::T;

    pub type Result = Option<Vec<super::call_hierarchy_item::T>>;
}

pub mod call_hierarchy_incoming_calls {
    pub type Params = super::call_hierarchy_calls_request_param::T;

    pub type Result = Option<Vec<CallHierarchyIncomingCall>>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CallHierarchyIncomingCall {
        pub from: super::call_hierarchy_item::T,
        pub from_ranges: Vec<super::Range>,
    }
}

pub mod call_hierarchy_outgoing_calls {
    pub type Params = super::call_hierarchy_calls_request_param::T;

    pub type Result = Option<Vec<CallHierarchyOutgoingCall>>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CallHierarchyOutgoingCall {
        /// The name should just be "to", but "to" is a reserved keyword in OCaml
        pub call_to: super::call_hierarchy_item::T,
        pub from_ranges: Vec<super::Range>,
    }
}

/// Document Highlights request, method="textDocument/documentHighlight"
pub mod document_highlight {
    pub type Params = super::text_document_position_params::T;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum DocumentHighlightKind {
        /// a textual occurrence
        Text,
        /// read-access of a symbol, like reading a variable
        Read,
        /// write-access of a symbol, like writing a variable
        Write,
    }

    pub fn document_highlight_kind_to_enum(x: DocumentHighlightKind) -> isize {
        match x {
            DocumentHighlightKind::Text => 1,
            DocumentHighlightKind::Read => 2,
            DocumentHighlightKind::Write => 3,
        }
    }

    pub fn document_highlight_kind_of_enum(i: isize) -> Option<DocumentHighlightKind> {
        match i {
            1 => Some(DocumentHighlightKind::Text),
            2 => Some(DocumentHighlightKind::Read),
            3 => Some(DocumentHighlightKind::Write),
            _ => None,
        }
    }

    pub type Result = Vec<DocumentHighlight>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DocumentHighlight {
        /// the range this highlight applies to
        pub range: super::Range,
        pub kind: Option<DocumentHighlightKind>,
    }
}

/// Document Formatting request, method="textDocument/formatting"
pub mod document_formatting {
    pub type Params = DocumentFormattingParams;

    pub type Result = Vec<super::text_edit::T>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DocumentFormattingParams {
        pub text_document: super::text_document_identifier::T,
        pub options: FormattingOptions,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct FormattingOptions {
        /// size of a tab in spaces
        pub tab_size: isize,
        /// prefer spaces over tabs
        /// omitted: signature for further properties
        pub insert_spaces: bool,
    }
}

/// Document Range Formatting request, method="textDocument/rangeFormatting"
pub mod document_range_formatting {
    pub type Params = DocumentRangeFormattingParams;

    pub type Result = Vec<super::text_edit::T>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DocumentRangeFormattingParams {
        pub text_document: super::text_document_identifier::T,
        pub range: super::Range,
        pub options: super::document_formatting::FormattingOptions,
    }
}

/// Document On Type Formatting req., method="textDocument/onTypeFormatting"
pub mod document_on_type_formatting {
    pub type Params = DocumentOnTypeFormattingParams;

    pub type Result = Vec<super::text_edit::T>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct DocumentOnTypeFormattingParams {
        pub text_document: super::text_document_identifier::T,
        /// the position at which this request was sent
        pub position: super::Position,
        /// the character that has been typed
        pub ch: String,
        pub options: super::document_formatting::FormattingOptions,
    }
}

/// Document Signature Help request, method="textDocument/signatureHelp"
pub mod signature_help {
    pub type Params = super::text_document_position_params::T;

    pub type Result = Option<T>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub signatures: Vec<SignatureInformation>,
        pub active_signature: isize,
        pub active_parameter: isize,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct SignatureInformation {
        pub siginfo_label: String,
        pub siginfo_documentation: Option<String>,
        pub parameters: Vec<ParameterInformation>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ParameterInformation {
        /// `parinfo_label`
        pub label: String,
        /// `parinfo_documentation`
        pub documentation: Option<String>,
    }
}

/// Auto close tag request, method="flow/autoCloseJsx"
/// This is a non-standard LSP extension.
pub mod auto_close_jsx {
    pub type Params = super::text_document_position_params::T;

    pub type Result = Option<String>;
}

/// Workspace Rename request, method="textDocument/rename"
pub mod rename {
    pub type Params = RenameParams;

    pub type Result = super::workspace_edit::T;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct RenameParams {
        pub text_document: super::text_document_identifier::T,
        pub position: super::Position,
        pub new_name: String,
    }
}

/// Code Lens request, method="textDocument/codeLens"
pub mod document_code_lens {
    pub type Params = CodelensParams;

    pub type Result = Vec<super::code_lens::T>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CodelensParams {
        pub text_document: super::text_document_identifier::T,
    }
}

/// LogMessage notification, method="window/logMessage"
pub mod log_message {
    pub type Params = LogMessageParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct LogMessageParams {
        pub type_: super::message_type::T,
        pub message: String,
    }
}

/// ShowMessage notification, method="window/showMessage"
pub mod show_message {
    pub type Params = ShowMessageParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ShowMessageParams {
        pub type_: super::message_type::T,
        pub message: String,
    }
}

/// ShowMessage request, method="window/showMessageRequest"
pub mod show_message_request {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum T {
        Present { id: super::LspId },
        Absent,
    }

    pub type Params = ShowMessageRequestParams;

    pub type Result = Option<MessageActionItem>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ShowMessageRequestParams {
        pub type_: super::message_type::T,
        pub message: String,
        pub actions: Vec<MessageActionItem>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct MessageActionItem {
        pub title: String,
    }
}

/// ShowStatus request, method="window/showStatus"
pub mod show_status_fb {
    use crate::yojson::safe as yojson;

    pub type Params = ShowStatusParams;

    pub type Result = ();

    /// the showStatus LSP request will be handled by our VSCode extension.
    /// It's a facebook-specific extension to the LSP spec. How it's rendered
    /// is currently [shortMessage] in the status-bar, and "[progress]/[total] [message]"
    /// in the tooltip. The [telemetry] field isn't displayed to the user, but might
    /// be useful to someone debugging an LSP transcript.
    #[derive(Clone, Debug, PartialEq)]
    pub struct ShowStatusParams {
        pub request: ShowStatusRequestParams,
        pub progress: Option<isize>,
        pub total: Option<isize>,
        pub short_message: Option<String>,
        pub telemetry: Option<yojson::T>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ShowStatusRequestParams {
        pub type_: super::message_type::T,
        pub message: String,
    }
}

/// ConnectionStatus notification, method="telemetry/connectionStatus"
pub mod connection_status_fb {
    pub type Params = ConnectionStatusParams;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ConnectionStatusParams {
        pub is_connected: bool,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LspRegistrationOptions {
    DidChangeWatchedFilesRegistrationOptions(did_change_watched_files::RegisterOptions),
}

/// Register capability request, method="client/registerCapability"
pub mod register_capability {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Params {
        pub registrations: Vec<Registration>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Registration {
        /// The ID field is arbitrary but unique per type of capability (for future
        /// deregistering, which we don't do).
        pub id: String,
        pub method_: String,
        pub register_options: super::LspRegistrationOptions,
    }

    pub fn make_registration(register_options: super::LspRegistrationOptions) -> Registration {
        let (id, method_) = match &register_options {
            super::LspRegistrationOptions::DidChangeWatchedFilesRegistrationOptions(_) => (
                "did-change-watched-files",
                "workspace/didChangeWatchedFiles",
            ),
        };
        Registration {
            id: id.to_string(),
            method_: method_.to_string(),
            register_options,
        }
    }
}

// Here are gathered-up ADTs for all the messages we handle

#[derive(Clone, Debug, PartialEq)]
pub enum LspRequest {
    InitializeRequest(initialize::Params),
    RegisterCapabilityRequest(register_capability::Params),
    ShutdownRequest,
    CodeLensResolveRequest(code_lens_resolve::Params),
    HoverRequest(hover::Params),
    DefinitionRequest(definition::Params),
    TypeDefinitionRequest(type_definition::Params),
    ImplementationRequest(implementation::Params),
    CodeActionRequest(code_action_request::Params),
    CodeActionResolveRequest(code_action_resolve_request::Params),
    CompletionRequest(completion::Params),
    CompletionItemResolveRequest(completion_item_resolve::Params),
    WorkspaceSymbolRequest(workspace_symbol::Params),
    DocumentSymbolRequest(document_symbol::Params),
    FindReferencesRequest(find_references::Params),
    PrepareCallHierarchyRequest(prepare_call_hierarchy::Params),
    CallHierarchyIncomingCallsRequest(call_hierarchy_incoming_calls::Params),
    CallHierarchyOutgoingCallsRequest(call_hierarchy_outgoing_calls::Params),
    DocumentHighlightRequest(document_highlight::Params),
    DocumentFormattingRequest(document_formatting::Params),
    DocumentRangeFormattingRequest(document_range_formatting::Params),
    DocumentOnTypeFormattingRequest(document_on_type_formatting::Params),
    ShowMessageRequestRequest(show_message_request::Params),
    ShowStatusRequestFB(show_status_fb::Params),
    RageRequestFB,
    RenameRequest(rename::Params),
    DocumentCodeLensRequest(document_code_lens::Params),
    SignatureHelpRequest(signature_help::Params),
    AutoCloseRequest(auto_close_jsx::Params),
    HackTestStartServerRequestFB,
    HackTestStopServerRequestFB,
    HackTestShutdownServerlessRequestFB,
    WillSaveWaitUntilRequest(will_save_wait_until::Params),
    TopLevelDefNameAtPosRequest(top_level_def_name_at_pos::Params),
    UnknownRequest(String, Option<yojson::T>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum LspResult {
    InitializeResult(initialize::Result),
    ShutdownResult,
    CodeLensResolveResult(code_lens_resolve::Result),
    HoverResult(hover::Result),
    DefinitionResult(definition::Result),
    TypeDefinitionResult(type_definition::Result),
    ImplementationResult(implementation::Result),
    CodeActionResult(code_action::Result, code_action_request::Params),
    CodeActionResolveResult(code_action_resolve::Result),
    CompletionResult(completion::Result),
    CompletionItemResolveResult(completion_item_resolve::Result),
    WorkspaceSymbolResult(workspace_symbol::Result),
    DocumentSymbolResult(document_symbol::Result),
    FindReferencesResult(find_references::Result),
    PrepareCallHierarchyResult(prepare_call_hierarchy::Result),
    CallHierarchyIncomingCallsResult(call_hierarchy_incoming_calls::Result),
    CallHierarchyOutgoingCallsResult(call_hierarchy_outgoing_calls::Result),
    DocumentHighlightResult(document_highlight::Result),
    DocumentFormattingResult(document_formatting::Result),
    DocumentRangeFormattingResult(document_range_formatting::Result),
    DocumentOnTypeFormattingResult(document_on_type_formatting::Result),
    ShowMessageRequestResult(show_message_request::Result),
    ShowStatusResultFB(show_status_fb::Result),
    RageResultFB(rage_fb::Result),
    RenameResult(rename::Result),
    DocumentCodeLensResult(document_code_lens::Result),
    SignatureHelpResult(signature_help::Result),
    AutoCloseResult(auto_close_jsx::Result),
    HackTestStartServerResultFB,
    HackTestStopServerResultFB,
    HackTestShutdownServerlessResultFB,
    RegisterCapabilityRequestResult,
    WillSaveWaitUntilResult(will_save_wait_until::Result),
    TopLevelDefNameAtPosResult(top_level_def_name_at_pos::Result),
    ErrorResult(error::T),
}

#[derive(Clone, Debug, PartialEq)]
pub enum LspNotification {
    ExitNotification,
    CancelRequestNotification(cancel_request::Params),
    PublishDiagnosticsNotification(publish_diagnostics::Params),
    DidOpenNotification(did_open::Params),
    DidCloseNotification(did_close::Params),
    DidSaveNotification(did_save::Params),
    DidChangeNotification(did_change::Params),
    DidChangeWatchedFilesNotification(did_change_watched_files::Params),
    LogMessageNotification(log_message::Params),
    /// For telemetry, LSP allows 'any', but we're going to send these
    TelemetryNotification(log_message::Params, Vec<(String, yojson::T)>),
    ShowMessageNotification(show_message::Params),
    ConnectionStatusNotificationFB(connection_status_fb::Params),
    InitializedNotification,
    FindReferencesPartialResultNotification(PartialResultToken, find_references::Result),
    SetTraceNotification(set_trace_notification::Params),
    SetTrace(set_trace_notification::Params),
    /// $/logTraceNotification
    LogTraceNotification,
    UnknownNotification(String, Option<yojson::T>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum LspMessage {
    RequestMessage(LspId, LspRequest),
    ResponseMessage(LspId, LspResult),
    NotificationMessage(LspNotification),
}

/// `'a lsp_handler = 'a lsp_result_handler * 'a lsp_error_handler`
pub type LspHandler<A> = (LspResultHandler<A>, LspErrorHandler<A>);

/// `'a lsp_error_handler = Error.t * string -> 'a -> 'a`
pub type LspErrorHandler<A> = std::rc::Rc<dyn Fn((error::T, String), &mut A)>;

pub enum LspResultHandler<A> {
    ShowMessageHandler(std::rc::Rc<dyn Fn(show_message_request::Result, &mut A)>),
    ShowStatusHandler(std::rc::Rc<dyn Fn(show_status_fb::Result, &mut A)>),
}

impl<A> Clone for LspResultHandler<A> {
    fn clone(&self) -> Self {
        match self {
            LspResultHandler::ShowMessageHandler(f) => {
                LspResultHandler::ShowMessageHandler(std::rc::Rc::clone(f))
            }
            LspResultHandler::ShowStatusHandler(f) => {
                LspResultHandler::ShowStatusHandler(std::rc::Rc::clone(f))
            }
        }
    }
}

pub mod id_key {
    pub type T = super::LspId;

    /// (The `Ord` of `LspId` is this order; the subtraction of OCaml wraps
    /// around as Rust's `wrapping_sub` does, for ids whose difference does
    /// not fit in an `int`.)
    pub fn compare(x: &T, y: &T) -> isize {
        match (x, y) {
            (super::NumberId(x), super::NumberId(y)) => x.wrapping_sub(*y),
            (super::NumberId(_), super::StringId(_)) => -1,
            (super::StringId(x), super::StringId(y)) => x.cmp(y) as isize,
            (super::StringId(_), super::NumberId(_)) => 1,
        }
    }
}

/// `Stdlib.Set.Make (IdKey)`
pub mod id_set {
    pub type T = im::OrdSet<super::LspId>;
}

/// `Wrapped_map.Make (IdKey)`
pub mod id_map {
    pub use crate::wrapped_map::*;

    pub type T<A> = im::OrdMap<super::LspId, A>;

    pub type Key = super::LspId;
}

pub mod uri_key {
    pub type T = super::DocumentUri;

    pub fn compare(super::document_uri::Uri(x): &T, super::document_uri::Uri(y): &T) -> isize {
        x.cmp(y) as isize
    }
}

/// `Stdlib.Set.Make (UriKey)`
pub mod uri_set {
    pub type T = im::OrdSet<super::DocumentUri>;
}

/// `Wrapped_map.Make (UriKey)`
pub mod uri_map {
    pub use crate::wrapped_map::*;

    pub type T<A> = im::OrdMap<super::DocumentUri, A>;

    pub type Key = super::DocumentUri;
}

pub fn lsp_result_to_log_string(r: &LspResult) -> String {
    use LspResult::*;
    match r {
        InitializeResult(_) => "InitializeResult",
        ShutdownResult => "ShutdownResult",
        CodeLensResolveResult(_) => "CodeLensResolveResult",
        HoverResult(_) => "HoverResult",
        DefinitionResult(_) => "DefinitionResult",
        TypeDefinitionResult(_) => "TypeDefinitionResult",
        ImplementationResult(_) => "ImplementationResult",
        CodeActionResult(_, _) => "CodeActionResult",
        CodeActionResolveResult(_) => "CodeActionResolveResult",
        CompletionResult(_) => "CompletionResult",
        CompletionItemResolveResult(_) => "CompletionItemResolveResult",
        WorkspaceSymbolResult(_) => "WorkspaceSymbolResult",
        DocumentSymbolResult(_) => "DocumentSymbolResult",
        FindReferencesResult(_) => "FindReferencesResult",
        PrepareCallHierarchyResult(_) => "PrepareCallHierarchyResult",
        CallHierarchyIncomingCallsResult(_) => "CallHierarchyIncomingCallsResult",
        CallHierarchyOutgoingCallsResult(_) => "CallHierarchyOutgoingCallsResult",
        DocumentHighlightResult(_) => "DocumentHighlightResult",
        DocumentFormattingResult(_) => "DocumentFormattingResult",
        DocumentRangeFormattingResult(_) => "DocumentRangeFormattingResult",
        DocumentOnTypeFormattingResult(_) => "DocumentOnTypeFormattingResult",
        ShowMessageRequestResult(_) => "ShowMessageRequestResult",
        ShowStatusResultFB(_) => "ShowStatusResultFB",
        RageResultFB(_) => "RageResultFB",
        RenameResult(_) => "RenameResult",
        DocumentCodeLensResult(_) => "DocumentCodeLensResult",
        SignatureHelpResult(_) => "SignatureHelpResult",
        HackTestStartServerResultFB => "HackTestStartServerResultFB",
        HackTestStopServerResultFB => "HackTestStopServerResultFB",
        HackTestShutdownServerlessResultFB => "HackTestShutdownServerlessResultFB",
        RegisterCapabilityRequestResult => "RegisterCapabilityRequestResult",
        WillSaveWaitUntilResult(_) => "WillSaveWaitUntilResult",
        TopLevelDefNameAtPosResult(_) => "TopLevelDefNameAtPosResult",
        ErrorResult(_) => "ErrorResult",
        AutoCloseResult(_) => "AutoCloseResult",
    }
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enums() {
        use symbol_information::*;
        assert_eq!(symbol_kind_to_enum(SymbolKind::File), 1);
        assert_eq!(symbol_kind_to_enum(SymbolKind::TypeParameter), 26);
        assert_eq!(symbol_kind_of_enum(13), Some(SymbolKind::Variable));
        assert_eq!(symbol_kind_of_enum(0), None);
        assert_eq!(symbol_kind_of_enum(27), None);
        use completion::*;
        assert_eq!(completion_item_kind_to_enum(CompletionItemKind::Text), 1);
        assert_eq!(completion_item_kind_to_enum(CompletionItemKind::TypeParameter), 25);
        assert_eq!(completion_item_kind_of_enum(14), Some(CompletionItemKind::Keyword));
        assert_eq!(error::code_to_enum(error::RequestCancelled), -32800);
        assert_eq!(error::code_of_enum(-32601), Some(error::MethodNotFound));
        assert_eq!(error::show_code(error::ServerErrorStart), "ServerErrorStart");
        assert_eq!(message_type::of_enum(4), Some(message_type::LogMessage));
    }

    #[test]
    fn code_action_kinds() {
        use code_action_kind::*;
        assert_eq!(kind_of_string("refactor.extract"), refactor_extract());
        assert_eq!(empty(), ("".to_string(), vec![]));
        assert!(is_kind(&refactor(), &refactor_extract()));
        assert!(!is_kind(&refactor_extract(), &refactor()));
        assert!(!is_kind(&quickfix(), &refactor()));
        assert!(contains_kind(&refactor(), &[quickfix(), refactor_inline()]));
        assert!(contains_kind_opt(true, &source(), None));
        assert!(!contains_kind_opt(true, &source(), Some(&[quickfix()])));
        assert_eq!(string_of_kind(&sub_kind(&refactor_extract(), "fn")), "refactor.extract.fn");
        assert_eq!(string_of_kind(&source_fix_all()), "source.fixAll");
    }

    #[test]
    fn ids_and_uris() {
        assert_eq!(id_key::compare(&NumberId(3), &NumberId(5)), -2);
        assert_eq!(id_key::compare(&NumberId(3), &StringId("a".to_string())), -1);
        assert!(NumberId(9) < StringId("".to_string()));
        assert!(StringId("a".to_string()) < StringId("b".to_string()));
        assert_eq!(string_of_uri(&uri_of_string("file:///a")), "file:///a");
        assert!(uri_key::compare(&uri_of_string("a"), &uri_of_string("b")) < 0);
        let reg = register_capability::make_registration(
            LspRegistrationOptions::DidChangeWatchedFilesRegistrationOptions(
                did_change_watched_files::RegisterOptions { watchers: vec![] },
            ),
        );
        assert_eq!(reg.id, "did-change-watched-files");
        assert_eq!(reg.method_, "workspace/didChangeWatchedFiles");
    }

    #[test]
    fn shows() {
        assert_eq!(
            show_marked_string(&MarkedString::MarkedString("a\"b".to_string())),
            "(Lsp.MarkedString \"a\\\"b\")"
        );
        assert_eq!(
            show_marked_string(&MarkedString::MarkedCode("hack".to_string(), "x".to_string())),
            "(Lsp.MarkedCode (\"hack\", \"x\"))"
        );
    }

    #[test]
    fn of_yojson() {
        let json = crate::yojson::safe::from_string(
            r#"{"textDocument": {"uri": "file:///x"}, "position": {"line": 1, "character": 2}}"#,
        )
        .unwrap();
        let p = top_level_def_name_at_pos::params_of_yojson(&json).unwrap();
        assert_eq!(p.text_document.uri, uri_of_string("file:///x"));
        assert_eq!(p.position, Position { line: 1, character: 2 });
        let bad = crate::yojson::safe::from_string(
            r#"{"textDocument": {"uri": "file:///x"}, "position": {"line": 1, "character": 2}, "x": 1}"#,
        )
        .unwrap();
        let error = top_level_def_name_at_pos::params_of_yojson(&bad).unwrap_err();
        assert_eq!(
            error.0,
            "hack/src/utils/lsp/lsp.ml.TextDocumentPositionParams.t_of_yojson: extra fields: x"
        );
        assert_eq!(
            top_level_def_name_at_pos::yojson_of_result(&Some("A".to_string())),
            yojson::T::String("A".to_string())
        );
    }
}
