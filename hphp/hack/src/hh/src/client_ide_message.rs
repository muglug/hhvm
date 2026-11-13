// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/client_ide_message.ml`.
//!
//! Owned by **G1** (plan §7.3).
//!
//! # The GADT `'a t`
//!
//! The OCaml request type is a GADT: each constructor fixes the type of its
//! response. Here the requests are one enum, [`T`] (what crosses to the IDE
//! thread, as the marshalled `'a t` crosses to the daemon process), and the
//! responses one enum, [`Response`], with one variant per response TYPE.
//! [`Request<A>`] is a [`T`] whose response has the type `A` (it can only be
//! made by the functions of [`request`], one per constructor, which give it
//! the type the OCaml constructor gives); [`IdeResult::of_response`] takes
//! the `A` out of the daemon's [`Response`] (the OCaml's `Obj.magic`, "safe
//! because if we pushed an 'a request then the daemon guarantees to return an
//! 'a"; here a mismatch is `None`, which the service reports as a desync).
//!
//! What has no counterpart: `daemon_args.shm_handle` (the daemon is a thread
//! of the process that runs `Client_lsp`: it shares its memory; plan §6 #35).

use std::marker::PhantomData;

use crate::autocomplete_types;
use crate::docblock_service;
use crate::file_content;
use crate::file_info::SiKind;
use crate::file_outline;
use crate::filter_diagnostics;
use crate::hover_service;
use crate::ide_api_types;
use crate::lsp;
use crate::path;
use crate::pos;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::search_types;
use crate::search_utils;
use crate::server_command_types;
use crate::server_rename_types;
use crate::symbol_definition;
use crate::user_diagnostic;
use crate::yojson::safe as yojson;

/// `Diagnostics.finalized_diagnostic`
pub type FinalizedDiagnostic = user_diagnostic::T<pos::Absolute, pos::Absolute>;

pub mod initialize_from_saved_state {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct NamingTableLoadInfo {
        pub path: path::T,
        /// artificial delay in seconds, for test purposes
        pub test_delay: f64,
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub root: path::T,
        pub naming_table_load_info: Option<NamingTableLoadInfo>,
        pub warnings_saved_state_path: Option<path::T>,
        pub config: Vec<(String, String)>,
        pub ignore_hh_version: bool,
        pub open_files: Vec<path::T>,
    }
}

pub mod completion_resolve {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Request {
        pub fullname: String,
        pub kind: SiKind,
    }

    #[derive(Clone, Debug, PartialEq)]
    pub struct Result {
        pub docblock: docblock_service::Result,
        pub signature: Option<String>,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Document {
    pub file_path: path::T,
    pub file_contents: String,
}

/// `fullname = Full_name of string`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fullname(pub String);

/// `Lsp.UriMap.t`
pub type UriMap<A> = lsp::document_uri::map::T<A>;

#[derive(Clone, Debug, PartialEq)]
pub enum FindRefsResult {
    InvalidSymbol,
    FindRefsSuccess {
        /// from [SymbolDefinition.full_name]
        full_name: String,
        /// if true, then clientLsp should shell out to hh_server to collect more positions;
        /// this action will specifiy what hh_server shoud look for.
        action: Option<server_command_types::find_refs::Action>,
        /// in case of a shell-out, we will suggest hh_server to look in these root-relative paths first.
        hint_suffixes: Vec<String>,
        /// All references that were found in all open files in clientIdeDaemon.
        open_file_results: UriMap<Vec<search_types::find_refs::Absolute>>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum RenameResult {
    NotRenameablePosition,
    RenameSuccess {
        shellout: Option<(
            symbol_definition::T<RelativePath>,
            server_command_types::find_refs::Action,
        )>,
        local: Vec<server_rename_types::Patch>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum GoToImplResult {
    InvalidSymbolImpl,
    GoToImplSuccess(
        String,
        server_command_types::find_refs::Action,
        UriMap<Vec<pos::Absolute>>,
    ),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompletionRequest {
    pub is_manually_invoked: bool,
}

/// Currently, a diagnostic is always an error with (optionally) a list
/// of locations where a "hint" should be displayed for that error.
#[derive(Clone, Debug, PartialEq)]
pub struct Diagnostic {
    pub diagnostic_error: FinalizedDiagnostic,
    pub diagnostic_hash: isize,
    /// Note that these will be displayed in the IDE, so this field
    /// only gets set when diagnostics are computed by clientIdeDaemon, and
    /// not when  they are computed by hh_server.
    ///
    /// This is fine because:
    /// (1) When a file is open in the IDE, we ignore hh_server signal
    /// (2) When a file is closed in the IDE, we use hh_server signal, but we
    ///     can't show hint locations anyways!
    pub diagnostic_related_hints: Vec<pos::Absolute>,
}

pub fn diagnostic_of_finalized_error_without_related_hints(
    (diagnostic_error, diagnostic_hash): (FinalizedDiagnostic, isize),
) -> Diagnostic {
    Diagnostic {
        diagnostic_error,
        diagnostic_related_hints: vec![],
        diagnostic_hash,
    }
}

/// `_ t`, the requests (see the module doc for how the GADT is kept).
#[derive(Clone, Debug)]
pub enum T {
    /// Invariant: the client sends no messages to the daemon before
    /// Initialize_from_state. And the daemon sends no messages before
    /// it has responded.
    InitializeFromSavedState(initialize_from_saved_state::T),
    Shutdown,
    /// This might include deleted files. The caller is responsible for filtering,
    /// and resolving symlinks (even resolving root symlink for a deleted file...)
    DidChangeWatchedFiles(relative_path::set::T),
    /// Lets ClientIdeDaemon know that the document is open, so we should start caching it.
    DidOpenOrChange(Document),
    /// Lets ClientIdeDaemon know the document is closed, so we no longer cache it.
    ///
    /// This returns diagnostics for the file as it is on disk.
    /// This is to serve the following scenario: (1) file was open with
    /// modified contents and squiggles appropriate to the modified contents,
    /// (2) user closes file without saving. In this scenario we must
    /// restore squiggles to what would be appropriate for the file on disk.
    /// It'd be possible to return an [Diagnostics.t option], and only return [Some]
    /// if the file had been closed while modified, if perf here is ever a concern.
    DidClose(path::T),
    /// Obtains latest diagnostics for file.
    Diagnostics(Document),
    VerboseToFile(bool),
    Hover(Document, file_content::position::T),
    Definition(Document, file_content::position::T),
    /// Handles "textDocument/completion" LSP messages
    Completion(Document, file_content::position::T, CompletionRequest),
    /// "completionItem/resolve" LSP messages - if we have file/line/column.
    /// The scenario is that VSCode requests textDocument/completion in A.PHP line 5 col 6,
    /// and we responded with a completion item that points to a class defined in B.PHP line 10 col 5,
    /// and now VSCode requests completionItem/resolve [(B.PHP, {line=10; column=5;}, class)],
    /// and this method will look up B.PHP to find the docblock for that class and return it.
    /// Typically B.PHP won't even be open. That's why we only provide it as Path.t
    CompletionResolveLocation(path::T, Fullname, file_content::position::T, SiKind),
    /// "completionItem/resolve" LSP messages - if we have symbol name, and [Completion_resolve_location] failed
    CompletionResolve(completion_resolve::Request),
    /// Handles "textDocument/documentHighlight" LSP messages
    DocumentHighlight(Document, file_content::position::T),
    /// Handles "textDocument/documentSymbol" LSP messages
    DocumentSymbol(Document),
    WorkspaceSymbol(String),
    GoToImplementation(Document, file_content::position::T, Vec<Document>),
    FindReferences(Document, file_content::position::T, Vec<Document>),
    /// The result of Rename is one of:
    ///  - Not_renameable_position, indicating an attempt to rename something that isn't a valid symbol
    ///  - Rename_success, where we return a record containing two fields:
    ///      - [shellout], an optional tuple of (SymbolDefinition.full_name * Find_refs.action)
    ///        to indicate that ClientIdeDaemon could not satisfy all of the rename (the non-localvar case)
    ///      - [local], a [Server_rename_types.patch list], a list of rename patches for each open file supplied
    ///       in the input document list
    Rename(Document, file_content::position::T, String, Vec<Document>),
    /// Handles "textDocument/typeDefinition" LSP messages
    TypeDefinition(Document, file_content::position::T),
    /// Handles "textDocument/signatureHelp" LSP messages
    SignatureHelp(Document, file_content::position::T),
    TopLevelDefNameAtPos(Document, file_content::position::T),
    /// Handles "textDocument/codeActions" LSP messages.
    ///
    /// Also, we take this as a handy opportunity to send updated [Diagnostics.t]
    /// to clientLsp so it can publish them. We return [None] if the TAST+errors
    /// haven't changed since they were last sent to clientLsp (through didOpen,
    /// didChange, didClose or an earlier codeAction), and [Some] if they have
    /// been changed.
    ///
    /// Why send errors in code-action? It's for the scenario where file A.PHP
    /// is open, file B.PHP changes on disk (e.g. due to user saving it), which
    /// invalidates the TAST+errors of A.PHP, and we might therefore need to send
    /// updated errors. For efficiency we chose to do this lazily when the user
    /// interacts with A.PHP or switches tab to it, rather than doing every single
    /// open file up-front. We could have sent updated errors on every single action,
    /// e.g. hover and go-to-def. But settled for now on only doing it for codeAction
    /// because this is called so frequently by VSCode (when you switch tab, and every
    /// time the caret moves) in the hope that this will be a good balance of simple
    /// code and decent experience.
    CodeAction(Document, ide_api_types::Range),
    CodeActionResolve {
        document: Document,
        range: ide_api_types::Range,
        resolve_title: String,
        use_snippet_edits: bool,
    },
    AutoClose(Document, file_content::position::T),
}

/// The responses, one variant per response type of the constructors of `'a t`.
#[derive(Clone, Debug)]
pub enum Response {
    /// `unit`: Initialize_from_saved_state, Shutdown, Did_change_watched_files,
    /// Did_open_or_change, Verbose_to_file
    Unit,
    /// `diagnostic list`: Did_close, Diagnostics
    Diagnostics(Vec<Diagnostic>),
    /// `Hover_service.result`
    Hover(hover_service::Result),
    /// `Server_command_types.Go_to_definition.result`
    Definition(server_command_types::go_to_definition::Result),
    /// `Autocomplete_types.ide_result`
    Completion(autocomplete_types::IdeResult),
    /// `Completion_resolve.result`: Completion_resolve_location, Completion_resolve
    CompletionResolve(completion_resolve::Result),
    /// `Ide_api_types.range list`
    DocumentHighlight(Vec<ide_api_types::Range>),
    /// `File_outline.outline`
    DocumentSymbol(file_outline::Outline),
    /// `Search_utils.result`
    WorkspaceSymbol(search_utils::Result),
    /// `go_to_impl_result`
    GoToImplementation(GoToImplResult),
    /// `find_refs_result`
    FindReferences(FindRefsResult),
    /// `rename_result`
    Rename(RenameResult),
    /// `Server_command_types.Go_to_type_definition.result`
    TypeDefinition(server_command_types::go_to_type_definition::Result),
    /// `Lsp.SignatureHelp.result`
    SignatureHelp(lsp::signature_help::Result),
    /// `string option`: Top_level_def_name_at_pos (`Lsp.TopLevelDefNameAtPos.result`), AutoClose
    OptionString(Option<String>),
    /// `Lsp.CodeAction.command_or_action list * Diagnostics.finalized_diagnostic list option`
    CodeAction(lsp::code_action::Result, Option<Vec<FinalizedDiagnostic>>),
    /// `Lsp.CodeActionResolve.result`
    CodeActionResolve(lsp::code_action_resolve::Result),
}

/// The type of a response, and how to take it out of a [`Response`].
pub trait IdeResult: Sized + Send + 'static {
    fn into_response(self) -> Response;
    fn of_response(response: Response) -> Option<Self>;
}

macro_rules! ide_result {
    ($ty:ty, $variant:ident) => {
        impl IdeResult for $ty {
            fn into_response(self) -> Response {
                Response::$variant(self)
            }
            fn of_response(response: Response) -> Option<Self> {
                match response {
                    Response::$variant(x) => Some(x),
                    _ => None,
                }
            }
        }
    };
}

impl IdeResult for () {
    fn into_response(self) -> Response {
        Response::Unit
    }
    fn of_response(response: Response) -> Option<Self> {
        match response {
            Response::Unit => Some(()),
            _ => None,
        }
    }
}

ide_result!(Vec<Diagnostic>, Diagnostics);
ide_result!(hover_service::Result, Hover);
ide_result!(server_command_types::go_to_definition::Result, Definition);
ide_result!(autocomplete_types::IdeResult, Completion);
ide_result!(completion_resolve::Result, CompletionResolve);
ide_result!(Vec<ide_api_types::Range>, DocumentHighlight);
ide_result!(file_outline::Outline, DocumentSymbol);
ide_result!(search_utils::Result, WorkspaceSymbol);
ide_result!(GoToImplResult, GoToImplementation);
ide_result!(FindRefsResult, FindReferences);
ide_result!(RenameResult, Rename);
ide_result!(server_command_types::go_to_type_definition::Result, TypeDefinition);
ide_result!(lsp::signature_help::Result, SignatureHelp);
ide_result!(Option<String>, OptionString);
ide_result!(lsp::code_action_resolve::Result, CodeActionResolve);

impl IdeResult for (lsp::code_action::Result, Option<Vec<FinalizedDiagnostic>>) {
    fn into_response(self) -> Response {
        Response::CodeAction(self.0, self.1)
    }
    fn of_response(response: Response) -> Option<Self> {
        match response {
            Response::CodeAction(actions, diagnostics) => Some((actions, diagnostics)),
            _ => None,
        }
    }
}

/// `'a t`: a request whose response has the type `A`. Made by the
/// functions of [`request`].
#[derive(Clone, Debug)]
pub struct Request<A> {
    pub message: T,
    result: PhantomData<fn() -> A>,
}

/// The constructors of `'a t`, each with the type of its response.
pub mod request {
    use super::*;

    fn make<A>(message: T) -> Request<A> {
        Request {
            message,
            result: PhantomData,
        }
    }

    pub fn initialize_from_saved_state(param: initialize_from_saved_state::T) -> Request<()> {
        make(T::InitializeFromSavedState(param))
    }
    pub fn shutdown() -> Request<()> {
        make(T::Shutdown)
    }
    pub fn did_change_watched_files(paths: relative_path::set::T) -> Request<()> {
        make(T::DidChangeWatchedFiles(paths))
    }
    pub fn did_open_or_change(document: Document) -> Request<()> {
        make(T::DidOpenOrChange(document))
    }
    pub fn did_close(file_path: path::T) -> Request<Vec<Diagnostic>> {
        make(T::DidClose(file_path))
    }
    pub fn diagnostics(document: Document) -> Request<Vec<Diagnostic>> {
        make(T::Diagnostics(document))
    }
    pub fn verbose_to_file(verbose: bool) -> Request<()> {
        make(T::VerboseToFile(verbose))
    }
    pub fn hover(document: Document, pos: file_content::position::T) -> Request<hover_service::Result> {
        make(T::Hover(document, pos))
    }
    pub fn definition(
        document: Document,
        pos: file_content::position::T,
    ) -> Request<server_command_types::go_to_definition::Result> {
        make(T::Definition(document, pos))
    }
    pub fn completion(
        document: Document,
        pos: file_content::position::T,
        req: CompletionRequest,
    ) -> Request<autocomplete_types::IdeResult> {
        make(T::Completion(document, pos, req))
    }
    pub fn completion_resolve_location(
        file_path: path::T,
        fullname: Fullname,
        pos: file_content::position::T,
        kind: SiKind,
    ) -> Request<completion_resolve::Result> {
        make(T::CompletionResolveLocation(file_path, fullname, pos, kind))
    }
    pub fn completion_resolve(req: completion_resolve::Request) -> Request<completion_resolve::Result> {
        make(T::CompletionResolve(req))
    }
    pub fn document_highlight(
        document: Document,
        pos: file_content::position::T,
    ) -> Request<Vec<ide_api_types::Range>> {
        make(T::DocumentHighlight(document, pos))
    }
    pub fn document_symbol(document: Document) -> Request<file_outline::Outline> {
        make(T::DocumentSymbol(document))
    }
    pub fn workspace_symbol(query: String) -> Request<search_utils::Result> {
        make(T::WorkspaceSymbol(query))
    }
    pub fn go_to_implementation(
        document: Document,
        pos: file_content::position::T,
        documents: Vec<Document>,
    ) -> Request<GoToImplResult> {
        make(T::GoToImplementation(document, pos, documents))
    }
    pub fn find_references(
        document: Document,
        pos: file_content::position::T,
        documents: Vec<Document>,
    ) -> Request<FindRefsResult> {
        make(T::FindReferences(document, pos, documents))
    }
    pub fn rename(
        document: Document,
        pos: file_content::position::T,
        new_name: String,
        documents: Vec<Document>,
    ) -> Request<RenameResult> {
        make(T::Rename(document, pos, new_name, documents))
    }
    pub fn type_definition(
        document: Document,
        pos: file_content::position::T,
    ) -> Request<server_command_types::go_to_type_definition::Result> {
        make(T::TypeDefinition(document, pos))
    }
    pub fn signature_help(
        document: Document,
        pos: file_content::position::T,
    ) -> Request<lsp::signature_help::Result> {
        make(T::SignatureHelp(document, pos))
    }
    pub fn top_level_def_name_at_pos(
        document: Document,
        pos: file_content::position::T,
    ) -> Request<lsp::top_level_def_name_at_pos::Result> {
        make(T::TopLevelDefNameAtPos(document, pos))
    }
    pub fn code_action(
        document: Document,
        range: ide_api_types::Range,
    ) -> Request<(lsp::code_action::Result, Option<Vec<FinalizedDiagnostic>>)> {
        make(T::CodeAction(document, range))
    }
    pub fn code_action_resolve(
        document: Document,
        range: ide_api_types::Range,
        resolve_title: String,
        use_snippet_edits: bool,
    ) -> Request<lsp::code_action_resolve::Result> {
        make(T::CodeActionResolve {
            document,
            range,
            resolve_title,
            use_snippet_edits,
        })
    }
    pub fn auto_close(document: Document, pos: file_content::position::T) -> Request<Option<String>> {
        make(T::AutoClose(document, pos))
    }
}

pub fn t_to_string(t: &T) -> String {
    match t {
        T::InitializeFromSavedState(_) => "Initialize_from_saved_state".to_string(),
        T::Shutdown => "Shutdown".to_string(),
        T::DidChangeWatchedFiles(paths) => {
            let paths: Vec<String> = paths.iter().map(relative_path::suffix).collect();
            let (files, remainder) = paths.split_at(paths.len().min(10));
            let remainder = if remainder.is_empty() { "" } else { ",..." };
            format!("Did_change_watched_files({}{})", files.concat(), remainder)
        }
        T::DidOpenOrChange(Document { file_path, .. }) => {
            format!("Did_open_or_change({})", path::to_string(file_path))
        }
        T::DidClose(file_path) => format!("Ide_file_closed({})", path::to_string(file_path)),
        T::Diagnostics(Document { file_path, .. }) => {
            format!("Diagnostics({})", path::to_string(file_path))
        }
        T::VerboseToFile(verbose) => format!("Verbose_to_file({})", verbose),
        T::Hover(Document { file_path, .. }, _) => format!("Hover({})", path::to_string(file_path)),
        T::Definition(Document { file_path, .. }, _) => {
            format!("Definition({})", path::to_string(file_path))
        }
        T::Completion(Document { file_path, .. }, _, _) => {
            format!("Completion({})", path::to_string(file_path))
        }
        T::CompletionResolve(completion_resolve::Request { fullname, kind: _ }) => {
            format!("Completion_resolve({})", fullname)
        }
        T::CompletionResolveLocation(file_path, _, _, _) => {
            format!("Completion_resolve_location({})", path::to_string(file_path))
        }
        T::DocumentHighlight(Document { file_path, .. }, _) => {
            format!("Document_highlight({})", path::to_string(file_path))
        }
        T::DocumentSymbol(Document { file_path, .. }) => {
            format!("Document_symbol({})", path::to_string(file_path))
        }
        T::WorkspaceSymbol(query) => format!("Workspace_symbol({})", query),
        T::TypeDefinition(Document { file_path, .. }, _) => {
            format!("Type_definition({})", path::to_string(file_path))
        }
        T::SignatureHelp(Document { file_path, .. }, _) => {
            format!("Signature_help({})", path::to_string(file_path))
        }
        T::TopLevelDefNameAtPos(Document { file_path, .. }, _) => {
            format!("Top_level_def_name_at_pos({})", path::to_string(file_path))
        }
        T::CodeAction(Document { file_path, .. }, _) => {
            format!("Code_action({})", path::to_string(file_path))
        }
        T::CodeActionResolve {
            document: Document { file_path, .. },
            resolve_title,
            ..
        } => format!(
            "Code_action_resolve({}, {})",
            path::to_string(file_path),
            resolve_title
        ),
        T::GoToImplementation(Document { file_path, .. }, _, _) => {
            format!("Go_to_implementation({})", path::to_string(file_path))
        }
        T::FindReferences(Document { file_path, .. }, _, _) => {
            format!("Find_references({})", path::to_string(file_path))
        }
        T::Rename(Document { file_path, .. }, _, _, _) => {
            format!("Rename({})", path::to_string(file_path))
        }
        T::AutoClose(Document { file_path, .. }, _) => {
            format!("AutoClose({})", path::to_string(file_path))
        }
    }
}

/// `'a tracked_t`
#[derive(Clone, Debug)]
pub struct TrackedT {
    pub tracking_id: String,
    pub message: T,
}

pub fn tracked_t_to_string(TrackedT { tracking_id, message }: &TrackedT) -> String {
    format!("#{}: {}", tracking_id, t_to_string(message))
}

pub mod processing_files {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct T {
        pub processed: isize,
        pub total: isize,
    }

    pub fn to_string(t: &T) -> String {
        format!("{}/{}", t.processed, t.total)
    }
}

/// This can be used for user-facing messages as well as LSP error responses.
#[derive(Clone, Debug, PartialEq)]
pub struct RichError {
    /// max 20 chars, for status bar. Will be prepended by "Hack:"
    pub short_user_message: String,
    /// max 10 words, for tooltip and alert. Will be postpended by " See <log>"
    pub medium_user_message: String,
    /// used to decide if we hould show window/showMessage, i.e. an alert
    pub is_actionable: bool,
    /// max 5 lines, for window/logMessage, i.e. Output>Hack window. Will be postpended by "\nDetails: <url>"
    pub long_user_message: String,
    /// used in LSP Error message and telemetry
    pub category: String,
    /// used in LSP Error message and telemetry
    pub data: Option<yojson::T>,
}

/// `notification`
#[derive(Clone, Debug, PartialEq)]
pub enum Notification {
    DoneInit(Result<(), RichError>),
}

pub fn notification_to_string(n: &Notification) -> String {
    match n {
        Notification::DoneInit(Ok(())) => "Done_init.".to_string(),
        Notification::DoneInit(Err(edata)) => {
            format!("Done_init failed - {}", edata.medium_user_message)
        }
    }
}

/// `'a timed_response`
#[derive(Clone, Debug)]
pub struct TimedResponse {
    pub unblocked_time: f64,
    pub tracking_id: String,
    pub response: Result<Response, lsp::error::T>,
}

#[derive(Clone, Debug)]
pub enum MessageFromDaemon {
    Notification(Notification),
    Response(TimedResponse),
}

pub fn message_from_daemon_to_string(m: &MessageFromDaemon) -> String {
    match m {
        MessageFromDaemon::Notification(n) => notification_to_string(n),
        MessageFromDaemon::Response(TimedResponse {
            response: Err(lsp::error::T { message, .. }),
            tracking_id,
            ..
        }) => format!("#{}: Response_error({})", tracking_id, message),
        MessageFromDaemon::Response(TimedResponse {
            response: Ok(_),
            tracking_id,
            ..
        }) => format!("#{}: Response_ok", tracking_id),
    }
}

/// `daemon_args` (without `shm_handle`: see the module doc).
#[derive(Clone, Debug)]
pub struct DaemonArgs {
    pub init_id: String,
    pub verbose_to_stderr: bool,
    pub verbose_to_file: bool,
    pub client_lsp_log_fn: String,
    pub error_filter: filter_diagnostics::filter::T,
}

/// Everything that crosses to and from the IDE thread is `Send`.
const _: fn() = || {
    fn send<A: Send>() {}
    send::<TrackedT>();
    send::<MessageFromDaemon>();
};
