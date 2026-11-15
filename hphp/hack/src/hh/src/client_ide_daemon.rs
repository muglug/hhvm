// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/client_ide_daemon.ml`.
//!
//! The daemon is a thread of `hh_client lsp` here, not a process:
//! [`daemon_main`] runs on the thread `Client_ide_service.make`
//! starts, with the requests and responses on channels instead of pipes, its
//! own `Hh_logger` state (`.client_ide_log`; its stderr is the LSP log file,
//! as `Daemon.spawn` gives the OCaml daemon), and the `Local_memory` backend
//! (`crate::provider_backend`). The Lwt threads of `serve` (`pump_stdin`,
//! `handle_messages`, `flush_event_logger`) are: a thread that reads the
//! input and pushes onto the message queue, the daemon's thread, which
//! handles the queue; `flush_event_logger` (the event logger: no-op in the
//! open-source build) has no counterpart. The asynchronous part of the init
//! (`Client_ide_init.init`, `Lwt.async`) runs on a thread of its own and
//! posts `GotNamingTable` on the queue, as the OCaml does.
//!
//! `Hack_event_logger` calls are no-ops in the open-source build: omitted.
//! The OCaml's exceptions are panics here: a request whose handling panics
//! answers the error the OCaml's `with exn` gives, and the panic is not
//! printed (the OCaml prints nothing either).

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::mpsc;

use crate::client_ide_init;
use crate::client_ide_message;
use crate::client_ide_message::Document;
use crate::client_ide_message::MessageFromDaemon;
use crate::client_ide_message::Response;
use crate::client_ide_message::RichError;
use crate::client_ide_message::T as M;
use crate::client_ide_message::TrackedT;
use crate::client_ide_utils;
use crate::diagnostics;
use crate::exception;
use crate::file_outline;
use crate::hh_logger;
use crate::lsp;
use crate::lsp_helpers;
use crate::lwt_message_queue;
use crate::naming_table;
use crate::path;
use crate::provider_backend::LocalMemory;
use crate::provider_context;
use crate::provider_context::Entry;
use crate::provider_context::EntryContents;
use crate::provider_utils;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::search_utils;
use crate::server_command_types::find_refs::Action;
use crate::server_config;
use crate::server_local_config;
use crate::tast_provider;
use crate::user_diagnostic;
use crate::yojson::safe as yojson;

// ---------------------------------------------------------------------------
// Debugging activities
// ---------------------------------------------------------------------------

thread_local! {
    /// For debugging. When we get to [at_exit], we'll log what the current activities are.
    /// (A global of the OCaml process: one per daemon thread here.)
    static DBG_CURRENT_ACTIVITIES: RefCell<BTreeMap<String, Vec<String>>> =
        const { RefCell::new(BTreeMap::new()) };
}

/// Each activity key is associated with up to five most recent timestamped activity values
/// under that key.
fn dbg_set_activity(key: &str, value: &str) {
    DBG_CURRENT_ACTIVITIES.with_borrow_mut(|activities| {
        let history = activities.get(key).cloned().unwrap_or_default();
        let mut new_history = vec![format!(
            "  {} {}",
            crate::utils::timestring(crate::rt::ocaml_unix::gettimeofday()),
            value
        )];
        new_history.extend(history.into_iter().take(4));
        activities.insert(key.to_string(), new_history);
    })
}

/// This prints a multiline string: for each activity key, the most recent activity values for that key.
fn dbg_dump_activity() -> String {
    DBG_CURRENT_ACTIVITIES.with_borrow(|activities| {
        activities
            .iter()
            .map(|(key, history)| {
                let mut lines = vec![key.clone()];
                lines.extend(history.iter().rev().cloned());
                lines.join("\n")
            })
            .collect::<Vec<_>>()
            .join("\n")
    })
}

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// These are messages on Client_ide_daemon's internal message-queue
enum Message {
    /// ClientRequest came from Client_ide_service over stdin;
    /// it expects a response.
    ClientRequest(TrackedT),
    CommitTransitionChanges(relative_path::set::T),
    /// GotNamingTable is posted from within Client_ide_daemon itself once
    /// our attempt at loading saved-state has finished; it's picked
    /// up by handle_messages.
    GotNamingTable(Result<client_ide_init::InitResult, RichError>),
}

type MessageQueue = lwt_message_queue::T<Message>;

/// `Outfd_write_error of string * string`
#[derive(Debug)]
pub(crate) struct OutfdWriteError(String, String);

impl std::fmt::Display for OutfdWriteError {
    /// `Printexc.to_string (Outfd_write_error (fn, param))`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Client_ide_daemon.Outfd_write_error({:?}, {:?})", self.0, self.1)
    }
}

#[derive(Clone)]
struct CommonState {
    /// hhi_root files are written during initialize, deleted at shutdown, and
    /// refreshed periodically in case the tmp-cleaner has deleted them.
    hhi_root: path::T,
    config: server_config::T,
    local_config: server_local_config::T,
    /// Local_memory backend; includes decl caches
    local_memory: Arc<LocalMemory>,
    /// The context without entries over the backend (`make_empty_ctx`).
    ctx: provider_context::T,
}

/// The identity of a `Diagnostics.t` (what `phys_equal` compares): the
/// entry it was computed for and the computation (see
/// [`get_user_facing_errors`]).
type DiagnosticsIdentity = (usize, u64);

#[derive(Clone)]
struct OpenFileState {
    entry: Arc<Entry>,
    diagnostics: Rc<RefCell<Option<DiagnosticsIdentity>>>,
}

/// The [entry] caches the TAST+diagnostics; the [Diagnostics.t option] stores what was
/// the most recent version of the diagnostics to have been returned to clientLsp
/// by didOpen/didChange/didClose/codeAction.
type OpenFilesState = relative_path::map::T<OpenFileState>;

/// istate, "initialized state", is the state the daemon after it has
/// finished initialization (i.e. finished loading saved state). (See the
/// OCaml for the invariants of the naming tables, entries and caches.)
#[derive(Clone)]
pub struct IState {
    icommon: CommonState,
    iopen_files: OpenFilesState,
    /// the forward-naming-table is constructed during initialize and updated
    /// during process_changed_files. It stores an in-memory map of FileInfos that
    /// have changed since sqlite. When a file is changed on disk, we need this to
    /// know which shallow decls to invalidate. Note: while the forward-naming-table
    /// is stored here, the reverse-naming-table is instead stored in ctx.
    naming_table: naming_table::T,
    error_filter: tast_provider::ErrorFilter,
    /// sienv provides autocomplete and find-symbols. It is constructed during
    /// initialize and updated during process_changed_files. It stores a few
    /// in-memory structures such as namespace-list, plus in-memory deltas.
    sienv: search_utils::SiEnv,
}

/// dstate, "during_init state", is the state the daemon after it has received an
/// init message (and has parsed config files to get popt/tcopt, has initialized
/// glean, as written out hhi files) but before it has loaded saved-state or processed
/// file updates.
#[derive(Clone)]
struct DState {
    /// When did we kick off the attempt to load saved-state?
    start_time: f64,
    dcommon: CommonState,
    dopen_files: OpenFilesState,
    /// [changed_files_to_process] is grown [During_init] upon [Did_change_watched_files changes]
    /// and then discharged in [initialize2] before changing to [Initialized] state.
    changed_files_to_process: relative_path::set::T,
}

/// `show_dstate` (`[@@deriving show]`, the opaque fields as `<opaque>`).
fn show_dstate(dstate: &DState) -> String {
    let changed = if dstate.changed_files_to_process.is_empty() {
        "{}".to_string()
    } else {
        format!(
            "{{{}}}",
            dstate
                .changed_files_to_process
                .iter()
                .map(|p| format!("{:?}", relative_path::to_absolute(p)))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    format!(
        "{{ Client_ide_daemon.start_time = {};\n  dcommon =\n  {{ Client_ide_daemon.hhi_root =\n    {:?}; config = <opaque>;\n    local_config = <opaque>; local_memory = <opaque> }};\n  dopen_files = <opaque>; changed_files_to_process = {} }}",
        crate::rt::ocaml_stdlib::string_of_float(dstate.start_time),
        path::to_string(&dstate.dcommon.hhi_root),
        changed
    )
}

#[derive(Clone)]
enum State {
    /// We haven't yet received init request
    PendingInit,
    /// We're working on the init request. We're still in
    /// the process of loading the saved state.
    DuringInit(DState),
    /// Finished work on init request.
    Initialized(IState),
    /// Failed request, with root cause
    FailedInit(RichError),
}

fn state_to_log_string(state: &State) -> String {
    let open_files_to_log_string = |open_files: &OpenFilesState| format!("{} open_files", open_files.len());
    match state {
        State::PendingInit => "Pending_init".to_string(),
        State::DuringInit(DState {
            dopen_files,
            changed_files_to_process,
            ..
        }) => format!(
            "During_init({}, {} changed during)",
            open_files_to_log_string(dopen_files),
            changed_files_to_process.len()
        ),
        State::Initialized(IState { iopen_files, .. }) => {
            format!("Initialized({})", open_files_to_log_string(iopen_files))
        }
        State::FailedInit(reason) => format!("Failed_init({})", reason.category),
    }
}

fn log(s: &str) {
    hh_logger::log(&format!("[ide-daemon] {}", s))
}

fn log_debug(s: &str) {
    hh_logger::debug(None, None, &format!("[ide-daemon] {}", s))
}

fn set_up_hh_logger_for_client_ide_service(root: &path::T) {
    // Log to a file on disk. Note that calls to `Hh_logger` will always write to
    // `stderr`; this is in addition to that.
    let client_ide_log_fn = crate::server_files::client_ide_log(root);
    let _ = std::fs::rename(&client_ide_log_fn, format!("{}.old", client_ide_log_fn));
    hh_logger::set_log(&client_ide_log_fn);
    log(&format!("Starting client IDE service at {}", client_ide_log_fn));
}

/// The daemon's output (`out_fd`).
type OutFd = mpsc::Sender<MessageFromDaemon>;

fn write_message(out_fd: &OutFd, message: MessageFromDaemon) {
    if out_fd.send(message).is_err() {
        // `Unix.Unix_error (Unix.EPIPE, fn, param)`
        std::panic::panic_any(OutfdWriteError("write".to_string(), "".to_string()))
    }
}

fn log_startup_time(component: &str, start_time: f64) -> f64 {
    let _ = component;
    // (`Hack_event_logger.serverless_ide_startup ?count ~start_time component`: no-op.)
    let _ = start_time;
    crate::rt::ocaml_unix::gettimeofday()
}

fn restore_hhi_root_if_necessary(istate: IState) -> IState {
    if std::path::Path::new(&path::to_string(&istate.icommon.hhi_root)).exists() {
        istate
    } else {
        // Some processes may clean up the temporary HHI directory we're using.
        // Assume that such a process has deleted the directory, and re-write the HHI
        // files to disk.
        let hhi_root = crate::hhi_root::get_hhi_root(true);
        log(&format!(
            "Old hhi root {} no longer exists. Creating a new hhi root at {}",
            path::to_string(&istate.icommon.hhi_root),
            path::to_string(&hhi_root)
        ));
        relative_path::set_path_prefix(
            relative_path::Prefix::Hhi,
            std::path::Path::new(&path::to_string(&hhi_root)),
        );
        IState {
            icommon: CommonState {
                hhi_root,
                ..istate.icommon.clone()
            },
            ..istate
        }
    }
}

/// Deletes the hhi files we've created.
fn remove_hhi(state: &State) {
    match state {
        State::PendingInit | State::FailedInit(_) => {}
        State::DuringInit(DState {
            dcommon: CommonState { hhi_root, .. },
            ..
        })
        | State::Initialized(IState {
            icommon: CommonState { hhi_root, .. },
            ..
        }) => {
            let hhi_root = path::to_string(hhi_root);
            log(&format!("Removing hhi directory {}...", hhi_root));
            if let Err(err) = std::fs::remove_dir_all(&hhi_root) {
                let e = exception::wrap(format!("Sys_error(\"{}: {}\")", hhi_root, err));
                client_ide_utils::log_bug(None, Some(&e), true, "remove_hhi");
            }
        }
    }
}

fn entries_of_open_files(open_files: &OpenFilesState) -> provider_context::Entries {
    open_files
        .iter()
        .map(|(path, OpenFileState { entry, .. })| (path.clone(), Arc::clone(entry)))
        .collect()
}

/// `batch_trigger`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BatchTrigger {
    Initialization,
    LspFileChanges,
    CommitTransition,
    TestIndex,
}

/// `show_batch_trigger` (`[@@deriving show { with_path = false }]`)
fn show_batch_trigger(trigger: BatchTrigger) -> &'static str {
    match trigger {
        BatchTrigger::Initialization => "Initialization",
        BatchTrigger::LspFileChanges => "Lsp_file_changes",
        BatchTrigger::CommitTransition => "Commit_transition",
        BatchTrigger::TestIndex => "Test_index",
    }
}

/// Helper called to process a batch of file changes.
/// Updates the naming table, and invalidates the decl and tast caches for the changes.
fn batch_update_naming_table_and_invalidate_caches(
    trigger: BatchTrigger,
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    sienv: &search_utils::SiEnv,
    local_memory: &Arc<LocalMemory>,
    open_files: &OpenFilesState,
    changes: &relative_path::set::T,
) -> (naming_table::T, search_utils::SiEnv) {
    let crate::client_ide_incremental::UpdateResult {
        changes,
        naming_table,
        sienv,
    } = crate::client_ide_incremental::update_naming_tables_and_si(ctx, naming_table, sienv, changes);
    let _telemetry = crate::telemetry::string_(
        None,
        "trigger",
        show_batch_trigger(trigger),
        provider_utils::invalidate_upon_file_changes(
            ctx,
            local_memory,
            &changes,
            &entries_of_open_files(open_files),
        ),
    );
    // (`Hack_event_logger.ProfileTypeCheck.invalidate`: no-op.)
    (naming_table, sienv)
}

/// An empty ctx with no entries
fn make_empty_ctx(common: &CommonState) -> provider_context::T {
    Arc::clone(&common.ctx)
}

fn process_changed_files(
    trigger: BatchTrigger,
    state: State,
    changes: &relative_path::set::T,
) -> State {
    match state {
        State::DuringInit(dstate) => {
            let changed_files_to_process =
                dstate.changed_files_to_process.clone().union(changes.clone());
            State::DuringInit(DState {
                changed_files_to_process,
                ..dstate
            })
        }
        State::Initialized(istate) => {
            let (naming_table, sienv) = batch_update_naming_table_and_invalidate_caches(
                trigger,
                &make_empty_ctx(&istate.icommon),
                &istate.naming_table,
                &istate.sienv,
                &istate.icommon.local_memory,
                &istate.iopen_files,
                changes,
            );
            State::Initialized(IState {
                naming_table,
                sienv,
                ..istate
            })
        }
        State::PendingInit | State::FailedInit(_) => state,
    }
}

/// Constructs a temporary ctx with just one entry.
fn make_singleton_ctx(common: &CommonState, entry: &Arc<Entry>) -> provider_context::T {
    let ctx = make_empty_ctx(common);
    provider_context::add_or_overwrite_entry(&ctx, Arc::clone(entry))
}

/// `Provider_context.empty_for_tool ~popt ~tcopt ~backend:(Local_memory ..)
/// ~deps_mode:(InMemoryMode None)`: the context of the daemon, whose stores
/// are its `Local_memory` backend. The hhi files are those of the binary.
fn make_local_memory_ctx(
    config: &server_config::T,
    root: &path::T,
    sizes: Option<(usize, usize, usize)>,
) -> (provider_context::T, Arc<LocalMemory>) {
    let tcopt = server_config::typechecker_options(config);
    let popt = server_config::parser_options(config);
    let mut ctx = match crate::ctx::Ctx::new(std::path::Path::new(root), tcopt) {
        Ok(ctx) => ctx,
        Err(err) => panic!("Provider_context: cannot make a context: {}", err),
    };
    ctx.decl_parser = decl_parser::DeclParser::new(
        Arc::clone(&ctx.files) as Arc<dyn ::file_provider::FileProvider>,
        oxidized::decl_parser_options::DeclParserOptions::from_parser_options(&popt),
    );
    ctx.parser_env.parser_options = popt;
    ctx.deps_mode = crate::typing_deps::mode::T::InMemoryMode(None);
    let deps_mode = ctx.deps_mode.clone();
    let lm = match sizes {
        Some((max_num_decls, max_num_folded_class_decls, max_num_shallow_class_decls)) => {
            crate::provider_backend::set_local_memory_backend(
                max_num_decls,
                max_num_folded_class_decls,
                max_num_shallow_class_decls,
                deps_mode,
            )
        }
        // `set_local_memory_backend_with_defaults_for_test`
        None => crate::provider_backend::make_local_memory(5000, 5000, 20000, deps_mode),
    };
    // (`Ctx::new_local_memory`, with the parser options of the config,
    // which `empty_for_tool` gives the context.)
    ctx.install_local_memory(lm);
    let ctx = Arc::new(ctx);
    let local_memory = Arc::clone(ctx.local_memory().unwrap());
    // `Provider_backend.set_local_memory_backend` also sets the decl store
    // (`Decl_store.set (make_decl_store_from_local_memory ..)`).
    crate::hh_single_type_check::install(&ctx);
    (ctx, local_memory)
}

/// Initializes:
///  - HackEventLogger and Hh_logger
///  - Root, hhi and tmp paths
///  - Load configs
///  - Local memory for the provider backend
fn initialize1(param: &client_ide_message::initialize_from_saved_state::T) -> DState {
    let client_ide_message::initialize_from_saved_state::T {
        root,
        config,
        open_files,
        naming_table_load_info: _,
        warnings_saved_state_path: _,
        ignore_hh_version: _,
    } = param;
    log_debug("initialize1");
    let start_time = crate::rt::ocaml_unix::gettimeofday();
    set_up_hh_logger_for_client_ide_service(root);

    relative_path::set_path_prefix(relative_path::Prefix::Root, std::path::Path::new(root));
    let hhi_root = crate::hhi_root::get_hhi_root(false);
    log(&format!(
        "Extracted hhi files to directory {}",
        path::to_string(&hhi_root)
    ));
    relative_path::set_path_prefix(
        relative_path::Prefix::Hhi,
        std::path::Path::new(&path::to_string(&hhi_root)),
    );
    relative_path::set_path_prefix(relative_path::Prefix::Tmp, std::path::Path::new("/tmp"));

    let (config, local_config) = match server_config::load(true, "", config) {
        Ok(configs) => configs,
        Err(err) => panic!("{:?}", err),
    };

    let (ctx, local_memory) = make_local_memory_ctx(&config, root, Some((5000, 5000, 20000)));

    // We only ever serve requests on files that are open. That's why our caller
    // passes an initial list of open files, the ones already open in the editor
    // at the time we were launched. We don't actually care about their contents
    // at this stage, since updated contents will be delivered upon each request.
    // (and indeed it's pointless to waste time reading existing contents off disk).
    // All we care is that every open file is listed in 'open_files'.
    let dopen_files: OpenFilesState = open_files
        .iter()
        .map(|path| relative_path::create_detect_prefix(&path::to_string(path)))
        .map(|path| {
            (
                path.clone(),
                OpenFileState {
                    entry: provider_context::make_entry(path, EntryContents::RaiseExnOnAttemptToRead),
                    diagnostics: Rc::new(RefCell::new(None)),
                },
            )
        })
        .collect();
    let start_time = log_startup_time("initialize1", start_time);
    log_debug("initialize1.done");
    DState {
        start_time,
        dcommon: CommonState {
            hhi_root,
            config,
            local_config,
            local_memory,
            ctx,
        },
        dopen_files,
        changed_files_to_process: Default::default(),
    }
}

/// initialize2 is called by handle_one_message upon receipt of a
/// [GotNamingTable] message. It sends the appropriate message on to the
/// client, and transitions into either [Initialized] or [Failed_init]
/// state.
fn initialize2(
    out_fd: &OutFd,
    dstate: DState,
    error_filter: &crate::filter_diagnostics::filter::T,
    init_result: Result<client_ide_init::InitResult, RichError>,
) -> State {
    let start_time = log_startup_time("load_naming_table", dstate.start_time);
    log_debug("initialize2");
    match init_result {
        Ok(client_ide_init::InitResult {
            naming_table,
            warnings_saved_state,
            sienv,
            changed_files,
        }) => {
            let changed_files_to_process: relative_path::set::T = dstate
                .changed_files_to_process
                .clone()
                .union(changed_files.into_iter().collect())
                .into_iter()
                .filter(crate::find_utils::path_filter)
                .collect();
            let (naming_table, sienv) = batch_update_naming_table_and_invalidate_caches(
                BatchTrigger::Initialization,
                &make_empty_ctx(&dstate.dcommon),
                &naming_table,
                &sienv,
                &dstate.dcommon.local_memory,
                &dstate.dopen_files,
                &changed_files_to_process,
            );
            let istate = IState {
                naming_table,
                error_filter: tast_provider::ErrorFilter {
                    warnings_saved_state,
                    error_filter: error_filter.clone(),
                },
                sienv,
                icommon: dstate.dcommon,
                iopen_files: dstate.dopen_files,
            };
            // Note: Done_init is needed to (1) transition clientIdeService state, (2) cause
            // clientLsp to know to ask for squiggles to be refreshed on open files.
            write_message(
                out_fd,
                MessageFromDaemon::Notification(client_ide_message::Notification::DoneInit(Ok(()))),
            );
            let _count = changed_files_to_process.len();
            let _: f64 = log_startup_time("initialize2", start_time);
            log_debug("initialize2.done");
            State::Initialized(istate)
        }
        Err(reason) => {
            log_debug("initialize2.error");
            write_message(
                out_fd,
                MessageFromDaemon::Notification(client_ide_message::Notification::DoneInit(Err(
                    reason.clone(),
                ))),
            );
            remove_hhi(&State::DuringInit(dstate));
            State::FailedInit(reason)
        }
    }
}

/// This funtion is about papering over a bug. Sometimes, rarely, we're
/// failing to receive DidOpen messages from clientLsp. Our model is to
/// only ever answer IDE requests on open files, so we know we'll eventually
/// reveive a DidClose even for them and be able to clear their TAST cache
/// at that time. But for now, to paper over the bug, we'll call this
/// function to log the event and we'll assume that we just missed a DidOpen.
fn log_missing_open_file_bug(reason: &str, path: &RelativePath) {
    let path = relative_path::to_absolute(path);
    let message = format!("Error: action on non-open file [{}] {}", reason, path);
    client_ide_utils::log_bug(None, None, true, &message);
}

/// Registers the file in response to DidOpen or DidChange,
/// during the During_init state, by putting in a new
/// entry in open_files, with empty AST and TAST. If the LSP client
/// happened to send us two DidOpens for a file, or DidChange before DidOpen,
/// well, we won't complain.
fn open_or_change_file_during_init(dstate: DState, path: RelativePath, contents: &str) -> DState {
    let entry = provider_context::make_entry(
        path.clone(),
        EntryContents::ProvidedContents(contents.into()),
    );
    let dopen_files = dstate.dopen_files.update(
        path,
        OpenFileState {
            entry,
            diagnostics: Rc::new(RefCell::new(None)),
        },
    );
    DState {
        dopen_files,
        ..dstate
    }
}

/// Closes a file, in response to DidClose event, by removing the
/// entry in open_files. If the LSP client sents us multile DidCloses,
/// or DidClose for an unopen file, we won't complain.
fn close_file(open_files: &OpenFilesState, path: &RelativePath) -> OpenFilesState {
    if !open_files.contains_key(path) {
        log_missing_open_file_bug("close-without-open", path);
    }
    open_files.without(path)
}

/// Updates an existing opened file, with new contents; if the
/// contents haven't changed then the existing open file's AST and TAST
/// will be left intact.
fn update_file(
    open_files: &OpenFilesState,
    document: &Document,
) -> (
    OpenFilesState,
    Arc<Entry>,
    Rc<RefCell<Option<DiagnosticsIdentity>>>,
) {
    let path = relative_path::create_detect_prefix(&path::to_string(&document.file_path));
    let contents = &document.file_contents;
    let (entry, prev_diagnostics) = match open_files.get(&path) {
        None => {
            // This is a common scenario although I'm not quite sure why
            (
                provider_context::make_entry(
                    path.clone(),
                    EntryContents::ProvidedContents(contents.as_str().into()),
                ),
                Rc::new(RefCell::new(None)),
            )
        }
        Some(OpenFileState { entry, diagnostics })
            if provider_context::get_file_contents_if_present(entry)
                .as_ref()
                .map(|c| c.as_slice())
                == Some(contents.as_bytes()) =>
        {
            // we can just re-use the existing entry; contents haven't changed
            (Arc::clone(entry), Rc::clone(diagnostics))
        }
        Some(_) => {
            // We'll create a new entry; existing entry caches, if present, will be dropped
            // But first, need to clear the Fixme cache. This is a global cache
            // which is updated as a side-effect of the Ast_provider.
            crate::fixme_provider::remove_batch(&std::iter::once(path.clone()).collect());
            (
                provider_context::make_entry(
                    path.clone(),
                    EntryContents::ProvidedContents(contents.as_str().into()),
                ),
                Rc::new(RefCell::new(None)),
            )
        }
    };
    let open_files = open_files.update(
        path,
        OpenFileState {
            entry: Arc::clone(&entry),
            diagnostics: Rc::clone(&prev_diagnostics),
        },
    );
    (open_files, entry, prev_diagnostics)
}

/// like [update_file], but for convenience also produces a ctx for
/// use in typechecking. Also ensures that hhi files haven't been deleted
/// by tmp_cleaner, so that type-checking will succeed.
fn update_file_ctx(
    istate: IState,
    document: &Document,
) -> (
    IState,
    provider_context::T,
    Arc<Entry>,
    Rc<RefCell<Option<DiagnosticsIdentity>>>,
) {
    let istate = restore_hhi_root_if_necessary(istate);
    let (iopen_files, entry, published_errors) = update_file(&istate.iopen_files, document);
    let ctx = make_singleton_ctx(&istate.icommon, &entry);
    (IState { iopen_files, ..istate }, ctx, entry, published_errors)
}

/// We avoid showing typing errors if there are parsing errors.
///
/// Also gives the identity of the result (what `phys_equal` tells apart in
/// `Code_action`): the AST errors of an entry are computed once; its TAST
/// errors are the value stored in the entry, whose identity is
/// `Entry::all_diagnostics_generation`.
fn get_user_facing_errors(
    ctx: &provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
    entry: &Arc<Entry>,
) -> (diagnostics::T, DiagnosticsIdentity) {
    let (_, ast_errors) =
        crate::ast_provider::compute_parser_return_and_ast_errors(provider_context::get_popt(ctx), entry);
    let entry_id = Arc::as_ptr(entry) as usize;
    if diagnostics::has_no_errors(None, &ast_errors) {
        let tast_provider::ComputeTastAndErrors {
            diagnostics: all_errors,
            ..
        } = tast_provider::compute_tast_and_errors_quarantined(ctx, entry, error_filter);
        // The errors stored in the entry, by whoever computed them last (a
        // code action computes the TAST too): their identity changes with
        // every new computation, as the OCaml value's.
        let id = entry
            .all_diagnostics_generation
            .load(std::sync::atomic::Ordering::Relaxed);
        (all_errors, (entry_id, id))
    } else {
        (ast_errors, (entry_id, 0))
    }
}

/// Computes the Diagnostics.t for what's on disk at a given path.
/// We provide [istate] just in case we can benefit from a cached answer.
fn get_diagnostics_for_path(istate: &IState, path: &RelativePath) -> diagnostics::T {
    let disk_content_opt = std::fs::read(relative_path::to_absolute(path)).ok();
    let cached_entry_opt = istate.iopen_files.get(path);
    let entry_opt = match (disk_content_opt, cached_entry_opt) {
        (None, _) => {
            // if the disk file is absent (e.g. it was deleted prior to the user closing it),
            // then we naturally can't compute errors for it.
            None
        }
        (Some(disk_content), Some(OpenFileState { entry, .. }))
            if match &*entry.contents.lock().unwrap() {
                EntryContents::ContentsFromDisk(str) | EntryContents::ProvidedContents(str) => {
                    str.as_slice() == disk_content.as_slice()
                }
                _ => false,
            } =>
        {
            // file on disk was the same as what we currently have in the entry, and
            // the entry very likely already has errors computed for it, so as an optimization
            // we'll re-use errors from that entry.
            Some(Arc::clone(entry))
        }
        (Some(disk_content), _) => {
            // file on disk is different from what we have in the entry, e.g. because the
            // user closed a modified file, so compute errors from the disk content.
            Some(provider_context::make_entry(
                path.clone(),
                EntryContents::ProvidedContents(disk_content.into()),
            ))
        }
    };
    match entry_opt {
        None => {
            // file couldn't be read off disk (maybe absent); therefore, by definition, no errors
            diagnostics::EMPTY
        }
        Some(entry) => {
            // Here we'll get either cached errors from the cached entry, or will recompute errors
            // from the partially cached entry, or will compute errors from the file on disk.
            let ctx = make_singleton_ctx(&istate.icommon, &entry);
            get_user_facing_errors(&ctx, &istate.error_filter, &entry).0
        }
    }
}

fn path_to_relative_path(path: &path::T) -> RelativePath {
    relative_path::create_detect_prefix(&path::to_string(path))
}

/// The errors of a file, sorted, with their hashes.
fn error_hashes(errors: diagnostics::T) -> Vec<(client_ide_message::FinalizedDiagnostic, isize)> {
    let errors = diagnostics::get_sorted_diagnostic_list(None, errors);
    errors
        .iter()
        .map(|err| {
            (
                user_diagnostic::to_absolute(err),
                user_diagnostic::hash_diagnostic_for_saved_state(err),
            )
        })
        .collect()
}

/// `Diagnostics.sort_and_finalize`
fn sort_and_finalize(errors: diagnostics::T) -> Vec<client_ide_message::FinalizedDiagnostic> {
    diagnostics::get_sorted_diagnostic_list(None, errors)
        .iter()
        .map(user_diagnostic::to_absolute)
        .collect()
}

/// `Server_command_types.Find_refs.show_action` (`[@@deriving show]`).
fn show_action(action: &Action) -> String {
    use crate::server_command_types::find_refs::Member;
    let member = |m: &Member| match m {
        Member::Method(s) => format!("(Find_refs.Method {:?})", s),
        Member::Property(s) => format!("(Find_refs.Property {:?})", s),
        Member::ClassConst(s) => format!("(Find_refs.Class_const {:?})", s),
        Member::Typeconst(s) => format!("(Find_refs.Typeconst {:?})", s),
    };
    match action {
        Action::Class(s) => format!("(Find_refs.Class {:?})", s),
        Action::ExplicitClass(s) => format!("(Find_refs.ExplicitClass {:?})", s),
        Action::Member(s, m) => format!("(Find_refs.Member ({:?}, {}))", s, member(m)),
        Action::Function(s) => format!("(Find_refs.Function {:?})", s),
        Action::GConst(s) => format!("(Find_refs.GConst {:?})", s),
        Action::LocalVar {
            filename,
            file_content,
            pos,
        } => format!(
            "Find_refs.LocalVar {{filename = {}; file_content = {:?}; pos = {:?}}}",
            relative_path::to_absolute(filename),
            file_content,
            pos
        ),
    }
}

/// `failwith msg`
fn failwith(msg: String) -> ! {
    std::panic::panic_any(format!("Failure({:?})", msg))
}

// ---------------------------------------------------------------------------
// handle_request
// ---------------------------------------------------------------------------

type HandleResult = (State, Result<Response, lsp::error::T>);

/// handle_request invariants: Messages are only ever handled serially; we never
/// handle one message while another is being handled. It is a bug if the client sends
/// anything other than [Initialize_from_saved_state] as its first message. Upon
/// receipt+processing of this we transition from [Pre_init] to [During_init]
/// and kick off some async work to prepare the naming table. During this async work, i.e.
/// during [During_init], we are able to handle a few requests but will reject
/// others. Important: files may change during [During_init], and it's important that we keep track of and eventually index these changed files.
///
/// Our caller [handle_one_message] is actually the one that transitions
/// us from [During_init] to either [Failed_init] or [Initialized]. Once in one
/// of those states, we never thereafter transition state.
fn handle_request(
    message_queue: &MessageQueue,
    state: State,
    _tracking_id: &str,
    message: M,
) -> HandleResult {
    match (state, message) {
        //*********************************************************
        //************************ HANDLED IN ANY STATE ***********
        //*********************************************************
        (state, M::VerboseToFile(verbose)) => {
            if verbose {
                hh_logger::level::set_min_level_file(hh_logger::level::T::Debug)
            } else {
                hh_logger::level::set_min_level_file(hh_logger::level::T::Info)
            }
            (state, Ok(Response::Unit))
        }
        (state, M::Shutdown) => {
            lwt_message_queue::close(message_queue);
            remove_hhi(&state);
            (state, Ok(Response::Unit))
        }
        //*********************************************************
        //************************ INITIALIZATION *****************
        //*********************************************************
        (State::PendingInit, M::InitializeFromSavedState(param)) => {
            // Invariant: no message will be sent to us prior to this request,
            // and we must send no message until we've sent this response.
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let dstate = initialize1(&param);
                // Establish the watcher clock before saved-state catch-up so changes
                // during naming-table loading are covered by the subscription.
                if dstate.dcommon.local_config.ide_file_watcher_enabled {
                    let message_queue = Arc::clone(message_queue);
                    crate::client_ide_eden_watcher::start(
                        &param.root,
                        dstate.dcommon.local_config.ide_file_watcher_max_changed_files,
                        move |changes| {
                            lwt_message_queue::push(
                                &message_queue,
                                Message::CommitTransitionChanges(changes),
                            )
                        },
                    );
                }
                dstate
            })) {
                Ok(dstate) => {
                    // We're going to kick off the asynchronous part of initializing now.
                    // Once it's done, it will appear as a GotNamingTable message on the queue.
                    start_async_init(message_queue, &dstate, param);
                    log(&format!(
                        "Finished saved state initialization. State: {}",
                        show_dstate(&dstate)
                    ));
                    (State::DuringInit(dstate), Ok(Response::Unit))
                }
                Err(payload) => {
                    let e = exception::wrap(payload);
                    let reason = client_ide_utils::make_rich_error(None, Some(&e), "initialize1");
                    // Our caller has an exception handler. But we must handle this ourselves
                    // to change state to Failed_init; our caller's handler doesn't change state.
                    // TODO: remove_hhi
                    let err = client_ide_utils::to_lsp_error(&reason);
                    (State::FailedInit(reason), Err(err))
                }
            }
        }
        (state, M::InitializeFromSavedState(_)) => {
            failwith(format!("Unexpected init in {}", state_to_log_string(&state)))
        }
        //*********************************************************
        //************************ CAN HANDLE DURING INIT *********
        //*********************************************************
        (state @ (State::DuringInit(_) | State::Initialized(_)), M::DidChangeWatchedFiles(changes)) => (
            process_changed_files(BatchTrigger::LspFileChanges, state, &changes),
            Ok(Response::Unit),
        ),
        // didClose
        (State::DuringInit(dstate), M::DidClose(file_path)) => {
            let path = path_to_relative_path(&file_path);
            let dopen_files = close_file(&dstate.dopen_files, &path);
            (
                State::DuringInit(DState { dopen_files, ..dstate }),
                Ok(Response::Diagnostics(vec![])),
            )
        }
        (State::Initialized(istate), M::DidClose(file_path)) => {
            let path = path_to_relative_path(&file_path);
            let errors = get_diagnostics_for_path(&istate, &path);
            let diagnostics = error_hashes(errors)
                .into_iter()
                .map(client_ide_message::diagnostic_of_finalized_error_without_related_hints)
                .collect();
            let iopen_files = close_file(&istate.iopen_files, &path);
            (
                State::Initialized(IState { iopen_files, ..istate }),
                Ok(Response::Diagnostics(diagnostics)),
            )
        }
        // didOpen or didChange
        (State::DuringInit(dstate), M::DidOpenOrChange(Document { file_path, file_contents })) => {
            let path = path_to_relative_path(&file_path);
            let dstate = open_or_change_file_during_init(dstate, path, &file_contents);
            (State::DuringInit(dstate), Ok(Response::Unit))
        }
        (State::Initialized(istate), M::DidOpenOrChange(document)) => {
            let (iopen_files, _entry, _errors) = update_file(&istate.iopen_files, &document);
            (
                State::Initialized(IState { iopen_files, ..istate }),
                Ok(Response::Unit),
            )
        }
        // Pull diagnostics
        (State::Initialized(istate), M::Diagnostics(document)) => {
            let (istate, ctx, entry, published_errors_ref) = update_file_ctx(istate, &document);
            let (errors, identity) = get_user_facing_errors(&ctx, &istate.error_filter, &entry);
            *published_errors_ref.borrow_mut() = Some(identity);
            let diagnostics = crate::ide_diagnostics::convert(&ctx, &entry, error_hashes(errors));
            (State::Initialized(istate), Ok(Response::Diagnostics(diagnostics)))
        }
        // Document Symbol
        (State::DuringInit(dstate), M::DocumentSymbol(document)) => {
            let (dopen_files, entry, _) = update_file(&dstate.dopen_files, &document);
            let result = file_outline::outline_entry_no_comments(
                &server_config::parser_options(&dstate.dcommon.config),
                &entry,
            );
            (
                State::DuringInit(DState { dopen_files, ..dstate }),
                Ok(Response::DocumentSymbol(result)),
            )
        }
        (State::Initialized(istate), M::DocumentSymbol(document)) => {
            let (iopen_files, entry, _) = update_file(&istate.iopen_files, &document);
            let result = file_outline::outline_entry_no_comments(
                &server_config::parser_options(&istate.icommon.config),
                &entry,
            );
            (
                State::Initialized(IState { iopen_files, ..istate }),
                Ok(Response::DocumentSymbol(result)),
            )
        }
        //*********************************************************
        //************************ UNABLE TO HANDLE ***************
        //*********************************************************
        (State::DuringInit(dstate), _) => {
            let e = lsp::error::T {
                code: lsp::error::RequestCancelled,
                message: "IDE service has not yet completed init".to_string(),
                data: None,
            };
            (State::DuringInit(dstate), Err(e))
        }
        (State::FailedInit(reason), _) => {
            let err = client_ide_utils::to_lsp_error(&reason);
            (State::FailedInit(reason), Err(err))
        }
        (state @ State::PendingInit, message) => failwith(format!(
            "unexpected message '{}' in state '{}'",
            client_ide_message::t_to_string(&message),
            state_to_log_string(&state)
        )),
        //*********************************************************
        //************************ NORMAL HANDLING AFTER INIT *****
        //*********************************************************
        (State::Initialized(istate), message) => handle_request_initialized(istate, message),
    }
}

/// The requests of the `Initialized` state (the second half of
/// `handle_request`).
fn handle_request_initialized(istate: IState, message: M) -> HandleResult {
    match message {
        M::Hover(document, pos) => {
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let result = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::ide_hover::go_quarantined(&ctx, &entry, &pos)
            });
            (State::Initialized(istate), Ok(Response::Hover(result)))
        }
        M::GoToImplementation(document, pos, document_list) => {
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let (istate, result) = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                match crate::server_find_refs::go_from_file_ctx(&ctx, &entry, &pos) {
                    Some((_name, action)) if !crate::server_go_to_impl::is_searchable(&action) => {
                        (istate, client_ide_message::GoToImplResult::InvalidSymbolImpl)
                    }
                    Some((name, action)) => {
                        // 1) For all open files that we know about in ClientIDEDaemon, uesd the
                        // cached TASTs to return positions of implementations
                        // 2) Return this list, alongside the name and action
                        // 3) ClientLSP, upon receiving, will shellout to hh_server
                        // and reject all server-provided positions for files that ClientIDEDaemon
                        // knew about, under the assumption that our cached TAST provides edited
                        // file info, if applicable.
                        let (istate, single_file_positions) = document_list.iter().fold(
                            (istate, client_ide_message::UriMap::new()),
                            |(istate, accum), document| {
                                let (istate, ctx, _entry, _errors) = update_file_ctx(istate, document);
                                let stringified_path = path::to_string(&document.file_path);
                                let filename = relative_path::create_detect_prefix(&stringified_path);
                                let single_file_pos: Vec<crate::pos::Absolute> =
                                    crate::server_find_refs::to_absolute(
                                        &crate::server_go_to_impl::go_for_single_file(
                                            &ctx,
                                            &action,
                                            &istate.naming_table,
                                            &filename,
                                        ),
                                    )
                                    .into_iter()
                                    .map(|crate::search_types::find_refs::Result { name: _, pos }| pos)
                                    .collect();
                                let urikey =
                                    lsp_helpers::path_string_to_lsp_uri(&stringified_path, &stringified_path);
                                let updated_map = accum.update(urikey, single_file_pos);
                                (istate, updated_map)
                            },
                        );
                        (
                            istate,
                            client_ide_message::GoToImplResult::GoToImplSuccess(
                                name,
                                action,
                                single_file_positions,
                            ),
                        )
                    }
                    None => (istate, client_ide_message::GoToImplResult::InvalidSymbolImpl),
                }
            });
            (State::Initialized(istate), Ok(Response::GoToImplementation(result)))
        }
        // textDocument/rename
        M::Rename(document, pos, new_name, document_list) => {
            let (istate, ctx, entry, _errors) = update_file_ctx(istate, &document);
            let (istate, result) = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                match crate::server_find_refs::go_from_file_ctx_with_symbol_definition(&ctx, &entry, &pos) {
                    None => (istate, client_ide_message::RenameResult::NotRenameablePosition),
                    Some((_definition, action)) if crate::server_find_refs::is_local(&action) => {
                        let res = match crate::server_rename::go_for_localvar(&ctx, &action, &new_name) {
                            Ok(Some(patch_list)) => client_ide_message::RenameResult::RenameSuccess {
                                shellout: None,
                                local: patch_list,
                            },
                            Ok(None) => client_ide_message::RenameResult::RenameSuccess {
                                shellout: None,
                                local: vec![],
                            },
                            Err(action) => {
                                let str = format!(
                                    "ClientIDEDaemon failed to rename for localvar {}",
                                    show_action(&action)
                                );
                                log(&str);
                                failwith("ClientIDEDaemon failed to rename for a localvar".to_string())
                            }
                        };
                        (istate, res)
                    }
                    Some((symbol_definition, action)) => {
                        let (istate, single_file_patches) = document_list.iter().fold(
                            (istate, vec![]),
                            |(istate, accum), document| {
                                let (istate, ctx, _entry, _errors) = update_file_ctx(istate, document);
                                let filename =
                                    relative_path::create_detect_prefix(&path::to_string(&document.file_path));
                                let single_file_patches = crate::server_rename::go_for_single_file(
                                    &ctx,
                                    &action,
                                    &new_name,
                                    &filename,
                                    &symbol_definition,
                                );
                                let patches = match single_file_patches {
                                    Ok(patches) => patches,
                                    Err(_) => vec![],
                                };
                                // `List.rev_append patches accum`
                                let mut patch_list: Vec<_> = patches.into_iter().rev().collect();
                                patch_list.extend(accum);
                                (istate, patch_list)
                            },
                        );
                        (
                            istate,
                            client_ide_message::RenameResult::RenameSuccess {
                                shellout: Some((symbol_definition, action)),
                                local: single_file_patches,
                            },
                        )
                    } // not a localvar, must defer to hh_server
                }
            });
            (State::Initialized(istate), Ok(Response::Rename(result)))
        }
        // textDocument/references - localvar only
        M::FindReferences(document, pos, document_list) => {
            // Update the state of the world with the document as it exists in the IDE
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let (istate, result) = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                match crate::server_find_refs::go_from_file_ctx(&ctx, &entry, &pos) {
                    Some((name, action)) if crate::server_find_refs::is_local(&action) => {
                        let result = crate::server_find_refs::go_for_localvar(&ctx, &action)
                            .map(|r| crate::server_find_refs::to_absolute(&r));
                        let result = match result {
                            Ok(ide_result) => {
                                let lsp_uri_map = match ide_result.as_slice() {
                                    [] => {
                                        // If we find-refs on a localvar via right-click, is it possible that it doesn't return references?
                                        // It's possible some nondeterminism changed the cached TAST,
                                        // but assert that it's a failure for now
                                        let err = format!(
                                            "FindRefs returned an empty list of positions for localvar {}",
                                            name
                                        );
                                        log(&err);
                                        failwith(err)
                                    }
                                    positions => {
                                        let filename: String = crate::pos::filename(&positions[0].pos).to_string();
                                        let uri = lsp_helpers::path_string_to_lsp_uri(&filename, &filename);
                                        client_ide_message::UriMap::new().update(uri, positions.to_vec())
                                    }
                                };
                                if lsp_uri_map.values().count() != 1 {
                                    // Can a localvar cross file boundaries? I sure hope not.
                                    let err = format!(
                                        "Found more than one file when executing find refs for localvar {}",
                                        name
                                    );
                                    log(&err);
                                    failwith(err)
                                }
                                client_ide_message::FindRefsResult::FindRefsSuccess {
                                    full_name: name,
                                    action: None,
                                    hint_suffixes: vec![],
                                    open_file_results: lsp_uri_map,
                                }
                            }
                            Err(_action) => {
                                let err = format!("Failed to find refs for localvar {}", name);
                                log(&err);
                                failwith(err)
                            }
                        };
                        (istate, result)
                        // clientLsp should raise if we return a LocalVar action
                    }
                    None => {
                        // Clicking a line+col that isn't a symbol
                        (istate, client_ide_message::FindRefsResult::InvalidSymbol)
                    }
                    Some((name, action)) => {
                        // Not a localvar, so we do the following:
                        // 1) For all open files that we know about in ClientIDEDaemon, uesd the
                        // cached TASTs to return positions of references
                        // 2) Return this list, alongside the name and action
                        // 3) ClientLSP, upon receiving, will shellout to hh_server
                        // and reject all server-provided positions for files that ClientIDEDaemon
                        // knew about, under the assumption that our cached TAST provides edited
                        // file info, if applicable.
                        let (istate, single_file_refs) = document_list.iter().fold(
                            (istate, client_ide_message::UriMap::new()),
                            |(istate, accum), document| {
                                let (istate, ctx, _entry, _errors) = update_file_ctx(istate, document);
                                let stringified_path = path::to_string(&document.file_path);
                                let filename = relative_path::create_detect_prefix(&stringified_path);
                                let single_file_ref = crate::server_find_refs::to_absolute(
                                    &crate::server_find_refs::go_for_single_file(&ctx, &action, &filename),
                                );
                                let urikey =
                                    lsp_helpers::path_string_to_lsp_uri(&stringified_path, &stringified_path);
                                let updated_map = accum.update(urikey, single_file_ref);
                                (istate, updated_map)
                            },
                        );
                        let mut sienv_ref = istate.sienv.clone();
                        let hints = crate::symbol_index::find_refs(&mut sienv_ref, &action, 100);
                        let hint_suffixes = match hints {
                            None => vec![],
                            Some(hints) => hints
                                .iter()
                                .filter_map(|path| {
                                    if relative_path::is_root(relative_path::prefix(path)) {
                                        Some(relative_path::suffix(path))
                                    } else {
                                        None
                                    }
                                })
                                .collect(),
                        };
                        (
                            IState {
                                sienv: sienv_ref,
                                ..istate
                            },
                            client_ide_message::FindRefsResult::FindRefsSuccess {
                                full_name: name,
                                action: Some(action),
                                hint_suffixes,
                                open_file_results: single_file_refs,
                            },
                        )
                    }
                }
            });
            (State::Initialized(istate), Ok(Response::FindReferences(result)))
        }
        // Autocomplete
        M::Completion(document, pos, client_ide_message::CompletionRequest { is_manually_invoked }) => {
            // Update the state of the world with the document as it exists in the IDE
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let mut sienv_ref = istate.sienv.clone();
            let result = crate::server_auto_complete::go_ctx(
                &ctx,
                &entry,
                &mut sienv_ref,
                &istate.naming_table,
                is_manually_invoked,
                &pos,
            );
            let istate = IState {
                sienv: sienv_ref,
                ..istate
            };
            (State::Initialized(istate), Ok(Response::Completion(result)))
        }
        // Autocomplete docblock resolve
        M::CompletionResolve(client_ide_message::completion_resolve::Request { fullname: symbol, kind }) => {
            // (`Hack_event_logger.completion_call ~method_name:"Completion_resolve"`: no-op.)
            let ctx = make_empty_ctx(&istate.icommon);
            let result = crate::server_docblock_at::go_docblock_for_symbol(&ctx, &symbol, kind);
            let signature = crate::server_auto_complete::get_signature(&ctx, &symbol);
            (
                State::Initialized(istate),
                Ok(Response::CompletionResolve(client_ide_message::completion_resolve::Result {
                    docblock: result,
                    signature,
                })),
            )
        }
        // Autocomplete docblock resolve
        M::CompletionResolveLocation(file_path, fullname, pos, kind) => {
            // We're given a location but it often won't be an opened file.
            // We will only serve autocomplete docblocks as of truth on disk.
            // Hence, we construct temporary entry to reflect the file which
            // contained the target of the resolve.
            // (`Hack_event_logger.completion_call ~method_name:"Completion_resolve_location"`: no-op.)
            let path = path_to_relative_path(&file_path);
            let ctx = make_empty_ctx(&istate.icommon);
            let (ctx, entry) = provider_context::add_entry_if_missing(&ctx, path);
            let result = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_docblock_at::go_docblock_ctx(&ctx, &entry, &pos, kind)
            });
            let client_ide_message::Fullname(s) = fullname;
            let signature = crate::server_auto_complete::get_signature(&ctx, &s);
            (
                State::Initialized(istate),
                Ok(Response::CompletionResolve(client_ide_message::completion_resolve::Result {
                    docblock: result,
                    signature,
                })),
            )
        }
        // Document highlighting
        M::DocumentHighlight(document, pos) => {
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let results = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::ide_highlight_refs::go_quarantined(&ctx, &entry, &pos)
            });
            (State::Initialized(istate), Ok(Response::DocumentHighlight(results)))
        }
        // Signature help
        M::SignatureHelp(document, pos) => {
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let results = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_signature_help::go_quarantined(&ctx, &entry, &pos)
            });
            (State::Initialized(istate), Ok(Response::SignatureHelp(results)))
        }
        M::TopLevelDefNameAtPos(document, pos) => {
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let res = crate::ide_top_level_def_name_at_pos::go_quarantined(&ctx, &entry, &pos);
            (State::Initialized(istate), Ok(Response::OptionString(res)))
        }
        // AutoClose
        M::AutoClose(document, pos) => {
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let close_tag = crate::autoclose_tags::go_xhp_close_tag(&ctx, &entry, &pos);
            (State::Initialized(istate), Ok(Response::OptionString(close_tag)))
        }
        // Code actions (refactorings, quickfixes)
        M::CodeAction(document, range) => {
            let (istate, ctx, entry, published_errors_ref) = update_file_ctx(istate, &document);
            let results = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::code_actions::code_actions_services::go(&ctx, &istate.error_filter, &entry, &range)
            });
            // We'll take this opportunity to make sure we've returned the latest errors.
            // Why only return errors from didOpen,didChange,didClose,codeAction, and not also all
            // the other methods like "hover" which might have recomputed TAST+errors? -- simplicity,
            // mainly -- it's simpler to perform+handle this logic in just a few places rather than
            // everywhere, and also because codeAction is called so frequently (e.g. upon changing
            // tabs) that it's the best opportunity we have.
            let (errors, identity) = get_user_facing_errors(&ctx, &istate.error_filter, &entry);
            let published = *published_errors_ref.borrow();
            let errors_opt = match published {
                Some(published_errors) if published_errors == identity => {
                    // If the previous errors we returned are physically equal, that's an indication
                    // that the entry's TAST+errors hasn't been recomputed since last we returned errors
                    // back to clientLsp, so no need to do anything.
                    // And we actively WANT to do nothing in this case, since codeAction is called so frequently --
                    // e.g. every time the caret moves -- and we wouldn't want errors to be republished that
                    // frequently.
                    None
                }
                Some(_) | None => {
                    // [Some _] -> the TAST+errors has changed since we last returned them.
                    // [None] -> we don't have a record of previous errors returned back to clientLsp.
                    *published_errors_ref.borrow_mut() = Some(identity);
                    Some(sort_and_finalize(errors))
                }
            };
            (State::Initialized(istate), Ok(Response::CodeAction(results, errors_opt)))
        }
        // Code action resolve (refactorings, quickfixes)
        M::CodeActionResolve {
            document,
            range,
            resolve_title,
            use_snippet_edits,
        } => {
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let result = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::code_actions::code_actions_services::resolve(
                    &ctx,
                    &istate.error_filter,
                    &entry,
                    &range,
                    &resolve_title,
                    use_snippet_edits,
                )
            });
            (State::Initialized(istate), Ok(Response::CodeActionResolve(result)))
        }
        // Go to definition
        M::Definition(document, pos) => {
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let result = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_go_to_definition::go_quarantined(&ctx, &entry, &pos)
            });
            (State::Initialized(istate), Ok(Response::Definition(result)))
        }
        // Type Definition
        M::TypeDefinition(document, pos) => {
            let (istate, ctx, entry, _) = update_file_ctx(istate, &document);
            let result = provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_type_definition::go_quarantined(&ctx, &entry, &pos)
            });
            (State::Initialized(istate), Ok(Response::TypeDefinition(result)))
        }
        // Workspace Symbol
        M::WorkspaceSymbol(query) => {
            // Note: needs reverse-naming-table, hence only works in initialized
            // state: for top-level queries it needs reverse-naming-table to look
            // up positions; for member queries "Foo::bar" it needs it to fetch the
            // decl for Foo.
            // Note: we intentionally don't give results from unsaved files
            let ctx = make_empty_ctx(&istate.icommon);
            let mut sienv_ref = istate.sienv.clone();
            let result = crate::ide_search::go(&ctx, &query, "", &mut sienv_ref);
            let istate = IState {
                sienv: sienv_ref,
                ..istate
            };
            (State::Initialized(istate), Ok(Response::WorkspaceSymbol(result)))
        }
        // (The other constructors are handled in every state, or before the
        // `Initialized` ones: `handle_request` matches them first.)
        M::VerboseToFile(_)
        | M::Shutdown
        | M::InitializeFromSavedState(_)
        | M::DidChangeWatchedFiles(_)
        | M::DidClose(_)
        | M::DidOpenOrChange(_)
        | M::Diagnostics(_)
        | M::DocumentSymbol(_) => unreachable!(),
    }
}

/// `Lwt.async (fun () -> let%lwt naming_table_result = Client_ide_init.init
/// ... in Lwt_message_queue.push message_queue (GotNamingTable ..))`: the
/// init runs on a thread of its own (see the module doc); this returns once
/// it first waits, as `Lwt.async` returns at the promise's first wait.
fn start_async_init(
    message_queue: &MessageQueue,
    dstate: &DState,
    param: client_ide_message::initialize_from_saved_state::T,
) {
    let message_queue = Arc::clone(message_queue);
    let config = dstate.dcommon.config.clone();
    let local_config = dstate.dcommon.local_config.clone();
    let hhi_root = dstate.dcommon.hhi_root.clone();
    let ctx = Arc::clone(&dstate.dcommon.ctx);
    let logger = hh_logger::thread_instance();
    let (first_wait_tx, first_wait_rx) = mpsc::channel::<()>();
    let spawned = std::thread::Builder::new()
        .name("ClientIdeService.init".to_string())
        .stack_size(crate::check::STACK_SIZE)
        .spawn(move || {
            hh_logger::set_thread_instance(logger);
            let mut waits = client_ide_init::Waits::new(move || {
                let _ = first_wait_tx.send(());
            });
            let naming_table_result = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                client_ide_init::init(&mut waits, &config, &local_config, &param, &hhi_root, &ctx)
            })) {
                Ok(result) => result,
                // (An exception escaping the promise: `Lwt.async` hands it
                // to `Lwt.async_exception_hook`, which exits the process.)
                Err(payload) => {
                    let e = exception::wrap(payload);
                    Err(client_ide_utils::make_rich_error(None, Some(&e), "init"))
                }
            };
            drop(waits);
            // if the following push fails, that must be because the queues
            // have been shut down, in which case there's nothing to do.
            let _succeeded: bool =
                lwt_message_queue::push(&message_queue, Message::GotNamingTable(naming_table_result));
        });
    if spawned.is_ok() {
        // The promise's first wait (or its end).
        let _ = first_wait_rx.recv();
    }
}

/// Awaits until the next message is available, and handles it
fn handle_one_message_exn(
    out_fd: &OutFd,
    message_queue: &MessageQueue,
    state: State,
    error_filter: &crate::filter_diagnostics::filter::T,
) -> Option<State> {
    dbg_set_activity("handle", "popping");
    let message = lwt_message_queue::pop(message_queue);
    dbg_set_activity(
        "handle",
        &match &message {
            None => "none".to_string(),
            Some(Message::CommitTransitionChanges(_)) => "commit_transition".to_string(),
            Some(Message::GotNamingTable(Ok(_))) => "got_naming_table_ok".to_string(),
            Some(Message::GotNamingTable(Err(_))) => "got_naming_table_err".to_string(),
            Some(Message::ClientRequest(message)) => client_ide_message::tracked_t_to_string(message),
        },
    );
    match (state, message) {
        (_, None) => None, // exit loop if message_queue has been closed
        (state, Some(Message::CommitTransitionChanges(changes))) => Some(process_changed_files(
            BatchTrigger::CommitTransition,
            state,
            &changes,
        )),
        (State::DuringInit(dstate), Some(Message::GotNamingTable(naming_table_result))) => {
            let state = initialize2(out_fd, dstate, error_filter, naming_table_result);
            Some(state)
        }
        (state, Some(Message::GotNamingTable(_))) => {
            failwith(format!("Unexpected GotNamingTable in {}", state_to_log_string(&state)))
        }
        (state, Some(Message::ClientRequest(TrackedT { tracking_id, message }))) => {
            let unblocked_time = crate::rt::ocaml_unix::gettimeofday();
            // (`Hack_event_logger.serverless_ide_set_tracking_id tracking_id`: no-op.)
            // Our caller has an exception handler which logs the exception.
            // But we instead must fulfil our contract of responding to the client,
            // even if we have an exception. Hence we need our own handler here.
            let prev_state = state.clone();
            let (state, response) = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                handle_request(message_queue, state, &tracking_id, message)
            })) {
                Ok(result) => result,
                Err(payload) => {
                    // (The quarantine of a request that raised was left by
                    // `respect_but_quarantine_unsaved_changes`'s finally.)
                    let e = exception::wrap(payload);
                    if exception::unwrap(&e)
                        .downcast_ref::<crate::worker_cancel::WorkerShouldExit>()
                        .is_some()
                    {
                        // When is this exception raised? several places during Typing_toplevel
                        // inner-loops call [WorkerCancel.raise_if_stop_requested]. So: it will
                        // be raised during [Tast_provider.compute_tast*] shortly after
                        // ClientLsp has called [WorkerCancel.stop_workers], which it does
                        // if it sees $/cancelRequest LSP notification on the incoming queue.
                        let stack = exception::clean_stack(&exception::get_backtrace_string(&e));
                        let lsp_error = lsp::error::T {
                            code: lsp::error::RequestCancelled,
                            message: client_ide_utils::ctor_string(&e),
                            data: Some(yojson::T::Assoc(vec![(
                                "stack".to_string(),
                                yojson::T::String(stack),
                            )])),
                        };
                        (prev_state, Err(lsp_error))
                    } else {
                        let reason = client_ide_utils::make_rich_error(None, Some(&e), "handle_request");
                        (prev_state, Err(client_ide_utils::to_lsp_error(&reason)))
                    }
                }
            };
            dbg_set_activity("handle", "write_response");
            write_message(
                out_fd,
                MessageFromDaemon::Response(client_ide_message::TimedResponse {
                    response,
                    tracking_id,
                    unblocked_time,
                }),
            );
            dbg_set_activity("handle", "written_response");
            Some(state)
        }
    }
}

fn serve(
    in_fd: mpsc::Receiver<TrackedT>,
    out_fd: OutFd,
    error_filter: &crate::filter_diagnostics::filter::T,
) {
    // `try%lwt ... with exn -> log_bug "fatal clientIdeDaemon"`
    if let Err(payload) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| serve_inner(in_fd, out_fd, error_filter))) {
        let e = exception::wrap(payload);
        client_ide_utils::log_bug(None, Some(&e), true, "fatal clientIdeDaemon");
        dbg_set_activity("main", &format!("exception {}", client_ide_utils::ctor_string(&e)));
    }
}

fn serve_inner(
    in_fd: mpsc::Receiver<TrackedT>,
    out_fd: OutFd,
    error_filter: &crate::filter_diagnostics::filter::T,
) {
    let message_queue: MessageQueue = lwt_message_queue::create();
    dbg_set_activity("main", "serve");
    // `pump_stdin`: on a thread of its own.
    let pump = {
        let message_queue = Arc::clone(&message_queue);
        let logger = hh_logger::thread_instance();
        std::thread::Builder::new()
            .name("ClientIdeService.pump".to_string())
            .spawn(move || {
                hh_logger::set_thread_instance(logger);
                loop {
                    dbg_set_activity("pump", "loop");
                    dbg_set_activity("pump", "from_fd");
                    let (message, is_queue_open) = match in_fd.recv() {
                        Ok(TrackedT { tracking_id, message }) => {
                            dbg_set_activity("pump", "push");
                            let is_shutdown = matches!(message, M::Shutdown);
                            let is_queue_open = lwt_message_queue::push(
                                &message_queue,
                                Message::ClientRequest(TrackedT { tracking_id, message }),
                            );
                            (is_shutdown, is_queue_open)
                        }
                        Err(_) => {
                            // There are two proper ways to close clientIdeDaemon: (1) by sending it a Shutdown message
                            // over the FD which is handled above, or (2) by closing the FD which is handled here. Neither
                            // path is considered anomalous and neither will raise an exception.
                            // Note that closing the message-queue is how we tell handle_messages loop to terminate.
                            dbg_set_activity("pump", "eof");
                            lwt_message_queue::close(&message_queue);
                            (true, false)
                        }
                    };
                    if !is_queue_open {
                        return;
                    }
                    if message {
                        // `Shutdown`: the OCaml's pump stops reading; the
                        // daemon then waits until the client kills it
                        // (`Daemon.force_quit`). Here the client closes our
                        // input instead (`Client_ide_service.destroy`):
                        // what comes before that is not read, and the end
                        // of the input ends the daemon.
                        while in_fd.recv().is_ok() {}
                        lwt_message_queue::close(&message_queue);
                        return;
                    }
                }
            })
    };
    // `handle_messages`
    let mut state = State::PendingInit;
    loop {
        dbg_set_activity("handle", "loop");
        let next_state_opt = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            handle_one_message_exn(&out_fd, &message_queue, state.clone(), error_filter)
        })) {
            Ok(state) => {
                dbg_set_activity("handle", "done");
                state
            }
            Err(payload) => {
                let e = exception::wrap(payload);
                let is_write_error = exception::unwrap(&e).downcast_ref::<OutfdWriteError>().is_some();
                dbg_set_activity(
                    "handle",
                    &format!(
                        "exn {}; is_write_error={}",
                        client_ide_utils::ctor_string(&e),
                        is_write_error
                    ),
                );
                client_ide_utils::log_bug(None, Some(&e), true, "handle_one_message");
                if is_write_error {
                    // if out_fd is down then there's no use continuing.
                    // (`exit 1`: the daemon's process exits; here its thread ends.)
                    lwt_message_queue::close(&message_queue);
                    None
                } else {
                    dbg_set_activity("handle", "exn continue");
                    Some(state.clone())
                }
            }
        };
        match next_state_opt {
            None => break, // exit loop
            Some(next) => state = next,
        }
    }
    dbg_set_activity("main", "ending");
    if let Ok(pump) = pump {
        // The pump ends at Shutdown or EOF (the client closes our input).
        drop(pump);
    }
}

/// Makes the panics of the daemon's threads silent (the OCaml's exceptions
/// print nothing): the panics of other threads still go to the hook that was
/// there before.
fn install_quiet_panic_hook() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            let quiet = std::thread::current()
                .name()
                .is_some_and(|name| name.starts_with("ClientIdeService"));
            if !quiet {
                previous(info)
            }
        }));
    })
}

/// `daemon_main args channels`: the daemon's main loop, on its own thread
/// (`Client_ide_service.make` starts it, with its `Hh_logger` state).
/// `channels` are its input (the requests) and its output (the responses
/// and notifications).
pub fn daemon_main(
    args: client_ide_message::DaemonArgs,
    channels: (mpsc::Receiver<TrackedT>, mpsc::Sender<MessageFromDaemon>),
) {
    let client_ide_message::DaemonArgs {
        init_id: _,
        verbose_to_file,
        verbose_to_stderr,
        error_filter,
        client_lsp_log_fn: _,
    } = args;
    // (`Startup_initializer.init ()`, `Printexc.record_backtrace true`.)
    install_quiet_panic_hook();
    let _ = crate::check::build_thread_pool(None);
    dbg_set_activity("main", "daemon_main");
    let (in_fd, out_fd) = channels;
    // (`daemon_init_id`, `Hack_event_logger.serverless_ide_init`: telemetry only.)
    if verbose_to_stderr {
        hh_logger::level::set_min_level_stderr(hh_logger::level::T::Debug)
    } else {
        hh_logger::level::set_min_level_stderr(hh_logger::level::T::Error)
    }
    if verbose_to_file {
        hh_logger::level::set_min_level_file(hh_logger::level::T::Debug)
    } else {
        hh_logger::level::set_min_level_file(hh_logger::level::T::Info)
    }
    // (`Shared_mem.connect shm_handle ~worker_id:1`: the daemon is a thread
    // of the process.)
    dbg_set_activity("main", "run_main");
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        serve(in_fd, out_fd, &error_filter);
    })) {
        Ok(()) => {
            dbg_set_activity("main", "done");
            hh_logger::log("SERVERLESS_IDE_DONE(ok)");
        }
        Err(payload) => {
            let e = exception::wrap(payload);
            dbg_set_activity("main", &format!("exn {}", client_ide_utils::ctor_string(&e)));
            hh_logger::log(&format!(
                "SERVERLESS_IDE_DONE(exn)\n{}",
                exception::clean_stack(&exception::to_string(&e))
            ));
        }
    }
    // `Stdlib.at_exit`: the daemon process exits after `daemon_main`.
    let activities = dbg_dump_activity();
    hh_logger::log(&format!("SERVERLESS_IDE_EXIT\n{}", activities));
}

#[cfg(test)]
mod tests;

pub mod test {
    //! `Client_ide_daemon.Test`: the daemon's handler, called directly.
    use super::*;

    pub type Env = IState;

    /// `init ~custom_config ~naming_sqlite`
    pub fn init(custom_config: Option<server_config::T>, naming_sqlite: &path::T) -> Env {
        let config = custom_config.unwrap_or_else(server_config::default_config);
        let local_config = crate::server_local_config_load::default();
        let tcopt = server_config::typechecker_options(&config);
        let root = relative_path::path_of_prefix(relative_path::Prefix::Root).unwrap_or_default();
        let (ctx, local_memory) = make_local_memory_ctx(&config, &root, None);
        let sienv = crate::symbol_index::initialize(
            &server_config::glean_options(&config),
            &tcopt.po.auto_namespace_map,
            &local_config.ide_symbolindex_search_provider,
            local_config.symbolindex_quiet,
        );
        let naming_table = client_ide_init::load_naming_table(&ctx, &path::to_string(naming_sqlite));
        IState {
            naming_table,
            error_filter: tast_provider::ErrorFilter::default(),
            sienv,
            icommon: CommonState {
                hhi_root: path::make("/"),
                config,
                local_config,
                local_memory,
                ctx,
            },
            iopen_files: Default::default(),
        }
    }

    pub fn index(istate: Env, changes: &relative_path::set::T) -> Env {
        hh_logger::log(&format!(
            "--> [index] {}",
            changes
                .iter()
                .map(relative_path::suffix)
                .collect::<Vec<_>>()
                .join(" ")
        ));
        let (naming_table, sienv) = batch_update_naming_table_and_invalidate_caches(
            BatchTrigger::TestIndex,
            &make_empty_ctx(&istate.icommon),
            &istate.naming_table,
            &istate.sienv,
            &istate.icommon.local_memory,
            &istate.iopen_files,
            changes,
        );
        IState {
            naming_table,
            sienv,
            ..istate
        }
    }

    pub fn handle<A: client_ide_message::IdeResult>(
        istate: Env,
        message: client_ide_message::Request<A>,
    ) -> (Env, A) {
        let message = message.message;
        hh_logger::log(&format!("--> {}", client_ide_message::t_to_string(&message)));
        let message_queue = lwt_message_queue::create();
        match handle_request(&message_queue, State::Initialized(istate), "tracking_id", message) {
            (State::Initialized(istate), Ok(response)) => match A::of_response(response) {
                Some(response) => (istate, response),
                None => panic!("handle_request ended in bad state"),
            },
            (_, Err(lsp::error::T { code, message, data })) => {
                let msg = format!(
                    "handle_request {}: {} {}",
                    lsp::error::show_code(code),
                    message,
                    data.map_or(String::new(), |d| crate::yojson::safe::pretty_to_string(&d))
                );
                panic!("{}", msg)
            }
            (_, Ok(_)) => {
                let msg = "handle_request ended in bad state".to_string();
                panic!("{}", msg)
            }
        }
    }
}
