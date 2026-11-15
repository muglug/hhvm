// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/client_ide_init.ml`.
//!
//! # Lwt
//!
//! `init` is an Lwt promise that the daemon starts with `Lwt.async` and
//! whose result it posts on its own queue (`GotNamingTable`). Here [`init`]
//! runs on a thread of its own (`Client_ide_daemon` starts it); it calls
//! `at_first_wait` when it first waits (the first `Lwt_unix.sleep` of the
//! OCaml, where `Lwt.async` returns to the daemon), so that the daemon goes
//! on from there, as the OCaml does, and its log has the same order.
//!
//! # The naming table
//!
//! `Naming_table.load_from_sqlite ctx path`: the daemon's `Ctx` has the
//! `Local_memory` backend (`Ctx::install_local_memory`), whose reverse
//! naming table reads the database from then on; decls are parsed on
//! demand, as in the OCaml.
//!
//! What the OSS OCaml does here, ported as it is: `find` and `fetch` fail
//! (`State_loader_lwt` is a stub: "Not implemented", and
//! `Saved_state_loader.LoadError.category_of_error` is ""), so a naming table
//! is BUILT, by the Rust `naming_table_builder::build_naming_table_ide` (the
//! code `Naming_table_builder_ffi_externs.build` runs, in-process here too),
//! into `<tmp>/<escaped root>.client_ide_naming_table`.

use crate::client_ide_message;
use crate::client_ide_message::RichError;
use crate::client_ide_utils;
use crate::exception;
use crate::file_info::SiAddendum;
use crate::hh_logger;
use crate::naming_table;
use crate::path;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::saved_state_loader::load_error;
use crate::search_utils;
use crate::server_config;
use crate::server_local_config;
use crate::symbol_index;
use crate::symbol_index_core;
use crate::telemetry;
use crate::yojson::safe as yojson;

/// `Warnings_saved_state.t`
pub type WarningsSavedState = oxidized::warnings_saved_state_impl::WarningsSavedState;

/// `Saved_state_loader.changed_files`
pub type ChangedFiles = Vec<RelativePath>;

/// Success case for [`init`].
pub struct InitResult {
    /// An open connection to sqlite naming-table file. (Naming_table.t is
    /// able to store an in-memory delta, but in our case the result of
    /// [`init`] always has an empty delta.)
    pub naming_table: naming_table::T,
    pub warnings_saved_state: Option<WarningsSavedState>,
    /// search+autocomplete index, either full (in case we built) or delta
    /// plus a connection to whatever symbolindex is specified in hh.conf and
    /// .hhconfig (in other cases)
    pub sienv: search_utils::SiEnv,
    /// files changed between saved-state and "now", for some arbitrary value
    /// of "now" during the execution of [`init`]. For race-freedom, the
    /// caller will need to set up some subscription for change-notifications
    /// prior to calling [`init`].
    pub changed_files: ChangedFiles,
}

pub enum Outcome<A> {
    Success(A),
    Failure(RichError),
    Skip(String),
}

/// `error_from_load_error load_error`
fn error_from_load_error(load_error: &load_error::T) -> RichError {
    let data = Some(yojson::T::Assoc(vec![(
        "debug_details".to_string(),
        yojson::T::String(load_error::debug_details_of_error(load_error)),
    )]));
    let reason = client_ide_utils::make_rich_error(data, None, &load_error::category_of_error(load_error));
    // [make_rich_error] returns a vague "IDE isn't working" message.
    // If load_error was actionable, then we can get more specific information
    // out of the load_error, although it's no longer IDE-specific.
    if load_error::is_error_actionable(load_error) {
        RichError {
            is_actionable: true,
            short_user_message: load_error::short_user_message_of_error(load_error),
            medium_user_message: load_error::medium_user_message_of_error(load_error),
            long_user_message: load_error::long_user_message_of_error(load_error),
            ..reason
        }
    } else {
        reason
    }
}

/// What waits do: `Lwt_unix.sleep`, after telling the daemon (once) that
/// the promise has reached its first wait.
pub struct Waits<'a> {
    at_first_wait: Option<Box<dyn FnOnce() + Send + 'a>>,
}

impl<'a> Waits<'a> {
    pub fn new(at_first_wait: impl FnOnce() + Send + 'a) -> Self {
        Self {
            at_first_wait: Some(Box::new(at_first_wait)),
        }
    }

    /// `Lwt_unix.sleep secs`
    fn sleep(&mut self, secs: f64) {
        if let Some(f) = self.at_first_wait.take() {
            f()
        }
        if secs > 0. {
            std::thread::sleep(std::time::Duration::from_secs_f64(secs));
        }
    }
}

/// LSP initialize method might directly contain the path of a saved-state to use.
/// Note: this path doesn't yet support changed_files.
fn init_via_lsp(
    waits: &mut Waits<'_>,
    naming_table_load_info: &Option<client_ide_message::initialize_from_saved_state::NamingTableLoadInfo>,
) -> Outcome<path::T> {
    match naming_table_load_info {
        None => Outcome::Skip("no naming_table_load_info".to_string()),
        Some(naming_table_load_info) => {
            // tests may wish to pretend there's a delay
            waits.sleep(naming_table_load_info.test_delay);
            Outcome::Success(naming_table_load_info.path.clone())
        }
    }
}

/// `State_loader_lwt.FromDisk.load_result`
pub struct FromDiskLoadResult {
    pub naming_table_path: path::T,
    pub warning_saved_state_path: path::T,
    pub files_changed: ChangedFiles,
}

/// We might find a saved-state available for download, and download it.
///
/// (`State_loader_lwt.load` of the open-source build returns
/// `Error "Not implemented"`.)
fn init_via_fetch(ignore_hh_version: bool) -> Outcome<FromDiskLoadResult> {
    let _ = ignore_hh_version;
    let load_result: Result<FromDiskLoadResult, load_error::T> = Err("Not implemented".to_string());
    match load_result {
        Ok(r) => Outcome::Success(r),
        Err(load_error) => Outcome::Failure(error_from_load_error(&load_error)),
    }
}

/// `Naming_table_builder_ffi_externs.build_result`
struct BuildResult {
    exit_status: i32,
    si_addenda: Vec<(RelativePath, Vec<SiAddendum>)>,
}

/// `naming_table_builder_ffi_build` + `poll_exn`: the build runs on a
/// thread of its own (as the FFI's does), polled every 0.1 s. An error of
/// the build is the exception of `poll_exn` (`unwrap_ocaml`).
fn poll_build_until_complete_exn(waits: &mut Waits<'_>, www: &str, custom_hhi_path: &str, output: &str) -> BuildResult {
    let (tx, rx) = std::sync::mpsc::channel();
    let (www, hhi, output) = (
        std::path::PathBuf::from(www),
        std::path::PathBuf::from(custom_hhi_path),
        std::path::PathBuf::from(output),
    );
    std::thread::spawn(move || {
        // TODO: an atomic rename would probably be more robust here.
        let result = (|| {
            if output.exists() {
                std::fs::remove_file(&output)?;
            }
            naming_table_builder::build_naming_table_ide(&www, &hhi, &output)
        })();
        let _ = tx.send(result);
    });
    let rec_poll = |waits: &mut Waits<'_>| loop {
        match rx.try_recv() {
            Ok(result) => return result,
            Err(std::sync::mpsc::TryRecvError::Empty) => waits.sleep(0.1),
            Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                return Err(anyhow::anyhow!("naming table build thread exited"));
            }
        }
    };
    match rec_poll(waits) {
        Ok((exit_status, si_addenda)) => BuildResult {
            exit_status: exit_status.as_code(),
            si_addenda,
        },
        // `unwrap_ocaml`: an OCaml `Failure` with the error's text.
        Err(err) => std::panic::panic_any(format!("Failure(\"{:#}\")", err)),
    }
}

/// Performs a full index of [root], building a naming table on disk,
/// and then loading it. Also returns [si_addenda] from what we gathered
/// during the full index.
fn init_via_build(
    waits: &mut Waits<'_>,
    config: &server_config::T,
    root: &path::T,
    hhi_root: &path::T,
) -> Outcome<(path::T, symbol_index_core::PathsWithAddenda)> {
    let path = path::make(&crate::server_files::client_ide_naming_table(root));
    if !server_config::ide_fall_back_to_full_index(config) {
        Outcome::Skip("ide_fallback_to_full_index=false".to_string())
    } else {
        let build_result = poll_build_until_complete_exn(waits, root, hhi_root, &path);
        match build_result {
            BuildResult {
                exit_status: 0,
                si_addenda,
            } => {
                let paths_with_addenda = si_addenda
                    .into_iter()
                    .map(|(path, addenda)| (path, addenda, search_utils::FileSource::TypeChecker))
                    .collect();
                Outcome::Success((path, paths_with_addenda))
            }
            BuildResult { exit_status, .. } => {
                let data = Some(yojson::T::Assoc(vec![(
                    "naming_table_builder_exit_status".to_string(),
                    yojson::T::Int(exit_status as isize),
                )]));
                Outcome::Failure(client_ide_utils::make_rich_error(data, None, "full_index_error"))
            }
        }
    }
}

/// Attempt to find the naming table and warning saved state
/// on disk.
///
/// (`State_loader_lwt.get_project_metadata` of the open-source build
/// returns `Error ("Not implemented", telemetry)`.)
fn init_via_find(
    local_config: &server_local_config::T,
    root: &path::T,
    ignore_hh_version: bool,
) -> Outcome<FromDiskLoadResult> {
    let _ = (root, ignore_hh_version);
    if !local_config.ide_load_naming_table_on_disk {
        Outcome::Skip("ide_load_naming_table_on_disk=false".to_string())
    } else {
        let project_metadata: Result<(), (load_error::T, telemetry::T)> =
            Err(("Not implemented".to_string(), telemetry::create()));
        match project_metadata {
            Err((load_error, _telemetry)) => Outcome::Failure(error_from_load_error(&load_error)),
            Ok(()) => unreachable!(),
        }
    }
}

pub struct SavedStatePaths {
    pub naming_table_path: path::T,
    pub warnings_saved_state_path: Option<path::T>,
}

type AttemptResult = Result<
    (
        telemetry::T,
        naming_table::T,
        Option<WarningsSavedState>,
        ChangedFiles,
        search_utils::SiEnv,
    ),
    (telemetry::T, RichError),
>;

/// `Warnings_saved_state.read_from_disk path`: `Marshal.from_channel` of an
/// `ErrorHashSet.t` (a `Set.Make(int)`).
fn read_warnings_saved_state_from_disk(path: &str) -> WarningsSavedState {
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(err) => panic!("Sys_error(\"{}: {}\")", path, err),
    };
    let value = match crate::rt::ocaml_marshal::from_bytes(&bytes, 0) {
        Ok(value) => value,
        Err(err) => panic!("Failure(\"input_value: {:?}\")", err),
    };
    match crate::rt::ocaml_marshal::ocaml_set::elements_of_ocaml(&value) {
        Ok(elements) => elements
            .into_iter()
            .filter_map(|v| v.as_int().ok().map(|i| i as isize))
            .collect(),
        Err(err) => panic!("Failure(\"input_value: {:?}\")", err),
    }
}

/// This is a helper function used to add logging+telemetry to each
/// attempt at initializing the symbol table. Used like this:
/// [let%lwt result = attempt ... |> map_attempt key ~telemetry ~prev ~f]
/// Here [attempt ...] returns an Lwt.t representing the attempt that has been
/// kicked off. The return of [map_attempt] is a wrapper promise around that
/// underlying promise, one which adds logging and telemetry, including
/// any unhandled exceptions.
///
/// (`promise` is the attempt, run here.)
fn map_attempt<A>(
    key: &str,
    ctx: &provider_context::T,
    prev: (telemetry::T, RichError),
    f: impl FnOnce(A) -> (SavedStatePaths, ChangedFiles, search_utils::SiEnv),
    promise: impl FnOnce() -> Outcome<A>,
) -> AttemptResult {
    let start_time = crate::rt::ocaml_unix::gettimeofday();
    let (telemetry, prev_error) = prev;
    hh_logger::log(&format!("Init: {}?", key));
    let attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let result = promise();
        match result {
            Outcome::Success(a) => {
                let (
                    SavedStatePaths {
                        naming_table_path,
                        warnings_saved_state_path,
                    },
                    changed_files,
                    sienv,
                ) = f(a);
                hh_logger::log(&format!(
                    "Init: {} ok, at {}, {} changed_files",
                    key,
                    path::to_string(&naming_table_path),
                    changed_files.len()
                ));
                let naming_table = load_naming_table(ctx, &path::to_string(&naming_table_path));
                let warnings_saved_state = warnings_saved_state_path
                    .map(|path| read_warnings_saved_state_from_disk(&path::to_string(&path)));
                Ok((naming_table, warnings_saved_state, changed_files, sienv))
            }
            Outcome::Skip(reason) => Err(Ok(reason)),
            Outcome::Failure(reason) => Err(Err(reason)),
        }
    }));
    match attempt {
        Ok(Ok((naming_table, warnings_saved_state, changed_files, sienv))) => {
            let telemetry = telemetry::string_(None, key, "winner", telemetry);
            let telemetry = telemetry::duration(None, start_time, None, telemetry);
            Ok((telemetry, naming_table, warnings_saved_state, changed_files, sienv))
        }
        Ok(Err(Ok(reason))) => {
            hh_logger::log(&format!("Init: {} skipped - {}", key, reason));
            let telemetry = telemetry::string_(None, key, &reason, telemetry);
            Err((telemetry, prev_error))
        }
        Ok(Err(Err(reason))) => {
            let RichError { category, data, .. } = &reason;
            let data = data.clone().unwrap_or(yojson::T::Null);
            hh_logger::log(&format!(
                "Init: {} error - {} - {}",
                key,
                category,
                crate::yojson::safe::to_string(&data)
            ));
            let sub = telemetry::create();
            let sub = telemetry::duration(None, start_time, None, sub);
            let sub = telemetry::string_(None, "error", category, sub);
            let sub = telemetry::json("data", data, sub);
            let telemetry = telemetry::object_(key, sub, telemetry);
            Err((telemetry, reason))
        }
        Err(payload) => {
            let e = exception::wrap(payload);
            // unhandled exception from the attempt itself, or from loading the found sqlite
            let reason = client_ide_utils::make_rich_error(None, Some(&e), &format!("{} exn", key));
            hh_logger::log(&format!("Init: {} exn - {}", key, exception::to_string(&e)));
            let sub = telemetry::create();
            let sub = telemetry::duration(None, start_time, None, sub);
            let telemetry = telemetry::object_(key, sub, telemetry);
            Err((telemetry, reason))
        }
    }
}

/// `Naming_table.load_from_sqlite ctx path` (the OCaml raises its errors).
pub fn load_naming_table(ctx: &provider_context::T, db_path: &str) -> naming_table::T {
    match naming_table::load_from_sqlite(ctx, db_path) {
        Ok(naming_table) => naming_table,
        Err(err) => panic!("{:?}", err),
    }
}

/// "Initialization" for clientIdeDaemon means:
/// - setting up naming-table
/// - setting up the search-index
/// - loading the warnings saved state
/// - figuring out what files have changed and need to be indexed.
///
/// For the naming table part, we use a strategy of LSP/FIND/FETCH/BUILD:
///
/// 1. LSP: If the LSP initialization request contains the path of a
///    naming-table then use it, trust that there are no files changed since
///    that saved-state, and initialize sienv empty. This is only used for
///    tests at time of writing.
/// 2. FIND: Otherwise, (if ide_load_naming_table_on_disk) look for any
///    saved-state already on disk in the canonical location /tmp/hh_server
///    that's within an age threshold, and if found then use it, ask mercurial
///    for files changed since that saved-state, and initialize sienv empty
/// 3. FETCH: Otherwise, try [State_loader_lwt.load] which uses manifold to
///    look for the best saved-state. If one is found then download it, ask
///    mercurial for files changed since that saved-state, and initialize
///    sienv empty
/// 4. BUILD: Otherwise, if .hhconfig allows fall_back_to_full_index (default
///    true) then do a fast multi-core build of the naming-table-sqlite,
///    initialize the naming-table with that, deem that there are no files
///    changed since the build, and initialize sienv with all the symbols that
///    we parsed while building the full naming table
/// 5. Otherwise, error.
///
/// If a step determines that it's got an sqlite file path, but we
/// subsequently error while trying to open the sqlite file (e.g. it has zero
/// size) then that counts as failure and we continue on to the next attempt.
/// Weird but true.
///
/// (`init ~config ~local_config ~param ~hhi_root ~local_memory`: the naming
/// table, warnings saved state and symbol index of the daemon; see the
/// module doc.) `ctx` is the daemon's context (its backend is the
/// `local_memory`).
pub fn init(
    waits: &mut Waits<'_>,
    config: &server_config::T,
    local_config: &server_local_config::T,
    param: &client_ide_message::initialize_from_saved_state::T,
    hhi_root: &path::T,
    ctx: &provider_context::T,
) -> Result<InitResult, RichError> {
    let _start_time = crate::rt::ocaml_unix::gettimeofday();
    let client_ide_message::initialize_from_saved_state::T {
        root,
        naming_table_load_info,
        warnings_saved_state_path,
        ignore_hh_version,
        config: _,
        open_files: _,
    } = param;
    let tcopt = server_config::typechecker_options(config);
    let gleanopt = server_config::glean_options(config);
    let sienv = symbol_index::initialize(
        &gleanopt,
        &tcopt.po.auto_namespace_map,
        &local_config.ide_symbolindex_search_provider,
        local_config.symbolindex_quiet,
    );

    // (How this code handles errors: see the OCaml. We will make several
    // attempts using different techniques, in order, to try to find a
    // saved-state, and use the first attempt to succeed.)

    // As mentioned, Skip will result in the previous error message falling through.
    // So we have to seed with an initial [prev] -- even though some of the attempts never
    // return Skip and so this [prev] never makes its way through to the end!
    let prev = (
        telemetry::create(),
        client_ide_utils::make_rich_error(None, None, "trying..."),
    );

    // LSP: Are the paths specified in the LSP initialize message?
    let result = map_attempt(
        "lsp",
        ctx,
        prev,
        |naming_table_path| {
            (
                SavedStatePaths {
                    naming_table_path,
                    warnings_saved_state_path: warnings_saved_state_path.clone(),
                },
                vec![],
                sienv.clone(),
            )
        },
        || init_via_lsp(waits, naming_table_load_info),
    );
    let with_sienv = |FromDiskLoadResult {
                          naming_table_path,
                          warning_saved_state_path,
                          files_changed,
                      }| {
        (
            SavedStatePaths {
                naming_table_path,
                warnings_saved_state_path: Some(warning_saved_state_path),
            },
            files_changed,
            sienv.clone(),
        )
    };
    // FIND: Find on disk?
    let result = match result {
        Ok(_) => result,
        Err(prev) => map_attempt("find", ctx, prev, with_sienv, || {
            init_via_find(local_config, root, *ignore_hh_version)
        }),
    };
    // FETCH
    let result = match result {
        Ok(_) => result,
        Err(prev) => map_attempt("fetch", ctx, prev, with_sienv, || init_via_fetch(*ignore_hh_version)),
    };
    // BUILD
    let result = match result {
        Ok(_) => result,
        Err(prev) => map_attempt(
            "build",
            ctx,
            prev,
            |(naming_table_path, paths_with_addenda): (path::T, symbol_index_core::PathsWithAddenda)| {
                let sienv = symbol_index_core::update_from_addenda(&sienv, &paths_with_addenda);
                (
                    SavedStatePaths {
                        naming_table_path,
                        warnings_saved_state_path: None,
                    },
                    vec![],
                    sienv,
                )
            },
            || init_via_build(waits, config, root, hhi_root),
        ),
    };
    match result {
        Ok((_telemetry, naming_table, warnings_saved_state, changed_files, sienv)) => {
            // (`Hack_event_logger.serverless_ide_load_naming_table`: no-op.)
            Ok(InitResult {
                naming_table,
                warnings_saved_state,
                sienv,
                changed_files,
            })
        }
        Err((_telemetry, e)) => Err(e),
    }
}
