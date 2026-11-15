// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/provider_context.ml`. See `hh/PORTING.md`.
//!
//! `Provider_context.t` is `Arc<Ctx>` ([`T`]): the record of the OCaml is the
//! `Ctx` (`crate::ctx`), whose fields are
//!
//! - `popt`: `Ctx::parser_env.parser_options` (the options the parser is
//!   given; `map_tcopt` does not change them, as it does not change `popt`);
//! - `tcopt`: `Ctx::tco`;
//! - `backend`: the stores of the `Ctx` (`Ctx::files`, `Ctx::shallow_decls`,
//!   `Ctx::folded_decls`), which stand for the heaps of the `Shared_memory`
//!   backend of `hh_server` and `hh_single_type_check`, or, for a `Ctx` made
//!   by `Ctx::new_local_memory`, the caches of the IDE daemon's
//!   `Local_memory` backend (`crate::provider_backend`). Where a function
//!   matches on the backend, those two branches are ported. `get_backend` is
//!   `Ctx::get_backend`, and `empty_for_tool` is part of
//!   `Ctx::new_local_memory`; `set_backend` and
//!   `ctx_with_pessimisation_info_exn` (a backend is chosen when the `Ctx` is
//!   made; `Pessimised_shared_memory` is not ported) are not here.
//! - `deps_mode`: `Ctx::deps_mode`;
//! - `entries`: `Ctx::entries`.
//!
//! A `Ctx` is shared by the threads that check files, so an [`Entry`] is
//! `Send` and `Sync`: its mutable fields are behind a `Mutex`. `cst`
//! (`PositionedSyntaxTree.t`) is the root of the parser's positioned syntax
//! tree, `parser_core_types::positioned_syntax::PositionedSyntax`, shared
//! (`Arc`); the module `PositionedSyntaxTree` is not here. `tast` (a TAST
//! holds types, which are not `Send`) is kept per thread:
//! [`get_entry_tast`], [`set_entry_tast`].
//!
//! A context with entries has local changes of its own over the decl stores
//! of the context it was made from: see [`local_changes`].
//!
//! The file contents of an entry are bytes (`BString`), as an OCaml string
//! is: a Hack file need not be UTF-8.

use std::cell::RefCell;
use std::path::Path;
use std::sync::Arc;
use std::sync::Mutex;

use bstr::BString;
use oxidized::package_info::PackageInfo;
use oxidized::parser_options::ParserOptions;
use oxidized::typechecker_options::TypecheckerOptions;
use relative_path::Prefix;
use relative_path::RelativePath;
use ty::decl::ty::FunElt;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::exception;
use crate::full_fidelity_source_text;
use crate::parser_return;
use crate::telemetry;
use crate::typing_deps::mode as typing_deps_mode;
use crate::utils::Callstack;

/// `Provider_context.t`
pub type T = Arc<Ctx>;

/// Represents the file contents for a given entry. We may lazily load the
/// file contents from disk, depending on how the entry is constructed.
#[derive(Debug)]
pub enum EntryContents {
    /// We've been provided a file path, but have not yet requested the
    /// contents to be read from disk. They will be read from disk the next
    /// time it is requested.
    NotYetReadFromDisk,
    /// Terminal state. We transitioned from [NotYetReadFromDisk] into
    /// this state after reading the file from disk. Do not construct directly;
    /// use [ProvidedContents] instead.
    ContentsFromDisk(BString),
    /// Terminal state. The file contents were provided explicitly when
    /// this entry was constructed. We will not read from disk.
    ProvidedContents(BString),
    /// Terminal state. We transitioned from [NotYetReadFromDisk] into
    /// this state after attempting to read the file from disk, but
    /// encountering an exception.
    ReadContentsFromDiskFailed(exception::T),
    /// Terminal state. Raise an exception on an attempt to read the file
    /// contents from this file.
    RaiseExnOnAttemptToRead,
}

/// Various information associated with a given file.
///
/// It's important to create an [entry] when processing data about a single file for
/// two reasons:
///
///   - To ensure that subsequent operations on the same file have a consistent view
///     of the same file. That is, they won't read the file from disk twice and
///     potentially introduce a race condition.
///   - To ensure that subsequent operations on the same file don't recalculate the
///     same data (such as an AST). This is important for performance, particularly
///     for IDE operation latency.
///
/// To create a new entry for a file, use [Provider_context.add_entry].
///
/// There should generally be no more than one entry inside the [Provider_context.t]
/// at a given time. Once you're done processing a file (e.g. you have the TAST and
/// don't need to access further data), then you should discard the [entry] and the
/// [Provider_context.t] that it came from.
///
/// All of these fields are monotonic, unless otherwise noted. They only
/// transition forward through states, never backwards (e.g. from None -> Some),
/// and don't lose information in doing so. Monotonic fields don't need to be
/// invalidated.
///
/// An entry is shared (`Arc`), as the OCaml record is.
#[derive(Debug)]
pub struct Entry {
    pub path: RelativePath,
    /// Derived from file contents of [path], which was possibly read from disk.
    pub contents: Mutex<EntryContents>,
    /// Derived from [contents]; contains additional preprocessing.
    pub source_text: Mutex<Option<full_fidelity_source_text::T>>,
    /// this parser_return, if present, came from source_text via Ast_provider.parse
    /// under ~full:true
    pub parser_return: Mutex<Option<parser_return::T>>,
    /// same invariant as parser_return
    pub ast_diagnostics: Mutex<Option<crate::diagnostics::T>>,
    /// Derived from [source_text]; the root of the positioned syntax tree
    /// (`Ast_provider.compute_cst`).
    pub cst: Mutex<Option<Arc<parser_core_types::positioned_syntax::PositionedSyntax>>>,
    /// NOT monotonic for the same reason as [tast].
    pub all_diagnostics: Mutex<Option<crate::diagnostics::T>>,
    /// Which computation stored [all_diagnostics] (a new number each time):
    /// stands for the OCaml's physical identity of the stored value
    /// (`phys_equal` in `ClientIdeDaemon`'s `Code_action`).
    pub all_diagnostics_generation: std::sync::atomic::AtomicU64,
    /// `Identify_symbol_service.all_symbols_ctx`
    pub symbols: Mutex<Option<Vec<crate::identify_symbol_service::Elt>>>,
}

/// The source of [`Entry::all_diagnostics_generation`].
pub static ALL_DIAGNOSTICS_GENERATIONS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// A `Ctx` (which holds the entries) is shared between threads.
const _: fn() = assert_send_sync::<Entry>;

fn assert_send_sync<A: Send + Sync>() {}

/// We often operate on collection of entries.
pub type Entries = crate::relative_path::map::T<Arc<Entry>>;

/// The context that `empty_for_worker`, `empty_for_test` and
/// `empty_for_debugging` make (the OCaml has the same record in each).
///
/// Its backend is `Provider_backend.Shared_memory` in OCaml: the heaps of the
/// process, which every context reads. A `Ctx` has stores of its own, and
/// these start empty. Its files are read under the root of the paths
/// (`Relative_path.path_of_prefix Root`), or relative to the current
/// directory when that is not set yet (OCaml raises when it reads a file then).
fn empty_shared_memory(
    popt: ParserOptions,
    tcopt: TypecheckerOptions,
    deps_mode: typing_deps_mode::T,
) -> T {
    let root = crate::relative_path::path_of_prefix(Prefix::Root).unwrap_or_default();
    let mut ctx = match Ctx::new(Path::new(&root), tcopt) {
        Ok(ctx) => ctx,
        Err(err) => panic!("Provider_context: cannot make a context: {}", err),
    };
    // `popt`: the decl parser reads it too (`Direct_decl_utils`).
    ctx.decl_parser = decl_parser::DeclParser::new(
        Arc::clone(&ctx.files) as Arc<dyn ::file_provider::FileProvider>,
        oxidized::decl_parser_options::DeclParserOptions::from_parser_options(&popt),
    );
    ctx.parser_env.parser_options = popt;
    ctx.deps_mode = deps_mode;
    Arc::new(ctx)
}

/// The empty context, for use with Multiworker workers. This assumes that the
/// backend is shared memory. We don't want to serialize and send the entire
/// [Server_env.env] to these workers because a [Server_env.env] contains large data
/// objects (such as the forward naming table).
pub fn empty_for_worker(
    popt: ParserOptions,
    tcopt: TypecheckerOptions,
    deps_mode: typing_deps_mode::T,
) -> T {
    empty_shared_memory(popt, tcopt, deps_mode)
}

/// The empty context, for use in tests, where there may not be a
/// [Server_env.env] available.
pub fn empty_for_test(
    popt: ParserOptions,
    tcopt: TypecheckerOptions,
    deps_mode: typing_deps_mode::T,
) -> T {
    empty_shared_memory(popt, tcopt, deps_mode)
}

/// The empty context, for use in debugging aides in production code, where
/// there may not be a [Server_env.env] available.
pub fn empty_for_debugging(
    popt: ParserOptions,
    tcopt: TypecheckerOptions,
    deps_mode: typing_deps_mode::T,
) -> T {
    empty_shared_memory(popt, tcopt, deps_mode)
}

/// Creates an entry.
pub fn make_entry(path: RelativePath, contents: EntryContents) -> Arc<Entry> {
    Arc::new(Entry {
        path,
        contents: Mutex::new(contents),
        source_text: Mutex::new(None),
        parser_return: Mutex::new(None),
        ast_diagnostics: Mutex::new(None),
        cst: Mutex::new(None),
        all_diagnostics: Mutex::new(None),
        all_diagnostics_generation: std::sync::atomic::AtomicU64::new(0),
        symbols: Mutex::new(None),
    })
}

/// Adds the entry into the supplied [Provider_context.t], overwriting
/// if the context already had an entry of the same path, and returns a new
/// [Provider_context.t] which includes that entry.
/// Note: for most callers, [add_entry_if_missing] is more appropriate.
///
/// The new context has local changes of its own over the stores of `ctx`
/// (see [`local_changes`]).
pub fn add_or_overwrite_entry(ctx: &T, entry: Arc<Entry>) -> T {
    local_changes::with_entries(ctx, ctx.entries.update(entry.path.clone(), entry))
}

/// Similar to [add_or_overwrite_entry], but makes a new entry with contents.
/// Also returns the new entry for convenience.  It's important that
/// callers use the resulting [Provider_context.t]. That way, if a
/// subsequent operation tries to access data about the same file, it will get
/// the [entry] we just added rather than reading from disk.
pub fn add_or_overwrite_entry_contents(
    ctx: &T,
    path: RelativePath,
    contents: BString,
) -> (T, Arc<Entry>) {
    let entry = make_entry(path, EntryContents::ProvidedContents(contents));
    (add_or_overwrite_entry(ctx, Arc::clone(&entry)), entry)
}

/// Similar to [add_entry], but (1) returns the existing entry if one
/// was already there, (2) if one wasn't there, then adds a new entry
/// by reading the contents of the path from disk; may throw if those
/// contents can't be read.
pub fn add_entry_if_missing(ctx: &T, path: RelativePath) -> (T, Arc<Entry>) {
    match ctx.entries.get(&path) {
        Some(entry) => (Arc::clone(ctx), Arc::clone(entry)),
        None => {
            // The OCaml extracts the hhi files to a directory (the `Hhi`
            // prefix) and reads them from there; here they are not on disk
            // but in the context's files (`Ctx::new`, `hh single`'s
            // builtins): their contents are read from there.
            let contents = match path.prefix() {
                crate::relative_path::Prefix::Hhi => {
                    match ::file_provider::FileProvider::get(&*ctx.files, pos::RelativePath::from(&path)) {
                        Ok(contents) => EntryContents::ContentsFromDisk(contents),
                        Err(_) => EntryContents::NotYetReadFromDisk,
                    }
                }
                _ => EntryContents::NotYetReadFromDisk,
            };
            let entry = make_entry(path, contents);
            (add_or_overwrite_entry(ctx, Arc::clone(&entry)), entry)
        }
    }
}

/// Get the [ParserOptions.t] contained within the [t].
pub fn get_popt(t: &T) -> &ParserOptions {
    &t.parser_env.parser_options
}

/// Get the [TypecheckerOptions.t] contained within the [t].
/// Get the [TypecheckerOptions.t] contained within the [t].
// (A reference: cloning the `Arc`, which all the threads share, at each
// call would write its count from every thread. Callers clone if they keep it.)
pub fn get_tcopt(t: &T) -> &Arc<TypecheckerOptions> {
    &t.tco
}

pub fn get_package_info(t: &T) -> &PackageInfo {
    &t.parser_env.parser_options.package_info
}

/// Update the [TypecheckerOptions.t] contained within the [t].
pub fn map_tcopt(t: &T, f: impl FnOnce(TypecheckerOptions) -> TypecheckerOptions) -> T {
    Arc::new(Ctx {
        tco: Arc::new(f(TypecheckerOptions::clone(&t.tco))),
        ..Ctx::clone(t)
    })
}

/// `map_tcopt t ~f:(fun _ -> tcopt)` for options that are already shared:
/// the context itself when these are its options (the common case: a typed
/// AST is checked with the options it was made with), and otherwise a
/// context that shares them, without copying the options.
pub fn with_tcopt(t: &T, tcopt: &Arc<TypecheckerOptions>) -> T {
    if Arc::ptr_eq(&t.tco, tcopt) {
        Arc::clone(t)
    } else {
        Arc::new(Ctx {
            tco: Arc::clone(tcopt),
            ..Ctx::clone(t)
        })
    }
}

/// Get the [Typing_deps_mode.t] that backs this [t].
pub fn get_deps_mode(t: &T) -> typing_deps_mode::T {
    t.deps_mode.clone()
}

/// Update the [Typing_deps_mode.t] that backs this [t].
pub fn map_deps_mode(t: &T, f: impl FnOnce(typing_deps_mode::T) -> typing_deps_mode::T) -> T {
    Arc::new(Ctx {
        deps_mode: f(t.deps_mode.clone()),
        ..Ctx::clone(t)
    })
}

/// Get the entries currently contained in this [t].
pub fn get_entries(t: &T) -> Entries {
    t.entries.clone()
}

/// `Sys_utils.cat`, which is `Disk.cat` (`Real_disk.cat`): the contents of a
/// file, read in binary. When it cannot be read, it raises `Sys_error` (its
/// message, as `Printexc.to_string` gives it, is the payload of the panic).
fn sys_utils_cat(filename: &str) -> BString {
    match std::fs::read(filename) {
        Ok(contents) => BString::from(contents),
        Err(err) => std::panic::resume_unwind(Box::new(format!(
            "Sys_error(\"{}: {}\")",
            filename,
            // the `strerror` text, as OCaml's `Sys_error` message
            match err.raw_os_error() {
                // SAFETY: `strerror` returns a static string for any errno.
                Some(errno) => unsafe { std::ffi::CStr::from_ptr(libc::strerror(errno)) }
                    .to_string_lossy()
                    .into_owned(),
                None => err.to_string(),
            }
        ))),
    }
}

/// Same as [read_file_contents], but raises an exception if the file contents
/// could not be read.
///
/// Idempotent: future calls to this function will return the same value or raise
/// the same exception.
pub fn read_file_contents_exn(entry: &Entry) -> BString {
    let mut contents = entry.contents.lock().unwrap();
    match &*contents {
        EntryContents::ProvidedContents(contents) | EntryContents::ContentsFromDisk(contents) => {
            contents.clone()
        }
        EntryContents::NotYetReadFromDisk => {
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                sys_utils_cat(&crate::relative_path::to_absolute(&entry.path))
            })) {
                Ok(new_contents) => {
                    *contents = EntryContents::ContentsFromDisk(new_contents.clone());
                    new_contents
                }
                Err(e) => {
                    // Be sure to capture the exception and mark the entry contents as
                    // [Read_contents_from_disk_failed]. Otherwise, reading the contents may
                    // not be idempotent:
                    //
                    //  1) We attempt to read the file from disk, but it doesn't exist, so we
                    //  raise an exception.
                    //  2) The file is created on disk.
                    //  3) We attempt to read the file from disk again. Now it exists, and we
                    //  return a different value.
                    let e = exception::wrap(e);
                    let message = exception::get_ctor_string(&e);
                    *contents = EntryContents::ReadContentsFromDiskFailed(e);
                    drop(contents);
                    std::panic::resume_unwind(Box::new(message))
                }
            }
        }
        EntryContents::RaiseExnOnAttemptToRead => {
            drop(contents);
            panic!(
                "Entry {} was marked as Raise_exn_on_attempt_to_read, but an attempt was made to read its contents",
                crate::relative_path::to_absolute(&entry.path)
            )
        }
        EntryContents::ReadContentsFromDiskFailed(e) => {
            // `Exception.reraise e`: the payload of a panic cannot be copied,
            // so the exception raised again is its message
            // (`Exception.get_ctor_string`, its `Printexc.to_string`), which
            // is the payload of the panic that was caught.
            let message = exception::get_ctor_string(e);
            drop(contents);
            std::panic::resume_unwind(Box::new(message))
        }
    }
}

/// Return the contents for the file backing this entry. This may involve a
/// disk read if the [entry_contents] are backed by disk. Consequently, this
/// function may fail and return [None].
///
/// Idempotent: future calls to this function will return the same value.
pub fn read_file_contents(entry: &Entry) -> Option<BString> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| read_file_contents_exn(entry))).ok()
}

/// Get the file contents from this entry if they've already been computed,
/// otherwise return [None]. This is mostly useful for telemetry, which doesn't
/// want to trigger a file-read event.
pub fn get_file_contents_if_present(entry: &Entry) -> Option<BString> {
    match &*entry.contents.lock().unwrap() {
        EntryContents::ProvidedContents(contents) | EntryContents::ContentsFromDisk(contents) => {
            Some(contents.clone())
        }
        EntryContents::NotYetReadFromDisk
        | EntryContents::RaiseExnOnAttemptToRead
        | EntryContents::ReadContentsFromDiskFailed(_) => None,
    }
}

thread_local! {
    /// ref_is_quarantined stores the stack at which it was last changed,
    /// so we can give better failwith error messages where appropriate.
    ///
    /// A global `ref` of the OCaml process. The quarantine is entered and
    /// left around work done on one thread
    /// (`Provider_utils.respect_but_quarantine_unsaved_changes`), and the
    /// local changes it pushes are those of the caches of that thread (see
    /// `crate::ast_provider`): it is a flag of the thread.
    static REF_IS_QUARANTINED: RefCell<(bool, Callstack)> =
        RefCell::new((false, Callstack("init".to_string())));
}

/// Not in the OCaml (whose worker process fails, and is started afresh):
/// after a panic was caught in the check of a file, the thread is not
/// quarantined (see `crate::rt::decl_epoch::after_panic`).
pub fn reset_quarantine_after_panic() {
    REF_IS_QUARANTINED.with_borrow_mut(|ref_is_quarantined| {
        *ref_is_quarantined = (false, Callstack("after_panic".to_string()))
    })
}

/// Are we within [Provider_utils.respect_but_quarantine_unsaved_changes] ?
pub fn is_quarantined() -> bool {
    REF_IS_QUARANTINED.with_borrow(|(is_quarantined, _)| *is_quarantined)
}

/// Called by [Provider_utils.respect_but_quarantine_unsaved_changes] upon entry.
/// Don't call it directly yourself.
pub fn set_is_quarantined_internal() {
    REF_IS_QUARANTINED.with_borrow_mut(|ref_is_quarantined| match ref_is_quarantined {
        (true, Callstack(stack)) => {
            panic!("set_is_quarantined: was already quarantined at\n{}", stack)
        }
        (false, _) => {
            *ref_is_quarantined = (
                true,
                Callstack(exception::get_current_callstack_string(99)),
            )
        }
    })
}

/// Called by [Provider_utils.respect_but_quarantine_unsaved_changes] upon exit.
/// Don't call it directly yourself.
pub fn unset_is_quarantined_internal() {
    REF_IS_QUARANTINED.with_borrow_mut(|ref_is_quarantined| match ref_is_quarantined {
        (true, _) => {
            *ref_is_quarantined = (
                false,
                Callstack(exception::get_current_callstack_string(99)),
            )
        }
        (false, Callstack(stack)) => panic!(
            "unset_is_quarantined: but quarantine had already been released at\n{}",
            stack
        ),
    })
}

/// Telemetry for a provider_context includes the current cache state of its backend,
/// plus 'counters' like how many times cache has been read or evicted.
pub fn get_telemetry(t: &T) -> telemetry::T {
    let entries_telemetry = telemetry::int_(
        "count",
        t.entries.len() as isize,
        telemetry::create(),
    );
    let size = t.entries.iter().fold(0, |acc, (_path, entry)| {
        let contents = get_file_contents_if_present(entry).unwrap_or_default();
        acc + contents.len() as isize
    });
    let entries_telemetry = telemetry::int_("size", size, entries_telemetry);
    let telemetry = telemetry::object_("entries", entries_telemetry, telemetry::create());
    // `Provider_backend.t_to_string`: the backend of `hh_server` and
    // `hh_single_type_check` in this version of the OCaml (`rust_provider_backend`
    // is turned off without `shm_use_sharded_hashtbl`, and is a stub in the
    // open-source build), whose semantics the stores of a `Ctx` and their
    // local changes follow.
    let telemetry = telemetry::string_(
        None,
        "backend",
        crate::provider_backend::t_to_string(&t.get_backend()),
        telemetry,
    );
    // We get Shared_mem telemetry for all providers, not just the Shared_mem
    // provider, just in case there are code paths which use Shared_mem despite
    // it not being the intended provider.
    //
    // (`Shared_mem.SMTelemetry.get_telemetry`, the sizes of the shared-memory
    // heaps, has no counterpart: nothing is added.)
    //
    match t.local_memory() {
        // `Provider_backend.Local_memory`
        Some(local_memory) => {
            let telemetry = local_memory
                .decl_cache
                .lock()
                .unwrap()
                .get_telemetry("decl_cache", telemetry);
            let telemetry = match &*local_memory.decls_reflect_this_file.lock().unwrap() {
                None => telemetry,
                Some((path, file_info, pfh_hash)) => {
                    // (`Int64.Hex.to_string` of Core: `0x..`, `-0x..`.)
                    let hex = if *pfh_hash < 0 {
                        format!("-0x{:x}", (*pfh_hash as i128).unsigned_abs())
                    } else {
                        format!("0x{:x}", pfh_hash)
                    };
                    let value = format!(
                        "{} [{}] #{}",
                        crate::relative_path::suffix(path),
                        crate::file_info::to_string(file_info),
                        hex
                    );
                    telemetry::string_(None, "decls_for_file", &value, telemetry)
                }
            };
            let telemetry = local_memory
                .shallow_decl_cache
                .lock()
                .unwrap()
                .get_telemetry("shallow_decl_cache", telemetry);
            let telemetry = local_memory
                .folded_class_cache
                .lock()
                .unwrap()
                .get_telemetry("folded_class_cache", telemetry);
            let telemetry = crate::provider_backend::reverse_naming_table_delta::get_telemetry(
                "reverse_naming_table_delta",
                &local_memory.reverse_naming_table_delta,
                telemetry,
            );
            // (`Fixmes.get_telemetry`: the fixmes of this backend are the
            // per-thread tables of `diagnostics`, not counted here: the
            // OCaml adds nothing when it has none.)
            telemetry::int_(
                "dep_table_entry_count",
                local_memory.dep_table.lock().unwrap().len() as isize,
                telemetry,
            )
        }
        // The backend is not `Provider_backend.Local_memory`: then the result
        // is `telemetry` itself.
        None => telemetry,
    }
}

/// This function resets the 'counters' associated with telemetry.
pub fn reset_telemetry(t: &T) {
    // Only a `Provider_backend.Local_memory` backend has counters to reset:
    // `| _ -> ()`.
    if let Some(local_memory) = t.local_memory() {
        local_memory.decl_cache.lock().unwrap().reset_telemetry();
        local_memory.shallow_decl_cache.lock().unwrap().reset_telemetry();
        local_memory.folded_class_cache.lock().unwrap().reset_telemetry();
    }
}

/// `Provider_context.implicit_sdt_for_fun`
pub fn implicit_sdt_for_fun(ctx: &T, fe: &FunElt<R>) -> bool {
    // `Typechecker_options.everything_sdt`
    get_tcopt(ctx).po.everything_sdt && !fe.no_auto_dynamic
}

pub fn no_auto_likes_for_fun(fe: &FunElt<R>) -> bool {
    fe.no_auto_likes
}

pub fn with_tcopt_for_autocomplete(t: &T) -> T {
    let tcopt = TypecheckerOptions::clone(&t.tco);
    let tcopt = crate::typechecker_options::set_tco_autocomplete_mode(tcopt);
    let tcopt = crate::typechecker_options::set_skip_check_under_dynamic(tcopt);
    let tcopt = crate::typechecker_options::set_skip_hierarchy_checks(tcopt);
    Arc::new(Ctx {
        tco: Arc::new(tcopt),
        ..Ctx::clone(t)
    })
}

/// The typed AST of an entry (`entry.tast`, NOT monotonic: it is
/// invalidated when declarations change).
///
/// A TAST holds types, which are not `Send`, and an [`Entry`] is shared by
/// the threads of a `Ctx`: the TASTs are kept per thread, by entry, for as
/// long as the entry lives. A thread that did not compute the TAST of an
/// entry computes it again (as if it had been invalidated), which only
/// costs time.
pub type EntryTast = crate::tast_with_dynamic::T<crate::tast::Program>;

thread_local! {
    static ENTRY_TASTS: RefCell<Vec<(std::sync::Weak<Entry>, EntryTast)>> =
        const { RefCell::new(Vec::new()) };
}

/// `entry.tast`
pub fn get_entry_tast(entry: &Arc<Entry>) -> Option<EntryTast> {
    ENTRY_TASTS.with_borrow_mut(|tasts| {
        tasts.retain(|(e, _)| e.strong_count() > 0);
        tasts
            .iter()
            .find(|(e, _)| std::ptr::eq(e.as_ptr(), Arc::as_ptr(entry)))
            .map(|(_, tast)| tast.clone())
    })
}

/// `entry.tast <- tast`
pub fn set_entry_tast(entry: &Arc<Entry>, tast: Option<EntryTast>) {
    ENTRY_TASTS.with_borrow_mut(|tasts| {
        tasts.retain(|(e, _)| {
            e.strong_count() > 0 && !std::ptr::eq(e.as_ptr(), Arc::as_ptr(entry))
        });
        if let Some(tast) = tast {
            tasts.push((Arc::downgrade(entry), tast))
        }
    })
}

/// The local changes of the decl stores of a context with entries: what the
/// OCaml's `*.LocalChanges.push_stack` / `pop_stack` of the shared-memory
/// decl heaps (`Decl_provider.local_changes_push_sharedmem_stack`) give
/// `Provider_utils.respect_but_quarantine_unsaved_changes`, for the stores of
/// a `Ctx`.
///
/// # What the OCaml does (the `Shared_memory` backend of `hh_server` and
/// `hh_single_type_check`)
///
/// The decl heaps hold the declarations of the files on disk. A lookup that
/// finds a name there uses that declaration, even when an entry of the
/// context declares the name too (`Decl_provider_internals`). A lookup that
/// finds nothing asks the naming table, which looks at the entries first
/// (`Naming_provider.find_symbol_in_context_with_suppression`); when the
/// name's file is an entry, its contents are parsed and every declaration of
/// the file that wins its name is cached in the heaps
/// (`Direct_decl_utils.direct_decl_parse_and_cache`): from then on those
/// replace the declarations of the same names from the disk. Inside a
/// quarantine the heaps have a stack of local changes, which takes these
/// writes (and the classes folded meanwhile), and which is popped at the
/// end: nothing of the unsaved contents is left in the heaps.
///
/// # Here
///
/// A `Ctx` is shared by the threads of a check and its stores are only
/// written by the phases of a recheck, so a context with entries
/// (made by [`add_or_overwrite_entry`] and [`add_entry_if_missing`]) gets
/// stores of its own: a [`Layer`] over each store of the context it was made
/// from (its five shallow-decl stores and its folded classes, read through
/// that context's `ShallowDeclStore` and `FoldedDeclProvider`), with a
/// `ShallowDeclStore` and a `LazyFoldedDeclProvider` of their own (so a new
/// identity for the caches keyed by it). A layer is a stack of
/// frames in front of its fallback: reads look at the frames (newest first)
/// then the fallback; writes go to the newest frame. Frame 0 belongs to the
/// context for its lifetime (what the OCaml would write to the heaps outside
/// a quarantine stays with the context instead of reaching the stores of the
/// daemon); [`LocalChanges::push`] and [`LocalChanges::pop`] add and drop a
/// frame around a quarantine. A lookup that the fallback does not answer
/// does what the OCaml does on a miss (above), with the naming table of the
/// context the entries were added to (its stores, and the entries).
///
/// The local changes of a context are found from its `ShallowDeclStore`
/// ([`of_ctx`]): `Ctx` has no field for them.
pub mod local_changes {
    use std::collections::HashMap;
    use std::collections::HashSet;
    use std::hash::Hash;
    use std::sync::LazyLock;
    use std::sync::RwLock;
    use std::sync::Weak;

    use datastore::Store;
    use folded_decl_provider::FoldedDeclProvider;
    use folded_decl_provider::LazyFoldedDeclProvider;
    use pos::ConstName;
    use pos::FunName;
    use pos::ModuleName;
    use pos::TypeName;
    use shallow_decl_provider::EagerShallowDeclProvider;
    use shallow_decl_provider::ShallowDeclStore;
    use ty::decl::ConstDecl;
    use ty::decl::FoldedClass;
    use ty::decl::FunDecl;
    use ty::decl::ShallowClass;
    use ty::decl::TypedefDecl;
    use ty::decl::shallow::ModuleDecl;
    use ty::decl::shallow::NamedDecl;

    use super::*;
    use crate::naming_provider;

    type Fallback<K, V> = Box<dyn Fn(K) -> anyhow::Result<Option<V>> + Send + Sync>;

    /// What a lookup that the frames and the fallback did not answer does.
    type Miss<K, V> = fn(&LocalChanges, K) -> Option<V>;

    /// One store with local changes (see the module doc).
    pub struct Layer<K, V> {
        /// Frame 0, then one per [`LocalChanges::push`] not popped yet. `None`
        /// is a removed key.
        frames: RwLock<Vec<HashMap<K, Option<V>>>>,
        fallback: Fallback<K, V>,
        miss: Option<Miss<K, V>>,
        owner: Weak<LocalChanges>,
    }

    impl<K, V> std::fmt::Debug for Layer<K, V> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("Provider_context.local_changes.Layer")
        }
    }

    impl<K: Copy + Eq + Hash, V: Clone> Layer<K, V> {
        fn new(owner: Weak<LocalChanges>, fallback: Fallback<K, V>, miss: Option<Miss<K, V>>) -> Self {
            Self {
                frames: RwLock::new(vec![HashMap::new()]),
                fallback,
                miss,
                owner,
            }
        }

        fn local(&self, key: K) -> Option<Option<V>> {
            let frames = self.frames.read().unwrap();
            frames.iter().rev().find_map(|frame| frame.get(&key).cloned())
        }

        fn insert_local(&self, key: K, val: V) {
            let mut frames = self.frames.write().unwrap();
            frames.last_mut().unwrap().insert(key, Some(val));
        }

        fn push(&self) {
            self.frames.write().unwrap().push(HashMap::new())
        }

        fn pop(&self) {
            let mut frames = self.frames.write().unwrap();
            if frames.len() <= 1 {
                // `Shared_mem.LocalChanges.pop_stack`
                panic!("There are no active local change stacks. Nothing to pop!")
            }
            frames.pop();
        }

        fn depth(&self) -> usize {
            self.frames.read().unwrap().len() - 1
        }
    }

    impl<K, V> Store<K, V> for Layer<K, V>
    where
        K: Copy + Eq + Hash + Send + Sync,
        V: Clone + Send + Sync,
    {
        fn get(&self, key: K) -> anyhow::Result<Option<V>> {
            if let Some(found) = self.local(key) {
                return Ok(found);
            }
            if let Some(val) = (self.fallback)(key)? {
                return Ok(Some(val));
            }
            match (self.miss, self.owner.upgrade()) {
                // A naming lookup reads the decl stores as its naming table
                // (`crate::naming_provider`): it parses nothing, as the
                // OCaml's naming heap does not.
                (Some(miss), Some(owner))
                    if !naming_provider::rust_provider_backend::is_ctx_proxy_set() =>
                {
                    Ok(miss(&owner, key))
                }
                _ => Ok(None),
            }
        }

        fn insert(&self, key: K, val: V) -> anyhow::Result<()> {
            self.insert_local(key, val);
            Ok(())
        }

        fn remove_batch(&self, keys: &mut dyn Iterator<Item = K>) -> anyhow::Result<()> {
            let mut frames = self.frames.write().unwrap();
            let frame = frames.last_mut().unwrap();
            for key in keys {
                frame.insert(key, None);
            }
            Ok(())
        }
    }

    /// The local changes of a context with entries.
    pub struct LocalChanges {
        /// The context the entries were added to, with its stores (those
        /// without these local changes) and the entries: its naming table is
        /// what a miss asks.
        naming_ctx: T,
        classes: Arc<Layer<TypeName, Arc<ShallowClass<R>>>>,
        typedefs: Arc<Layer<TypeName, Arc<TypedefDecl<R>>>>,
        funs: Arc<Layer<FunName, Arc<FunDecl<R>>>>,
        consts: Arc<Layer<ConstName, Arc<ConstDecl<R>>>>,
        modules: Arc<Layer<ModuleName, Arc<ModuleDecl<R>>>>,
        folded: Arc<Layer<TypeName, Arc<FoldedClass<R>>>>,
    }

    type Registry = Vec<(Weak<ShallowDeclStore<R>>, Weak<LocalChanges>)>;

    /// The local changes of the contexts that have them, by their
    /// `ShallowDeclStore`.
    static REGISTRY: LazyLock<Mutex<Registry>> = LazyLock::new(Default::default);

    /// The local changes of `ctx`, if it has entries.
    pub fn of_ctx(ctx: &Ctx) -> Option<Arc<LocalChanges>> {
        let mut registry = REGISTRY.lock().unwrap();
        registry.retain(|(store, lc)| store.strong_count() > 0 && lc.strong_count() > 0);
        registry
            .iter()
            .find(|(store, _)| std::ptr::eq(store.as_ptr(), Arc::as_ptr(&ctx.shallow_decls)))
            .and_then(|(_, lc)| lc.upgrade())
    }

    /// `ctx` with `entries`, and local changes over the stores of `ctx`
    /// (those it reads itself, without local changes of its own).
    pub fn with_entries(ctx: &T, entries: Entries) -> T {
        // The `Local_memory` backend (the IDE daemon's) has one set of
        // caches for every context, as the OCaml's: no local changes.
        if ctx.local_memory().is_some() {
            return Arc::new(crate::ctx::local_memory_with_entries(ctx, entries));
        }
        let (shallow_decls, folded_decls) = match of_ctx(ctx) {
            Some(lc) => (
                Arc::clone(&lc.naming_ctx.shallow_decls),
                Arc::clone(&lc.naming_ctx.folded_decls),
            ),
            None => (Arc::clone(&ctx.shallow_decls), Arc::clone(&ctx.folded_decls)),
        };
        let naming_ctx = Arc::new(Ctx {
            entries: entries.clone(),
            shallow_decls,
            folded_decls,
            ..Ctx::clone(ctx)
        });
        let lc = Arc::new_cyclic(|owner: &Weak<LocalChanges>| {
            let base = &naming_ctx;
            macro_rules! shallow {
                ($get:ident, $miss:ident) => {{
                    let base = Arc::clone(&base.shallow_decls);
                    Arc::new(Layer::new(
                        owner.clone(),
                        Box::new(move |name| base.$get(name)),
                        Some($miss),
                    ))
                }};
            }
            let folded_base = Arc::clone(&base.folded_decls);
            LocalChanges {
                classes: shallow!(get_class, miss_class),
                typedefs: shallow!(get_typedef, miss_typedef),
                funs: shallow!(get_fun, miss_fun),
                consts: shallow!(get_const, miss_const),
                modules: shallow!(get_module, miss_module),
                folded: Arc::new(Layer::new(
                    owner.clone(),
                    Box::new(move |name| Ok(folded_base.get_class(name)?)),
                    None,
                )),
                naming_ctx: Arc::clone(&naming_ctx),
            }
        });
        // The stores of the context hold `lc` (its layers only hold it
        // weakly): it lives as long as the context.
        fn held<K, V>(layer: &Arc<Layer<K, V>>, lc: &Arc<LocalChanges>) -> Arc<Held<K, V>> {
            Arc::new(Held {
                layer: Arc::clone(layer),
                _lc: Arc::clone(lc),
            })
        }
        let shallow_decls = Arc::new(ShallowDeclStore::with_no_member_stores(
            held(&lc.classes, &lc),
            held(&lc.typedefs, &lc),
            held(&lc.funs, &lc),
            held(&lc.consts, &lc),
            held(&lc.modules, &lc),
        ));
        let folded_decls: Arc<dyn FoldedDeclProvider<R>> = Arc::new(LazyFoldedDeclProvider::new(
            Arc::new(oxidized::decl_fold_options::DeclFoldOptions::from_global_options(
                &ctx.tco,
            )),
            held(&lc.folded, &lc),
            Arc::new(EagerShallowDeclProvider::new(Arc::clone(&shallow_decls))),
        ));
        REGISTRY
            .lock()
            .unwrap()
            .push((Arc::downgrade(&shallow_decls), Arc::downgrade(&lc)));
        Arc::new(Ctx {
            entries,
            shallow_decls,
            folded_decls,
            ..Ctx::clone(ctx)
        })
    }

    /// A [`Layer`] as the stores of the context see it: with its owner.
    struct Held<K, V> {
        layer: Arc<Layer<K, V>>,
        _lc: Arc<LocalChanges>,
    }

    impl<K, V> std::fmt::Debug for Held<K, V> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.layer.fmt(f)
        }
    }

    impl<K, V> Store<K, V> for Held<K, V>
    where
        K: Copy + Eq + Hash + Send + Sync,
        V: Clone + Send + Sync,
    {
        fn get(&self, key: K) -> anyhow::Result<Option<V>> {
            self.layer.get(key)
        }

        fn insert(&self, key: K, val: V) -> anyhow::Result<()> {
            self.layer.insert(key, val)
        }

        fn remove_batch(&self, keys: &mut dyn Iterator<Item = K>) -> anyhow::Result<()> {
            self.layer.remove_batch(keys)
        }
    }

    impl LocalChanges {
        fn layers_do(&self, f: &dyn Fn(&dyn LayerOps)) {
            f(&*self.classes);
            f(&*self.typedefs);
            f(&*self.funs);
            f(&*self.consts);
            f(&*self.modules);
            f(&*self.folded);
        }

        /// `*.LocalChanges.push_stack` of the decl heaps.
        pub fn push(&self) {
            self.layers_do(&|layer| layer.push())
        }

        /// `*.LocalChanges.pop_stack` of the decl heaps.
        pub fn pop(&self) {
            self.layers_do(&|layer| layer.pop())
        }

        /// The number of pushes not popped yet.
        pub fn depth(&self) -> usize {
            self.funs.depth()
        }

        /// `Direct_decl_utils.direct_decl_parse_and_cache ctx file`
        /// (`Shared_memory`): the decls of `file` (in lexical order), from the
        /// contents of its entry if it has one, else of the file
        /// (`File_provider.get_contents`); those that win their name are
        /// cached (`cache_decls`). `None` when the file has no contents.
        fn direct_decl_parse_and_cache(
            &self,
            file: &relative_path::RelativePath,
        ) -> Option<Vec<NamedDecl<R>>> {
            let parsed = crate::counters::count(crate::counters::category::T::DirectDeclParse, || {
                let ctx = &self.naming_ctx;
                let path = pos::RelativePath::from(file);
                // `get_file_contents ~ignore_file_content_caches:false`
                let contents = match naming_provider::get_entry_contents(ctx, file) {
                    Some(contents) => contents,
                    None => ::file_provider::FileProvider::get(&*ctx.files, path).ok()?,
                };
                ctx.decl_parser.parse_with_text(path, &contents).ok()
            });
            if let Some(decls) = &parsed {
                self.cache_decls(file, decls);
            }
            parsed
        }

        /// `Direct_decl_utils.cache_decls` (`Shared_memory`): the first
        /// declaration of each name (`dedup_decls`) that wins its name
        /// (`remove_naming_conflict_losers`), into the newest frame.
        fn cache_decls(&self, file: &relative_path::RelativePath, decls: &[NamedDecl<R>]) {
            let ctx = &self.naming_ctx;
            let mut seen_types = HashSet::new();
            let mut seen_funs = HashSet::new();
            let mut seen_consts = HashSet::new();
            let mut seen_modules = HashSet::new();
            let wins = |path: Option<relative_path::RelativePath>| match path {
                Some(nfile) => nfile == *file,
                None => true,
            };
            for decl in decls {
                match decl {
                    NamedDecl::Class(name, _) | NamedDecl::Typedef(name, _) => {
                        if !seen_types.insert(*name)
                            || !wins(naming_provider::get_type_path(ctx, name.as_str()))
                        {
                            continue;
                        }
                    }
                    NamedDecl::Fun(name, _) => {
                        if !seen_funs.insert(*name)
                            || !wins(naming_provider::get_fun_path(ctx, name.as_str()))
                        {
                            continue;
                        }
                    }
                    NamedDecl::Const(name, _) => {
                        if !seen_consts.insert(*name)
                            || !wins(naming_provider::get_const_path(ctx, name.as_str()))
                        {
                            continue;
                        }
                    }
                    NamedDecl::Module(name, _) => {
                        if !seen_modules.insert(*name)
                            || !wins(naming_provider::get_module_path(ctx, name.as_str()))
                        {
                            continue;
                        }
                    }
                }
                match decl {
                    NamedDecl::Class(name, d) => self.classes.insert_local(*name, Arc::new(d.clone())),
                    NamedDecl::Typedef(name, d) => self.typedefs.insert_local(*name, Arc::new(d.clone())),
                    NamedDecl::Fun(name, d) => self.funs.insert_local(*name, Arc::new(d.clone())),
                    NamedDecl::Const(name, d) => self.consts.insert_local(*name, Arc::new(d.clone())),
                    NamedDecl::Module(name, d) => self.modules.insert_local(*name, Arc::new(d.clone())),
                }
            }
        }

        /// `Decl_provider_internals.find_in_direct_decl_parse ~cache_results:true`:
        /// the declaration of `name` that `extract` takes, the last one in
        /// the file (the OCaml searches the decls of the parser, which are in
        /// reverse lexical order). Raises `Decl_not_found` when the file
        /// has no contents.
        fn find_in_direct_decl_parse<V>(
            &self,
            file: relative_path::RelativePath,
            name: &str,
            extract: impl Fn(&NamedDecl<R>) -> Option<V>,
        ) -> Option<V> {
            match self.direct_decl_parse_and_cache(&file) {
                None => crate::decl_defs::raise_decl_not_found(Some(&file), name),
                Some(decls) => decls.iter().rev().find_map(|decl| match decl_name(decl) {
                    decl_name if decl_name == name => extract(decl),
                    _ => None,
                }),
            }
        }
    }

    fn decl_name(decl: &NamedDecl<R>) -> &str {
        match decl {
            NamedDecl::Class(name, _) | NamedDecl::Typedef(name, _) => name.as_str(),
            NamedDecl::Fun(name, _) => name.as_str(),
            NamedDecl::Const(name, _) => name.as_str(),
            NamedDecl::Module(name, _) => name.as_str(),
        }
    }

    /// The decl of a name (in the newest frame, when the parse cached it:
    /// the same `Arc`), else the one parsed.
    fn found<K: Copy + Eq + Hash, V: Clone>(layer: &Layer<K, V>, name: K, parsed: Option<V>) -> Option<V> {
        let parsed = parsed?;
        match layer.local(name) {
            Some(Some(cached)) => Some(cached),
            _ => Some(parsed),
        }
    }

    /// `Shallow_classes_provider.get` (`Decl_provider_internals.get_shallow_class`)
    /// on a miss of `Shallow_classes_heap.Classes`.
    fn miss_class(lc: &LocalChanges, name: TypeName) -> Option<Arc<ShallowClass<R>>> {
        let path = naming_provider::get_class_path(&lc.naming_ctx, name.as_str())?;
        let parsed = lc.find_in_direct_decl_parse(path, name.as_str(), |decl| match decl {
            NamedDecl::Class(_, d) => Some(Arc::new(d.clone())),
            _ => None,
        });
        found(&lc.classes, name, parsed)
    }

    /// `Decl_provider_internals.get_typedef_without_pessimise` on a miss.
    fn miss_typedef(lc: &LocalChanges, name: TypeName) -> Option<Arc<TypedefDecl<R>>> {
        let path = naming_provider::get_typedef_path(&lc.naming_ctx, name.as_str())?;
        let parsed = lc.find_in_direct_decl_parse(path, name.as_str(), |decl| match decl {
            NamedDecl::Typedef(_, d) => Some(Arc::new(d.clone())),
            _ => None,
        });
        found(&lc.typedefs, name, parsed)
    }

    /// `Decl_provider_internals.get_fun_without_pessimise` on a miss.
    fn miss_fun(lc: &LocalChanges, name: FunName) -> Option<Arc<FunDecl<R>>> {
        let path = naming_provider::get_fun_path(&lc.naming_ctx, name.as_str())?;
        let parsed = lc.find_in_direct_decl_parse(path, name.as_str(), |decl| match decl {
            NamedDecl::Fun(_, d) => Some(Arc::new(d.clone())),
            _ => None,
        });
        found(&lc.funs, name, parsed)
    }

    /// `Decl_provider_internals.get_gconst_without_pessimise` on a miss.
    fn miss_const(lc: &LocalChanges, name: ConstName) -> Option<Arc<ConstDecl<R>>> {
        let path = naming_provider::get_const_path(&lc.naming_ctx, name.as_str())?;
        let parsed = lc.find_in_direct_decl_parse(path, name.as_str(), |decl| match decl {
            NamedDecl::Const(_, d) => Some(Arc::new(d.clone())),
            _ => None,
        });
        found(&lc.consts, name, parsed)
    }

    /// `Decl_provider_internals.get_module_without_pessimise` on a miss.
    fn miss_module(lc: &LocalChanges, name: ModuleName) -> Option<Arc<ModuleDecl<R>>> {
        let path = naming_provider::get_module_path(&lc.naming_ctx, name.as_str())?;
        let parsed = lc.find_in_direct_decl_parse(path, name.as_str(), |decl| match decl {
            NamedDecl::Module(_, d) => Some(Arc::new(d.clone())),
            _ => None,
        });
        found(&lc.modules, name, parsed)
    }

    /// What [`LocalChanges::push`] and [`LocalChanges::pop`] do to each layer.
    trait LayerOps {
        fn push(&self);
        fn pop(&self);
    }

    impl<K: Copy + Eq + Hash, V: Clone> LayerOps for Layer<K, V> {
        fn push(&self) {
            Layer::push(self)
        }
        fn pop(&self) {
            Layer::pop(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ctx() -> T {
        Arc::new(Ctx::new(Path::new("/"), TypecheckerOptions::default()).unwrap())
    }

    fn path(name: &str) -> RelativePath {
        RelativePath::make(Prefix::Root, name.into())
    }

    #[test]
    fn options() {
        let ctx = ctx();
        assert_eq!(
            get_deps_mode(&ctx),
            typing_deps_mode::T::InMemoryMode(None)
        );
        let ctx2 = map_tcopt(&ctx, |mut tcopt| {
            tcopt.tco_skip_hierarchy_checks = true;
            tcopt.po.everything_sdt = !tcopt.po.everything_sdt;
            tcopt
        });
        assert!(get_tcopt(&ctx2).tco_skip_hierarchy_checks);
        assert!(!get_tcopt(&ctx).tco_skip_hierarchy_checks);
        // `popt` is its own field: it is not that of the new options.
        assert_eq!(
            get_popt(&ctx2).everything_sdt,
            get_popt(&ctx).everything_sdt
        );
        // The stores are shared.
        assert!(Arc::ptr_eq(&ctx.files, &ctx2.files));
        let ctx3 = map_deps_mode(&ctx2, |_| typing_deps_mode::T::InMemoryMode(Some("g".into())));
        assert_eq!(
            get_deps_mode(&ctx3),
            typing_deps_mode::T::InMemoryMode(Some("g".into()))
        );
        assert!(get_tcopt(&ctx3).tco_skip_hierarchy_checks);
        let ctx4 = with_tcopt_for_autocomplete(&ctx);
        assert!(get_tcopt(&ctx4).tco_skip_hierarchy_checks);
    }

    #[test]
    fn entries() {
        let ctx = ctx();
        assert!(get_entries(&ctx).is_empty());
        let (ctx2, entry) =
            add_or_overwrite_entry_contents(&ctx, path("a.php"), BString::from("<?hh"));
        assert!(get_entries(&ctx).is_empty());
        assert_eq!(get_entries(&ctx2).len(), 1);
        let (ctx3, entry2) = add_entry_if_missing(&ctx2, path("a.php"));
        assert!(Arc::ptr_eq(&entry, &entry2));
        assert!(Arc::ptr_eq(&ctx2, &ctx3));
        assert_eq!(read_file_contents(&entry), Some(BString::from("<?hh")));
        assert_eq!(get_file_contents_if_present(&entry), Some(BString::from("<?hh")));
    }

    #[test]
    fn contents_that_cannot_be_read() {
        let entry = make_entry(
            RelativePath::make(Prefix::Dummy, "/nonexistent/hh_provider_context_test.php".into()),
            EntryContents::NotYetReadFromDisk,
        );
        assert_eq!(get_file_contents_if_present(&entry), None);
        assert_eq!(read_file_contents(&entry), None);
        assert!(matches!(
            &*entry.contents.lock().unwrap(),
            EntryContents::ReadContentsFromDiskFailed(_)
        ));
        // The same exception, again.
        let first = std::panic::catch_unwind(|| read_file_contents_exn(&entry)).unwrap_err();
        let second = std::panic::catch_unwind(|| read_file_contents_exn(&entry)).unwrap_err();
        assert_eq!(
            first.downcast_ref::<String>(),
            second.downcast_ref::<String>()
        );
        assert!(
            first
                .downcast_ref::<String>()
                .unwrap()
                .starts_with("Sys_error(\"/nonexistent/hh_provider_context_test.php: ")
        );
        let entry = make_entry(path("b.php"), EntryContents::RaiseExnOnAttemptToRead);
        assert_eq!(read_file_contents(&entry), None);
    }

    #[test]
    fn quarantine() {
        assert!(!is_quarantined());
        set_is_quarantined_internal();
        assert!(is_quarantined());
        assert!(std::panic::catch_unwind(set_is_quarantined_internal).is_err());
        unset_is_quarantined_internal();
        assert!(!is_quarantined());
        assert!(std::panic::catch_unwind(unset_is_quarantined_internal).is_err());
    }
}
