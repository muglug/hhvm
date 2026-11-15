// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/fixme_provider.ml`: the table containing all the
//! HH_FIXMEs found in the source code. Associates:
//!
//!   filename =>
//!   line number guarded by HH_FIXME =>
//!   error_node_number =>
//!   position of HH_FIXME comment
//!
//! The tables are process wide (`SHARED`), as the
//! OCaml's heaps in shared memory are for every worker, with a per-thread copy
//! in front of them for the files the thread parsed itself.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use oxidized::i_map::IMap;
use oxidized::i_set::ISet;
use oxidized::pos::Pos;
use std::sync::Arc;
use std::sync::RwLock;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use oxidized::scoured_comments::ScouredComments;
use relative_path::RelativePath;

use crate::diagnostics::ErrorCode;

/// `Fixme_provider.FixmeMap`
pub mod fixme_map {
    pub type T = oxidized::scoured_comments::Fixmes;
}

/// The entries of the four heaps of the OCaml for one file
/// (`HH_FIXMES`, `DECL_HH_FIXMES`, `DISALLOWED_FIXMES`, `IGNORES`),
/// shared so that a copy is cheap.
#[derive(Clone, Default)]
struct FileFixmes {
    hh_fixmes: Option<Arc<fixme_map::T>>,
    decl_hh_fixmes: Option<Arc<fixme_map::T>>,
    disallowed_fixmes: Option<Arc<fixme_map::T>>,
    ignores: Option<Arc<fixme_map::T>>,
}

/// The four heaps, by file.
type Tables = BTreeMap<RelativePath, FileFixmes>;

/// The heaps, in shared memory in the OCaml: one for all the threads of
/// the process. Every thread writes here what it provides (outside a
/// stack of local changes, as the OCaml's `HeapWithLocalCache.add`),
/// [`remove_batch`] removes from it, and a thread reads it for the files
/// it did not parse itself. So an error positioned in a file that another
/// thread parsed sees that file's fixmes, and `UnusedFixmes` (on the RPC
/// thread) sees the fixmes of every file that any thread parsed.
static SHARED: RwLock<Tables> = RwLock::new(BTreeMap::new());

/// Whether [`SHARED`] is used. Always in the binaries; in the unit tests
/// of this crate (which run on many threads at once, on the same file
/// names) only once a test (in a child process) turns it on with
/// [`set_shared_tables`]. When it is off, the tables of a thread are all
/// there is.
static SHARING: AtomicBool = AtomicBool::new(!cfg!(test));

/// See [`SHARING`].
pub fn set_shared_tables(on: bool) {
    SHARING.store(on, Ordering::Relaxed)
}

fn sharing() -> bool {
    SHARING.load(Ordering::Relaxed)
}

fn shared() -> std::sync::RwLockReadGuard<'static, Tables> {
    SHARED.read().unwrap_or_else(|e| e.into_inner())
}

fn shared_mut() -> std::sync::RwLockWriteGuard<'static, Tables> {
    SHARED.write().unwrap_or_else(|e| e.into_inner())
}

/// A fixme map as the heaps store it.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
struct FixmeMapValue(fixme_map::T);

impl crate::shared_mem::Value for FixmeMapValue {
    const DESCRIPTION: &'static str = "Fixme_HH_FIXMES";
}

/// The four heaps of the OCaml on the shared heap (`HH_FIXMES`,
/// `DECL_HH_FIXMES`, `DISALLOWED_FIXMES`, `IGNORES`: `HeapWithLocalCache`s
/// of capacity 1000), when the server has one (see
/// `ctx::use_shared_memory_stores`): then they replace [`SHARED`], so
/// that what a worker's clone provides is seen by the master and the
/// other workers, as in the OCaml.
fn shared_heaps() -> Option<&'static [crate::shared_mem::HeapWithLocalCache<FixmeMapValue>; 4]> {
    static HEAPS: std::sync::OnceLock<[crate::shared_mem::HeapWithLocalCache<FixmeMapValue>; 4]> =
        std::sync::OnceLock::new();
    if !crate::ctx::shared_memory_stores() {
        return None;
    }
    Some(HEAPS.get_or_init(|| {
        [
            crate::shared_mem::HeapWithLocalCache::new_named("Fixme_HH_FIXMES", 0),
            crate::shared_mem::HeapWithLocalCache::new_named("Fixme_DECL_HH_FIXMES", 0),
            crate::shared_mem::HeapWithLocalCache::new_named("Fixme_DISALLOWED_FIXMES", 0),
            crate::shared_mem::HeapWithLocalCache::new_named("Fixme_IGNORES", 0),
        ]
    }))
}

/// `Relative_path.S.to_string`: the key of a file in the heaps.
fn key(filename: &RelativePath) -> Vec<u8> {
    filename.to_string().into_bytes()
}

/// What the shared tables have for `filename`.
fn shared_get(filename: &RelativePath) -> Option<FileFixmes> {
    match shared_heaps() {
        None => shared().get(filename).cloned(),
        Some(heaps) => {
            let k = key(filename);
            let get = |i: usize| heaps[i].get(&k).map(|v| Arc::new(v.0.clone()));
            let file = FileFixmes {
                hh_fixmes: get(0),
                decl_hh_fixmes: get(1),
                disallowed_fixmes: get(2),
                ignores: get(3),
            };
            (file.hh_fixmes.is_some()
                || file.decl_hh_fixmes.is_some()
                || file.disallowed_fixmes.is_some()
                || file.ignores.is_some())
            .then_some(file)
        }
    }
}

/// The index of a table in [`shared_heaps`] (by what it writes).
fn table_index(table: Table) -> usize {
    let mut probe = FileFixmes::default();
    let map = Arc::new(fixme_map::T::default());
    *table(&mut probe) = Some(map);
    if probe.hh_fixmes.is_some() {
        0
    } else if probe.decl_hh_fixmes.is_some() {
        1
    } else if probe.disallowed_fixmes.is_some() {
        2
    } else {
        3
    }
}

/// Adds a table of `filename` to the shared tables (on the shared heap
/// `add` keeps the first value, as the OCaml's).
fn shared_provide(table: Table, filename: RelativePath, fixme_map: Arc<fixme_map::T>) {
    match shared_heaps() {
        None => *table(shared_mut().entry(filename).or_default()) = Some(fixme_map),
        Some(heaps) => heaps[table_index(table)].add(&key(&filename), Arc::new(FixmeMapValue((*fixme_map).clone()))),
    }
}

/// The census of the fixme heap `i` (`HH_FIXMES`, `DECL_HH_FIXMES`,
/// `DISALLOWED_FIXMES`, `IGNORES`) for a file (`crate::mem_census`).
pub fn census_entry(i: usize, filename: &RelativePath) -> Option<(u64, u64, u64)> {
    shared_heaps()?[i].direct().census_entry(&key(filename))
}

/// Removes `filename` from the shared tables.
fn shared_remove(filename: &RelativePath) {
    match shared_heaps() {
        None => {
            shared_mut().remove(filename);
        }
        Some(heaps) => {
            let k = key(filename);
            for heap in heaps {
                heap.remove(&k)
            }
        }
    }
}

thread_local! {
    /// Not in the OCaml: the files for which this thread is authoritative
    /// (it parsed them, or changed them inside a stack of local changes),
    /// with their tables as this thread sees them (what [`SHARED`] has,
    /// or the local changes). The other files are read from [`SHARED`].
    /// (OCaml reads every file's fixmes from the shared heaps; this copy
    /// lets the errors of a thread's own file be matched without taking
    /// the lock of [`SHARED`].)
    static FIXMES: RefCell<Tables> = const { RefCell::new(BTreeMap::new()) };
}

/// Whether this thread is inside a `local_changes_push_sharedmem_stack`:
/// what it provides or removes then stays on this thread.
fn in_local_changes() -> bool {
    LOCAL_CHANGES.with_borrow(|stack| !stack.is_empty())
}

/// Calls `f` with the tables of `filename` as the OCaml's heaps would
/// give them to this thread: this thread's when it is authoritative for
/// the file, the shared ones otherwise.
fn with_file<R>(filename: &RelativePath, f: impl FnOnce(Option<&FileFixmes>) -> R) -> R {
    FIXMES.with(|local| {
        let local = local.borrow();
        match local.get(filename) {
            Some(file) => f(Some(file)),
            None if sharing() => {
                drop(local);
                f(shared_get(filename).as_ref())
            }
            None => f(None),
        }
    })
}

/// Makes this thread authoritative for `filename`, starting from what
/// the shared tables have for it (the OCaml reads its local changes,
/// then the shared heap).
fn make_known(local: &mut Tables, filename: &RelativePath) {
    if !local.contains_key(filename) {
        let file = if sharing() {
            shared_get(filename).unwrap_or_default()
        } else {
            FileFixmes::default()
        };
        local.insert(filename.clone(), file);
    }
}

/// One of the four tables of a [`FileFixmes`].
type Table = fn(&mut FileFixmes) -> &mut Option<Arc<fixme_map::T>>;

/// `HeapWithLocalCache.add`: in the shared tables, unless inside a stack
/// of local changes (where it stays on this thread, which is then
/// authoritative for the file), and on this thread when it is
/// authoritative for the file.
fn provide(table: Table, filename: RelativePath, fixme_map: fixme_map::T) {
    if fixme_map.is_empty() {
        return;
    }
    let local_only = in_local_changes();
    let fixme_map = Arc::new(fixme_map);
    FIXMES.with(|local| {
        let mut local = local.borrow_mut();
        if local_only {
            make_known(&mut local, &filename);
        }
        if !sharing() {
            *table(local.entry(filename.clone()).or_default()) = Some(fixme_map.clone());
        } else if let Some(file) = local.get_mut(&filename) {
            *table(file) = Some(fixme_map.clone());
        }
    });
    if sharing() && !local_only {
        shared_provide(table, filename, fixme_map);
    }
}

/// One of the `get_*` functions of OCaml, on the tables of a file.
type GetMap = for<'a> fn(&'a FileFixmes) -> Option<&'a fixme_map::T>;

fn fixmes_of(file: &FileFixmes) -> Option<&fixme_map::T> {
    match file.hh_fixmes.as_deref() {
        None => file.decl_hh_fixmes.as_deref(),
        Some(x) => Some(x),
    }
}

fn hh_fixmes_of(file: &FileFixmes) -> Option<&fixme_map::T> {
    file.hh_fixmes.as_deref()
}

fn decl_hh_fixmes_of(file: &FileFixmes) -> Option<&fixme_map::T> {
    file.decl_hh_fixmes.as_deref()
}

fn disallowed_fixmes_of(file: &FileFixmes) -> Option<&fixme_map::T> {
    file.disallowed_fixmes.as_deref()
}

fn ignores_of(file: &FileFixmes) -> Option<&fixme_map::T> {
    file.ignores.as_deref()
}

fn get(get_map: GetMap, filename: &RelativePath) -> Option<fixme_map::T> {
    with_file(filename, |file| file.and_then(get_map).cloned())
}

/// `get_map filename` from the shared tables when they are used (what
/// the OCaml's server reads outside of any local changes: the RPC
/// handlers, whose thread may not have seen the latest epoch), else
/// from this thread's.
fn get_shared(get_map: GetMap, filename: &RelativePath) -> Option<fixme_map::T> {
    if sharing() {
        shared_get(filename).as_ref().and_then(get_map).cloned()
    } else {
        get(get_map, filename)
    }
}

/// `Fixme_provider.fixmes_of filename` (used by `UnusedFixmes`):
/// from the shared tables, see [`get_shared`].
pub fn get_fixmes(filename: &RelativePath) -> Option<fixme_map::T> {
    get_shared(fixmes_of, filename)
}

/// `Fixme_provider.ignores_of filename` (used by `UnusedFixmes`):
/// from the shared tables, see [`get_shared`].
pub fn get_ignores(filename: &RelativePath) -> Option<fixme_map::T> {
    get_shared(ignores_of, filename)
}

pub fn get_hh_fixmes(filename: &RelativePath) -> Option<fixme_map::T> {
    get(hh_fixmes_of, filename)
}

pub fn get_decl_hh_fixmes(filename: &RelativePath) -> Option<fixme_map::T> {
    get(decl_hh_fixmes_of, filename)
}

pub fn provide_hh_fixmes(filename: RelativePath, fixme_map: fixme_map::T) {
    provide(|f| &mut f.hh_fixmes, filename, fixme_map)
}

pub fn provide_decl_hh_fixmes(filename: RelativePath, fixme_map: fixme_map::T) {
    provide(|f| &mut f.decl_hh_fixmes, filename, fixme_map)
}

pub fn provide_disallowed_fixmes(filename: RelativePath, fixme_map: fixme_map::T) {
    provide(|f| &mut f.disallowed_fixmes, filename, fixme_map)
}

pub fn provide_ignores(filename: RelativePath, fixme_map: fixme_map::T) {
    provide(|f| &mut f.ignores, filename, fixme_map)
}

/// Install the comments of `file`, as found by the parser: what
/// `Full_fidelity_ast.process_scour_comments` does with them (it also
/// reports `sc_error_pos` and `sc_bad_ignore_pos` as parsing errors, which
/// this does not do).
///
/// `quick_mode` is the parser's (declarations only). As in OCaml, a table
/// that is empty does not replace what a previous parse of `file`
/// provided (on any thread); use [`remove_batch`] for that. This thread
/// is authoritative for `file` afterwards.
pub fn provide_scoured_comments(file: &RelativePath, sc: &ScouredComments, quick_mode: bool) {
    FIXMES.with(|local| make_known(&mut local.borrow_mut(), file));
    provide_disallowed_fixmes(file.clone(), sc.misuses.clone());
    provide_ignores(file.clone(), sc.ignores.clone());
    if quick_mode {
        provide_decl_hh_fixmes(file.clone(), sc.fixmes.clone())
    } else {
        provide_hh_fixmes(file.clone(), sc.fixmes.clone())
    }
}

thread_local! {
    /// The tables as they were at each `local_changes_push_sharedmem_stack`
    /// that is not popped yet.
    static LOCAL_CHANGES: RefCell<Vec<Tables>> = const { RefCell::new(Vec::new()) };
}

/// `local_changes_push_sharedmem_stack`: `HH_FIXMES`, `DECL_HH_FIXMES`,
/// `DISALLOWED_FIXMES` and `IGNORES` `.LocalChanges.push_stack`. What
/// is provided or removed until the matching pop is forgotten then: the
/// tables of this thread are saved, and restored by the pop (for
/// `Provider_utils.respect_but_quarantine_unsaved_changes`); in
/// between, nothing reaches the shared tables.
pub fn local_changes_push_sharedmem_stack() {
    let saved = FIXMES.with(|fixmes| fixmes.borrow().clone());
    LOCAL_CHANGES.with_borrow_mut(|stack| stack.push(saved))
}

/// `local_changes_pop_sharedmem_stack`
pub fn local_changes_pop_sharedmem_stack() {
    match LOCAL_CHANGES.with_borrow_mut(|stack| stack.pop()) {
        // `Shared_mem.LocalChanges.pop_stack`
        None => panic!("There are no active local change stacks. Nothing to pop!"),
        Some(saved) => FIXMES.with(|fixmes| *fixmes.borrow_mut() = saved),
    }
}

/// Not in the OCaml: the tables of this thread stand in front of the
/// shared ones, from which `Fixme_provider.remove_batch` removes the
/// changed files; here every file is removed from this thread's, when the
/// files may have changed (see `crate::rt::decl_epoch`), and the thread
/// reads the shared tables until it parses the files again.
pub fn forget_thread_tables() {
    FIXMES.with(|fixmes| fixmes.borrow_mut().clear());
    // (The tables saved by a push are emptied too: the pop then gives
    // empty tables, at the same depth.)
    LOCAL_CHANGES.with_borrow_mut(|stack| stack.iter_mut().for_each(|saved| saved.clear()))
}

pub fn remove_batch(paths: &BTreeSet<RelativePath>) {
    let local_only = in_local_changes();
    FIXMES.with(|fixmes| {
        let mut fixmes = fixmes.borrow_mut();
        for path in paths {
            if local_only && sharing() {
                // (Removed in the local changes: the shared tables must
                // not be read for it until the pop.)
                fixmes.insert(path.clone(), FileFixmes::default());
            } else {
                fixmes.remove(path);
            }
        }
    });
    if sharing() && !local_only {
        for path in paths {
            shared_remove(path);
        }
    }
}

// We register the function that can look up a position and determine if a
// given position is affected by an HH_FIXME. We use a reference to avoid a
// cyclic dependency: everything depends on the Errors module (the module
// defining all the errors), because of that making the Errors module call
// into anything that isn't in the standard library is very unwise,
// because that code won't be able to add errors.

fn get_entries(get_map: GetMap, pos: &Pos) -> IMap<Pos> {
    let filename = pos.filename();
    let (line, _, _) = pos.info_pos();
    with_file(filename, |file| {
        file.and_then(get_map)
            .and_then(|map| map.get(&(line as isize)))
            .cloned()
            .unwrap_or_default()
    })
}

fn get_fixmes_for_pos(pos: &Pos) -> IMap<Pos> {
    get_entries(fixmes_of, pos)
}

pub fn get_fixme_codes_for_pos(pos: &Pos) -> ISet {
    get_fixmes_for_pos(pos).into_keys().collect()
}

fn get_entry(get_map: GetMap, pos: &Pos, code: ErrorCode) -> Option<Pos> {
    get_entries(get_map, pos).remove(&code)
}

/// What `Diagnostics.get_disallowed_fixme_pos` is set to.
pub fn get_disallowed_fixme_pos(pos: &Pos, code: ErrorCode) -> Option<Pos> {
    get_entry(disallowed_fixmes_of, pos, code)
}

/// What `Diagnostics.get_ignore_pos` is set to.
pub fn get_ignore_pos(pos: &Pos, code: ErrorCode) -> Option<Pos> {
    get_entry(ignores_of, pos, code)
}

const INF_ERR_CODES: [ErrorCode; 3] = [4110, 4323, 4324];

fn is_inf_err_code(err_code: ErrorCode) -> bool {
    INF_ERR_CODES.contains(&err_code)
}

fn any_inf_err_code(imap: &IMap<Pos>) -> Option<Pos> {
    INF_ERR_CODES
        .iter()
        .find_map(|code| imap.get(code))
        .cloned()
}

/// What `Diagnostics.get_hh_fixme_pos` is set to.
pub fn get_hh_fixme_pos(err_pos: &Pos, err_code: ErrorCode) -> Option<Pos> {
    let imap = get_fixmes_for_pos(err_pos);
    if crate::diagnostics::code_agnostic_fixme() {
        if imap.is_empty() {
            None
        } else {
            Some(err_pos.clone())
        }
    } else {
        match imap.get(&err_code) {
            None if is_inf_err_code(err_code) => any_inf_err_code(&imap),
            x => x.cloned(),
        }
    }
}

/// `UnusedFixmes`: over the process-wide fixme tables (the OCaml's shared
/// heaps), filled by whichever threads parsed the files.
pub mod unused_fixmes {
    use std::collections::BTreeMap;
    use std::collections::BTreeSet;

    use oxidized::pos::Pos;

    use crate::fixme_provider;
    use crate::naming_table;
    use crate::pos;
    use crate::relative_path;

    /// `FileToLineToCodesMap.t`: mapping error lines to sets of codes, per file
    type FileToLineToCodesMap = BTreeMap<relative_path::T, BTreeMap<isize, BTreeSet<isize>>>;

    fn make(pos_codes: &[(Pos, isize)]) -> FileToLineToCodesMap {
        let mut m = FileToLineToCodesMap::new();
        for (pos, code) in pos_codes {
            let fn_ = pos::filename(pos);
            let (line, _, _) = pos::info_pos(pos);
            m.entry(fn_).or_default().entry(line).or_default().insert(*code);
        }
        m
    }

    fn fixme_was_applied(
        applied_fixmes: &FileToLineToCodesMap,
        fn_: &relative_path::T,
        err_line: isize,
        err_code: isize,
    ) -> bool {
        applied_fixmes
            .get(fn_)
            .and_then(|m| m.get(&err_line))
            .is_some_and(|s| s.contains(&err_code))
    }

    fn code_is_concerned(codes: &[isize], code: isize) -> bool {
        codes.contains(&code)
            || codes.is_empty()
                && (code < 5000 || crate::error_codes::warning::of_enum(code).is_some())
    }

    fn get_unused_fixmes_in_file(
        fixmes_of: fn(&relative_path::T) -> Option<fixme_provider::fixme_map::T>,
        codes: &[isize],
        applied_fixmes: &FileToLineToCodesMap,
        fn_: &relative_path::T,
        mut acc: Vec<Pos>,
    ) -> Vec<Pos> {
        match fixmes_of(fn_) {
            None => acc,
            Some(fixme_map) => {
                // `FixmeMap.fold`: by line, then by code; `fixme_pos :: acc`.
                for (err_line, codes_map) in &fixme_map {
                    for (code, fixme_pos) in codes_map {
                        if code_is_concerned(codes, *code)
                            && !fixme_was_applied(applied_fixmes, fn_, *err_line, *code)
                        {
                            acc.insert(0, fixme_pos.clone());
                        }
                    }
                }
                acc
            }
        }
    }

    pub fn get(
        codes: &[isize],
        applied_fixmes: &[(Pos, isize)],
        files: &naming_table::T,
    ) -> Vec<Pos> {
        let applied_fixmes = make(applied_fixmes);
        naming_table::fold(Some(true), files, vec![], |fn_, _, acc| {
            let acc = get_unused_fixmes_in_file(
                fixme_provider::get_fixmes,
                codes,
                &applied_fixmes,
                fn_,
                acc,
            );
            get_unused_fixmes_in_file(
                fixme_provider::get_ignores,
                codes,
                &applied_fixmes,
                fn_,
                acc,
            )
        })
    }
}
