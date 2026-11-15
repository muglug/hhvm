// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/naming_table.ml`: the forward naming table (file ->
//! `File_info.t`).
//!
//! The type keeps the two variants of the OCaml: `Unbacked` (an in-memory
//! map, what a full init builds) and `Backed` (a SQLite naming table,
//! `crate::naming_sqlite`, with the local changes since it was saved: the
//! file infos changed since, in memory).
//!
//! The OCaml raises the exceptions of `Naming_sqlite` (a SQLite failure, a
//! corrupt database) through the operations of a backed table; here they
//! are a panic with the `naming_sqlite::Error` as payload (an uncaught
//! exception: `Server_utils.exit_on_exception` and the like report it),
//! except for the loads and saves, which return them (their callers catch
//! them: `Client_ide_init.map_attempt`, the saved-state loader).

use crate::file_info;
use crate::hh_logger;
use crate::naming_sqlite;
use crate::relative_path::RelativePath;

type RPMap<A> = crate::relative_path::map::T<A>;

/// `t`: key order = `Relative_path.compare`; an update is a pointer copy
/// (`im`), so that the old and the new table can be kept at once.
#[derive(Clone, Debug)]
pub enum T {
    Unbacked(RPMap<file_info::T>),
    Backed(naming_sqlite::LocalChanges, naming_sqlite::DbPath),
}

/// `changes_since_baseline`
pub type ChangesSinceBaseline = Option<naming_sqlite::LocalChanges>;

/// `defs_per_file`
pub type DefsPerFile = RPMap<file_info::Names>;

/// `saved_state_info`
pub type SavedStateInfo = RPMap<file_info::Saved>;

/// An exception of `Naming_sqlite` that the OCaml lets through: raised.
fn raise<A>(result: naming_sqlite::Result<A>) -> A {
    match result {
        Ok(a) => a,
        Err(e) => std::panic::panic_any(e),
    }
}

/// `Relative_path.Map.union a b` (the values of `a` win; `im`'s `union`
/// keeps those of the larger map, so the bindings of `a` are inserted).
fn map_union<A: Clone>(a: &RPMap<A>, b: &RPMap<A>) -> RPMap<A> {
    let mut b = b.clone();
    for (key, data) in a {
        b.insert(key.clone(), data.clone());
    }
    b
}

// ---------------------------------------------------------------------------
// Forward naming table functions
// ---------------------------------------------------------------------------

pub fn empty() -> T {
    T::Unbacked(RPMap::new())
}

/// [filter] is implemented using tombstones on SQLite-backed naming tables, so
/// if your naming table is backed by SQLite you should try to avoid removing
/// more than half the table by filtering (otherwise it would be best to just
/// make a new empty one and add elements to it). On non-SQLite backed tables
/// we remove entries, so it's no more or less efficient depending on how many
/// are removed.
pub fn filter(a: &T, f: impl Fn(&RelativePath, &file_info::T) -> bool) -> T {
    match a {
        T::Unbacked(a) => T::Unbacked(
            a.iter()
                .filter(|(path, fi)| f(path, fi))
                .map(|(path, fi)| (path.clone(), fi.clone()))
                .collect(),
        ),
        T::Backed(local_changes, db_path) => {
            let file_deltas = &local_changes.file_deltas;
            T::Backed(
                naming_sqlite::LocalChanges {
                    file_deltas: raise(naming_sqlite::fold(
                        Some(true),
                        db_path,
                        file_deltas.clone(),
                        |path, fi, mut acc| {
                            if f(path, fi) {
                                acc
                            } else {
                                acc.insert(path.clone(), naming_sqlite::ForwardNamingTableDelta::Deleted);
                                acc
                            }
                        },
                        file_deltas,
                    )),
                    ..local_changes.clone()
                },
                db_path.clone(),
            )
        }
    }
}

/// `fold ?warn_on_naming_costly_iter a ~init ~f` (`warn_on_naming_costly_iter`
/// only concerns backed tables; it defaults to `true`).
pub fn fold<A>(
    warn_on_naming_costly_iter: Option<bool>,
    a: &T,
    init: A,
    mut f: impl FnMut(&RelativePath, &file_info::T, A) -> A,
) -> A {
    let warn_on_naming_costly_iter = warn_on_naming_costly_iter.unwrap_or(true);
    match a {
        T::Unbacked(a) => a.iter().fold(init, |acc, (path, fi)| f(path, fi, acc)),
        T::Backed(local_changes, db_path) => raise(naming_sqlite::fold(
            Some(warn_on_naming_costly_iter),
            db_path,
            init,
            f,
            &local_changes.file_deltas,
        )),
    }
}

pub fn get_files(a: &T) -> Vec<RelativePath> {
    match a {
        T::Unbacked(a) => a.keys().cloned().collect(),
        // Reverse at the end to preserve ascending sort order. (Pushed at
        // the end here: the same order.)
        T::Backed(local_changes, db_path) => raise(naming_sqlite::fold(
            Some(true),
            db_path,
            vec![],
            |path, _, mut acc| {
                acc.push(path.clone());
                acc
            },
            &local_changes.file_deltas,
        )),
    }
}

pub fn get_files_changed_since_baseline(
    changes_since_baseline: &ChangesSinceBaseline,
) -> Vec<RelativePath> {
    match changes_since_baseline {
        Some(changes_since_baseline) => changes_since_baseline.file_deltas.keys().cloned().collect(),
        None => vec![],
    }
}

pub fn get_file_info(a: &T, key: &RelativePath) -> Option<file_info::T> {
    match a {
        T::Unbacked(a) => a.get(key).cloned(),
        T::Backed(local_changes, db_path) => match local_changes.file_deltas.get(key) {
            Some(naming_sqlite::ForwardNamingTableDelta::Modified(fi)) => Some(fi.clone()),
            Some(naming_sqlite::ForwardNamingTableDelta::Deleted) => None,
            None => raise(naming_sqlite::get_file_info(db_path, key)),
        },
    }
}

/// `exception File_info_not_found`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FileInfoNotFound;

impl std::fmt::Display for FileInfoNotFound {
    /// `Printexc.to_string File_info_not_found`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Naming_table.File_info_not_found")
    }
}

impl std::error::Error for FileInfoNotFound {}

/// Like [get_file_info], but entries read from SQLite include declaration hashes
/// from its primary symbol table. These describe the database's winning
/// declarations, which may belong to another file or declaration kind.
/// Local and unbacked entries retain their own declaration hashes unchanged.
pub fn get_file_info_with_db_decl_hashes(
    naming_table: &T,
    path: &RelativePath,
) -> Option<file_info::T> {
    match naming_table {
        T::Unbacked(files) => files.get(path).cloned(),
        T::Backed(local_changes, db_path) => match local_changes.file_deltas.get(path) {
            Some(naming_sqlite::ForwardNamingTableDelta::Modified(file_info)) => {
                Some(file_info.clone())
            }
            Some(naming_sqlite::ForwardNamingTableDelta::Deleted) => None,
            None => raise(naming_sqlite::get_file_info_with_decl_hashes(db_path, path)),
        },
    }
}

/// Might raise {!File_info_not_found}
pub fn get_file_info_exn(a: &T, key: &RelativePath) -> Result<file_info::T, FileInfoNotFound> {
    match get_file_info(a, key) {
        Some(info) => Ok(info),
        None => Err(FileInfoNotFound),
    }
}

/// Look up the files declaring the symbols provided in the given set of
/// dependency hashes. Only works for backed naming tables, and 64bit dep_sets
pub fn get_64bit_dep_set_files(
    naming_table: &T,
    deps: &crate::typing_deps::dep_set::T,
) -> crate::relative_path::set::T {
    match naming_table {
        T::Unbacked(_) => panic!(
            "get_64bit_dep_set_files not supported for unbacked naming tables. Use Typing_deps.get_ifiles instead."
        ),
        T::Backed(local_changes, db_path) => {
            let mut base_results = crate::relative_path::set::T::new();
            for dep in deps.iter() {
                match raise(naming_sqlite::get_path_by_64bit_dep(db_path, *dep)) {
                    None => {}
                    Some((file, _namekind)) => {
                        base_results.insert(file);
                    }
                }
            }
            local_changes
                .file_deltas
                .iter()
                .fold(base_results, |mut acc, (path, file_info)| {
                    match file_info {
                        naming_sqlite::ForwardNamingTableDelta::Deleted => {
                            acc.remove(path);
                        }
                        naming_sqlite::ForwardNamingTableDelta::Modified(file_info) => {
                            let file_deps: crate::typing_deps::dep_set::T =
                                crate::typing_deps::deps_of_file_info(file_info).into_iter().collect();
                            if !deps.clone().intersection(file_deps).is_empty() {
                                acc.insert(path.clone());
                            } else {
                                // If this file happened to be present in the base changes, it
                                // would be permissible to include it since we can return an
                                // overestimate, but we may as well remove it.
                                acc.remove(path);
                            }
                        }
                    }
                    acc
                })
        }
    }
}

pub fn has_file(a: &T, key: &RelativePath) -> bool {
    match get_file_info(a, key) {
        Some(_) => true,
        None => false,
    }
}

pub fn iter(a: &T, mut f: impl FnMut(&RelativePath, &file_info::T)) {
    match a {
        T::Unbacked(a) => a.iter().for_each(|(path, fi)| f(path, fi)),
        T::Backed(local_changes, db_path) => raise(naming_sqlite::fold(
            Some(true),
            db_path,
            (),
            |path, fi, ()| f(path, fi),
            &local_changes.file_deltas,
        )),
    }
}

pub fn remove(a: &T, key: &RelativePath) -> T {
    match a {
        T::Unbacked(a) => T::Unbacked(a.without(key)),
        T::Backed(local_changes, db_path) => T::Backed(
            naming_sqlite::LocalChanges {
                file_deltas: local_changes
                    .file_deltas
                    .update(key.clone(), naming_sqlite::ForwardNamingTableDelta::Deleted),
                ..local_changes.clone()
            },
            db_path.clone(),
        ),
    }
}

pub fn update(a: &T, key: RelativePath, data: file_info::T) -> T {
    match a {
        T::Unbacked(a) => T::Unbacked(a.update(key, data)),
        T::Backed(local_changes, db_path) => T::Backed(
            naming_sqlite::LocalChanges {
                file_deltas: local_changes
                    .file_deltas
                    .update(key, naming_sqlite::ForwardNamingTableDelta::Modified(data)),
                ..local_changes.clone()
            },
            db_path.clone(),
        ),
    }
}

pub fn update_many(a: &T, updates: &RPMap<file_info::T>) -> T {
    match a {
        // Reverse the order because union always takes the first value.
        T::Unbacked(a) => T::Unbacked(map_union(updates, a)),
        T::Backed(local_changes, db_path) => {
            let local_updates: naming_sqlite::FileDeltas = updates
                .iter()
                .map(|(path, data)| {
                    (path.clone(), naming_sqlite::ForwardNamingTableDelta::Modified(data.clone()))
                })
                .collect();
            T::Backed(
                naming_sqlite::LocalChanges {
                    file_deltas: map_union(&local_updates, &local_changes.file_deltas),
                    ..local_changes.clone()
                },
                db_path.clone(),
            )
        }
    }
}

pub fn update_from_deltas(a: &T, file_deltas: &naming_sqlite::FileDeltas) -> T {
    match a {
        T::Unbacked(file_infos) => {
            let file_infos = file_deltas.iter().fold(file_infos.clone(), |mut acc, (path, file_delta)| {
                match file_delta {
                    naming_sqlite::ForwardNamingTableDelta::Modified(file_info) => {
                        acc.insert(path.clone(), file_info.clone());
                    }
                    naming_sqlite::ForwardNamingTableDelta::Deleted => {
                        acc.remove(path);
                    }
                }
                acc
            });
            T::Unbacked(file_infos)
        }
        T::Backed(local_changes, db_path) => {
            // Reverse the order because union always takes the first value.
            let file_deltas = map_union(file_deltas, &local_changes.file_deltas);
            T::Backed(
                naming_sqlite::LocalChanges {
                    file_deltas,
                    ..local_changes.clone()
                },
                db_path.clone(),
            )
        }
    }
}

pub fn combine(a: &T, b: &T) -> T {
    match b {
        T::Unbacked(b) => update_many(a, b),
        T::Backed(..) => panic!("SQLite-backed naming tables cannot be the second argument to combine."),
    }
}

/// This function saves the local changes structure as a binary blob.
/// Local changes represents the (forward) naming table changes since
/// the SQLite naming table baseline. Therefore, this function is most meaningful
/// when the naming table is backed by SQLite. If the naming table is NOT backed
/// by SQLite, meaning that it was computed from scratch by parsing the whole
/// repo, then this baseline-to-current difference is an empty set.
/// The resulting snapshot can be applied when loading a SQLite naming table.
///
/// (`Marshal.to_string snapshot [Marshal.No_sharing]`: `None` is the
/// immediate 0, whose encoding is [`naming_sqlite::EMPTY_LOCAL_CHANGES_BLOB`].
/// The OCaml has no caller of this function; the `Some local_changes` of a
/// backed table, which marshals `File_info.t` values and their `Pos.t`
/// positions, is not ported.)
pub fn save_changes_since_baseline(naming_table: &T, destination_path: &str) {
    let contents: &[u8] = match naming_table {
        T::Unbacked(_) => naming_sqlite::EMPTY_LOCAL_CHANGES_BLOB,
        T::Backed(..) => todo!(
            "Naming_table.save_changes_since_baseline of a backed table: the Marshal of File_info.t is not ported (the OCaml has no caller)"
        ),
    };
    // `Disk.write_file ~file:destination_path ~contents`
    if let Err(e) = std::fs::write(destination_path, contents) {
        panic!("Sys_error {:?}", format!("{}: {}", destination_path, e))
    }
}

pub fn save(naming_table: &T, db_name: &str) -> naming_sqlite::Result<naming_sqlite::SaveResult> {
    match naming_table {
        T::Unbacked(naming_table) => {
            let t = crate::rt::ocaml_unix::gettimeofday();
            // Ideally, we would have a commit hash, which would result in the same
            // content version given the same version of source files. However,
            // using a unique version every time we save the naming table from scratch
            // is good enough to enable us to check that the local changes diff
            // provided as an argument to load_from_sqlite_with_changes_since_baseline
            // is compatible with the underlying SQLite table.
            let base_content_version = format!("{}-{}", t as i64, crate::random_id::short_string());
            let save_result = naming_sqlite::save_file_infos(db_name, naming_table, &base_content_version)?;
            naming_sqlite::free_db_cache();
            let _: f64 = hh_logger::log_duration(
                None,
                None,
                &format!(
                    "Inserted {} symbols from {} files",
                    save_result.symbols_added, save_result.files_added
                ),
                t,
            );
            Ok(save_result)
        }
        T::Backed(local_changes, db_path) => {
            let t = crate::rt::ocaml_unix::gettimeofday();
            let save_result = naming_sqlite::copy_and_update(
                db_path,
                &naming_sqlite::DbPath(db_name.to_string()),
                local_changes,
            )?;
            naming_sqlite::free_db_cache();
            let _: f64 = hh_logger::log_duration(
                None,
                None,
                &format!(
                    "Inserted {} symbols from {} files",
                    save_result.symbols_added, save_result.files_added
                ),
                t,
            );
            Ok(save_result)
        }
    }
}

// ---------------------------------------------------------------------------
// Conversion functions
// ---------------------------------------------------------------------------

pub fn from_saved(saved: &SavedStateInfo) -> T {
    hh_logger::log("Loading naming table from marshalled blob...");
    let t = crate::rt::ocaml_unix::gettimeofday();
    let naming_table = T::Unbacked(
        saved
            .iter()
            .map(|(fn_, saved)| (fn_.clone(), file_info::from_saved(fn_.clone(), saved)))
            .collect(),
    );
    let _t = hh_logger::log_duration(None, None, "Loaded naming table from blob", t);
    naming_table
}

pub fn to_saved(a: &T) -> SavedStateInfo {
    match a {
        T::Unbacked(a) => a
            .iter()
            .map(|(path, fi)| (path.clone(), file_info::to_saved(fi)))
            .collect(),
        T::Backed(..) => fold(None, a, RPMap::new(), |path, fi, mut acc| {
            acc.insert(path.clone(), file_info::to_saved(fi));
            acc
        }),
    }
}

pub fn to_defs_per_file(a: &T, warn_on_naming_costly_iter: Option<bool>) -> DefsPerFile {
    let warn_on_naming_costly_iter = warn_on_naming_costly_iter.unwrap_or(true);
    match a {
        T::Unbacked(a) => a
            .iter()
            .map(|(path, fi)| (path.clone(), file_info::simplify(fi)))
            .collect(),
        T::Backed(..) => fold(Some(warn_on_naming_costly_iter), a, RPMap::new(), |path, fi, mut acc| {
            acc.insert(path.clone(), file_info::simplify(fi));
            acc
        }),
    }
}

pub fn saved_to_defs_per_file(saved: &SavedStateInfo) -> DefsPerFile {
    saved
        .iter()
        .map(|(path, saved)| (path.clone(), file_info::saved_to_names(saved)))
        .collect()
}

// ---------------------------------------------------------------------------
// Forward naming table creation functions
// ---------------------------------------------------------------------------

pub fn create(a: RPMap<file_info::T>) -> T {
    T::Unbacked(a)
}

/// Helper function to apply new files info to reverse naming table
fn update_reverse_entries_helper(
    ctx: &crate::provider_context::T,
    changed_ids: &[(RelativePath, Option<file_info::T>)],
) -> naming_sqlite::Result<()> {
    use crate::naming_provider;
    let backend: &crate::ctx::Ctx = ctx;
    let db_path_opt = crate::db_path_provider::get_naming_db_path(backend);
    let names = |ids: &[file_info::Id]| -> Vec<String> { ids.iter().map(|id| id.name.clone()).collect() };
    // Remove all old file symbols first
    for (path, _file_info) in changed_ids {
        let fi_opt = match &db_path_opt {
            Some(db_path) => naming_sqlite::get_file_info(db_path, path)?,
            None => None,
        };
        match fi_opt {
            Some(fi) => {
                let file_info::Ids {
                    classes,
                    typedefs,
                    funs,
                    consts,
                    modules,
                } = &fi.ids;
                naming_provider::remove_type_batch(backend, &names(classes));
                naming_provider::remove_type_batch(backend, &names(typedefs));
                naming_provider::remove_fun_batch(backend, &names(funs));
                naming_provider::remove_const_batch(backend, &names(consts));
                naming_provider::remove_module_batch(backend, &names(modules));
            }
            None => {}
        }
    }
    // Add new file symbols after removing old files symbols
    for (_path, new_file_info) in changed_ids {
        match new_file_info {
            Some(fi) => {
                let file_info::Ids {
                    classes,
                    typedefs,
                    funs,
                    consts,
                    modules,
                } = &fi.ids;
                for id in classes {
                    naming_provider::add_class(backend, &id.name, &id.pos)
                }
                for id in typedefs {
                    naming_provider::add_typedef(backend, &id.name, &id.pos)
                }
                for id in funs {
                    naming_provider::add_fun(backend, &id.name, &id.pos)
                }
                for id in consts {
                    naming_provider::add_const(backend, &id.name, &id.pos)
                }
                for id in modules {
                    naming_provider::add_module(backend, &id.name, &id.pos)
                }
            }
            None => {}
        }
    }
    Ok(())
}

fn update_reverse_entries(
    ctx: &crate::provider_context::T,
    file_deltas: &naming_sqlite::FileDeltas,
) -> naming_sqlite::Result<()> {
    let changed_files_info: Vec<(RelativePath, Option<file_info::T>)> = file_deltas
        .iter()
        .map(|(path, file_delta)| match file_delta {
            naming_sqlite::ForwardNamingTableDelta::Modified(fi) => (path.clone(), Some(fi.clone())),
            naming_sqlite::ForwardNamingTableDelta::Deleted => (path.clone(), None),
        })
        .collect();
    update_reverse_entries_helper(ctx, &changed_files_info)
}

fn choose_local_changes(
    local_changes: naming_sqlite::LocalChanges,
    changes_since_baseline: ChangesSinceBaseline,
) -> naming_sqlite::Result<naming_sqlite::LocalChanges> {
    match changes_since_baseline {
        None => Ok(local_changes),
        Some(changes_since_baseline) => {
            if changes_since_baseline.base_content_version == local_changes.base_content_version {
                Ok(changes_since_baseline)
            } else {
                Err(naming_sqlite::Error::Failure(format!(
                    "{}\nSQLite content version: {}\nLocal changes content version: {}",
                    "Incompatible local changes diff supplied.",
                    local_changes.base_content_version,
                    changes_since_baseline.base_content_version
                )))
            }
        }
    }
}

/// Loads the naming table from a SQLite database. The optional custom local
/// changes represents the naming table changes that occurred since the original
/// SQLite database was created.
/// To recap, the SQLite-based naming table, once loaded, is not mutated. All the
/// forward naming table changes are kept in an in-memory map. When we save an
/// update to a naming table that is backed by SQLite, we store the changes
/// since the baseline as a blob is a separate table and we rehydrate those
/// changes into an in-memory map when we load the updated naming table later.
/// The custom local changes is an alternative to the changes serialized as a
/// blob into the SQLite table. This enables scenarios that require repeatedly
/// loading the same base SQLite naming table with different versions of
/// the local changes.
fn load_from_sqlite_for_type_checking(
    changes_since_baseline: ChangesSinceBaseline,
    ctx: &crate::provider_context::T,
    db_path: &str,
) -> naming_sqlite::Result<T> {
    hh_logger::log("Loading naming table from SQLite...");
    let t = crate::rt::ocaml_unix::gettimeofday();
    let db_path = naming_sqlite::DbPath(db_path.to_string());
    naming_sqlite::validate_can_open_db(&db_path)?;
    // throw in master if anything's wrong
    crate::db_path_provider::set_naming_db_path(ctx, Some(db_path.clone()));
    // I believe that changes_since_baseline is never used. I want to check...
    // (`Hack_event_logger.naming_sqlite_has_changes_since_baseline ()`: a
    // no-op in OSS.)
    let local_changes = choose_local_changes(naming_sqlite::get_local_changes(&db_path)?, changes_since_baseline)?;
    let t = hh_logger::log_duration(None, None, "Loaded local naming table changes", t);
    update_reverse_entries(ctx, &local_changes.file_deltas)?;
    let _t = hh_logger::log_duration(None, None, "Updated reverse naming table entries", t);
    Ok(T::Backed(local_changes, db_path))
}

/// `load_from_sqlite_with_changed_file_infos ctx changed_file_infos db_path`
pub fn load_from_sqlite_with_changed_file_infos(
    ctx: &crate::provider_context::T,
    changed_file_infos: &[(RelativePath, Option<file_info::T>)],
    db_path: &str,
) -> naming_sqlite::Result<T> {
    hh_logger::log("Loading naming table from SQLite...");
    let db_path = naming_sqlite::DbPath(db_path.to_string());
    naming_sqlite::validate_can_open_db(&db_path)?;
    // throw in master if anything's wrong
    crate::db_path_provider::set_naming_db_path(ctx, Some(db_path.clone()));
    let t = crate::rt::ocaml_unix::gettimeofday();
    // Get changed files delta from file info
    let changed_file_deltas: naming_sqlite::FileDeltas =
        changed_file_infos
            .iter()
            .fold(naming_sqlite::FileDeltas::new(), |mut acc_files_delta, (path, changed_file_info_opt)| {
                let file_delta = match changed_file_info_opt {
                    Some(file_info) => naming_sqlite::ForwardNamingTableDelta::Modified(file_info.clone()),
                    None => naming_sqlite::ForwardNamingTableDelta::Deleted,
                };
                acc_files_delta.insert(path.clone(), file_delta);
                acc_files_delta
            });
    let base_local_changes = naming_sqlite::get_local_changes(&db_path)?;
    let local_changes = naming_sqlite::LocalChanges {
        file_deltas: changed_file_deltas,
        base_content_version: base_local_changes.base_content_version,
    };
    let t = hh_logger::log_duration(None, None, "Calculate changed files delta", t);
    update_reverse_entries_helper(ctx, changed_file_infos)?;
    let _t = hh_logger::log_duration(None, None, "Updated reverse naming table entries", t);
    Ok(T::Backed(local_changes, db_path))
}

/// `load_from_sqlite_with_changes_since_baseline ctx changes_since_baseline db_path`
pub fn load_from_sqlite_with_changes_since_baseline(
    ctx: &crate::provider_context::T,
    changes_since_baseline: ChangesSinceBaseline,
    db_path: &str,
) -> naming_sqlite::Result<T> {
    load_from_sqlite_for_type_checking(changes_since_baseline, ctx, db_path)
}

/// `load_from_sqlite ctx db_path`
pub fn load_from_sqlite(ctx: &crate::provider_context::T, db_path: &str) -> naming_sqlite::Result<T> {
    load_from_sqlite_for_type_checking(None, ctx, db_path)
}

/// The path to the table's SQLite database mapping filenames to symbol names, if any
pub fn get_forward_naming_fallback_path(a: &T) -> Option<String> {
    match a {
        T::Unbacked(_) => None,
        T::Backed(_, naming_sqlite::DbPath(db_path)) => Some(db_path.clone()),
    }
}

// (`SaveAsync`, `save_async`: the OCaml marshals the table to a file and
// saves it from a daemon process. Nothing calls it in this OCaml version:
// not ported.)

/// Test function; do not use.
pub fn get_backed_delta_test_only(t: &T) -> Option<&naming_sqlite::LocalChanges> {
    match t {
        T::Backed(local_changes, _) => Some(local_changes),
        T::Unbacked(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(s: &str) -> RelativePath {
        crate::relative_path::from_root(s)
    }

    fn info(funs: &[&str]) -> file_info::T {
        let mut fi = file_info::empty_t();
        fi.ids.funs = funs
            .iter()
            .map(|name| file_info::pos_full((oxidized::pos::Pos::NONE, name.to_string(), None)))
            .collect();
        fi
    }

    #[test]
    fn forward_table() {
        let t = create([(path("b.php"), info(&["\\b"]))].into_iter().collect());
        let t2 = update(&t, path("a.php"), info(&["\\a"]));
        // The old table is unchanged.
        assert_eq!(get_files(&t), vec![path("b.php")]);
        assert_eq!(get_files(&t2), vec![path("a.php"), path("b.php")]);
        assert!(has_file(&t2, &path("a.php")));
        assert_eq!(get_file_info_exn(&t, &path("a.php")), Err(FileInfoNotFound));
        // `update_many` prefers the updates.
        let updates: RPMap<file_info::T> =
            [(path("b.php"), info(&["\\b2"]))].into_iter().collect();
        let t3 = update_many(&t2, &updates);
        assert_eq!(get_file_info(&t3, &path("b.php")).unwrap().ids.funs[0].name, "\\b2");
        assert_eq!(get_file_info(&t3, &path("a.php")).unwrap().ids.funs[0].name, "\\a");
        let t4 = combine(&t3, &create(updates.update(path("c.php"), info(&[]))));
        assert_eq!(get_files(&t4).len(), 3);
        let t5 = remove(&t4, &path("a.php"));
        assert!(!has_file(&t5, &path("a.php")));
        assert_eq!(
            fold(None, &t5, vec![], |p, _, mut acc| {
                acc.push(p.clone());
                acc
            }),
            vec![path("b.php"), path("c.php")]
        );
        let defs = to_defs_per_file(&t5, None);
        assert!(defs.get(&path("b.php")).unwrap().funs.contains("\\b2"));
        assert_eq!(get_files(&filter(&t5, |p, _| p == &path("c.php"))), vec![path("c.php")]);
        assert_eq!(get_forward_naming_fallback_path(&t5), None);
    }

    // -- Backed tables -------------------------------------------------------

    use std::path::Path;
    use std::sync::Arc;

    use crate::naming_sqlite::ForwardNamingTableDelta;
    use crate::relative_path::Prefix;

    fn setup_prefixes() {
        static ONCE: std::sync::Once = std::sync::Once::new();
        ONCE.call_once(|| {
            for (prefix, dir) in [
                (Prefix::Root, "/tmp/hh-naming-table-test-root"),
                (Prefix::Hhi, "/tmp/hh-naming-table-test-hhi"),
                (Prefix::Tmp, "/tmp/hh-naming-table-test-tmp"),
            ] {
                if crate::relative_path::path_of_prefix(prefix).is_err() {
                    crate::relative_path::set_path_prefix(prefix, Path::new(dir));
                }
            }
        });
    }

    fn tmp_db(name: &str) -> String {
        let dir = std::env::temp_dir().join(format!("hh_naming_table_tests_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let p = dir.join(name);
        let _ = std::fs::remove_file(&p);
        p.display().to_string()
    }

    /// A file info as a database gives it back: `File` positions, no decl
    /// hashes of the ids, no comments.
    fn db_info(p: &RelativePath, funs: &[&str], classes: &[&str], hash: i64) -> file_info::T {
        let ids = |l: &[&str], t| -> Vec<file_info::Id> {
            l.iter()
                .map(|n| file_info::Id {
                    pos: file_info::Pos::File(t, Arc::new(p.clone())),
                    name: n.to_string(),
                    decl_hash: None,
                })
                .collect()
        };
        file_info::FileInfo {
            position_free_decl_hash: file_info::HashType(Some(hash)),
            file_mode: Some(file_info::Mode::Mstrict),
            ids: file_info::Ids {
                funs: ids(funs, file_info::NameType::Fun),
                classes: ids(classes, file_info::NameType::Class),
                typedefs: vec![],
                consts: vec![],
                modules: vec![],
            },
            comments: None,
        }
    }

    /// The same with decl hashes on the ids, as a save needs them.
    fn to_save(fi: &file_info::T) -> file_info::T {
        let mut fi = fi.clone();
        let mut h = 0;
        for id in fi.ids.funs.iter_mut().chain(fi.ids.classes.iter_mut()) {
            h += 1;
            id.decl_hash = Some(h);
        }
        fi
    }

    fn sample() -> RPMap<file_info::T> {
        setup_prefixes();
        let a = path("a.php");
        let b = path("b/c.php");
        let c = path("b-c.php");
        let h = RelativePath::make(Prefix::Hhi, std::path::PathBuf::from("x.hhi"));
        [
            (a.clone(), db_info(&a, &["\\fa"], &["\\A"], 1)),
            (b.clone(), db_info(&b, &["\\fb"], &[], 2)),
            (c.clone(), db_info(&c, &[], &["\\C"], 3)),
            (h.clone(), db_info(&h, &["\\hh"], &[], 4)),
        ]
        .into_iter()
        .collect()
    }

    /// A backed table over a database saved from `infos`, with no deltas.
    fn backed(infos: &RPMap<file_info::T>, name: &str) -> T {
        let db = tmp_db(name);
        let unbacked = create(infos.iter().map(|(p, fi)| (p.clone(), to_save(fi))).collect());
        let r = save(&unbacked, &db).unwrap();
        assert_eq!(r.files_added as usize, infos.len());
        let db = naming_sqlite::DbPath(db);
        T::Backed(naming_sqlite::get_local_changes(&db).unwrap(), db)
    }

    fn all(t: &T) -> Vec<(RelativePath, file_info::T)> {
        fold(Some(false), t, vec![], |p, fi, mut acc| {
            acc.push((p.clone(), fi.clone()));
            acc
        })
    }

    /// Every operation of a backed table gives what the same operations on
    /// an unbacked table of the same files give.
    #[test]
    fn backed_table_operations() {
        let infos = sample();
        let u = create(infos.clone());
        let b = backed(&infos, "ops.sql");
        assert!(get_forward_naming_fallback_path(&b).unwrap().ends_with("ops.sql"));
        assert_eq!(get_files(&b), get_files(&u));
        assert_eq!(all(&b), all(&u));
        for p in get_files(&u) {
            assert_eq!(get_file_info(&b, &p), get_file_info(&u, &p));
        }
        assert_eq!(get_file_info(&b, &path("nope.php")), None);
        assert_eq!(get_file_info_exn(&b, &path("nope.php")), Err(FileInfoNotFound));
        assert_eq!(get_backed_delta_test_only(&b).unwrap().file_deltas.len(), 0);

        // The same edits on both.
        let d = path("d.php");
        let edits = |t: &T| -> T {
            let t = update(t, d.clone(), db_info(&d, &["\\fd"], &[], 5));
            let t = remove(&t, &path("b/c.php"));
            let updates: RPMap<file_info::T> =
                [(path("a.php"), db_info(&path("a.php"), &["\\fa2"], &[], 6))].into_iter().collect();
            let t = update_many(&t, &updates);
            filter(&t, |p, _| p != &path("b-c.php"))
        };
        let (u2, b2) = (edits(&u), edits(&b));
        assert_eq!(all(&b2), all(&u2));
        assert_eq!(get_files(&b2), get_files(&u2));
        let mut n = 0;
        iter(&b2, |_, _| n += 1);
        assert_eq!(n, 3);
        assert!(!has_file(&b2, &path("b/c.php")));
        assert!(has_file(&b2, &d));
        // The table it came from is unchanged.
        assert_eq!(all(&b), all(&u));
        let deltas = &get_backed_delta_test_only(&b2).unwrap().file_deltas;
        assert_eq!(deltas.get(&path("b/c.php")), Some(&ForwardNamingTableDelta::Deleted));
        assert_eq!(deltas.get(&path("b-c.php")), Some(&ForwardNamingTableDelta::Deleted));
        assert!(matches!(deltas.get(&d), Some(ForwardNamingTableDelta::Modified(_))));
        assert_eq!(
            get_files_changed_since_baseline(&Some(get_backed_delta_test_only(&b2).unwrap().clone())),
            vec![path("a.php"), path("b-c.php"), path("b/c.php"), d.clone()]
        );
        assert_eq!(get_files_changed_since_baseline(&None), vec![]);
        // combine
        let e = path("e.php");
        let more = create([(e.clone(), db_info(&e, &["\\fe"], &[], 7))].into_iter().collect());
        assert_eq!(all(&combine(&b2, &more)), all(&combine(&u2, &more)));
        assert!(std::panic::catch_unwind(|| combine(&u2, &b2)).is_err());
        // update_from_deltas
        assert_eq!(all(&update_from_deltas(&b, deltas)), all(&update_from_deltas(&u, deltas)));
        assert_eq!(all(&update_from_deltas(&b, deltas)), all(&b2));
        // Conversions.
        assert_eq!(to_saved(&b2), to_saved(&u2));
        assert_eq!(to_defs_per_file(&b2, Some(false)), to_defs_per_file(&u2, None));
        // get_64bit_dep_set_files: by the database, then the deltas.
        use crate::typing_deps::dep;
        let deps = |names: &[&str]| -> crate::typing_deps::dep_set::T {
            names.iter().map(|n| dep::make(&dep::Variant::Fun(n.to_string()))).collect()
        };
        assert_eq!(get_64bit_dep_set_files(&b, &deps(&["\\fa", "\\fb"])), [path("a.php"), path("b/c.php")].into_iter().collect());
        // \fb's file is deleted; \fa is no longer in a.php; \fd is new.
        assert_eq!(get_64bit_dep_set_files(&b2, &deps(&["\\fa", "\\fb", "\\fd"])), [d.clone()].into_iter().collect());
        assert_eq!(get_64bit_dep_set_files(&b2, &deps(&["\\fa2"])), [path("a.php")].into_iter().collect());
        assert!(std::panic::catch_unwind(|| get_64bit_dep_set_files(&u, &deps(&["\\fa"]))).is_err());

        // Saving a backed table (`copy_and_update`) gives a database of the
        // edited files.
        let saved_db = tmp_db("ops-saved.sql");
        let with_hashes = update_many(
            &T::Backed(
                naming_sqlite::LocalChanges { file_deltas: Default::default(), ..get_backed_delta_test_only(&b).unwrap().clone() },
                naming_sqlite::DbPath(get_forward_naming_fallback_path(&b).unwrap()),
            ),
            &[(d.clone(), to_save(&db_info(&d, &["\\fd"], &[], 5)))].into_iter().collect(),
        );
        let with_hashes = remove(&with_hashes, &path("b/c.php"));
        let r = save(&with_hashes, &saved_db).unwrap();
        assert_eq!(r.files_added, 1);
        let db = naming_sqlite::DbPath(saved_db);
        let reloaded = T::Backed(naming_sqlite::get_local_changes(&db).unwrap(), db);
        assert_eq!(get_files(&reloaded), vec![path("a.php"), path("b-c.php"), d.clone(), get_files(&u)[3].clone()]);
        assert_eq!(get_file_info(&reloaded, &d), Some(db_info(&d, &["\\fd"], &[], 5)));
        // save_changes_since_baseline of an unbacked table: the empty blob.
        let blob = tmp_db("changes.bin");
        save_changes_since_baseline(&u, &blob);
        assert_eq!(std::fs::read(&blob).unwrap(), naming_sqlite::EMPTY_LOCAL_CHANGES_BLOB);
        naming_sqlite::free_db_cache();
    }

    /// `load_from_sqlite`: the local changes of the database (a non-empty
    /// blob, as `save_changes_since_baseline` would write), applied to the
    /// reverse naming table; `load_from_sqlite_with_changes_since_baseline`
    /// and `load_from_sqlite_with_changed_file_infos`.
    #[test]
    fn load_from_sqlite_applies_the_local_changes() {
        let infos = sample();
        let b = backed(&infos, "load.sql");
        let db = get_forward_naming_fallback_path(&b).unwrap();
        // A blob: a.php now declares \fa3 (not \fa, \A); b/c.php is deleted.
        let a = path("a.php");
        let blob: naming_sqlite::BlobFormat = vec![
            (a.clone(), ForwardNamingTableDelta::Modified(file_info::to_saved(&db_info(&a, &["\\fa3"], &[], 9)))),
            (path("b/c.php"), ForwardNamingTableDelta::Deleted),
        ];
        let bytes = crate::rt::ocaml_marshal::to_bytes(
            &naming_sqlite::blob_format_to_ocaml(&blob),
            &[crate::rt::ocaml_marshal::ExternFlag::NoSharing],
        )
        .unwrap();
        {
            let conn = rusqlite::Connection::open(&db).unwrap();
            conn.execute("UPDATE NAMING_LOCAL_CHANGES SET LOCAL_CHANGES = ?", [&bytes]).unwrap();
        }
        naming_sqlite::free_db_cache();
        let ctx = Arc::new(
            crate::ctx::Ctx::new(Path::new("/tmp/hh-naming-table-test-root"), Default::default()).unwrap(),
        );
        ctx.build_reverse_naming_table();
        // The names the init would have bound from the database.
        for (p, fi) in &infos {
            crate::naming_provider::update(&ctx, p, None, Some(&fi.ids));
        }
        let t = load_from_sqlite(&ctx, &db).unwrap();
        assert_eq!(get_files(&t), vec![a.clone(), path("b-c.php"), get_files(&create(infos.clone()))[3].clone()]);
        assert_eq!(get_file_info(&t, &a).unwrap().ids.funs[0].name, "\\fa3");
        // The reverse table: the names of the database's version of the
        // changed files are removed, the new ones added.
        assert!(ctx.naming_funs_get_pos("\\fa").is_none());
        assert!(ctx.naming_types_get_pos("\\A").is_none());
        assert!(ctx.naming_funs_get_pos("\\fb").is_none());
        assert_eq!(ctx.naming_funs_get_pos("\\fa3").map(|p| file_info::get_pos_filename(&p)), Some(a.clone()));
        assert!(ctx.naming_types_get_pos("\\C").is_some());
        assert_eq!(
            crate::db_path_provider::get_naming_db_path(&ctx),
            Some(naming_sqlite::DbPath(db.clone()))
        );
        // Changes since the baseline: they must be of the same version.
        let lc = get_backed_delta_test_only(&t).unwrap().clone();
        let mut other = lc.clone();
        other.base_content_version = "another".to_string();
        match load_from_sqlite_with_changes_since_baseline(&ctx, Some(other), &db) {
            Err(naming_sqlite::Error::Failure(msg)) => assert_eq!(
                msg,
                format!(
                    "Incompatible local changes diff supplied.\nSQLite content version: {}\nLocal changes content version: another",
                    lc.base_content_version
                )
            ),
            other => panic!("{:?}", other.map(|_| ())),
        }
        let mut mine = lc.clone();
        mine.file_deltas = Default::default();
        let t2 = load_from_sqlite_with_changes_since_baseline(&ctx, Some(mine), &db).unwrap();
        assert_eq!(get_files(&t2), get_files(&create(infos.clone())));
        // Changed file infos given by the caller instead of the blob.
        let e = path("e.php");
        let t3 = load_from_sqlite_with_changed_file_infos(
            &ctx,
            &[(e.clone(), Some(db_info(&e, &["\\fe"], &[], 1))), (path("b-c.php"), None)],
            &db,
        )
        .unwrap();
        assert!(has_file(&t3, &e) && !has_file(&t3, &path("b-c.php")) && has_file(&t3, &path("b/c.php")));
        assert_eq!(get_backed_delta_test_only(&t3).unwrap().base_content_version, lc.base_content_version);
        assert!(ctx.naming_types_get_pos("\\C").is_none());
        assert!(ctx.naming_funs_get_pos("\\fe").is_some());
        // A database that cannot be opened.
        assert!(load_from_sqlite(&ctx, "/nonexistent/x.sql").is_err());
        naming_sqlite::free_db_cache();
    }

    /// A database written by the OCaml (`hh_server --check --save-naming`),
    /// as a backed table: every file and every lookup against the database's
    /// rows (`naming_sqlite::tests::ocaml_database_read_compared_and_rewritten`
    /// checks the rows themselves). `HH_NAMING_TABLE_TEST_OCAML_DB=<db> cargo test ...
    /// naming_table -- --ignored`
    #[test]
    #[ignore]
    fn ocaml_database_as_a_backed_table() {
        let Some(db) = std::env::var_os("HH_NAMING_TABLE_TEST_OCAML_DB") else {
            eprintln!("skipped: HH_NAMING_TABLE_TEST_OCAML_DB is not set");
            return;
        };
        setup_prefixes();
        let db = naming_sqlite::DbPath(db.to_string_lossy().into_owned());
        let lc = naming_sqlite::get_local_changes(&db).unwrap();
        let b = T::Backed(lc, db.clone());
        let files = all(&b);
        let u = create(files.iter().cloned().collect());
        assert_eq!(get_files(&b), get_files(&u));
        for (p, fi) in &files {
            assert_eq!(get_file_info(&b, p).as_ref(), Some(fi));
        }
        // Edit a tenth of the files (every other one deleted, the others
        // given one more function), then compare everything again, and
        // save + reload.
        let mut edited_b = b.clone();
        let mut edited_u = u.clone();
        for (i, (p, fi)) in files.iter().enumerate().step_by(10) {
            if i % 20 == 0 {
                edited_b = remove(&edited_b, p);
                edited_u = remove(&edited_u, p);
            } else {
                let mut fi = fi.clone();
                fi.ids.funs.push(file_info::Id {
                    pos: file_info::Pos::File(file_info::NameType::Fun, Arc::new(p.clone())),
                    name: format!("\\added_{}", i),
                    decl_hash: None,
                });
                edited_b = update(&edited_b, p.clone(), fi.clone());
                edited_u = update(&edited_u, p.clone(), fi);
            }
        }
        assert_eq!(all(&edited_b), all(&edited_u));
        for p in get_files(&u) {
            assert_eq!(get_file_info(&edited_b, &p), get_file_info(&edited_u, &p));
        }
        eprintln!("{} files compared", files.len());
        naming_sqlite::free_db_cache();
    }
}
