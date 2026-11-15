// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_incremental.ml`.

use std::sync::Arc;

use crate::ctx::Ctx;
use crate::decl_compare::versioned_names;
use crate::diagnostics;
use crate::fanout;
use crate::file_info;
use crate::hh_logger;
use crate::naming_global;
use crate::naming_provider;
use crate::naming_table;
use crate::provider_context;
use crate::relative_path;
use crate::s_map;
use crate::server_env::Env;
use crate::server_progress;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;
use crate::user_diagnostic;

type RPSet = crate::relative_path::set::T;
type RPMap<A> = crate::relative_path::map::T<A>;
type Diag = crate::diagnostics::T;

/// Removes the names that were defined in the files from the reverse naming table
pub fn remove_defs_from_reverse_naming_table(
    ctx: &Ctx,
    nt: &naming_table::T,
    defs_per_file_parsed: &RPMap<file_info::T>,
) {
    for fn_ in defs_per_file_parsed.keys() {
        match naming_table::get_file_info(nt, fn_) {
            None => {}
            Some(file_info::T { ids, .. }) => {
                let file_info::Ids {
                    funs,
                    classes,
                    typedefs,
                    consts,
                    modules,
                } = ids;
                // we use [snd] to strip away positions
                let snd = |ids: &[file_info::Id]| -> Vec<String> {
                    ids.iter().map(|id| id.name.clone()).collect()
                };
                naming_global::remove_decls(
                    ctx,
                    &snd(&funs),
                    &snd(&classes),
                    &snd(&typedefs),
                    &snd(&consts),
                    &snd(&modules),
                )
            }
        }
    }
}

/// Used only by [get_old_names_batch] to collect parsed files and existing
/// owners of their new names before naming is updated.
/// The returned files will be the keys of the map returned by [get_old_names_batch].
fn get_files_to_snapshot(
    ctx: &provider_context::T,
    defs_per_file_parsed: &RPMap<file_info::T>,
) -> RPSet {
    let fun_canon_path = |name: &str| {
        naming_provider::get_fun_canon_name(ctx, name)
            .and_then(|name| naming_provider::get_fun_path(ctx, &name))
    };
    let type_canon_path = |name: &str| {
        naming_provider::get_type_canon_name(ctx, name)
            .and_then(|name| naming_provider::get_type_path(ctx, &name))
    };
    let add_owners = |paths: RPSet, kind: file_info::NameType, ids: &[file_info::Id]| -> RPSet {
        let get_path = |name: &str| match kind {
            file_info::NameType::Fun => fun_canon_path(name),
            file_info::NameType::Class | file_info::NameType::Typedef => type_canon_path(name),
            file_info::NameType::Const => naming_provider::get_const_path(ctx, name),
            file_info::NameType::Module => naming_provider::get_module_path(ctx, name),
        };
        let add_owner = |mut paths: RPSet, id: &file_info::Id| match get_path(&id.name) {
            None => paths,
            Some(path) => {
                paths.insert(path);
                paths
            }
        };
        ids.iter().fold(paths, add_owner)
    };
    let add_file = |mut paths: RPSet, (path, file_info): (&relative_path::T, &file_info::T)| {
        let file_info::Ids {
            funs,
            classes,
            typedefs,
            consts,
            modules,
        } = &file_info.ids;
        paths.insert(path.clone());
        let paths = add_owners(paths, file_info::NameType::Fun, funs);
        let paths = add_owners(paths, file_info::NameType::Class, classes);
        let paths = add_owners(paths, file_info::NameType::Typedef, typedefs);
        let paths = add_owners(paths, file_info::NameType::Const, consts);
        add_owners(paths, file_info::NameType::Module, modules)
    };
    defs_per_file_parsed.iter().fold(RPSet::new(), add_file)
}

/// Private to the [get_old_names_batch] stages, with one value per kind.
#[derive(Clone)]
struct SymbolInfo<A> {
    funs: A,
    classes: A,
    typedefs: A,
    consts: A,
    modules: A,
}

fn map_symbol_info<A, B>(
    info: SymbolInfo<A>,
    mut f: impl FnMut(file_info::NameType, A) -> B,
) -> SymbolInfo<B> {
    // Record fields are evaluated from right to left.
    let modules = f(file_info::NameType::Module, info.modules);
    let consts = f(file_info::NameType::Const, info.consts);
    let typedefs = f(file_info::NameType::Typedef, info.typedefs);
    let classes = f(file_info::NameType::Class, info.classes);
    let funs = f(file_info::NameType::Fun, info.funs);
    SymbolInfo {
        funs,
        classes,
        typedefs,
        consts,
        modules,
    }
}

fn symbol_info_of_ids(ids: file_info::Ids) -> SymbolInfo<Vec<file_info::Id>> {
    SymbolInfo {
        funs: ids.funs,
        classes: ids.classes,
        typedefs: ids.typedefs,
        consts: ids.consts,
        modules: ids.modules,
    }
}

fn get_old_winner_file(
    ctx: &provider_context::T,
    kind: file_info::NameType,
    name: &str,
) -> Option<relative_path::T> {
    match kind {
        file_info::NameType::Fun => naming_provider::get_fun_path(ctx, name),
        file_info::NameType::Class => naming_provider::get_class_path(ctx, name),
        file_info::NameType::Typedef => naming_provider::get_typedef_path(ctx, name),
        file_info::NameType::Const => naming_provider::get_const_path(ctx, name),
        file_info::NameType::Module => naming_provider::get_module_path(ctx, name),
    }
}

/// Used only by [get_old_names_batch] to record old symbol names and their
/// previous owners. Ordinary file information is sufficient; hash fields are
/// ignored. Missing owners retain their symbol keys with [None].
fn get_old_symbol_owners(
    ctx: &provider_context::T,
    old_naming_table: &naming_table::T,
    files: &RPSet,
) -> RPMap<SymbolInfo<s_map::T<Option<relative_path::T>>>> {
    let owners_of_ids = |kind: file_info::NameType, ids: Vec<file_info::Id>| {
        let add_first = |mut owners: s_map::T<Option<relative_path::T>>, id: &file_info::Id| {
            if owners.contains_key(&id.name) {
                owners
            } else {
                owners.insert(id.name.clone(), get_old_winner_file(ctx, kind, &id.name));
                owners
            }
        };
        ids.iter().fold(s_map::T::new(), add_first)
    };
    let add_file = |mut acc: RPMap<_>, path: &relative_path::T| {
        let ids = match naming_table::get_file_info(old_naming_table, path) {
            None => file_info::empty_ids(),
            Some(file_info) => file_info.ids,
        };
        let owners = map_symbol_info(symbol_info_of_ids(ids), owners_of_ids);
        acc.insert(path.clone(), owners);
        acc
    };
    files.iter().fold(RPMap::new(), add_file)
}

/// Used only by [get_old_names_batch] to load decl hashes for snapshot files.
fn load_old_file_decl_hashes(
    old_naming_table: &naming_table::T,
    files: &RPSet,
) -> RPMap<SymbolInfo<s_map::T<Option<file_info::decl_hash::T>>>> {
    let hashes_of_ids = |_kind: file_info::NameType, ids: Vec<file_info::Id>| {
        let add_first =
            |mut hashes: s_map::T<Option<file_info::decl_hash::T>>, id: &file_info::Id| {
                if hashes.contains_key(&id.name) {
                    hashes
                } else {
                    hashes.insert(id.name.clone(), id.decl_hash);
                    hashes
                }
            };
        ids.iter().fold(s_map::T::new(), add_first)
    };
    let add_file = |mut acc: RPMap<_>, path: &relative_path::T| {
        match naming_table::get_file_info_with_db_decl_hashes(old_naming_table, path) {
            None => acc,
            Some(file_info) => {
                let hashes = map_symbol_info(symbol_info_of_ids(file_info.ids), hashes_of_ids);
                acc.insert(path.clone(), hashes);
                acc
            }
        }
    };
    files.iter().fold(RPMap::new(), add_file)
}

/// Used only by [get_old_names_batch] to assemble [Old_names] from recorded
/// owners and loaded hashes.
fn resolve_old_names_for_file(
    file_decl_hashes_by_path: &RPMap<SymbolInfo<s_map::T<Option<file_info::decl_hash::T>>>>,
    old_owners: &SymbolInfo<s_map::T<Option<relative_path::T>>>,
) -> file_info::old_names::T {
    let resolve_kind = |kind: file_info::NameType,
                        owners: &s_map::T<Option<relative_path::T>>|
     -> s_map::T<Option<file_info::decl_hash::T>> {
        let resolve_hash = |name: &String, owner: &Option<relative_path::T>| match owner {
            None => None,
            Some(path) => match file_decl_hashes_by_path.get(path) {
                None => None,
                Some(file_hashes) => {
                    let hashes = match kind {
                        file_info::NameType::Fun => &file_hashes.funs,
                        file_info::NameType::Class => &file_hashes.classes,
                        file_info::NameType::Typedef => &file_hashes.typedefs,
                        file_info::NameType::Const => &file_hashes.consts,
                        file_info::NameType::Module => &file_hashes.modules,
                    };
                    hashes.get(name).copied().flatten()
                }
            },
        };
        // `S_map.mapi resolve_hash owners`
        owners
            .iter()
            .map(|(name, owner)| (name.clone(), resolve_hash(name, owner)))
            .collect()
    };
    let SymbolInfo {
        funs,
        classes,
        typedefs,
        consts,
        modules,
    } = old_owners;
    let resolved = map_symbol_info(
        SymbolInfo {
            funs,
            classes,
            typedefs,
            consts,
            modules,
        },
        resolve_kind,
    );
    file_info::old_names::T {
        funs: resolved.funs,
        classes: resolved.classes,
        types: resolved.typedefs,
        consts: resolved.consts,
        modules: resolved.modules,
    }
}

/// Capture old names and their winning declaration hashes before updating
/// reverse naming.
///
/// If an input file participated in a naming conflict in the previous check,
/// every other file involved in that conflict must also be included in
/// [defs_per_file_parsed]. The server ensures this by including the entire
/// previous [failed_naming] set.
///
/// Conflicts introduced by the parsed contents are handled here: the snapshot
/// includes the parsed files and the existing owners of all their new names,
/// so files subsequently discovered through new naming conflicts are covered.
pub fn get_old_names_batch(
    ctx: &provider_context::T,
    old_naming_table: &naming_table::T,
    defs_per_file_parsed: &RPMap<file_info::T>,
) -> RPMap<file_info::old_names::T> {
    // 1. Extend files (= keys in [defs_per_file_parsed]) with additional files
    //    that naming may add through a new conflict.
    let result_files: RPSet = get_files_to_snapshot(ctx, defs_per_file_parsed);

    // 2. For each such file, look up *old* names therein and their naming winner
    //    files. The keys of this map are [result_files].
    let owners_by_file: RPMap<SymbolInfo<s_map::T<Option<relative_path::T>>>> =
        get_old_symbol_owners(ctx, old_naming_table, &result_files);
    // 3. Fetch decl hash information for [result_files], which include every old
    //    winner under the input prerequisite. The keys of this map are
    //    [result_files], excluding files for which we didn't find the file info.
    let file_decl_hashes_by_path: RPMap<SymbolInfo<s_map::T<Option<file_info::decl_hash::T>>>> =
        load_old_file_decl_hashes(old_naming_table, &result_files);
    // 4. Construct the resolved snapshot from winner decl hashes.
    let resolve_file = |owners: &SymbolInfo<s_map::T<Option<relative_path::T>>>| {
        resolve_old_names_for_file(&file_decl_hashes_by_path, owners)
    };
    owners_by_file
        .iter()
        .map(|(path, owners)| (path.clone(), resolve_file(owners)))
        .collect()
}

/// `get_old_and_new_defs_in_files old_naming_table ~old_names_per_file
/// new_naming_table files`
pub fn get_old_and_new_defs_in_files(
    old_naming_table: &naming_table::T,
    old_names_per_file: &RPMap<file_info::old_names::T>,
    new_naming_table: &naming_table::T,
    files: &RPSet,
) -> RPMap<versioned_names::T> {
    let mut acc = RPMap::new();
    for path in files {
        let old_names =
            // TODO(T298623016): When remote_old_decl_fetching_include_non_class
            // is disabled, old_names_per_file is empty; use the names-only
            // fallback until hash population is unconditional.
            match old_names_per_file.get(path) {
                Some(old_names) => Some(old_names.clone()),
                None => naming_table::get_file_info(old_naming_table, path)
                    .map(|i| file_info::simplify(&i))
                    .map(|names| file_info::old_names::of_names(&names)),
            };
        let new_names =
            naming_table::get_file_info(new_naming_table, path).map(|i| file_info::simplify(&i));
        match (old_names, new_names) {
            (None, None) => {}
            (old_names, new_names) => {
                acc.insert(
                    path.clone(),
                    versioned_names::T {
                        old_names: old_names.unwrap_or_else(file_info::old_names::empty),
                        new_names: new_names.unwrap_or_else(file_info::empty_names),
                    },
                );
            }
        }
    }
    acc
}

/// If the only things that would change about file analysis are positions,
/// we're not going to recheck it, and positions in its error list might
/// become stale. Look if any of those positions refer to files that have
/// actually changed and add them to files to recheck.
///
/// `reparsed`: Set of files that were reparsed (so their ASTs and positions
/// in them could have changed.
///
/// `diagnostics`: Current global diagnostic list
fn add_files_with_stale_errors(
    ctx: &Arc<Ctx>,
    reparsed: &RPSet,
    diagnostics: &Diag,
    files_acc: RPSet,
) -> RPSet {
    diagnostics::fold_errors(None, diagnostics, files_acc, |source, error, mut acc| {
        if user_diagnostic::to_list_(error).iter().any(|e| {
            reparsed.contains(naming_provider::resolve_position(ctx, &e.0).filename())
        }) {
            acc.insert(source.clone());
            acc
        } else {
            acc
        }
    })
}

/// `resolve_files ctx ~reparsed env fanout`
pub fn resolve_files(ctx: &Arc<Ctx>, reparsed: &RPSet, env: &Env, fanout: &fanout::T) -> RPSet {
    server_progress::with_message(None, None, "resolving files", || {
        let fanout::T {
            changed: _,
            to_recheck,
            to_recheck_if_errors,
        } = fanout;
        let deps_mode = provider_context::get_deps_mode(ctx);
        let dependent_on_files = reparsed.iter().fold(dep_set::make(), |depset, file| {
            let file_dep = dep::Variant::File(file.clone());
            let file_dependents = typing_deps::get_ideps(&deps_mode, &file_dep);
            dep_set::union(&depset, &file_dependents)
        });
        let to_recheck = dep_set::union(&dependent_on_files, to_recheck);
        let files_to_recheck = naming_provider::get_files(ctx, &to_recheck);
        let files_with_errors_to_recheck = {
            let files_with_errors: RPSet = diagnostics::get_failed_files(&env.diagnostics)
                .into_iter()
                .collect();
            let files_to_recheck_if_errors = naming_provider::get_files(ctx, to_recheck_if_errors);
            files_with_errors.intersection(files_to_recheck_if_errors)
        };
        let files = files_to_recheck.union(files_with_errors_to_recheck);
        hh_logger::log(&format!(
            "{}:\n{}",
            if files.len() <= 10 {
                "Files to recheck"
            } else {
                "First 10 files to recheck"
            },
            files
                .iter()
                .take(10)
                .map(relative_path::suffix)
                .collect::<Vec<_>>()
                .join("\n")
        ));
        files
    })
}

/// `get_files_to_recheck ctx env fanout ~reparsed ~diagnostics`
pub fn get_files_to_recheck(
    ctx: &Arc<Ctx>,
    env: &Env,
    fanout: &fanout::T,
    reparsed: &RPSet,
    diagnostics: &Diag,
) -> RPSet {
    let files = resolve_files(ctx, reparsed, env, fanout);
    // We want to also recheck files that have typing errors referring to files that were
    // reparsed, since positions in those errors can be now stale.
    add_files_with_stale_errors(ctx, reparsed, diagnostics, files)
}

#[cfg(test)]
mod tests {
    //! `test/unit/naming/old_names_tests.ml`, on file infos with given
    //! hashes rather than parsed files: a fresh context over a real SQLite
    //! naming baseline.

    use std::path::Path;

    use super::*;
    use crate::relative_path::Prefix;

    struct TestEnv {
        ctx: provider_context::T,
        baseline: naming_table::T,
        file_infos: RPMap<file_info::T>,
    }

    fn path(suffix: &str) -> relative_path::T {
        relative_path::from_root(suffix)
    }

    fn id(path: &relative_path::T, kind: file_info::NameType, name: &str, hash: i64) -> file_info::Id {
        file_info::Id {
            pos: file_info::Pos::File(kind, Arc::new(path.clone())),
            name: name.to_string(),
            decl_hash: Some(file_info::decl_hash::from_naming_table(hash)),
        }
    }

    fn file_info(ids: file_info::Ids) -> file_info::T {
        file_info::FileInfo {
            position_free_decl_hash: file_info::HashType(Some(1)),
            file_mode: Some(file_info::Mode::Mstrict),
            ids,
            comments: None,
        }
    }

    fn with_env(name: &str, files: &[(&str, file_info::T)], f: impl FnOnce(&TestEnv)) {
        for (prefix, dir) in [
            (Prefix::Root, "/tmp/hh-old-names-test-root"),
            (Prefix::Hhi, "/tmp/hh-old-names-test-hhi"),
            (Prefix::Tmp, "/tmp/hh-old-names-test-tmp"),
        ] {
            if relative_path::path_of_prefix(prefix).is_err() {
                relative_path::set_path_prefix(prefix, Path::new(dir));
            }
        }
        let ctx = Arc::new(Ctx::new(Path::new("/tmp/hh-old-names-test-root"), Default::default()).unwrap());
        ctx.build_reverse_naming_table();
        let file_infos: RPMap<file_info::T> = files
            .iter()
            .map(|(suffix, info)| (path(suffix), info.clone()))
            .collect();
        let dir = std::env::temp_dir().join(format!("hh_old_names_tests_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let db_path = dir.join(format!("{}.sqlite", name)).display().to_string();
        let _ = std::fs::remove_file(&db_path);
        let saved = naming_table::save(&naming_table::create(file_infos.clone()), &db_path).unwrap();
        assert!(saved.errors.is_empty());
        let baseline = naming_table::load_from_sqlite(&ctx, &db_path).unwrap();
        f(&TestEnv {
            ctx,
            baseline,
            file_infos,
        });
        crate::naming_sqlite::free_db_cache();
        let _ = std::fs::remove_file(&db_path);
    }

    fn assert_winner_hashes(winner: &file_info::T, old_names: &file_info::old_names::T) {
        let check = |ids: &[file_info::Id], hashes: &s_map::T<Option<file_info::decl_hash::T>>| {
            assert_eq!(ids.len(), hashes.len(), "all old symbols are retained");
            for id in ids {
                assert_eq!(
                    hashes.get(&id.name),
                    Some(&Some(id.decl_hash.unwrap())),
                    "old winning hash for {}",
                    id.name
                );
            }
        };
        let file_info::Ids {
            funs,
            classes,
            typedefs,
            consts,
            modules,
        } = &winner.ids;
        check(funs, &old_names.funs);
        check(classes, &old_names.classes);
        check(typedefs, &old_names.types);
        check(consts, &old_names.consts);
        check(modules, &old_names.modules);
    }

    fn winner_ids(path: &relative_path::T, first_hash: i64) -> file_info::Ids {
        use file_info::NameType::*;
        file_info::Ids {
            funs: vec![id(path, Fun, "\\winner_fun", first_hash)],
            classes: vec![id(path, Class, "\\WinnerClass", first_hash + 1)],
            typedefs: vec![id(path, Typedef, "\\WinnerType", first_hash + 2)],
            consts: vec![id(path, Const, "\\WINNER_CONST", first_hash + 3)],
            modules: vec![id(path, Module, "WinnerModule", first_hash + 4)],
        }
    }

    /// Old records for duplicate symbols carry the same winning hashes. Merging
    /// those records must preserve their symbol keys and matching hashes.
    #[test]
    fn test_merge_winner_hashes() {
        let winner_path = path("winner.php");
        let loser_path = path("loser.php");
        with_env(
            "merge_winner_hashes",
            &[("winner.php", file_info(winner_ids(&winner_path, 10)))],
            |env| {
                // The fixture's SQLite baseline contains only winner.php, which owns all
                // five symbols in reverse naming.
                let winner = env.file_infos.get(&winner_path).unwrap().clone();
                let loser = file_info(winner_ids(&loser_path, 20));
                // Add the duplicate to the forward overlay while reverse naming still
                // selects winner.php. This bypasses normal naming-conflict tracking.
                let previous = naming_table::update(&env.baseline, loser_path.clone(), loser);
                // Include both conflicting files, as required by get_old_names_batch.
                // The winner is unchanged and the loser removes its declarations.
                let snapshot = get_old_names_batch(
                    &env.ctx,
                    &previous,
                    &[
                        (winner_path.clone(), winner.clone()),
                        (loser_path.clone(), file_info::empty_t()),
                    ]
                    .into_iter()
                    .collect(),
                );
                assert_eq!(snapshot.len(), 2, "both conflicting files belong to this snapshot");
                let winner_names = snapshot.get(&winner_path).unwrap();
                let loser_names = snapshot.get(&loser_path).unwrap();
                assert_winner_hashes(&winner, winner_names);
                assert_winner_hashes(&winner, loser_names);
                // Matching hashes must survive merging old records from different files.
                assert_winner_hashes(
                    &winner,
                    &file_info::old_names::merge(winner_names, loser_names),
                );
            },
        );
    }

    /// Exercise first-occurrence selection and declaration-kind matching in an
    /// old file's forward overlay. The first function/constant occurrences remain
    /// the expected definitions; a later duplicate must not supply their hashes.
    /// An explicitly unknown first hash must remain unknown, even when another
    /// occurrence or SQLite has a known hash.
    ///
    /// The class owns Guarded in the shared type namespace, so the losing typedef
    /// retains its name with an unknown hash while the class keeps its own hash.
    /// This is a direct helper test with synthetic metadata, including an injected
    /// [None] hash; it does not run naming or oldify declarations.
    #[test]
    fn test_overlay_first_hash() {
        use file_info::NameType::*;
        let path = path("guarded.php");
        let baseline_ids = file_info::Ids {
            funs: vec![id(&path, Fun, "\\guarded_fun", 31)],
            classes: vec![id(&path, Class, "\\Guarded", 32)],
            consts: vec![id(&path, Const, "\\UNKNOWN", 33)],
            ..file_info::empty_ids()
        };
        with_env(
            "overlay_first_hash",
            &[("guarded.php", file_info(baseline_ids))],
            |env| {
                // Append duplicates after the baseline declarations. The typedef also
                // conflicts with the class. Make only the selected first constant's
                // hash unknown. The second occurrence and the original SQLite
                // declaration still have known hashes.
                let info = file_info(file_info::Ids {
                    funs: vec![
                        id(&path, Fun, "\\guarded_fun", 41),
                        id(&path, Fun, "\\guarded_fun", 42),
                    ],
                    classes: vec![id(&path, Class, "\\Guarded", 43)],
                    typedefs: vec![id(&path, Typedef, "\\Guarded", 44)],
                    consts: vec![
                        file_info::Id {
                            decl_hash: None,
                            ..id(&path, Const, "\\UNKNOWN", 45)
                        },
                        id(&path, Const, "\\UNKNOWN", 46),
                    ],
                    modules: vec![],
                });
                // Treat this metadata as the old contents of guarded.php. Reverse naming
                // still selects the baseline bindings; only the forward overlay changes.
                let previous = naming_table::update(&env.baseline, path.clone(), info.clone());
                let snapshot = get_old_names_batch(
                    &env.ctx,
                    &previous,
                    &[(path.clone(), info.clone())].into_iter().collect(),
                );
                let old_names = snapshot.get(&path).unwrap();
                // Select the first occurrence, rather than the later function.
                assert_eq!(
                    old_names.funs.get("\\guarded_fun"),
                    Some(&info.ids.funs[0].decl_hash),
                    "the first function occurrence supplies the old hash"
                );
                // Do not replace an unknown selected hash with a known duplicate or DB hash.
                assert_eq!(
                    old_names.consts.get("\\UNKNOWN"),
                    Some(&None),
                    "the first constant's unknown hash is not replaced by a later or database hash"
                );
                // The type winner is a class. Neither its hash nor the losing typedef's
                // own hash is a valid expected old typedef hash.
                assert_eq!(
                    old_names.types.get("\\Guarded"),
                    Some(&None),
                    "a typedef cannot borrow the winning class hash"
                );
                // The class's matching kind allows its known hash to be retained.
                assert_eq!(
                    old_names.classes.get("\\Guarded"),
                    Some(&info.ids.classes[0].decl_hash),
                    "the unique class retains its own hash"
                );
            },
        );
    }
}
