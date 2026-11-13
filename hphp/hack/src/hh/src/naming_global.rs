// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/naming_global.ml`: binding the names of files in the
//! reverse naming table (the daemon's table of the `Ctx`, plan D4), and the
//! conflict files.
//!
//! The lookups of the OCaml (`Naming_provider.get_*_pos`,
//! `get_*_canon_name`) are those of the reverse naming table here
//! (`crate::naming_heap`): the daemon's context has no entries, so the
//! OCaml's answers are those of its backend's table, which is this one; the
//! `Naming_provider` lookups of this crate answer from the decl stores,
//! which are being updated while the names are. The changes go through
//! `Naming_provider` (`add_*`, `remove_*_batch`), as in the OCaml.
//!
//! `File_provider_stale` (`GEnv.file_disappeared_under_our_feet`) is raised as
//! `std::panic::panic_any(FileProviderStale)`, as elsewhere in this crate
//! (`crate::file_provider`).
//!
//! Owned by **N1** (plan §3.1).

use std::sync::Arc;

use oxidized::naming_types::KindOfType;

use crate::ctx::Ctx;
use crate::file_info;
use crate::file_info::NameType;
use crate::naming_heap;
use crate::naming_provider;
use crate::relative_path::RelativePath;

type RPSet = crate::relative_path::set::T;

const CATEGORY: &str = "naming_global";

/// `GEnv`
mod genv {
    use super::*;

    /// This function logs and error and raises an exception,
    /// ultimately causing the typechecker to terminate.
    /// Why? We looked for a file in the file heap, but it was deleted
    /// before we could get it. This occurs with highest probability when we
    /// have multiple large rebases in quick succession, and the typechecker
    /// doesn't get updates from the file watcher while checking. For now, we restart
    /// gracefully, but in future versions we'll be restarting the server on
    /// large rebases anyhow, so this is sufficient behavior.
    pub fn file_disappeared_under_our_feet((pos, name): (&file_info::Pos, &str)) -> ! {
        let fn_ = file_info::get_pos_filename(pos);
        crate::hh_logger::log(&format!(
            "File missing: {}",
            crate::relative_path::to_absolute(&fn_)
        ));
        crate::hh_logger::log(&format!("Name missing: {}", name));
        std::panic::panic_any(crate::file_provider::FileProviderStale)
    }

    pub fn get_fun_full_pos(ctx: &Arc<Ctx>, (pos, name): (&file_info::Pos, &str)) -> oxidized::pos::Pos {
        match naming_provider::get_fun_full_pos_by_parsing_file(ctx, (pos, name)) {
            Some(pos) => pos,
            None => file_disappeared_under_our_feet((pos, name)),
        }
    }

    pub fn get_type_full_pos(ctx: &Arc<Ctx>, (pos, name): (&file_info::Pos, &str)) -> oxidized::pos::Pos {
        match naming_provider::get_type_full_pos_by_parsing_file(ctx, (pos, name)) {
            Some(pos) => pos,
            None => file_disappeared_under_our_feet((pos, name)),
        }
    }

    pub fn get_const_full_pos(ctx: &Arc<Ctx>, (pos, name): (&file_info::Pos, &str)) -> oxidized::pos::Pos {
        match naming_provider::get_const_full_pos_by_parsing_file(ctx, (pos, name)) {
            Some(pos) => pos,
            None => file_disappeared_under_our_feet((pos, name)),
        }
    }

    pub fn get_module_full_pos(
        ctx: &Arc<Ctx>,
        (pos, name): (&file_info::Pos, &str),
    ) -> oxidized::pos::Pos {
        match naming_provider::get_module_full_pos_by_parsing_file(ctx, (pos, name)) {
            Some(pos) => pos,
            None => file_disappeared_under_our_feet((pos, name)),
        }
    }

    pub fn type_pos(ctx: &Arc<Ctx>, name: &str) -> Option<oxidized::pos::Pos> {
        match naming_heap::types::get_pos(ctx, name) {
            Some((pos, _kind)) => Some(get_type_full_pos(ctx, (&pos, name))),
            None => None,
        }
    }

    #[allow(dead_code)]
    pub fn type_info(ctx: &Arc<Ctx>, name: &str) -> Option<(oxidized::pos::Pos, KindOfType)> {
        match naming_heap::types::get_pos(ctx, name) {
            Some((pos, kind @ (KindOfType::TClass | KindOfType::TTypedef))) => {
                Some((get_type_full_pos(ctx, (&pos, name)), kind))
            }
            None => None,
        }
    }

    pub fn fun_pos(ctx: &Arc<Ctx>, name: &str) -> Option<oxidized::pos::Pos> {
        match naming_heap::funs::get_pos(ctx, name) {
            Some(pos) => Some(get_fun_full_pos(ctx, (&pos, name))),
            None => None,
        }
    }

    #[allow(dead_code)]
    pub fn typedef_pos(ctx: &Arc<Ctx>, name: &str) -> Option<oxidized::pos::Pos> {
        match naming_heap::types::get_pos(ctx, name) {
            Some((pos, KindOfType::TTypedef)) => Some(get_type_full_pos(ctx, (&pos, name))),
            Some((_, KindOfType::TClass)) | None => None,
        }
    }

    pub fn gconst_pos(ctx: &Arc<Ctx>, name: &str) -> Option<oxidized::pos::Pos> {
        match naming_heap::consts::get_pos(ctx, name) {
            Some(pos) => Some(get_const_full_pos(ctx, (&pos, name))),
            None => None,
        }
    }

    pub fn module_pos(ctx: &Arc<Ctx>, name: &str) -> Option<oxidized::pos::Pos> {
        match naming_heap::modules::get_pos(ctx, name) {
            Some(pos) => Some(get_module_full_pos(ctx, (&pos, name))),
            None => None,
        }
    }
}

/// Given name-and-position [id], compared to the [canonical_id] name-and-position,
/// this judges whether we should report [id] as "already bound".
///
/// This is surprising. Notionally you'd expect that the mere existence of
/// a canonical_id means that we should report [id] as already-bound.
/// But this function has some historical quirks:
/// - The function was written to support [id] being a file-only
///   position. But in practice it's always a full position that comes
///   from parsing. If we encounter a file-only position, we log this
///   anomalous path.
/// - The function was written so that if you declare [id], but it's
///   in the exact same file+position as [canonical_id], then you must
///   be declaring the same name and hence shouldn't report it as
///   already-bound. This path should never arise (since a file's
///   previous names all get removed before we decl that file);
///   we log this anomalous path.
/// - From the way this function is invoked, [canonical_id] should
///   always be either in a different file (meaning that the user declared
///   a symbol in the currently-being-declared file which conflicts with another
///   file), or in the same file (meaning that the user declared two conflicting
///   symbols in the same file). The parameter [current_file_symbols_acc]
///   gathers all the symbol positions we've declared so far from the current file.
///   If we encounter a [canonical_id] that's in the same file but not already in
///   [current_file_symbols_acc], that's anomalous, and we log it.
fn should_report_duplicate(
    ctx: &Arc<Ctx>,
    fi: &file_info::Ids,
    current_file_symbols_acc: &[file_info::Pos],
    id: &file_info::Id,
    canonical_id: &file_info::Id,
) -> bool {
    use file_info::Pos::File;
    use file_info::Pos::Full;
    let p = &id.pos;
    let name = &id.name;
    let pc = &canonical_id.pos;
    let canonical = &canonical_id.name;
    // helper, for the various paths below which want to log a bug
    let bug = |desc: &str| {
        crate::hh_logger::log(&format!(
            "INVARIANT_VIOLATION_BUG [{}] {} {}",
            desc,
            name,
            file_info::show_pos(p)
        ));
        eprintln!(
            "{}",
            crate::exception::clean_stack(&crate::exception::get_current_callstack_string(99))
        );
        let telemetry = crate::telemetry::create();
        let telemetry = crate::telemetry::string_(None, "name", name, telemetry);
        let telemetry = crate::telemetry::string_(None, "canonical_name", canonical, telemetry);
        let telemetry = crate::telemetry::string_(
            None,
            "canonical_path",
            &crate::relative_path::to_absolute(&file_info::get_pos_filename(pc)),
            telemetry,
        );
        let telemetry = crate::telemetry::string_(None, "fileinfo", &file_info::show_ids(fi), telemetry);
        crate::hack_event_logger::invariant_violation_bug(
            Some(&file_info::get_pos_filename(p)),
            None,
            None,
            None,
            Some(&telemetry),
            desc,
        );
    };
    // Detect anomaly where we're given a file-only [id]
    match p {
        Full(_) => {}
        File(..) => bug("naming_duplicate_file_only_p"),
    }
    let same = |a: &oxidized::pos::Pos, b: &oxidized::pos::Pos| {
        crate::pos::compare(a, b) == std::cmp::Ordering::Equal
    };
    let is_same_pos = match (pc, p) {
        (Full(a), Full(b)) => same(a, b),
        (a @ File(NameType::Fun, _), Full(b)) | (Full(b), a @ File(NameType::Fun, _)) => {
            let a = genv::get_fun_full_pos(ctx, (a, canonical));
            same(&a, b)
        }
        (a @ File(NameType::Const, _), Full(b)) | (Full(b), a @ File(NameType::Const, _)) => {
            let a = genv::get_const_full_pos(ctx, (a, canonical));
            same(&a, b)
        }
        (a @ File(NameType::Class | NameType::Typedef, _), Full(b))
        | (Full(b), a @ File(NameType::Class | NameType::Typedef, _)) => {
            let a = genv::get_type_full_pos(ctx, (a, canonical));
            same(&a, b)
        }
        (a @ File(NameType::Module, _), Full(b)) | (Full(b), a @ File(NameType::Module, _)) => {
            let a = genv::get_module_full_pos(ctx, (a, canonical));
            same(&a, b)
        }
        (File(a, fna), File(b, fnb)) => {
            crate::relative_path::equal(fna, fnb) && file_info::equal_name_type(*a, *b)
        }
    };
    // Detect anomaly if [id] and [canonical_id] are identical positions
    if is_same_pos {
        bug("naming_duplicate_same")
    }
    // Detect anomaly where [canonical_id] is in the same file but not found in [current_file_symbols_acc]
    if !is_same_pos
        && crate::relative_path::equal(
            &file_info::get_pos_filename(pc),
            &file_info::get_pos_filename(p),
        )
        && !current_file_symbols_acc
            .iter()
            .any(|x| file_info::equal_pos(x, pc))
    {
        bug("naming_duplicate_same_file_not_acc")
    }
    // Finally, should we report duplicates? Generally yes, except in that same anomalous case!
    !is_same_pos
}

/// The primitives to manipulate the naming environment
mod env {
    use super::*;

    pub fn new_fun_skip_if_already_bound(ctx: &Arc<Ctx>, fn_: &RelativePath, id: &file_info::Id) {
        match naming_heap::funs::get_canon_name(ctx, &id.name) {
            Some(_) => {}
            None => {
                let backend = ctx;
                naming_provider::add_fun(
                    backend,
                    &id.name,
                    &file_info::Pos::File(NameType::Fun, Arc::new(fn_.clone())),
                )
            }
        }
    }

    pub fn new_type_skip_if_already_bound(
        ctx: &Arc<Ctx>,
        fn_: &RelativePath,
        kind: KindOfType,
        id: &file_info::Id,
    ) {
        let name_type = NameType::from(kind);
        match naming_heap::types::get_canon_name(ctx, &id.name) {
            Some(_) => {}
            None => {
                let backend = ctx;
                // We store redundant info in this case, but if the position is a
                // Full position, we don't store the kind, so this is necessary
                naming_provider::add_type(
                    backend,
                    &id.name,
                    &file_info::Pos::File(name_type, Arc::new(fn_.clone())),
                    kind,
                )
            }
        }
    }

    pub fn new_global_const_skip_if_already_bound(
        ctx: &Arc<Ctx>,
        fn_: &RelativePath,
        id: &file_info::Id,
    ) {
        let backend = ctx;
        naming_provider::add_const(
            backend,
            &id.name,
            &file_info::Pos::File(NameType::Const, Arc::new(fn_.clone())),
        )
    }

    pub fn new_fun_error_if_already_bound(
        ctx: &Arc<Ctx>,
        fi: &file_info::Ids,
        (mut current_file_symbols_acc, is_okay_acc): (Vec<file_info::Pos>, bool),
        id: &file_info::Id,
    ) -> (Vec<file_info::Pos>, bool) {
        let p = &id.pos;
        let name = &id.name;
        match naming_heap::funs::get_canon_name(ctx, name) {
            Some(canonical) => {
                let pos = naming_heap::funs::get_pos(ctx, &canonical).expect("Option.value_exn");
                let name = canonical;
                let decl_hash = None;
                let is_error = should_report_duplicate(
                    ctx,
                    fi,
                    &current_file_symbols_acc,
                    id,
                    &file_info::Id {
                        pos,
                        name,
                        decl_hash,
                    },
                );
                (current_file_symbols_acc, is_okay_acc && !is_error)
            }
            None => {
                let backend = ctx;
                naming_provider::add_fun(backend, name, p);
                current_file_symbols_acc.insert(0, p.clone());
                (current_file_symbols_acc, is_okay_acc)
            }
        }
    }

    pub fn new_type_error_if_already_bound(
        ctx: &Arc<Ctx>,
        fi: &file_info::Ids,
        kind: KindOfType,
        (mut current_file_symbols_acc, is_okay_acc): (Vec<file_info::Pos>, bool),
        id: &file_info::Id,
    ) -> (Vec<file_info::Pos>, bool) {
        let p = &id.pos;
        let name = &id.name;
        match naming_heap::types::get_canon_name(ctx, name) {
            Some(canonical) => {
                let pos = naming_heap::types::get_pos(ctx, &canonical)
                    .map(|(pos, _kind)| pos)
                    .expect("Option.value_exn");
                let name = canonical;
                let decl_hash = None;
                let is_error = should_report_duplicate(
                    ctx,
                    fi,
                    &current_file_symbols_acc,
                    id,
                    &file_info::Id {
                        pos,
                        name,
                        decl_hash,
                    },
                );
                (current_file_symbols_acc, is_okay_acc && !is_error)
            }
            None => {
                let backend = ctx;
                naming_provider::add_type(backend, name, p, kind);
                current_file_symbols_acc.insert(0, p.clone());
                (current_file_symbols_acc, is_okay_acc)
            }
        }
    }

    pub fn new_global_const_error_if_already_bound(
        ctx: &Arc<Ctx>,
        fi: &file_info::Ids,
        (mut current_file_symbols_acc, is_okay_acc): (Vec<file_info::Pos>, bool),
        id: &file_info::Id,
    ) -> (Vec<file_info::Pos>, bool) {
        let p = &id.pos;
        let name = &id.name;
        match naming_heap::consts::get_pos(ctx, name) {
            Some(pos) => {
                let decl_hash = None;
                let is_error = should_report_duplicate(
                    ctx,
                    fi,
                    &current_file_symbols_acc,
                    id,
                    &file_info::Id {
                        pos,
                        name: name.clone(),
                        decl_hash,
                    },
                );
                (current_file_symbols_acc, is_okay_acc && !is_error)
            }
            None => {
                let backend = ctx;
                naming_provider::add_const(backend, name, p);
                current_file_symbols_acc.insert(0, p.clone());
                (current_file_symbols_acc, is_okay_acc)
            }
        }
    }

    pub fn new_module_skip_if_already_bound(ctx: &Arc<Ctx>, fn_: &RelativePath, id: &file_info::Id) {
        let backend = ctx;
        naming_provider::add_module(
            backend,
            &id.name,
            &file_info::Pos::File(NameType::Module, Arc::new(fn_.clone())),
        )
    }

    pub fn new_module_error_if_already_bound(
        ctx: &Arc<Ctx>,
        fi: &file_info::Ids,
        (mut current_file_symbols_acc, is_okay_acc): (Vec<file_info::Pos>, bool),
        id: &file_info::Id,
    ) -> (Vec<file_info::Pos>, bool) {
        let p = &id.pos;
        let name = &id.name;
        match naming_heap::modules::get_pos(ctx, name) {
            Some(pos) => {
                let decl_hash = None;
                let is_error = should_report_duplicate(
                    ctx,
                    fi,
                    &current_file_symbols_acc,
                    id,
                    &file_info::Id {
                        pos,
                        name: name.clone(),
                        decl_hash,
                    },
                );
                (current_file_symbols_acc, is_okay_acc && !is_error)
            }
            None => {
                let backend = ctx;
                naming_provider::add_module(backend, name, p);
                current_file_symbols_acc.insert(0, p.clone());
                (current_file_symbols_acc, is_okay_acc)
            }
        }
    }
}

/// `remove_decls ~backend ~funs ~classes ~typedefs ~consts ~modules`
pub fn remove_decls(
    backend: &Ctx,
    funs: &[String],
    classes: &[String],
    typedefs: &[String],
    consts: &[String],
    modules: &[String],
) {
    let types: Vec<String> = typedefs.iter().chain(classes.iter()).cloned().collect();
    naming_provider::remove_type_batch(backend, &types);
    naming_provider::remove_fun_batch(backend, funs);
    naming_provider::remove_const_batch(backend, consts);
    naming_provider::remove_module_batch(backend, modules);
}

/// `remove_decls_using_file_info backend ids`
pub fn remove_decls_using_file_info(backend: &Ctx, ids: &file_info::Ids) {
    let id_name = |ids: &[file_info::Id]| ids.iter().map(|id| id.name.clone()).collect::<Vec<_>>();
    let file_info::Ids {
        funs,
        classes,
        typedefs,
        consts,
        modules,
    } = ids;
    remove_decls(
        backend,
        &id_name(funs),
        &id_name(classes),
        &id_name(typedefs),
        &id_name(consts),
        &id_name(modules),
    )
}

// ---------------------------------------------------------------------------
// The entry point to build the naming environment
// ---------------------------------------------------------------------------

/// return true if no names were already bound; returns false if some were
fn make_env_and_check_not_already_bound(ctx: &Arc<Ctx>, ids: &file_info::Ids) -> bool {
    let file_info::Ids {
        classes,
        funs,
        modules,
        typedefs,
        consts,
    } = ids;
    let is_okay = true;
    // funs
    let (_, is_okay) = funs.iter().fold((vec![], is_okay), |acc, id| {
        env::new_fun_error_if_already_bound(ctx, ids, acc, id)
    });
    // types
    let (current_file_symbols_acc, is_okay) = classes.iter().fold((vec![], is_okay), |acc, id| {
        env::new_type_error_if_already_bound(ctx, ids, KindOfType::TClass, acc, id)
    });
    let (_, is_okay) = typedefs
        .iter()
        .fold((current_file_symbols_acc, is_okay), |acc, id| {
            env::new_type_error_if_already_bound(ctx, ids, KindOfType::TTypedef, acc, id)
        });
    // consts
    let (_, is_okay) = consts.iter().fold((vec![], is_okay), |acc, id| {
        env::new_global_const_error_if_already_bound(ctx, ids, acc, id)
    });
    // modules
    let (_, is_okay) = modules.iter().fold((vec![], is_okay), |acc, id| {
        env::new_module_error_if_already_bound(ctx, ids, acc, id)
    });
    is_okay
}

fn make_env_skip_if_already_bound(ctx: &Arc<Ctx>, fn_: &RelativePath, fileinfo: &file_info::Ids) {
    for id in &fileinfo.funs {
        env::new_fun_skip_if_already_bound(ctx, fn_, id)
    }
    for id in &fileinfo.classes {
        env::new_type_skip_if_already_bound(ctx, fn_, KindOfType::TClass, id)
    }
    for id in &fileinfo.typedefs {
        env::new_type_skip_if_already_bound(ctx, fn_, KindOfType::TTypedef, id)
    }
    for id in &fileinfo.consts {
        env::new_global_const_skip_if_already_bound(ctx, fn_, id)
    }
    for id in &fileinfo.modules {
        env::new_module_skip_if_already_bound(ctx, fn_, id)
    }
}

// ---------------------------------------------------------------------------
// Declaring the names in a list of files
// ---------------------------------------------------------------------------

fn add_files_to_rename(
    failed: RPSet,
    defl: &[file_info::Id],
    defs_in_env: impl Fn(&str) -> Option<oxidized::pos::Pos>,
) -> RPSet {
    defl.iter().fold(failed, |mut failed, id| match defs_in_env(&id.name) {
        None => failed,
        Some(previous_definition_position) => {
            let filename = previous_definition_position.filename();
            failed.insert(RelativePath::clone(filename));
            failed
        }
    })
}

/// `ndecl_file_skip_if_already_bound ctx fn ids`
pub fn ndecl_file_skip_if_already_bound(ctx: &Arc<Ctx>, fn_: &RelativePath, ids: &file_info::Ids) {
    make_env_skip_if_already_bound(ctx, fn_, ids)
}

/// `ndecl_file_and_get_conflict_files ctx fn ids`
pub fn ndecl_file_and_get_conflict_files(
    ctx: &Arc<Ctx>,
    fn_: &RelativePath,
    ids: &file_info::Ids,
) -> RPSet {
    crate::hh_logger::debug(
        Some(CATEGORY),
        None,
        &format!("Naming decl: {}", crate::relative_path::to_absolute(fn_)),
    );
    let is_okay = make_env_and_check_not_already_bound(ctx, ids);
    if is_okay {
        RPSet::new()
    } else {
        // IMPORTANT:
        // If a file has name collisions, we MUST add the list of files that
        // were previously defining the type to the set of "failed" files.
        // If we fail to do so, we will be in a phony state, where a name could
        // be missing.
        //
        // Example:
        // A.php defines class A
        // B.php defines class B
        // Save the state, now let's introduce a new file (foo.php):
        // foo.php defines class A and class B.
        //
        // 2 things happen (cf serverTypeCheck.ml):
        // We remove the names A and B from the global environment.
        // We report the error.
        //
        // But this is clearly not enough. If the user removes the file foo.php,
        // both class A and class B are now missing from the naming environment.
        // If the user has a file using class A (in strict), he now gets the
        // error "Unbound name class A".
        //
        // The solution consist in adding all the files that were previously
        // defining the same things as foo.php to the set of files to recheck.
        //
        // This way, when the user removes foo.php, A.php and B.php are recomputed
        // and the naming environment is in a sane state.
        //
        // XXX (jezng): we can probably be less conservative about this -- instead
        // of adding all the declarations in the file, why not just add those that
        // were actually duplicates?
        let type_canon_pos = |name: &str| {
            naming_heap::types::get_canon_name(ctx, name).and_then(|name| genv::type_pos(ctx, &name))
        };
        let fun_canon_pos = |name: &str| {
            naming_heap::funs::get_canon_name(ctx, name).and_then(|name| genv::fun_pos(ctx, &name))
        };

        let file_info::Ids {
            classes,
            typedefs,
            funs,
            consts,
            modules,
        } = ids;
        let failed = RPSet::unit(fn_.clone());
        let failed = add_files_to_rename(failed, funs, fun_canon_pos);
        let failed = add_files_to_rename(failed, classes, type_canon_pos);
        let failed = add_files_to_rename(failed, typedefs, type_canon_pos);
        let failed = add_files_to_rename(failed, consts, |name| genv::gconst_pos(ctx, name));
        add_files_to_rename(failed, modules, |name| genv::module_pos(ctx, name))
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;

    /// The daemon's context after an init of `files`, with their file infos
    /// (as `Direct_decl_service` makes them).
    fn init(files: &[(&str, &str)]) -> (Arc<Ctx>, crate::relative_path::map::T<file_info::T>) {
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, Path::new("/nonexistent"));
        let ctx = Arc::new(Ctx::new(Path::new("/nonexistent"), TypecheckerOptions::default()).unwrap());
        let mut paths = vec![];
        for (name, contents) in files {
            let path = crate::relative_path::from_root(name);
            ctx.files.set((&path).into(), *contents);
            paths.push(path);
        }
        let infos = crate::direct_decl_service::go(&ctx, &paths, false, crate::direct_decl_service::DeclMode::Normal);
        ctx.build_dep_hash_index();
        (ctx, infos)
    }

    fn rp(name: &str) -> RelativePath {
        crate::relative_path::from_root(name)
    }

    fn set(paths: &[&str]) -> RPSet {
        paths.iter().map(|p| rp(p)).collect()
    }

    /// `update_reverse_naming_table_from_env_and_get_duplicate_name_errors`
    /// of the init, sequentially, and its `failed_naming`.
    fn name_all(ctx: &Arc<Ctx>, infos: &crate::relative_path::map::T<file_info::T>) -> RPSet {
        infos.iter().fold(RPSet::new(), |failed, (path, fi)| {
            failed.union(ndecl_file_and_get_conflict_files(ctx, path, &fi.ids))
        })
    }

    fn type_file(ctx: &Ctx, name: &str) -> Option<RelativePath> {
        naming_heap::types::get_pos(ctx, name).map(|(pos, _)| file_info::get_pos_filename(&pos))
    }

    #[test]
    fn bind_and_remove() {
        let (ctx, infos) = init(&[
            ("a.php", "<?hh\nclass A {}\nfunction f(): void {}\nconst int K = 1;\nnew module m {}\n"),
            ("b.php", "<?hh\nclass B {}\n"),
        ]);
        assert!(name_all(&ctx, &infos).is_empty());
        assert_eq!(type_file(&ctx, "\\A"), Some(rp("a.php")));
        // Positions are those of the decls (`Full`).
        assert!(matches!(naming_heap::funs::get_pos(&ctx, "\\f"), Some(file_info::Pos::Full(_))));
        assert_eq!(naming_heap::types::get_canon_name(&ctx, "\\a"), Some("\\A".to_string()));
        remove_decls_using_file_info(&ctx, &infos.get(&rp("a.php")).unwrap().ids);
        assert_eq!(type_file(&ctx, "\\A"), None);
        assert_eq!(naming_heap::funs::get_canon_name(&ctx, "\\F"), None);
        assert_eq!(naming_heap::consts::get_pos(&ctx, "\\K"), None);
        assert_eq!(naming_heap::modules::get_pos(&ctx, "m"), None);
        assert_eq!(type_file(&ctx, "\\B"), Some(rp("b.php")));
        // Renaming it binds its names again.
        assert!(ndecl_file_and_get_conflict_files(&ctx, &rp("a.php"), &infos.get(&rp("a.php")).unwrap().ids).is_empty());
        assert_eq!(type_file(&ctx, "\\A"), Some(rp("a.php")));
    }

    #[test]
    fn skip_if_already_bound() {
        let (ctx, infos) = init(&[
            ("a.php", "<?hh\nclass A {}\nconst int K = 1;\n"),
            ("b.php", "<?hh\nclass a {}\nfunction g(): void {}\nconst int K = 2;\n"),
        ]);
        let a = &infos.get(&rp("a.php")).unwrap().ids;
        let b = &infos.get(&rp("b.php")).unwrap().ids;
        ndecl_file_skip_if_already_bound(&ctx, &rp("a.php"), a);
        ndecl_file_skip_if_already_bound(&ctx, &rp("b.php"), b);
        // Types and funs are skipped when bound (up to case), with `File`
        // positions; constants are always added, which keeps a.php's `K`
        // (a `Shared_mem` `add` does not overwrite).
        assert_eq!(
            naming_heap::types::get_pos(&ctx, "\\A"),
            Some((file_info::Pos::File(NameType::Class, Arc::new(rp("a.php"))), KindOfType::TClass))
        );
        assert_eq!(naming_heap::types::get_pos(&ctx, "\\a"), None);
        assert_eq!(
            naming_heap::consts::get_pos(&ctx, "\\K"),
            Some(file_info::Pos::File(NameType::Const, Arc::new(rp("a.php"))))
        );
        assert_eq!(
            naming_heap::funs::get_pos(&ctx, "\\g"),
            Some(file_info::Pos::File(NameType::Fun, Arc::new(rp("b.php"))))
        );
    }

    /// Duplicates: the first file named wins (`Relative_path.Map` order at
    /// the init), the losers and the winners' files are the conflict files;
    /// in a recheck the previous winner stays bound (`do_naming`'s comment).
    #[test]
    fn conflict_files() {
        let (ctx, infos) = init(&[
            ("a.php", "<?hh\nclass A {}\nfunction mine(): void {}\n"),
            ("b.php", "<?hh\nfunction shared(): void {}\nfunction SHARED(): void {}\n"),
            ("c.php", "<?hh\nclass A {}\nconst int K = 1;\n"),
            ("d.php", "<?hh\nconst int K = 2;\ntype t = int;\n"),
            ("e.php", "<?hh\nclass T {}\nfunction mine2(): void {}\n"),
            ("f.php", "<?hh\nclass F {}\n"),
        ]);
        let failed = name_all(&ctx, &infos);
        assert_eq!(failed, set(&["a.php", "b.php", "c.php", "d.php", "e.php"]));
        assert_eq!(type_file(&ctx, "\\T"), None);
        assert_eq!(naming_heap::types::get_canon_name(&ctx, "\\T"), Some("\\t".to_string()));
        // A recheck of e.php and a new z.php declaring `F`: the names of
        // e.php are removed, then e.php and z.php named in order; f.php keeps
        // `F`.
        let z = rp("z.php");
        ctx.files.set((&z).into(), "<?hh\nclass F {}\n");
        let parsed = crate::direct_decl_service::go(&ctx, &[rp("e.php"), z.clone()], false, crate::direct_decl_service::DeclMode::Normal);
        remove_decls_using_file_info(&ctx, &infos.get(&rp("e.php")).unwrap().ids);
        // Removing e.php's `T` removed the canon entry of `\t` (d.php's),
        // whose position stays.
        assert_eq!(naming_heap::types::get_canon_name(&ctx, "\\t"), None);
        assert_eq!(type_file(&ctx, "\\t"), Some(rp("d.php")));
        let failed = parsed.iter().fold(RPSet::new(), |failed, (path, fi)| {
            failed.union(ndecl_file_and_get_conflict_files(&ctx, path, &fi.ids))
        });
        assert_eq!(failed, set(&["f.php", "z.php"]));
        assert_eq!(type_file(&ctx, "\\F"), Some(rp("f.php")));
        // e.php now binds `T` (the canon entry was gone).
        assert_eq!(type_file(&ctx, "\\T"), Some(rp("e.php")));
    }

    /// The init's `failed_naming` (`Ctx::take_init_conflict_files`, from the
    /// parallel binding of `Ctx::declare_file`) is what the OCaml's
    /// sequential naming of the files gives, and so are the winners.
    #[test]
    fn init_failed_naming_is_the_sequential_one() {
        let files: &[(&str, &str)] = &[
            ("0.php", "<?hh\nclass Alone {}\n"),
            ("a.php", "<?hh\nclass A {}\nfunction mine(): void {}\ntype TT = int;\n"),
            ("b.php", "<?hh\nfunction shared(): void {}\nfunction SHARED(): void {}\n"),
            ("c.php", "<?hh\nclass A {}\nconst int K = 1;\nclass tt {}\n"),
            ("d.php", "<?hh\nconst int K = 2;\ntype t = int;\nclass D {}\ntype D = string;\n"),
            ("dir/e.php", "<?hh\nclass T {}\nfunction Mine(): void {}\n"),
            ("f.php", "<?hh\nnew module m {}\nclass Lone {}\n"),
            ("g.php", "<?hh\nnew module m {}\n"),
            ("h.php", "<?hh\nclass H {}\nclass H {}\n"),
        ];
        // The init: parallel binding (here in reverse order), then the
        // conflict files from the forward table.
        let ctx = Arc::new(Ctx::new(Path::new("/nonexistent"), TypecheckerOptions::default()).unwrap());
        let mut nt = crate::relative_path::map::T::new();
        for (name, contents) in files.iter().rev() {
            let path = pos::RelativePath::new(pos::Prefix::Root, name);
            ctx.files.set(path, *contents);
            let decls = ctx.decl_parser.parse(path).unwrap();
            nt.insert(path.into(), crate::direct_decl_service::file_info_of_decls(path, &decls, None));
            ctx.declare_file(path, decls);
        }
        let init_failed = ctx.take_init_conflict_files(&crate::naming_table::create(nt));
        ctx.build_dep_hash_index();
        // The OCaml: every file named in order.
        let (seq, infos) = init(&[]);
        for (name, contents) in files {
            seq.files.set(pos::RelativePath::new(pos::Prefix::Root, name), *contents);
        }
        let _ = infos;
        let paths: Vec<RelativePath> = files.iter().map(|(name, _)| rp(name)).collect();
        let infos = crate::direct_decl_service::go(&seq, &paths, false, crate::direct_decl_service::DeclMode::Normal);
        let seq_failed = name_all(&seq, &infos);
        assert_eq!(init_failed, seq_failed);
        assert_eq!(
            seq_failed,
            set(&["a.php", "b.php", "c.php", "d.php", "dir/e.php", "f.php", "g.php", "h.php"])
        );
        // The same winners.
        for (_, fi) in infos.iter() {
            for id in fi.ids.classes.iter().chain(fi.ids.typedefs.iter()) {
                assert_eq!(type_file(&ctx, &id.name), type_file(&seq, &id.name), "{}", id.name);
                assert_eq!(
                    naming_heap::types::get_canon_name(&ctx, &id.name),
                    naming_heap::types::get_canon_name(&seq, &id.name)
                );
            }
            for id in &fi.ids.funs {
                assert_eq!(
                    naming_heap::funs::get_canon_name(&ctx, &id.name),
                    naming_heap::funs::get_canon_name(&seq, &id.name)
                );
            }
            for id in &fi.ids.consts {
                assert_eq!(
                    naming_heap::consts::get_pos(&ctx, &id.name).map(|p| file_info::get_pos_filename(&p)),
                    naming_heap::consts::get_pos(&seq, &id.name).map(|p| file_info::get_pos_filename(&p))
                );
            }
        }
        // The decls of the winners only, in the stores of the init.
        assert!(ctx.check_naming_invariant().is_ok());
    }

    /// The "hh_server / typing_check_service" view of `hh_single_decl
    /// --winners` (`name_and_then_print_name_results`) on the suite
    /// `hphp/hack/test/duplicates`: every file named in order, then the
    /// `Naming_provider` lookups (over the reverse naming table) of each
    /// toplevel name, against the expected outputs of the OCaml. Only the
    /// `Naming_provider` lines are compared (not the `Decl_provider` ones),
    /// and only the toplevels of the decl parser (not those of the AST, so
    /// not `ns.php`, where they differ).
    #[test]
    fn duplicates_suite_naming_provider() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../test/duplicates");
        for test in ["fun.php", "type.php", "const.php", "module.php", "type_conflict_behavior.php"] {
            let contents = std::fs::read(dir.join(test)).unwrap();
            let files = crate::multifile::file_to_file_list(test, &contents);
            let (ctx, _) = init(&[]);
            let mut toplevels = vec![];
            for (name, contents) in &files {
                let path = rp(name);
                ctx.files.set((&path).into(), bstr::BString::from(contents.clone()));
                let decls = crate::direct_decl_service::direct_decl_parse(&ctx, &path).unwrap();
                let fi = crate::direct_decl_service::decls_to_fileinfo(&path, &decls);
                let _conflict_filenames = ndecl_file_and_get_conflict_files(&ctx, &path, &fi.ids);
                let add = |toplevels: &mut Vec<_>, name_type, ids: &[file_info::Id]| {
                    for id in ids {
                        let file_info::Pos::Full(pos) = &id.pos else { unreachable!() };
                        toplevels.push((name_type, pos.clone(), id.name.clone()));
                    }
                };
                add(&mut toplevels, NameType::Fun, &fi.ids.funs);
                add(&mut toplevels, NameType::Class, &fi.ids.classes);
                add(&mut toplevels, NameType::Typedef, &fi.ids.typedefs);
                add(&mut toplevels, NameType::Const, &fi.ids.consts);
                add(&mut toplevels, NameType::Module, &fi.ids.modules);
            }
            // `compare_toplevels`
            toplevels.sort_by(|(at, ap, an), (bt, bp, bn)| {
                an.to_ascii_lowercase()
                    .cmp(&bn.to_ascii_lowercase())
                    .then_with(|| an.cmp(bn))
                    .then_with(|| file_info::compare_name_type(*at, *bt))
                    .then_with(|| crate::pos::compare(ap, bp))
            });
            toplevels.dedup();
            let pos_string = |pos: &oxidized::pos::Pos| {
                let (line, start, end) = pos.info_pos();
                format!(
                    "File \"{}\", line {}, characters {}-{}:",
                    crate::relative_path::suffix(pos.filename()),
                    line,
                    start,
                    end
                )
            };
            let show_pos = |pos: &file_info::Pos| match pos {
                file_info::Pos::Full(pos) => format!("(File_info.Full: {})", pos_string(pos)),
                file_info::Pos::File(name_type, fn_) => format!(
                    "(File_info.File: {} {:?})",
                    file_info::show_name_type(*name_type),
                    fn_
                ),
            };
            let mut out = vec![];
            for (name_type, pos, name) in &toplevels {
                out.push(format!(
                    "name={}, name_type={}, pos={}",
                    name,
                    file_info::show_name_type(*name_type),
                    pos_string(pos)
                ));
                let lower = file_info::show_name_type(*name_type).to_ascii_lowercase();
                let (exists, npos, canon) = match name_type {
                    NameType::Fun => (
                        naming_provider::fun_exists(&ctx, name),
                        naming_provider::get_fun_pos(&ctx, name),
                        naming_provider::get_fun_canon_name(&ctx, name),
                    ),
                    NameType::Class => (
                        naming_provider::get_class_path(&ctx, name).is_some(),
                        naming_provider::get_type_pos(&ctx, name),
                        naming_provider::get_type_canon_name(&ctx, name),
                    ),
                    NameType::Typedef => (
                        naming_provider::get_typedef_path(&ctx, name).is_some(),
                        naming_provider::get_type_pos(&ctx, name),
                        naming_provider::get_type_canon_name(&ctx, name),
                    ),
                    NameType::Const => (
                        naming_provider::const_exists(&ctx, name),
                        naming_provider::get_const_pos(&ctx, name),
                        Some("[undefined]".to_string()),
                    ),
                    NameType::Module => (
                        naming_provider::module_exists(&ctx, name),
                        naming_provider::get_module_pos(&ctx, name),
                        Some("[undefined]".to_string()),
                    ),
                };
                out.push(format!("   Naming_provider.{}_exists(name): {}", lower, exists));
                out.push(format!(
                    "   Naming_provider.get_{}_pos(name): {}",
                    lower,
                    npos.as_ref().map_or("[none]".to_string(), show_pos)
                ));
                out.push(format!(
                    "   Naming_provider.get_{}_canon_name(name): {}",
                    lower,
                    canon.unwrap_or("[none]".to_string())
                ));
            }
            let expected: Vec<String> = std::fs::read_to_string(dir.join(format!("{}.exp", test)))
                .unwrap()
                .lines()
                .filter(|line| {
                    line.starts_with("name=")
                        || (line.starts_with("   Naming_provider.")
                            && !line.ends_with("  [Provider_context.entry]"))
                })
                .map(|line| line.trim_end_matches("  [hh_server / typing_check_service]").to_string())
                .collect();
            // The blocks of the toplevels found by the AST only (whose
            // positions differ from those of the decls) are left out.
            let headers: std::collections::HashSet<&String> =
                out.iter().filter(|line| line.starts_with("name=")).collect();
            let mut keep = false;
            let expected: Vec<&String> = expected
                .iter()
                .filter(|line| {
                    if line.starts_with("name=") {
                        keep = headers.contains(line);
                    }
                    keep
                })
                .collect();
            let out: Vec<&String> = out.iter().collect();
            assert_eq!(out, expected, "{}", test);
        }
    }
}
