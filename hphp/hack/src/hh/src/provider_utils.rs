// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/provider_utils.ml`.
//!
//! Owned by **P0** (plan §7.3).
//!
//! Of the backends the OCaml matches on, two are ported: `Shared_memory`,
//! the backend of `hh_server` and `hh_single_type_check` in this version
//! (see `crate::provider_context::local_changes`), and `Local_memory`, the
//! IDE daemon's (`crate::provider_backend`, L0), with the functions on it
//! (`invalidate_shallow_decls` ... `invalidate_upon_file_changes`, added by
//! L0).

use std::cell::Cell;
use std::sync::Arc;

use crate::diagnostics_state;
use crate::provider_context;
#[cfg(feature = "server")]
use crate::server_env;

/// After the caches of a `Local_memory` backend lost declarations: what
/// this thread derived from them (the class cache of `crate::decl_provider`,
/// which stands for the `Class_decl` entries of `Decl_cache`, and the memos
/// of the port) is forgotten too. (Not in the OCaml, whose IDE daemon has
/// no such caches beyond the backend's.)
fn forget_derived_from_decls() {
    crate::rt::decl_epoch::invalidate_local_caches();
}

/// `invalidate_shallow_decls symbols local_memory`
pub fn invalidate_shallow_decls(symbols: &crate::file_info::Names, local_memory: &crate::provider_backend::LocalMemory) {
    use crate::provider_backend::decl_cache_entry::Key;
    let crate::file_info::Names {
        classes: n_classes,
        types: n_types,
        funs: n_funs,
        consts: n_consts,
        modules: n_modules,
    } = symbols;
    {
        let mut decl_cache = local_memory.decl_cache.lock().unwrap();
        for name in n_funs {
            decl_cache.remove(&Key::FunDecl(pos::FunName::new(name)));
        }
        for name in n_consts {
            decl_cache.remove(&Key::GconstDecl(pos::ConstName::new(name)));
        }
        for name in n_types {
            decl_cache.remove(&Key::TypedefDecl(pos::TypeName::new(name)));
        }
        for name in n_modules {
            decl_cache.remove(&Key::ModuleDecl(pos::ModuleName::new(name)));
        }
    }
    let mut shallow_decl_cache = local_memory.shallow_decl_cache.lock().unwrap();
    for name in n_classes {
        shallow_decl_cache.remove(&pos::TypeName::new(name));
    }
    drop(shallow_decl_cache);
    forget_derived_from_decls();
}

/// `remove_folded_decl local_memory name`
pub fn remove_folded_decl(local_memory: &crate::provider_backend::LocalMemory, name: &str) {
    // (`Decl_cache.remove ~key:(Class_decl name)`: see
    // [`forget_derived_from_decls`].)
    local_memory
        .folded_class_cache
        .lock()
        .unwrap()
        .remove(&pos::TypeName::new(name));
    forget_derived_from_decls();
}

/// This is a leftover function, because we haven't yet migrated to
/// sticky decls and more correct invalidation.
pub fn invalidate_shallow_and_some_folded_decls(
    local_memory: &crate::provider_backend::LocalMemory,
    ids: &crate::file_info::Ids,
) {
    invalidate_shallow_decls(&crate::file_info::ids_to_names(ids), local_memory);
    for crate::file_info::Id { name, .. } in &ids.classes {
        remove_folded_decl(local_memory, name)
    }
}

/// This is a leftover function, because we haven't yet migrated to
/// sticky decls and more correct invalidation.
pub fn invalidate_named_shallow_and_some_folded_decls_for_entry(
    local_memory: &crate::provider_backend::LocalMemory,
    entries: &provider_context::Entries,
) {
    for (_path, entry) in entries.iter() {
        let parser_return = entry.parser_return.lock().unwrap().clone();
        match parser_return {
            None => {} // hasn't been parsed, hence nothing to invalidate
            Some(parser_return) => {
                let ids = crate::nast::get_def_names(&parser_return.ast);
                invalidate_shallow_and_some_folded_decls(local_memory, &ids)
            }
        }
    }
}

/// `combine_old_and_new_symbols changes`
pub fn combine_old_and_new_symbols(changes: &[crate::file_info::Change]) -> crate::file_info::Names {
    // Helper for merging [File_info.ids] list-of-ids into [File_info.names] set-of-names
    let merge_ids = |mut acc: crate::file_info::Names, change: &crate::file_info::Ids| {
        let f = |set: &mut std::collections::BTreeSet<String>, ids: &[crate::file_info::Id]| {
            for id in ids {
                set.insert(id.name.clone());
            }
        };
        f(&mut acc.funs, &change.funs);
        f(&mut acc.classes, &change.classes);
        f(&mut acc.types, &change.typedefs);
        f(&mut acc.consts, &change.consts);
        f(&mut acc.modules, &change.modules);
        acc
    };
    changes.iter().fold(crate::file_info::empty_names(), |acc, change| {
        let acc = match &change.old_ids {
            Some(old_ids) => merge_ids(acc, old_ids),
            None => acc,
        };
        match &change.new_ids {
            Some(new_ids) => merge_ids(acc, new_ids),
            None => acc,
        }
    })
}

/// `resolve_deps dep_table deps`
pub fn resolve_deps(
    dep_table: &hash::HashMap<crate::typing_deps::dep::T, String>,
    deps: &crate::typing_deps::dep_set::T,
) -> crate::s_set::T {
    deps.iter().fold(crate::s_set::T::new(), |mut set, dep| {
        if let Some(name) = dep_table.get(dep) {
            set.insert(name.clone());
        }
        set
    })
}

/// Optimised folded decl invalidation using the dependency graph.
/// This will flush the dependency edges before querying the graph.
pub fn invalidate_folded_decls_flush_deps(
    ctx: &provider_context::T,
    names: &crate::file_info::Names,
    local_memory: &crate::provider_backend::LocalMemory,
) {
    use crate::typing_deps;
    let deps_mode = provider_context::get_deps_mode(ctx);
    typing_deps::flush_deps(&deps_mode);
    let classes_depset: typing_deps::dep_set::T = names
        .classes
        .iter()
        .map(|class_name| typing_deps::dep::make(&typing_deps::dep::Variant::Type(class_name.clone())))
        .collect();
    let to_invalidate_depset = typing_deps::add_extend_deps(&deps_mode, &classes_depset);
    let to_invalidate_class_names = resolve_deps(&local_memory.dep_table.lock().unwrap(), &to_invalidate_depset);
    for name in &to_invalidate_class_names {
        remove_folded_decl(local_memory, name)
    }
}

/// `invalidate_upon_file_changes ~ctx ~local_memory ~changes ~entries`
pub fn invalidate_upon_file_changes(
    ctx: &provider_context::T,
    local_memory: &crate::provider_backend::LocalMemory,
    changes: &[crate::file_info::Change],
    entries: &provider_context::Entries,
) -> crate::telemetry::T {
    let start_time = crate::rt::ocaml_unix::gettimeofday();
    let decls_reflect_this_file = local_memory.decls_reflect_this_file.lock().unwrap().clone();
    let (kind, telemetry_opt, tasts_to_invalidate): (&str, Option<crate::telemetry::T>, provider_context::Entries) =
        match (changes, &decls_reflect_this_file) {
            ([], _) => ("no_changes", None, provider_context::Entries::new()),
            (
                [
                    crate::file_info::Change {
                        path,
                        new_pfh_hash: Some(pfh_hash),
                        ..
                    },
                ],
                Some((path2, _, pfh_hash2)),
            ) if crate::relative_path::equal(path, path2) && pfh_hash == pfh_hash2 => {
                let tasts_to_invalidate = entries
                    .iter()
                    .filter(|(path2, _entry)| !crate::relative_path::equal(path, path2))
                    .map(|(p, e)| (p.clone(), Arc::clone(e)))
                    .collect();
                ("no_signature_changes", None, tasts_to_invalidate)
            }
            _ => {
                let symbols = combine_old_and_new_symbols(changes);
                invalidate_shallow_decls(&symbols, local_memory);
                invalidate_folded_decls_flush_deps(ctx, &symbols, local_memory);
                ("exhaustive", None, entries.clone())
            }
        };
    // In addition to decls, we also have derived facts in the form of TASTs.
    // We'll invalidate them all since we don't know which are affected.
    // Only exception, calculated above, is that if [decls_reflect_this_file]
    // matches one of the entries, then its TAST is already correct and
    // needn't be invalidated. (This is the common case where you save
    // a file that you'd previously been editing).
    for (_path, entry) in tasts_to_invalidate.iter() {
        provider_context::set_entry_tast(entry, None);
        *entry.all_diagnostics.lock().unwrap() = None;
    }
    let telemetry = telemetry_opt.unwrap_or_else(crate::telemetry::create);
    let telemetry = crate::telemetry::duration(Some("invalidate_upon_file_changes_ms"), start_time, None, telemetry);
    crate::telemetry::string_(None, "kind", kind, telemetry)
}

/// `ctx_from_server_env env`: `Provider_context.empty_for_tool` with the
/// options, backend and dependency mode of the server: the context of the
/// server without entries.
#[cfg(feature = "server")]
pub fn ctx_from_server_env(env: &server_env::Env) -> provider_context::T {
    // TODO: backend should be stored in [env].
    let ctx = &env.ctx;
    // (The context of the server has no entries and the dependency mode of
    // the server: it is the one meant, and keeps its identity, which the
    // caches of the threads are keyed by.)
    if ctx.entries.is_empty() && ctx.deps_mode == env.deps_mode {
        std::sync::Arc::clone(ctx)
    } else {
        std::sync::Arc::new(crate::ctx::Ctx {
            entries: Default::default(),
            deps_mode: env.deps_mode.clone(),
            ..crate::ctx::Ctx::clone(ctx)
        })
    }
}

/// `respect_but_quarantine_unsaved_changes ~ctx ~f`: runs `f` with the
/// unsaved contents of the entries of `ctx` in force, and nothing of them
/// left afterwards.
///
/// "Quarantine" (the module comment of `provider_utils.mli`): the
/// declarations that the decl providers compute from the entries of `ctx`
/// while `f` runs (and the ASTs, file contents and fixmes cached
/// meanwhile) are local changes, which are dropped when `f` returns or
/// raises. A quarantine cannot be entered twice on a thread
/// (`Provider_context.set_is_quarantined_internal` raises).
///
/// The decl stores with local changes are those of `ctx` (a context with
/// entries has its own, see `crate::provider_context::local_changes`); `f`
/// must use `ctx` (or a context derived from it with `map_tcopt` and the
/// like), as every OCaml caller does: a context made inside `f` by adding
/// another entry has local changes of its own, outside this quarantine.
pub fn respect_but_quarantine_unsaved_changes<A>(
    ctx: &provider_context::T,
    f: impl FnOnce() -> A,
) -> A {
    let backend_pushed = Cell::new(false);
    let quarantine_set = Cell::new(false);
    let local_changes = provider_context::local_changes::of_ctx(ctx);
    // Explanation for the invariants+operation of this function are in the module-level
    // comments in Provider_utils.mli.
    let enter_quarantine_exn = || {
        if let Some(local) = ctx.local_memory() {
            // `Provider_backend.Local_memory local`
            let entries = &ctx.entries;
            if entries.len() != 1 {
                crate::hack_event_logger::invariant_violation_bug(
                    None,
                    None,
                    None,
                    Some(entries.len() as isize),
                    None,
                    "Should only enter quarantine with exactly one entry",
                );
            }
            for (_path, entry) in entries.iter() {
                let _: crate::nast::Program = crate::ast_provider::compute_ast(provider_context::get_popt(ctx), entry);
            }
            // (`Hack_event_logger.ProfileTypeCheck.quarantine` with the
            // telemetry of the invalidation: a no-op in OSS.)
            if local.decls_reflect_this_file.lock().unwrap().is_none() {
                invalidate_named_shallow_and_some_folded_decls_for_entry(local, entries);
            }
            backend_pushed.set(true);
            crate::ide_parser_cache::activate();
            diagnostics_state::set_allow_errors_in_default_path(true);
            provider_context::set_is_quarantined_internal();
            quarantine_set.set(true);
            return;
        }
        // `Provider_backend.Shared_memory`
        crate::ast_provider::local_changes_push_sharedmem_stack();
        // `Decl_provider.local_changes_push_sharedmem_stack`
        // (`Shallow_classes_heap.Classes.LocalChanges.push_stack` and
        // `Decl_store.((get ()).push_local_changes ())`): the decl stores of
        // the context.
        if let Some(local_changes) = &local_changes {
            local_changes.push();
        }
        (crate::decl_store::get().push_local_changes)();
        crate::file_provider::local_changes_push_sharedmem_stack();
        diagnostics_state::fixme_provider::local_changes_push_sharedmem_stack();
        crate::naming_provider::local_changes_push_sharedmem_stack();
        // `Shared_mem.set_allow_hashtable_writes_by_current_process false`:
        // the stores of a context with entries take every write in their
        // local changes; those of a context without are not written but by
        // the caches of folded classes, which are what the stores give.
        crate::rt::decl_epoch::invalidate_local_caches();
        backend_pushed.set(true);
        crate::ide_parser_cache::activate();
        diagnostics_state::set_allow_errors_in_default_path(true);
        provider_context::set_is_quarantined_internal();
        quarantine_set.set(true);
    };
    let leave_quarantine_exn = || {
        if quarantine_set.get() {
            provider_context::unset_is_quarantined_internal();
        }
        diagnostics_state::set_allow_errors_in_default_path(false);
        crate::ide_parser_cache::deactivate();
        if let (true, Some(local)) = (backend_pushed.get(), ctx.local_memory()) {
            // `Provider_backend.Local_memory local`
            if local.decls_reflect_this_file.lock().unwrap().is_none() {
                invalidate_named_shallow_and_some_folded_decls_for_entry(local, &ctx.entries);
            }
        } else if backend_pushed.get() {
            crate::ast_provider::local_changes_pop_sharedmem_stack();
            if let Some(local_changes) = &local_changes {
                local_changes.pop();
            }
            (crate::decl_store::get().pop_local_changes)();
            crate::file_provider::local_changes_pop_sharedmem_stack();
            diagnostics_state::fixme_provider::local_changes_pop_sharedmem_stack();
            crate::naming_provider::local_changes_pop_sharedmem_stack();
            // `Shared_mem.set_allow_hashtable_writes_by_current_process true`
            // `Shared_mem.invalidate_local_caches ()`
            crate::rt::decl_epoch::invalidate_local_caches();
        }
    };
    let (_errors, result) = diagnostics_state::do_(None, || {
        crate::utils::try_finally(
            || {
                enter_quarantine_exn();
                f()
            },
            leave_quarantine_exn,
        )
    });
    result
}
