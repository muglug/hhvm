// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_lazy_init.ml`: `full_init`, `parse_only_init`,
//! `initialize_naming_table`, and the saved-state init:
//! `saved_state_init`, `use_precomputed_state_exn` (`--with-mini-state`),
//! the open-source `Load_state_natively` (the loader of
//! `State_loader_futures` is a stub that fails: "Not implemented"),
//! `post_saved_state_initialization`, `update_naming_table`,
//! `compute_fanout`, `calculate_fanout_and_defer_or_do_type_check`.
//!
//! The saved-state load leaves `env.ctx` the `Shared_memory`-like context of
//! the daemon over the state's naming database: its reverse naming table is
//! built empty (`Ctx::build_reverse_naming_table` with nothing declared) and falls
//! back to the SQLite database (`Naming_table.load_from_sqlite` sets the
//! path), decls are parsed on demand (lazy decl), and the dependency graph
//! is the state's (`InMemoryMode (Some deptable)`, loaded on first use).
//! With `--write-symbol-info` (`do_indexing`), the files named, the Glean
//! indexer runs (`write_symbol_info`).
//!
//! Lazy init: during lazy initialization, hh_server tries to do as little
//! work as possible. The init_from_saved_state behavior is this:
//!
//!   Load from saved state -> Parse dirty files -> Naming -> Dirty Typecheck
//!
//! The full_init behavior is this: (similar to eager init, but with lazy decl)
//!
//!   Full Parsing -> Naming -> Full Typecheck (with lazy decl)

use crate::cgroup_profiler;
use crate::direct_decl_service::DirectDeclMode;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::naming_table;
use crate::path;
use crate::relative_path;
use crate::rt::ocaml_unix::gettimeofday;
use crate::server_env;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_env::init_telemetry;
use crate::server_init_common;
use crate::server_init_types::LoadStateApproach;
use crate::server_init_types::LoadStateError;
use crate::server_progress;
use crate::telemetry;

/// `initialize_naming_table progress_message ?fnl ?do_naming ~cache_decls
/// genv env`
pub fn initialize_naming_table(
    progress_message: &str,
    fnl: Option<Vec<relative_path::T>>,
    do_naming: bool,
    cache_decls: bool,
    genv: &Genv,
    env: Env,
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> (Env, f64) {
    server_progress::with_message(None, None, progress_message, || {
        let (get_next, count, t): (server_init_common::GetNext, Option<usize>, f64) = match fnl {
            Some(fnl) => {
                let count = fnl.len();
                (Box::new(move || fnl), Some(count), gettimeofday())
            }
            None => {
                let (get_next, t) =
                    server_init_common::directory_walk(None, "lazy.nt.indexing", genv, &env);
                (get_next, None, t)
            }
        };
        // full init - too many files to trace all of them
        let trace = false;
        let (env, t) = server_init_common::parse_files_and_update_forward_naming_table(
            genv,
            env,
            get_next,
            count,
            t,
            trace,
            if cache_decls {
                DirectDeclMode::Cached
            } else {
                DirectDeclMode::Normal
            },
            "lazy.nt.parsing",
            cgroup_steps,
        );
        if do_naming {
            server_init_common::update_reverse_naming_table_from_env_and_get_duplicate_name_errors(
                env,
                t,
                "lazy.nt.do_naming.naming",
                cgroup_steps,
            )
        } else {
            (env, t)
        }
    })
}

/// `write_symbol_info genv env cgroup_steps t`: names the files, then runs
/// the Glean indexer (`Write_symbol_info.Entrypoint.go`) on the files to
/// index, or only writes their list to `symbol_write_index_paths_file_output`.
/// The OCaml's exceptions (`Failure`) reach the handler of `Monitor_start`,
/// which exits with `Uncaught_exception`.
pub fn write_symbol_info(genv: &Genv, env: Env, cgroup_steps: &cgroup_profiler::StepGroup, t: f64) -> (Env, f64) {
    use crate::write_symbol_info::entrypoint;
    use crate::write_symbol_info::indexable;
    use crate::write_symbol_info::indexer_options;
    let uncaught = |e: crate::write_symbol_info::predicate::Failure| -> ! {
        exit::exit(
            None,
            None,
            None,
            None,
            exit_status::T::UncaughtException(crate::exception::wrap(e.exn_to_string())),
        )
    };
    let (env, t) = server_init_common::update_reverse_naming_table_from_env_and_get_duplicate_name_errors(
        env,
        t,
        "write_symbol_info.naming",
        cgroup_steps,
    );
    // (`env.swriteopt`)
    let swriteopt = crate::server_config::symbol_write_options(&genv.config);
    let paths = &swriteopt.symbol_write_index_paths;
    let paths_file = swriteopt.symbol_write_index_paths_file.as_deref();
    let include_hhi = swriteopt.symbol_write_include_hhi;
    let ignore_paths = &swriteopt.symbol_write_ignore_paths;
    // files to index, they could be either provided or deduced
    // from the naming table, depending on the combination of options
    let files = if !paths.is_empty() || paths_file.is_some() {
        indexable::from_options(paths, paths_file, include_hhi).unwrap_or_else(|e| uncaught(e))
    } else {
        indexable::from_naming_table(&env.naming_table, include_hhi, ignore_paths)
    };
    match &swriteopt.symbol_write_index_paths_file_output {
        Some(output) => {
            // Don't run indexer, just returns list of all files to index
            let lines: String = files
                .iter()
                .map(|indexable::T { path, .. }| format!("{}\n", relative_path::storage_to_string(path)))
                .collect();
            if let Err(e) = std::fs::write(output, lines) {
                uncaught(crate::write_symbol_info::predicate::Failure(format!("{}: {}", output, e)))
            }
            (env, t)
        }
        None => {
            let out_dir = match crate::server_args::write_symbol_info(&genv.options) {
                None => uncaught(crate::write_symbol_info::predicate::Failure(
                    "No write directory specified for --write-symbol-info".to_string(),
                )),
                Some(s) => s,
            };
            let opts = indexer_options::create(&swriteopt, &out_dir).unwrap_or_else(|e| uncaught(e));
            let namespace_map = env.ctx.tco.po.auto_namespace_map.clone();
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            if let Err(e) = entrypoint::go(Some(genv.num_workers as usize), &ctx, &opts, &namespace_map, files) {
                uncaught(e)
            }
            (env, t)
        }
    }
}

/// `write_symbol_info_full_init genv env cgroup_steps`
pub fn write_symbol_info_full_init(genv: &Genv, env: Env, cgroup_steps: &cgroup_profiler::StepGroup) -> (Env, f64) {
    let (env, t) =
        initialize_naming_table("write symbol info initialization", None, false, true, genv, env, cgroup_steps);
    write_symbol_info(genv, env, cgroup_steps, t)
}

/// If we fail to load a saved state, fall back to typechecking everything
/// (`full_init genv env cgroup_steps`).
pub fn full_init(genv: &Genv, env: Env, cgroup_steps: &cgroup_profiler::StepGroup) -> (Env, f64) {
    let init_telemetry = init_telemetry::T {
        reason: init_telemetry::Reason::InitLazyFull,
        telemetry: telemetry::float_("start_time", gettimeofday(), telemetry::create()),
    };
    let existing_name_count = naming_table::fold(None, &env.naming_table, 0isize, |_, _, i| i + 1);
    if existing_name_count > 0 {
        let desc = "full_init_naming_not_empty";
        hh_logger::log(&format!(
            "INVARIANT_VIOLATION_BUG [{}] count={}",
            desc, existing_name_count
        ));
        // (`Hack_event_logger.invariant_violation_bug`: a no-op.)
    }
    hh_logger::log("full init");
    let (env, t) = initialize_naming_table("full initialization", None, true, true, genv, env, cgroup_steps);
    server_init_common::validate_no_errors(&env.diagnostics);
    let fnl = naming_table::get_files(&env.naming_table);
    server_init_common::defer_or_do_type_check(
        genv,
        env,
        fnl,
        init_telemetry,
        t,
        "lazy.full.type_check",
        cgroup_steps,
    )
}

/// `parse_only_init genv env cgroup_steps`
pub fn parse_only_init(genv: &Genv, env: Env, cgroup_steps: &cgroup_profiler::StepGroup) -> (Env, f64) {
    initialize_naming_table("parse-only initialization", None, false, false, genv, env, cgroup_steps)
}

/// `download_and_load_state_exn ~genv ~ctx ~root`, as the open-source build
/// runs it: `State_loader_futures.load` is
/// `Future.of_value (Error "Not implemented")`, so the result is
/// `Load_state_saved_state_loader_failure "Not implemented"` at once.
fn download_and_load_state_exn(genv: &Genv, root: &path::T) -> LoadStateError {
    let _ = (genv, root);
    hh_logger::log("Downloading dependency graph from DevX infra");
    // `run_saved_state_future`: `Future.get` of the (ready) future gives
    // `Ok (Error error)`.
    LoadStateError::LoadStateSavedStateLoaderFailure("Not implemented".to_string())
}

// ~~ The saved-state init ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

use std::sync::Arc;

use crate::decl_compare::versioned_names;
use crate::decl_redecl_service;
use crate::exception;
use crate::file_info;
use crate::find_utils;
use crate::hg;
use crate::naming_provider;
use crate::naming_sqlite;
use crate::provider_utils;
use crate::save_state_service;
use crate::server_args;
use crate::server_check_utils;
use crate::server_init_types::LoadedInfo;
use crate::server_notifier;
use crate::server_prechecked_files;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;

type RPSet = crate::relative_path::set::T;
type RPMap<A> = crate::relative_path::map::T<A>;

/// An OCaml exception, printed (`Printexc.to_string`).
struct Printed(String);

impl std::fmt::Debug for Printed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// `failwith s`, as an exception of the loader.
fn failure(s: String) -> exception::T {
    exception::wrap(crate::remote_old_decl_client::Failure(s))
}

/// `deptable` (`CustomDeptable of string`)
enum Deptable {
    CustomDeptable(String),
}

/// `deptable_with_filename fn`
fn deptable_with_filename(fn_: &str) -> Deptable {
    Deptable::CustomDeptable(fn_.to_string())
}

/// `lock_and_load_deptable ~base_file_name ~deptable ~ignore_hh_version`
fn lock_and_load_deptable(
    base_file_name: &str,
    deptable: &Deptable,
    ignore_hh_version: bool,
) -> Result<(), exception::T> {
    match deptable {
        Deptable::CustomDeptable(fn_) => {
            // (`Saved_state_loader.ignore_saved_state_version_mismatch
            // ~ignore_hh_version` is `ignore_hh_version` in the open-source
            // build.)
            if !ignore_hh_version {
                let build_revision = save_state_service::saved_state_build_revision_read(base_file_name)
                    .map_err(|e| exception::wrap(Printed(e)))?;
                if build_revision != crate::build_id::build_revision() {
                    return Err(failure(format!(
                        "Saved-state build mismatch, this saved-state was built  for version '{}', but we expected '{}'",
                        build_revision,
                        crate::build_id::build_revision()
                    )));
                }
            }
            // The new dependency graph is threaded through function calls
            // instead of stored in a global
            hh_logger::log(&format!(
                "Custom dependency graph will be loaded lazily from {}",
                fn_
            ));
            Ok(())
        }
    }
}

/// `mergebase_info root_path saved_state_rev`
fn mergebase_info(
    root_path: &path::T,
    saved_state_rev: &str,
) -> Result<server_env::SavedStateRevsInfo, exception::T> {
    let root_path = path::to_string(root_path);
    let future = (|| -> Result<hg::Future<server_env::SavedStateRevsInfo>, hg::ExecError> {
        let mergebase_rev = match hg::current_mergebase_hg_rev(&root_path)? {
            Ok(r) => r,
            Err(e) => return Ok(Err(e)),
        };
        let mergebase_globalrev = match hg::get_closest_global_ancestor(&mergebase_rev, &root_path)? {
            Ok(r) => r,
            Err(e) => return Ok(Err(e)),
        };
        Ok(Ok(server_env::SavedStateRevsInfo {
            age: None,
            distance: None,
            saved_state_rev: saved_state_rev.to_string(),
            saved_state_globalrev: None,
            saved_state_rev_timestamp: None,
            mergebase_rev: Some(mergebase_rev),
            mergebase_globalrev: Some(mergebase_globalrev),
            mergebase_rev_timestamp: None,
        }))
    })()
    .map_err(exception::wrap)?;
    match future {
        Ok(x) => Ok(x),
        Err(e) => {
            hh_logger::log(&format!(
                "[serverLazyInit]: mergebase_info failed: {}",
                hg::error_to_string(&e)
            ));
            Ok(server_env::saved_state_revs_info::default(saved_state_rev.to_string()))
        }
    }
}

/// `use_precomputed_state_exn ~root genv ctx info cgroup_steps`
fn use_precomputed_state_exn(
    root: &path::T,
    genv: &Genv,
    ctx: &crate::provider_context::T,
    info: &server_args::SavedStateTargetInfo,
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> Result<LoadedInfo, exception::T> {
    let server_args::SavedStateTargetInfo {
        naming_table_path,
        corresponding_base_revision,
        deptable_fn,
        compressed_deptable_fn: _,
        changes,
        naming_changes,
        prechecked_changes,
    } = info;
    let ignore_hh_version = server_args::ignore_hh_version(&genv.options);
    cgroup_profiler::step_start_end(cgroup_steps, None, "load deptable", || {
    let deptable_fn = {
        let deptable = deptable_with_filename(deptable_fn);
        lock_and_load_deptable(naming_table_path, &deptable, ignore_hh_version)?;
        deptable_fn.clone()
    };
    let changes: RPSet = changes.iter().cloned().collect();
    let naming_changes: RPSet = naming_changes.iter().cloned().collect();
    let prechecked_changes: RPSet = prechecked_changes.iter().cloned().collect();
    let naming_sqlite_table_path = server_args::naming_sqlite_path_for_target_info(info);
    let naming_table_fallback_path = if std::path::Path::new(&naming_sqlite_table_path).exists() {
        hh_logger::log("Using sqlite naming table from saved state");
        Some(naming_sqlite_table_path)
    } else {
        server_check_utils::get_naming_table_fallback_path(genv)
    };
    let errors_path = server_args::errors_path_for_target_info(info);
    let warning_hashes_path = server_args::warnings_path_for_target_info(info);
    let (old_naming_table, crate::save_state_service_types::OldIssues {
        old_errors,
        old_warnings,
    }) = cgroup_profiler::step_start_end(cgroup_steps, None, "load saved state", || {
        // The reverse naming table of the daemon (the OCaml's naming heap,
        // which always exists): empty, then falling back to the database
        // that `load_from_sqlite` sets.
        if !ctx.has_reverse_naming_table() {
            ctx.build_reverse_naming_table();
        }
        save_state_service::load_saved_state_exn(
            naming_table_fallback_path.as_deref(),
            &errors_path,
            &warning_hashes_path,
            ctx,
        )
        .map_err(|e| exception::wrap(Printed(e.to_string())))
    })?;
    let saved_state_revs_info = mergebase_info(root, corresponding_base_revision)?;
    Ok(LoadedInfo {
        naming_table_fn: naming_table_path.clone(),
        naming_table_fallback_fn: naming_table_fallback_path,
        deptable_fn,
        changed_files_since_saved_state_rev: naming_changes,
        dirty_master_files: prechecked_changes,
        dirty_local_files: changes,
        old_naming_table,
        old_errors,
        old_warnings,
        saved_state_revs_info,
        naming_table_manifold_path: None,
    })
    })
}

/// This function ensures the naming-table is ready for us to do
/// [update_reverse_naming_table_from_env_and_get_duplicate_name_errors] on
/// the [env.naming_table] forward-naming-table files.
/// - In the case of saved-state-init, [env.naming_table] has dirty files so we'll
///   remove them from the global naming table
/// - In the case of full init, I don't believe this is ever called...!
/// (`remove_items_from_reverse_naming_table_or_build_new_reverse_naming_table
/// ctx old_naming_table parsing_files naming_table_fallback_fn t`)
fn remove_items_from_reverse_naming_table_or_build_new_reverse_naming_table(
    ctx: &crate::provider_context::T,
    old_naming_table: &naming_table::T,
    parsing_files: &RPSet,
    naming_table_fallback_fn: Option<&str>,
    t: f64,
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> f64 {
    cgroup_profiler::step_start_end(cgroup_steps, None, "naming from saved state", || {
    match naming_table_fallback_fn {
        Some(_) => {
            // Set the SQLite fallback path for the reverse naming table, then block out all entries in
            // any dirty files to make sure we properly handle file deletes.
            for k in parsing_files {
                match naming_table::get_file_info(old_naming_table, k) {
                    None => {
                        // If we can't find the file in [old_naming_table] we don't consider that an error, since
                        // it could be a new file that was added.
                    }
                    Some(file_info::T { ids, .. }) => {
                        let backend = &**ctx;
                        let snd = |ids: &[file_info::Id]| -> Vec<String> {
                            ids.iter().map(|id| id.name.clone()).collect()
                        };
                        naming_provider::remove_type_batch(backend, &snd(&ids.classes));
                        naming_provider::remove_type_batch(backend, &snd(&ids.typedefs));
                        naming_provider::remove_fun_batch(backend, &snd(&ids.funs));
                        naming_provider::remove_const_batch(backend, &snd(&ids.consts));
                        naming_provider::remove_module_batch(backend, &snd(&ids.modules));
                    }
                }
            }
        }
        None => {
            // (`Hack_event_logger.invariant_violation_bug "unexpected
            // saved-state build-new-reverse-naming-table"`: a no-op.)
            // Name all the files from the old naming-table (except the new ones we parsed since
            // they'll be named by our caller, next). We assume the old naming-table came from a clean
            // state, which is why we skip checking for "already bound" conditions.
            let old_hack_names = naming_table::filter(old_naming_table, |k, _v| !parsing_files.contains(k));
            naming_table::fold(None, &old_hack_names, (), |k, info, ()| {
                crate::naming_global::ndecl_file_skip_if_already_bound(ctx, k, &info.ids)
            });
        }
    }
    // (`Hack_event_logger.naming_from_saved_state_end`: a no-op.)
    hh_logger::log_duration(None, None, "NAMING_FROM_SAVED_STATE_END", t)
    })
}

/// Prechecked files are gated with a flag and not supported in AI/check
/// modes. (`use_prechecked_files genv`)
fn use_prechecked_files(genv: &Genv) -> bool {
    server_prechecked_files::should_use(&genv.options, &genv.local_config)
        && !server_args::check_mode(&genv.options)
}

/// `file_names_to_deps names deps`
fn file_names_to_deps(names: &file_info::Names, deps: dep_set::T) -> dep_set::T {
    let file_info::Names {
        funs,
        classes,
        types,
        consts,
        modules,
    } = names;
    let add_deps_of_sset = |dep_ctor: &dyn Fn(String) -> dep::Variant,
                            sset: &std::collections::BTreeSet<String>,
                            depset: dep_set::T|
     -> dep_set::T {
        sset.iter()
            .fold(depset, |acc, n| dep_set::add(&acc, dep::make(&dep_ctor(n.clone()))))
    };
    let deps = add_deps_of_sset(&dep::Variant::Fun, funs, deps);
    let deps = add_deps_of_sset(&dep::Variant::Type, classes, deps);
    let deps = add_deps_of_sset(&dep::Variant::Type, types, deps);
    let deps = add_deps_of_sset(&dep::Variant::GConst, consts, deps);
    let deps = add_deps_of_sset(&dep::Variant::GConstName, consts, deps);
    add_deps_of_sset(&dep::Variant::Module, modules, deps)
}

/// `names_to_deps names`
fn names_to_deps(names: &versioned_names::T) -> dep_set::T {
    let versioned_names::T {
        old_names,
        new_names,
    } = names;
    file_names_to_deps(
        new_names,
        file_names_to_deps(&file_info::old_names::to_names(old_names), dep_set::make()),
    )
}

/// `log_fanout_information to_recheck_deps files_to_recheck`
fn log_fanout_information(to_recheck_deps: &dep_set::T, files_to_recheck: &RPSet) {
    // we use lazy here to avoid expensive string generation when logging
    // is not enabled
    let max = 1000;
    hh_logger::level::log_lazy(hh_logger::level::T::Info, Some("fanout_tests"), None, || {
        use crate::yojson::safe as yojson;
        yojson::to_string(&yojson::T::Assoc(vec![
            ("tag".to_string(), yojson::T::String("saved_state_init_fanout".to_string())),
            (
                "hashes".to_string(),
                yojson::T::List(
                    dep_set::elements(to_recheck_deps)
                        .into_iter()
                        .take(max)
                        .map(|d| yojson::T::String(dep::to_hex_string(d)))
                        .collect(),
                ),
            ),
            (
                "hashes_was_truncated".to_string(),
                yojson::T::Bool(dep_set::cardinal(to_recheck_deps) > max as isize),
            ),
            (
                "files".to_string(),
                yojson::T::List(
                    files_to_recheck
                        .iter()
                        .take(max)
                        .map(|p| yojson::T::String(relative_path::suffix(p)))
                        .collect(),
                ),
            ),
            (
                "files_was_truncated".to_string(),
                yojson::T::Bool(files_to_recheck.len() > max),
            ),
        ]))
    });
}

/// Compute fanout for saved state init (`get_files_to_recheck genv env
/// old_naming_table new_naming_table defs_per_dirty_file files_to_redeclare`)
fn get_files_to_recheck(
    genv: &Genv,
    env: &Env,
    old_naming_table: &naming_table::T,
    new_naming_table: &naming_table::T,
    defs_per_dirty_file: &RPMap<versioned_names::T>,
    files_to_redeclare: &RPSet,
) -> RPSet {
    let bucket_size = genv.local_config.type_decl_bucket_size;
    let defs_per_file_to_redeclare: RPMap<versioned_names::T> = files_to_redeclare
        .iter()
        .filter_map(|path| defs_per_dirty_file.get(path).map(|info| (path.clone(), info.clone())))
        .collect();
    let get_old_and_new_classes = |path: &relative_path::T| -> crate::s_set::T {
        let old_names = naming_table::get_file_info(old_naming_table, path).map(|i| file_info::simplify(&i));
        let new_names = naming_table::get_file_info(new_naming_table, path).map(|i| file_info::simplify(&i));
        let old_classes = old_names.map(|x| x.classes);
        let new_classes = new_names.map(|x| x.classes);
        let merged: Option<std::collections::BTreeSet<String>> = match (old_classes, new_classes) {
            (Some(a), Some(b)) => Some(a.union(&b).cloned().collect()),
            (a, b) => a.or(b),
        };
        merged.unwrap_or_default().into_iter().collect()
    };
    let old_dirty_names = defs_per_dirty_file
        .values()
        .fold(file_info::empty_names(), |acc, v| {
            file_info::merge_names(&file_info::old_names::to_names(&v.old_names), &acc)
        });
    let ctx = provider_utils::ctx_from_server_env(env);
    decl_redecl_service::oldify_decls_and_remove_descendants(
        &ctx,
        None,
        &get_old_and_new_classes,
        bucket_size,
        &old_dirty_names,
    );
    let decl_redecl_service::RedoTypeDeclResult { fanout, .. } = decl_redecl_service::redo_type_decl(
        &ctx,
        true,
        None,
        bucket_size,
        &get_old_and_new_classes,
        &old_dirty_names,
        &defs_per_file_to_redeclare,
    );
    decl_redecl_service::remove_old_defs(&ctx, bucket_size, &old_dirty_names);
    // (`Relative_path.Map.keys` then `set_of_list`: the set of the keys.)
    let reparsed: RPSet = defs_per_dirty_file.keys().cloned().collect();
    let files_to_recheck = crate::server_incremental::resolve_files(&ctx, &reparsed, env, &fanout);
    log_fanout_information(&fanout.to_recheck, &files_to_recheck);
    files_to_recheck
}

/// We start off with a list of files that have changed since the state was
/// saved ([dirty_files]), the naming table from the saved state
/// ([old_naming_table]) and a map of the current class / function
/// declarations per file ([new_defs_per_file]). We grab the declarations
/// from both, to account for both the declarations that were deleted and
/// those that are newly created. Then we use the deptable to figure out the
/// files that referred to them. Finally we recheck the lot.
/// (`calculate_fanout_and_defer_or_do_type_check genv env ~old_naming_table
/// ~old_names_per_file ~new_naming_table ~dirty_master_files_unchanged_decls
/// ~dirty_master_files_changed_decls ~dirty_local_files_unchanged_decls
/// ~dirty_local_files_changed_decls t`)
#[allow(clippy::too_many_arguments)]
fn calculate_fanout_and_defer_or_do_type_check(
    genv: &Genv,
    env: Env,
    old_naming_table: &naming_table::T,
    old_names_per_file: &RPMap<file_info::old_names::T>,
    new_naming_table: &naming_table::T,
    dirty_master_files_unchanged_decls: &RPSet,
    dirty_master_files_changed_decls: &RPSet,
    dirty_local_files_unchanged_decls: &RPSet,
    dirty_local_files_changed_decls: &RPSet,
    t: f64,
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> (Env, f64) {
    let start_t = gettimeofday();
    let dirty_files_unchanged_decls = dirty_master_files_unchanged_decls
        .clone()
        .union(dirty_local_files_unchanged_decls.clone());
    let dirty_files_changed_decls = dirty_master_files_changed_decls
        .clone()
        .union(dirty_local_files_changed_decls.clone());
    let old_and_new_defs_per_dirty_files_changed_decls = crate::server_incremental::get_old_and_new_defs_in_files(
        old_naming_table,
        old_names_per_file,
        new_naming_table,
        &dirty_files_changed_decls,
    );
    // We're looking at files with unchanged decls and therefore unchanged
    // def names, so it does not matter which version of the naming table
    // we are looking at (since there should have been no changes).
    let old_and_new_defs_per_dirty_files_unchanged_decls: RPMap<versioned_names::T> =
        server_check_utils::extend_defs_per_file(
            genv,
            RPMap::new(),
            &env.naming_table,
            &dirty_files_unchanged_decls,
        )
        .into_iter()
        .map(|(k, v)| (k, versioned_names::make_unchanged(v)))
        .collect();
    // (`Relative_path.Map.union`: the maps are disjoint.)
    let mut old_and_new_defs_per_dirty_files = old_and_new_defs_per_dirty_files_unchanged_decls;
    for (k, v) in old_and_new_defs_per_dirty_files_changed_decls.iter() {
        old_and_new_defs_per_dirty_files.insert(k.clone(), v.clone());
    }
    let old_and_new_defs_in_files = |files: &RPSet| -> versioned_names::T {
        old_and_new_defs_per_dirty_files_changed_decls
            .iter()
            .fold(versioned_names::empty(), |acc, (k, v)| {
                if files.contains(k) {
                    versioned_names::merge(v, &acc)
                } else {
                    acc
                }
            })
    };
    let ctx = provider_utils::ctx_from_server_env(&env);
    let master_deps = names_to_deps(&old_and_new_defs_in_files(dirty_master_files_changed_decls));
    let local_deps = names_to_deps(&old_and_new_defs_in_files(dirty_local_files_changed_decls));
    let get_files_to_recheck_ = |env: &Env, files_to_redeclare: &RPSet| {
        get_files_to_recheck(
            genv,
            env,
            old_naming_table,
            new_naming_table,
            &old_and_new_defs_per_dirty_files,
            files_to_redeclare,
        )
    };
    let (env, to_recheck) = if use_prechecked_files(genv) {
        // Start with dirty files and fan-out of local changes only
        hh_logger::log(&format!(
            "Using prechecked algorithm. Computing fanout from {} files with changed decls since the mergebase.",
            dirty_local_files_changed_decls.len()
        ));
        let to_recheck = if genv.local_config.fetch_remote_old_decls {
            get_files_to_recheck_(&env, dirty_local_files_changed_decls)
        } else {
            let deps = typing_deps::add_all_deps(&env.deps_mode, &local_deps);
            let files = naming_provider::get_files(&ctx, &deps);
            log_fanout_information(&deps, &files);
            files
        };
        let env = server_prechecked_files::init(env, local_deps, master_deps);
        (env, to_recheck)
    } else {
        // Start with full fan-out immediately
        hh_logger::log(&format!(
            "Prechecked algorithm is disabled. Computing the full fanout from {} changed files since the saved state revision.",
            dirty_files_changed_decls.len()
        ));
        let to_recheck = if genv.local_config.fetch_remote_old_decls {
            get_files_to_recheck_(&env, &dirty_files_changed_decls)
        } else {
            let deps = dep_set::union(&master_deps, &local_deps);
            let deps = typing_deps::add_all_deps(&env.deps_mode, &deps);
            let files = naming_provider::get_files(&ctx, &deps);
            log_fanout_information(&deps, &files);
            files
        };
        (env, to_recheck)
    };
    // We still need to typecheck files whose declarations did not change
    let to_recheck = to_recheck
        .union(dirty_files_unchanged_decls.clone())
        .union(dirty_files_changed_decls.clone());
    // HACK: dump the fanout that we calculated and exit. This is for
    // `hh_fanout`'s regression testing vs. `hh_server`. This can be deleted once
    // we no longer worry about `hh_fanout` regressing vs. `hh_server`. Deletion
    // is tracked at T65464119.
    if server_args::dump_fanout(&genv.options) {
        use crate::yojson::safe as yojson;
        let j = yojson::T::Assoc(vec![(
            "recheck_files".to_string(),
            yojson::T::List(
                to_recheck
                    .iter()
                    .map(|p| yojson::T::String(relative_path::to_absolute(p)))
                    .collect(),
            ),
        )]);
        print!("{}", crate::yojson::safe::pretty_to_string(&j));
        println!();
        use std::io::Write;
        let _ = std::io::stdout().flush();
        // `exit 0` (`Stdlib.exit`)
        std::process::exit(0)
    }
    let env = Env {
        changed_files: dirty_files_changed_decls.clone(),
        ..env
    };
    let reparsed = dirty_files_unchanged_decls.clone().union(dirty_files_changed_decls.clone());
    let to_recheck = if !genv.local_config.enable_type_check_filter_files {
        to_recheck
    } else {
        server_check_utils::user_filter_type_check_files(&to_recheck, &reparsed)
    };
    let init_telemetry = init_telemetry::T {
        reason: init_telemetry::Reason::InitLazyDirty,
        telemetry: {
            let t = telemetry::create();
            let t = telemetry::float_("start_time", start_t, t);
            let t = telemetry::int_(
                "dirty_master_files_unchanged_decls",
                dirty_master_files_unchanged_decls.len() as isize,
                t,
            );
            let t = telemetry::int_(
                "dirty_master_files_changed_decls",
                dirty_master_files_changed_decls.len() as isize,
                t,
            );
            let t = telemetry::int_(
                "dirty_local_files_unchanged_decls",
                dirty_local_files_unchanged_decls.len() as isize,
                t,
            );
            let t = telemetry::int_(
                "dirty_local_files_changed_decls",
                dirty_local_files_changed_decls.len() as isize,
                t,
            );
            let t = telemetry::int_(
                "dirty_files_unchanged_decls",
                dirty_files_unchanged_decls.len() as isize,
                t,
            );
            let t = telemetry::int_(
                "dirty_files_changed_decls",
                dirty_files_changed_decls.len() as isize,
                t,
            );
            let t = telemetry::int_("to_recheck", to_recheck.len() as isize, t);
            telemetry::object_opt(
                "saved_state_revs_info",
                env.init_env
                    .saved_state_revs_info
                    .as_ref()
                    .map(server_env::saved_state_revs_info::to_telemetry),
                t,
            )
        },
    };
    let to_recheck_count = to_recheck.len();
    let result = server_init_common::defer_or_do_type_check(
        genv,
        env,
        to_recheck.into_iter().collect(),
        init_telemetry,
        t,
        "type_check_dirty",
        cgroup_steps,
    );
    // (`Hack_event_logger.type_check_dirty`: a no-op.)
    hh_logger::log(&format!(
        "ServerInit type_check_dirty count: {}. Files to recheck count: {}",
        dirty_files_changed_decls.len(),
        to_recheck_count
    ));
    result
}

/// `get_updates_exn ~genv ~root`
fn get_updates_exn(genv: &Genv, root: &path::T) -> Result<(RPSet, Option<server_notifier::Clock>), exception::T> {
    let start_t = gettimeofday();
    hh_logger::log("Getting files changed while parsing...");
    server_notifier::wait_until_ready(&genv.notifier);
    let telemetry = telemetry::create();
    let (changes, clock, _telemetry) =
        server_notifier::get_changes_async(&genv.notifier, telemetry).map_err(exception::wrap)?;
    let files_changed_while_parsing: RPSet = match changes {
        server_notifier::Changes::Unavailable => RPSet::new(),
        server_notifier::Changes::SyncChanges(updates) | server_notifier::Changes::AsyncChanges(updates) => {
            let root = path::to_string(root);
            // `Relative_path.relativize_set Relative_path.Root`
            updates
                .iter()
                .filter(|p| p.starts_with(&root) && find_utils::file_filter(p))
                .map(|p| relative_path::create(relative_path::Prefix::Root, p))
                .collect()
        }
    };
    hh_logger::log(&format!(
        "Found {} files changed while parsing",
        files_changed_while_parsing.len()
    ));
    let _: f64 = hh_logger::log_duration(None, None, "Finished getting files changed while parsing", start_t);
    hh_logger::log(&format!("Watchclock: {}", server_env::show_clock(clock.as_ref())));
    // (`Hack_event_logger.changed_while_parsing_end`: a no-op.)
    Ok((files_changed_while_parsing, clock))
}

/// Saved errors contain filenames rather than diagnostics. Recover the owners
/// of their symbols from the baseline before reverse naming bindings are
/// removed, so both sides of a duplicate can be processed by naming.
fn get_saved_state_error_files_and_owners(
    old_naming_table: &naming_table::T,
    db_path: &naming_sqlite::DbPath,
    old_errors: &RPSet,
) -> RPSet {
    fn raise<A>(result: naming_sqlite::Result<A>) -> A {
        match result {
            Ok(a) => a,
            Err(e) => std::panic::panic_any(e),
        }
    }
    fn add_owners(
        mut files: RPSet,
        ids: &[file_info::Id],
        get_path: impl Fn(&str) -> Option<relative_path::T>,
    ) -> RPSet {
        for id in ids {
            match get_path(&id.name) {
                None => {}
                Some(path) => {
                    files.insert(path);
                }
            }
        }
        files
    }
    let get_type_path =
        |name: &str| raise(naming_sqlite::get_itype_path_by_name(db_path, name)).map(|(path, _)| path);
    let get_exact_type_path =
        |name: &str| raise(naming_sqlite::get_type_path_by_name(db_path, name)).map(|(path, _)| path);
    old_errors.iter().fold(old_errors.clone(), |files, path| {
        match naming_table::get_file_info(old_naming_table, path) {
            None => files,
            Some(file_info::T { ids, .. }) => {
                let file_info::Ids {
                    funs,
                    classes,
                    typedefs,
                    consts,
                    modules,
                } = &ids;
                let files = add_owners(files, funs, |name| {
                    raise(naming_sqlite::get_fun_path_by_name(db_path, name))
                });
                let files = add_owners(files, funs, |name| {
                    raise(naming_sqlite::get_ifun_path_by_name(db_path, name))
                });
                let files = add_owners(files, classes, get_exact_type_path);
                let files = add_owners(files, typedefs, get_exact_type_path);
                let files = add_owners(files, classes, get_type_path);
                let files = add_owners(files, typedefs, get_type_path);
                let files = add_owners(files, consts, |name| {
                    raise(naming_sqlite::get_const_path_by_name(db_path, name))
                });
                add_owners(files, modules, |name| {
                    raise(naming_sqlite::get_module_path_by_name(db_path, name))
                })
            }
        }
    })
}

/// We'll adjust the forward and reverse naming table to reflect changes to
/// files which changed since the saved-state. Files with saved errors and
/// their baseline symbol owners also go through naming to restore
/// duplicate-name tracking. (`update_naming_table env genv ~do_indexing
/// ~state_result`: see the OCaml's documentation.)
fn update_naming_table(
    env: Env,
    genv: &Genv,
    do_indexing: bool,
    state_result: &(LoadedInfo, RPSet, Option<server_notifier::Clock>),
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> (
    Env,
    f64,
    Option<naming_table::T>,
    RPMap<file_info::old_names::T>,
) {
    let (loaded_info, changed_while_parsing, clock) = state_result;
    let trace = genv.local_config.trace_parsing;
    let LoadedInfo {
        naming_table_fallback_fn,
        changed_files_since_saved_state_rev,
        dirty_local_files,
        dirty_master_files,
        old_naming_table,
        old_errors,
        ..
    } = loaded_info;
    server_progress::with_message(None, None, "updating file-to-symbol table", || {
        let t = gettimeofday();
        let old_error_files_and_owners = match naming_table_fallback_fn {
            None => old_errors.clone(),
            Some(db_path) => get_saved_state_error_files_and_owners(
                old_naming_table,
                &naming_sqlite::DbPath(db_path.clone()),
                old_errors,
            ),
        };
        let naming_files: RPSet = changed_files_since_saved_state_rev
            .clone()
            .union(dirty_master_files.clone())
            .union(dirty_local_files.clone())
            .union(changed_while_parsing.clone())
            .union(old_error_files_and_owners.clone())
            .into_iter()
            .filter(find_utils::path_filter)
            .collect();
        let file_count = naming_files.len();
        hh_logger::log(&format!(
            "Processing {} hack/php files for naming (that are not ignored according to ignore_paths flag).",
            file_count
        ));
        cgroup_profiler::step_start_end(cgroup_steps, None, "remove fixmes", || {
            crate::fixme_provider::remove_batch(&naming_files.iter().cloned().collect())
        });
        // Parse dirty files and files needed to restore duplicate-name tracking.
        let files: Vec<relative_path::T> = naming_files.iter().cloned().collect();
        let (env, t) = server_init_common::parse_files_and_update_forward_naming_table(
            genv,
            env,
            Box::new(move || files),
            Some(file_count),
            t,
            trace,
            // Don't overwrite old decls loaded from saved state
            DirectDeclMode::Normal,
            "post_ss1.parsing",
            cgroup_steps,
        );
        let ctx = provider_utils::ctx_from_server_env(&env);
        let old_names_per_file =
            // TODO(T298623016): Populate old hashes independently of remote fetching.
            if crate::provider_context::get_tcopt(&ctx).tco_remote_old_decl_fetching_include_non_class {
                let add_parsed_file = |mut files: RPMap<file_info::T>, path: &relative_path::T| {
                    let file_info = naming_table::get_file_info(&env.naming_table, path)
                        .unwrap_or_else(file_info::empty_t);
                    files.insert(path.clone(), file_info);
                    files
                };
                let defs_per_file_parsed = {
                    // Ignored files are not parsed or renamed, but old conflict owners
                    // must remain in the metadata snapshot to include every old winner.
                    let snapshot_files = naming_files.clone().union(old_error_files_and_owners);
                    snapshot_files.iter().fold(RPMap::new(), add_parsed_file)
                };
                // Capture information about "old" decls that reflect the state as of the
                // saved state. Crucially, this must run before the reverse naming table
                // updates below, at which point the reverse naming table includes the
                // changes since the saved state.
                crate::server_incremental::get_old_names_batch(
                    &ctx,
                    old_naming_table,
                    &defs_per_file_parsed,
                )
            } else {
                RPMap::new()
            };
        let t = remove_items_from_reverse_naming_table_or_build_new_reverse_naming_table(
            &ctx,
            old_naming_table,
            &naming_files,
            naming_table_fallback_fn.as_deref(),
            t,
            cgroup_steps,
        );
        if do_indexing {
            let (env, t) = write_symbol_info(genv, env, cgroup_steps, t);
            (env, t, None, old_names_per_file)
        } else {
            // Do global naming on all parsed files
            let (env, t) = server_init_common::update_reverse_naming_table_from_env_and_get_duplicate_name_errors(
                env,
                t,
                "post_ss1.naming",
                cgroup_steps,
            );
            server_init_common::validate_no_errors(&env.diagnostics);
            let new_naming_table = env.naming_table.clone();
            let env = Env {
                clock: clock.clone(),
                naming_table: naming_table::combine(old_naming_table, &env.naming_table),
                disk_needs_parsing: RPSet::new(),
                needs_recheck: env.needs_recheck.clone().union(old_errors.clone()),
                ..env
            };
            (env, t, Some(new_naming_table), old_names_per_file)
        }
    })
}

/// `log_changed_files_counts ...`
fn log_changed_files_counts(
    dirty_local_files_unchanged_decls: &RPSet,
    dirty_local_files_changed_decls: &RPSet,
    dirty_master_files_unchanged_decls: &RPSet,
    dirty_master_files_changed_decls: &RPSet,
    dirty_master_files: &RPSet,
    dirty_local_files: &RPSet,
) {
    hh_logger::log(&format!(
        "Number of files changed between saved state revision and mergebase: {}",
        dirty_master_files.len()
    ));
    hh_logger::log(&format!(
        "Out of which {} have changed decls, and the rest ({}) have unchanged decls",
        dirty_master_files_changed_decls.len(),
        dirty_master_files_unchanged_decls.len()
    ));
    hh_logger::log(&format!(
        "Number of files changed since mergebase: {}",
        dirty_local_files.len()
    ));
    hh_logger::log(&format!(
        "Out of which {} have changed decls, and the rest ({}) have unchanged decls",
        dirty_local_files_changed_decls.len(),
        dirty_local_files_unchanged_decls.len()
    ));
}

/// What files should be checked? (`compute_fanout env genv t
/// ~old_naming_table ~old_names_per_file ~new_naming_table ~dirty_master_files
/// ~dirty_local_files`: see the OCaml's documentation.)
fn compute_fanout(
    env: Env,
    genv: &Genv,
    t: f64,
    cgroup_steps: &cgroup_profiler::StepGroup,
    old_naming_table: &naming_table::T,
    old_names_per_file: &RPMap<file_info::old_names::T>,
    new_naming_table: &naming_table::T,
    dirty_master_files: &RPSet,
    dirty_local_files: &RPSet,
) -> (Env, f64) {
    server_progress::with_message(None, None, "figuring out files to recheck", || {
        let partition_unchanged_hash = |dirty_files: &RPSet| -> (RPSet, RPSet) {
            dirty_files.iter().cloned().partition(|f| {
                let old_info = naming_table::get_file_info(old_naming_table, f);
                let new_info = naming_table::get_file_info(&env.naming_table, f);
                match (old_info, new_info) {
                    (Some(x), Some(y)) => match (x.position_free_decl_hash.0, y.position_free_decl_hash.0) {
                        (Some(x), Some(y)) => x == y,
                        _ => false,
                    },
                    _ => false,
                }
            })
        };
        let (dirty_master_files_unchanged_decls, dirty_master_files_changed_decls) =
            partition_unchanged_hash(dirty_master_files);
        let (dirty_local_files_unchanged_decls, dirty_local_files_changed_decls) =
            partition_unchanged_hash(dirty_local_files);
        log_changed_files_counts(
            &dirty_local_files_unchanged_decls,
            &dirty_local_files_changed_decls,
            &dirty_master_files_unchanged_decls,
            &dirty_master_files_changed_decls,
            dirty_master_files,
            dirty_local_files,
        );
        calculate_fanout_and_defer_or_do_type_check(
            genv,
            env,
            old_naming_table,
            old_names_per_file,
            new_naming_table,
            &dirty_master_files_unchanged_decls,
            &dirty_master_files_changed_decls,
            &dirty_local_files_unchanged_decls,
            &dirty_local_files_changed_decls,
            t,
            cgroup_steps,
        )
    })
}

/// Among other things, updates the naming table and compute fanout.
/// (`post_saved_state_initialization ~do_indexing ~genv ~env
/// ~state_result`)
fn post_saved_state_initialization(
    do_indexing: bool,
    genv: &Genv,
    env: Env,
    state_result: &(LoadedInfo, RPSet, Option<server_notifier::Clock>),
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> (Env, f64) {
    let (loaded_info, _changed_while_parsing, _clock) = state_result;
    let LoadedInfo {
        dirty_local_files,
        dirty_master_files,
        old_naming_table,
        old_errors,
        old_warnings,
        deptable_fn,
        saved_state_revs_info,
        naming_table_manifold_path,
        ..
    } = loaded_info;
    // (`Hack_event_logger.set_mergebase_globalrev` of the mergebase globalrev:
    // a no-op.)
    if genv.local_config.hg_aware {
        if server_args::is_using_precomputed_saved_state(&genv.options)
            && !genv.local_config.allow_restart_from_precomputed_saved_state
        {
            // (`Hack_event_logger.tried_to_be_hg_aware_with_precomputed_saved_state_warning`:
            // a no-op.)
            hh_logger::log(
                "Warning: disabling restart on rebase (server was started with precomputed saved-state)",
            );
        } else {
            // (`Server_revision_tracker.initialize` of the mergebase
            // globalrev: the revision tracker is Meta's (`hg_aware`), not
            // ported.)
        }
    }
    let env = Env {
        init_env: server_env::InitEnv {
            mergebase_warning_hashes: if !server_args::preexisting_warnings(&genv.options) {
                Some(old_warnings.clone())
            } else {
                None
            },
            naming_table_manifold_path: naming_table_manifold_path.clone(),
            saved_state_revs_info: Some(saved_state_revs_info.clone()),
            ..env.init_env.clone()
        },
        deps_mode: match server_args::save_64bit(&genv.options) {
            Some(new_edges_dir) => {
                let human_readable_dep_map_dir = server_args::save_human_readable_64bit_dep_map(&genv.options);
                typing_deps::mode::T::SaveToDiskMode {
                    graph: Some(deptable_fn.clone()),
                    new_edges_dir,
                    human_readable_dep_map_dir,
                }
            }
            None => typing_deps::mode::T::InMemoryMode(Some(deptable_fn.clone())),
        },
        ..env
    };
    // The context of the providers, with the new dependency mode.
    let env = crate::server_type_check::with_ctx_of_env(env);
    hh_logger::log(&format!("Number of files with errors: {}", old_errors.len()));
    // (INVARIANTS: `Hack_event_logger.invariant_violation_bug` only, a
    // no-op: old_naming_table is Backed with an empty delta, env.naming_table
    // is Unbacked and empty, env.disk_needs_parsing and env.needs_recheck are
    // empty.)
    let _ = naming_table::get_backed_delta_test_only(old_naming_table);
    // NAMING TABLE. See doc of update_naming_table.
    let (env, t, new_naming_table, old_names_per_file) =
        update_naming_table(env, genv, do_indexing, state_result, cgroup_steps);
    // FANOUT. See doc of compute_fanout
    match new_naming_table {
        None => (env, t),
        Some(new_naming_table) => compute_fanout(
            env,
            genv,
            t,
            cgroup_steps,
            old_naming_table,
            &old_names_per_file,
            &new_naming_table,
            dirty_master_files,
            dirty_local_files,
        ),
    }
}

/// `load_saved_state_exn env genv load_state_approach root cgroup_steps`
fn load_saved_state_exn(
    env: &Env,
    genv: &Genv,
    load_state_approach: &LoadStateApproach,
    root: &path::T,
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> Result<Result<LoadedInfo, LoadStateError>, exception::T> {
    cgroup_profiler::step_start_end(cgroup_steps, None, "load saved state", || {
        let ctx = provider_utils::ctx_from_server_env(env);
        match load_state_approach {
            LoadStateApproach::Precomputed(info) => {
                Ok(Ok(use_precomputed_state_exn(root, genv, &ctx, info, cgroup_steps)?))
            }
            LoadStateApproach::LoadStateNatively => Ok(Err(download_and_load_state_exn(genv, root))),
        }
    })
}

/// `saved_state_init ~do_indexing ~load_state_approach genv env root
/// cgroup_steps`. The
/// error comes back with the environment (the OCaml keeps its `env` for the
/// fallback to a full init): its context is made afresh (the OCaml's naming
/// heap would keep the SQLite fallback of a state whose load failed later,
/// e.g. at the `hg` query; here the fallback full init starts from an empty
/// context).
pub fn saved_state_init(
    do_indexing: bool,
    load_state_approach: &LoadStateApproach,
    genv: &Genv,
    env: Env,
    root: &path::T,
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> Result<((Env, f64), server_env::SavedStateRevsInfo), (Env, LoadStateError)> {
    // `check_credentials genv`: `Security.check_credentials` is `Ok
    // Checks_skipped` in the open-source build (and the event logger a
    // no-op).
    server_progress::write(None, None, "loading saved state");
    let _t = gettimeofday();
    let state_result: Result<(LoadedInfo, RPSet, Option<server_notifier::Clock>), LoadStateError> =
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            match load_saved_state_exn(&env, genv, load_state_approach, root, cgroup_steps)? {
                Err(e) => Ok(Err(e)),
                Ok(loaded_info) => {
                    let (changed_while_parsing, clock) = get_updates_exn(genv, root)?;
                    Ok(Ok((loaded_info, changed_while_parsing, clock)))
                }
            }
        })) {
            Ok(Ok(r)) => r,
            Ok(Err(e)) => Err(LoadStateError::LoadStateUnhandledException(e)),
            Err(payload) => Err(LoadStateError::LoadStateUnhandledException(exception::wrap(payload))),
        };
    // (`Hack_event_logger.saved_state_download_and_load_done`: a no-op.)
    crate::hack_event_logger::flush();
    match state_result {
        Err(e) => {
            let env = match crate::ctx::Ctx::new(&env.ctx.path_ctx.root, (*env.ctx.tco).clone()) {
                Ok(ctx) => crate::server_type_check::with_ctx_of_env(Env {
                    ctx: Arc::new(ctx),
                    ..env
                }),
                Err(err) => panic!("{:#}", err),
            };
            Err((env, e))
        }
        Ok(state_result) => {
            server_progress::write(None, None, "loading saved state succeeded");
            hh_logger::log(&format!(
                "Watchclock: {}",
                server_env::show_clock(state_result.2.as_ref())
            ));
            let (env, t) = post_saved_state_initialization(do_indexing, genv, env, &state_result, cgroup_steps);
            Ok(((env, t), state_result.0.saved_state_revs_info.clone()))
        }
    }
}

/// The equivalence of a saved-state load with a full init: a state of the
/// base tree (the producer, `Save_state_service.save_state`), files changed
/// before the load, then the daemon loaded from the state against a fresh
/// daemon on the changed tree; then rechecks after the load against fresh
/// daemons. Each daemon runs in a child process (global state), as
/// `server_type_check::tests`.
#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::path::PathBuf;
    use std::process::Command;
    use std::process::Stdio;

    use super::*;
    use crate::diagnostics;
    use crate::server_env::FullCheckStatus;
    use crate::server_init_types::InitApproach;

    const CHILD_MODE: &str = "HH_LAZY_INIT_TEST_MODE";

    type Files<'a> = &'a [(&'a str, &'a str)];
    type Step<'a> = &'a [(&'a str, Option<&'a str>)];

    fn write_files(root: &Path, files: Step<'_>) {
        std::fs::create_dir_all(root).unwrap();
        for (name, contents) in files {
            let path = root.join(name);
            match contents {
                Some(contents) => {
                    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
                    std::fs::write(path, contents).unwrap();
                }
                None => {
                    let _ = std::fs::remove_file(path);
                }
            }
        }
    }

    fn show(root: &Path, env: &Env) -> String {
        let root = format!("{}/", root.display());
        let mut out = String::new();
        for d in &diagnostics::get_sorted_diagnostic_list(None, env.diagnostics.clone()) {
            let s = crate::user_diagnostic::to_string(&crate::user_diagnostic::to_absolute(d));
            out.push_str(&s.replace(&root, "ROOT/"));
            out.push('\n');
        }
        out
    }

    fn make_genv(root: &Path, args: &[&str]) -> Genv {
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, root);
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Hhi, Path::new("/hhi"));
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Tmp, Path::new("/tmp"));
        // (`fetch_remote_old_decls` is true by default: the open-source build
        // then fails when a class changed, as the OCaml's.)
        let overrides = [("fetch_remote_old_decls".to_string(), "false".to_string())];
        let (config, local_config) = crate::server_config::load(true, "", &overrides).unwrap();
        let mut argv = vec!["hh_server".to_string(), root.display().to_string()];
        argv.extend(args.iter().map(|s| s.to_string()));
        let options = crate::server_args::parse_options_of_argv(argv, "").unwrap();
        Genv {
            options,
            config,
            local_config,
            notifier: crate::server_notifier::T::IndexOnly {
                root: crate::path::make(&root.display().to_string()),
            },
            num_workers: 1,
        }
    }

    fn make_env(genv: &Genv, root: &Path) -> Env {
        crate::server_env_build::make_env(
            "test",
            crate::typing_deps::mode::T::InMemoryMode(None),
            None,
            &genv.config,
            root,
        )
    }

    /// Rechecks until there is nothing left to recheck (the daemon's loop).
    fn settle(genv: &Genv, mut env: Env) -> Env {
        loop {
            let done = env.needs_recheck.is_empty()
                && env.disk_needs_parsing.is_empty()
                && server_env::is_full_check_done(env.full_check_status);
            if done {
                return env;
            }
            if server_env::is_full_check_done(env.full_check_status) {
                env = Env {
                    full_check_status: FullCheckStatus::FullCheckStarted,
                    ..env
                };
            }
            env = crate::cgroup_profiler::step_group("Full_check", true, |steps| {
                crate::server_type_check::type_check(None, genv, env, gettimeofday(), steps)
            })
            .0;
        }
    }

    /// Applies the edits of `edits/<step>` (files, and `<step>.deleted`),
    /// then rechecks.
    fn recheck_steps(genv: &Genv, mut env: Env, root: &Path, edits: &Path, out: &mut String) -> Env {
        let mut step = 1;
        loop {
            let dir = edits.join(step.to_string());
            if !dir.exists() {
                return env;
            }
            let mut changed = relative_path::set::T::new();
            let mut files = vec![];
            let mut stack = vec![dir.clone()];
            while let Some(d) = stack.pop() {
                for e in std::fs::read_dir(&d).unwrap() {
                    let p = e.unwrap().path();
                    if p.is_dir() {
                        stack.push(p)
                    } else {
                        files.push(p)
                    }
                }
            }
            for f in files {
                let dest = root.join(f.strip_prefix(&dir).unwrap());
                std::fs::create_dir_all(dest.parent().unwrap()).unwrap();
                std::fs::copy(&f, &dest).unwrap();
                changed.insert(relative_path::create(relative_path::Prefix::Root, &dest.display().to_string()));
            }
            if let Ok(deleted) = std::fs::read_to_string(edits.join(format!("{}.deleted", step))) {
                for name in deleted.lines().filter(|l| !l.is_empty()) {
                    let dest = root.join(name);
                    let _ = std::fs::remove_file(&dest);
                    changed.insert(relative_path::create(relative_path::Prefix::Root, &dest.display().to_string()));
                }
            }
            env = Env {
                disk_needs_parsing: env.disk_needs_parsing.clone().union(changed),
                full_check_status: FullCheckStatus::FullCheckStarted,
                ..env
            };
            env = settle(genv, env);
            out.push_str(&format!("=== step {}\n", step));
            out.push_str(&show(root, &env));
            step += 1;
        }
    }

    fn run_child(mode: &str) -> String {
        crate::server_progress::disable();
        crate::check::build_thread_pool(Some(2)).unwrap();
        crate::typing_deps::TRACE.store(true, std::sync::atomic::Ordering::SeqCst);
        let var = |k: &str| std::env::var(k).unwrap();
        let root = PathBuf::from(var("HH_LAZY_INIT_TEST_ROOT"));
        let state = var("HH_LAZY_INIT_TEST_STATE");
        match mode {
            "produce" => {
                let genv = make_genv(&root, &[]);
                let env = make_env(&genv, &root);
                let (env, _) = crate::server_init::init(&genv, env, InitApproach::FullInit);
                let env = settle(&genv, env);
                crate::save_state_writer::save_state_service_save_state(&env, &state).unwrap();
                show(&root, &env)
            }
            "full" | "load" => {
                let genv = make_genv(&root, &["--preexisting-warnings"]);
                let env = make_env(&genv, &root);
                let approach = if mode == "full" {
                    InitApproach::FullInit
                } else {
                    let changes: Vec<relative_path::T> = var("HH_LAZY_INIT_TEST_CHANGES")
                        .lines()
                        .filter(|l| !l.is_empty())
                        .map(relative_path::from_root)
                        .collect();
                    InitApproach::SavedStateInit(LoadStateApproach::Precomputed(server_args::SavedStateTargetInfo {
                        changes,
                        naming_changes: vec![],
                        corresponding_base_revision: "1".to_string(),
                        deptable_fn: format!("{}.hhdg", state),
                        compressed_deptable_fn: None,
                        prechecked_changes: vec![],
                        naming_table_path: state.clone(),
                    }))
                };
                let (env, result) = crate::server_init::init(&genv, env, approach);
                if mode == "load" {
                    assert!(
                        matches!(result, crate::server_init_types::InitResult::LoadStateSucceeded(_)),
                        "the load failed"
                    );
                    assert!(naming_table::get_forward_naming_fallback_path(&env.naming_table).is_some());
                }
                let env = settle(&genv, env);
                let mut out = String::from("=== step 0\n");
                out.push_str(&show(&root, &env));
                if let Ok(edits) = std::env::var("HH_LAZY_INIT_TEST_EDITS") {
                    recheck_steps(&genv, env, &root, Path::new(&edits), &mut out);
                }
                out
            }
            _ => panic!("mode {}", mode),
        }
    }

    /// The child process: does nothing unless run by [`spawn`].
    #[test]
    fn child() {
        let Some(mode) = std::env::var_os(CHILD_MODE) else {
            return;
        };
        let mode = mode.to_string_lossy().into_owned();
        let out = crate::check::run_on_large_stack("world", move || run_child(&mode)).unwrap();
        std::fs::write(std::env::var("HH_LAZY_INIT_TEST_OUT").unwrap(), out).unwrap();
    }

    fn spawn(mode: &str, vars: &[(&str, String)], out: &Path, bin: &Path) -> String {
        let mut cmd = Command::new(std::env::current_exe().unwrap());
        cmd.args(["server_lazy_init::tests::child", "--exact", "--nocapture", "--test-threads=1"])
            .env(CHILD_MODE, mode)
            .env("HH_LAZY_INIT_TEST_OUT", out)
            // `hg` (the loader asks it for the mergebase): one that fails.
            .env("PATH", format!("{}:{}", bin.display(), std::env::var("PATH").unwrap_or_default()))
            .stdin(Stdio::null());
        for (k, v) in vars {
            cmd.env(k, v);
        }
        let output = cmd.output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && stdout.contains("1 passed"),
            "the child ({mode}) failed:\n{stdout}\n{}",
            &stderr[stderr.len().saturating_sub(20000)..]
        );
        std::fs::read_to_string(out).unwrap()
    }

    fn write_edits(edits: &Path, steps: &[Step<'_>]) {
        for (k, step) in steps.iter().enumerate() {
            let step_dir = edits.join((k + 1).to_string());
            std::fs::create_dir_all(&step_dir).unwrap();
            let mut deleted = String::new();
            for (name, contents) in step.iter() {
                match contents {
                    Some(contents) => {
                        let path = step_dir.join(name);
                        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
                        std::fs::write(path, contents).unwrap();
                    }
                    None => {
                        deleted.push_str(name);
                        deleted.push('\n');
                    }
                }
            }
            std::fs::write(edits.join(format!("{}.deleted", k + 1)), deleted).unwrap();
        }
    }

    /// A state of `base`, the `before_load` changes, a load against a full
    /// init, then each of `after_load` on both.
    fn equivalence(test: &str, base: Files<'_>, before_load: Step<'_>, after_load: &[Step<'_>]) {
        let dir = std::env::temp_dir()
            .canonicalize()
            .unwrap()
            .join(format!("hh-ss3-{}-{}", test, std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let bin = dir.join("bin");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::write(bin.join("hg"), "#!/bin/sh\nexit 1\n").unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(bin.join("hg"), std::fs::Permissions::from_mode(0o755)).unwrap();
        let state = dir.join("state").join("s").display().to_string();
        let base_files: Vec<(&str, Option<&str>)> = base.iter().map(|(n, c)| (*n, Some(*c))).collect();
        let edits = dir.join("edits");
        write_edits(&edits, after_load);
        // The state of the base tree.
        let prod = dir.join("prod");
        write_files(&prod, &base_files);
        std::fs::write(prod.join(".hhconfig"), "").unwrap();
        spawn(
            "produce",
            &[("HH_LAZY_INIT_TEST_ROOT", prod.display().to_string()), ("HH_LAZY_INIT_TEST_STATE", state.clone())],
            &dir.join("prod.out"),
            &bin,
        );
        assert!(Path::new(&format!("{}.hhdg", state)).exists());
        let changes: String = before_load.iter().map(|(n, _)| format!("{}\n", n)).collect();
        let mut outs = vec![];
        for mode in ["load", "full"] {
            let root = dir.join(mode);
            write_files(&root, &base_files);
            std::fs::write(root.join(".hhconfig"), "").unwrap();
            write_files(&root, before_load);
            outs.push(spawn(
                mode,
                &[
                    ("HH_LAZY_INIT_TEST_ROOT", root.display().to_string()),
                    ("HH_LAZY_INIT_TEST_STATE", state.clone()),
                    ("HH_LAZY_INIT_TEST_CHANGES", changes.clone()),
                    ("HH_LAZY_INIT_TEST_EDITS", edits.display().to_string()),
                ],
                &dir.join(format!("{}.out", mode)),
                &bin,
            ));
        }
        assert_eq!(outs[0], outs[1], "{test}: the load differs from a full init");
        // (Every scenario has diagnostics: the comparison is not of nothing.)
        assert!(outs[0].lines().count() > 2, "{test}: {}", outs[0]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    const BASE: &[(&str, &str)] = &[
        ("base.php", "<?hh
interface I { public function m(): int; }
abstract class Base implements I {
  public int $p = 0;
  public function m(): int { return 1; }
  abstract public function g(int $x): int;
}
type Alias = shape('a' => int);
const int K0 = 3;
function mk(int $i): Alias { return shape('a' => $i); }
"),
        ("a.php", "<?hh
class A extends Base {
  public function g(int $x): int { return $x + K0; }
}
function fa(A $a): int { return $a->g(1) + $a->m(); }
"),
        ("b.php", "<?hh
class B extends A {}
function fb(): int { return fa(new B()) + mk(1)['a']; }
"),
        ("c.php", "<?hh
function fc(): string { return 'c'; }
function warn_c(int $i): bool { return $i === null; }
"),
        ("err.php", "<?hh
function err(): int { return 'x'; }
"),
        ("use_c.php", "<?hh
function use_c(): string { return fc(); }
"),
    ];

    #[test]
    fn body_change_before_load() {
        equivalence("body", BASE, &[("c.php", Some("<?hh\nfunction fc(): string { return 'd'; }\nfunction warn_c(int $i): bool { return $i === null; }\n"))], &[]);
    }

    #[test]
    fn signature_changes_before_load() {
        equivalence(
            "sig",
            BASE,
            &[
                ("c.php", Some("<?hh\nfunction fc(): int { return 1; }\n")),
                ("base.php", Some("<?hh\ninterface I { public function m(): string; }\nabstract class Base implements I {\n  public int $p = 0;\n  public function m(): string { return 'a'; }\n  abstract public function g(int $x): int;\n}\ntype Alias = shape('a' => string);\nconst string K0 = 'x';\nfunction mk(int $i): Alias { return shape('a' => 'y'); }\n")),
            ],
            &[],
        );
    }

    #[test]
    fn classes_removed_added_and_files_deleted_before_load() {
        equivalence(
            "classes",
            BASE,
            &[
                ("a.php", None),
                ("new.php", Some("<?hh\nclass A2 extends Base { public function g(int $x): int { return 0; } }\nfunction fnew(): int { return fa(new A2()); }\n")),
                ("err.php", Some("<?hh\nfunction err(): int { return 0; }\n")),
            ],
            &[],
        );
    }

    #[test]
    fn duplicates_and_syntax_errors_before_load() {
        equivalence(
            "dups",
            BASE,
            &[
                ("dup.php", Some("<?hh\nfunction fc(): string { return 'dup'; }\nclass B {}\n")),
                ("syntax.php", Some("<?hh\nfunction broken( {\n")),
            ],
            &[],
        );
    }

    #[test]
    fn rechecks_after_load() {
        equivalence(
            "after",
            BASE,
            &[("c.php", Some("<?hh\nfunction fc(): string { return 'd'; }\n"))],
            &[
                &[("dup.php", Some("<?hh\nfunction fc(): string { return 'dup'; }\n"))],
                &[("dup.php", None)],
                &[("base.php", Some("<?hh\ninterface I { public function m(): int; }\nabstract class Base implements I {\n  public int $p = 0;\n  public function m(): int { return 1; }\n  abstract public function g(int $x): int;\n  public function added(): void {}\n}\ntype Alias = shape('a' => int);\nconst int K0 = 3;\nfunction mk(int $i): Alias { return shape('a' => $i); }\n"))],
                &[("a.php", None)],
                &[("a.php", Some("<?hh\nclass A extends Base {\n  public function g(int $x): int { return $x + K0; }\n}\nfunction fa(A $a): int { return $a->g(1) + $a->m(); }\n"))],
                &[("err.php", None)],
            ],
        );
    }
}
