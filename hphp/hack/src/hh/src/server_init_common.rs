// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_init_common.ml`.
//!
//! Owned by **S1** (plan §3.1).
//!
//! How the init's parsing and naming map onto the `Ctx` (plan D4, N1's
//! init order): with `Direct_decl_service.Cached` (the full init), the
//! files are declared by the batch checker's parallel declaration
//! ([`check::declare_files_with`]), which binds every name to the
//! declaration the OCaml's sequential naming in `Relative_path.Map` order
//! binds it to, and gives each file's decls to build the forward naming
//! table (no second parse). The naming step
//! ([`update_reverse_naming_table_from_env_and_get_duplicate_name_errors`])
//! then builds the reverse naming table from those bindings
//! (`Ctx::build_dep_hash_index`) and computes `failed_naming` as
//! `Naming_global.ndecl_file_and_get_conflict_files` would have, file after
//! file (`Ctx::take_init_conflict_files`). Deviations, not observable: the
//! decls cached while parsing are those of the winners (the OCaml's
//! `Shared_mem` heap keeps whichever worker wrote a name first, then the
//! naming binds the first file); the file infos of the full init have no
//! decl hashes and no mode (only saved states read them).

use std::sync::Arc;
use std::sync::Mutex;

use crate::check;
use crate::diagnostics_state;
use crate::direct_decl_service;
use crate::file_info;
use crate::find_utils;
use crate::hh_logger;
use crate::naming_table;
use crate::relative_path;
use crate::rt::ocaml_unix::gettimeofday;
use crate::server_args;
use crate::server_check_utils;
use crate::server_config;
use crate::server_env;
use crate::server_env::Env;
use crate::server_env::FullCheckStatus;
use crate::server_env::Genv;
use crate::server_env::InitTelemetry;
use crate::server_env::PrecheckedFilesStatus;
use crate::server_notifier;
use crate::server_progress;
use crate::typing_check_service;
use crate::user_diagnostic;

type RPSet = crate::relative_path::set::T;
type RPMap<A> = crate::relative_path::map::T<A>;

/// `Relative_path.t list Bucket.next`: the files of the walk. The OCaml's
/// closure walks as it is called; this one walks when it is called (once).
pub type GetNext = Box<dyn FnOnce() -> Vec<relative_path::T> + Send>;

/// `Server_utils.make_next ?hhi_filter ~indexer ~extra_roots`: the hhi
/// files (those of the context: the binary's, which `Hhi.get_hhi_root ()`
/// extracts), then the files the indexer gives (under the root), then those
/// of the extra roots.
fn make_next(
    genv: &Genv,
    ctx: &Arc<crate::ctx::Ctx>,
    hhi_filter: Option<fn(&str) -> bool>,
) -> GetNext {
    let hhi_filter = hhi_filter.unwrap_or(find_utils::is_hack);
    let hhi_files: Vec<relative_path::T> = ctx
        .hhi_paths
        .iter()
        .map(|p| relative_path::T::from(*p))
        .filter(|p| hhi_filter(&relative_path::suffix(p)))
        .collect();
    let indexer = server_notifier::indexer(&genv.notifier, Box::new(find_utils::file_filter));
    let extra_roots = server_config::extra_paths(&genv.config);
    Box::new(move || {
        let mut files = hhi_files;
        let mut next = match indexer {
            Ok(next) => next,
            Err(e) => std::panic::panic_any(e),
        };
        loop {
            let batch = next();
            if batch.is_empty() {
                break;
            }
            files.extend(
                batch
                    .iter()
                    .map(|f| relative_path::create(relative_path::Prefix::Root, f)),
            );
        }
        for root in &extra_roots {
            let mut next = crate::find::make_next_files(
                None,
                None,
                Some(Box::new(find_utils::file_filter)),
                None,
                root,
            );
            loop {
                let batch = next();
                if batch.is_empty() {
                    break;
                }
                files.extend(batch.iter().map(|f| relative_path::create_detect_prefix(f)));
            }
        }
        files
    })
}

/// `directory_walk ?hhi_filter ~telemetry_label genv`
pub fn directory_walk(
    hhi_filter: Option<fn(&str) -> bool>,
    telemetry_label: &str,
    genv: &Genv,
    env: &Env,
) -> (GetNext, f64) {
    server_progress::write(None, None, "indexing");
    let t = gettimeofday();
    let get_next = make_next(genv, &env.ctx, hhi_filter);
    // (`Hack_event_logger.indexing_end`: a no-op in the open-source build.)
    let t = hh_logger::log_duration(None, None, &format!("indexing {}", telemetry_label), t);
    (get_next, t)
}

/// The full init's `Direct_decl_service.go ~decl_mode:Cached`: see the
/// module documentation. The files `Find_utils.path_filter` rejects are
/// skipped, as `Direct_decl_service.parse` skips them.
fn declare_and_get_file_infos(env: &Env, files: Vec<relative_path::T>) -> RPMap<file_info::T> {
    let paths: Vec<pos::RelativePath> = files
        .iter()
        .filter(|f| find_utils::path_filter(f))
        .map(pos::RelativePath::from)
        .collect();
    let infos: Mutex<Vec<(relative_path::T, file_info::T)>> = Mutex::new(Vec::with_capacity(paths.len()));
    let on_file = |path: pos::RelativePath, decls: &[ty::decl::shallow::NamedDecl<crate::ctx::R>]| {
        let info = direct_decl_service::file_info_of_decls(path, decls, None);
        infos
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push((path.into(), info));
    };
    check::declare_files_with(&env.ctx, &paths, &mut check::Stats::default(), &on_file);
    infos
        .into_inner()
        .unwrap_or_else(|e| e.into_inner())
        .into_iter()
        .collect()
}

/// This parses files with the direct decl parser and uses the result to update
/// the naming table in the provided env.
pub fn parse_files_and_update_forward_naming_table(
    genv: &Genv,
    env: Env,
    get_next: GetNext,
    count: Option<usize>,
    t: f64,
    trace: bool,
    decl_mode: direct_decl_service::DeclMode,
    telemetry_label: &str,
) -> (Env, f64) {
    let _ = genv;
    match count {
        None => server_progress::write(None, None, "parsing"),
        Some(c) => server_progress::write(None, None, &format!("parsing {} files", c)),
    }
    let files = get_next();
    let defs_per_file = match decl_mode {
        direct_decl_service::DeclMode::Cached => declare_and_get_file_infos(&env, files),
        direct_decl_service::DeclMode::Normal => {
            direct_decl_service::go(&env.ctx, &files, trace, decl_mode)
        }
    };
    let naming_table = naming_table::update_many(&env.naming_table, &defs_per_file);
    // (`Stats.init_parsing_heap_size`, `Hack_event_logger.parsing_end_for_init`:
    // the shared heap has no counterpart; the logger is a no-op.)
    let env = Env {
        naming_table,
        ..env
    };
    let t = hh_logger::log_duration(None, None, &format!("Parsing {}", telemetry_label), t);
    (env, t)
}

/// `update_reverse_naming_table_from_env_and_get_duplicate_name_errors env t
/// ~telemetry_label`: the naming of every file of the naming table, after
/// [`parse_files_and_update_forward_naming_table`] with
/// `Direct_decl_service.Cached` (see the module documentation).
pub fn update_reverse_naming_table_from_env_and_get_duplicate_name_errors(
    env: Env,
    t: f64,
    telemetry_label: &str,
) -> (Env, f64) {
    let env = server_progress::with_message(None, None, "resolving symbol references", || {
        let failed_naming = env.ctx.take_init_conflict_files(&env.naming_table);
        env.ctx.build_dep_hash_index();
        Env {
            failed_naming: env.failed_naming.clone().union(failed_naming),
            ..env
        }
    });
    // (`Hack_event_logger.global_naming_end`: a no-op.)
    let t = hh_logger::log_duration(None, None, &format!("Naming {}", telemetry_label), t);
    (env, t)
}

/// `validate_no_errors errors`
pub fn validate_no_errors(errors: &diagnostics_state::T) {
    let witness_opt = diagnostics_state::fold_errors(None, errors, None, |path, error, _acc| {
        Some((path.clone(), error.clone()))
    });
    match witness_opt {
        None => {}
        Some((_path, error)) => {
            let error = user_diagnostic::to_string(&user_diagnostic::to_absolute(&error));
            hh_logger::log(&format!("Unexpected error during init: {}", error));
            // (`Hack_event_logger.invariant_violation_bug`: a no-op.)
        }
    }
}

/// `defer_or_do_type_check genv env files_to_check init_telemetry t
/// ~telemetry_label`
pub fn defer_or_do_type_check(
    genv: &Genv,
    env: Env,
    files_to_check: Vec<relative_path::T>,
    init_telemetry: InitTelemetry,
    t: f64,
    telemetry_label: &str,
) -> (Env, f64) {
    if server_args::check_mode(&genv.options) {
        // Prechecked files are not supported in check mode, we
        // should always recheck everything necessary up-front.
        assert!(matches!(
            env.prechecked_files,
            PrecheckedFilesStatus::PrecheckedFilesDisabled
        ));
        // Streaming errors aren't supported for these niche cases: for simplicity, the only
        // code that sets up and tears down streaming errors is in [ServerTypeCheck.type_check].
        // Our current code calls into typing_check_service.ml without having done that set up,
        // and so we will override whatever was set before and disable it now.
        hh_logger::log("Streaming errors disabled for eager init");
        server_progress::enable_error_production(false);
        server_progress::write(None, None, "typechecking");
        let count = files_to_check.len();
        let logstring = format!("Filter {} files [{}]", count, telemetry_label);
        hh_logger::log(&format!("Begin {}", logstring));
        let files_to_check: Vec<relative_path::T> =
            if !genv.local_config.enable_type_check_filter_files {
                files_to_check
            } else {
                let files_to_check_set: RPSet = files_to_check.into_iter().collect();
                let filtered_check = server_check_utils::user_filter_type_check_files(
                    &files_to_check_set,
                    &RPSet::new(),
                );
                filtered_check.into_iter().collect()
            };
        let _new_t: f64 = hh_logger::log_duration(None, None, &logstring, t);
        let total_rechecked_count = files_to_check.len();
        let logstring = format!("type-check {} files", total_rechecked_count);
        hh_logger::log(&format!("Begin {}", logstring));
        let typing_check_service::TypingResult {
            diagnostics: errorl,
            telemetry: _typecheck_telemetry,
        } = {
            let ctx = Arc::clone(&env.ctx);
            let check_info = server_check_utils::get_check_info(
                &server_env::init_telemetry::get_reason(&init_telemetry),
                true,
                server_env::discard_warnings(&env),
                genv,
                &env,
            );
            typing_check_service::go(&ctx, &files_to_check, &check_info)
        };
        let env = Env {
            diagnostics: diagnostics_state::merge(errorl, env.diagnostics),
            ..env
        };
        // (`log_type_check_end`: only `Hack_event_logger.type_check_end`,
        // a no-op in the open-source build, reads what it computes.)
        let t = hh_logger::log_duration(None, None, &logstring, t);
        (env, t)
    } else {
        let needs_recheck: RPSet = files_to_check.into_iter().collect();
        let env = Env {
            needs_recheck: env.needs_recheck.clone().union(needs_recheck),
            // eagerly start rechecking after init
            full_check_status: FullCheckStatus::FullCheckStarted,
            init_env: server_env::InitEnv {
                why_needed_full_check: Some(init_telemetry),
                ..env.init_env.clone()
            },
            ..env
        };
        (env, t)
    }
}
