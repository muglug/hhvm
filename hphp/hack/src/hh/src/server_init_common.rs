// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_init_common.ml`.
//!
//! How the init's parsing and naming map onto the `Ctx`: with
//! `Direct_decl_service.Cached` (the full init), the files are declared by the
//! batch checker's parallel declaration ([`check::declare_files_with`]), which
//! binds every name to the declaration the OCaml's sequential naming in
//! `Relative_path.Map` order binds it to, and gives each file's decls to build
//! the forward naming table (no second parse). The naming step
//! ([`update_reverse_naming_table_from_env_and_get_duplicate_name_errors`])
//! then builds the reverse naming table from those bindings
//! (`Ctx::build_reverse_naming_table`) and computes `failed_naming` as
//! `Naming_global.ndecl_file_and_get_conflict_files` would have, file after
//! file (`Ctx::take_init_conflict_files`). Deviations, not observable: the
//! decls cached while parsing are those of the winners (the OCaml's
//! `Shared_mem` heap keeps whichever worker wrote a name first, then the naming
//! binds the first file). The file infos of the full init have the decl hashes
//! and the mode, as the OCaml's (`Naming_table.save` and saved states write
//! them).

use std::sync::Arc;

use crate::cgroup_profiler;
use crate::check;
use crate::diagnostics;
use crate::direct_decl_service;
use crate::file_info;
use crate::find_utils;
use crate::hh_logger;
use crate::naming_table;
use crate::relative_path;
use crate::rt::ocaml_unix::gettimeofday;
use crate::server_args;
use crate::server_check_utils;
use crate::server_env;
use crate::server_env::Env;
use crate::server_env::FullCheckStatus;
use crate::server_env::Genv;
use crate::server_env::init_telemetry;
use crate::server_env::PrecheckedFilesStatus;
use crate::server_progress;
use crate::typing_check_service;
use crate::user_diagnostic;

type RPSet = crate::relative_path::set::T;
type RPMap<A> = crate::relative_path::map::T<A>;

/// `Relative_path.t list Bucket.next`: the files of the walk. The OCaml's
/// closure walks as it is called; this one walks when it is called (once).
pub type GetNext = Box<dyn FnOnce() -> Vec<relative_path::T> + Send>;

/// `directory_walk ?hhi_filter ~telemetry_label genv`: walks the directory
/// tree to find all .php files that match [Find_utils.file_filter]. It
/// actually returns a [Bucket.next], i.e. a lazy list, rather than doing it
/// eagerly.
pub fn directory_walk(
    hhi_filter: Option<fn(&str) -> bool>,
    telemetry_label: &str,
    genv: &Genv,
    env: &Env,
) -> (GetNext, f64) {
    directory_walk_with(telemetry_label, || crate::server_utils::make_next(genv, &env.ctx, hhi_filter))
}

/// [`directory_walk`] with the walk `walk` (the OCaml's `Server_utils.make_next`,
/// which walks lazily; `hh_server --check` walks at once): its progress and
/// its log line around `walk`.
pub fn directory_walk_with<R>(telemetry_label: &str, walk: impl FnOnce() -> R) -> (R, f64) {
    server_progress::write(None, None, "indexing");
    let t = gettimeofday();
    let get_next = walk();
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
    check::declare_files_with_infos(&env.ctx, &paths, &mut check::Stats::default())
        .into_iter()
        .map(|(path, info)| (relative_path::T::from(path), info))
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
    decl_mode: direct_decl_service::DirectDeclMode,
    telemetry_label: &str,
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> (Env, f64) {
    let _ = genv;
    parse_files_and_update_forward_naming_table_with(count, t, telemetry_label, cgroup_steps, || {
        let files = get_next();
        let defs_per_file = match decl_mode {
            direct_decl_service::DirectDeclMode::Cached => declare_and_get_file_infos(&env, files),
            direct_decl_service::DirectDeclMode::Normal => {
                direct_decl_service::go(&env.ctx, &files, trace, decl_mode)
            }
        };
        let naming_table = naming_table::update_many(&env.naming_table, &defs_per_file);
        Env {
            naming_table,
            ..env
        }
    })
}

/// [`parse_files_and_update_forward_naming_table`] with the parsing
/// `parse`: its cgroup step, progress and log line around `parse` (which
/// `hh_server --check` does its own way).
pub fn parse_files_and_update_forward_naming_table_with<R>(
    count: Option<usize>,
    t: f64,
    telemetry_label: &str,
    cgroup_steps: &cgroup_profiler::StepGroup,
    parse: impl FnOnce() -> R,
) -> (R, f64) {
    cgroup_profiler::step_start_end(cgroup_steps, None, telemetry_label, || {
        match count {
            None => server_progress::write(None, None, "parsing"),
            Some(c) => server_progress::write(None, None, &format!("parsing {} files", c)),
        }
        let r = parse();
        // (`Stats.init_parsing_heap_size`: no reader;
        // `Hack_event_logger.parsing_end_for_init`: a no-op.)
        let t = hh_logger::log_duration(None, None, &format!("Parsing {}", telemetry_label), t);
        (r, t)
    })
}

/// `update_reverse_naming_table_from_env_and_get_duplicate_name_errors env t
/// ~telemetry_label`: the naming of every file of the naming table, after
/// [`parse_files_and_update_forward_naming_table`] with
/// `Direct_decl_service.Cached` (see the module documentation).
pub fn update_reverse_naming_table_from_env_and_get_duplicate_name_errors(
    env: Env,
    t: f64,
    telemetry_label: &str,
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> (Env, f64) {
    update_reverse_naming_table_from_env_and_get_duplicate_name_errors_with(t, telemetry_label, cgroup_steps, || {
        if env.ctx.has_reverse_naming_table() {
            // After a saved-state load (the reverse naming table exists,
            // backed by the state's database): the OCaml's naming of each
            // file of the forward naming table, in order.
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            naming_table::fold(None, &env.naming_table.clone(), env, |k, fi, env| {
                let failed_naming = crate::naming_global::ndecl_file_and_get_conflict_files(&ctx, k, &fi.ids);
                Env {
                    failed_naming: env.failed_naming.clone().union(failed_naming),
                    ..env
                }
            })
        } else {
            let failed_naming = env.ctx.take_init_conflict_files(&env.naming_table);
            env.ctx.build_reverse_naming_table_from(Some(&env.naming_table));
            Env {
                failed_naming: env.failed_naming.clone().union(failed_naming),
                ..env
            }
        }
    })
}

/// [`update_reverse_naming_table_from_env_and_get_duplicate_name_errors`]
/// with the naming `name`: its cgroup step, progress and log line around
/// `name` (which `hh_server --check` does its own way).
pub fn update_reverse_naming_table_from_env_and_get_duplicate_name_errors_with<R>(
    t: f64,
    telemetry_label: &str,
    cgroup_steps: &cgroup_profiler::StepGroup,
    name: impl FnOnce() -> R,
) -> (R, f64) {
    cgroup_profiler::step_start_end(cgroup_steps, None, telemetry_label, || {
        let r = server_progress::with_message(None, None, "resolving symbol references", name);
        // (`Hack_event_logger.global_naming_end`: a no-op.)
        let t = hh_logger::log_duration(None, None, &format!("Naming {}", telemetry_label), t);
        (r, t)
    })
}

/// `validate_no_errors errors`: just a quick validation that there are no
/// errors
pub fn validate_no_errors(errors: &diagnostics::T) {
    let witness_opt = diagnostics::fold_errors(None, errors, None, |path, error, _acc| {
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

/// `log_type_check_end env genv ~start_t ~rust_disk_provider_read_start
/// ~total_rechecked_count ~desc ~init_telemetry ~typecheck_telemetry`: the
/// load of the shared hash table is logged; the rest is telemetry for
/// `Hack_event_logger.type_check_end`, a no-op in the open-source build.
pub fn log_type_check_end(
    rust_disk_provider_read_start: &server_env::RustDiskProviderReadTelemetry,
) {
    let _rust_disk_provider_read = server_env::rust_disk_provider_read_telemetry::get_delta_telemetry(
        rust_disk_provider_read_start,
    );
    let _hash_telemetry = crate::server_utils::log_and_get_sharedmem_load_telemetry();
}

/// `defer_or_do_type_check genv env files_to_check init_telemetry t
/// ~telemetry_label ~cgroup_steps`. This function has two different behaviors:
/// - For the normal case, it adds the provided list of files into
///   [env.needs_recheck]. It also sets
///   [env.full_check_status=Full_check_started] which is important for
///   correctness of streaming errors (it guarantees that ServerTypeCheck will
///   do an iteration, even if [env.needs_recheck] is empty). It also sets
///   [env.init_env] which is important for telemetry, so the first
///   ServerTypeCheck loop will record information about the Init_telemetry
///   (i.e. saved-state-loading) which determined the typecheck.
/// - For Zoncolan, and "hh_server check" (i.e. full init that doesn't
///   support incremental updates), and "hh_server --save-state" (i.e.
///   full-init which saves a state and then quits), it typechecks all the
///   files provided in the list.
pub fn defer_or_do_type_check(
    genv: &Genv,
    env: Env,
    files_to_check: Vec<relative_path::T>,
    init_telemetry: init_telemetry::T,
    t: f64,
    telemetry_label: &str,
    cgroup_steps: &cgroup_profiler::StepGroup,
) -> (Env, f64) {
    if server_args::check_mode(&genv.options) {
        // Prechecked files are not supported in check mode, we
        // should always recheck everything necessary up-front.
        assert!(matches!(
            env.prechecked_files,
            PrecheckedFilesStatus::PrecheckedFilesDisabled
        ));
        let (errorl, t) = do_type_check_with(
            genv.local_config.enable_type_check_filter_files,
            files_to_check,
            t,
            telemetry_label,
            cgroup_steps,
            |files_to_check| {
                let ctx = Arc::clone(&env.ctx);
                let check_info = server_check_utils::get_check_info(
                    &server_env::init_telemetry::get_reason(&init_telemetry),
                    true,
                    server_env::discard_warnings(&env),
                    genv,
                    &env,
                );
                let typing_check_service::Result { diagnostics: errorl, .. } = typing_check_service::go(
                    &ctx,
                    crate::telemetry::create(),
                    &files_to_check,
                    &check_info,
                    env.init_env.mergebase_warning_hashes.clone(),
                );
                errorl
            },
        );
        let env = Env {
            diagnostics: diagnostics::merge(errorl, env.diagnostics),
            ..env
        };
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

/// The check-mode branch of [`defer_or_do_type_check`] with the type check
/// `type_check` of the files (which `hh_server --check` does its own way):
/// the filter of the files, the cgroup step, the progress and the log lines
/// around `type_check`, and [`log_type_check_end`].
pub fn do_type_check_with<R>(
    enable_type_check_filter_files: bool,
    files_to_check: Vec<relative_path::T>,
    t: f64,
    telemetry_label: &str,
    cgroup_steps: &cgroup_profiler::StepGroup,
    type_check: impl FnOnce(Vec<relative_path::T>) -> R,
) -> (R, f64) {
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
    let files_to_check: Vec<relative_path::T> = if !enable_type_check_filter_files {
        files_to_check
    } else {
        let files_to_check_set: RPSet = files_to_check.into_iter().collect();
        let filtered_check =
            server_check_utils::user_filter_type_check_files(&files_to_check_set, &RPSet::new());
        filtered_check.into_iter().collect()
    };
    let _new_t: f64 = hh_logger::log_duration(None, None, &logstring, t);
    let total_rechecked_count = files_to_check.len();
    let logstring = format!("type-check {} files", total_rechecked_count);
    hh_logger::log(&format!("Begin {}", logstring));
    let rust_disk_provider_read_start = server_env::rust_disk_provider_read_telemetry::get_totals();
    let r = cgroup_profiler::step_start_end(cgroup_steps, None, telemetry_label, || {
        type_check(files_to_check)
    });
    log_type_check_end(&rust_disk_provider_read_start);
    let t = hh_logger::log_duration(None, None, &logstring, t);
    (r, t)
}
