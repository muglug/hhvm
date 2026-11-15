// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_type_check.ml`: one recheck (`indexing`,
//! `do_naming`, `do_redecl`, `do_type_checking`, `type_check_core`,
//! `type_check`).
//!
//! # Threads, the `Ctx` and the per-thread caches
//!
//! Everything here runs on the world thread: it alone changes
//! the naming tables and the decl stores of `env.ctx`, between the parallel
//! phases (parsing in `Direct_decl_service.go`, comparison in
//! `Decl_redecl_service`, typing in `Typing_check_service`). Where the
//! OCaml's processes would see the new contents of the shared heaps, the
//! threads are told with the decl epoch (`crate::rt::decl_epoch`): bumped
//! once the changed files are forgotten (`indexing`: their per-thread ASTs, file
//! contents and fixmes must not be reused), and again once naming and
//! redecl changed the decls, when the `Ctx` also gets a new generation
//! (`Ctx::next_generation`, installed as the context of the providers) so
//! that the caches keyed by its identity start afresh.
//!
//! # Not ported (no counterpart or no-ops in the open-source build)
//!
//! `Hack_event_logger` calls, `Measure` statistics (only with `hh_log_level > 0`),
//! `Server_revision_tracker` (its queries come from the `Active` informant,
//! which is not ported: with the `Resigned` one its three calls do
//! nothing), `Server_invalidate_units.go` (a stub in the open-source
//! build), distc (`use_distc`: the typing service has no distc). The
//! telemetry keys whose values come from unported functions (`gc`, `proc`,
//! `errors`, `repo_states`, `shmem`) are left out; the telemetry
//! goes nowhere but the errors file's `Complete` sentinel and the logs.

use std::sync::Arc;

use crate::decl_compare::versioned_names;
use crate::decl_redecl_service;
use crate::diagnostics;
use crate::direct_decl_service;
use crate::file_info;
use crate::hh_logger;
use crate::naming_global;
use crate::naming_table;
use crate::provider_context;
use crate::relative_path;
use crate::rt::decl_epoch;
use crate::rt::ocaml_unix::gettimeofday;
use crate::s_set;
use crate::server_args;
use crate::server_check_utils;
use crate::server_env;
use crate::server_env::Env;
use crate::server_env::FullCheckStatus;
use crate::server_env::Genv;
use crate::server_incremental;
use crate::server_prechecked_files;
use crate::server_progress;
use crate::server_progress::errors_write;
use crate::telemetry;
use crate::typing_check_service;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;

type RPSet = crate::relative_path::set::T;
type RPMap<A> = crate::relative_path::map::T<A>;
type Diag = crate::diagnostics::T;

/// `CheckStats.t`
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CheckStats {
    pub reparse_count: isize,
    pub total_rechecked_count: isize,
    /// This is either the duration to get the first error if any or until
    /// we get "typecheck done" status message.
    pub time_first_result: Option<server_env::SecondsSinceEpoch>,
}

impl CheckStats {
    /// Update field [time_first_result] if given timestamp is the
    /// first sent result.
    pub fn record_result_sent_ts(stats: CheckStats) -> CheckStats {
        CheckStats {
            time_first_result: stats.time_first_result.or(Some(gettimeofday())),
            ..stats
        }
    }
}

/// `Multi_threaded_call.cancel_reason` (`timestamp` is only logged, and the
/// typing service does not give it).
#[derive(Clone, Debug, PartialEq)]
pub struct CancelReason {
    pub user_message: String,
    pub log_message: String,
}

/// Makes `ctx` the context of the providers (the decl store reads its
/// stores; the OCaml's providers read the global heaps), as the batch
/// check does (`check::check_root`). The per-thread cache of ASTs
/// (`LocalParserCache`, which the OCaml always fills) is off, as in the
/// batch check: a recheck reads each AST once, so the cache would only cost
/// memory and a copy of each AST; it never changes what is computed.
pub fn install_ctx(ctx: &Arc<crate::ctx::Ctx>) {
    crate::hh_single_type_check::install(ctx);
    crate::ast_provider::set_local_parser_cache_enabled(false);
}

/// `env` with the context of `Provider_utils.ctx_from_server_env env` (the
/// dependency mode of `env`), made the context of the providers. A context
/// that has no reverse naming table yet (a server that starts with an
/// empty naming table, as the OCaml's tests do, without
/// `Server_init.init`) gets an empty one: the OCaml's naming heap starts
/// empty.
pub fn with_ctx_of_env(env: Env) -> Env {
    let ctx = crate::provider_utils::ctx_from_server_env(&env);
    install_ctx(&ctx);
    Env { ctx, ..env }
}

/// We want add all the declarations that were present in a file *before*
/// the current modification. The scenario:
/// File foo.php was defining the class A.
/// The user gets rid of class A (in foo.php)
/// In general, the type-checker determines what must be re-declared or
/// re-typechecked, by comparing the old and the new type-definitions.
/// That's why we are adding the 'old' definitions to the file.
/// In this case, the redecl phase (typing/typing_redecl_service.ml) is going
/// to compare the 'old' definition of A with the new one. It will realize that
/// the new one is missing, and go ahead and retype everything that depends
/// on A.
/// Without a call to add_old_decls, the class A wouldn't appear anywhere,
/// and we wouldn't realize that we have to re-check the types that depend
/// on A.
fn add_old_decls(
    ctx: &provider_context::T,
    old_naming_table: &naming_table::T,
    old_names_per_file: &RPMap<file_info::old_names::T>,
    new_names_per_file: &RPMap<file_info::Names>,
) -> RPMap<versioned_names::T> {
    let add_old_names = |filename: &relative_path::T, new_names: &file_info::Names| {
        let old_names =
            // TODO(T298623016): Populate old hashes independently of remote fetching.
            if provider_context::get_tcopt(ctx).tco_remote_old_decl_fetching_include_non_class {
                match old_names_per_file.get(filename) {
                    None => file_info::old_names::empty(),
                    Some(old_names) => old_names.clone(),
                }
            } else {
                match naming_table::get_file_info(old_naming_table, filename) {
                    None => file_info::old_names::empty(),
                    Some(old_info) => {
                        file_info::old_names::of_names(&file_info::simplify(&old_info))
                    }
                }
            };
        versioned_names::T {
            old_names,
            new_names: new_names.clone(),
        }
    };
    new_names_per_file
        .iter()
        .map(|(filename, new_names)| (filename.clone(), add_old_names(filename, new_names)))
        .collect()
}

/// This pushes all [phase] errors in errors, that aren't in [files],
/// to the errors-file.
fn push_errors_outside_files_to_errors_file(errors: &Diag, files: &RPSet) {
    let typing_errors_not_in_files_to_check =
        diagnostics::fold_errors(Some(true), errors, vec![], |path, error, mut acc| {
            if files.contains(path) {
                acc
            } else {
                acc.push((path.clone(), error.clone()));
                acc
            }
        });
    // (The OCaml conses, so its list is in the reverse order of the fold.)
    let typing_errors_not_in_files_to_check: Vec<_> =
        typing_errors_not_in_files_to_check.into_iter().rev().collect();
    let typing_errors_not_in_files_to_check =
        diagnostics::from_file_diagnostic_list(typing_errors_not_in_files_to_check);
    errors_write::report(&typing_errors_not_in_files_to_check);
}

/// `indexing genv env to_check cgroup_steps`
fn indexing(genv: &Genv, env: Env, to_check: &RPSet, cgroup_steps: &crate::cgroup_profiler::StepGroup) -> (Env, RPMap<file_info::T>) {
    let _ = genv;
    // (The OCaml's heaps are shared; these are the world thread's own, and
    // the decl epoch tells the other threads to forget theirs.)
    crate::file_provider::file_heap::remove_batch(to_check);
    crate::ast_provider::remove_batch(to_check);
    crate::fixme_provider::remove_batch(&to_check.iter().cloned().collect());
    bump_decl_epoch();
    // `Shared_mem.GC.collect `gentle`
    crate::shared_mem::gc::collect(crate::shared_mem::gc::Effort::Gentle);
    let files: Vec<relative_path::T> = to_check.iter().cloned().collect();
    let ctx = Arc::clone(&env.ctx);
    // Not caching here, otherwise oldification done in redo_type_decl will
    // oldify the new version (and override the real old versions.
    let defs_per_file = crate::cgroup_profiler::step_start_end(cgroup_steps, None, "parsing", || {
        direct_decl_service::go(&ctx, &files, true, direct_decl_service::DirectDeclMode::Normal)
    });
    (env, defs_per_file)
}

/// `get_classes_from_old_and_new ~new_naming_table ~old_naming_table path`
fn get_classes_from_old_and_new(
    new_naming_table: &naming_table::T,
    old_naming_table: &naming_table::T,
    path: &relative_path::T,
) -> s_set::T {
    let classes = |t: &naming_table::T| -> s_set::T {
        match naming_table::get_file_info(t, path) {
            None => s_set::T::new(),
            Some(info) => info.ids.classes.iter().map(|id| id.name.clone()).collect(),
        }
    };
    let new_classes = classes(new_naming_table);
    let old_classes = classes(old_naming_table);
    new_classes.union(old_classes)
}

/// `naming_result`
struct NamingResult {
    failed_naming: RPSet,
    naming_table: naming_table::T,
    /// When hash tracking is enabled, has entries for each file
    /// [add_old_decls] may ask for. Empty when tracking is disabled.
    /// TODO(T298623016): Populate this independently of remote fetching.
    old_names_per_file: RPMap<file_info::old_names::T>,
    telemetry: telemetry::T,
}

/// Updates the naming_table, which is a map from filename to the names of
/// toplevel symbols declared in that file: at any given point in time, we want
/// to know what each file defines. The updated naming table is returned
/// in the return value.
/// Also runs [Naming_global.ndecl_file_and_get_conflict_files] which updates
/// the global reverse naming table.
/// When hash tracking is enabled, returns old names and winning declaration
/// hashes captured before these updates.
/// TODO(T298623016): Populate these hashes independently of remote fetching.
///
/// The "winner" in case of duplicate definitions? All filenames involved in any
/// duplicate definition were stored by the caller in [env.failed_parsing], and
/// the caller includes then in [defs_per_file_parsed]. We iterate over them
/// in alphabetical order. Thus, the winner definition will be the one from the
/// alphabetically first file. (Within a file, classes win over types, and
/// after that the lexically first definition wins).
///
/// Note that on the first typecheck after a duplicate definition has been introduced,
/// then [env.failed_parsing] doesn't yet contain all filenames involved, so the
/// winner in this first typecheck is non-determnistic -- it's simply previous
/// definition. We only get the alphabetically first filename as winner on subsequent
/// typechecks. Yuck.
fn do_naming(
    env: &Env,
    ctx: &Arc<crate::ctx::Ctx>,
    defs_per_file_parsed: &RPMap<file_info::T>,
    cgroup_steps: &crate::cgroup_profiler::StepGroup,
) -> NamingResult {
    let telemetry = telemetry::create();
    let start_t = gettimeofday();

    let old_names_per_file =
        // TODO(T298623016): Populate old hashes independently of remote fetching.
        if provider_context::get_tcopt(ctx).tco_remote_old_decl_fetching_include_non_class {
            server_incremental::get_old_names_batch(ctx, &env.naming_table, defs_per_file_parsed)
        } else {
            RPMap::new()
        };

    let count = defs_per_file_parsed.len() as isize;
    crate::cgroup_profiler::step_start_end(cgroup_steps, None, "naming", || {
    server_incremental::remove_defs_from_reverse_naming_table(
        ctx,
        &env.naming_table,
        defs_per_file_parsed,
    );
    let failed_naming = defs_per_file_parsed
        .iter()
        .fold(RPSet::new(), |failed, (file, fileinfo)| {
            let failed_ = naming_global::ndecl_file_and_get_conflict_files(ctx, file, &fileinfo.ids);
            failed_.union(failed)
        });
    let t2 = hh_logger::log_duration(None, None, "Declare_names (name->filename)", start_t);
    // Update filename->File_info.t forward naming table (into this local variable)
    let naming_table = naming_table::update_many(&env.naming_table, defs_per_file_parsed);
    // final telemetry
    let t3 = hh_logger::log_duration(None, None, "Update_many (filename->names)", t2);
    let heap_size = crate::shared_mem::sm_telemetry::heap_size() as isize;
    // (`Hack_event_logger.naming_end`: a no-op.)
    let telemetry = telemetry::float_("update_reverse_duration", t2 - start_t, telemetry);
    let telemetry = telemetry::float_("update_fwd_duration", t3 - t2, telemetry);
    let telemetry = telemetry::int_("end_heap_mb", heap_size, telemetry);
    let telemetry = telemetry::float_("total_duration", t3 - start_t, telemetry);
    let telemetry = telemetry::int_("count", count, telemetry);
    let telemetry = telemetry::int_("failed_naming_count", failed_naming.len() as isize, telemetry);
    NamingResult {
        failed_naming,
        naming_table,
        old_names_per_file,
        telemetry,
    }
    })
}

/// `redecl_result`
struct RedeclResult {
    changed: dep_set::T,
    to_recheck: RPSet,
    to_recheck_deps: dep_set::T,
    old_decl_missing_count: isize,
}

fn invoke_testing_hook_before_redecl(
    hooks: Option<&server_env::TypeCheckTestingHooks>,
    defs_per_file: &RPMap<versioned_names::T>,
) {
    if let Some(hooks) = hooks {
        (hooks.before_redecl)(defs_per_file)
    }
}

/// Oldify defs and compute files to recheck.
fn do_redecl(
    genv: &Genv,
    env: &Env,
    reparsed: &RPSet,
    defs_per_file: &RPMap<versioned_names::T>,
    naming_table: &naming_table::T,
    cgroup_steps: &crate::cgroup_profiler::StepGroup,
) -> RedeclResult {
    invoke_testing_hook_before_redecl(env.type_check_testing_hooks.as_deref(), defs_per_file);
    let old_naming_table = &env.naming_table;
    let get_classes =
        |path: &relative_path::T| get_classes_from_old_and_new(naming_table, old_naming_table, path);
    let bucket_size = genv.local_config.type_decl_bucket_size;
    let ctx = Arc::clone(&env.ctx);
    let decl_redecl_service::RedoTypeDeclResult {
        old_decl_missing_count,
        fanout,
    } = crate::cgroup_profiler::step_start_end(cgroup_steps, None, "redecl", || {
        decl_redecl_service::redo_type_decl(
            &ctx,
            false,
            env.type_check_testing_hooks.as_deref(),
            bucket_size,
            &get_classes,
            &file_info::empty_names(),
            defs_per_file,
        )
    });
    let to_recheck =
        server_incremental::get_files_to_recheck(&ctx, env, &fanout, reparsed, &env.diagnostics);
    RedeclResult {
        changed: fanout.changed,
        to_recheck,
        to_recheck_deps: fanout.to_recheck,
        old_decl_missing_count,
    }
}

/// `type_checking_result`
struct TypeCheckingResult {
    env: Env,
    diagnostics: Diag,
    telemetry: telemetry::T,
    files_checked: RPSet,
    #[allow(dead_code)]
    full_check_done: bool,
    needs_recheck: RPSet,
    total_rechecked_count: isize,
    time_first_typing_error: Option<server_env::Seconds>,
    cancel_reason: Option<CancelReason>,
}

fn do_type_checking(
    genv: &Genv,
    env: Env,
    diagnostics: Diag,
    files_to_check: &RPSet,
    lazy_check_later: &RPSet,
    check_reason: &str,
    files_with_naming_errors: &RPSet,
    cgroup_steps: &crate::cgroup_profiler::StepGroup,
) -> TypeCheckingResult {
    let _ = files_with_naming_errors;
    let telemetry = telemetry::create();
    if files_to_check.contains(&relative_path::DEFAULT) {
        hh_logger::log("WARNING: rechecking definition in a dummy file");
    }
    // (`hh_distc_config`: no distc; `longlived_workers`: no workers.)
    let ctx = Arc::clone(&env.ctx);
    let check_info = {
        let during_init = env.init_env.why_needed_full_check.is_some();
        server_check_utils::get_check_info(
            check_reason,
            true,
            during_init && server_env::discard_warnings(&env),
            genv,
            &env,
        )
    };
    let files: Vec<relative_path::T> = files_to_check.iter().cloned().collect();
    // `get_interrupt_config genv env`
    let handlers = (env.interrupt_handlers)(genv, &env);
    let warnings_saved_state = env.init_env.mergebase_warning_hashes.clone();
    let type_check_testing_hooks = env.type_check_testing_hooks.clone();
    let interrupt = typing_check_service::InterruptConfig { env, handlers };
    let mut cgroup_typecheck_telemetry = None;
    let typecheck_with_prefetch = || {
        let root = server_args::root(&genv.options);
        let typecheck = || {
            typing_check_service::go_with_interrupt(
                &ctx,
                telemetry,
                &files,
                interrupt,
                &check_info,
                type_check_testing_hooks.as_deref(),
                warnings_saved_state,
            )
        };
        if genv.local_config.eden_prefetch_enabled
            && files_to_check.len() as isize >= genv.local_config.eden_prefetch_fanout_threshold
        {
            let (result, telemetry) = crate::edenfs_prefetch::with_prefetch(
                &root,
                files_to_check,
                genv.local_config.eden_prefetch_workers,
                typecheck,
            );
            (result, Some(telemetry))
        } else {
            (typecheck(), None)
        }
    };
    let (((env, typing_result), cancelled), prefetch_telemetry) =
        crate::cgroup_profiler::step_start_end(
            cgroup_steps,
            Some(&mut cgroup_typecheck_telemetry),
            "type check",
            typecheck_with_prefetch,
        );
    let typing_check_service::Result {
        diagnostics: errorl_,
        warnings_saved_state: mergebase_warning_hashes,
        telemetry,
    } = typing_result;
    let telemetry = match prefetch_telemetry {
        None => telemetry,
        Some(prefetch) => telemetry::object_("edenfs_prefetch", prefetch, telemetry),
    };
    // (`time_first_error`: the typing service does not give it.)
    let time_first_typing_error = None;
    let env = Env {
        init_env: server_env::InitEnv {
            mergebase_warning_hashes,
            ..env.init_env.clone()
        },
        ..env
    };
    let telemetry = telemetry::object_opt("cgroup", cgroup_typecheck_telemetry, telemetry);
    // (`gc`, `proc`: no counterpart.)
    let files_checked = files_to_check.clone();
    // Add new things that need to be rechecked
    let needs_recheck = env.needs_recheck.clone().union(lazy_check_later.clone());
    // Remove things that were cancelled from things we started rechecking...
    let (cancelled, cancel_reason) = match cancelled {
        None => (vec![], None),
        Some((unfinished, (user_message, log_message))) => (
            unfinished,
            Some(CancelReason {
                user_message,
                log_message,
            }),
        ),
    };
    let (files_checked, needs_recheck) = cancelled.into_iter().fold(
        (files_checked, needs_recheck),
        |(mut files_checked, mut needs_recheck), path| {
            files_checked.remove(&path);
            needs_recheck.insert(path);
            (files_checked, needs_recheck)
        },
    );
    // ... leaving only things that we actually checked, and which can be
    // removed from needs_recheck
    let needs_recheck = needs_recheck.relative_complement(files_checked.clone());
    // Here we do errors paradigm (1) env.diagnostics: merge in typecheck results, to flow into [env.diagnostics].
    // As for paradigms (2) persistent-connection and (3) errors-file, they're handled
    // inside [Typing_check_service.go_with_interrupt] because they want to push errors
    // as soon as they're discovered.
    let rechecked: std::collections::BTreeSet<relative_path::T> =
        files_checked.iter().cloned().collect();
    let diagnostics = diagnostics::incremental_update(diagnostics, errorl_, &rechecked);
    let full_check_done = needs_recheck.is_empty();
    let total_rechecked_count = files_checked.len() as isize;
    TypeCheckingResult {
        env,
        diagnostics,
        telemetry,
        files_checked,
        full_check_done,
        needs_recheck,
        total_rechecked_count,
        time_first_typing_error,
        cancel_reason,
    }
}

/// `invoke_testing_hook_after_indexing hooks`
fn invoke_testing_hook_after_indexing(hooks: Option<&server_env::TypeCheckTestingHooks>) {
    if let Some(hooks) = hooks {
        (hooks.after_indexing)()
    }
}

/// `quantile ~index ~count files`
fn quantile(index: isize, count: isize, files: &RPSet) -> RPSet {
    let file_count_in_quantile = files.len() as isize / count;
    let (file_count_in_quantile, index) = if file_count_in_quantile == 0 {
        let count = files.len() as isize;
        let file_count_in_quantile = 1;
        let index = if index >= count { count - 1 } else { index };
        (file_count_in_quantile, index)
    } else {
        (file_count_in_quantile, index)
    };
    // Work with BigList-s the same way Typing_check_service does, to preserve
    // the same typechecking order within the quantile.
    let files: Vec<relative_path::T> = files.iter().cloned().collect();
    let n = file_count_in_quantile.max(0) as usize;
    let start = (index.max(0) as usize).saturating_mul(n).min(files.len());
    let end = start.saturating_add(n).min(files.len());
    files[start..end].iter().cloned().collect()
}

/// `Random.bits ()`: 30 random bits (as `random_id`'s, from the randomly
/// seeded hasher of the standard library).
fn random_bits() -> isize {
    use std::hash::BuildHasher;
    use std::hash::Hasher;
    let mut hasher = std::collections::hash_map::RandomState::new().build_hasher();
    hasher.write_u64(gettimeofday().to_bits());
    (hasher.finish() & 0x3FFF_FFFF) as isize
}

/// The decl epoch moves; the world thread forgets its own memos at once
/// (the threads of the pool do at their next unit of work).
pub(crate) fn bump_decl_epoch() {
    decl_epoch::bump();
    decl_epoch::sync_thread();
}

/// The decls changed (naming and redecl): a new generation of the context,
/// made the context of the providers, and the decl epoch moved, so that no
/// thread reuses what it cached of the previous decls.
fn new_ctx_generation(env: Env) -> Env {
    let ctx = env.ctx.next_generation();
    install_ctx(&ctx);
    bump_decl_epoch();
    Env { ctx, ..env }
}

/// `type_check_core ?agent_session_id genv env start_time ~check_reason
/// cgroup_steps` (`agent_session_id` goes to `Hack_event_logger.type_check_end`,
/// a no-op.)
fn type_check_core(
    agent_session_id: Option<&str>,
    genv: &Genv,
    env: Env,
    start_time: f64,
    check_reason: &str,
    cgroup_steps: &crate::cgroup_profiler::StepGroup,
) -> (Env, CheckStats, telemetry::T, Option<CancelReason>) {
    let _ = agent_session_id;
    let rust_disk_provider_read_start = server_env::rust_disk_provider_read_telemetry::get_totals();
    let t = gettimeofday();
    // `start_time` is when the recheck_loop started and includes preliminaries like
    // reading about file-change notifications and communicating with client.
    // We record all our telemetry uniformally with respect to this start.
    // `t` is legacy, used for ad-hoc duration reporting within this function.
    // For the following, env.int_env.why_needed_full_check is set to Some by
    // ServerLazyInit, and we include it here, and then it's subsequently
    // set to None at the end of this method in the "wrap up" section.
    // Thus, if it's present here, it means the typecheck we're about to do is
    // the initial one of a lazy init.
    let telemetry = telemetry::object_opt(
        "init",
        env.init_env
            .why_needed_full_check
            .as_ref()
            .map(server_env::init_telemetry::get),
        telemetry::create(),
    );
    let time_first_error: Option<f64> = None;
    let env = with_ctx_of_env(env);
    if !env.ctx.has_reverse_naming_table() {
        env.ctx.build_reverse_naming_table();
    }
    let do_errors_file = genv.local_config.produce_streaming_errors;
    let env = Env {
        full_check_status: FullCheckStatus::FullCheckStarted,
        ..env
    };
    let files_to_parse = env.disk_needs_parsing.clone();
    // We need to do naming phase for files that failed naming in a previous cycle.
    // "Failed_naming" comes from duplicate name errors; the idea is that a change
    // deletes one of the duplicates, well, this change should cause us to re-parse
    // and re-process the remaining duplicate so it can be properly recorded in the
    // forward and reverse naming tables (even though the remaining duplicate
    // didn't itself change).
    if !env.failed_naming.is_empty() {
        hh_logger::log(&format!(
            "Also reparsing these files with failed naming: {}",
            env.failed_naming
                .iter()
                .map(relative_path::suffix)
                .collect::<Vec<_>>()
                .join(" ")
        ));
    }
    let files_to_parse = files_to_parse.union(env.failed_naming.clone());

    let reparse_count = files_to_parse.len() as isize;
    if reparse_count == 1 {
        // (`Relative_path.Set.choose`: the smallest element.)
        let file = files_to_parse.get_min().unwrap();
        hh_logger::log(&format!(
            "Processing changes to 1 file: {}",
            relative_path::to_absolute(file)
        ));
    } else {
        hh_logger::log(&format!("Processing changes to {} files", reparse_count));
    }

    let check_count = env.needs_recheck.len() as isize;
    hh_logger::log(&format!(
        "Processing deferred typechecking for {} file(s)",
        check_count
    ));
    let telemetry = telemetry::int_("check_count", check_count, telemetry);

    // PARSING ***************************************************************
    server_progress::write(
        Some(false),
        None,
        &format!("parsing {} files", reparse_count),
    );
    let logstring = format!("Parsing {} files", reparse_count);
    hh_logger::log(&format!("Begin {}", logstring));

    // Parse all changed files. This clears the file contents cache prior
    // to parsing.
    let telemetry = telemetry::duration(Some("parse_start"), start_time, None, telemetry);
    let diagnostics = env.diagnostics.clone();
    let (env, defs_per_file_parsed) = indexing(genv, env, &files_to_parse, cgroup_steps);
    invoke_testing_hook_after_indexing(env.type_check_testing_hooks.as_deref());

    let hs = crate::shared_mem::sm_telemetry::heap_size() as isize;
    let telemetry = telemetry::duration(Some("parse_end"), start_time, None, telemetry);
    let telemetry = telemetry::int_("parse_end_heap_size", hs, telemetry);
    let telemetry = telemetry::int_("parse_count", reparse_count, telemetry);
    // (`Hack_event_logger.parsing_end_for_typecheck`: a no-op.)
    let t = hh_logger::log_duration(None, None, &logstring, t);

    // UPDATE NAMING TABLES **************************************************
    server_progress::write(Some(false), None, "updating naming tables");
    let logstring = "updating naming tables";
    hh_logger::log(&format!("Begin {}", logstring));
    let telemetry = telemetry::duration(Some("naming_start"), start_time, None, telemetry);
    let ctx = Arc::clone(&env.ctx);
    // Note: although do_naming updates global reverse-naming-table maps,
    // the updated forward-naming-table "naming_table" only gets assigned
    // into env.naming_table later on
    let NamingResult {
        failed_naming,
        naming_table,
        old_names_per_file,
        telemetry: naming_telemetry,
    } = do_naming(&env, &ctx, &defs_per_file_parsed, cgroup_steps);
    let t = hh_logger::log_duration(None, None, logstring, t);
    let telemetry = telemetry::duration(Some("naming_end"), start_time, None, telemetry);
    let telemetry = telemetry::object_("naming", naming_telemetry, telemetry);

    // REDECL PHASE 1 ********************************************************
    // The things we redecl `defs_per_file` come from the current content of
    // files changed `defs_per_files_parsed`, plus the previous content `add_old_decls`,
    // plus those that had duplicate names `failed_naming`
    server_progress::write(None, None, "determining changes");
    let deptable_unlocked = typing_deps::allow_dependency_table_reads(&env.deps_mode, true);

    hh_logger::log("(Recomputing type declarations in relation to naming)");
    // failed_naming can be a superset of keys in defs_per_file - see comment in Naming_global.ndecl_file
    // The term [defs_per_file] doesn't mean anything. It's just exactly the same as defs_per_file_parsed,
    // that is a filename->File_info.t map of the files we just parsed,
    // except it's just filename->File_info.names -- i.e. purely the names, without positions.
    let defs_per_file = naming_table::to_defs_per_file(
        &naming_table::create(defs_per_file_parsed.clone()),
        None,
    );
    let defs_per_file =
        server_check_utils::extend_defs_per_file(genv, defs_per_file, &naming_table, &failed_naming);
    let defs_per_file =
        add_old_decls(&ctx, &env.naming_table, &old_names_per_file, &defs_per_file);

    let count = defs_per_file.len() as isize;
    let logstring = format!("Type declaration for {} files", count);
    hh_logger::log(&format!("Begin {}", logstring));
    hh_logger::log(
        "(Recomputing type declarations in changed files and determining immediate typechecking fanout)",
    );
    let telemetry = telemetry::duration(Some("redecl_start"), start_time, None, telemetry);
    let telemetry = telemetry::int_("redecl_file_count", count, telemetry);

    // Compute fanout. Here we compare the old and new versions of
    // the declarations defined in all changed files, and collect the set of
    // files which need to be re-typechecked as a consequence of those changes.
    let reparsed = files_to_parse;
    let RedeclResult {
        changed,
        to_recheck,
        to_recheck_deps,
        old_decl_missing_count,
    } = do_redecl(genv, &env, &reparsed, &defs_per_file, &naming_table, cgroup_steps);
    let telemetry = telemetry::int_("old_decl_missing_count", old_decl_missing_count, telemetry);

    let hs = crate::shared_mem::sm_telemetry::heap_size() as isize;
    // (`Hack_event_logger.first_redecl_end`: a no-op.)
    let t = hh_logger::log_duration(None, None, &logstring, t);
    let telemetry = telemetry::duration(Some("redecl_end"), start_time, None, telemetry);
    let telemetry = telemetry::int_("redecl_end_heap_size", hs, telemetry);

    let telemetry =
        telemetry::duration(Some("revtrack_decl_changed_end"), start_time, None, telemetry);

    // (`Server_revision_tracker.typing_changed`: see the module documentation.)

    // we use lazy here to avoid expensive string generation when logging
    // is not enabled
    let max = 1000;
    hh_logger::level::log_lazy(
        hh_logger::level::T::Info,
        Some("fanout_tests"),
        None,
        || {
            use crate::yojson::safe as yojson;
            yojson::to_string(&yojson::T::Assoc(vec![
                (
                    "tag".to_string(),
                    yojson::T::String("incremental_fanout".to_string()),
                ),
                (
                    "hashes".to_string(),
                    yojson::T::List(
                        to_recheck_deps
                            .iter()
                            .take(max)
                            .map(|d| yojson::T::String(dep::to_hex_string(*d)))
                            .collect(),
                    ),
                ),
                (
                    "hashes_was_truncated".to_string(),
                    yojson::T::Bool(to_recheck_deps.len() > max),
                ),
                (
                    "files".to_string(),
                    yojson::T::List(
                        to_recheck
                            .iter()
                            .take(max)
                            .map(|p| yojson::T::String(relative_path::suffix(p)))
                            .collect(),
                    ),
                ),
                (
                    "files_was_truncated".to_string(),
                    yojson::T::Bool(to_recheck.len() > max),
                ),
            ]))
        },
    );

    // Here's where we update the forward-naming-table in [env]
    let env = Env {
        naming_table,
        failed_naming,
        disk_needs_parsing: RPSet::new(),
        ..env
    };
    // The decls changed: the threads must not reuse what they cached of
    // the previous ones.
    let env = new_ctx_generation(env);
    let ctx = Arc::clone(&env.ctx);
    // HANDLE PRECHECKED FILES AFTER LOCAL CHANGES ***************************
    server_progress::write(None, None, "determining trunk changes");
    hh_logger::log("Begin evaluating prechecked changes");
    let telemetry = telemetry::duration(Some("prechecked1_start"), start_time, None, telemetry);

    let (env, prechecked1_telemetry) =
        server_prechecked_files::update_after_local_changes(genv, env, &changed, start_time);

    let t = hh_logger::log_duration(None, None, "Evaluating prechecked changes", t);
    let telemetry = telemetry::duration(Some("prechecked1_end"), start_time, None, telemetry);
    let telemetry = telemetry::object_("prechecked1", prechecked1_telemetry, telemetry);
    let telemetry = telemetry::int_("prechecked1_changed", changed.len() as isize, telemetry);

    let _: bool = typing_deps::allow_dependency_table_reads(&env.deps_mode, deptable_unlocked);

    // Checking this before starting typechecking because we want to attribute
    // big rechecks to rebases, even when restarting is disabled
    // (`Server_revision_tracker.check_blocking` when
    // `hg_aware_recheck_restart_threshold = 0`: see the module documentation.)
    let telemetry = telemetry::duration(
        Some("revtrack3_check_blocking_end"),
        start_time,
        None,
        telemetry,
    );

    // TYPE CHECKING *********************************************************
    // The things we recheck are those from the fanout `do_redecl().fanout` plus every file
    // whose error reasons were in changed files.
    let _type_check_start_t = gettimeofday();
    server_progress::write(None, None, "typechecking");

    // For a full check, typecheck everything which may be affected by the
    // changes. For a lazy check, typecheck only the affected files which are
    // open in the IDE, leaving other affected files to be lazily checked later.
    // In either case, don't attempt to typecheck files with parse errors.
    let enable_type_check_filter_files = genv.local_config.enable_type_check_filter_files;
    let lazy_check_later = RPSet::new();
    // If the user has enabled a custom file filter, we want to only
    // type check files that pass the filter
    let to_recheck = if enable_type_check_filter_files {
        server_check_utils::user_filter_type_check_files(&to_recheck, &reparsed)
    } else {
        to_recheck
    };
    let to_recheck = env.needs_recheck.clone().union(to_recheck);
    let to_recheck: RPSet = defs_per_file.keys().cloned().collect::<RPSet>().union(to_recheck);

    server_progress::write(
        None,
        None,
        &format!("typechecking {} files", to_recheck.len()),
    );

    let to_recheck = match &genv.local_config.workload_quantile {
        None => to_recheck,
        Some(crate::server_local_config::Quantile { index, count }) => {
            let to_recheck = quantile(*index, *count, &to_recheck);
            hh_logger::log(&format!(
                "Will typecheck {}-th {}-quantile only, containing {} files.",
                index,
                count,
                to_recheck.len()
            ));
            to_recheck
        }
    };

    // The errors file must accumulate ALL errors. The call below to [do_type_checking ~files_to_check]
    // will report all errors in [files_to_check].
    // But there might be other errors in [env.diagnostics] from a previous round of typecheck,
    // but which aren't in the current fanout i.e. not in [files_to_check]. We must report those too.
    // It remains open for discussion whether the user-experience would be better to have these
    // not-in-fanout errors reported here before the typecheck starts, or later after the typecheck
    // has finished. We'll report them here for now.
    if do_errors_file {
        push_errors_outside_files_to_errors_file(&diagnostics, &to_recheck);
    }
    // And what about the files in [files_to_check] which we were going to typecheck but then
    // the typecheck got interrupted  and they were returned from [do_typechecking] as [needs_recheck]?
    // Shouldn't we report those too into the errors-file? Well, there's no need to bother:
    // if there's anything in [needs_recheck] then the current errors-file will be marked as "incomplete"
    // and another round of ServerTypeCheck (hence another errors-file) will be created next.
    let to_recheck_count = to_recheck.len() as isize;
    // The intent of capturing the snapshot here is to increase the likelihood
    // of the state-on-disk being the same as what the parser saw
    hh_logger::log(&format!("Begin typechecking {} files.", to_recheck_count));
    if do_errors_file {
        errors_write::telemetry(&telemetry::int_(
            "to_recheck_count",
            to_recheck_count,
            telemetry::create(),
        ));
    }

    let telemetry = telemetry::duration(Some("typecheck_start"), start_time, None, telemetry);
    // Typecheck all of the files we determined might need rechecking as a
    // consequence of the changes (or, in a lazy check,
    // the subset of those
    // files which are open in an IDE buffer).
    let failed_naming = env.failed_naming.clone();
    let TypeCheckingResult {
        env,
        diagnostics,
        telemetry: typecheck_telemetry,
        files_checked,
        full_check_done: _,
        needs_recheck,
        total_rechecked_count,
        time_first_typing_error,
        cancel_reason,
    } = do_type_checking(
        genv,
        env,
        diagnostics,
        &to_recheck,
        &lazy_check_later,
        check_reason,
        &failed_naming,
        cgroup_steps,
    );
    let time_first_error = time_first_error.or(time_first_typing_error);

    let heap_size = crate::shared_mem::sm_telemetry::heap_size() as isize;

    server_progress::write(None, None, "typecheck ending");
    let logstring = format!(
        "Typechecked {} files [{} errors]",
        total_rechecked_count,
        diagnostics::count(None, &diagnostics)
    );
    let t = hh_logger::log_duration(None, None, &logstring, t);
    hh_logger::log(&format!(
        "Total: {}\n",
        crate::rt::ocaml_printf::sprintf_f(6, t - start_time)
    ));

    let telemetry = telemetry::duration(Some("typecheck_end"), start_time, None, telemetry);
    let telemetry = telemetry::object_("typecheck", typecheck_telemetry, telemetry);
    let telemetry = telemetry::object_(
        "hash",
        crate::server_utils::log_and_get_sharedmem_load_telemetry(),
        telemetry,
    );
    let telemetry = telemetry::int_opt(
        "depgraph_delta_num_edges",
        typing_deps::telemetry::depgraph_delta_num_edges(&crate::provider_context::get_deps_mode(
            &ctx,
        )),
        telemetry,
    );
    let telemetry = telemetry::int_("typecheck_heap_size", heap_size, telemetry);
    let telemetry = telemetry::int_("typecheck_to_recheck_count", to_recheck_count, telemetry);
    let telemetry = telemetry::int_(
        "typecheck_total_rechecked_count",
        total_rechecked_count,
        telemetry,
    );
    let telemetry = telemetry::int_(
        "typecheck_files_checked",
        files_checked.len() as isize,
        telemetry,
    );
    let telemetry = telemetry::int_(
        "typecheck_lazy_check_later_count",
        lazy_check_later.len() as isize,
        telemetry,
    );
    let telemetry = telemetry::bool_(
        "enable_type_check_filter_files",
        genv.local_config.enable_type_check_filter_files,
        telemetry,
    );
    let telemetry = telemetry::bool_(
        "typecheck_longlived_workers",
        genv.local_config.longlived_workers,
        telemetry,
    );
    let telemetry = telemetry::string_opt(
        None,
        "cancel_reason",
        cancel_reason.as_ref().map(|r| r.user_message.as_str()),
        telemetry,
    );
    let telemetry = telemetry::string_opt(
        None,
        "cancel_details",
        cancel_reason.as_ref().map(|r| r.log_message.as_str()),
        telemetry,
    );

    // INVALIDATE FILES (EXPERIMENTAL TYPES IN CODEGEN) **********************
    // (`Server_invalidate_units.go`: a stub in the open-source build.)

    let telemetry = telemetry::duration(Some("invalidate_end"), start_time, None, telemetry);

    // WRAP-UP ***************************************************************
    let needs_recheck = if genv.local_config.workload_quantile.is_some() {
        // If we were typechecking quantiles only, then artificially assume that everything
        // was typechecked. Otherwise the next recheck iteration will keep typechecking the other
        // quantiles.
        RPSet::new()
    } else {
        needs_recheck
    };
    let full_check_status = if needs_recheck.is_empty() {
        // TODO(frankemrich) It's surprising that we do not look at env.disk_needs_parsing here as
        // well:  The latter may be added to by the interrupt handlers and is not necessarily empty
        // here. Revisit this once ServerPrecheckedFiles is gone, and it becomes easier to lock down
        // the intended semantics of Full_check_done
        FullCheckStatus::FullCheckDone
    } else {
        env.full_check_status
    };
    let why_needed_full_check = match &env.init_env.why_needed_full_check {
        None => None,
        Some(why_needed_full_check) => {
            if server_env::is_full_check_done(full_check_status) {
                None
            } else {
                Some(why_needed_full_check.clone())
            }
        }
    };
    let init_env = server_env::InitEnv {
        why_needed_full_check,
        ..env.init_env.clone()
    };
    let env = Env {
        diagnostics,
        needs_recheck,
        full_check_status,
        init_env,
        ..env
    };

    // STATS LOGGING *********************************************************
    // (`Measure.print_stats`, `shmem`: only with `hh_log_level > 0`, which
    // has no counterpart.)
    // (`errors`, `repo_states`: see the module documentation.)

    // HANDLE PRECHECKED FILES AFTER RECHECK *********************************
    let telemetry = telemetry::duration(Some("prechecked2_start"), start_time, None, telemetry);
    let deptable_unlocked = typing_deps::allow_dependency_table_reads(&env.deps_mode, true);
    let (env, prechecked2_telemetry) =
        server_prechecked_files::update_after_recheck(genv, env, &files_checked, start_time);
    let _: bool = typing_deps::allow_dependency_table_reads(&env.deps_mode, deptable_unlocked);
    let telemetry = telemetry::duration(Some("prechecked2_end"), start_time, None, telemetry);
    let telemetry = telemetry::object_("prechecked2", prechecked2_telemetry, telemetry);

    // We might have completed a full check, which might mean that a rebase was
    // successfully processed.
    // (`Server_revision_tracker.check_non_blocking`: see the module
    // documentation.)
    let telemetry = telemetry::duration(
        Some("revtrack4_check_non_blocking_end"),
        start_time,
        None,
        telemetry,
    );

    let telemetry = telemetry::duration(Some("stop_typing_service"), start_time, None, telemetry);

    // We create an ID for the TYPE_CHECK_END event so we can join the server
    // events table with the errors table
    let type_check_end_id = random_bits();
    let telemetry = telemetry::int_("type_check_end_id", type_check_end_id, telemetry);
    let telemetry = telemetry::object_(
        "rust_disk_provider_read",
        server_env::rust_disk_provider_read_telemetry::get_delta_telemetry(
            &rust_disk_provider_read_start,
        ),
        telemetry,
    );

    // CAUTION! Lots of alerts/dashboards depend on this event, particularly start_t
    // (`Hack_event_logger.type_check_end ?agent_session_id`,
    // `TypingErrors.log_errors`: no-ops.)
    (
        env,
        CheckStats {
            reparse_count,
            total_rechecked_count,
            time_first_result: time_first_error,
        },
        telemetry,
        cancel_reason,
    )
}

/// `type_check_unsafe ?agent_session_id genv env start_time profiling`
fn type_check_unsafe(
    agent_session_id: Option<&str>,
    genv: &Genv,
    env: Env,
    start_time: f64,
    cgroup_steps: &crate::cgroup_profiler::StepGroup,
) -> (Env, CheckStats, telemetry::T, Option<CancelReason>) {
    let check_kind = "Full_check";
    let check_reason = match &env.init_env.why_needed_full_check {
        Some(init_telemetry) => server_env::init_telemetry::get_reason(init_telemetry),
        None => "incremental".to_string(),
    };
    let telemetry = telemetry::create();
    let telemetry = telemetry::string_(None, "kind", check_kind, telemetry);
    let telemetry = telemetry::duration(Some("start"), start_time, None, telemetry);

    // CAUTION! Lots of alerts/dashboards depend on the exact string of check_kind and check_reason
    // (`Hack_event_logger.with_check_kind`: no-op.)
    hh_logger::log("******************************************");
    hh_logger::log(&format!(
        "Check kind: will bring hh_server to consistency with code changes, by checking whatever fanout is needed ('{}')",
        check_kind
    ));
    let telemetry = telemetry::duration(Some("core_start"), start_time, None, telemetry);

    let (env, stats, core_telemetry, cancel_reason) =
        type_check_core(agent_session_id, genv, env, start_time, &check_reason, cgroup_steps);

    let telemetry = telemetry::duration(Some("core_end"), start_time, None, telemetry);
    let telemetry = telemetry::object_("core", core_telemetry, telemetry);
    let stats = CheckStats::record_result_sent_ts(stats);
    let telemetry = telemetry::duration(Some("sent_done"), start_time, None, telemetry);
    (env, stats, telemetry, cancel_reason)
}

/// `type_check ?agent_session_id genv env start_time cgroup_steps`
///
/// (1) THE ENV MODEL FOR DIAGNOSTICS...
/// env.{diagnostics, needs_recheck, disk_needs_parsing} are all persistent values that
/// might be adjusted as we go:
/// * disk_needs_parsing gets initialized in serverLazyInit, augmented in server_main both
///   at the start of the loop and during file watcher interrupts, and in serverTypeCheck it
///   gets reset to empty once we have computed files-to-parse and decls-to-refresh from it.
///   (files-to-recheck is computed from these two).
/// * needs_recheck gets augmented in serverTypeCheck from fanout/stale computation,
///   and gets discharged by the files we end up typechecking
/// * diagnostics starts out empty and it grows+shrinks during serverTypeCheck
///   through calls to "diagnostics = Diagnostics.incremental_update ~diagnostics ~new_errors ~phase ~files_examined".
///   This will shrink those diagnostics that had been in diagnostics before, and were in files_examined,
///   but are not in new_errors. It will replace others. It will grow others.
///   And it will leave remaining in diagnostics anything that was not touched by files_examined
///   or which came from a different phase.
///
/// (3) THE STREAMING MODEL FOR ERRORS...
/// The errors-file grows monotonically: it has no "backsies", no way to remove an error
/// from it, short of deciding that the current errors-file is wrong and a new error-file must
/// be restarted.
/// * Hh_server, upon startup, must eventually produce an errors-file.
/// * Right here at the start of the type check, we restart the errors-file (because of the
///   potential that in the current typecheck we discover that some files no longer have errors).
/// * The typecheck fulfills the contract that every single error must be reported to the errors-file.
///   Not just newly discovered errors. Every error, even those from files that do not get rechecked.
/// * Right here at the end of the type check, if the type check was complete then we need to report
///   this fact right away in the errors-file so that the client "hh check" can finish "No errors!".
///   But if it was not complete (e.g. it got interrupted by watchman) then there is no need to finish
///   for the sake of the client: there will be an immediate next round of
///   Server_main.recheck_until_no_changes_left, and it will call us again, and the errors-file
///   will be restarted on that next round, and the act of restarting will close the current errors-file.
///
pub fn type_check(
    agent_session_id: Option<&str>,
    genv: &Genv,
    env: Env,
    start_time: f64,
    cgroup_steps: &crate::cgroup_profiler::StepGroup,
) -> (Env, CheckStats, telemetry::T) {
    crate::server_utils::with_exit_on_exception(|| {
        type_check_(agent_session_id, genv, env, start_time, cgroup_steps)
    })
}

fn type_check_(
    agent_session_id: Option<&str>,
    genv: &Genv,
    env: Env,
    start_time: f64,
    cgroup_steps: &crate::cgroup_profiler::StepGroup,
) -> (Env, CheckStats, telemetry::T) {
    let ignore_hh_version = server_args::ignore_hh_version(&genv.options);
    // Restart the errors-file at the start of type_check.
    errors_write::new_empty_file(
        env.clock.clone(),
        ignore_hh_version,
        env.why_needs_server_type_check.clone(),
    );

    // This is the main typecheck function. Its contract is to
    // (1) tweak env.diagnostics as needed based on what was rechecked , (2) write every single error to errors-file.
    let (env, stats, telemetry, cancel_reason) =
        type_check_unsafe(agent_session_id, genv, env, start_time, cgroup_steps);

    // If the typecheck completed, them mark the errors-file as complete.
    // A "completed" typecheck means (1) all the [env.needs_recheck] files
    // were indeed typechecked, i.e. not interrupted and cancelled by an
    // interrupt handler like the file watcher; (2) file watcher interrupt didn't
    // insert any [env.disk_needs_parsing] files.
    // Because we mark the errors-file as complete, anyone tailing it will
    // know that they can finish their tailing.
    //
    // For incomplete typechecks, we don't do anything here. Necessarily Server_main
    // will do another round of [ServerTypeCheck.type_check] (i.e. us) shortly,
    // and then next round will call [Server_progress.ErrorsWrite.new_empty_file]
    // which will put a "restarted" sentinel at the end of the current file as
    // well as starting a new file. Indeed it's *better* to place the "restarted"
    // sentinel at that future time rather than now, because it'll have a more
    // up-to-date watchclock at that time.
    let is_complete = env.needs_recheck.is_empty() && env.disk_needs_parsing.is_empty();
    if is_complete {
        errors_write::complete(&telemetry);
    }

    // If this was a full check, store in [env] whether+why it got interrupted+cancelled.
    let env = match cancel_reason {
        Some(CancelReason {
            user_message,
            log_message,
        }) => Env {
            why_needs_server_type_check: (user_message, log_message),
            ..env
        },
        // The typecheck wasn't interrupted, but there are still items to check.
        // This is a weird situation, and one that hopefully won't exist.
        // Once lazy checks have been eliminated, we'll revisit the TODO
        // on this subject at the end of [do_type_checking], and see if we can
        // eliminate this path throgh the typesystem.
        //
        // Until that time, what now should we put as the value for [env.why_needs_server_type_check]?
        // Well, the existing value in [env] said why it needed a type check earlier, and it still needs
        // that same type check to be completed, so it is a plausible answer!
        None if !is_complete => env,
        None => Env {
            why_needs_server_type_check: ("Type check is complete".to_string(), "".to_string()),
            ..env
        },
    };

    // (The pool threads' caches do not outlive the check; not in
    // `hh_server --check`, whose process ends after this check.)
    if !server_args::check_mode(&genv.options) && std::env::var_os("HH_KEEP_THREAD_CACHES").is_none() {
        crate::rt::decl_epoch::release_after_check(stats.total_rechecked_count.max(0) as usize);
    }
    crate::rt::heap_stats::after_recheck();
    (env, stats, telemetry)
}

/// The equivalence of a recheck and a full check: for each scenario (a
/// tree, then edits), the diagnostics of the daemon after each recheck are
/// those of a fresh daemon on the edited tree, and those of a fresh daemon
/// are those of the batch check (`hh_server --check`).
///
/// The daemon's state is global to the process (the dependency graph,
/// `Typing_deps.trace`, the context of the providers, the path prefixes),
/// so each run happens in a child process (this test binary running only
/// [`tests::child`]), which prints the diagnostics after each step.
#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::path::PathBuf;
    use std::process::Command;
    use std::process::Stdio;

    use super::*;

    /// The allocator of `hh_server` (`bin/hh_server.rs`), so that the
    /// times and memory of a daemon run in a child compare with the batch
    /// check's (the whole lib test binary gets it).
    /// It counts the bytes live (`rt::heap_stats`), for the recheck-cycle
    /// tests (`rt::heap_stats::tests`), when a child enables it.
    #[cfg(not(feature = "dhat-heap"))]
    #[global_allocator]
    pub(crate) static GLOBAL: crate::rt::heap_stats::Counting<mimalloc::MiMalloc> =
        crate::rt::heap_stats::Counting(mimalloc::MiMalloc);
    /// With the feature `dhat-heap`: a DHAT profile of the steps
    /// `HH_TYPE_CHECK_TEST_DHAT_FROM` to `HH_TYPE_CHECK_TEST_DHAT_TO` of a `daemon` child (to
    /// attribute what a recheck keeps).
    #[cfg(feature = "dhat-heap")]
    #[global_allocator]
    pub(crate) static GLOBAL: crate::rt::heap_stats::Counting<dhat::Alloc> =
        crate::rt::heap_stats::Counting(dhat::Alloc);

    const CHILD_MODE: &str = "HH_TYPE_CHECK_TEST_MODE";
    const CHILD_ROOT: &str = "HH_TYPE_CHECK_TEST_ROOT";
    const CHILD_EDITS: &str = "HH_TYPE_CHECK_TEST_EDITS";

    type Files<'a> = &'a [(&'a str, &'a str)];
    /// The edits of a step: a file and its new contents (`None`: deleted).
    type Step<'a> = &'a [(&'a str, Option<&'a str>)];

    fn write_tree(root: &Path, files: &[(String, String)]) {
        std::fs::create_dir_all(root).unwrap();
        std::fs::write(root.join(".hhconfig"), "").unwrap();
        for (name, contents) in files {
            let path = root.join(name);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, contents).unwrap();
        }
    }

    /// The diagnostics as `hh_server --check` would print them, with the
    /// root replaced by `ROOT/`.
    fn show(root: &Path, diagnostics: Vec<crate::diagnostics::Diagnostic>) -> String {
        let root = format!("{}/", root.display());
        let mut out = String::new();
        for d in &diagnostics {
            let s = crate::user_diagnostic::to_string(&crate::user_diagnostic::to_absolute(d));
            out.push_str(&s.replace(&root, "ROOT/"));
            out.push('\n');
        }
        out
    }

    /// The configuration of the root (`ROOT/.hhconfig`, as the monitor
    /// loads it).
    fn load_config(
        root: &Path,
    ) -> (
        crate::server_config::T,
        crate::server_local_config::T,
    ) {
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, root);
        crate::relative_path::set_path_prefix(
            crate::relative_path::Prefix::Hhi,
            Path::new("/hhi"),
        );
        crate::relative_path::set_path_prefix(
            crate::relative_path::Prefix::Tmp,
            Path::new("/tmp"),
        );
        crate::server_config::load(true, "", &[]).unwrap()
    }

    fn make_genv(root: &Path) -> Genv {
        let (config, local_config) = load_config(root);
        // (As `Server_main.setup_server`.)
        for re in crate::files::ignored_path_regexes(crate::server_config::ignored_path_patterns(&config))
            .unwrap()
        {
            crate::files_to_ignore::ignore_path(re)
        }
        Genv {
            options: crate::server_args::default_options(&root.display().to_string()),
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
            typing_deps::mode::T::InMemoryMode(None),
            None,
            &genv.config,
            root,
        )
    }

    /// What a child process does, per `HH_TYPE_CHECK_TEST_MODE`: `batch` (the batch
    /// check), `daemon` (init and the first full check, then a recheck per
    /// step of `HH_TYPE_CHECK_TEST_EDITS`, a directory with one directory per step
    /// holding the files written and a `.deleted` list).
    fn run_child(mode: &str, root: PathBuf, edits: Option<PathBuf>) -> String {
        crate::server_progress::disable();
        let threads = std::env::var("HH_TYPE_CHECK_TEST_THREADS").ok().map(|t| t.parse().unwrap());
        crate::check::build_thread_pool(threads).unwrap();
        if mode == "batch" {
            let r = crate::check::discover_root(&root, &[]).unwrap();
            let hhi = PathBuf::from("/hhi");
            let checked = crate::check::check_root(r, None, &hhi).unwrap();
            return show(&root, checked.sorted_diagnostics());
        }
        let start = gettimeofday();
        typing_deps::TRACE.store(true, std::sync::atomic::Ordering::SeqCst);
        // As `Server_main.setup_server`: the decl stores on the shared heap.
        if !crate::hh_shared::is_initialized() {
            let mut config = crate::shared_mem::default_config();
            config.hash_table_pow = 22;
            crate::hh_shared::init(&config, 0).unwrap();
        }
        crate::ctx::use_shared_memory_stores(true);
        let genv = make_genv(&root);
        let env = make_env(&genv, &root);
        let (env, _) = crate::server_init::init(
            &genv,
            env,
            crate::server_init_types::InitApproach::FullInit,
        );
        let after_init = crate::rt::heap_stats::live_bytes();
        let (mut env, _, _) =
            crate::cgroup_profiler::step_group("Full_check", true, |steps| type_check(None, &genv, env, gettimeofday(), steps));
        if mode == "breakdown" {
            return crate::rt::heap_stats::tests::breakdown(after_init, env);
        }
        if mode == "daemon-raw" {
            // What `hh_server --check` prints (`Program.run_once_and_exit`).
            let error_list: Vec<_> =
                diagnostics::get_diagnostic_list(None, env.diagnostics.clone())
                    .iter()
                    .map(crate::user_diagnostic::to_absolute)
                    .collect();
            let mut out = vec![];
            crate::server_main::print_error_list(&mut out, false, &error_list);
            let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
            unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) };
            eprintln!(
                "init and full check: {:.1} s, peak RSS {:.2} GB",
                gettimeofday() - start,
                usage.ru_maxrss as f64 / 1e9
            );
            return String::from_utf8(out).unwrap();
        }
        if mode == "progress" {
            return run_progress(&genv, env, &root);
        }
        if mode == "cancel" || mode == "mock-cancel" {
            return run_cancel(mode, &genv, env, &root);
        }
        let mut out = String::new();
        let mut step = 0;
        #[cfg(feature = "dhat-heap")]
        let mut dhat_profiler: Option<dhat::Profiler> = None;
        loop {
            out.push_str(&format!("=== step {}\n", step));
            out.push_str(&show(
                &root,
                diagnostics::get_sorted_diagnostic_list(None, env.diagnostics.clone()),
            ));
            #[cfg(feature = "dhat-heap")]
            {
                let step_env = |v: &str| std::env::var(v).ok().map(|s| s.parse::<usize>().unwrap());
                if step_env("HH_TYPE_CHECK_TEST_DHAT_FROM") == Some(step) {
                    dhat_profiler = Some(dhat::Profiler::builder().file_name(std::env::var("HH_TYPE_CHECK_TEST_DHAT_FILE").unwrap()).build());
                }
                if step_env("HH_TYPE_CHECK_TEST_DHAT_TO") == Some(step) {
                    dhat_profiler = None;
                }
            }
            if let Some(live) = crate::rt::heap_stats::live_bytes() {
                // (`rt::heap_stats::tests`: the bytes live after each step,
                // once the collection the check may have started is over.)
                crate::rt::decl_epoch::wait_for_hash_consed_gc();
                let live = crate::rt::heap_stats::live_bytes().unwrap_or(live);
                // (Without the output of the steps itself.)
                out.push_str(&format!("=== heap {}\n", live - out.capacity() as i64));
            }
            if mode == "dead-fixmes" {
                // The fixmes that an error at line 5 of `m_2.php` would be
                // matched against, on a thread that parsed nothing.
                let m2 = relative_path::create(
                    relative_path::Prefix::Root,
                    &root.join("m_2.php").display().to_string(),
                );
                let pos = oxidized::pos::Pos::from_lnum_bol_offset(
                    Arc::new(m2),
                    (5, 100, 102),
                    (5, 100, 103),
                );
                let codes = std::thread::spawn(move || {
                    crate::fixme_provider::get_fixme_codes_for_pos(&pos)
                })
                .join()
                .unwrap();
                out.push_str(&format!("codes at m_2.php:5 {:?}\n", codes));
                // `hh_client --remove-dead-fixmes` (`REMOVE_DEAD_FIXMES []`):
                // the patches, on this (the world) thread.
                let root_prefix = format!("{}/", root.display());
                for patch in crate::server_rename::get_fixme_patches(&[], &env) {
                    let crate::server_rename_types::Patch::Remove(pos) = patch else {
                        panic!("not a removal");
                    };
                    out.push_str(&format!("dead {}\n", crate::pos::string(&pos).replace(&root_prefix, "ROOT/")));
                }
            }
            assert!(env.needs_recheck.is_empty());
            assert!(server_env::is_full_check_done(env.full_check_status));
            step += 1;
            let Some(edits) = &edits else { break };
            let dir = edits.join(step.to_string());
            if !dir.exists() {
                break;
            }
            let mut changed = RPSet::new();
            for entry in walk(&dir) {
                let rel = entry.strip_prefix(&dir).unwrap();
                let dest = root.join(rel);
                std::fs::create_dir_all(dest.parent().unwrap()).unwrap();
                std::fs::copy(&entry, &dest).unwrap();
                changed.insert(relative_path::create(
                    relative_path::Prefix::Root,
                    &dest.display().to_string(),
                ));
            }
            let deleted = edits.join(format!("{}.deleted", step));
            if let Ok(deleted) = std::fs::read_to_string(deleted) {
                for name in deleted.lines().filter(|l| !l.is_empty()) {
                    let dest = root.join(name);
                    let _ = std::fs::remove_file(&dest);
                    changed.insert(relative_path::create(
                        relative_path::Prefix::Root,
                        &dest.display().to_string(),
                    ));
                }
            }
            env = Env {
                disk_needs_parsing: env.disk_needs_parsing.clone().union(changed),
                full_check_status: FullCheckStatus::FullCheckStarted,
                ..env
            };
            let (new_env, _, _) =
                crate::cgroup_profiler::step_group("Full_check", true, |steps| type_check(None, &genv, env, gettimeofday(), steps));
            env = new_env;
            if std::env::var_os("HH_INCR_VERIFY").is_some() {
                env.ctx.check_naming_invariant().unwrap();
            }
        }
        out
    }

    /// A recheck that a cancellation interrupts, then the recheck that
    /// finishes it. `cancel`: the file `b.php` changes on disk while
    /// `a.php` is rechecked, and an interrupt handler (as `ServerMain`'s
    /// `file_changes_interrupt_handler`) adds it to `disk_needs_parsing` and
    /// cancels; `mock-cancel`: `Typing_check_service.TestMocking`
    /// cancels `c.php`. Prints the diagnostics after the second recheck.
    fn run_cancel(mode: &str, genv: &Genv, env: Env, root: &Path) -> String {
        let rp = |name: &str| {
            relative_path::create(relative_path::Prefix::Root, &root.join(name).display().to_string())
        };
        std::fs::write(root.join("a.php"), "<?hh\nfunction f(): string { return 'x'; }\n").unwrap();
        let mut env = Env {
            disk_needs_parsing: std::iter::once(rp("a.php")).collect(),
            full_check_status: FullCheckStatus::FullCheckStarted,
            ..env
        };
        let mut pipe = [0; 2];
        if mode == "cancel" {
            std::fs::write(root.join("b.php"), "<?hh\nfunction g(): int { return f() . 'y'; }\n").unwrap();
            assert_eq!(unsafe { libc::pipe(pipe.as_mut_ptr()) }, 0);
            assert_eq!(unsafe { libc::write(pipe[1], b"x".as_ptr().cast(), 1) }, 1);
            let fd = pipe[0];
            let b = rp("b.php");
            env.interrupt_handlers = Arc::new(move |_genv, _env| {
                let b = b.clone();
                let handler: server_env::InterruptHandler<'_> = Box::new(move |env: Env| {
                    let env = Env {
                        disk_needs_parsing: env.disk_needs_parsing.update(b.clone()),
                        ..env
                    };
                    (
                        env,
                        typing_check_service::InterruptResult::Cancel {
                            user_message: "Files have changed on disk! b.php".to_string(),
                            log_message: "test".to_string(),
                            timestamp: 0.0,
                        },
                    )
                });
                vec![(fd, handler)]
            });
        } else {
            typing_check_service::test_mocking::set_is_cancelled(rp("c.php"));
        }
        let (env, _, _) =
            crate::cgroup_profiler::step_group("Full_check", true, |steps| type_check(None, genv, env, gettimeofday(), steps));
        let complete = env.needs_recheck.is_empty() && env.disk_needs_parsing.is_empty();
        assert!(!complete, "the cancelled recheck is complete");
        let expected_message = if mode == "cancel" {
            "Files have changed on disk! b.php"
        } else {
            "mock cancel"
        };
        assert_eq!(env.why_needs_server_type_check.0, expected_message);
        if mode == "cancel" {
            assert!(env.disk_needs_parsing.contains(&rp("b.php")));
        } else {
            assert_eq!(env.needs_recheck, std::iter::once(rp("c.php")).collect());
            assert!(!server_env::is_full_check_done(env.full_check_status));
        }
        // The next recheck (the handler's file descriptor is closed: no
        // handler any more).
        let env = Env {
            interrupt_handlers: Arc::new(|_genv, _env| vec![]),
            type_check_testing_hooks: None,
            full_check_status: FullCheckStatus::FullCheckStarted,
            ..env
        };
        if mode == "cancel" {
            unsafe {
                libc::close(pipe[0]);
                libc::close(pipe[1]);
            }
        }
        let (env, _, _) =
            crate::cgroup_profiler::step_group("Full_check", true, |steps| type_check(None, genv, env, gettimeofday(), steps));
        assert!(env.needs_recheck.is_empty() && env.disk_needs_parsing.is_empty());
        assert!(server_env::is_full_check_done(env.full_check_status));
        assert_eq!(env.why_needs_server_type_check.0, "Type check is complete");
        show(
            root,
            diagnostics::get_sorted_diagnostic_list(None, env.diagnostics.clone()),
        )
    }

    /// The progress messages of a recheck after a change to a base class,
    /// then after a body-only change: one line per message, numbers as `N`,
    /// repeats collapsed (as the OCaml's are compared).
    fn run_progress(genv: &Genv, env: Env, root: &Path) -> String {
        let rp = |name: &str| {
            relative_path::create(relative_path::Prefix::Root, &root.join(name).display().to_string())
        };
        let mut env = env;
        let mut out = String::new();
        let edits: [(&str, String); 2] = [
            (
                "base.php",
                "<?hh\nclass C0 {\n  public function m(int $a0 = 0): int { return 0; }\n}\n".to_string(),
            ),
            (
                "f1.php",
                std::fs::read_to_string(root.join("f1.php")).unwrap().replace("return $x;", "return $x + 1;"),
            ),
        ];
        for (name, contents) in edits {
            std::fs::write(root.join(name), contents).unwrap();
            env = Env {
                disk_needs_parsing: std::iter::once(rp(name)).collect(),
                full_check_status: FullCheckStatus::FullCheckStarted,
                ..env
            };
            crate::server_progress::trace_for_test::start();
            let (new_env, _, _) =
                crate::cgroup_profiler::step_group("Full_check", true, |steps| type_check(None, genv, env, gettimeofday(), steps));
            env = new_env;
            out.push_str(&format!("== {}\n", name));
            out.push_str(&normalize_progress(&crate::server_progress::trace_for_test::take()));
        }
        out
    }

    fn normalize_progress(trace: &[(crate::server_progress::Disposition, String)]) -> String {
        let digits = regex::Regex::new(r"[0-9]+(\.[0-9]+)?").unwrap();
        let mut lines: Vec<String> = vec![];
        for (d, m) in trace {
            let line = format!("{:?}\t{}", d, digits.replace_all(m, "N"));
            if lines.last() != Some(&line) {
                lines.push(line);
            }
        }
        lines.iter().map(|l| format!("{l}\n")).collect()
    }

    fn walk(dir: &Path) -> Vec<PathBuf> {
        let mut out = vec![];
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                out.extend(walk(&path));
            } else {
                out.push(path);
            }
        }
        out.sort();
        out
    }

    /// The child process: does nothing unless run by [`spawn`].
    #[test]
    fn child() {
        let Some(mode) = std::env::var_os(CHILD_MODE) else {
            return;
        };
        let mode = mode.to_string_lossy().into_owned();
        if std::env::var_os("HH_TYPE_CHECK_TEST_HEAP").is_some() {
            GLOBAL.enable();
            if let Some(every) = std::env::var_os("HH_HEAP_SAMPLE") {
                crate::rt::heap_stats::sampler::enable(every.to_string_lossy().parse().unwrap());
            }
        }
        let default_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if let Some(e) = info.payload().downcast_ref::<typing_deps::DepgraphUnavailable>() {
                eprintln!("panic payload: {}", e);
            }
            default_hook(info)
        }));
        // (As in the binaries: one set of fixme tables for all the threads.)
        crate::fixme_provider::set_shared_tables(true);
        let root = PathBuf::from(std::env::var_os(CHILD_ROOT).unwrap());
        let edits = std::env::var_os(CHILD_EDITS).map(PathBuf::from);
        let out = crate::check::run_on_large_stack("world", move || run_child(&mode, root, edits))
            .unwrap();
        std::fs::write(
            std::env::var("HH_TYPE_CHECK_TEST_OUT").unwrap(),
            out,
        )
        .unwrap();
    }

    fn spawn(mode: &str, root: &Path, edits: Option<&Path>, out: &Path) -> String {
        let mut cmd = Command::new(std::env::current_exe().unwrap());
        cmd.args([
            "server_type_check::tests::child",
            "--exact",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(CHILD_MODE, mode)
        .env(CHILD_ROOT, root)
        .env("HH_TYPE_CHECK_TEST_OUT", out)
        .stdin(Stdio::null());
        if let Some(edits) = edits {
            cmd.env(CHILD_EDITS, edits);
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

    fn scratch(test: &str) -> PathBuf {
        let dir = std::env::temp_dir()
            .canonicalize()
            .unwrap()
            .join(format!("hh-s1-{}-{}", test, std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// The daemon on `files` then each step: its diagnostics per step.
    fn incremental(test: &str, files: Files<'_>, steps: &[Step<'_>]) -> Vec<String> {
        incremental_in_mode("daemon", test, files, steps)
    }

    fn incremental_in_mode(
        mode: &str,
        test: &str,
        files: Files<'_>,
        steps: &[Step<'_>],
    ) -> Vec<String> {
        let dir = scratch(test);
        let edits = dir.join("edits");
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
        let root = dir.join("root");
        let files: Vec<(String, String)> =
            files.iter().map(|(n, c)| (n.to_string(), c.to_string())).collect();
        write_tree(&root, &files);
        let out = spawn(mode, &root, Some(&edits), &dir.join("incremental.out"));
        let _ = std::fs::remove_dir_all(&dir);
        out.split("=== step ")
            .filter(|s| !s.is_empty())
            .map(|s| s.split_once('\n').unwrap().1.to_string())
            .collect()
    }

    /// Runs the scenario: the daemon on `files` then each step, against a
    /// fresh daemon on the tree after each step, and the fresh daemon
    /// against the batch check. Returns the daemon's output per step.
    fn scenario(test: &str, files: Files<'_>, steps: &[Step<'_>]) -> Vec<String> {
        let dir = scratch(test);
        let mut tree: std::collections::BTreeMap<String, String> = files
            .iter()
            .map(|(n, c)| (n.to_string(), c.to_string()))
            .collect();
        let edits = dir.join("edits");
        let mut trees = vec![tree.clone()];
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
                        tree.insert(name.to_string(), contents.to_string());
                    }
                    None => {
                        deleted.push_str(name);
                        deleted.push('\n');
                        tree.remove(*name);
                    }
                }
            }
            std::fs::write(edits.join(format!("{}.deleted", k + 1)), deleted).unwrap();
            trees.push(tree.clone());
        }
        let root = dir.join("root");
        let first: Vec<(String, String)> = trees[0].clone().into_iter().collect();
        write_tree(&root, &first);
        let incremental = spawn("daemon", &root, Some(&edits), &dir.join("incremental.out"));
        let parts: Vec<String> = incremental
            .split("=== step ")
            .filter(|s| !s.is_empty())
            .map(|s| s.split_once('\n').unwrap().1.to_string())
            .collect();
        assert_eq!(parts.len(), trees.len(), "{incremental}");
        for (k, tree) in trees.iter().enumerate() {
            let fresh_root = dir.join(format!("fresh{}", k)).join("root");
            let files: Vec<(String, String)> = tree.clone().into_iter().collect();
            write_tree(&fresh_root, &files);
            let fresh = spawn("daemon", &fresh_root, None, &dir.join(format!("fresh{}.out", k)));
            let fresh = fresh.split_once('\n').unwrap().1.to_string();
            // (The roots differ: compare with the root masked.)
            assert_eq!(
                parts[k], fresh,
                "{test}: step {k}: the recheck differs from a full check of the tree"
            );
            let batch = spawn("batch", &fresh_root, None, &dir.join(format!("batch{}.out", k)));
            assert_eq!(
                fresh, batch,
                "{test}: step {k}: the daemon's full check differs from the batch check"
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
        parts
    }

    const PARENT: &str = "<?hh
class Parent_ {
  public function f(): int { return 1; }
}
";
    const CHILD_: &str = "<?hh
class Child_ extends Parent_ {}
function use_child(Child_ $c): int { return $c->f(); }
";

    /// A file of [`dead_fixmes_whatever_thread_checked_the_files`]: two
    /// fixmes still needed, dead ones (three on one line, one of two on a
    /// line, one after the code it was for), an `HH_IGNORE` of a warning that
    /// is used, one that is dead.
    fn fixmes_file(k: usize, param: &str) -> String {
        format!(
            "<?hh
function take_int_{k}({param} $i): void {{}}
function f_{k}(string $s, int $n): void {{
  /* HH_FIXME[4110] needed */
  take_int_{k}($s);
  /* HH_FIXME[4110] dead */ /* HH_FIXME[4011] dead too */ /* HH_FIXME[4089] dead3 */
  take_int_{k}(1);
  /* HH_FIXME[4110] needed */ /* HH_FIXME[4099] dead */
  take_int_{k}($s);
  /* HH_IGNORE[12009] used */
  if ($n is int) {{}}
  /* HH_IGNORE[12001] dead */
  $u = 1;
  take_int_{k}($s); /* HH_FIXME[4110] after */
}}
"
        )
    }

    /// `hh_client --remove-dead-fixmes`: the patches are the dead
    /// fixmes of every file, whichever thread parsed and checked it (here on
    /// the world thread, which checked none), after the full check and
    /// after a recheck (a file whose fixme is no longer needed, a file whose
    /// errors went away through a dependency, a new file; the other files
    /// were not rechecked). The OCaml (`hh_client check --remove-dead-fixmes`
    /// on the same tree) removes exactly these comments.
    #[test]
    fn dead_fixmes_whatever_thread_checked_the_files() {
        const N: usize = 48;
        let config = "allowed_fixme_codes_strict = 4110,4011,4089,4099,12009,12001\n";
        let names: Vec<String> = (1..=N).map(|k| format!("m_{k}.php")).collect();
        let contents: Vec<String> = (1..=N).map(|k| fixmes_file(k, "int")).collect();
        let mut files: Vec<(&str, &str)> = vec![(".hhconfig", config)];
        files.extend(names.iter().map(|n| n.as_str()).zip(contents.iter().map(|c| c.as_str())));
        let m1 = fixmes_file(1, "int").replace("take_int_1($s);\n  /* HH_FIXME[4110] dead */", "take_int_1(3);\n  /* HH_FIXME[4110] dead */");
        let m3 = fixmes_file(3, "mixed");
        let new_file = "<?hh\nfunction new_one(): void {\n  /* HH_FIXME[4110] dead */\n  $x = 1;\n}\n";
        let out = incremental_in_mode(
            "dead-fixmes",
            "deadfixmes",
            &files,
            &[&[("m_1.php", Some(&m1)), ("m_3.php", Some(&m3)), ("m_new.php", Some(new_file))]],
        );
        assert_eq!(out.len(), 2);
        // (An error positioned in a file sees the file's fixmes whichever
        // thread parsed it.)
        assert!(out[0].contains("codes at m_2.php:5 {4110}"), "{}", out[0]);
        // The dead fixmes of each file (the patches name the file first).
        let dead = |step: &str| -> std::collections::BTreeMap<String, Vec<String>> {
            let mut m = std::collections::BTreeMap::<String, Vec<String>>::new();
            for line in step.lines().filter_map(|l| l.strip_prefix("dead File \"ROOT/")) {
                let (file, rest) = line.split_once('"').unwrap();
                m.entry(file.to_string()).or_default().push(rest.to_string());
            }
            m.values_mut().for_each(|v| v.sort());
            m
        };
        let usual = |k: usize| -> Vec<String> {
            let after = 18 + k.to_string().len();
            let mut v = vec![
                ", line 6, characters 3-27:".to_string(),
                ", line 6, characters 29-57:".to_string(),
                ", line 6, characters 59-84:".to_string(),
                ", line 8, characters 31-55:".to_string(),
                ", line 12, characters 3-29:".to_string(),
                format!(", line 14, characters {}-{}:", after, after + 25),
            ];
            v.sort();
            v
        };
        let (init, after) = (dead(&out[0]), dead(&out[1]));
        assert_eq!(init.len(), N, "{}", out[0]);
        for k in 1..=N {
            assert_eq!(init[&format!("m_{k}.php")], usual(k), "{}", out[0]);
        }
        assert_eq!(after.len(), N + 1, "{}", out[1]);
        for k in 1..=N {
            let mut expected = usual(k);
            if k == 1 {
                expected.push(", line 4, characters 3-29:".to_string());
            }
            if k == 3 {
                expected.push(", line 4, characters 3-29:".to_string());
                expected.push(", line 8, characters 3-29:".to_string());
            }
            expected.sort();
            assert_eq!(after[&format!("m_{k}.php")], expected, "m_{k}.php: {}", out[1]);
        }
        assert_eq!(after["m_new.php"], vec![", line 3, characters 3-27:".to_string()]);
    }

    #[test]
    fn body_only_change() {
        let out = scenario(
            "body",
            &[("a.php", "<?hh\nfunction f(): int { return 1; }\n"), ("b.php", "<?hh\nfunction g(): int { return f(); }\n")],
            &[
                &[("a.php", Some("<?hh\nfunction f(): int { return 'x'; }\n"))],
                &[("a.php", Some("<?hh\nfunction f(): int { return 2; }\n"))],
            ],
        );
        assert!(out[0].is_empty(), "{}", out[0]);
        assert!(out[1].contains("Invalid return type"), "{}", out[1]);
        assert!(out[2].is_empty(), "{}", out[2]);
    }

    #[test]
    fn signature_change() {
        let out = scenario(
            "signature",
            &[("a.php", "<?hh\nfunction f(): int { return 1; }\n"), ("b.php", "<?hh\nfunction g(): int { return f(); }\n")],
            &[
                &[("a.php", Some("<?hh\nfunction f(): string { return 'x'; }\n"))],
                &[("a.php", Some("<?hh\nfunction f(): int { return 1; }\n"))],
            ],
        );
        assert!(out[1].contains("ROOT/b.php"), "{}", out[1]);
        assert!(out[2].is_empty(), "{}", out[2]);
    }

    #[test]
    fn classes_added_removed_renamed() {
        scenario(
            "classes",
            &[("p.php", PARENT), ("c.php", CHILD_)],
            &[
                // removed
                &[("p.php", None)],
                // added back
                &[("p.php", Some(PARENT))],
                // renamed
                &[("p.php", Some("<?hh\nclass Parent2 {\n  public function f(): int { return 1; }\n}\n"))],
                &[("c.php", Some("<?hh\nclass Child_ extends Parent2 {}\nfunction use_child(Child_ $c): int { return $c->f(); }\n"))],
            ],
        );
    }

    #[test]
    fn member_added_to_a_parent() {
        scenario(
            "member",
            &[
                ("p.php", PARENT),
                ("c.php", CHILD_),
                ("d.php", "<?hh\nfunction use_g(Child_ $c): int { return $c->g(); }\n"),
            ],
            &[
                &[("p.php", Some("<?hh\nclass Parent_ {\n  public function f(): int { return 1; }\n  public function g(): int { return 2; }\n}\n"))],
                &[("p.php", Some("<?hh\nclass Parent_ {\n  public function f(): string { return ''; }\n  public function g(): int { return 2; }\n}\n"))],
                &[("p.php", Some(PARENT))],
            ],
        );
    }

    #[test]
    fn file_deleted_and_duplicates() {
        let out = scenario(
            "duplicates",
            &[("a.php", "<?hh\nclass A {}\n"), ("u.php", "<?hh\nfunction u(A $a): void {}\n")],
            &[
                // a duplicate, added
                &[("b.php", Some("<?hh\nclass A {}\n"))],
                // the first one removed
                &[("a.php", None)],
                // and the second
                &[("b.php", None)],
                &[("a.php", Some("<?hh\nclass A {}\n"))],
            ],
        );
        assert!(out[3].contains("Unbound name") || out[3].contains("unbound"), "{}", out[3]);
    }

    #[test]
    fn typedefs_and_constants() {
        scenario(
            "typedefs",
            &[
                ("t.php", "<?hh\ntype T = int;\nconst int K = 1;\n"),
                ("u.php", "<?hh\nfunction u(T $t): int { return $t + K; }\n"),
            ],
            &[
                &[("t.php", Some("<?hh\ntype T = string;\nconst int K = 1;\n"))],
                &[("t.php", Some("<?hh\ntype T = int;\nconst string K = 'k';\n"))],
                &[("t.php", Some("<?hh\ntype T = int;\nconst int K = 1;\n"))],
            ],
        );
    }

    #[test]
    fn syntax_error_and_repair() {
        scenario(
            "syntax",
            &[("a.php", "<?hh\nfunction f(): int { return 1; }\n"), ("b.php", "<?hh\nfunction g(): int { return f(); }\n")],
            &[
                &[("a.php", Some("<?hh\nfunction f(): int { return 1 }\n"))],
                &[("a.php", Some("<?hh\nfunction f(: int { return 1; }\n"))],
                &[("a.php", Some("<?hh\nfunction f(): int { return 1; }\n"))],
            ],
        );
    }

    /// A duplicate added in a file that comes first: on the first recheck
    /// the previous definition keeps the name (the comment of `do_naming`),
    /// so the error is in the new file; the next recheck renames both files
    /// (`failed_naming`) and the first file wins. As the OCaml daemon does
    /// (checked against the OCaml daemon).
    #[test]
    fn duplicate_added_before_the_winner() {
        let out = incremental(
            "dup_first",
            &[
                ("z.php", "<?hh\nclass A {}\n"),
                ("u.php", "<?hh\nfunction u(A $a): void {}\n"),
            ],
            &[
                &[("a.php", Some("<?hh\nclass A { public function f(): void {} }\n"))],
                &[("u.php", Some("<?hh\nfunction u(A $a): void { $a->f(); }\n"))],
                &[("z.php", Some("<?hh\n"))],
            ],
        );
        let bound = |file: &str, previous: &str| {
            format!(
                "ERROR: File \"ROOT/{file}\", line 2, characters 7-7:\nName already bound: `A` (Naming[2012])\n  File \"ROOT/{previous}\", line 2, characters 7-7:\n  Previous definition is here\n\n"
            )
        };
        assert_eq!(out, vec!["".to_string(), bound("a.php", "z.php"), bound("z.php", "a.php"), "".to_string()]);
    }

    fn cancelled(mode: &str) {
        let dir = scratch(mode);
        let mut files: Vec<(String, String)> = vec![
            ("a.php".to_string(), "<?hh\nfunction f(): int { return 1; }\n".to_string()),
            ("b.php".to_string(), "<?hh\nfunction g(): int { return f(); }\n".to_string()),
            ("c.php".to_string(), "<?hh\nfunction h(): int { return f(); }\n".to_string()),
        ];
        // Enough files that the check is still running when the handler runs.
        for i in 0..300 {
            files.push((format!("m{i}.php"), format!("<?hh\nfunction m{i}(): int {{ return f(); }}\n")));
        }
        let root = dir.join("root");
        write_tree(&root, &files);
        let out = spawn(mode, &root, None, &dir.join("cancel.out"));
        // A fresh daemon on the tree as it is now.
        let fresh = spawn("daemon", &root, None, &dir.join("fresh.out"));
        let fresh = fresh.split_once('\n').unwrap().1.to_string();
        assert_eq!(out, fresh);
        assert!(out.contains("ROOT/c.php"), "{out}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// An interrupt handler cancels the recheck: the files left are
    /// rechecked by the next one, which gives what a full check gives.
    #[test]
    fn cancelled_by_a_file_change() {
        cancelled("cancel")
    }

    #[test]
    fn cancelled_by_test_mocking() {
        cancelled("mock-cancel")
    }

    /// Two classes whose names differ in case (`test_capitalization.ml`;
    /// the same diagnostics on the oracle): the second is not bound, so
    /// its decl kept in the stores must not make it the winner.
    #[test]
    fn capitalization() {
        let expected = "ERROR: File \"ROOT/foo2.php\", line 2, characters 9-11:\nName already bound: `FOO` (Naming[2012])\n  File \"ROOT/foo1.php\", line 2, characters 9-11:\n  Previous definition is here\n\n";
        let out = scenario(
            "capitalization",
            &[("x.php", "<?hh\n")],
            &[
                &[("foo1.php", Some("<?hh\n  class foo {}\n")), ("foo2.php", Some("<?hh\n  class FOO {}\n"))],
                &[("bar.php", Some(""))],
            ],
        );
        assert_eq!(out, vec!["".to_string(), expected.to_string(), expected.to_string()]);
    }

    /// The progress.json texts of a recheck, as the OCaml writes them (the
    /// fixture: every write of the oracle daemon, captured by an interposed
    /// `write` on a root of `gen.py` (3,000 classes extending `C0`), the
    /// part written by `Server_type_check.type_check`). The numbers differ
    /// with the sizes; the texts and their order do not.
    #[test]
    fn progress_messages_of_a_recheck() {
        let dir = scratch("progress");
        let root = dir.join("root");
        let mut files = vec![(
            "base.php".to_string(),
            "<?hh\nclass C0 {\n  public function m(): int { return 0; }\n}\n".to_string(),
        )];
        for i in 1..=40 {
            files.push((
                format!("f{i}.php"),
                format!(
                    "<?hh\nclass C{i} extends C0 {{\n  const int K = {i};\n  public function g(int $x): int {{\n    if ($x > 1) {{ $x = $x + C{i}::K + $this->m(); }}\n    return $x;\n  }}\n}}\nfunction fn{i}(C{i} $c): int {{ return $c->m() + $c->g({i}); }}\n"
                ),
            ));
        }
        write_tree(&root, &files);
        let out = spawn("progress", &root, None, &dir.join("progress.out"));
        let _ = std::fs::remove_dir_all(&dir);
        let typecheck = "DWorking\tdetermining trunk changes\nDWorking\ttypechecking\nDWorking\ttypechecking N files\nDWorking\ttypechecking N/N files (N%)\nDWorking\ttypecheck ending\n";
        let members = "DWorking\tgetting members of N/N classes (N%)\nDWorking\tdetermining changes\n";
        let expected = format!(
            "== base.php\nDWorking\tparsing N files\nDWorking\tupdating naming tables\nDWorking\tdetermining changes\n{members}{members}DWorking\tresolving files\nDWorking\tdetermining changes\n{typecheck}== f1.php\nDWorking\tparsing N files\nDWorking\tupdating naming tables\nDWorking\tdetermining changes\nDWorking\tresolving files\nDWorking\tdetermining changes\n{typecheck}"
        );
        assert_eq!(out, expected);
    }

    /// In the daemon the decl stores also hold decls of names
    /// that lost their binding (`cache_decls` keeps them, as the OCaml's
    /// heaps): b.php's `FOO`, `TR`, `TT`, cached when b.php (a conflict file
    /// of the init) is reparsed. They must not count as bound: unbound-name
    /// checks and did-you-mean (`Naming_provider`), the class checks of a
    /// loser class (`Decl_provider.get_class`: only a name bound to a class is
    /// folded), `__Sealed` with a trait (`Naming_provider.get_type_path`), and
    /// whether a property type requires initialization (the kind of the name,
    /// `Naming_provider.get_type_kind`). Each step equals a fresh check.
    #[test]
    fn loser_decls_are_not_bound() {
        let uses = "<?hh
function c1(FOO $x): void {}
<<__Sealed(TR::class)>> class C {}
class D { public TT $p; }
function c2(): void { new FOO(); }
";
        let out = scenario(
            "losers",
            &[
                ("a.php", "<?hh\nclass foo {}\nclass tr {}\nclass tt {}\n"),
                ("b.php", "<?hh\nclass FOO { public int $x; }\ntrait TR {}\ntype TT = ?int;\n"),
                ("c.php", "<?hh\nfunction c(): void {}\n"),
            ],
            &[&[("c.php", Some(uses))], &[("e.php", Some("<?hh\n"))]],
        );
        // (Checked against the OCaml daemon.)
        assert_eq!(out[1].matches("Did you mean").count(), 4, "{}", out[1]);
        assert!(!out[1].contains("sealed"), "{}", out[1]);
        assert!(out[1].contains("Class `D` has properties"), "{}", out[1]);
        assert!(!out[1].contains("Class `FOO` has"), "{}", out[1]);
    }
}
