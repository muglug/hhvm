// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_prechecked_files.ml`. See
//! `hh/PORTING.md`.
//!
//! `Server_revision_tracker.typing_changed` is a no-op unless the tracker
//! was initialized (`hg_aware`, Meta's): not called.

use crate::hh_logger;
use crate::naming_provider;
use crate::provider_utils;
use crate::server_env;
use crate::server_env::DirtyDeps;
use crate::server_env::Env;
use crate::server_env::FullCheckStatus;
use crate::server_env::Genv;
use crate::server_env::PrecheckedFilesStatus;
use crate::telemetry;
use crate::typing_deps;
use crate::typing_deps::dep_set;

type RPSet = crate::relative_path::set::T;

/// `should_use options local_config`
pub fn should_use(
    options: &crate::server_args::Options,
    local_config: &crate::server_local_config::T,
) -> bool {
    crate::server_args::prechecked(options).unwrap_or(local_config.prechecked_files)
}

/// `set env prechecked_files`
pub fn set(env: Env, prechecked_files: PrecheckedFilesStatus) -> Env {
    Env {
        prechecked_files,
        ..env
    }
}

/// `init env ~dirty_local_deps ~dirty_master_deps`
pub fn init(env: Env, dirty_local_deps: dep_set::T, dirty_master_deps: dep_set::T) -> Env {
    set(
        env,
        PrecheckedFilesStatus::InitialTypechecking(DirtyDeps {
            rechecked_files: RPSet::new(),
            dirty_local_deps,
            dirty_master_deps,
            clean_local_deps: dep_set::make(),
        }),
    )
}

fn ms_since(tend: f64, tstart: f64) -> isize {
    ((tend - tstart) * 1000.) as isize
}

/// Update env.needs_recheck and return new value for [dirty_master_deps]
/// using the following pseudo-code:
///     needs_recheck = files(fanout(fanout(deps) /\ dirty_master_deps)) \ rechecked_files
///     dirty_master_deps = dirty_master_deps \ fanout(deps)
/// (`intersect_with_master_deps ~ctx ~deps ~dirty_master_deps
/// ~rechecked_files genv env`)
fn intersect_with_master_deps(
    ctx: &crate::provider_context::T,
    deps: &dep_set::T,
    dirty_master_deps: &dep_set::T,
    rechecked_files: &RPSet,
    _genv: &Genv,
    env: Env,
) -> (Env, dep_set::T, usize, telemetry::T) {
    let now = crate::rt::ocaml_unix::gettimeofday;
    let t0 = now();
    let deps_mode = crate::provider_context::get_deps_mode(ctx);
    // Compute maximum fan-out of input dep set
    let deps = typing_deps::add_all_deps(&deps_mode, deps);
    let t1 = now();
    // See if it intersects in any way with dirty_master_deps
    let common_deps = dep_set::inter(&deps, dirty_master_deps);
    let t2 = now();
    // Expand the common part
    let more_deps = typing_deps::add_all_deps(&deps_mode, &common_deps);
    let t3 = now();
    // Remove the common part from dirty_master_deps (because after expanding it's
    // no longer dirty.
    let dirty_master_deps = dep_set::diff(dirty_master_deps, &common_deps);
    let t4 = now();
    // Translate the dependencies to files that need to be rechecked.
    let needs_recheck0 = naming_provider::get_files(ctx, &more_deps);
    let t5 = now();
    let needs_recheck = needs_recheck0.clone().relative_complement(rechecked_files.clone());
    let t6 = now();
    let size = needs_recheck.len();
    let env = if size == 0 {
        env
    } else {
        hh_logger::log(&format!("Adding {} files to recheck", size));
        let needs_recheck = env.needs_recheck.clone().union(needs_recheck);
        Env { needs_recheck, ..env }
    };
    let telemetry = telemetry::create();
    let telemetry = telemetry::int_("t1", ms_since(t1, t0), telemetry);
    let telemetry = telemetry::int_("t2", ms_since(t2, t1), telemetry);
    let telemetry = telemetry::int_("t3", ms_since(t3, t2), telemetry);
    let telemetry = telemetry::int_("t4", ms_since(t4, t3), telemetry);
    let telemetry = telemetry::int_("t5", ms_since(t5, t4), telemetry);
    let telemetry = telemetry::int_("t6", ms_since(t6, t5), telemetry);
    let telemetry = telemetry::int_("deps", dep_set::cardinal(&deps), telemetry);
    let telemetry = telemetry::int_("common_deps", dep_set::cardinal(&common_deps), telemetry);
    let telemetry = telemetry::int_("more_deps", dep_set::cardinal(&more_deps), telemetry);
    let telemetry = telemetry::int_("needs_recheck0", needs_recheck0.len() as isize, telemetry);
    let telemetry = telemetry::int_("needs_recheck", size as isize, telemetry);
    (env, dirty_master_deps, size, telemetry)
}

/// Update env.prechecked_files by adding to the recheck_files field of each
/// variant (`update_rechecked_files env rechecked`)
fn update_rechecked_files(env: Env, rechecked: &RPSet) -> Env {
    let add_rechecked = |dirty_deps: DirtyDeps| -> DirtyDeps {
        DirtyDeps {
            rechecked_files: rechecked.clone().union(dirty_deps.rechecked_files.clone()),
            ..dirty_deps
        }
    };
    let prechecked_files = match env.prechecked_files.clone() {
        PrecheckedFilesStatus::PrecheckedFilesDisabled => PrecheckedFilesStatus::PrecheckedFilesDisabled,
        PrecheckedFilesStatus::InitialTypechecking(dirty_deps) => {
            PrecheckedFilesStatus::InitialTypechecking(add_rechecked(dirty_deps))
        }
        PrecheckedFilesStatus::PrecheckedFilesReady(dirty_deps) => {
            PrecheckedFilesStatus::PrecheckedFilesReady(add_rechecked(dirty_deps))
        }
    };
    // (`Hack_event_logger.prechecked_update_rechecked`: a no-op in the
    // open-source build.)
    set(env, prechecked_files)
}

/// Update:
///   - env.needs_recheck,
///   - env.full_check_status,
///   - env.prechecked_files,
///   - env.init_env.why_needed_full_check
/// in esoteric ways (`update_after_recheck genv env rechecked ~start_time`)
pub fn update_after_recheck(
    genv: &Genv,
    env: Env,
    rechecked: &RPSet,
    start_time: f64,
) -> (Env, telemetry::T) {
    let ctx = provider_utils::ctx_from_server_env(&env);
    let telemetry = telemetry::create();
    let telemetry = telemetry::duration(Some("start"), start_time, None, telemetry);
    let telemetry = telemetry::int_("rechecked", rechecked.len() as isize, telemetry);
    let env = update_rechecked_files(env, rechecked);
    let telemetry = telemetry::duration(Some("end"), start_time, None, telemetry);
    match (&env.full_check_status, env.prechecked_files.clone()) {
        (
            FullCheckStatus::FullCheckDone,
            PrecheckedFilesStatus::InitialTypechecking(DirtyDeps {
                dirty_local_deps,
                dirty_master_deps,
                rechecked_files,
                clean_local_deps,
            }),
        ) => {
            assert!(dep_set::is_empty(&clean_local_deps));
            hh_logger::log("Finished rechecking dirty files, evaluating their fanout");
            // Take any prechecked files that could have been affected by local changes
            // and expand them too
            let (env, dirty_master_deps, size, _telemetry) = intersect_with_master_deps(
                &ctx,
                &dirty_local_deps,
                &dirty_master_deps,
                &rechecked_files,
                genv,
                env,
            );
            let env = if size == 0 {
                env
            } else {
                let full_check_status = FullCheckStatus::FullCheckStarted;
                let why_needed_full_check = Some(crate::server_env::init_telemetry::T {
                    reason: crate::server_env::init_telemetry::Reason::InitPrecheckedFanout,
                    telemetry: {
                        let t = telemetry::create();
                        let t = telemetry::float_("time", crate::rt::ocaml_unix::gettimeofday(), t);
                        let t = telemetry::string_(None, "reason", "prechecked_fanout", t);
                        telemetry::object_opt(
                            "prev",
                            env.init_env
                                .why_needed_full_check
                                .as_ref()
                                .map(server_env::init_telemetry::get),
                            t,
                        )
                    },
                });
                let init_env = server_env::InitEnv {
                    why_needed_full_check,
                    ..env.init_env.clone()
                };
                Env {
                    init_env,
                    full_check_status,
                    ..env
                }
            };
            let clean_local_deps = dirty_local_deps;
            let dirty_local_deps = dep_set::make();
            // (`Hack_event_logger.prechecked_evaluate_init`: a no-op.)
            let telemetry = telemetry::duration(Some("fanout_end"), start_time, None, telemetry);
            let telemetry = telemetry::int_("size", size as isize, telemetry);
            let env = set(
                env,
                PrecheckedFilesStatus::PrecheckedFilesReady(DirtyDeps {
                    dirty_local_deps,
                    dirty_master_deps,
                    rechecked_files,
                    clean_local_deps,
                }),
            );
            (env, telemetry)
        }
        _ => (env, telemetry),
    }
}

/// Update:
///   - env.needs_recheck,
///   - env.full_check_status,
///   - env.prechecked_files,
/// in esoteric ways (`update_after_local_changes genv env changes
/// ~start_time`)
pub fn update_after_local_changes(
    genv: &Genv,
    env: Env,
    changes: &dep_set::T,
    start_time: f64,
) -> (Env, telemetry::T) {
    let ctx = provider_utils::ctx_from_server_env(&env);
    let telemetry = telemetry::create();
    let telemetry = telemetry::duration(Some("start"), start_time, None, telemetry);
    let telemetry = telemetry::int_("changes", dep_set::cardinal(changes), telemetry);
    let (env, telemetry) = match env.prechecked_files.clone() {
        PrecheckedFilesStatus::PrecheckedFilesDisabled => {
            let telemetry = telemetry::string_(None, "mode", "disabled", telemetry);
            (env, telemetry)
        }
        PrecheckedFilesStatus::InitialTypechecking(dirty_deps) => {
            // Add [changes] dep set to [dirty_local_deps]
            let dirty_local_deps = dep_set::union(changes, &dirty_deps.dirty_local_deps);
            let env = set(
                env,
                PrecheckedFilesStatus::InitialTypechecking(DirtyDeps {
                    dirty_local_deps,
                    ..dirty_deps
                }),
            );
            let telemetry = telemetry::string_(None, "mode", "initial", telemetry);
            (env, telemetry)
        }
        PrecheckedFilesStatus::PrecheckedFilesReady(dirty_deps) => {
            // This is cleared during transition from Initial_typechecking to
            // Prechecked_files_ready and should not be populated again
            assert!(dep_set::is_empty(&dirty_deps.dirty_local_deps));
            let changes = dep_set::diff(changes, &dirty_deps.clean_local_deps);
            if dep_set::is_empty(&changes) {
                let telemetry = telemetry::string_(None, "mode", "ready_empty", telemetry);
                (env, telemetry)
            } else {
                let clean_local_deps = dep_set::union(&dirty_deps.clean_local_deps, &changes);
                let (env, dirty_master_deps, size, intersect_telemetry) = intersect_with_master_deps(
                    &ctx,
                    &changes,
                    &dirty_deps.dirty_master_deps,
                    &dirty_deps.rechecked_files,
                    genv,
                    env,
                );
                let env = if size == 0 {
                    env
                } else {
                    let full_check_status = match env.full_check_status {
                        FullCheckStatus::FullCheckDone => FullCheckStatus::FullCheckNeeded,
                        x => x,
                    };
                    Env {
                        full_check_status,
                        ..env
                    }
                };
                let telemetry = telemetry::string_(None, "mode", "ready_changes", telemetry);
                let telemetry = telemetry::int_("size", size as isize, telemetry);
                let telemetry = telemetry::int_("changes", dep_set::cardinal(&changes), telemetry);
                let telemetry = telemetry::int_(
                    "dirty_local_deps",
                    dep_set::cardinal(&dirty_deps.dirty_local_deps),
                    telemetry,
                );
                let telemetry = telemetry::int_(
                    "dirty_master_deps",
                    dep_set::cardinal(&dirty_deps.dirty_master_deps),
                    telemetry,
                );
                let telemetry =
                    telemetry::int_("dirty_master_deps_new", dep_set::cardinal(&dirty_master_deps), telemetry);
                let telemetry = telemetry::int_(
                    "rechecked_files",
                    dirty_deps.rechecked_files.len() as isize,
                    telemetry,
                );
                let telemetry = telemetry::int_(
                    "clean_local_deps",
                    dep_set::cardinal(&dirty_deps.clean_local_deps),
                    telemetry,
                );
                let telemetry =
                    telemetry::int_("clean_local_deps_new", dep_set::cardinal(&clean_local_deps), telemetry);
                let telemetry =
                    telemetry::int_("needs_recheck_new", env.needs_recheck.len() as isize, telemetry);
                let telemetry = telemetry::string_(
                    None,
                    "full_check_status",
                    &server_env::show_full_check_status(env.full_check_status),
                    telemetry,
                );
                let telemetry = telemetry::object_("intersect", intersect_telemetry, telemetry);
                // (`Hack_event_logger.prechecked_evaluate_incremental`: a no-op.)
                let env = set(
                    env,
                    PrecheckedFilesStatus::PrecheckedFilesReady(DirtyDeps {
                        dirty_master_deps,
                        clean_local_deps,
                        ..dirty_deps
                    }),
                );
                (env, telemetry)
            }
        }
    };
    let telemetry = telemetry::duration(Some("end"), start_time, None, telemetry);
    (env, telemetry)
}

/// `expand_all env`
pub fn expand_all(env: Env) -> Env {
    match env.prechecked_files.clone() {
        PrecheckedFilesStatus::PrecheckedFilesDisabled => env,
        PrecheckedFilesStatus::InitialTypechecking(dirty_deps)
        | PrecheckedFilesStatus::PrecheckedFilesReady(dirty_deps) => {
            let ctx = provider_utils::ctx_from_server_env(&env);
            let deps_mode = crate::provider_context::get_deps_mode(&ctx);
            let deps = typing_deps::add_all_deps(&deps_mode, &dirty_deps.dirty_master_deps);
            let needs_recheck = naming_provider::get_files(&ctx, &deps);
            let needs_recheck = needs_recheck.relative_complement(dirty_deps.rechecked_files.clone());
            let env = if needs_recheck.is_empty() {
                env
            } else {
                hh_logger::log(&format!(
                    "Adding {} files to recheck after expanding all master deps",
                    needs_recheck.len()
                ));
                let needs_recheck = env.needs_recheck.clone().union(needs_recheck);
                Env {
                    needs_recheck,
                    full_check_status: FullCheckStatus::FullCheckStarted,
                    ..env
                }
            };
            set(
                env,
                PrecheckedFilesStatus::PrecheckedFilesReady(DirtyDeps {
                    dirty_master_deps: dep_set::make(),
                    ..dirty_deps
                }),
            )
        }
    }
}
