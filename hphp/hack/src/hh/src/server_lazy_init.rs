// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_lazy_init.ml`, the parts in scope: `full_init`
//! (`:985`), `parse_only_init` (`:1028`), `initialize_naming_table`
//! (`:868`), and of `saved_state_init` (`:1432`) the path the open-source
//! build takes with `Load_state_natively` (the loader of
//! `State_loader_futures` is a stub that fails: "Not implemented").
//!
//! Owned by **S1** (plan §3.1), then **SS3** (plan §7.3), who ports the
//! saved-state paths (`use_precomputed_state_exn`, `post_saved_state_initialization`,
//! ...): `Precomputed` exits as not ported meanwhile (plan D11).
//!
//! Lazy init: during lazy initialization, hh_server tries to do as little
//! work as possible. The init_from_saved_state behavior is this:
//!
//!   Load from saved state -> Parse dirty files -> Naming -> Dirty Typecheck
//!
//! The full_init behavior is this: (similar to eager init, but with lazy decl)
//!
//!   Full Parsing -> Naming -> Full Typecheck (with lazy decl)

use crate::direct_decl_service::DeclMode;
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
use crate::server_env::InitTelemetry;
use crate::server_env::InitTelemetryReason;
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
                DeclMode::Cached
            } else {
                DeclMode::Normal
            },
            "lazy.nt.parsing",
        );
        if do_naming {
            server_init_common::update_reverse_naming_table_from_env_and_get_duplicate_name_errors(
                env,
                t,
                "lazy.nt.do_naming.naming",
            )
        } else {
            (env, t)
        }
    })
}

/// If we fail to load a saved state, fall back to typechecking everything
/// (`full_init genv env`).
pub fn full_init(genv: &Genv, env: Env) -> (Env, f64) {
    let init_telemetry = InitTelemetry {
        reason: InitTelemetryReason::InitLazyFull,
        telemetry: telemetry::float_("start_time", gettimeofday(), telemetry::create()),
    };
    let existing_name_count = naming_table::fold(&env.naming_table, 0isize, |_, _, i| i + 1);
    if existing_name_count > 0 {
        let desc = "full_init_naming_not_empty";
        hh_logger::log(&format!(
            "INVARIANT_VIOLATION_BUG [{}] count={}",
            desc, existing_name_count
        ));
        // (`Hack_event_logger.invariant_violation_bug`: a no-op.)
    }
    hh_logger::log("full init");
    let (env, t) = initialize_naming_table("full initialization", None, true, true, genv, env);
    server_init_common::validate_no_errors(&env.diagnostics);
    let fnl = naming_table::get_files(&env.naming_table);
    server_init_common::defer_or_do_type_check(
        genv,
        env,
        fnl,
        init_telemetry,
        t,
        "lazy.full.type_check",
    )
}

/// `parse_only_init genv env`
pub fn parse_only_init(genv: &Genv, env: Env) -> (Env, f64) {
    initialize_naming_table("parse-only initialization", None, false, false, genv, env)
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

/// `saved_state_init ~do_indexing ~load_state_approach genv env root`.
/// Only the open-source failure of `Load_state_natively` is ported: the
/// error comes back with the environment (the OCaml keeps its `env` for the
/// fallback to a full init). `Precomputed` (`--with-mini-state`) exits as
/// not ported (plan D11; the monitor refuses the option before that).
pub fn saved_state_init(
    do_indexing: bool,
    load_state_approach: &LoadStateApproach,
    genv: &Genv,
    env: Env,
    root: &path::T,
) -> Result<((Env, f64), server_env::SavedStateRevsInfo), (Env, LoadStateError)> {
    let _ = do_indexing;
    // `check_credentials genv`: `Security.check_credentials` is `Ok
    // Checks_skipped` in the open-source build (and the event logger a
    // no-op).
    server_progress::write(None, None, "loading saved state");
    let _t = gettimeofday();
    let state_result = match load_state_approach {
        LoadStateApproach::Precomputed(_) => {
            eprint!("hh_server: --with-mini-state is not ported to Rust yet\n");
            exit::exit(None, None, None, exit_status::T::InputError)
        }
        LoadStateApproach::LoadStateNatively => download_and_load_state_exn(genv, root),
    };
    // (`Hack_event_logger.saved_state_download_and_load_done`: a no-op.)
    Err((env, state_result))
}
