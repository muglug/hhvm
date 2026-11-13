// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_env_build.ml`: building `genv` and `env`.
//!
//! Owned by **SRV** (plan §3.1).
//!
//! `make_genv` takes the number of workers (the threads of the pool)
//! instead of the workers. `make_env` also takes the root, for the `Ctx`
//! of the environment (the OCaml's context is global).

use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::Ordering;

use crate::ctx::Ctx;
use crate::diagnostics_state;
use crate::naming_table;
use crate::relative_path;
use crate::server_args;
use crate::server_config;
use crate::server_env::Env;
use crate::server_env::FullCheckStatus;
use crate::server_env::Genv;
use crate::server_env::InitEnv;
use crate::server_env::PrecheckedFilesStatus;
use crate::server_env::recheck_loop_stats;
use crate::server_local_config;
use crate::server_local_config_load;
use crate::server_notifier;
use crate::typing_deps;

/// `make_genv options config local_config workers`. A failure of the
/// notifier's `init` is raised (a panic with the `Watchman` exception), as
/// the OCaml lets it go up to `Server_utils.with_exit_on_exception`.
pub fn make_genv(
    options: server_args::Options,
    config: server_config::T,
    local_config: server_local_config::T,
    num_workers: isize,
) -> Genv {
    typing_deps::trace.store(!server_args::check_mode(&options), Ordering::SeqCst);
    let (notifier, _indexer) =
        match server_notifier::init(&options, &local_config, num_workers) {
            Ok(r) => r,
            Err(e) => std::panic::panic_any(e),
        };
    Genv {
        options,
        config,
        local_config,
        notifier,
        num_workers,
    }
}

/// `default_genv` (useful in testing code)
pub fn default_genv() -> Genv {
    Genv {
        options: server_args::default_options(""),
        config: server_config::default_config(),
        local_config: server_local_config_load::default(),
        notifier: server_notifier::init_null(),
        num_workers: 1,
    }
}

/// `make_env ~init_id ~deps_mode ?diagnostics config`, with the root of
/// the context.
pub fn make_env(
    init_id: &str,
    deps_mode: typing_deps::mode::T,
    diagnostics: Option<diagnostics_state::T>,
    config: &server_config::T,
    root: &Path,
) -> Env {
    let ctx = match Ctx::new(root, server_config::typechecker_options(config)) {
        Ok(ctx) => Arc::new(ctx),
        Err(e) => panic!("{:#}", e),
    };
    Env {
        ctx,
        naming_table: naming_table::empty(),
        deps_mode,
        diagnostics: diagnostics.unwrap_or_default(),
        failed_naming: relative_path::set::T::new(),
        last_command_time: 0.0,
        last_notifier_check_time: 0.0,
        last_idle_job_time: 0.0,
        disk_needs_parsing: relative_path::set::T::new(),
        clock: None,
        needs_phase2_redecl: relative_path::set::T::new(),
        needs_recheck: relative_path::set::T::new(),
        full_check_status: FullCheckStatus::FullCheckDone,
        changed_files: relative_path::set::T::new(),
        prechecked_files: PrecheckedFilesStatus::PrecheckedFilesDisabled,
        interrupt_handlers: Arc::new(|_genv, _env| vec![]),
        nonpersistent_client_pending_command_needs_full_check: None,
        why_needs_server_type_check: ("init".to_string(), "".to_string()),
        init_env: InitEnv {
            approach_name: "".to_string(),
            init_error: None,
            init_id: init_id.to_string(),
            init_start_t: crate::rt::ocaml_unix::gettimeofday(),
            init_type: "".to_string(),
            why_needed_full_check: None,
            recheck_id: None,
            saved_state_revs_info: None,
        },
        last_recheck_loop_stats: recheck_loop_stats::empty("<none>"),
        last_recheck_loop_stats_for_actual_work: None,
    }
}
