// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_init.ml`, and of `Server_main.resolve_init_approach`
//! (plan §8 item 5: it lives here because `server_main.rs` is SRV's).
//!
//! Owned by **S1** (plan §3.1).
//!
//! `Full_init` and `Parse_only_init` are ported (the saving of
//! `--save-naming` is SS4's), and of `Saved_state_init` the open-source
//! failure of `Load_state_natively` with its fallback or exit
//! (`saved_state_init_error`). `Precomputed` (`--with-mini-state`) and
//! `Write_symbol_info*` (`--write-symbol-info`) exit as not ported (plan
//! D11, §6 #24; the monitor already refuses those options).

use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::server_args;
use crate::server_env;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_init_types::InitApproach;
use crate::server_init_types::LoadStateApproach;
use crate::server_init_types::LoadStateError;
use crate::server_lazy_init;
use crate::telemetry;

/// `init_result`
#[derive(Clone, Debug)]
pub enum InitResult {
    /// Loaded a saved saved state of this distance.
    LoadStateSucceeded(server_env::SavedStateRevsInfo),
    /// Loading error
    LoadStateFailed(String, telemetry::T),
    /// This option means we didn't even try to load a saved state
    LoadStateDeclined(String),
}

/// `Server_init_messages.messageSavedStateFailedFullInitDisabled` (the
/// open-source text, `server_init_messages.stubs.ml`).
const MESSAGE_SAVED_STATE_FAILED_FULL_INIT_DISABLED: &str = "Please retry. If the problem persists, check your saved state set up or open an issue on GitHub.";

/// `post_init genv (env, _t)` (`Shared_mem.SMTelemetry.init_done`: no
/// shared memory).
fn post_init(genv: &Genv, (env, _t): (Env, f64)) -> Env {
    let _ = genv;
    env
}

fn full_init(genv: &Genv, env: Env) -> (Env, InitResult) {
    (
        post_init(genv, server_lazy_init::full_init(genv, env)),
        InitResult::LoadStateDeclined("No saved-state requested (for lazy init)".to_string()),
    )
}

fn parse_only_init(genv: &Genv, env: Env) -> (Env, InitResult) {
    (
        server_lazy_init::parse_only_init(genv, env).0,
        InitResult::LoadStateDeclined(
            "No saved-state requested (for lazy parse-only init)".to_string(),
        ),
    )
}

/// `saved_state_init_error env genv ~do_indexing err`
fn saved_state_init_error(
    env: Env,
    genv: &Genv,
    do_indexing: bool,
    err: &LoadStateError,
) -> (Env, InitResult) {
    let crate::server_init_types::LoadStateVerboseError {
        message,
        auto_retry,
        telemetry,
    } = crate::server_init_types::load_state_error_to_verbose_string(err);
    let (next_step_descr, next_step, user_instructions) = if do_indexing {
        // ServerInit.Write_symbol_info_with_state will never fallback upon saved-state problems
        ("fatal", exit_status::T::FailedToLoadShouldAbort, None)
    } else if !genv.local_config.require_saved_state {
        // without "--config require_saved_state=true", we're happy to fallback to full init
        ("fallback", exit_status::T::NoError, None)
    } else if auto_retry {
        // The auto-retry means we'll exit in such a way that find_hh.sh will rerun us
        ("retry", exit_status::T::FailedToLoadShouldRetry, None)
    } else {
        // No fallbacks, no retries, no recourse! Let's explain this clearly to the user.
        (
            "fatal",
            exit_status::T::FailedToLoadShouldAbort,
            Some(MESSAGE_SAVED_STATE_FAILED_FULL_INIT_DISABLED),
        )
    };
    let user_message = format!("{} [{}]", message, next_step_descr);
    let user_message = match user_instructions {
        None => user_message,
        Some(user_instructions) => format!("{}\n\n{}", user_message, user_instructions),
    };
    // (`Hack_event_logger.load_state_exn`: a no-op.)
    hh_logger::log(&format!(
        "LOAD_STATE_EXN {}",
        telemetry::to_string(None, &telemetry)
    ));
    match next_step {
        exit_status::T::NoError => {
            // (`Cgroup_profiler.step_group "full_init"`: no cgroups.)
            let env = post_init(genv, server_lazy_init::full_init(genv, env));
            (env, InitResult::LoadStateFailed(user_message, telemetry))
        }
        _ => exit::exit(Some(user_message), Some(telemetry), None, next_step),
    }
}

fn saved_state_init(
    do_indexing: bool,
    genv: &Genv,
    env: Env,
    root: &crate::path::T,
    load_state_approach: &LoadStateApproach,
) -> (Env, InitResult) {
    let result =
        server_lazy_init::saved_state_init(do_indexing, load_state_approach, genv, env, root);
    match result {
        Ok(((env, t), saved_state_revs_info)) => {
            let env = post_init(genv, (env, t));
            (env, InitResult::LoadStateSucceeded(saved_state_revs_info))
        }
        Err((env, err)) => saved_state_init_error(env, genv, do_indexing, &err),
    }
}

/// Write symbol info for Glean (`write_symbol_info_init`): not ported.
fn write_symbol_info_init(
    genv: &Genv,
    env: Env,
    load_state: Option<&LoadStateApproach>,
) -> (Env, InitResult) {
    let _ = (genv, env, load_state);
    eprint!("hh_server: --write-symbol-info is not ported to Rust yet\n");
    exit::exit(None, None, None, exit_status::T::InputError)
}

/// `possibly_set_rust_provider_backend env genv`. (After the local config
/// is loaded, `rust_provider_backend` is false unless
/// `shm_use_sharded_hashtbl`; the backend of the OCaml has no counterpart.)
fn possibly_set_rust_provider_backend(env: &Env, genv: &Genv) {
    let _ = env;
    if genv.local_config.rust_provider_backend {
        hh_logger::log("ServerInit: using rust backend");
    }
}

/// `show_load_state_approach` (`[@@deriving show]`)
fn show_load_state_approach(a: &LoadStateApproach) -> String {
    match a {
        LoadStateApproach::Precomputed(info) => {
            format!("(Server_init_types.Precomputed {:?})", info)
        }
        LoadStateApproach::LoadStateNatively => "Server_init_types.Load_state_natively".to_string(),
    }
}

/// `show_init_approach` (`[@@deriving show]`)
pub fn show_init_approach(a: &InitApproach) -> String {
    match a {
        InitApproach::FullInit => "Server_init_types.Full_init".to_string(),
        InitApproach::ParseOnlyInit => "Server_init_types.Parse_only_init".to_string(),
        InitApproach::SavedStateInit(l) => format!(
            "(Server_init_types.Saved_state_init {})",
            show_load_state_approach(l)
        ),
        InitApproach::WriteSymbolInfo => "Server_init_types.Write_symbol_info".to_string(),
        InitApproach::WriteSymbolInfoWithState(l) => format!(
            "(Server_init_types.Write_symbol_info_with_state {})",
            show_load_state_approach(l)
        ),
    }
}

/// `init ~init_approach genv env` (plan §8 item 5: the approach is an
/// argument).
pub fn init(genv: &Genv, env: Env, init_approach: InitApproach) -> (Env, InitResult) {
    // (The context the init fills, with the dependency mode of `env`:
    // `Provider_utils.ctx_from_server_env`, made the context of the
    // providers.)
    let env = crate::server_type_check::with_ctx_of_env(env);
    possibly_set_rust_provider_backend(&env, genv);
    hh_logger::log(&format!(
        "ServerInit: init_approach={}",
        show_init_approach(&init_approach)
    ));
    let root = server_args::root(&genv.options);
    // (`Cgroup_profiler.step_group init_method_name ~log:true`: no cgroups.)
    match &init_approach {
        InitApproach::FullInit => full_init(genv, env),
        InitApproach::SavedStateInit(load_state_approach) => {
            saved_state_init(false, genv, env, &root, load_state_approach)
        }
        InitApproach::ParseOnlyInit => parse_only_init(genv, env),
        InitApproach::WriteSymbolInfo => write_symbol_info_init(genv, env, None),
        InitApproach::WriteSymbolInfoWithState(load_state_approach) => {
            write_symbol_info_init(genv, env, Some(load_state_approach))
        }
    }
}

/// `Server_main.resolve_init_approach genv` (plan §8 item 5; ported by SRV
/// from `server_main.ml:968`, S1 owns it).
///
/// Rules for whether+how to load saved-state...
/// 1. If hh.conf lacks "use_mini_state = true", then don't load it.
/// 2. If hh_server --no-load, then don't load it.
/// 3. If hh_server --save-mini or -s, then save but don't load it.
/// 4. If "hh_server --with-mini-state", then load the one specified there!
/// 5. If hh.conf lacks "load_state_natively_v4", then don't load it
/// 6. Otherwise, load it normally!
pub fn resolve_init_approach(genv: &Genv) -> (crate::server_init_types::InitApproach, String) {
    use crate::server_args;
    use crate::server_init_types::InitApproach;
    use crate::server_init_types::LoadStateApproach;
    let (approach, name) = if server_args::save_naming_filename(&genv.options).is_some() {
        (InitApproach::ParseOnlyInit, "Server_args_saving_naming")
    } else if server_args::no_load(&genv.options) {
        (InitApproach::FullInit, "Server_args_no_load")
    } else if !genv.local_config.use_saved_state
        && server_args::write_symbol_info(&genv.options).is_none()
    {
        (InitApproach::FullInit, "Local_config_saved_state_disabled")
    } else if server_args::write_symbol_info(&genv.options).is_some() {
        match (
            genv.local_config.use_saved_state_when_indexing,
            server_args::with_saved_state(&genv.options),
        ) {
            (false, None) => (
                InitApproach::WriteSymbolInfo,
                "Server_args_writing_symbol_info",
            ),
            (true, None) => (
                InitApproach::WriteSymbolInfoWithState(LoadStateApproach::LoadStateNatively),
                "Server_args_writing_symbol_info_load_native",
            ),
            (_, Some(server_args::SavedStateTarget::SavedStateTargetInfo(target))) => (
                InitApproach::WriteSymbolInfoWithState(LoadStateApproach::Precomputed(target)),
                "Server_args_writing_symbol_info_precomputed",
            ),
        }
    } else {
        match (
            genv.local_config.load_state_natively,
            server_args::with_saved_state(&genv.options),
        ) {
            (_, Some(server_args::SavedStateTarget::SavedStateTargetInfo(target))) => (
                InitApproach::SavedStateInit(LoadStateApproach::Precomputed(target)),
                "Precomputed",
            ),
            (false, None) => (InitApproach::FullInit, "No_native_loading_or_precomputed"),
            // Use native loading only if the config specifies a load script,
            // and the local config prefers native.
            (true, None) => (
                InitApproach::SavedStateInit(LoadStateApproach::LoadStateNatively),
                "Load_state_natively",
            ),
        }
    };
    (approach, name.to_string())
}
