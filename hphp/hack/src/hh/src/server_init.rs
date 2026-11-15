// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_init.ml`.
//!
//! `Full_init`, `Parse_only_init` and `Saved_state_init` are ported (with the
//! open-source failure of `Load_state_natively` and its fallback or exit,
//! `saved_state_init_error`), and `Write_symbol_info*` (`--write-symbol-info`:
//! the Glean indexer).

use crate::cgroup_profiler;
use crate::exit;
use crate::format;
use crate::exit_status;
use crate::hh_logger;
use crate::server_args;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_init_messages;
use crate::server_init_types::InitApproach;
use crate::server_init_types::InitResult;
use crate::server_init_types::LoadStateApproach;
use crate::server_init_types::LoadStateError;
use crate::server_lazy_init;
use crate::telemetry;

/// `post_init genv (env, _t)` (`Shared_mem.SMTelemetry.init_done`: no
/// shared memory).
fn post_init(genv: &Genv, (env, _t): (Env, f64)) -> Env {
    let _ = genv;
    env
}

fn full_init(genv: &Genv, env: Env, profiling: &cgroup_profiler::StepGroup) -> (Env, InitResult) {
    (
        post_init(genv, server_lazy_init::full_init(genv, env, profiling)),
        InitResult::LoadStateDeclined("No saved-state requested (for lazy init)".to_string()),
    )
}

fn parse_only_init(genv: &Genv, env: Env, profiling: &cgroup_profiler::StepGroup) -> (Env, InitResult) {
    (
        server_lazy_init::parse_only_init(genv, env, profiling).0,
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
            Some(server_init_messages::MESSAGE_SAVED_STATE_FAILED_FULL_INIT_DISABLED),
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
            let env = cgroup_profiler::step_group("full_init", true, |profiling| {
                post_init(genv, server_lazy_init::full_init(genv, env, profiling))
            });
            (env, InitResult::LoadStateFailed(user_message, telemetry))
        }
        _ => exit::exit(Some(user_message), Some(telemetry), None, None, next_step),
    }
}

fn saved_state_init(
    do_indexing: bool,
    genv: &Genv,
    env: Env,
    root: &crate::path::T,
    load_state_approach: &LoadStateApproach,
    profiling: &cgroup_profiler::StepGroup,
) -> (Env, InitResult) {
    let result =
        server_lazy_init::saved_state_init(do_indexing, load_state_approach, genv, env, root, profiling);
    match result {
        Ok(((env, t), saved_state_revs_info)) => {
            let env = post_init(genv, (env, t));
            (env, InitResult::LoadStateSucceeded(saved_state_revs_info))
        }
        Err((env, err)) => saved_state_init_error(env, genv, do_indexing, &err),
    }
}

/// Write symbol info for Glean
fn write_symbol_info_init(
    genv: &Genv,
    env: Env,
    load_state: Option<&LoadStateApproach>,
    profiling: &cgroup_profiler::StepGroup,
) -> (Env, InitResult) {
    match load_state {
        None => (
            post_init(genv, server_lazy_init::write_symbol_info_full_init(genv, env, profiling)),
            InitResult::LoadStateDeclined("Write Symobl info state".to_string()),
        ),
        Some(load_state_approach) => {
            let root = server_args::root(&genv.options);
            saved_state_init(true, genv, env, &root, load_state_approach, profiling)
        }
    }
}

/// `possibly_set_rust_provider_backend env genv`. (After the local config
/// is loaded, `rust_provider_backend` is false unless
/// `shm_use_sharded_hashtbl` and not `populate_member_heaps`.)
fn possibly_set_rust_provider_backend(env: &Env, genv: &Genv) {
    let _ = env;
    set_rust_provider_backend(&genv.local_config);
}

/// The body of [`possibly_set_rust_provider_backend`] (`hh_server --check`
/// runs it too). `Hh_server_provider_backend.make` has no counterpart: see
/// `crate::provider_backend`.
pub fn set_rust_provider_backend(local_config: &crate::server_local_config::T) {
    if local_config.rust_provider_backend {
        hh_logger::log("ServerInit: using rust backend");
        crate::provider_backend::set_rust_backend();
    }
}

/// `pp_saved_state_target_info` (`Cli_args_sig.Types`, `[@@deriving
/// show]`)
fn pp_saved_state_target_info(fmt: &mut format::Formatter, info: &server_args::SavedStateTargetInfo) {
    let s = crate::rt::ocaml_printf::sprintf_s;
    let fields: [(&str, &dyn Fn(&mut format::Formatter)); 7] = [
        ("Cli_args_sig.Types.changes", &|fmt| crate::utils::pp_large_list(crate::relative_path::pp, fmt, &info.changes)),
        ("naming_changes", &|fmt| crate::utils::pp_large_list(crate::relative_path::pp, fmt, &info.naming_changes)),
        ("corresponding_base_revision", &|fmt| {
            format::pp_print_string(fmt, &s(&info.corresponding_base_revision))
        }),
        ("deptable_fn", &|fmt| format::pp_print_string(fmt, &s(&info.deptable_fn))),
        ("compressed_deptable_fn", &|fmt| match &info.compressed_deptable_fn {
            None => format::pp_print_string(fmt, "None"),
            Some(x) => {
                format::pp_print_string(fmt, "(Some ");
                format::pp_print_string(fmt, &s(x));
                format::pp_print_string(fmt, ")");
            }
        }),
        ("prechecked_changes", &|fmt| crate::utils::pp_large_list(crate::relative_path::pp, fmt, &info.prechecked_changes)),
        ("naming_table_path", &|fmt| format::pp_print_string(fmt, &s(&info.naming_table_path))),
    ];
    // ppx_deriving's record: `"@[<2>{ "`, the fields separated by `";@ "`,
    // then `"@ }@]"`; a field is `"@[%s =@ "`, its value, `"@]"`.
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "{ ");
    for (i, (name, pp_value)) in fields.iter().enumerate() {
        if i > 0 {
            format::pp_print_char(fmt, ';');
            format::pp_print_space(fmt);
        }
        format::pp_open_box(fmt, 0);
        format::pp_print_string(fmt, name);
        format::pp_print_string(fmt, " =");
        format::pp_print_space(fmt);
        pp_value(fmt);
        format::pp_close_box(fmt);
    }
    format::pp_print_space(fmt);
    format::pp_print_char(fmt, '}');
    format::pp_close_box(fmt);
}

/// A constructor with an argument, as ppx_deriving prints it:
/// `"(@[<2>C@ "`, the argument, `"@])"`.
fn pp_constructor(fmt: &mut format::Formatter, name: &str, pp_arg: &dyn Fn(&mut format::Formatter)) {
    format::pp_print_string(fmt, "(");
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, name);
    format::pp_print_space(fmt);
    pp_arg(fmt);
    format::pp_close_box(fmt);
    format::pp_print_string(fmt, ")");
}

/// `pp_load_state_approach` (`[@@deriving show]`)
fn pp_load_state_approach(fmt: &mut format::Formatter, a: &LoadStateApproach) {
    match a {
        LoadStateApproach::Precomputed(info) => pp_constructor(fmt, "Server_init_types.Precomputed", &|fmt| {
            pp_saved_state_target_info(fmt, info)
        }),
        LoadStateApproach::LoadStateNatively => format::pp_print_string(fmt, "Server_init_types.Load_state_natively"),
    }
}

/// `show_init_approach` (`[@@deriving show]`)
pub fn show_init_approach(a: &InitApproach) -> String {
    format::asprintf(|fmt| match a {
        InitApproach::FullInit => format::pp_print_string(fmt, "Server_init_types.Full_init"),
        InitApproach::ParseOnlyInit => format::pp_print_string(fmt, "Server_init_types.Parse_only_init"),
        InitApproach::SavedStateInit(l) => {
            pp_constructor(fmt, "Server_init_types.Saved_state_init", &|fmt| pp_load_state_approach(fmt, l))
        }
        InitApproach::WriteSymbolInfo => format::pp_print_string(fmt, "Server_init_types.Write_symbol_info"),
        InitApproach::WriteSymbolInfoWithState(l) => pp_constructor(
            fmt,
            "Server_init_types.Write_symbol_info_with_state",
            &|fmt| pp_load_state_approach(fmt, l),
        ),
    })
}

/// The line of `init` that names the approach (`hh_server --check` logs it
/// too).
pub fn log_init_approach(init_approach: &InitApproach) {
    hh_logger::log(&format!(
        "ServerInit: init_approach={}",
        show_init_approach(init_approach)
    ));
}

/// `init ~init_approach genv env` (the approach is an argument): parse,
/// name, typecheck the next set of files, refresh the environment and update
/// the many shared heaps.
pub fn init(genv: &Genv, env: Env, init_approach: InitApproach) -> (Env, InitResult) {
    // (The context the init fills, with the dependency mode of `env`:
    // `Provider_utils.ctx_from_server_env`, made the context of the
    // providers.)
    let env = crate::server_type_check::with_ctx_of_env(env);
    possibly_set_rust_provider_backend(&env, genv);
    log_init_approach(&init_approach);
    let root = server_args::root(&genv.options);
    let init_method_name = match &init_approach {
        InitApproach::FullInit => "full_init",
        InitApproach::SavedStateInit(_) => "saved_state_init",
        InitApproach::ParseOnlyInit => "parse_only_init",
        InitApproach::WriteSymbolInfo => "write_symbol_info_init",
        InitApproach::WriteSymbolInfoWithState(_) => "write_symbol_info_with_state",
    };
    cgroup_profiler::step_group(init_method_name, true, |profiling| match &init_approach {
        InitApproach::FullInit => full_init(genv, env, profiling),
        InitApproach::SavedStateInit(load_state_approach) => {
            saved_state_init(false, genv, env, &root, load_state_approach, profiling)
        }
        InitApproach::ParseOnlyInit => parse_only_init(genv, env, profiling),
        InitApproach::WriteSymbolInfo => write_symbol_info_init(genv, env, None, profiling),
        InitApproach::WriteSymbolInfoWithState(load_state_approach) => {
            write_symbol_info_init(genv, env, Some(load_state_approach), profiling)
        }
    })
}
