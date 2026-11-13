// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_check.ml`. See `hh/PORTING.md`.
//!
//! Owned by **STATUS** (plan §3.1), then E1 and E2 (plan §7.4).
//!
//! Ported: `connect`, `connect_then_close`, `rpc_with_connection`, `rpc`,
//! `main`, and the arms of `main_internal` for `MODE_STATUS` (the default,
//! `check`, `--status`, `--json`, `--jsonl`, with or without streaming),
//! `MODE_LIST_FILES` and `MODE_STATS`. Every other mode is the temporary
//! stand-in of plan §3.4: `hh_client: <MODE> is not ported to Rust yet` on
//! stderr and `Exit_with Input_error` (exit 10), before connecting. The
//! phase-2 owners replace an arm each with its OCaml body (the arms are in
//! the OCaml's order).
//!
//! - `Lwt` is gone; `Lwt_utils.run_main f` is `f ()`.
//! - The exceptions are `Result`s ([`hh_client::Exn`]); `main`'s `try ...
//!   with exn` also catches panics, as OCaml's catches every exception.
//! - The SIGINT handler (`hh_client.ml`) raises `Exit_with Interrupted` in
//!   OCaml, which `main`'s handler catches: here `main` installs, while it
//!   runs, what that handler does with it ([`hh_client::set_interrupt_catch`]).
//! - `Hack_event_logger` calls are no-ops in the OSS build and are not made;
//!   so is `flush_event_logger` (`Event_logger_lwt.flush`).

use std::panic::AssertUnwindSafe;
use std::sync::Arc;
use std::sync::Mutex;

use crate::client_check_status;
use crate::client_check_status::PartialTelemetryRef;
use crate::client_connect;
use crate::client_env;
use crate::client_env::ClientMode;
use crate::exit;
use crate::exit_status;
use crate::filter_diagnostics;
use crate::hh_client;
use crate::hh_client::Exn;
use crate::hh_logger;
use crate::rt::ocaml_str;
use crate::server_command_types;
use crate::server_command_types::ResultOf;
use crate::server_config;
use crate::server_local_config;
use crate::stats;
use crate::telemetry;

/// `connect ?use_priority_pipe ?do_post_handoff_handshake
/// args`
pub fn connect(
    use_priority_pipe: Option<bool>,
    do_post_handoff_handshake: Option<bool>,
    args: &client_env::ClientCheckEnv,
) -> Result<client_connect::Conn, Exn> {
    let use_priority_pipe = use_priority_pipe.unwrap_or(false);
    let do_post_handoff_handshake = do_post_handoff_handshake.unwrap_or(true);
    let client_env::ClientCheckEnv {
        root,
        from,
        autostart,
        force_dormant_start,
        deadline,
        no_load,
        watchman_debug_logging,
        show_spinner,
        ignore_hh_version,
        save_64bit,
        save_human_readable_64bit_dep_map,
        saved_state_ignore_hhconfig,
        prechecked,
        mini_state,
        config,
        allow_non_opt_build,
        custom_hhi_path,
        custom_telemetry_data,
        preexisting_warnings,
        reason: _,
        error_format: _,
        paths: _,
        max_errors: _,
        mode: _,
        output_json: _,
        output_jsonl: _,
        sort_results: _,
        stdin_name: _,
        desc: _,
        is_interactive: _,
        warning_switches: _,
        dump_config: _,
    } = args;
    let show_spinner = *show_spinner;
    // `Client_messages.angery_reaccs_only ()` is `false` in the OSS build.
    let angery_reaccs_only = false;
    Ok(client_connect::connect(&client_connect::Env {
        root: root.clone(),
        from: from.clone(),
        autostart: *autostart,
        force_dormant_start: *force_dormant_start,
        deadline: *deadline,
        no_load: *no_load,
        watchman_debug_logging: *watchman_debug_logging,
        progress_callback: Arc::new(move |s| {
            crate::client_spinner::report(show_spinner, angery_reaccs_only, s)
        }),
        do_post_handoff_handshake,
        ignore_hh_version: *ignore_hh_version,
        save_64bit: save_64bit.clone(),
        save_human_readable_64bit_dep_map: save_human_readable_64bit_dep_map.clone(),
        saved_state_ignore_hhconfig: *saved_state_ignore_hhconfig,
        use_priority_pipe,
        prechecked: *prechecked,
        mini_state: mini_state.clone(),
        config: config.clone(),
        custom_hhi_path: custom_hhi_path.clone(),
        custom_telemetry_data: custom_telemetry_data.clone(),
        allow_non_opt_build: *allow_non_opt_build,
        preexisting_warnings: *preexisting_warnings,
    })?)
}

/// `connect_then_close args`
pub fn connect_then_close(
    args: &client_env::ClientCheckEnv,
) -> Result<(), Exn> {
    let client_connect::Conn {
        channels: (ic, oc),
        ..
    } = connect(Some(true), Some(false), args)?;
    // `Out_channel.close oc`: the socket is closed (`ic` and `oc` are one
    // descriptor in OCaml, two here: both are closed).
    drop(oc);
    drop(ic);
    // The connection is derived from [Unix.open_connection]. Its docs explain:
    // "The two channels returned by [open_connection] share a descriptor
    //  to a socket.  Therefore, when the connection is over, you should
    //  call {!Stdlib.close_out} on the output channel, which will also close
    //  the underlying socket.  Do not call {!Stdlib.close_in} on the input
    //  channel; it will be collected by the GC eventually."
    Ok(())
}

/// `rpc args command` (with `rpc_with_connection`,
/// whose `call` it is the only caller of here).
pub fn rpc<A: ResultOf>(
    args: &client_env::ClientCheckEnv,
    command: server_command_types::T,
) -> Result<(A, telemetry::T), Exn> {
    // `rpc_with_connection`
    let use_priority_pipe = server_command_types::use_priority_pipe(&command);
    let conn = || connect(Some(use_priority_pipe), None, args);
    // `call conn ~desc:args.desc command`
    let conn = conn()?;
    let (result, telemetry) = client_connect::rpc(&conn, &args.desc, command)?;
    Ok((result, telemetry))
}

/// `Str.regexp` of a configured pattern (a malformed one raises `Failure`).
fn str_regexp(s: &str) -> ocaml_str::Regexp {
    match ocaml_str::regexp(s) {
        Ok(re) => re,
        Err(ocaml_str::Failure(message)) => panic!("Failure: {}", message),
    }
}

/// `Filter_diagnostics.Filter.make ~default_all ~generated_files
/// args.warning_switches`, as every mode builds it.
fn error_filter(
    config: &server_config::T,
    local_config: &server_local_config::T,
    args: &client_env::ClientCheckEnv,
) -> filter_diagnostics::filter::T {
    filter_diagnostics::filter::make(
        local_config.warnings_default_all,
        server_config::warnings_generated_files(config)
            .iter()
            .map(|s| str_regexp(s))
            .collect(),
        args.warning_switches.clone(),
    )
}

/// The temporary stand-in for the modes that are not ported yet (plan
/// §3.4): a message, then `Exit_with Input_error`, before connecting.
fn not_ported(mode: &ClientMode) -> Result<(exit_status::T, telemetry::T), Exn> {
    eprintln!(
        "hh_client: {} is not ported to Rust yet",
        client_env::variants_of_client_mode::to_name(mode)
    );
    Err(Exn::ExitWith(exit_status::T::InputError))
}

/// `main_internal args config local_config partial_telemetry_ref`
pub fn main_internal(
    args: &client_env::ClientCheckEnv,
    config: &server_config::T,
    local_config: &server_local_config::T,
    partial_telemetry_ref: &PartialTelemetryRef,
) -> Result<(exit_status::T, telemetry::T), Exn> {
    let connect_then_close = || connect_then_close(args);
    match &args.mode {
        ClientMode::MODESTATUS => {
            let prechecked = args.prechecked.unwrap_or(true);
            let ((), telemetry1): ((), telemetry::T) = if prechecked {
                ((), telemetry::create())
            } else {
                rpc(args, server_command_types::T::NOPRECHECKEDFILES)?
            };
            let error_filter = error_filter(config, local_config, args);
            // We don't do streaming errors under [output_json]: our contract
            // with the outside world is that if a caller uses [output_json] then they
            // will never see [Exit_status.Typecheck_restarted], which streaming might show.
            //
            // We don't do streaming errors under [not prechecked]. That's because the
            // [go_streaming] contract is to report on a typecheck that reflects all *file*
            // changes up until now; it has no guarantee that the typecheck will reflects our
            // preceding call to ServerCommandTypes.NO_PRECHECKED_FILES.
            //
            // (`Sandcastle.is_sandcastle ()` is `false` in the OSS build.)
            let use_streaming =
                local_config.consume_streaming_errors && !args.output_json && prechecked;
            if use_streaming {
                let mut connect_then_close = connect_then_close;
                client_check_status::go_streaming(
                    args,
                    local_config,
                    &error_filter,
                    partial_telemetry_ref,
                    &mut connect_then_close,
                )
            } else {
                let (status, telemetry): (server_command_types::server_status::T, _) = rpc(
                    args,
                    server_command_types::T::STATUS {
                        max_errors: args.max_errors,
                        error_filter,
                    },
                )?;
                let last_recheck_stats = status.last_recheck_stats.clone();
                let exit_status = client_check_status::go(
                    status,
                    args.error_format,
                    args.is_interactive,
                    args.output_json,
                    args.output_jsonl,
                    args.max_errors,
                );
                let telemetry = telemetry::bool_("streaming", false, telemetry);
                let telemetry = telemetry::object_("no_prechecked", telemetry1, telemetry);
                let telemetry = telemetry::object_opt("last_recheck_stats", last_recheck_stats, telemetry);
                Ok((exit_status, telemetry))
            }
        }
        mode @ ClientMode::MODESTATUSSINGLE(_) => not_ported(mode),
        mode @ ClientMode::MODELOGERRORS(_) => not_ported(mode),
        ClientMode::MODELISTFILES => {
            let (infol, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::LISTFILESWITHERRORS)?;
            for s in &infol {
                print!("{}\n", s);
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        mode @ ClientMode::MODEFINDCLASSREFS(_) => not_ported(mode),
        mode @ ClientMode::MODEFINDREFS(_) => not_ported(mode),
        mode @ ClientMode::MODEGOTOIMPLCLASS(_) => not_ported(mode),
        mode @ ClientMode::MODEGOTOIMPLMETHOD(_) => not_ported(mode),
        mode @ ClientMode::MODEHACKTONOTEBOOK => not_ported(mode),
        mode @ ClientMode::MODEIDEFINDREFSBYSYMBOL(_) => not_ported(mode),
        mode @ ClientMode::MODEIDEGOTOIMPLBYSYMBOL(_) => not_ported(mode),
        mode @ ClientMode::MODEDUMPSYMBOLINFO(_) => not_ported(mode),
        mode @ ClientMode::MODERENAME(..) => not_ported(mode),
        mode @ ClientMode::MODEIDERENAMEBYSYMBOL(_) => not_ported(mode),
        mode @ ClientMode::MODEIDENTIFYSYMBOL(_) => not_ported(mode),
        mode @ (ClientMode::MODEIDENTIFYSYMBOL1(_)
        | ClientMode::MODEIDENTIFYSYMBOL2(_)
        | ClientMode::MODEIDENTIFYSYMBOL3(_)) => not_ported(mode),
        mode @ ClientMode::MODETYPEATPOS(_) => not_ported(mode),
        mode @ ClientMode::MODEINFERDYNAMIC(..) => not_ported(mode),
        mode @ ClientMode::MODEENFORCEMENTATPOSBATCH(_) => not_ported(mode),
        mode @ ClientMode::MODETYPEATPOSBATCH(_) => not_ported(mode),
        mode @ ClientMode::MODEISSUBTYPE => not_ported(mode),
        mode @ ClientMode::MODETYPEERRORATPOS(_) => not_ported(mode),
        mode @ ClientMode::MODETASTHOLES(_) => not_ported(mode),
        mode @ ClientMode::MODETASTHOLESBATCH(_) => not_ported(mode),
        mode @ ClientMode::MODEFUNDEPSATPOSBATCH(_) => not_ported(mode),
        mode @ ClientMode::MODEDEPSOUTATPOSBATCH(_) => not_ported(mode),
        mode @ (ClientMode::MODEOUTLINE | ClientMode::MODEOUTLINE2) => not_ported(mode),
        mode @ ClientMode::MODEOUTLINEFORAGENTS(_) => not_ported(mode),
        mode @ ClientMode::MODEMETHODJUMPCHILDREN(_) => not_ported(mode),
        mode @ ClientMode::MODEMETHODJUMPANCESTORS(..) => not_ported(mode),
        mode @ ClientMode::MODEMETHODJUMPANCESTORSBATCH(..) => not_ported(mode),
        mode @ ClientMode::MODENOTEBOOKTOHACK { .. } => not_ported(mode),
        mode @ ClientMode::MODEINMEMORYDEPTABLESIZE => not_ported(mode),
        mode @ ClientMode::MODESAVENAMING(_) => not_ported(mode),
        mode @ ClientMode::MODESEARCH(_) => not_ported(mode),
        mode @ ClientMode::MODELINT => not_ported(mode),
        mode @ ClientMode::MODESERVERRAGE => not_ported(mode),
        mode @ ClientMode::MODELINTSTDIN(_) => not_ported(mode),
        mode @ ClientMode::MODELINTALL(_) => not_ported(mode),
        ClientMode::MODESTATS => {
            let (stats, telemetry): (stats::T, _) = rpc(args, server_command_types::T::STATS)?;
            print!(
                "{}",
                crate::rt::yojson_ext::pretty_to_string(&stats::to_json(&stats))
            );
            Ok((exit_status::T::NoError, telemetry))
        }
        mode @ ClientMode::MODEREMOVEDEADFIXMES(_) => not_ported(mode),
        mode @ ClientMode::MODEREMOVEDEADUNSAFECASTS => not_ported(mode),
        mode @ ClientMode::MODEREWRITEDECLARATIONS => not_ported(mode),
        mode @ ClientMode::MODEREWRITELAMBDAPARAMETERS(_) => not_ported(mode),
        mode @ ClientMode::MODEFULLFIDELITYPARSE(_) => not_ported(mode),
        mode @ ClientMode::MODEFULLFIDELITYSCHEMA => not_ported(mode),
        mode @ ClientMode::MODECSTSEARCH(_) => not_ported(mode),
        mode @ ClientMode::MODEFILELEVELDEPENDENCIES => not_ported(mode),
        mode @ ClientMode::MODEFINDISOLATABLECLUSTERS => not_ported(mode),
        mode @ ClientMode::MODEVERBOSE(_) => not_ported(mode),
        mode @ ClientMode::MODEDEPSINATPOSBATCH(_) => not_ported(mode),
        mode @ ClientMode::MODEFINDMYTESTS(_) => not_ported(mode),
        mode @ ClientMode::MODEPACKAGELINT(_) => not_ported(mode),
        mode @ ClientMode::MODEPACKAGELINTFULL(_) => not_ported(mode),
    }
}

/// The `with exn ->` of [`main`], for an exception whose exit status is
/// `exit_status` (`Exit_with`, or `Uncaught_exception`, already printed).
fn handle_exit(exit_status: exit_status::T, partial_telemetry_ref: &PartialTelemetryRef) -> ! {
    let spinner = crate::client_spinner::get_latest_report();
    // hide the spinner
    crate::client_spinner::report(false, false, None);
    let spinner_name = spinner.map(|(s, _)| s).unwrap_or_default();
    let partial_telemetry = partial_telemetry_ref
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .is_some();
    match (&exit_status, partial_telemetry) {
        (exit_status::T::Interrupted | exit_status::T::ClientBrokenPipe, true) => {
            // [Interrupted] is raised by a SIGINT exit-handler installed in hh_client.
            // [Client_broken_pipe] is raised in [clientCheckStatus.go_streaming] when
            // it can't write errors to the pipe.
            // (`Hack_event_logger.client_check_partial`: a no-op.)
            hh_logger::log(&format!(
                "CLIENT_CHECK_PARTIAL [{}] {}",
                spinner_name,
                exit_status::show(&exit_status)
            ))
        }
        _ => {
            // (`Hack_event_logger.client_check_bad_exit`: a no-op.)
            hh_logger::log(&format!(
                "CLIENT_CHECK_EXIT [{}] {}",
                spinner_name,
                exit_status::show_expanded(&exit_status)
            ))
        }
    }
    exit::exit(None, None, None, exit_status)
}

/// `main check_env config local_config ~init_proc_stack`: never returns
/// (`Exit.exit`).
pub fn main(
    check_env: client_env::ClientCheckEnv,
    config: &server_config::T,
    local_config: &server_local_config::T,
    init_proc_stack: Option<Vec<String>>,
) -> Result<exit_status::T, hh_client::Exn> {
    let args = check_env;
    let _ = init_proc_stack;
    // `Hack_event_logger.client_set_mode (Client_env.Variants_of_client_mode.to_name
    // args.mode)` and `Hack_event_logger.client_check_start ~reason:args.reason`:
    // no-ops in the OSS build.
    crate::client_spinner::start_heartbeat_telemetry();
    // `Lwt.dont_wait flush_event_logger (fun _exn -> ())`: `Event_logger_lwt.flush`
    // does nothing in the OSS build.
    let partial_telemetry_ref: PartialTelemetryRef = Arc::new(Mutex::new(None));

    // Note: SIGINT exception handler is typically raised from [run_main], not from
    // the lwt code that's running in [main_internal]. Thus, [Lwt_utils.run_main]'s caller is
    // the only place that we can deal with it. This also motivates the use of a reference
    // [partial_telemetry_ref], since there's no way for a return value to survive SIGINT.
    {
        let partial_telemetry_ref = partial_telemetry_ref.clone();
        hh_client::set_interrupt_catch(Some(Arc::new(move || {
            handle_exit(exit_status::T::Interrupted, &partial_telemetry_ref)
        })));
    }
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        main_internal(&args, config, local_config, &partial_telemetry_ref)
    }));
    match result {
        Ok(Ok((exit_status, _telemetry))) => {
            let _spinner = crate::client_spinner::get_latest_report();
            // (`Hack_event_logger.client_check exit_status telemetry ~init_proc_stack
            // ~spinner`: a no-op.)
            hh_logger::log(&format!("CLIENT_CHECK {}", exit_status::show(&exit_status)));
            exit::exit(None, None, None, exit_status)
        }
        Ok(Err(Exn::ExitWith(exit_status))) => {
            // we assume that whoever raised [Exit_with] had the decency to print an explanation
            handle_exit(exit_status, &partial_telemetry_ref)
        }
        Ok(Err(Exn::Other(e))) => uncaught(e, &partial_telemetry_ref),
        Err(payload) => uncaught(crate::exception::wrap(payload), &partial_telemetry_ref),
    }
}

/// The `with exn ->` of [`main`] for an exception other than `Exit_with`:
/// if it was uncaught, then presumably no one else has printed it, so it's
/// up to us. Let's include lots of details, including stack trace.
fn uncaught(e: crate::exception::T, partial_telemetry_ref: &PartialTelemetryRef) -> ! {
    // (The spinner is hidden before the message, as in OCaml.)
    let _spinner = crate::client_spinner::get_latest_report();
    crate::client_spinner::report(false, false, None);
    let exit_status = exit_status::T::UncaughtException(e);
    eprintln!("{}", exit_status::show_expanded(&exit_status));
    {
        use std::io::Write;
        let _ = std::io::stderr().flush();
    }
    handle_exit(exit_status, partial_telemetry_ref)
}

#[cfg(test)]
mod tests;
