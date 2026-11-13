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
    Ok(connect_(use_priority_pipe, do_post_handoff_handshake, args)?)
}

/// [`connect`], with the error of `Client_connect`.
fn connect_(
    use_priority_pipe: Option<bool>,
    do_post_handoff_handshake: Option<bool>,
    args: &client_env::ClientCheckEnv,
) -> Result<client_connect::Conn, client_connect::ClientConnectError> {
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
    client_connect::connect(&client_connect::Env {
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
    })
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

/// `rpc_with_retry args command`
fn rpc_with_retry<A>(args: &client_env::ClientCheckEnv, command: server_command_types::T) -> Result<A, Exn>
where
    server_command_types::done_or_retry::T<A>: ResultOf,
{
    let use_priority_pipe = server_command_types::use_priority_pipe(&command);
    let conn = || connect_(Some(use_priority_pipe), None, args);
    Ok(client_connect::rpc_with_retry(conn, &args.desc, command)?)
}

/// `rpc_with_retry_list args command`
#[allow(dead_code)]
fn rpc_with_retry_list<A>(args: &client_env::ClientCheckEnv, command: server_command_types::T) -> Result<Vec<A>, Exn>
where
    Vec<server_command_types::done_or_retry::T<A>>: ResultOf,
{
    let use_priority_pipe = server_command_types::use_priority_pipe(&command);
    let conn = || connect_(Some(use_priority_pipe), None, args);
    Ok(client_connect::rpc_with_retry_list(conn, &args.desc, command)?)
}

fn input_error<A>() -> Result<A, Exn> {
    Err(Exn::ExitWith(exit_status::T::InputError))
}

/// `Sys_utils.read_stdin_to_string ()`
fn read_stdin_to_string() -> String {
    use std::io::Read;
    let mut buf = vec![];
    let _ = std::io::stdin().read_to_end(&mut buf);
    String::from_utf8_lossy(&buf).into_owned()
}

fn print_refs(results: &[crate::search_types::find_refs::Absolute], json: bool) {
    if json {
        println!(
            "{}",
            crate::yojson::safe::to_string(&crate::find_refs_wire_format::hack_ast::to_json(results))
        )
    } else {
        crate::find_refs_wire_format::cli_human_readable::print_results(results)
    }
}

/// `parse_name_or_member_id ~name_only_action ~name_and_member_action name`
fn parse_name_or_member_id<A>(
    name_only_action: impl FnOnce(String) -> Result<A, Exn>,
    name_and_member_action: impl FnOnce(String, String) -> Result<A, Exn>,
    name: &str,
) -> Result<A, Exn> {
    let pieces = ocaml_str::split_literal("::", name);
    // (`Str.first_chars str 1` raises on an empty string: "Invalid input".)
    let default_namespace = |str: &str| -> Option<String> {
        if str.is_empty() {
            None
        } else if str.starts_with('\\') {
            Some(str.to_string())
        } else {
            Some(format!("\\{}", str))
        }
    };
    // (`with _ ->`: any exception of the actions is "Invalid input" too.)
    let result = match pieces.as_slice() {
        [class_name, member_name, ..] => match default_namespace(class_name) {
            Some(class_name) => name_and_member_action(class_name, member_name.to_string()).ok(),
            None => None,
        },
        [name] => match default_namespace(name) {
            Some(name) => name_only_action(name).ok(),
            None => None,
        },
        _ => None,
    };
    match result {
        Some(x) => Ok(x),
        None => {
            eprint!("Invalid input\n");
            input_error()
        }
    }
}

fn expand_path(file: &str) -> String {
    let path = crate::path::make(file);
    if crate::path::file_exists(&path) {
        crate::path::to_string(&path)
    } else {
        let cwd = std::env::current_dir().map(|d| d.to_string_lossy().into_owned()).unwrap_or_default();
        let file = crate::rt::ocaml_filename::concat(&cwd, file);
        let path = crate::path::make(&file);
        if crate::path::file_exists(&path) {
            crate::path::to_string(&path)
        } else {
            print!("File not found: {}\n", file);
            {
                use std::io::Write;
                let _ = std::io::stdout().flush();
            }
            std::process::exit(2)
        }
    }
}

#[allow(dead_code)]
fn expand_file_path(file: &str) -> Result<String, Exn> {
    let path = expand_path(file);
    if std::path::Path::new(&path).is_dir() {
        eprintln!("Path is a directory, only files are allowed: '{}'", file);
        return input_error();
    }
    Ok(path)
}

fn int_of_string(s: &str) -> Option<isize> {
    crate::rt::ocaml_arg::int_of_string_opt(s)
}

fn parse_position_string(split_on: &str, arg: &str) -> Result<(isize, isize), Exn> {
    let tpos = ocaml_str::split_literal(split_on, arg);
    let parsed = match tpos.as_slice() {
        [line, char] => int_of_string(line).zip(int_of_string(char)),
        _ => None,
    };
    match parsed {
        Some(x) => Ok(x),
        None => {
            eprint!("Invalid position\n");
            input_error()
        }
    }
}

#[allow(dead_code)]
fn parse_positions(positions: &[String]) -> Result<Vec<(String, isize, isize)>, Exn> {
    positions
        .iter()
        .map(|pos| {
            let parsed = match ocaml_str::split_literal(":", pos).as_slice() {
                [filename, line, char] => match (int_of_string(line), int_of_string(char)) {
                    (Some(line), Some(char)) => Some((expand_path(filename), line, char)),
                    _ => None,
                },
                _ => None,
            };
            match parsed {
                Some(x) => Ok(x),
                None => {
                    eprint!("Invalid position\n");
                    input_error()
                }
            }
        })
        .collect()
}

/// Filters and prints errors when a path is not a realpath
fn filter_real_paths(allow_directories: bool, paths: &[String]) -> Vec<String> {
    paths
        .iter()
        .filter_map(|fn_| match crate::sys_utils::realpath(fn_) {
            Some(path) => {
                if !allow_directories && std::path::Path::new(fn_).is_dir() {
                    eprintln!("Path is a directory, only files are allowed: '{}'", fn_);
                    None
                } else {
                    Some(path)
                }
            }
            None => {
                eprintln!("Could not find file '{}'", fn_);
                None
            }
        })
        .collect()
}

/// `[filename; line; char]` or `[line; char]` (the contents are read from
/// stdin), for `--type-at-pos` and `--type-error-at-pos`.
fn parse_file_position(arg: &str) -> Option<(server_command_types::FileInput, isize, isize)> {
    let tpos = ocaml_str::split_literal(":", arg);
    match tpos.as_slice() {
        [filename, line, char] => {
            let fn_ = expand_path(filename);
            Some((
                server_command_types::FileInput::FileName(fn_),
                int_of_string(line)?,
                int_of_string(char)?,
            ))
        }
        [line, char] => {
            let content = read_stdin_to_string();
            Some((
                server_command_types::FileInput::FileContent(content),
                int_of_string(line)?,
                int_of_string(char)?,
            ))
        }
        _ => None,
    }
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

/// The paths of a `--package-lint` result, as a JSON list.
fn print_package_lint_result(results: &server_command_types::package_lint::FastResult) {
    use crate::yojson::safe as yojson;
    let paths = results
        .iter()
        .map(|p| yojson::T::String(crate::relative_path::to_absolute(p)))
        .collect();
    println!("{}", yojson::to_string(&yojson::T::List(paths)))
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
        // (The TASTs of `--single --show-tast` cannot cross the socket: see
        // `rt::protocol::wire::status_single_result`.)
        mode @ ClientMode::MODESTATUSSINGLE(client_env::StatusSingle { show_tast: true, .. }) => not_ported(mode),
        ClientMode::MODESTATUSSINGLE(client_env::StatusSingle {
            filenames,
            show_tast,
            preexisting_warnings,
        }) => {
            let mut file_inputs = vec![];
            for filename in filenames {
                file_inputs.push(match filename.as_str() {
                    "-" => server_command_types::FileInput::FileContent(read_stdin_to_string()),
                    _ => server_command_types::FileInput::FileName(expand_file_path(filename)?),
                })
            }
            let error_filter = error_filter(config, local_config, args);
            let (((error_list, dropped_count), _tasts), telemetry): (server_command_types::StatusSingleResult, _) =
                rpc(
                    args,
                    server_command_types::T::STATUSSINGLE {
                        file_names: file_inputs,
                        max_errors: args.max_errors,
                        error_filter,
                        return_expanded_tast: *show_tast,
                        preexisting_warnings: *preexisting_warnings,
                    },
                )?;
            let status = server_command_types::server_status::T {
                error_list,
                dropped_count,
                liveness: server_command_types::StatusLiveness::LiveStatus,
                last_recheck_stats: None,
                file_watcher_clock: None,
            };
            let exit_status = client_check_status::go(
                status,
                args.error_format,
                args.is_interactive,
                args.output_json,
                args.output_jsonl,
                args.max_errors,
            );
            Ok((exit_status, telemetry))
        }
        ClientMode::MODELOGERRORS(client_env::LogErrorsParams {
            log_file,
            preexisting_warnings,
        }) => {
            let files = filter_real_paths(false, &args.paths);
            let error_filter = error_filter(config, local_config, args);
            let ((), telemetry): ((), _) = rpc(
                args,
                server_command_types::T::LOGERRORS {
                    files,
                    log_file: log_file.clone(),
                    error_filter,
                    preexisting_warnings: *preexisting_warnings,
                },
            )?;
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODELISTFILES => {
            let (infol, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::LISTFILESWITHERRORS)?;
            for s in &infol {
                print!("{}\n", s);
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEFINDCLASSREFS(name) => {
            use crate::search_types::find_refs::Action;
            let results: Vec<_> = rpc_with_retry(args, server_command_types::T::FINDREFS(Action::Class(name.clone())))?;
            print_refs(&results, args.output_json);
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::MODEFINDREFS(name) => {
            use crate::search_types::find_refs::Action;
            use crate::search_types::find_refs::Member;
            let pieces = ocaml_str::split_literal("|", name);
            let (kind, name) = match pieces.as_slice() {
                [name] => (None, *name),
                [kind, name] => (Some(*kind), *name),
                _ => {
                    eprint!("Invalid input\n");
                    return input_error();
                }
            };
            let action = parse_name_or_member_id(
                |name| match kind {
                    Some("Function") | None => Ok(Action::Function(name)),
                    Some("Class") => Ok(Action::Class(name)),
                    Some("ExplicitClass") => Ok(Action::ExplicitClass(name)),
                    Some("GConst") => Ok(Action::GConst(name)),
                    Some(_) => input_error(),
                },
                |class_name, member_name| {
                    let member = match kind {
                        Some("Method") | None => Member::Method(member_name),
                        Some("Property") => Member::Property(member_name),
                        Some("Class_const") => Member::ClassConst(member_name),
                        Some("Typeconst") => Member::Typeconst(member_name),
                        Some(_) => return input_error(),
                    };
                    Ok(Action::Member(class_name, member))
                },
                name,
            )?;
            let results: Vec<_> = rpc_with_retry(args, server_command_types::T::FINDREFS(action))?;
            print_refs(&results, args.output_json);
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::MODEGOTOIMPLCLASS(class_name) => {
            use crate::search_types::find_refs::Action;
            let results: Vec<_> =
                rpc_with_retry(args, server_command_types::T::GOTOIMPL(Action::Class(class_name.clone())))?;
            print_refs(&results, args.output_json);
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::MODEGOTOIMPLMETHOD(name) => {
            use crate::search_types::find_refs::Action;
            use crate::search_types::find_refs::Member;
            let action = parse_name_or_member_id(
                |fun_name| Ok(Action::Function(fun_name)),
                |class_name, method_name| Ok(Action::Member(class_name, Member::Method(method_name))),
                name,
            )?;
            match action {
                Action::Member(..) => {
                    let results: Vec<_> = rpc_with_retry(args, server_command_types::T::GOTOIMPL(action))?;
                    print_refs(&results, args.output_json);
                    Ok((exit_status::T::NoError, telemetry::create()))
                }
                _ => {
                    eprint!("Invalid input\n");
                    Ok((exit_status::T::InputError, telemetry::create()))
                }
            }
        }
        mode @ ClientMode::MODEHACKTONOTEBOOK => not_ported(mode),
        ClientMode::MODEIDEFINDREFSBYSYMBOL(arg) => {
            let results: Vec<_> = rpc_with_retry(args, server_command_types::T::IDEFINDREFSBYSYMBOL(arg.clone()))?;
            println!("{}", crate::find_refs_wire_format::ide_shellout::to_string(&results));
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::MODEIDEGOTOIMPLBYSYMBOL(arg) => {
            let results: Vec<_> = rpc_with_retry(args, server_command_types::T::IDEGOTOIMPLBYSYMBOL(arg.clone()))?;
            println!("{}", crate::find_refs_wire_format::ide_shellout::to_string(&results));
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::MODEDUMPSYMBOLINFO(files) => {
            let conn = connect(None, None, args)?;
            crate::client_symbol_info::go(&conn, &args.desc, files, expand_path)?;
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::MODERENAME(ref_mode, before, after) => {
            let conn = || connect_(None, None, args);
            crate::client_rename::go(conn, &args.desc, args, ref_mode, before, after)?;
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::MODEIDERENAMEBYSYMBOL(arg) => {
            let (new_name, action, symbol_definition) = server_command_types::rename::string_to_args(arg)?;
            let results: server_command_types::rename::IdeResult = rpc_with_retry(
                args,
                server_command_types::T::IDERENAMEBYSYMBOL(action, new_name, symbol_definition),
            )?;
            match results {
                Ok(patches) => {
                    crate::client_rename::go_ide_from_patches(patches, args.output_json);
                    Ok((exit_status::T::NoError, telemetry::create()))
                }
                Err(_msg) => input_error(),
            }
        }
        ClientMode::MODEIDENTIFYSYMBOL(arg) => {
            use crate::yojson::safe as yojson;
            if !args.output_json {
                eprint!("Must use --json\n");
                return input_error();
            }
            let (result, telemetry): (Vec<crate::symbol_definition::T<crate::pos::Absolute>>, _) =
                rpc(args, server_command_types::T::IDENTIFYSYMBOL(arg.clone()))?;
            let definition_to_json = |d: &crate::symbol_definition::T<crate::pos::Absolute>| {
                yojson::T::Assoc(vec![
                    (
                        "full_name".to_string(),
                        yojson::T::String(crate::symbol_definition::full_name(d)),
                    ),
                    ("pos".to_string(), crate::pos::json(&d.pos)),
                    (
                        "kind".to_string(),
                        yojson::T::String(crate::symbol_definition::string_of_kind(&d.kind).to_string()),
                    ),
                ])
            };
            let definitions = result.iter().map(definition_to_json).collect();
            println!("{}", yojson::to_string(&yojson::T::List(definitions)));
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEIDENTIFYSYMBOL1(arg)
        | ClientMode::MODEIDENTIFYSYMBOL2(arg)
        | ClientMode::MODEIDENTIFYSYMBOL3(arg) => {
            let (line, char) = parse_position_string(":", arg)?;
            let pos = crate::file_content::position::from_one_based(line, char);
            let file = match &args.stdin_name {
                None => String::new(),
                Some(f) => expand_path(f),
            };
            let content = server_command_types::FileInput::FileContent(read_stdin_to_string());
            let (result, telemetry): (server_command_types::identify_symbol::Result, _) =
                rpc(args, server_command_types::T::IDENTIFYFUNCTION(file, content, pos))?;
            crate::client_get_definition::go(&result, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODETYPEATPOS(arg) => {
            let (fn_, line, char) = match parse_file_position(arg) {
                Some(x) => x,
                None => {
                    eprint!("Invalid position\n");
                    return input_error();
                }
            };
            let pos = crate::file_content::position::from_one_based(line, char);
            let (ty, telemetry): (Option<(String, String)>, _) =
                rpc(args, server_command_types::T::INFERTYPE(fn_, pos))?;
            crate::client_type_at_pos::go(ty, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEINFERDYNAMIC(arg, as_data) => {
            let (json, telemetry): (crate::yojson::safe::T, _) =
                rpc(args, server_command_types::T::INFERDYNAMIC(arg.clone(), *as_data))?;
            print!("{}\n", crate::rt::yojson_ext::pretty_to_string(&json));
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEENFORCEMENTATPOSBATCH(positions) => {
            let mut parsed = vec![];
            for pos in positions {
                let p = match ocaml_str::split_literal(":", pos).as_slice() {
                    [filename, line, char] => match (int_of_string(line), int_of_string(char)) {
                        (Some(line), Some(char)) => Some((
                            expand_path(filename),
                            crate::file_content::position::from_one_based(line, char),
                        )),
                        _ => None,
                    },
                    _ => None,
                };
                match p {
                    Some(p) => parsed.push(p),
                    None => {
                        eprint!("Invalid position\n");
                        return input_error();
                    }
                }
            }
            let (responses, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::ENFORCEMENTATPOSBATCH(parsed))?;
            for response in &responses {
                println!("{}", response)
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODETYPEATPOSBATCH(positions) => {
            use crate::file_content::position::from_one_based;
            let mut parsed = vec![];
            for pos in positions {
                let pieces = ocaml_str::split_literal(":", pos);
                let ints: Option<Vec<isize>> = pieces.iter().skip(1).map(|s| int_of_string(s)).collect();
                let p = match (pieces.as_slice(), ints.as_deref()) {
                    ([filename, _, _], Some([line, char])) => {
                        Some((expand_path(filename), from_one_based(*line, *char), None))
                    }
                    ([filename, _, _, _, _], Some([start_line, start_char, end_line, end_char])) => {
                        let filename = expand_path(filename);
                        let start_pos = from_one_based(*start_line, *start_char);
                        let end_pos = from_one_based(*end_line, *end_char);
                        Some((filename, start_pos, Some(end_pos)))
                    }
                    _ => None,
                };
                match p {
                    Some(p) => parsed.push(p),
                    None => {
                        eprint!("Invalid position\n");
                        return input_error();
                    }
                }
            }
            let (responses, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::INFERTYPEBATCH(parsed))?;
            for response in &responses {
                println!("{}", response)
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEISSUBTYPE => {
            let stdin = read_stdin_to_string();
            let (response, telemetry): (Result<String, String>, _) =
                rpc(args, server_command_types::T::ISSUBTYPE(stdin))?;
            match response {
                Ok(str) => {
                    print!("{}", str);
                    Ok((exit_status::T::NoError, telemetry))
                }
                Err(str) => {
                    eprint!("{}", str);
                    input_error()
                }
            }
        }
        ClientMode::MODETYPEERRORATPOS(arg) => {
            let (fn_, line, char) = match parse_file_position(arg) {
                Some(x) => x,
                None => {
                    eprint!(
                        "Invalid position; expected an argument of the form [filename]:[line]:[column] or [line]:[column]\n"
                    );
                    return input_error();
                }
            };
            let (ty, telemetry): (crate::infer_error_at_pos_service::Result, _) =
                rpc(args, server_command_types::T::INFERTYPEERROR(fn_, line, char))?;
            crate::client_type_error_at_pos::go(&ty, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODETASTHOLES(arg) => {
            use server_command_types::FileInput;
            use server_command_types::tast_hole::Filter;
            let parse_hole_filter = |s: &str| match s {
                "any" => Some(Filter::Any),
                "typing" => Some(Filter::Typing),
                "cast" => Some(Filter::Cast),
                _ => None,
            };
            let parsed = match ocaml_str::split_literal(":", arg).as_slice() {
                [filename, filter_str] => {
                    let fn_ = expand_path(filename);
                    parse_hole_filter(filter_str).map(|filter| (FileInput::FileName(fn_), filter))
                }
                [part] => match parse_hole_filter(part) {
                    Some(src_opt) => {
                        let content = read_stdin_to_string();
                        Some((FileInput::FileContent(content), src_opt))
                    }
                    None => {
                        let fn_ = expand_path(part);
                        // No hole source specified; default to `Typing`
                        Some((FileInput::FileName(fn_), Filter::Typing))
                    }
                },
                _ => None,
            };
            let (filename, hole_src_opt) = match parsed {
                Some(x) => x,
                None => {
                    eprint!(
                        "Invalid argument; expected an argument of the form [filename](:[any|typing|cast])? or [any|typing|cast]\n"
                    );
                    return input_error();
                }
            };
            let (ty, telemetry): (crate::tast_holes_service::Result, _) =
                rpc(args, server_command_types::T::TASTHOLES(filename, hole_src_opt))?;
            crate::client_tast_holes::go(&ty, false, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODETASTHOLESBATCH(file) => {
            let contents = match crate::sys_utils::cat(&expand_path(file)) {
                Ok(contents) => String::from_utf8_lossy(&contents).into_owned(),
                Err(e) => panic!("{:?}", e),
            };
            // `String.strip |> String.split ~on:'\n'`
            let files: Vec<String> = contents
                .trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r'))
                .split('\n')
                .map(expand_path)
                .collect();
            let (holes, telemetry): (crate::tast_holes_service::Result, _) =
                rpc(args, server_command_types::T::TASTHOLESBATCH(files))?;
            crate::client_tast_holes::go(&holes, true, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEFUNDEPSATPOSBATCH(positions) => {
            let positions = parse_positions(positions)?;
            let (responses, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::FUNDEPSBATCH(positions))?;
            for response in &responses {
                println!("{}", response)
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEDEPSOUTATPOSBATCH(positions) => {
            let positions = parse_positions(positions)?;
            let (responses, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::DEPSOUTBATCH(positions))?;
            for response in &responses {
                println!("{}", response)
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEOUTLINE | ClientMode::MODEOUTLINE2 => {
            // (`Shared_mem.init`: nothing to set up here.)
            let content = read_stdin_to_string();
            // TODO: Don't use default parser options.
            //
            // Parser options enables certain features (such as namespace aliasing)
            // Thus, for absolute correctness of outlining, we need to use the same
            // parser options that the server uses. But this client request doesn't
            // hit the server at all. So either change this to a server RPC, or
            // ask the server what its parser options are, or parse the
            // options from the .hhconfig file (needs to be the same hhconfig file the
            // server used).
            let results = crate::file_outline::outline(&Default::default(), content.as_bytes());
            crate::client_outline::go(&results, args.output_json);
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::MODEOUTLINEFORAGENTS(path) => {
            let content = match crate::sys_utils::cat(path) {
                Ok(content) => content,
                Err(e) => panic!("{:?}", e),
            };
            let result = crate::outline_for_agents::outline(&content);
            {
                use std::io::Write;
                let _ = std::io::stdout().write_all(&result);
            }
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::MODEMETHODJUMPCHILDREN(class_) => {
            let filter = server_command_types::method_jumps::Filter::NoFilter;
            let (results, telemetry): (Vec<server_command_types::method_jumps::Result>, _) =
                rpc(args, server_command_types::T::METHODJUMP((class_.clone(), filter, true)))?;
            crate::client_method_jumps::go(&results, true, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEMETHODJUMPANCESTORS(class_, filter) => {
            let filter = match crate::method_jumps::string_filter_to_method_jump_filter(filter) {
                Some(filter) => filter,
                None => {
                    eprint!("Invalid method jump filter {}\n", filter);
                    return input_error();
                }
            };
            let (results, telemetry): (Vec<server_command_types::method_jumps::Result>, _) =
                rpc(args, server_command_types::T::METHODJUMP((class_.clone(), filter, false)))?;
            crate::client_method_jumps::go(&results, false, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEMETHODJUMPANCESTORSBATCH(classes, filter) => {
            let filter = match crate::method_jumps::string_filter_to_method_jump_filter(filter) {
                Some(filter) => filter,
                None => {
                    eprint!("Invalid method jump filter {}\n", filter);
                    return input_error();
                }
            };
            let (results, telemetry): (Vec<server_command_types::method_jumps::Result>, _) =
                rpc(args, server_command_types::T::METHODJUMPBATCH((classes.clone(), filter)))?;
            crate::client_method_jumps::go(&results, false, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        mode @ ClientMode::MODENOTEBOOKTOHACK { .. } => not_ported(mode),
        ClientMode::MODEINMEMORYDEPTABLESIZE => {
            let (result, telemetry): (Result<isize, String>, _) =
                rpc(args, server_command_types::T::INMEMORYDEPTABLESIZE)?;
            crate::client_result_printer::int_printer_go(&result, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODESAVENAMING(path) => {
            use crate::save_state_service_types::SaveNamingResult;
            use crate::yojson::safe as yojson;
            let dirname = crate::rt::ocaml_filename::dirname(path);
            if let Err(e) = crate::sys_utils::mkdir_p(&dirname) {
                panic!("Sys_error({:?})", e.to_string())
            }
            let path = crate::path::make(path);
            let (result, telemetry): (Result<SaveNamingResult, String>, _) =
                rpc(args, server_command_types::T::SAVENAMING(crate::path::to_string(&path)))?;
            // `SaveNamingResultPrinter.go`
            crate::client_result_printer::go(
                &result,
                args.output_json,
                |t| format!("Files added: {}, symbols added: {}", t.nt_files_added, t.nt_symbols_added),
                |t| {
                    yojson::T::Assoc(vec![
                        ("files_added".to_string(), yojson::T::Int(t.nt_files_added)),
                        ("symbols_added".to_string(), yojson::T::Int(t.nt_symbols_added)),
                    ])
                },
            );
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODESEARCH(query) => {
            if query != "this_is_just_to_check_liveness_of_hh_server" {
                eprintln!("Usage: hh --search this_is_just_to_check_liveness_of_hh_server");
                Ok((exit_status::T::InputError, telemetry::create()))
            } else {
                let ((), telemetry): ((), _) = rpc(args, server_command_types::T::CHECKLIVENESS)?;
                if args.output_json {
                    println!("[]")
                }
                Ok((exit_status::T::NoError, telemetry))
            }
        }
        ClientMode::MODELINT => {
            let fnl = filter_real_paths(false, &args.paths);
            if args.paths.is_empty() {
                eprintln!("No lint errors (0 files checked)!");
                eprintln!("Note: --lint expects a list of filenames to check.");
                Ok((exit_status::T::NoError, telemetry::create()))
            } else {
                let (results, telemetry): (crate::server_lint_types::Result, _) =
                    rpc(args, server_command_types::T::LINT(fnl))?;
                let error_format = crate::diagnostics_state::format_or_default(args.error_format);
                crate::client_lint::go(&results, args.output_json, error_format);
                Ok((exit_status::T::NoError, telemetry))
            }
        }
        ClientMode::MODESERVERRAGE => {
            use crate::yojson::safe as yojson;
            if !args.output_json {
                eprint!("Must use --json\n");
                return input_error();
            }
            // Our json output format is read by clientRage.ml
            let make_item = |item: &crate::server_rage_types::RageItem| {
                yojson::T::Assoc(vec![
                    ("name".to_string(), yojson::T::String(item.title.clone())),
                    ("contents".to_string(), yojson::T::String(item.data.clone())),
                ])
            };
            let (items, telemetry): (crate::server_rage_types::Result, _) =
                rpc(args, server_command_types::T::RAGE)?;
            println!(
                "{}",
                yojson::to_string(&yojson::T::List(items.iter().map(make_item).collect()))
            );
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODELINTSTDIN(filename) => match crate::sys_utils::realpath(filename) {
            None => {
                eprintln!("Could not find file '{}'", filename);
                Ok((exit_status::T::InputError, telemetry::create()))
            }
            Some(filename) => {
                let contents = read_stdin_to_string();
                let (results, telemetry): (crate::server_lint_types::Result, _) = rpc(
                    args,
                    server_command_types::T::LINTSTDIN(server_command_types::LintStdinInput { filename, contents }),
                )?;
                let error_format = crate::diagnostics_state::format_or_default(args.error_format);
                crate::client_lint::go(&results, args.output_json, error_format);
                Ok((exit_status::T::NoError, telemetry))
            }
        },
        ClientMode::MODELINTALL(code) => {
            let (results, telemetry): (crate::server_lint_types::Result, _) =
                rpc(args, server_command_types::T::LINTALL(*code))?;
            let error_format = crate::diagnostics_state::format_or_default(args.error_format);
            crate::client_lint::go(&results, args.output_json, error_format);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEPAUSE => {
            let ((), telemetry): ((), _) = rpc(args, server_command_types::T::PAUSE)?;
            println!("Paused automatic rechecks. The next client request resumes them.");
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODESTATS => {
            let (stats, telemetry): (stats::T, _) = rpc(args, server_command_types::T::STATS)?;
            print!(
                "{}",
                crate::rt::yojson_ext::pretty_to_string(&stats::to_json(&stats))
            );
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEREMOVEDEADFIXMES(codes) => {
            let conn = connect(None, None, args)?;
            let (response, telemetry): (server_command_types::PatchesOrError, _) = client_connect::rpc(
                &conn,
                &args.desc,
                server_command_types::T::REMOVEDEADFIXMES(codes.clone()),
            )?;
            match response {
                server_command_types::PatchesOrError::Error(msg) => {
                    eprint!("{}\n", msg);
                    Ok((exit_status::T::TypeError, telemetry))
                }
                server_command_types::PatchesOrError::Ok(patches) => {
                    if args.output_json {
                        crate::client_rename::print_patches_json(patches)
                    } else {
                        crate::client_rename::apply_patches(patches)
                    }
                    Ok((exit_status::T::NoError, telemetry))
                }
            }
        }
        ClientMode::MODEREMOVEDEADUNSAFECASTS => {
            let error_filter = error_filter(config, local_config, args);
            let status_cmd = || server_command_types::T::STATUS {
                max_errors: args.max_errors,
                error_filter: error_filter.clone(),
            };
            loop {
                let (response, telemetry): (server_command_types::PatchesOrError, _) =
                    rpc(args, server_command_types::T::REMOVEDEADUNSAFECASTS)?;
                match response {
                    server_command_types::PatchesOrError::Error(msg) => {
                        eprint!("{}\n", msg);
                        return Ok((exit_status::T::TypeError, telemetry));
                    }
                    server_command_types::PatchesOrError::Ok(patches) => {
                        let is_empty = patches.is_empty();
                        crate::client_rename::apply_patches(patches);
                        if is_empty {
                            return Ok((exit_status::T::NoError, telemetry));
                        } else {
                            let _: (server_command_types::server_status::T, _) = rpc(args, status_cmd())?;
                        }
                    }
                }
            }
        }
        ClientMode::MODEREWRITEDECLARATIONS => {
            // `Declarations_rewriter.start`: the stub of the open-source build
            // (`stubs/declarations_rewriter.ml`) does nothing.
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        // (The server's `REWRITE_LAMBDA_PARAMETERS` is not ported.)
        mode @ ClientMode::MODEREWRITELAMBDAPARAMETERS(_) => not_ported(mode),
        ClientMode::MODEFULLFIDELITYPARSE(file) => {
            // We can cheaply do this on the client today, but we might want to
            // do it on the server and cache the results in the future.
            let do_it_on_server = false;
            let (results, telemetry): (String, _) = if do_it_on_server {
                rpc(args, server_command_types::T::DUMPFULLFIDELITYPARSE(file.clone()))?
            } else {
                (crate::full_fidelity_parse_service::go(file), telemetry::create())
            };
            crate::client_full_fidelity_parse::go(&results);
            Ok((exit_status::T::NoError, telemetry))
        }
        mode @ ClientMode::MODEFULLFIDELITYSCHEMA => not_ported(mode),
        ClientMode::MODECSTSEARCH(files_to_search) => {
            use crate::yojson::safe as yojson;
            let sort_results = args.sort_results;
            let input = match yojson::from_string(&read_stdin_to_string()) {
                Ok(input) => input,
                Err(e) => panic!("Yojson.Json_error: {:?}", e),
            };
            let (result, telemetry): (Result<yojson::T, String>, _) = rpc(
                args,
                server_command_types::T::CSTSEARCH(server_command_types::CstSearchInput {
                    sort_results,
                    input,
                    files_to_search: files_to_search.clone(),
                }),
            )?;
            match result {
                Ok(result) => {
                    println!("{}", yojson::to_string(&result));
                    Ok((exit_status::T::NoError, telemetry))
                }
                Err(error) => {
                    println!("{}", error);
                    input_error()
                }
            }
        }
        ClientMode::MODEFILELEVELDEPENDENCIES => {
            use crate::yojson::safe as yojson;
            let paths = filter_real_paths(true, &args.paths);
            let (responses, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::FILEDEPENDENTS(paths))?;
            if args.output_json {
                let json_path_list = responses.iter().map(|path| yojson::T::String(path.clone())).collect();
                let output = yojson::T::Assoc(vec![("dependents".to_string(), yojson::T::List(json_path_list))]);
                println!("{}", yojson::to_string(&output))
            } else {
                for response in &responses {
                    print!("{}\n", response)
                }
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        mode @ ClientMode::MODEFINDISOLATABLECLUSTERS => not_ported(mode),
        ClientMode::MODEVERBOSE(verbose) => {
            let ((), telemetry): ((), _) = rpc(args, server_command_types::T::VERBOSE(*verbose))?;
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEDEPSINATPOSBATCH(positions) => {
            let positions = parse_positions(positions)?;
            let results: Vec<Vec<crate::search_types::find_refs::Absolute>> =
                rpc_with_retry_list(args, server_command_types::T::DEPSINBATCH(positions))?;
            for s in &results {
                print_refs(s, true)
            }
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        mode @ ClientMode::MODEFINDMYTESTS(_) => not_ported(mode),
        ClientMode::MODEPACKAGELINT(file) => {
            let file = expand_file_path(file)?;
            let (results, telemetry): (server_command_types::package_lint::FastResult, _) =
                rpc(args, server_command_types::T::PACKAGELINT(file))?;
            print_package_lint_result(&results);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::MODEPACKAGELINTFULL((file, candidates)) => {
            let file = expand_file_path(file)?;
            let candidates = candidates
                .iter()
                .map(|c| expand_file_path(c))
                .collect::<Result<Vec<_>, _>>()?;
            let (results, telemetry): (server_command_types::package_lint::FastResult, _) =
                rpc(args, server_command_types::T::PACKAGELINTFULL((file, candidates)))?;
            print_package_lint_result(&results);
            Ok((exit_status::T::NoError, telemetry))
        }
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
