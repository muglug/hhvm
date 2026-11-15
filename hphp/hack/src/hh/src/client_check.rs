// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_check.ml`. See `hh/PORTING.md`.
//!
//! Every mode of `main_internal` is ported, in the OCaml's order, with
//! `connect`, `connect_then_close`, `rpc` (which includes
//! `rpc_with_connection`), `rpc_with_retry` and `main`.
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
use crate::rt::ocaml_stdlib::int_of_string_opt;
use crate::search_types::find_refs;
use crate::exit_status;
use crate::filter_diagnostics;
use crate::hh_client;
use crate::hh_client::Exn;
use crate::hh_logger;
use crate::rt::ocaml_str;
use crate::server_command_types;
use crate::server_command_types::ResultOf;
use crate::server_config;
use crate::server_isolation_types;
use crate::server_local_config;
use crate::stats;
use crate::telemetry;

/// `connect ?use_priority_pipe ?do_post_handoff_handshake args`
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
pub fn connect_then_close(args: &client_env::ClientCheckEnv) -> Result<(), Exn> {
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

/// A printed `Unix.Unix_error` (its `Printexc.to_string`).
struct UnixErrorPrinted(String);

impl std::fmt::Debug for UnixErrorPrinted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// `SaveNamingResultPrinter` (`Client_result_printer.Make`).
struct SaveNamingResultPrinter;

impl crate::client_result_printer::ResultConverter for SaveNamingResultPrinter {
    type T = crate::save_state_service_types::SaveNamingResult;
    fn to_string(t: &Self::T) -> String {
        format!(
            "Files added: {}, symbols added: {}",
            t.nt_files_added, t.nt_symbols_added
        )
    }
    fn to_json(t: &Self::T) -> crate::yojson::safe::T {
        crate::yojson::safe::T::Assoc(vec![
            ("files_added".to_string(), crate::yojson::safe::T::Int(t.nt_files_added)),
            ("symbols_added".to_string(), crate::yojson::safe::T::Int(t.nt_symbols_added)),
        ])
    }
}

/// `rpc_with_connection args command call`: `call` with a function that
/// connects on the pipe that `command` asks for.
fn rpc_with_connection<B>(
    args: &client_env::ClientCheckEnv,
    command: server_command_types::T,
    call: impl FnOnce(
        &dyn Fn() -> Result<client_connect::Conn, Exn>,
        &str,
        server_command_types::T,
    ) -> Result<B, Exn>,
) -> Result<B, Exn> {
    let use_priority_pipe = server_command_types::use_priority_pipe(&command);
    let conn = || connect(Some(use_priority_pipe), None, args);
    call(&conn, &args.desc, command)
}

/// `rpc args command`
pub fn rpc<A: ResultOf>(
    args: &client_env::ClientCheckEnv,
    command: server_command_types::T,
) -> Result<(A, telemetry::T), Exn> {
    rpc_with_connection(args, command, |conn_f, desc, command| {
        let conn = conn_f()?;
        let (result, telemetry) = client_connect::rpc(&conn, desc, command)?;
        Ok((result, telemetry))
    })
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

/// `rpc_with_retry args command` (and
/// `Client_connect.rpc_with_retry`): the same request again on `Retry`, at
/// most once.
pub fn rpc_with_retry<A>(
    mut conn: impl FnMut() -> Result<client_connect::Conn, Exn>,
    desc: &str,
    command: server_command_types::T,
) -> Result<A, Exn>
where
    server_command_types::done_or_retry::T<A>: ResultOf,
{
    use server_command_types::done_or_retry;
    for _ in 0..2 {
        let c = conn()?;
        let (result, _telemetry): (done_or_retry::T<A>, _) = client_connect::rpc(&c, desc, command.clone())?;
        match result {
            done_or_retry::T::Done(x) => return Ok(x),
            done_or_retry::T::Retry => {}
        }
    }
    Err(Exn::from(client_connect::ClientConnectError::TwoRetriesInARow(
        done_or_retry::TwoRetriesInARow,
    )))
}

/// `print_refs results ~json`
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

/// `parse_name_or_member_id ~name_only_action ~name_and_member_action name`:
/// any failure (an `Exit_with` of the actions too) is "Invalid input".
fn parse_name_or_member_id<A>(
    name_only_action: impl FnOnce(String) -> Option<A>,
    name_and_member_action: impl FnOnce(String, String) -> Option<A>,
    name: &str,
) -> Result<A, Exn> {
    let pieces = crate::rt::ocaml_str::split("::", name);
    // `Str.first_chars str 1` raises on the empty string.
    let default_namespace = |str: &str| -> Option<String> {
        if str.is_empty() {
            None
        } else if str.starts_with('\\') {
            Some(str.to_string())
        } else {
            Some(format!("\\{}", str))
        }
    };
    let result = match &pieces[..] {
        [class_name, member_name, ..] => {
            default_namespace(class_name).and_then(|c| name_and_member_action(c, member_name.clone()))
        }
        [name, ..] => default_namespace(name).and_then(name_only_action),
        _ => None,
    };
    match result {
        Some(a) => Ok(a),
        None => {
            eprint!("Invalid input\n");
            Err(Exn::ExitWith(exit_status::T::InputError))
        }
    }
}

/// `parse_positions positions`: `file:line:char` each (the file expanded
/// first, then the numbers: the tuple is evaluated from its last component).
fn parse_positions(positions: &[String]) -> Result<Vec<(String, isize, isize)>, Exn> {
    positions
        .iter()
        .map(|pos| {
            let parsed = match &crate::rt::ocaml_str::split(":", pos)[..] {
                [filename, line, char] => match (int_of_string_opt(char), int_of_string_opt(line)) {
                    (Some(char), Some(line)) => Some((expand_path(filename), line, char)),
                    _ => None,
                },
                _ => None,
            };
            parsed.ok_or_else(|| {
                eprint!("Invalid position\n");
                Exn::ExitWith(exit_status::T::InputError)
            })
        })
        .collect()
}

/// `Input_error` when the run was refused: the caller asked for more than the
/// limit allows and nothing was computed, so a zero exit would read as a run
/// that found nothing.
fn isolation_status(result: &server_isolation_types::Result) -> exit_status::T {
    match result.refused {
        Some(_) => exit_status::T::InputError,
        None => exit_status::T::NoError,
    }
}

/// The line about clusters that stopped at the size cap. It says "It" of a lone
/// cluster and "N of them" otherwise, and the verb agrees with the count.
fn truncated_clusters_sentence(total_clusters: isize, total_truncated: isize) -> String {
    format!(
        "{} stopped at the size cap and {} not complete.\n",
        if total_clusters == 1 {
            "It".to_string()
        } else {
            format!("{} of them", total_truncated)
        },
        if total_truncated == 1 { "is" } else { "are" }
    )
}

/// `output_isolation_result result ~output_json`
fn output_isolation_result(result: &server_isolation_types::Result, output_json: bool) {
    let _ = write_isolation_result(&mut std::io::stdout(), result, output_json);
}

/// [`output_isolation_result`] to `out`, so that the tests can read it.
fn write_isolation_result(
    out: &mut dyn std::io::Write,
    result: &server_isolation_types::Result,
    output_json: bool,
) -> std::io::Result<()> {
    use crate::utils::print_count;
    use crate::yojson::safe::T as J;
    use server_isolation_types::Movability;
    if output_json {
        let j = J::Assoc(vec![
            (
                "refused".to_string(),
                match &result.refused {
                    None => J::Null,
                    Some(reason) => J::String(reason.clone()),
                },
            ),
            (
                "movability".to_string(),
                match &result.movability {
                    None => J::Null,
                    Some(Movability::Movable) => J::String("movable".to_string()),
                    Some(Movability::Blocked(_)) => J::String("blocked".to_string()),
                },
            ),
            (
                "blockers".to_string(),
                match &result.movability {
                    Some(Movability::Blocked(blockers)) => {
                        J::List(blockers.iter().map(|b| J::String(b.file.clone())).collect())
                    }
                    _ => J::Null,
                },
            ),
            (
                "blocked_by".to_string(),
                match &result.movability {
                    Some(Movability::Blocked(blockers)) => J::List(
                        blockers
                            .iter()
                            .map(crate::client_isolation_move::blocker_to_json)
                            .collect(),
                    ),
                    _ => J::Null,
                },
            ),
            (
                "summary".to_string(),
                J::Assoc(vec![
                    ("grown".to_string(), J::Bool(result.grown)),
                    ("total_seeds".to_string(), J::Int(result.total_seeds)),
                    ("total_isolatable_files".to_string(), J::Int(result.total_isolatable_files)),
                    ("total_clusters".to_string(), J::Int(result.total_clusters)),
                    ("total_truncated".to_string(), J::Int(result.total_truncated)),
                    ("total_refused".to_string(), J::Int(result.total_refused)),
                    ("largest_cluster".to_string(), J::Int(result.largest_cluster)),
                ]),
            ),
        ]);
        write!(out, "{}\n", crate::yojson::safe::to_string(&j))
    } else {
        match (&result.refused, &result.movability) {
            (Some(reason), _) => write!(out, "Did not run: {}\n", reason),
            (None, Some(Movability::Movable)) => write!(
                out,
                "Movable: {}, nothing outside references in.\n",
                print_count(result.total_isolatable_files, "file")
            ),
            (None, Some(Movability::Blocked(blockers))) => {
                let files: Vec<String> = blockers.iter().map(|b| b.file.clone()).collect();
                write!(
                    out,
                    "Blocked: referenced from {} outside.\n",
                    print_count(files.len() as isize, "file")
                )?;
                crate::utils::fprint_capped_list(out, None, Some("; --json lists them all"), &files)
            }
            (None, None) => {
                write!(out, "Started from {}.\n", print_count(result.total_seeds, "file"))?;
                // Both modes report sets of files called clusters, and they mean different
                // things, so the line a person reads has to say which.
                if result.grown {
                    write!(
                        out,
                        "Grew {} covering {}{}.\n",
                        print_count(result.total_clusters, "cluster"),
                        print_count(result.total_isolatable_files, "file"),
                        // With one cluster the largest is that cluster, which the count
                        // already says.
                        if result.total_clusters > 1 {
                            format!(" (largest: {})", result.largest_cluster)
                        } else {
                            String::new()
                        }
                    )?;
                    // A truncated cluster stopped at the cap with more to take, so something
                    // outside it still references in. Saying how many kept that from being
                    // read as a count of finished packages. Read off the summary rather than
                    // counted here, so that it survives a run that streamed its clusters to a
                    // file and sent back none of them.
                    if result.total_truncated > 0 {
                        write!(
                            out,
                            "{}",
                            truncated_clusters_sentence(result.total_clusters, result.total_truncated)
                        )?
                    }
                } else {
                    write!(
                        out,
                        "Found {} without growing, covering {}{}.\n",
                        print_count(result.total_clusters, "isolatable cluster"),
                        print_count(result.total_isolatable_files, "file"),
                        if result.total_clusters > 1 {
                            format!(
                                " in all; the largest has {}",
                                print_count(result.largest_cluster, "file")
                            )
                        } else {
                            String::new()
                        }
                    )?
                }
                if result.total_refused > 0 {
                    write!(
                        out,
                        "Not in any cluster: {} (for example, more files depend on one than --isolation-max-dependents allows, or it declares nothing).\n",
                        print_count(result.total_refused, "starting file")
                    )?
                }
                Ok(())
            }
        }
    }
}

/// `Client_result_printer.Int_printer.go res output_json`
fn int_printer_go(res: &std::result::Result<isize, String>, output_json: bool) {
    use crate::yojson::safe::T as J;
    if output_json {
        let result = match res {
            Ok(i) => ("result".to_string(), J::Int(*i)),
            Err(s) => ("error_message".to_string(), J::String(s.clone())),
        };
        println!("{}", crate::yojson::safe::to_string(&J::Assoc(vec![result])))
    } else {
        match res {
            Ok(i) => print!("{}", i),
            Err(s) => {
                println!("Error: {}", s);
                {
                    use std::io::Write;
                    let _ = std::io::stdout().flush();
                }
                std::process::exit(1)
            }
        }
    }
}

/// `Find_my_tests.json_input_of_yojson` (`[@@deriving yojson]`: an object
/// with exactly the fields of the record, each once, the `[@default]` ones
/// optional). `None` is `Of_yojson_error`.
fn find_my_tests_json_input_of_yojson(
    json: &crate::yojson::safe::T,
) -> Option<server_command_types::find_my_tests::JsonInput> {
    use crate::yojson::safe::T as J;
    use server_command_types::find_my_tests;
    fn fields<'j>(json: &'j J, known: &[&str]) -> Option<std::collections::BTreeMap<String, &'j J>> {
        let J::Assoc(l) = json else { return None };
        let mut m = std::collections::BTreeMap::new();
        for (k, v) in l {
            if !known.contains(&k.as_str()) || m.insert(k.clone(), v).is_some() {
                return None;
            }
        }
        Some(m)
    }
    let int = |j: &J| match j {
        J::Int(i) => Some(*i),
        _ => None,
    };
    let int_opt = |j: Option<&&J>| -> Option<Option<isize>> {
        match j {
            None | Some(J::Null) => Some(None),
            Some(j) => int(j).map(Some),
        }
    };
    let bool_ = |j: Option<&&J>, d: bool| -> Option<bool> {
        match j {
            None => Some(d),
            Some(J::Bool(b)) => Some(*b),
            _ => None,
        }
    };
    let top = fields(json, &["roots", "config", "version"])?;
    let roots = match top.get("roots")? {
        J::List(l) => l
            .iter()
            .map(|r| match r {
                J::String(s) => Some(s.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?,
        _ => return None,
    };
    let c = fields(
        top.get("config")?,
        &[
            "max_distance",
            "max_test_files",
            "root_provenance",
            "reason_provenance",
            "path_provenance",
            "time_limit_secs",
            "test_count_checkpoint_secs",
            "symbol_node_count_checkpoint_interval",
            "test_file_node_count_checkpoint_interval",
            "max_method_parent_steps",
            "max_class_parent_steps",
            "parent_max_fanout_files",
            "non_parent_max_fanout_files",
            "enclosing_class_all_methods",
            "cldp_member_selection",
        ],
    )?;
    let config = find_my_tests::Config {
        max_distance: match c.get("max_distance") {
            None => 1,
            Some(j) => int(j)?,
        },
        max_test_files: int_opt(c.get("max_test_files"))?,
        root_provenance: bool_(c.get("root_provenance"), false)?,
        reason_provenance: bool_(c.get("reason_provenance"), false)?,
        path_provenance: bool_(c.get("path_provenance"), false)?,
        time_limit_secs: int_opt(c.get("time_limit_secs"))?,
        test_count_checkpoint_secs: match c.get("test_count_checkpoint_secs") {
            None => vec![20, 30, 40],
            Some(J::List(l)) => l.iter().map(int).collect::<Option<Vec<_>>>()?,
            Some(_) => return None,
        },
        symbol_node_count_checkpoint_interval: int_opt(c.get("symbol_node_count_checkpoint_interval"))?,
        test_file_node_count_checkpoint_interval: int_opt(c.get("test_file_node_count_checkpoint_interval"))?,
        max_method_parent_steps: int_opt(c.get("max_method_parent_steps"))?,
        max_class_parent_steps: int_opt(c.get("max_class_parent_steps"))?,
        parent_max_fanout_files: int_opt(c.get("parent_max_fanout_files"))?,
        non_parent_max_fanout_files: int_opt(c.get("non_parent_max_fanout_files"))?,
        enclosing_class_all_methods: bool_(c.get("enclosing_class_all_methods"), true)?,
        cldp_member_selection: bool_(c.get("cldp_member_selection"), false)?,
    };
    let version = find_my_tests::version_of_yojson(top.get("version")?).ok()?;
    Some(find_my_tests::JsonInput { roots, config, version })
}

/// `filter_real_paths ~allow_directories paths`: Filters and prints errors
/// when a path is not a realpath
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

/// An exception (`Sys_error`, as `Printexc.to_string` shows it) that
/// `main` reports as uncaught.
fn sys_error(message: String) -> Exn {
    let payload: Box<dyn std::any::Any + Send> = Box::new(message);
    Exn::Other(crate::exception::wrap(payload))
}

/// `Sys_utils.read_stdin_to_string ()`: every line of stdin, each followed
/// by a newline.
fn read_stdin_to_string() -> String {
    use std::io::BufRead;
    let mut buf: Vec<u8> = Vec::with_capacity(4096);
    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();
    loop {
        let mut line = vec![];
        match stdin.read_until(b'\n', &mut line) {
            Ok(0) | Err(_) => break,
            Ok(_) => {
                if line.last() == Some(&b'\n') {
                    line.pop();
                }
                buf.extend(line);
                buf.push(b'\n');
            }
        }
    }
    String::from_utf8_lossy(&buf).into_owned()
}

/// `expand_path file`: exits with 2 if the file is not found.
fn expand_path(file: &str) -> String {
    let path = crate::path::make(file);
    if crate::path::file_exists(&path) {
        crate::path::to_string(&path)
    } else {
        let cwd = std::env::current_dir()
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_default();
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

fn expand_file_path(file: &str) -> Result<String, Exn> {
    let path = expand_path(file);
    if std::path::Path::new(&path).is_dir() {
        eprintln!("Path is a directory, only files are allowed: '{}'", file);
        return Err(Exn::ExitWith(exit_status::T::InputError));
    }
    Ok(path)
}

/// `parse_position_string ~split_on arg`
fn parse_position_string(split_on: &str, arg: &str) -> Result<(isize, isize), Exn> {
    let tpos = crate::rt::ocaml_str::split(split_on, arg);
    match &tpos[..] {
        [line, char] => {
            // (The tuple is evaluated from its last component.)
            if let Some(char) = int_of_string_opt(char) {
                if let Some(line) = int_of_string_opt(line) {
                    return Ok((line, char));
                }
            }
        }
        _ => {}
    }
    eprint!("Invalid position\n");
    Err(Exn::ExitWith(exit_status::T::InputError))
}

/// The `[filename; line; char]` / `[line; char]` argument of
/// `MODE_TYPE_AT_POS` and `MODE_TYPE_ERROR_AT_POS`, with the message of
/// each mode.
fn parse_file_input_position(
    arg: &str,
    invalid: &str,
) -> Result<(server_command_types::FileInput, isize, isize), Exn> {
    let tpos = crate::rt::ocaml_str::split(":", arg);
    let parsed = match &tpos[..] {
        [filename, line, char] => {
            let fn_ = expand_path(filename);
            match (int_of_string_opt(char), int_of_string_opt(line)) {
                (Some(char), Some(line)) => Some((server_command_types::FileInput::FileName(fn_), line, char)),
                _ => None,
            }
        }
        [line, char] => {
            let content = read_stdin_to_string();
            match (int_of_string_opt(char), int_of_string_opt(line)) {
                (Some(char), Some(line)) => Some((server_command_types::FileInput::FileContent(content), line, char)),
                _ => None,
            }
        }
        _ => None,
    };
    match parsed {
        Some(x) => Ok(x),
        None => {
            eprint!("{}\n", invalid);
            Err(Exn::ExitWith(exit_status::T::InputError))
        }
    }
}

/// `main_internal args config local_config partial_telemetry_ref`
pub fn main_internal(
    args: &client_env::ClientCheckEnv,
    config: &server_config::T,
    local_config: &server_local_config::T,
    partial_telemetry_ref: &PartialTelemetryRef,
) -> Result<(exit_status::T, telemetry::T), Exn> {
    let connect_then_close = || connect_then_close(args);
    // `rpc_with_connection`'s `conn` for `command`.
    let conn_for = |command: &server_command_types::T| {
        let use_priority_pipe = server_command_types::use_priority_pipe(command);
        move || connect(Some(use_priority_pipe), None, args)
    };
    match &args.mode {
        ClientMode::ModeStatus => {
            let prechecked = args.prechecked.unwrap_or(true);
            let ((), telemetry1): ((), telemetry::T) = if prechecked {
                ((), telemetry::create())
            } else {
                rpc(args, server_command_types::T::NoPrecheckedFiles)?
            };
            let error_filter = error_filter(config, local_config, args);
            // We don't do streaming errors under [output_json]: our contract
            // with the outside world is that if a caller uses [output_json] then they
            // will never see [Exit_status.Typecheck_restarted], which streaming might show.
            //
            // We don't do streaming errors under [not prechecked]. That's because the
            // [go_streaming] contract is to report on a typecheck that reflects all *file*
            // changes up until now; it has no guarantee that the typecheck will reflects our
            // preceding call to Server_command_types.NO_PRECHECKED_FILES.
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
                    server_command_types::T::Status {
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
        ClientMode::ModeStatusFiles(client_env::StatusFiles {
            filenames,
            show_tast,
            preexisting_warnings,
        }) => {
            let file_input = |filename: &String| -> Result<server_command_types::FileInput, Exn> {
                Ok(match filename.as_str() {
                    "-" => server_command_types::FileInput::FileContent(read_stdin_to_string()),
                    _ => server_command_types::FileInput::FileName(expand_file_path(filename)?),
                })
            };
            let file_inputs = filenames.iter().map(file_input).collect::<Result<Vec<_>, _>>()?;
            let error_filter = error_filter(config, local_config, args);
            let (((error_list, dropped_count), tasts), telemetry): (server_command_types::StatusSingleResult, _) =
                rpc(
                    args,
                    server_command_types::T::StatusSingle {
                        file_names: file_inputs,
                        max_errors: args.max_errors,
                        error_filter,
                        return_expanded_tast: *show_tast,
                        preexisting_warnings: *preexisting_warnings,
                    },
                )?;
            match tasts {
                None => {}
                Some(server_command_types::ShownTasts { hashes, tasts }) => {
                    // `Printf.printf "TAST hashes:\n\n"`, the JSON
                    // (`pretty_to_channel`), then the TASTs.
                    print!("TAST hashes:\n\n");
                    print!("{}", hashes);
                    print!("\n\n\nTASTs:\n\n{}\n", tasts);
                    use std::io::Write;
                    let _ = std::io::stdout().flush();
                }
            }
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
        ClientMode::ModeLogErrors(client_env::LogErrorsParams {
            log_file,
            preexisting_warnings,
        }) => {
            let files = filter_real_paths(false, &args.paths);
            let error_filter = error_filter(config, local_config, args);
            let ((), telemetry): ((), _) = rpc(
                args,
                server_command_types::T::LogErrors {
                    files,
                    log_file: log_file.clone(),
                    error_filter,
                    preexisting_warnings: *preexisting_warnings,
                },
            )?;
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeListFiles => {
            let (infol, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::ListFilesWithErrors)?;
            for s in &infol {
                print!("{}\n", s);
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeFindClassRefs(name) => {
            let command = server_command_types::T::FindRefs(find_refs::Action::Class(name.clone()));
            let results: Vec<find_refs::Absolute> = rpc_with_retry(conn_for(&command), &args.desc, command)?;
            print_refs(&results, args.output_json);
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeFindRefs(name) => {
            let pieces = crate::rt::ocaml_str::split("|", name);
            let (kind, name) = match &pieces[..] {
                [name] => (None, name.clone()),
                [kind, name] => (Some(kind.clone()), name.clone()),
                _ => {
                    eprint!("Invalid input\n");
                    return Err(Exn::ExitWith(exit_status::T::InputError));
                }
            };
            let kind = kind.as_deref();
            let action = parse_name_or_member_id(
                |name| match kind {
                    Some("Function") | None => Some(find_refs::Action::Function(name)),
                    Some("Class") => Some(find_refs::Action::Class(name)),
                    Some("ExplicitClass") => Some(find_refs::Action::ExplicitClass(name)),
                    Some("GConst") => Some(find_refs::Action::GConst(name)),
                    Some(_) => None,
                },
                |class_name, member_name| {
                    let member = match kind {
                        Some("Method") | None => find_refs::Member::Method(member_name),
                        Some("Property") => find_refs::Member::Property(member_name),
                        Some("Class_const") => find_refs::Member::ClassConst(member_name),
                        Some("Typeconst") => find_refs::Member::Typeconst(member_name),
                        Some(_) => return None,
                    };
                    Some(find_refs::Action::Member(class_name, member))
                },
                &name,
            )?;
            let command = server_command_types::T::FindRefs(action);
            let results: Vec<find_refs::Absolute> = rpc_with_retry(conn_for(&command), &args.desc, command)?;
            print_refs(&results, args.output_json);
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeGoToImplClass(class_name) => {
            let command = server_command_types::T::GoToImpl(find_refs::Action::Class(class_name.clone()));
            let results: Vec<find_refs::Absolute> = rpc_with_retry(conn_for(&command), &args.desc, command)?;
            print_refs(&results, args.output_json);
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeGoToImplMethod(name) => {
            let action = parse_name_or_member_id(
                |fun_name| Some(find_refs::Action::Function(fun_name)),
                |class_name, method_name| {
                    Some(find_refs::Action::Member(class_name, find_refs::Member::Method(method_name)))
                },
                name,
            )?;
            match action {
                find_refs::Action::Member(..) => {
                    let command = server_command_types::T::GoToImpl(action);
                    let results: Vec<find_refs::Absolute> =
                        rpc_with_retry(conn_for(&command), &args.desc, command)?;
                    print_refs(&results, args.output_json);
                    Ok((exit_status::T::NoError, telemetry::create()))
                }
                _ => {
                    eprint!("Invalid input\n");
                    Ok((exit_status::T::InputError, telemetry::create()))
                }
            }
        }
        ClientMode::ModeHackToNotebook => {
            let exit_status = crate::notebook_convert::hack_to_notebook(&read_stdin_to_string());
            Ok((exit_status, telemetry::create()))
        }
        ClientMode::ModeIdeFindRefsBySymbol(arg) => {
            let command = server_command_types::T::IdeFindRefsBySymbol(arg.clone());
            let results: Vec<find_refs::Absolute> = rpc_with_retry(conn_for(&command), &args.desc, command)?;
            println!("{}", crate::find_refs_wire_format::ide_shellout::to_string(&results));
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeIdeGoToImplBySymbol(arg) => {
            let command = server_command_types::T::IdeGoToImplBySymbol(arg.clone());
            let results: Vec<find_refs::Absolute> = rpc_with_retry(conn_for(&command), &args.desc, command)?;
            println!("{}", crate::find_refs_wire_format::ide_shellout::to_string(&results));
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeDumpSymbolInfo(files) => {
            // `Client_symbol_info.go conn ~desc files expand_path`
            let conn = connect(None, None, args)?;
            let file_list: Vec<String> = match files.as_str() {
                "-" => {
                    let content = read_stdin_to_string();
                    crate::rt::ocaml_str::split("\n", &content)
                }
                _ => crate::rt::ocaml_str::split(";", files),
            };
            // `List.rev_map`
            let expanded: Vec<String> = file_list.iter().rev().map(|f| expand_path(f)).collect();
            let command = server_command_types::T::DumpSymbolInfo(expanded);
            let (result, _telemetry): (server_command_types::symbol_info_service::Result, _) =
                client_connect::rpc(&conn, &args.desc, command)?;
            let result_json = server_command_types::symbol_info_service::to_json(&result);
            println!("{}", crate::yojson::safe::to_string(&result_json));
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeRename(ref_mode, before, after) => {
            let conn = || connect(None, None, args);
            crate::client_rename::go(conn, &args.desc, args, ref_mode, before, after)?;
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeIdeRenameBySymbol(arg) => {
            let (new_name, action, symbol_definition) =
                server_command_types::rename::string_to_args(arg).map_err(|e| Exn::ExitWith(e.0))?;
            let command = server_command_types::T::IdeRenameBySymbol(action, new_name, symbol_definition);
            let results: server_command_types::rename::IdeResult =
                rpc_with_retry(conn_for(&command), &args.desc, command)?;
            match results {
                Ok(patches) => {
                    crate::client_rename::go_ide_from_patches(&patches, args.output_json);
                    Ok((exit_status::T::NoError, telemetry::create()))
                }
                Err(_msg) => Err(Exn::ExitWith(exit_status::T::InputError)),
            }
        }
        ClientMode::ModeIdentifySymbol(arg) => {
            if !args.output_json {
                eprint!("Must use --json\n");
                return Err(Exn::ExitWith(exit_status::T::InputError));
            }
            let (result, telemetry): (Vec<crate::symbol_definition::T<crate::pos::Absolute>>, _) = rpc(
                args,
                server_command_types::T::IdentifySymbol(arg.clone()),
            )?;
            let definition_to_json = |d: &crate::symbol_definition::T<crate::pos::Absolute>| {
                crate::yojson::safe::T::Assoc(vec![
                    (
                        "full_name".to_string(),
                        crate::yojson::safe::T::String(crate::symbol_definition::full_name(d)),
                    ),
                    ("pos".to_string(), crate::pos::json(&d.pos)),
                    (
                        "kind".to_string(),
                        crate::yojson::safe::T::String(
                            crate::symbol_definition::string_of_kind(&d.kind).to_string(),
                        ),
                    ),
                ])
            };
            let definitions = result.iter().map(definition_to_json).collect();
            println!(
                "{}",
                crate::yojson::safe::to_string(&crate::yojson::safe::T::List(definitions))
            );
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeIdentifySymbol1(arg)
        | ClientMode::ModeIdentifySymbol2(arg)
        | ClientMode::ModeIdentifySymbol3(arg) => {
            let (line, char) = parse_position_string(":", arg)?;
            let pos = crate::file_content::position::from_one_based(line, char);
            let file = match &args.stdin_name {
                None => String::new(),
                Some(f) => expand_path(f),
            };
            let content = server_command_types::FileInput::FileContent(read_stdin_to_string());
            let (result, telemetry): (server_command_types::identify_symbol::Result, _) = rpc(
                args,
                server_command_types::T::IdentifyFunction(file, content, pos),
            )?;
            crate::client_get_definition::go(&result, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeTypeAtPos(arg) => {
            let (fn_, line, char) = parse_file_input_position(arg, "Invalid position")?;
            let pos = crate::file_content::position::from_one_based(line, char);
            let (ty, telemetry): (crate::infer_at_pos_service::Result, _) = rpc(
                args,
                server_command_types::T::InferType(fn_, pos),
            )?;
            crate::client_type_at_pos::go(ty, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeInferDynamic(arg, as_data) => {
            let (json, telemetry): (crate::yojson::safe::T, _) = rpc(
                args,
                server_command_types::T::InferDynamic(arg.clone(), *as_data),
            )?;
            print!("{}\n", crate::yojson::safe::pretty_to_string(&json));
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeEnforcementAtPosBatch(positions) => {
            use crate::file_content::position;
            let mut parsed = vec![];
            for pos in positions {
                let p = match &crate::rt::ocaml_str::split(":", pos)[..] {
                    [filename, line, char] => match (int_of_string_opt(char), int_of_string_opt(line)) {
                        (Some(char), Some(line)) => Some((expand_path(filename), position::from_one_based(line, char))),
                        _ => None,
                    },
                    _ => None,
                };
                match p {
                    Some(p) => parsed.push(p),
                    None => {
                        eprint!("Invalid position\n");
                        return Err(Exn::ExitWith(exit_status::T::InputError));
                    }
                }
            }
            let (responses, telemetry): (Vec<String>, _) = rpc(
                args,
                server_command_types::T::EnforcementAtPosBatch(parsed),
            )?;
            for r in &responses {
                println!("{}", r);
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeTypeAtPosBatch(positions) => {
            use crate::file_content::position;
            let invalid = || {
                eprint!("Invalid position\n");
                Exn::ExitWith(exit_status::T::InputError)
            };
            let mut parsed = vec![];
            for pos in positions {
                parsed.push(match &crate::rt::ocaml_str::split(":", pos)[..] {
                    [filename, line, char] => {
                        // (The tuple is evaluated from its last component.)
                        let char = int_of_string_opt(char).ok_or_else(invalid)?;
                        let line = int_of_string_opt(line).ok_or_else(invalid)?;
                        let start = position::from_one_based(line, char);
                        (expand_path(filename), start, None)
                    }
                    [filename, start_line, start_char, end_line, end_char] => {
                        let filename = expand_path(filename);
                        let start_line = int_of_string_opt(start_line).ok_or_else(invalid)?;
                        let start_char = int_of_string_opt(start_char).ok_or_else(invalid)?;
                        let end_line = int_of_string_opt(end_line).ok_or_else(invalid)?;
                        let end_char = int_of_string_opt(end_char).ok_or_else(invalid)?;
                        let start_pos = position::from_one_based(start_line, start_char);
                        let end_pos = position::from_one_based(end_line, end_char);
                        (filename, start_pos, Some(end_pos))
                    }
                    _ => return Err(invalid()),
                })
            }
            let (responses, telemetry): (Vec<String>, _) = rpc(
                args,
                server_command_types::T::InferTypeBatch(parsed),
            )?;
            for r in &responses {
                println!("{}", r);
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeIsSubtype => {
            let stdin = read_stdin_to_string();
            let (response, telemetry): (std::result::Result<String, String>, _) =
                rpc(args, server_command_types::T::IsSubtype(stdin))?;
            match response {
                Ok(str) => {
                    print!("{}", str);
                    Ok((exit_status::T::NoError, telemetry))
                }
                Err(str) => {
                    eprint!("{}", str);
                    Err(Exn::ExitWith(exit_status::T::InputError))
                }
            }
        }
        ClientMode::ModeTypeErrorAtPos(arg) => {
            let (fn_, line, char) = parse_file_input_position(
                arg,
                "Invalid position; expected an argument of the form [filename]:[line]:[column] or [line]:[column]",
            )?;
            let (ty, telemetry): (crate::infer_error_at_pos_service::Result, _) = rpc(
                args,
                server_command_types::T::InferTypeError(fn_, line, char),
            )?;
            crate::client_type_error_at_pos::go(ty, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeTastHoles(arg) => {
            use server_command_types::tast_hole::Filter;
            let parse_hole_filter = |s: &str| match s {
                "any" => Some(Filter::Any),
                "typing" => Some(Filter::Typing),
                "cast" => Some(Filter::Cast),
                _ => None,
            };
            let invalid = || {
                eprint!(
                    "Invalid argument; expected an argument of the form [filename](:[any|typing|cast])? or [any|typing|cast]\n"
                );
                Exn::ExitWith(exit_status::T::InputError)
            };
            let (filename, hole_src_opt) = match &crate::rt::ocaml_str::split(":", arg)[..] {
                [filename, filter_str] => {
                    let fn_ = expand_path(filename);
                    match parse_hole_filter(filter_str) {
                        Some(filter) => (server_command_types::FileInput::FileName(fn_), filter),
                        _ => return Err(invalid()),
                    }
                }
                [part] => match parse_hole_filter(part) {
                    Some(src_opt) => {
                        let content = read_stdin_to_string();
                        (server_command_types::FileInput::FileContent(content), src_opt)
                    }
                    _ => {
                        let fn_ = expand_path(part);
                        // No hole source specified; default to `Typing`
                        (server_command_types::FileInput::FileName(fn_), Filter::Typing)
                    }
                },
                _ => return Err(invalid()),
            };
            let (ty, telemetry): (crate::tast_holes_service::Result, _) = rpc(
                args,
                server_command_types::T::TastHoles(filename, hole_src_opt),
            )?;
            crate::client_tast_holes::go(&ty, false, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeTastHolesBatch(file) => {
            let path = expand_path(file);
            let content = match crate::sys_utils::cat(&path) {
                Ok(c) => String::from_utf8_lossy(&c).into_owned(),
                Err(e) => return Err(sys_error(format!("Sys_error({:?})", e.0))),
            };
            // `String.strip |> String.split ~on:'\n' |> List.map ~f:expand_path`
            let files: Vec<String> = content.trim().split('\n').map(expand_path).collect();
            let (holes, telemetry): (crate::tast_holes_service::Result, _) = rpc(
                args,
                server_command_types::T::TastHolesBatch(files),
            )?;
            crate::client_tast_holes::go(&holes, true, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeFunDepsAtPosBatch(positions) => {
            let positions = parse_positions(positions)?;
            let (responses, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::FunDepsBatch(positions))?;
            for r in &responses {
                println!("{}", r);
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeDepsOutAtPosBatch(positions) => {
            let positions = parse_positions(positions)?;
            let (responses, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::DepsOutBatch(positions))?;
            for r in &responses {
                println!("{}", r);
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeOutline | ClientMode::ModeOutline2 => {
            // (`Shared_mem.init ~num_workers:0 Shared_mem.default_config`:
            // there is no shared memory.)
            let content = read_stdin_to_string();
            let results = crate::file_outline::outline(
                // TODO: Don't use default parser options.
                //
                // Parser options enables certain features (such as namespace aliasing)
                // Thus, for absolute correctness of outlining, we need to use the same
                // parser options that the server uses. But this client request doesn't
                // hit the server at all. So either change this to a server RPC, or
                // ask the server what its parser options are, or parse the
                // options from the .hhconfig file (needs to be the same hhconfig file the
                // server used).
                &oxidized::parser_options::ParserOptions::default(),
                content.as_bytes(),
            );
            crate::client_outline::go(&results, args.output_json);
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeOutlineForAgents(path) => {
            let content = match crate::sys_utils::cat(path) {
                Ok(content) => content,
                Err(e) => return Err(sys_error(format!("Sys_error({:?})", e.0))),
            };
            let result = crate::outline_for_agents::outline(&content);
            {
                use std::io::Write;
                let _ = std::io::stdout().write_all(&result);
            }
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeMethodJumpChildren(class_) => {
            let filter = server_command_types::method_jumps::Filter::NoFilter;
            let (results, telemetry): (Vec<server_command_types::method_jumps::Result>, _) = rpc(
                args,
                server_command_types::T::MethodJump((class_.clone(), filter, true)),
            )?;
            crate::client_method_jumps::go(&results, true, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeMethodJumpAncestors(class_, filter) => {
            let filter = match crate::method_jumps::string_filter_to_method_jump_filter(filter) {
                Some(filter) => filter,
                None => {
                    eprint!("Invalid method jump filter {}\n", filter);
                    return Err(Exn::ExitWith(exit_status::T::InputError));
                }
            };
            let (results, telemetry): (Vec<server_command_types::method_jumps::Result>, _) = rpc(
                args,
                server_command_types::T::MethodJump((class_.clone(), filter, false)),
            )?;
            crate::client_method_jumps::go(&results, false, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeMethodJumpAncestorsBatch(classes, filter) => {
            let filter = match crate::method_jumps::string_filter_to_method_jump_filter(filter) {
                Some(filter) => filter,
                None => {
                    eprint!("Invalid method jump filter {}\n", filter);
                    return Err(Exn::ExitWith(exit_status::T::InputError));
                }
            };
            let (results, telemetry): (Vec<server_command_types::method_jumps::Result>, _) = rpc(
                args,
                server_command_types::T::MethodJumpBatch((classes.clone(), filter)),
            )?;
            crate::client_method_jumps::go(&results, false, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeNotebookToHack {
            notebook_number,
            notebook_header,
        } => {
            let source = read_stdin_to_string();
            let exit_status = crate::notebook_convert::notebook_to_hack(notebook_number, notebook_header, &source);
            Ok((exit_status, telemetry::create()))
        }
        ClientMode::ModeInMemoryDepTableSize => {
            let (result, telemetry): (std::result::Result<isize, String>, _) =
                rpc(args, server_command_types::T::InMemoryDepTableSize)?;
            int_printer_go(&result, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeSaveNaming(path) => {
            let dir = crate::path::dirname(path);
            if let Err(e) = crate::sys_utils::mkdir_p(&dir) {
                // `Unix.Unix_error (e, "mkdir", d)` of the first directory
                // that could not be made.
                let mut d = dir.clone();
                loop {
                    let parent = crate::path::dirname(&d);
                    if parent == d || std::path::Path::new(&parent).exists() {
                        break;
                    }
                    d = parent;
                }
                return Err(Exn::Other(crate::exception::wrap(UnixErrorPrinted(
                    crate::rt::ocaml_unix::unix_error_to_string(&e, "mkdir", &d),
                ))));
            }
            let path = crate::path::make(path);
            let (result, telemetry): (std::result::Result<crate::save_state_service_types::SaveNamingResult, String>, _) =
                rpc(args, server_command_types::T::SaveNaming(crate::path::to_string(&path)))?;
            crate::client_result_printer::go::<SaveNamingResultPrinter>(&result, args.output_json);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModePause => {
            let ((), telemetry): ((), _) = rpc(args, server_command_types::T::Pause)?;
            println!("Paused automatic rechecks. The next client request resumes them.");
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeSearch(query) => {
            if query != "this_is_just_to_check_liveness_of_hh_server" {
                eprintln!("Usage: hh --search this_is_just_to_check_liveness_of_hh_server");
                Ok((exit_status::T::InputError, telemetry::create()))
            } else {
                let ((), telemetry): ((), _) =
                    rpc(args, server_command_types::T::CheckLiveness)?;
                if args.output_json {
                    println!("[]");
                }
                Ok((exit_status::T::NoError, telemetry))
            }
        }
        ClientMode::ModeLint => {
            let fnl = filter_real_paths(false, &args.paths);
            match &args.paths[..] {
                [] => {
                    eprintln!("No lint errors (0 files checked)!");
                    eprintln!("Note: --lint expects a list of filenames to check.");
                    Ok((exit_status::T::NoError, telemetry::create()))
                }
                _ => {
                    let (results, telemetry): (crate::server_lint_types::Result, _) =
                        rpc(args, server_command_types::T::Lint(fnl))?;
                    let error_format = crate::diagnostics::format_or_default(args.error_format);
                    crate::client_lint::go(&results, args.output_json, error_format);
                    Ok((exit_status::T::NoError, telemetry))
                }
            }
        }
        ClientMode::ModeServerRage => {
            use crate::yojson::safe::T as J;
            if !args.output_json {
                eprint!("Must use --json\n");
                return Err(Exn::ExitWith(exit_status::T::InputError));
            }
            // Our json output format is read by clientRage.ml
            let (items, telemetry): (crate::server_rage_types::Result, _) =
                rpc(args, server_command_types::T::Rage)?;
            let make_item = |i: &crate::server_rage_types::RageItem| {
                J::Assoc(vec![
                    ("name".to_string(), J::String(i.title.clone())),
                    ("contents".to_string(), J::String(i.data.clone())),
                ])
            };
            println!(
                "{}",
                crate::yojson::safe::to_string(&J::List(items.iter().map(make_item).collect()))
            );
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeLintStdin(filename) => match crate::sys_utils::realpath(filename) {
            None => {
                eprintln!("Could not find file '{}'", filename);
                Ok((exit_status::T::InputError, telemetry::create()))
            }
            Some(filename) => {
                let contents = read_stdin_to_string();
                let (results, telemetry): (crate::server_lint_types::Result, _) = rpc(
                    args,
                    server_command_types::T::LintStdin(server_command_types::LintStdinInput {
                        filename,
                        contents,
                    }),
                )?;
                let error_format = crate::diagnostics::format_or_default(args.error_format);
                crate::client_lint::go(&results, args.output_json, error_format);
                Ok((exit_status::T::NoError, telemetry))
            }
        },
        ClientMode::ModeLintAll(code) => {
            let (results, telemetry): (crate::server_lint_types::Result, _) =
                rpc(args, server_command_types::T::LintAll(*code))?;
            let error_format = crate::diagnostics::format_or_default(args.error_format);
            crate::client_lint::go(&results, args.output_json, error_format);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeStats => {
            let (stats, telemetry): (stats::T, _) = rpc(args, server_command_types::T::Stats)?;
            print!(
                "{}",
                crate::yojson::safe::pretty_to_string(&stats::to_json(&stats))
            );
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeRemoveDeadFixmes(codes) => {
            let conn = connect(None, None, args)?;
            let (response, telemetry): (server_command_types::PatchesOrError, _) = client_connect::rpc(
                &conn,
                &args.desc,
                server_command_types::T::RemoveDeadFixmes(codes.clone()),
            )?;
            match response {
                server_command_types::PatchesOrError::Error(msg) => {
                    eprint!("{}\n", msg);
                    Ok((exit_status::T::TypeError, telemetry))
                }
                server_command_types::PatchesOrError::Ok(patches) => {
                    if args.output_json {
                        crate::client_rename::print_patches_json(&patches)
                    } else {
                        crate::client_rename::apply_patches(&patches)
                    }
                    Ok((exit_status::T::NoError, telemetry))
                }
            }
        }
        ClientMode::ModeRemoveDeadUnsafeCasts => {
            let error_filter = error_filter(config, local_config, args);
            loop {
                let (response, telemetry): (server_command_types::PatchesOrError, _) =
                    rpc(args, server_command_types::T::RemoveDeadUnsafeCasts)?;
                match response {
                    server_command_types::PatchesOrError::Error(msg) => {
                        eprint!("{}\n", msg);
                        return Ok((exit_status::T::TypeError, telemetry));
                    }
                    server_command_types::PatchesOrError::Ok(patches) => {
                        crate::client_rename::apply_patches(&patches);
                        if patches.is_empty() {
                            return Ok((exit_status::T::NoError, telemetry));
                        } else {
                            let (_, _): (server_command_types::server_status::T, _) = rpc(
                                args,
                                server_command_types::T::Status {
                                    max_errors: args.max_errors,
                                    error_filter: error_filter.clone(),
                                },
                            )?;
                        }
                    }
                }
            }
        }
        ClientMode::ModeRewriteDeclarations => {
            // HHVM uses existence of this file to indicate it is paused, which
            // happens when HHVM is at a breakpoint.
            // Is also read by the language server.
            let _file_whose_existence_indicates_hhvm_is_paused =
                std::env::var("HOME").ok().map(|home_dir| format!("{}/.vscode-sockets/hhvm-paused", home_dir));
            // `Declarations_rewriter.start (Random.State.make_self_init ())
            // ~file_whose_existence_indicates_hhvm_is_paused`: the OSS stub
            // (`stubs/declarations_rewriter.ml`) does nothing.
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeRewriteLambdaParameters(files) => {
            let conn = connect(None, None, args)?;
            let (patches, telemetry): (Vec<crate::server_rename_types::Patch>, _) = client_connect::rpc(
                &conn,
                &args.desc,
                server_command_types::T::RewriteLambdaParameters(files.clone()),
            )?;
            if args.output_json {
                crate::client_rename::print_patches_json(&patches)
            } else {
                crate::client_rename::apply_patches(&patches)
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeFullFidelityParse(file) => {
            // We can cheaply do this on the client today, but we might want to
            // do it on the server and cache the results in the future.
            let do_it_on_server = false;
            let (results, telemetry): (String, _) = if do_it_on_server {
                rpc(args, server_command_types::T::DumpFullFidelityParse(file.clone()))?
            } else {
                (
                    crate::full_fidelity_parse_service::go_result(file).map_err(sys_error)?,
                    telemetry::create(),
                )
            };
            // `Client_full_fidelity_parse.go results`
            println!("{}", results);
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeFullFidelitySchema => {
            // `Full_fidelity_schema.schema_as_json ()`
            print!("{}", crate::full_fidelity_parse_service::SCHEMA_AS_JSON);
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeCstSearch(files_to_search) => {
            let sort_results = args.sort_results;
            let input = match crate::yojson::safe::from_string(&read_stdin_to_string()) {
                Ok(j) => j,
                // `Yojson.Json_error`, uncaught
                Err(e) => return Err(sys_error(format!("Yojson.Json_error({:?})", e.0))),
            };
            let (result, telemetry): (std::result::Result<crate::yojson::safe::T, String>, _) = rpc(
                args,
                server_command_types::T::CstSearch(server_command_types::CstSearchInput {
                    sort_results,
                    input,
                    files_to_search: files_to_search.clone(),
                }),
            )?;
            match result {
                Ok(result) => {
                    println!("{}", crate::yojson::safe::to_string(&result));
                    Ok((exit_status::T::NoError, telemetry))
                }
                Err(error) => {
                    println!("{}", error);
                    Err(Exn::ExitWith(exit_status::T::InputError))
                }
            }
        }
        ClientMode::ModeFileLevelDependencies => {
            use crate::yojson::safe::T as J;
            let paths = filter_real_paths(true, &args.paths);
            let (responses, telemetry): (Vec<String>, _) =
                rpc(args, server_command_types::T::FileDependents(paths))?;
            if args.output_json {
                let json_path_list = responses.iter().map(|p| J::String(p.clone())).collect();
                let output = J::Assoc(vec![("dependents".to_string(), J::List(json_path_list))]);
                println!("{}", crate::yojson::safe::to_string(&output));
            } else {
                for p in &responses {
                    print!("{}\n", p);
                }
            }
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeIsolation(
            options @ server_isolation_types::Options {
                mode: server_isolation_types::Mode::MoveTo(parent),
                ..
            },
        ) => {
            let error_filter = error_filter(config, local_config, args);
            let exit_status = crate::client_isolation_move::move_into(
                args,
                &|use_priority_pipe| connect(Some(use_priority_pipe), None, args),
                options,
                &error_filter,
                parent,
            )?;
            Ok((exit_status, telemetry::create()))
        }
        ClientMode::ModeIsolation(options) => {
            use server_isolation_types::ClustersDestination;
            // Clusters are written by the server, never returned: there can be
            // hundreds of thousands. With [--json] and no file of the caller's own,
            // they go to a temporary one that is printed and removed here, so stdout
            // costs no more memory than a file does.
            let temp_file = match (&options.clusters_destination, args.output_json) {
                (ClustersDestination::Dropped, true) => Some(filename_temp_file("hh_isolation", ".jsonl")?),
                _ => None,
            };
            let options = match &temp_file {
                Some(path) => server_isolation_types::Options {
                    clusters_destination: ClustersDestination::ToFile(path.clone()),
                    ..options.clone()
                },
                None => options.clone(),
            };
            // [Lwt.finalize] rather than wrapping only the printing: the file exists
            // before the query is sent, so a query that raises must still clean it
            // up.
            let run = || -> Result<(exit_status::T, telemetry::T), Exn> {
                let (result, telemetry): (server_isolation_types::Result, _) = rpc(
                    args,
                    server_command_types::T::FindIsolatableClusters(options.clone()),
                )?;
                // A line at a time. Reading the file into a list first would hold
                // every cluster in memory, which is the cost this avoids.
                if let Some(path) = &temp_file {
                    print_lines_of_file(path)?;
                }
                output_isolation_result(&result, args.output_json);
                match &options.clusters_destination {
                    ClustersDestination::ToFile(path) if temp_file.is_none() && !args.output_json => {
                        print!("Clusters written to {}.\n", path)
                    }
                    _ => {}
                }
                Ok((isolation_status(&result), telemetry))
            };
            crate::utils::try_finally(run, || {
                if let Some(path) = &temp_file {
                    let _ = std::fs::remove_file(path);
                }
            })
        }
        ClientMode::ModeValidateIsolation(list_file) => {
            // Read here rather than on the server: the list file is a path on the
            // caller's machine, and the server only ever sees repo-relative paths.
            let files: Vec<String> = match crate::sys_utils::cat(list_file) {
                Err(_) => {
                    eprint!("Could not read {}\n", list_file);
                    return Err(Exn::ExitWith(exit_status::T::InputError));
                }
                Ok(contents) => split_lines(&String::from_utf8_lossy(&contents))
                    .into_iter()
                    .filter_map(|line| match base_strip(line) {
                        "" => None,
                        path => Some(path.to_string()),
                    })
                    .collect(),
            };
            if files.is_empty() {
                eprint!(
                    "{} names no files. --validate-isolation takes a file of repo-relative paths, one per line.\n",
                    list_file
                );
                return Err(Exn::ExitWith(exit_status::T::InputError));
            }
            let (result, telemetry): (server_command_types::isolation_validation::Result, _) =
                rpc(args, server_command_types::T::ValidateIsolation(files))?;
            crate::client_isolation_validate::output(&result, args.output_json);
            Ok((crate::client_isolation_validate::status(&result), telemetry))
        }
        ClientMode::ModeVerbose(verbose) => {
            let ((), telemetry): ((), _) =
                rpc(args, server_command_types::T::Verbose(*verbose))?;
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModeDepsInAtPosBatch(positions) => {
            let positions = parse_positions(positions)?;
            let command = server_command_types::T::DepsInBatch(positions);
            let use_priority_pipe = server_command_types::use_priority_pipe(&command);
            let c = connect(Some(use_priority_pipe), None, args)?;
            let (job_list, _): (Vec<server_command_types::done_or_retry::T<Vec<find_refs::Absolute>>>, _) =
                client_connect::rpc(&c, &args.desc, command)?;
            // `rpc_with_retry_list`: a `Retry` stays one, twice: Two_retries_in_a_row.
            let mut results = vec![];
            for job in job_list {
                match job {
                    server_command_types::done_or_retry::T::Done(x) => results.push(x),
                    server_command_types::done_or_retry::T::Retry => {
                        return Err(Exn::from(client_connect::ClientConnectError::TwoRetriesInARow(
                            server_command_types::done_or_retry::TwoRetriesInARow,
                        )));
                    }
                }
            }
            for s in &results {
                print_refs(s, true)
            }
            Ok((exit_status::T::NoError, telemetry::create()))
        }
        ClientMode::ModeFindMyTests(path) => {
            use server_command_types::find_my_tests;
            let parse_symbol = |symbol: &String| -> Result<find_my_tests::Action, Exn> {
                let pieces = crate::rt::ocaml_str::split("|", symbol);
                let (kind, name) = match &pieces[..] {
                    [name] => (None, name.clone()),
                    [kind, name] => (Some(kind.clone()), name.clone()),
                    _ => {
                        eprint!("Invalid input\n");
                        return Err(Exn::ExitWith(exit_status::T::InputError));
                    }
                };
                let (kind, soft) = match kind {
                    Some(s) => match s.strip_suffix("@soft") {
                        Some(base) => (Some(base.to_string()), true),
                        None => (Some(s), false),
                    },
                    None => (None, false),
                };
                let kind = kind.as_deref();
                let action_kind = parse_name_or_member_id(
                    |name| match kind {
                        Some("Class") => Some(find_my_tests::ActionKind::Class { class_name: name }),
                        Some("Typedef") => Some(find_my_tests::ActionKind::Typedef { name }),
                        Some(_) | None => None,
                    },
                    |class_name, member_name| {
                        let m = find_my_tests::Member { class_name, member_name };
                        match kind {
                            Some("Method") | None => Some(find_my_tests::ActionKind::Method(m)),
                            Some("Typeconst") => Some(find_my_tests::ActionKind::Typeconst(m)),
                            Some("Class_const") => Some(find_my_tests::ActionKind::ClassConst(m)),
                            Some(_) => None,
                        }
                    },
                    &name,
                )?;
                Ok(find_my_tests::Action { kind: action_kind, soft })
            };
            let json_content = match crate::sys_utils::cat(path) {
                Ok(c) => String::from_utf8_lossy(&c).into_owned(),
                Err(e) => return Err(sys_error(format!("Sys_error({:?})", e.0))),
            };
            // `Exn.to_string exn`: the sexp of `Printexc.to_string`.
            let input = match crate::yojson::safe::from_string(&json_content) {
                Err(e) => Err(format!("Yojson.Json_error({:?})", e.0)),
                Ok(json) => find_my_tests_json_input_of_yojson(&json)
                    .ok_or_else(|| "Ppx_yojson_conv_lib__Yojson_conv.Of_yojson_error(_, _)".to_string()),
            };
            let input = match input {
                Ok(i) => i,
                Err(e) => {
                    eprint!("Failed to parse JSON: ({:?})\n", e);
                    return Err(Exn::ExitWith(exit_status::T::InputError));
                }
            };
            let actions = input.roots.iter().map(parse_symbol).collect::<Result<Vec<_>, _>>()?;
            let (result, telemetry): (find_my_tests::Result, _) = rpc(
                args,
                server_command_types::T::FindMyTests((input.version, input.config, actions)),
            )?;
            match result {
                Ok(fmt_result) => {
                    // `print_find_my_tests_result`
                    if args.output_json {
                        // (`yojson_of_result_data` is not ported: the OSS server's
                        // `Find_my_tests_v2.go` and `_staging.go` always answer
                        // `Error`.)
                        unreachable!("FIND_MY_TESTS answered Ok: the OSS server never does")
                    } else {
                        for file in &fmt_result.selected_test_files {
                            println!("{}", file.file_path)
                        }
                    }
                    Ok((exit_status::T::NoError, telemetry))
                }
                Err(error) => {
                    eprint!("{}\n", error);
                    Ok((exit_status::T::InputError, telemetry))
                }
            }
        }
        ClientMode::ModePackageLint(file) => {
            use crate::yojson::safe::T as J;
            let file = expand_file_path(file)?;
            let (results, telemetry): (crate::relative_path::set::T, _) =
                rpc(args, server_command_types::T::PackageLint(file))?;
            let j = J::List(results.iter().map(|p| J::String(crate::relative_path::to_absolute(p))).collect());
            println!("{}", crate::yojson::safe::to_string(&j));
            Ok((exit_status::T::NoError, telemetry))
        }
        ClientMode::ModePackageLintFull((file, candidates)) => {
            use crate::yojson::safe::T as J;
            let file = expand_file_path(file)?;
            let candidates = candidates.iter().map(|c| expand_file_path(c)).collect::<Result<Vec<_>, _>>()?;
            let (results, telemetry): (crate::relative_path::set::T, _) = rpc(
                args,
                server_command_types::T::PackageLintFull((file, candidates)),
            )?;
            let j = J::List(results.iter().map(|p| J::String(crate::relative_path::to_absolute(p))).collect());
            println!("{}", crate::yojson::safe::to_string(&j));
            Ok((exit_status::T::NoError, telemetry))
        }
    }
}

/// The mode name `main` gives `Hack_event_logger.client_set_mode`.
fn telemetry_mode_name(mode: &ClientMode) -> &'static str {
    match mode {
        ClientMode::ModeStatusFiles(_) => {
            // Telemetry names are stable across internal renames.
            "MODE_STATUS_SINGLE"
        }
        mode => client_env::variants_of_client_mode::to_name(mode),
    }
}

/// `Stdlib.Filename.temp_file prefix suffix`: a new empty file in
/// `Filename.get_temp_dir_name ()` (`$TMPDIR`, or `/tmp`), closed. Raises
/// `Sys_error` when none can be made.
fn filename_temp_file(prefix: &str, suffix: &str) -> Result<String, Exn> {
    let temp_dir = std::env::var("TMPDIR").unwrap_or_else(|_| crate::sys_utils::TEMP_DIR_NAME.to_string());
    match crate::rt::ocaml_filename::open_temp_file(&temp_dir, prefix, suffix) {
        Ok((name, _file)) => Ok(name),
        Err(e) => Err(sys_error(format!(
            "Sys_error({:?})",
            crate::sys_utils::SysError::of_io_error(&temp_dir, &e).0
        ))),
    }
}

/// `In_channel.with_file path ~f:(fun ic -> In_channel.iter_lines ic
/// ~f:print_endline)`: each line, without its `\n` (or `\r\n`), then a
/// newline.
fn print_lines_of_file(path: &str) -> Result<(), Exn> {
    use std::io::BufRead;
    use std::io::Write;
    let file = std::fs::File::open(path).map_err(|e| {
        sys_error(format!("Sys_error({:?})", crate::sys_utils::SysError::of_io_error(path, &e).0))
    })?;
    let mut reader = std::io::BufReader::new(file);
    let stdout = std::io::stdout();
    let mut stdout = stdout.lock();
    let mut line = vec![];
    loop {
        line.clear();
        match reader.read_until(b'\n', &mut line) {
            Ok(0) => break,
            Ok(_) => {
                if line.last() == Some(&b'\n') {
                    line.pop();
                    if line.last() == Some(&b'\r') {
                        line.pop();
                    }
                }
                let _ = stdout.write_all(&line);
                let _ = stdout.write_all(b"\n");
            }
            Err(e) => return Err(sys_error(format!("Sys_error({:?})", e.to_string()))),
        }
    }
    let _ = stdout.flush();
    Ok(())
}

/// `String.split_lines`: the lines of `s`, split at `\n` or `\r\n`, without a
/// last empty line.
fn split_lines(s: &str) -> Vec<&str> {
    if s.is_empty() {
        return vec![];
    }
    let s = s.strip_suffix('\n').unwrap_or(s);
    s.split('\n').map(|l| l.strip_suffix('\r').unwrap_or(l)).collect()
}

/// `String.strip`: without the whitespace (` `, `\t`, `\n`, `\x0b`, `\x0c`,
/// `\r`) at both ends.
fn base_strip(s: &str) -> &str {
    s.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r'))
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
    exit::exit(None, None, None, None, exit_status)
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
    // `Hack_event_logger.client_set_mode mode_name` and
    // `Hack_event_logger.client_check_start ~reason:args.reason`: no-ops in the
    // OSS build.
    let _mode_name = telemetry_mode_name(&args.mode);
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
            exit::exit(None, None, None, None, exit_status)
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
