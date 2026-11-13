// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_rpc.ml`. See `hh/PORTING.md`.
//!
//! [`handle`] is OCaml's `match`, one arm per command, in the OCaml's order.
//! Ported (by STATUS, plan §3.1): `STATUS`, `CHECK_LIVENESS`, `STATS`,
//! `NO_PRECHECKED_FILES`, `LIST_FILES_WITH_ERRORS`, and the two that need
//! nothing else (`IN_MEMORY_DEP_TABLE_SIZE`, `VERBOSE`). Every other arm is
//! the temporary stand-in of plan §3.4: it logs, then panics with
//! `Server_rpc.handle: <CMD> is not ported`, which the server loop (SRV)
//! catches by dropping the connection (a Rust `hh_client` never sends these:
//! it refuses their modes before connecting). The phase-2 owners (E1, E2,
//! E3) replace an arm each with its OCaml body, without restructuring.
//!
//! - `Diagnostics.sort_and_finalize` is a private helper here
//!   ([`sort_and_finalize`]), so that `diagnostics_state.rs` stays MEMO's.
//! - `log_check_response` calls `Hack_event_logger.check_response`, a no-op
//!   in the OSS build: it is kept, empty, where the OCaml calls it.
//! - `Server_prechecked_files.expand_all` is SS3's: with
//!   `Prechecked_files_disabled`, the only status there is until saved
//!   states are ported, it is the identity ([`expand_all`]).

use crate::diagnostics_state;
use crate::filter_diagnostics;
use crate::hh_logger;
use crate::server_command_types;
use crate::server_command_types::CmdMetadata;
use crate::server_command_types::CommandResult;
use crate::server_command_types::StatusLiveness;
use crate::server_command_types::T;
use crate::server_command_types::server_status;
use crate::server_env;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_progress::FinalizedDiagnostic;
use crate::stats;
use crate::telemetry;
use crate::user_diagnostic;

/// [take_max_errors n errors] truncate [errors] so its length is
/// at most [n].
///
/// Returns the truncated errors and the dropped error count.
fn take_max_errors(
    max_errors: Option<isize>,
    error_list: Vec<FinalizedDiagnostic>,
) -> (Vec<FinalizedDiagnostic>, isize) {
    match max_errors {
        Some(max_errors) => {
            // `List.split_n error_list max_errors` (a count of 0 or less
            // keeps nothing).
            let mut error_list = error_list;
            let n = std::cmp::max(0, max_errors) as usize;
            let dropped_errors = if n < error_list.len() {
                error_list.split_off(n)
            } else {
                vec![]
            };
            (error_list, dropped_errors.len() as isize)
        }
        None => (error_list, 0),
    }
}

/// `Diagnostics.sort_and_finalize`
fn sort_and_finalize(errors: diagnostics_state::T) -> Vec<FinalizedDiagnostic> {
    diagnostics_state::get_sorted_diagnostic_list(None, errors)
        .iter()
        .map(user_diagnostic::to_absolute)
        .collect()
}

/// `log_check_response env`: `Hack_event_logger.check_response` of the codes
/// of the diagnostics, a no-op in the OSS build.
fn log_check_response(_env: &Env) {}

/// `Server_prechecked_files.expand_all env`
fn expand_all(env: Env) -> Env {
    match env.prechecked_files {
        server_env::PrecheckedFilesStatus::PrecheckedFilesDisabled => env,
    }
}

/// `single_ctx env path file_input`
fn single_ctx(
    env: &Env,
    path: crate::relative_path::T,
    file_input: &server_command_types::FileInput,
) -> (crate::provider_context::T, std::sync::Arc<crate::provider_context::Entry>) {
    let contents: bstr::BString = match file_input {
        server_command_types::FileInput::FileName(path) => match crate::sys_utils::cat(path) {
            Ok(contents) => contents.into(),
            Err(e) => panic!("{:?}", e),
        },
        server_command_types::FileInput::FileContent(contents) => contents.as_bytes().into(),
    };
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    crate::provider_context::add_or_overwrite_entry_contents(&ctx, path, contents)
}

/// The path of a `file_input`: `Relative_path.create_detect_prefix fn`, or
/// of `""` for contents.
fn path_of_file_input(file_input: &server_command_types::FileInput) -> crate::relative_path::T {
    match file_input {
        server_command_types::FileInput::FileName(fn_) => crate::relative_path::create_detect_prefix(fn_),
        server_command_types::FileInput::FileContent(_) => crate::relative_path::create_detect_prefix(""),
    }
}

/// The stand-in for a command that is not ported yet (plan §3.4).
fn not_ported(cmd: &T) -> ! {
    let name = crate::server_command_types_utils::debug_describe_t(cmd);
    hh_logger::log(&format!("Server_rpc.handle: {} is not ported", name));
    panic!("Server_rpc.handle: {} is not ported", name)
}

/// `handle genv env ~is_stale metadata cmd`
pub fn handle(
    genv: &Genv,
    env: Env,
    is_stale: bool,
    metadata: &CmdMetadata,
    cmd: server_command_types::T,
) -> (Env, CommandResult) {
    let _ = metadata;
    match cmd {
        T::STATUS {
            max_errors,
            error_filter,
        } => {
            log_check_response(&env);
            let (error_list, dropped_count) = take_max_errors(
                max_errors,
                filter_diagnostics::filter(&error_filter, sort_and_finalize(env.diagnostics.clone())),
            );
            let liveness = if is_stale {
                StatusLiveness::StaleStatus
            } else {
                StatusLiveness::LiveStatus
            };
            let last_recheck_stats = match &env.last_recheck_loop_stats_for_actual_work {
                None => None,
                Some(recheck_stats) => Some(telemetry::string_(
                    None,
                    "init_id",
                    &env.init_env.init_id,
                    server_env::recheck_loop_stats::to_user_telemetry(recheck_stats),
                )),
            };
            let file_watcher_clock = env.clock.clone();
            (
                env,
                CommandResult::STATUS(server_status::T {
                    liveness,
                    error_list,
                    dropped_count,
                    last_recheck_stats,
                    file_watcher_clock,
                }),
            )
        }
        T::STATUSSINGLE {
            file_names,
            max_errors,
            error_filter,
            preexisting_warnings,
            return_expanded_tast,
        } => {
            // (`env.init_env.mergebase_warning_hashes`: the port's init env
            // has none.)
            let error_filter = crate::tast_provider::ErrorFilter {
                error_filter,
                warnings_saved_state: None,
            };
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (errors, tasts) = {
                let use_cached_diagnostics = genv.local_config.status_single_use_cached_diagnostics;
                let uses_partial_typecheck =
                    genv.local_config.enable_type_check_filter_files || genv.local_config.workload_quantile.is_some();
                let cached_result = if use_cached_diagnostics {
                    crate::server_status_single::go_from_cached_diagnostics(
                        &env,
                        &file_names,
                        return_expanded_tast,
                        preexisting_warnings,
                        is_stale,
                        uses_partial_typecheck,
                        &error_filter,
                    )
                } else {
                    None
                };
                match cached_result {
                    Some(result) => result,
                    None => crate::server_status_single::go(&file_names, &ctx, return_expanded_tast, &error_filter),
                }
            };
            let errors = take_max_errors(max_errors, sort_and_finalize(errors));
            let tasts = if return_expanded_tast {
                Some(
                    tasts
                        .into_iter()
                        .map(|(path, tast)| {
                            (
                                path,
                                crate::tast_with_dynamic::map(
                                    |tast: crate::tast::Program| {
                                        oxidized::aast::Program(crate::tast_expand::expand_program(&ctx, tast.0))
                                    },
                                    tast,
                                ),
                            )
                        })
                        .collect(),
                )
            } else {
                None
            };
            (env, CommandResult::STATUSSINGLE((errors, tasts)))
        }
        T::LOGERRORS {
            files,
            log_file,
            error_filter,
            preexisting_warnings,
        } => {
            let telemetry = crate::server_log_errors::go(&env, &files, error_filter, preexisting_warnings);
            match log_file {
                Some(path) => {
                    use std::io::Write;
                    match std::fs::OpenOptions::new().append(true).create(true).open(&path) {
                        Ok(mut oc) => {
                            let _ = oc.write_all(telemetry::to_string(None, &telemetry).as_bytes());
                            let _ = oc.write_all(b"\n");
                        }
                        Err(e) => panic!("Sys_error({:?})", format!("{}: {}", path, e)),
                    }
                }
                // (`Hack_event_logger.LogFileErrors.log`: a no-op in the OSS build.)
                None => {}
            }
            (env, CommandResult::LOGERRORS(()))
        }
        T::INFERTYPE(file_input, pos) => {
            let path = path_of_file_input(&file_input);
            let (ctx, entry) = single_ctx(&env, path, &file_input);
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_infer_type::go_ctx(&ctx, &entry, &pos)
            });
            (env, CommandResult::INFERTYPE(result))
        }
        T::INFERDYNAMIC(identifier, as_data) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let ctx = crate::provider_context::map_tcopt(&ctx, |mut tcopt| {
                tcopt.tco_dynamic_inference = true;
                tcopt
            });
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_infer_dynamic::go(&ctx, &identifier, as_data)
            });
            (env, CommandResult::INFERDYNAMIC(result))
        }
        T::ENFORCEMENTATPOSBATCH(positions) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let results = positions
                .iter()
                .map(|(fn_, pos)| {
                    let path = crate::relative_path::create_detect_prefix(fn_);
                    let (ctx, entry) = crate::provider_context::add_entry_if_missing(&ctx, path);
                    let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                        crate::server_enforcement_at_pos::go_ctx(&ctx, &entry, pos)
                    });
                    crate::server_enforcement_at_pos::result_to_json_string(&result, (fn_, pos))
                })
                .collect();
            (env, CommandResult::ENFORCEMENTATPOSBATCH(results))
        }
        T::INFERTYPEBATCH(positions) => {
            let result = crate::server_infer_type_batch::go(positions, &env);
            (env, CommandResult::INFERTYPEBATCH(result))
        }
        T::ISSUBTYPE(stdin) => {
            let result = crate::server_is_subtype::check(&stdin, &env);
            (env, CommandResult::ISSUBTYPE(result))
        }
        T::TASTHOLES(file_input, hole_filter) => {
            let path = path_of_file_input(&file_input);
            let (ctx, entry) = single_ctx(&env, path, &file_input);
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_collect_tast_holes::go_ctx(&ctx, &entry, hole_filter)
            });
            (env, CommandResult::TASTHOLES(result))
        }
        T::TASTHOLESBATCH(files) => {
            let result = crate::server_tast_holes_batch::go(files, &env);
            (env, CommandResult::TASTHOLESBATCH(result))
        }
        T::INFERTYPEERROR(file_input, line, column) => {
            let path = path_of_file_input(&file_input);
            let (ctx, entry) = single_ctx(&env, path, &file_input);
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_infer_type_error::go_ctx(&ctx, &entry, line, column)
            });
            (env, CommandResult::INFERTYPEERROR(result))
        }
        // TODO: edit this to look for classname
        T::IDENTIFYSYMBOL(arg) => {
            use crate::symbol_occurrence as so;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let get_def_opt = |type_: so::Kind, name: &str| -> Vec<_> {
                crate::server_symbol_definition::go(
                    &ctx,
                    None,
                    &so::T {
                        type_,
                        name: name.to_string(),
                        is_declaration: None,
                        pos: crate::pos::Pos::NONE,
                        affects_prod_build: true,
                    },
                )
                .into_iter()
                .map(|d| crate::symbol_definition::to_absolute(&d))
                .collect()
            };
            // The following are all the different named entities I could think of in Hack.
            let results = match crate::rt::ocaml_str::split_literal("::", &arg).as_slice() {
                [c_name, member] => {
                    let c_name = crate::utils::add_ns(c_name);
                    let member = member.to_string();
                    let class_name = || so::ReceiverClass::ClassName(c_name.clone());
                    [
                        get_def_opt(so::Kind::Method(class_name(), member.clone()), ""),
                        get_def_opt(so::Kind::Property(class_name(), member.clone()), ""),
                        get_def_opt(so::Kind::XhpLiteralAttr(c_name.clone(), member.clone()), ""),
                        get_def_opt(so::Kind::ClassConst(class_name(), member.clone()), ""),
                        get_def_opt(so::Kind::Typeconst(c_name.clone(), member.clone()), ""),
                    ]
                    .concat()
                }
                [name] => {
                    let name = crate::utils::add_ns(name);
                    [
                        get_def_opt(so::Kind::Class(so::ClassIdType::ClassId), &name),
                        // SO.Record and Class find the same things
                        get_def_opt(so::Kind::Function, &name),
                        get_def_opt(so::Kind::GConst, &name),
                    ]
                    .concat()
                }
                _ => vec![],
            };
            (env, CommandResult::IDENTIFYSYMBOL(results))
        }
        T::IDENTIFYFUNCTION(filename, file_input, pos) => {
            let (ctx, entry) = single_ctx(&env, crate::relative_path::create_detect_prefix(&filename), &file_input);
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_identify_function::go_quarantined_absolute(&ctx, &entry, &pos)
            });
            (env, CommandResult::IDENTIFYFUNCTION(result))
        }
        T::METHODJUMP((class_, filter, find_children)) => {
            print!("{}", class_);
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = match crate::method_jumps::get_inheritance(
                &ctx,
                &class_,
                filter,
                find_children,
                &env.naming_table,
                crate::server_find_refs::workers(genv),
            ) {
                Ok(result) => result,
                Err(e) => panic!("{:?}", e),
            };
            (env, CommandResult::METHODJUMP(result))
        }
        T::METHODJUMPBATCH((classes, filter)) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_method_jumps_batch::go(&ctx, classes, filter);
            (env, CommandResult::METHODJUMPBATCH(result))
        }
        T::FINDREFS(find_refs_action) => {
            use server_command_types::done_or_retry;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, result) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                let include_defs = false;
                done_or_retry::map_env(
                    |r| crate::server_find_refs::to_absolute(&r),
                    crate::server_find_refs::go(&ctx, &find_refs_action, include_defs, None, &[], genv, env),
                )
            });
            (env, CommandResult::FINDREFS(result))
        }
        T::GOTOIMPL(go_to_impl_action) => {
            use server_command_types::done_or_retry;
            let (env, result) = done_or_retry::map_env(
                |r| crate::server_find_refs::to_absolute(&r),
                crate::server_go_to_impl::go(&go_to_impl_action, genv, env),
            );
            (env, CommandResult::GOTOIMPL(result))
        }
        T::IDEFINDREFSBYSYMBOL(crate::find_refs_wire_format::cli_args::T {
            symbol_name: _,
            action,
            stream_file,
            hint_suffixes,
        }) => {
            use server_command_types::done_or_retry;
            let hints: Vec<crate::relative_path::T> = hint_suffixes
                .iter()
                .map(|suffix| crate::relative_path::from_root(suffix))
                .collect();
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, result) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                let include_defs = false;
                done_or_retry::map_env(
                    |r| crate::server_find_refs::to_absolute(&r),
                    crate::server_find_refs::go(&ctx, &action, include_defs, stream_file.as_ref(), &hints, genv, env),
                )
            });
            (env, CommandResult::IDEFINDREFSBYSYMBOL(result))
        }
        T::IDEGOTOIMPLBYSYMBOL(crate::find_refs_wire_format::cli_args::T {
            symbol_name: _, action, ..
        }) => {
            use server_command_types::done_or_retry;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, result) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                done_or_retry::map_env(
                    |r| crate::server_find_refs::to_absolute(&r),
                    crate::server_go_to_impl::go(&action, genv, env),
                )
            });
            (env, CommandResult::IDEGOTOIMPLBYSYMBOL(result))
        }
        T::RENAME(rename_action) => {
            use crate::server_rename_types::Action;
            use crate::symbol_occurrence as so;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, result) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                let definition_for_wrapper = match &rename_action {
                    Action::ClassRename(..) | Action::ClassConstRename(..) | Action::LocalVarRename { .. } => None,
                    Action::MethodRename {
                        class_name, old_name, ..
                    } => crate::server_symbol_definition::go(
                        &ctx,
                        None,
                        &so::T {
                            name: "unused for lookup".to_string(),
                            type_: so::Kind::Method(
                                so::ReceiverClass::ClassName(crate::utils::add_ns(class_name)),
                                old_name.clone(),
                            ),
                            is_declaration: None,
                            pos: crate::pos::Pos::NONE,
                            affects_prod_build: true,
                        },
                    ),
                    Action::FunctionRename { old_name, .. } => crate::server_symbol_definition::go(
                        &ctx,
                        None,
                        &so::T {
                            name: crate::utils::add_ns(old_name),
                            type_: so::Kind::Function,
                            is_declaration: None,
                            pos: crate::pos::Pos::NONE,
                            affects_prod_build: true,
                        },
                    ),
                };
                crate::server_rename::go(&ctx, &rename_action, genv, env, definition_for_wrapper.as_ref())
            });
            (env, CommandResult::RENAME(result))
        }
        T::IDERENAMEBYSYMBOL(action, new_name, symbol_definition) => {
            use server_command_types::done_or_retry;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, result) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                match crate::server_rename::go_ide_with_find_refs_action(
                    &ctx,
                    &action,
                    &new_name,
                    &symbol_definition,
                    genv,
                    env,
                ) {
                    // `| Error e -> (env, Done (Error e))`: the port of
                    // `go_ide_with_find_refs_action` takes the environment and
                    // never returns an error.
                    Err(e) => unreachable!("Server_rename.go_ide_with_find_refs_action: {}", e),
                    Ok(r) => done_or_retry::map_env(Ok, r),
                }
            });
            (env, CommandResult::IDERENAMEBYSYMBOL(result))
        }
        T::REMOVEDEADFIXMES(codes) => {
            log_check_response(&env);
            let patches = crate::server_rename::get_fixme_patches(&codes, &env);
            (
                env,
                CommandResult::REMOVEDEADFIXMES(server_command_types::PatchesOrError::Ok(patches)),
            )
        }
        T::REMOVEDEADUNSAFECASTS => {
            log_check_response(&env);
            let patches = crate::server_rename::get_dead_unsafe_cast_patches(&env);
            (
                env,
                CommandResult::REMOVEDEADUNSAFECASTS(server_command_types::PatchesOrError::Ok(patches)),
            )
        }
        // (`Server_rename.get_lambda_parameter_rewrite_patches` needs
        // `Server_rewrite_lambda_parameters`, which is not ported.)
        cmd @ T::REWRITELAMBDAPARAMETERS(_) => not_ported(&cmd),
        T::DUMPSYMBOLINFO(file_list) => {
            let result = crate::symbol_info_service::go(&file_list, &env);
            (env, CommandResult::DUMPSYMBOLINFO(result))
        }
        T::INMEMORYDEPTABLESIZE => {
            // TODO(hverr): Clean up 32-bit/migrate
            (env, CommandResult::INMEMORYDEPTABLESIZE(Ok(0)))
        }
        T::SAVENAMING(filename) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let naming_table = crate::save_state_service::naming_table_with_decl_hashes(&ctx, &env.naming_table);
            let result = crate::save_state_service::go_naming(&naming_table, &filename);
            (env, CommandResult::SAVENAMING(result))
        }
        T::CHECKLIVENESS => {
            // This is for the client to know "is the server available to process requests?"
            (env, CommandResult::CHECKLIVENESS(()))
        }
        T::PAUSE => {
            let mut env = env;
            env.full_check_status = server_env::FullCheckStatus::FullCheckPaused;
            (env, CommandResult::PAUSE(()))
        }
        T::LINT(fnl) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_lint::go(genv, &ctx, &fnl);
            (env, CommandResult::LINT(result))
        }
        T::LINTSTDIN(server_command_types::LintStdinInput { filename, contents }) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_lint::go_stdin(&ctx, &filename, &contents);
            (env, CommandResult::LINTSTDIN(result))
        }
        T::LINTALL(code) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_lint::lint_all(genv, &ctx, code);
            (env, CommandResult::LINTALL(result))
        }
        T::STATS => (env, CommandResult::STATS(stats::get_stats())),
        T::DUMPFULLFIDELITYPARSE(file) => {
            let result = crate::full_fidelity_parse_service::go(&file);
            (env, CommandResult::DUMPFULLFIDELITYPARSE(result))
        }
        T::RAGE => {
            let result = crate::server_rage::go(genv, &env);
            (env, CommandResult::RAGE(result))
        }
        T::CSTSEARCH(server_command_types::CstSearchInput {
            sort_results,
            input,
            files_to_search,
        }) => {
            // (`Multi_threaded_call.Coalesced_failures`: there is no worker.)
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                crate::cst_search_service::go(genv, &env, sort_results, files_to_search.as_deref(), &input)
            }));
            let result = match r {
                Ok(result) => result,
                Err(payload) => Err(crate::exception::to_string(&crate::exception::wrap(payload))),
            };
            (env, CommandResult::CSTSEARCH(result))
        }
        T::NOPRECHECKEDFILES => (expand_all(env), CommandResult::NOPRECHECKEDFILES(())),
        T::FUNDEPSBATCH(positions) => {
            let result = crate::server_fun_deps_batch::go(positions, &env);
            (env, CommandResult::FUNDEPSBATCH(result))
        }
        T::LISTFILESWITHERRORS => {
            let files = server_env::list_files_with_errors(&env);
            (env, CommandResult::LISTFILESWITHERRORS(files))
        }
        T::FILEDEPENDENTS(filenames) => {
            let files = crate::server_file_dependents::go(genv, &env, &filenames);
            (env, CommandResult::FILEDEPENDENTS(files))
        }
        cmd @ T::FINDISOLATABLECLUSTERS => not_ported(&cmd),
        T::VERBOSE(verbose) => {
            if verbose {
                hh_logger::level::set_min_level(hh_logger::level::T::Debug)
            } else {
                hh_logger::level::set_min_level(genv.local_config.min_log_level)
            }
            (env, CommandResult::VERBOSE(()))
        }
        T::DEPSOUTBATCH(positions) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_deps_out_batch::go(&ctx, &positions);
            (env, CommandResult::DEPSOUTBATCH(result))
        }
        T::DEPSINBATCH(positions) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, result) = crate::server_deps_in_batch::go(&ctx, genv, env, &positions);
            (env, CommandResult::DEPSINBATCH(result))
        }
        // `Find_my_tests_v2.go` and `Find_my_tests_staging.go`: the stubs of
        // the open-source build (`stubs/find_my_tests_*.ml`).
        T::FINDMYTESTS(..) => (
            env,
            CommandResult::FINDMYTESTS(Err(
                "FindMyTests is not available in open source builds".to_string()
            )),
        ),
        T::PACKAGELINT(file) => {
            let files = crate::server_package_lint::go_fast(genv, &env, &file);
            (env, CommandResult::PACKAGELINT(files))
        }
        T::PACKAGELINTFULL((file, candidates)) => {
            let files = crate::server_package_lint::go(genv, &env, &file, &candidates);
            (env, CommandResult::PACKAGELINTFULL(files))
        }
    }
}

#[cfg(test)]
mod tests;
