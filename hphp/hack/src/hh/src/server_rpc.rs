// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_rpc.ml`. See `hh/PORTING.md`.
//!
//! [`handle`] is OCaml's `match`, one arm per command, in the OCaml's order:
//! every command is ported. Deviations:
//!
//! - `STATUS_SINGLE` with `return_expanded_tast` (`hh_client --show-tast`):
//!   the TASTs do not cross the socket (`crate::rt::protocol`): the server
//!   sends what the client prints of them (`crate::typing_show::show_tasts`), whose TAST hash values are not
//!   reproduced (see there). The mergebase warning hashes
//!   (`init_env.mergebase_warning_hashes`) only come with saved states: here
//!   `None`.
//! - `log_check_response` calls `Hack_event_logger.check_response`, a no-op
//!   in the OSS build: it is kept, empty, where the OCaml calls it.

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
use crate::diagnostics::FinalizedDiagnostic;
use crate::stats;
use crate::telemetry;

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

/// `single_ctx env path file_input` (reading a missing file raises
/// `Sys_error`: a panic).
fn single_ctx(
    env: &Env,
    path: crate::relative_path::T,
    file_input: &server_command_types::FileInput,
) -> (crate::provider_context::T, std::sync::Arc<crate::provider_context::Entry>) {
    let contents: bstr::BString = match file_input {
        server_command_types::FileInput::FileName(path) => match crate::sys_utils::cat(path) {
            Ok(contents) => contents.into(),
            Err(e) => std::panic::panic_any(format!("Sys_error({:?})", e.0)),
        },
        server_command_types::FileInput::FileContent(contents) => contents.as_str().into(),
    };
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    crate::provider_context::add_or_overwrite_entry_contents(&ctx, path, contents)
}

/// The path of the file of `INFER_TYPE`, `TAST_HOLES` and
/// `INFER_TYPE_ERROR`.
fn path_of_file_input(file_input: &server_command_types::FileInput) -> crate::relative_path::T {
    match file_input {
        server_command_types::FileInput::FileName(fn_) => crate::relative_path::create_detect_prefix(fn_),
        server_command_types::FileInput::FileContent(_) => crate::relative_path::create_detect_prefix(""),
    }
}

/// `log_check_response env`: `Hack_event_logger.check_response` of the codes
/// of the diagnostics, a no-op in the OSS build.
fn log_check_response(_env: &Env) {}


/// `handle genv env ~is_stale metadata cmd`. Might raise
/// `Naming_table.File_info_not_found`.
pub fn handle(
    genv: &Genv,
    env: Env,
    is_stale: bool,
    metadata: &CmdMetadata,
    cmd: server_command_types::T,
) -> (Env, CommandResult) {
    let _ = metadata;
    match cmd {
        T::Status {
            max_errors,
            error_filter,
        } => {
            log_check_response(&env);
            let (error_list, dropped_count) = take_max_errors(
                max_errors,
                filter_diagnostics::filter(&error_filter, crate::diagnostics::sort_and_finalize(env.diagnostics.clone())),
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
                CommandResult::Status(server_status::T {
                    liveness,
                    error_list,
                    dropped_count,
                    last_recheck_stats,
                    file_watcher_clock,
                }),
            )
        }
        T::StatusSingle {
            file_names,
            max_errors,
            error_filter,
            preexisting_warnings,
            return_expanded_tast,
        } => {
            let error_filter = crate::tast_provider::ErrorFilter {
                error_filter,
                // `Server_env.(env.init_env.mergebase_warning_hashes) >>=
                // Option.some_if (not preexisting_warnings)`: there are no
                // mergebase warning hashes without saved states.
                warnings_saved_state: None,
            };
            let _ = preexisting_warnings;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (errors, tasts) = {
                let use_cached_diagnostics = genv.local_config.status_single_use_cached_diagnostics;
                let uses_partial_typecheck = genv.local_config.enable_type_check_filter_files
                    || genv.local_config.workload_quantile.is_some();
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
                    None => crate::server_status_single::go(
                        genv.num_workers,
                        &file_names,
                        &ctx,
                        return_expanded_tast,
                        &error_filter,
                    ),
                }
            };
            let errors = take_max_errors(max_errors, crate::diagnostics::sort_and_finalize(errors));
            // Unforced lazy values are closures which make serialization over RPC fail.
            // (Here the TASTs do not cross the socket: what the client prints
            // of them does, `typing_show::show_tasts`.)
            let tasts = if return_expanded_tast {
                let expanded: server_command_types::Tasts = tasts
                    .into_iter()
                    .map(|(path, t)| {
                        let t = crate::tast_with_dynamic::map(
                            |tast: crate::tast::Program| {
                                // `Tast_expand.expand_program (Lazy.force ctx)
                                // |> Tast.force_lazy_values` (nothing is lazy here)
                                crate::tast::Program::from(crate::tast_expand::expand_program(&ctx, tast.into()))
                            },
                            t,
                        );
                        (path, t)
                    })
                    .collect();
                let (hashes, tasts) = crate::typing_show::show_tasts(&expanded);
                Some(server_command_types::ShownTasts { hashes, tasts })
            } else {
                None
            };
            (env, CommandResult::StatusSingle((errors, tasts)))
        }
        T::LogErrors {
            files,
            log_file,
            error_filter,
            preexisting_warnings,
        } => {
            let telemetry =
                crate::server_log_errors::go(genv.num_workers, &env, &files, error_filter, preexisting_warnings);
            match log_file {
                Some(path) => {
                    use std::io::Write;
                    // `Out_channel.create ~binary:false ~append:true path`
                    let mut oc = match std::fs::OpenOptions::new().create(true).append(true).open(&path) {
                        Ok(oc) => oc,
                        Err(e) => std::panic::panic_any(format!("Sys_error({:?})", format!("{}: {}", path, e))),
                    };
                    let _ = oc.write_all(telemetry::to_string(None, &telemetry).as_bytes());
                    let _ = oc.write_all(b"\n");
                }
                // (`Hack_event_logger.LogFileErrors.log`: a no-op in the OSS build.)
                None => {}
            }
            (env, CommandResult::LogErrors(()))
        }
        T::InferType(file_input, pos) => {
            let path = path_of_file_input(&file_input);
            let (ctx, entry) = single_ctx(&env, path, &file_input);
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_infer_type::go_ctx(&ctx, &entry, &pos)
            });
            (env, CommandResult::InferType(result))
        }
        T::InferDynamic(identifier, as_data) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let ctx = crate::provider_context::map_tcopt(&ctx, |mut tcopt| {
                tcopt.tco_dynamic_inference = true;
                tcopt
            });
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_infer_dynamic::go(&ctx, &identifier, as_data)
            });
            (env, CommandResult::InferDynamic(result))
        }
        T::EnforcementAtPosBatch(positions) => {
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
            (env, CommandResult::EnforcementAtPosBatch(results))
        }
        T::InferTypeBatch(positions) => {
            let result = crate::server_infer_type_batch::go(genv.num_workers, positions, &env);
            (env, CommandResult::InferTypeBatch(result))
        }
        T::IsSubtype(stdin) => {
            let result = crate::server_is_subtype::check(genv.num_workers, &stdin, &env);
            (env, CommandResult::IsSubtype(result))
        }
        T::TastHoles(file_input, hole_filter) => {
            let path = path_of_file_input(&file_input);
            let (ctx, entry) = single_ctx(&env, path, &file_input);
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_collect_tast_holes::go_ctx(&ctx, &entry, hole_filter)
            });
            (env, CommandResult::TastHoles(result))
        }
        T::TastHolesBatch(files) => {
            let result = crate::server_tast_holes_batch::go(Some(std::cmp::max(1, genv.num_workers) as usize), &files, &env);
            (env, CommandResult::TastHolesBatch(result))
        }
        T::InferTypeError(file_input, line, column) => {
            let path = path_of_file_input(&file_input);
            let (ctx, entry) = single_ctx(&env, path, &file_input);
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_infer_type_error::go_ctx(&ctx, &entry, line, column)
            });
            (env, CommandResult::InferTypeError(result))
        }
        // TODO: edit this to look for classname
        T::IdentifySymbol(arg) => {
            use crate::symbol_occurrence as so;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let get_def_opt = |type_: so::Kind, name: &str| -> Vec<crate::symbol_definition::T<crate::pos::Absolute>> {
                crate::server_symbol_definition::go(
                    &ctx,
                    None,
                    &so::T {
                        type_,
                        name: name.to_string(),
                        is_declaration: None,
                        pos: oxidized::pos::Pos::NONE,
                        affects_prod_build: true,
                    },
                )
                .into_iter()
                .map(|d| crate::symbol_definition::to_absolute(&d))
                .collect()
            };
            let arg = crate::rt::ocaml_str::split("::", &arg);
            // The following are all the different named entities I could think of in Hack.
            let results = match &arg[..] {
                [c_name, member] => {
                    let c_name = crate::utils::add_ns(c_name);
                    let mut l = get_def_opt(
                        so::Kind::Method(so::ReceiverClass::ClassName(c_name.clone()), member.clone()),
                        "",
                    );
                    l.extend(get_def_opt(
                        so::Kind::Property(so::ReceiverClass::ClassName(c_name.clone()), member.clone()),
                        "",
                    ));
                    l.extend(get_def_opt(so::Kind::XhpLiteralAttr(c_name.clone(), member.clone()), ""));
                    l.extend(get_def_opt(
                        so::Kind::ClassConst(so::ReceiverClass::ClassName(c_name.clone()), member.clone()),
                        "",
                    ));
                    l.extend(get_def_opt(so::Kind::Typeconst(c_name, member.clone()), ""));
                    l
                }
                [name] => {
                    let name = crate::utils::add_ns(name);
                    let mut l = get_def_opt(so::Kind::Class(so::ClassIdType::ClassId), &name);
                    // SO.Record and Class find the same things
                    l.extend(get_def_opt(so::Kind::Function, &name));
                    l.extend(get_def_opt(so::Kind::GConst, &name));
                    l
                }
                _ => vec![],
            };
            (env, CommandResult::IdentifySymbol(results))
        }
        T::IdentifyFunction(filename, file_input, pos) => {
            let (ctx, entry) = single_ctx(
                &env,
                crate::relative_path::create_detect_prefix(&filename),
                &file_input,
            );
            let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                crate::server_identify_function::go_quarantined_absolute(&ctx, &entry, &pos)
            });
            (env, CommandResult::IdentifyFunction(result))
        }
        T::MethodJump((class_, filter, find_children)) => {
            // (The OCaml prints the class to the server's stdout.)
            print!("{}", class_);
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = match crate::method_jumps::get_inheritance(
                &ctx,
                &class_,
                filter,
                find_children,
                &env.naming_table,
                Some(std::cmp::max(1, genv.num_workers) as usize),
            ) {
                Ok(r) => r,
                // `Naming_table.File_info_not_found`, uncaught
                Err(e) => panic!("{}", e),
            };
            (env, CommandResult::MethodJump(result))
        }
        T::MethodJumpBatch((classes, filter)) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_method_jumps_batch::go(&ctx, genv.num_workers, &classes, filter);
            (env, CommandResult::MethodJumpBatch(result))
        }
        T::FindRefs(find_refs_action) => {
            use server_command_types::done_or_retry::map_env;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, r) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                let include_defs = false;
                map_env(
                    |r| crate::server_find_refs::to_absolute(&r),
                    crate::server_find_refs::go(&ctx, &find_refs_action, include_defs, None, &[], genv, env),
                )
            });
            (env, CommandResult::FindRefs(r))
        }
        T::GoToImpl(go_to_impl_action) => {
            use server_command_types::done_or_retry::map_env;
            let (env, r) = map_env(
                |r| crate::server_find_refs::to_absolute(&r),
                crate::server_go_to_impl::go(&go_to_impl_action, genv, env),
            );
            (env, CommandResult::GoToImpl(r))
        }
        T::IdeFindRefsBySymbol(crate::find_refs_wire_format::cli_args::T {
            symbol_name: _,
            action,
            stream_file,
            hint_suffixes,
        }) => {
            use server_command_types::done_or_retry::map_env;
            let hints: Vec<crate::relative_path::T> = hint_suffixes
                .iter()
                .map(|suffix| crate::relative_path::from_root(suffix))
                .collect();
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, r) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                let include_defs = false;
                map_env(
                    |r| crate::server_find_refs::to_absolute(&r),
                    crate::server_find_refs::go(
                        &ctx,
                        &action,
                        include_defs,
                        stream_file.as_ref(),
                        &hints,
                        genv,
                        env,
                    ),
                )
            });
            (env, CommandResult::IdeFindRefsBySymbol(r))
        }
        T::IdeGoToImplBySymbol(crate::find_refs_wire_format::cli_args::T { action, .. }) => {
            use server_command_types::done_or_retry::map_env;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, r) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                map_env(
                    |r| crate::server_find_refs::to_absolute(&r),
                    crate::server_go_to_impl::go(&action, genv, env),
                )
            });
            (env, CommandResult::IdeGoToImplBySymbol(r))
        }
        T::Rename(rename_action) => {
            use crate::server_rename_types::Action as RA;
            use crate::symbol_occurrence as so;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, r) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                let definition_for_wrapper = match &rename_action {
                    RA::ClassRename(..) | RA::ClassConstRename(..) | RA::LocalVarRename { .. } => None,
                    RA::MethodRename { class_name, old_name, .. } => crate::server_symbol_definition::go(
                        &ctx,
                        None,
                        &so::T {
                            name: "unused for lookup".to_string(),
                            type_: so::Kind::Method(
                                so::ReceiverClass::ClassName(crate::utils::add_ns(class_name)),
                                old_name.clone(),
                            ),
                            is_declaration: None,
                            pos: oxidized::pos::Pos::NONE,
                            affects_prod_build: true,
                        },
                    ),
                    RA::FunctionRename { old_name, .. } => crate::server_symbol_definition::go(
                        &ctx,
                        None,
                        &so::T {
                            name: crate::utils::add_ns(old_name),
                            type_: so::Kind::Function,
                            is_declaration: None,
                            pos: oxidized::pos::Pos::NONE,
                            affects_prod_build: true,
                        },
                    ),
                };
                crate::server_rename::go(&ctx, &rename_action, genv, env, definition_for_wrapper.as_ref())
            });
            (env, CommandResult::Rename(r))
        }
        T::IdeRenameBySymbol(action, new_name, symbol_definition) => {
            use server_command_types::done_or_retry;
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, r) = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                match crate::server_rename::go_ide_with_find_refs_action(
                    &ctx,
                    &action,
                    &new_name,
                    &symbol_definition,
                    genv,
                    env,
                ) {
                    // (`Error e -> (env, Done (Error e))`: the function never
                    // returns an `Error`, which would have consumed `env`.)
                    Err(e) => panic!("Server_rename.go_ide_with_find_refs_action: {}", e),
                    Ok(r) => done_or_retry::map_env(Ok, r),
                }
            });
            (env, CommandResult::IdeRenameBySymbol(r))
        }
        T::RemoveDeadFixmes(codes) => {
            log_check_response(&env);
            let patches = crate::server_rename::get_fixme_patches(&codes, &env);
            (env, CommandResult::RemoveDeadFixmes(server_command_types::PatchesOrError::Ok(patches)))
        }
        T::RemoveDeadUnsafeCasts => {
            log_check_response(&env);
            let patches = crate::server_rename::get_dead_unsafe_cast_patches(&env);
            (env, CommandResult::RemoveDeadUnsafeCasts(server_command_types::PatchesOrError::Ok(patches)))
        }
        T::RewriteLambdaParameters(files) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let patches = crate::server_rename::get_lambda_parameter_rewrite_patches(&ctx, &files);
            (env, CommandResult::RewriteLambdaParameters(patches))
        }
        T::DumpSymbolInfo(file_list) => {
            let result = crate::symbol_info_service::go(Some(std::cmp::max(1, genv.num_workers) as usize), &file_list, &env);
            (env, CommandResult::DumpSymbolInfo(result))
        }
        T::InMemoryDepTableSize => {
            // TODO(hverr): Clean up 32-bit/migrate
            (env, CommandResult::InMemoryDepTableSize(Ok(0)))
        }
        T::SaveNaming(filename) => {
            let result = crate::save_state_service::go_naming(&env.naming_table, &filename);
            (env, CommandResult::SaveNaming(result))
        }
        T::Pause => {
            let mut env = env;
            env.full_check_status = server_env::FullCheckStatus::FullCheckPaused;
            (env, CommandResult::Pause(()))
        }
        T::CheckLiveness => {
            // This is for the client to know "is the server available to process requests?"
            (env, CommandResult::CheckLiveness(()))
        }
        T::Lint(fnl) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_lint::go(genv, &ctx, &fnl);
            (env, CommandResult::Lint(result))
        }
        T::LintStdin(server_command_types::LintStdinInput { filename, contents }) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_lint::go_stdin(&ctx, &filename, &contents);
            (env, CommandResult::LintStdin(result))
        }
        T::LintAll(code) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_lint::lint_all(genv, &ctx, code);
            (env, CommandResult::LintAll(result))
        }
        T::Stats => {
            crate::mem_census::mem_census(&env);
            (env, CommandResult::Stats(stats::get_stats()))
        }
        T::DumpFullFidelityParse(file) => (
            env,
            CommandResult::DumpFullFidelityParse(crate::full_fidelity_parse_service::go(&file)),
        ),
        T::Rage => {
            // `Server_rage.go genv env`
            let data = format!(
                "hh_server pid={} ppid={}\ndisk_needs_parsing: {}\n",
                std::process::id(),
                std::os::unix::process::parent_id(),
                env.disk_needs_parsing
                    .iter()
                    .map(crate::relative_path::to_absolute)
                    .collect::<Vec<_>>()
                    .join(" ")
            );
            let result = vec![crate::server_rage_types::RageItem {
                title: "status".to_string(),
                data,
            }];
            (env, CommandResult::Rage(result))
        }
        T::CstSearch(server_command_types::CstSearchInput {
            sort_results,
            input,
            files_to_search,
        }) => {
            // (`Multi_threaded_call.Coalesced_failures`, a worker that died, has
            // no counterpart: the search runs on threads.)
            let result = crate::cst_search_service::server::go(
                genv,
                &env,
                sort_results,
                files_to_search.as_deref(),
                &input,
            );
            (env, CommandResult::CstSearch(result))
        }
        T::NoPrecheckedFiles => (
            crate::server_prechecked_files::expand_all(env),
            CommandResult::NoPrecheckedFiles(()),
        ),
        T::FunDepsBatch(positions) => {
            let result = crate::server_fun_deps_batch::go(Some(std::cmp::max(1, genv.num_workers) as usize), &positions, &env);
            (env, CommandResult::FunDepsBatch(result))
        }
        T::ListFilesWithErrors => {
            let files = server_env::list_files_with_errors(&env);
            (env, CommandResult::ListFilesWithErrors(files))
        }
        T::FileDependents(filenames) => {
            let files = crate::server_file_dependents::go(genv, &env, &filenames);
            (env, CommandResult::FileDependents(files))
        }
        T::FindIsolatableClusters(options) => {
            let result = crate::server_isolation::go(&options, genv, &env);
            (env, CommandResult::FindIsolatableClusters(result))
        }
        T::ValidateIsolation(filenames) => {
            let files: Vec<_> = filenames
                .iter()
                .map(|suffix| crate::relative_path::from_root(suffix))
                .collect();
            let result = crate::server_isolation_validate::go(genv, &env, &files);
            (env, CommandResult::ValidateIsolation(result))
        }
        T::Verbose(verbose) => {
            if verbose {
                hh_logger::level::set_min_level(hh_logger::level::T::Debug)
            } else {
                hh_logger::level::set_min_level(genv.local_config.min_log_level)
            }
            (env, CommandResult::Verbose(()))
        }
        T::DepsOutBatch(positions) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let result = crate::server_deps_out_batch::go(&ctx, &positions);
            (env, CommandResult::DepsOutBatch(result))
        }
        T::DepsInBatch(positions) => {
            let ctx = crate::provider_utils::ctx_from_server_env(&env);
            let (env, result) = crate::server_deps_in_batch::go(&ctx, genv, env, &positions);
            (env, CommandResult::DepsInBatch(result))
        }
        T::FindMyTests((version, _config, _actions)) => {
            // `Find_my_tests_v2.go` / `Find_my_tests_staging.go`: the OSS stubs.
            let result = match version {
                server_command_types::find_my_tests::Version::V2
                | server_command_types::find_my_tests::Version::Staging => {
                    Err("FindMyTests is not available in open source builds".to_string())
                }
            };
            (env, CommandResult::FindMyTests(result))
        }
        T::PackageLint(file) => {
            let (env, result) = crate::server_package_lint::go_fast(genv, env, &file);
            (env, CommandResult::PackageLint(result))
        }
        T::PackageLintFull((file, candidates)) => {
            let (env, result) = crate::server_package_lint::go(genv, env, &file, &candidates);
            (env, CommandResult::PackageLintFull(result))
        }
    }
}

#[cfg(test)]
mod tests;
