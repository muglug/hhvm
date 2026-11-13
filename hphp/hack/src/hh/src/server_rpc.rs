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
        cmd @ T::STATUSSINGLE { .. } => not_ported(&cmd),
        cmd @ T::LOGERRORS { .. } => not_ported(&cmd),
        cmd @ T::INFERTYPE(..) => not_ported(&cmd),
        cmd @ T::INFERDYNAMIC(..) => not_ported(&cmd),
        cmd @ T::ENFORCEMENTATPOSBATCH(_) => not_ported(&cmd),
        cmd @ T::INFERTYPEBATCH(_) => not_ported(&cmd),
        cmd @ T::ISSUBTYPE(_) => not_ported(&cmd),
        cmd @ T::TASTHOLES(..) => not_ported(&cmd),
        cmd @ T::TASTHOLESBATCH(_) => not_ported(&cmd),
        cmd @ T::INFERTYPEERROR(..) => not_ported(&cmd),
        cmd @ T::IDENTIFYSYMBOL(_) => not_ported(&cmd),
        cmd @ T::IDENTIFYFUNCTION(..) => not_ported(&cmd),
        cmd @ T::METHODJUMP(_) => not_ported(&cmd),
        cmd @ T::METHODJUMPBATCH(_) => not_ported(&cmd),
        cmd @ T::FINDREFS(_) => not_ported(&cmd),
        cmd @ T::GOTOIMPL(_) => not_ported(&cmd),
        cmd @ T::IDEFINDREFSBYSYMBOL(_) => not_ported(&cmd),
        cmd @ T::IDEGOTOIMPLBYSYMBOL(_) => not_ported(&cmd),
        cmd @ T::RENAME(_) => not_ported(&cmd),
        cmd @ T::IDERENAMEBYSYMBOL(..) => not_ported(&cmd),
        cmd @ T::REMOVEDEADFIXMES(_) => {
            log_check_response(&env);
            not_ported(&cmd)
        }
        cmd @ T::REMOVEDEADUNSAFECASTS => {
            log_check_response(&env);
            not_ported(&cmd)
        }
        cmd @ T::REWRITELAMBDAPARAMETERS(_) => not_ported(&cmd),
        cmd @ T::DUMPSYMBOLINFO(_) => not_ported(&cmd),
        T::INMEMORYDEPTABLESIZE => {
            // TODO(hverr): Clean up 32-bit/migrate
            (env, CommandResult::INMEMORYDEPTABLESIZE(Ok(0)))
        }
        cmd @ T::SAVENAMING(_) => not_ported(&cmd),
        T::CHECKLIVENESS => {
            // This is for the client to know "is the server available to process requests?"
            (env, CommandResult::CHECKLIVENESS(()))
        }
        T::PAUSE => {
            let mut env = env;
            env.full_check_status = server_env::FullCheckStatus::FullCheckPaused;
            (env, CommandResult::PAUSE(()))
        }
        cmd @ T::LINT(_) => not_ported(&cmd),
        cmd @ T::LINTSTDIN(_) => not_ported(&cmd),
        cmd @ T::LINTALL(_) => not_ported(&cmd),
        T::STATS => (env, CommandResult::STATS(stats::get_stats())),
        cmd @ T::DUMPFULLFIDELITYPARSE(_) => not_ported(&cmd),
        cmd @ T::RAGE => not_ported(&cmd),
        cmd @ T::CSTSEARCH(_) => not_ported(&cmd),
        T::NOPRECHECKEDFILES => (expand_all(env), CommandResult::NOPRECHECKEDFILES(())),
        cmd @ T::FUNDEPSBATCH(_) => not_ported(&cmd),
        T::LISTFILESWITHERRORS => {
            let files = server_env::list_files_with_errors(&env);
            (env, CommandResult::LISTFILESWITHERRORS(files))
        }
        cmd @ T::FILEDEPENDENTS(_) => not_ported(&cmd),
        cmd @ T::FINDISOLATABLECLUSTERS => not_ported(&cmd),
        T::VERBOSE(verbose) => {
            if verbose {
                hh_logger::level::set_min_level(hh_logger::level::T::Debug)
            } else {
                hh_logger::level::set_min_level(genv.local_config.min_log_level)
            }
            (env, CommandResult::VERBOSE(()))
        }
        cmd @ T::DEPSOUTBATCH(_) => not_ported(&cmd),
        cmd @ T::DEPSINBATCH(_) => not_ported(&cmd),
        cmd @ T::FINDMYTESTS(_) => not_ported(&cmd),
        cmd @ T::PACKAGELINT(_) => not_ported(&cmd),
        cmd @ T::PACKAGELINTFULL(_) => not_ported(&cmd),
    }
}

#[cfg(test)]
mod tests;
