// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_init_types.ml`.
//!
//! (`load_state_error`: `Load_state_dirty_files_failure of Future.error` is
//! not a variant: there is no `Future` here.)

use crate::exception;
use crate::server_args;
use crate::server_env;
use crate::telemetry;

/// `load_state_error`
pub enum LoadStateError {
    /// an error reported when downloading saved-state through
    /// [Saved_state_loader] (`Saved_state_loader.LoadError.t` is `string`
    /// in the open-source build)
    LoadStateSavedStateLoaderFailure(String),
    /// any other unhandled exception from lazy_init
    LoadStateUnhandledException(exception::T),
}

/// `load_state_approach`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoadStateApproach {
    Precomputed(server_args::SavedStateTargetInfo),
    LoadStateNatively,
}

/// `init_approach`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InitApproach {
    FullInit,
    /// Only does parsing. Used in particular with --save-naming.
    ParseOnlyInit,
    SavedStateInit(LoadStateApproach),
    /// Write symbol info. Used by Glean.
    WriteSymbolInfo,
    /// Write symbol info. Initialize with a saved state. Used by Glean.
    WriteSymbolInfoWithState(LoadStateApproach),
}

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

/// `load_state_verbose_error`
pub struct LoadStateVerboseError {
    pub message: String,
    pub auto_retry: bool,
    pub telemetry: telemetry::T,
}

/// `load_state_error_to_verbose_string err`: returns
/// human-readable string, an indication of whether auto-retry is sensible,
/// and stack.
pub fn load_state_error_to_verbose_string(err: &LoadStateError) -> LoadStateVerboseError {
    match err {
        LoadStateError::LoadStateSavedStateLoaderFailure(err) => LoadStateVerboseError {
            message: format!(
                "Could not load saved-state from DevX infrastructure. The underlying error message was: {}\n\nThe accompanying debug details are: {}",
                crate::saved_state_loader::load_error::long_user_message_of_error(err),
                crate::saved_state_loader::load_error::debug_details_of_error(err)
            ),
            auto_retry: false,
            telemetry: {
                let t = telemetry::create();
                let t = telemetry::string_(None, "kind", "Load_state_saved_state_loader_failure", t);
                let t = telemetry::string_(None, "category", &crate::saved_state_loader::load_error::category_of_error(err), t);
                let t = telemetry::string_(
                    None,
                    "debug_details",
                    &crate::saved_state_loader::load_error::debug_details_of_error(err),
                    t,
                );
                telemetry::string_opt(
                    None,
                    "saved_state_manifold_api_key",
                    crate::saved_state_loader::load_error::saved_state_manifold_api_key_of_error(err).as_deref(),
                    t,
                )
            },
        },
        LoadStateError::LoadStateUnhandledException(e) => LoadStateVerboseError {
            message: format!(
                "Unexpected bug loading saved state - {}",
                exception::get_ctor_string(e)
            ),
            auto_retry: false,
            telemetry: {
                let t = telemetry::create();
                let t = telemetry::string_(None, "kind", "Load_state_unhandled_exception", t);
                // `Telemetry.exception_ ~e`
                telemetry::json(
                    "error",
                    crate::yojson::safe::T::Assoc(vec![
                        (
                            "stack".to_string(),
                            crate::yojson::safe::T::String(exception::get_backtrace_string(e)),
                        ),
                        (
                            "message".to_string(),
                            crate::yojson::safe::T::String(exception::get_ctor_string(e)),
                        ),
                    ]),
                    t,
                )
            },
        },
    }
}


/// `files_changed_while_parsing`
pub type FilesChangedWhileParsing = crate::relative_path::set::T;

/// `loaded_info`
pub struct LoadedInfo {
    pub naming_table_fn: String,
    pub deptable_fn: String,
    pub naming_table_fallback_fn: Option<String>,
    /// All files changed since the saved state revision according to either
    /// Saved_state_lookup if we load using Saved_state_loader, or
    /// if we initialized with a pre-loaded saved state, the list of files passed to hh_server.
    /// This should be the disjoint union of `dirty_master_files` and `dirty_local_files`,
    /// which are determined using hg and this set.
    pub changed_files_since_saved_state_rev: crate::relative_path::set::T,
    /// Files changed between saved state revision and current public merge base
    pub dirty_master_files: crate::relative_path::set::T,
    /// Files changed since the public merge base
    pub dirty_local_files: crate::relative_path::set::T,
    pub old_naming_table: crate::naming_table::T,
    pub old_errors: crate::save_state_service_types::SavedStateErrors,
    pub old_warnings: oxidized::warnings_saved_state_impl::WarningsSavedState,
    pub saved_state_revs_info: crate::server_env::SavedStateRevsInfo,
    /// The manifold path for naming table saved state, to be used by remote type checker
    /// for downloading the naming table in the case of a saved-state init
    pub naming_table_manifold_path: Option<String>,
}
