// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_init_types.ml` (the types of plan §7.4; SS3
//! extends it later).
//!
//! Owned by **S1** (plan §8 item 5), then **SS3** (plan §7.3). Created
//! empty by W0b.
//!
//! (`load_state_error`: `Load_state_dirty_files_failure of Future.error`
//! needs `Future`, SS3 adds it with `loaded_info`.)

use crate::exception;
use crate::server_args;
use crate::telemetry;

// `init_result` is defined (by W0) in `server_init.rs`; S1 may move it here.
pub use crate::server_init::InitResult;

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

/// `load_state_verbose_error`
pub struct LoadStateVerboseError {
    pub message: String,
    pub auto_retry: bool,
    pub telemetry: telemetry::T,
}

/// `Saved_state_loader.LoadError` of the open-source build
/// (`stubs/saved_state_loader.ml`): every message is the same.
pub mod load_error {
    pub fn long_user_message_of_error(_: &str) -> String {
        "Saved states are not supported in this build.".to_string()
    }

    pub fn debug_details_of_error(_: &str) -> String {
        "".to_string()
    }

    pub fn category_of_error(_: &str) -> String {
        "".to_string()
    }

    pub fn saved_state_manifold_api_key_of_error(_: &str) -> Option<String> {
        None
    }
}

/// `load_state_error_to_verbose_string err`: returns
/// human-readable string, an indication of whether auto-retry is sensible,
/// and stack.
pub fn load_state_error_to_verbose_string(err: &LoadStateError) -> LoadStateVerboseError {
    match err {
        LoadStateError::LoadStateSavedStateLoaderFailure(err) => LoadStateVerboseError {
            message: format!(
                "Could not load saved-state from DevX infrastructure. The underlying error message was: {}\n\nThe accompanying debug details are: {}",
                load_error::long_user_message_of_error(err),
                load_error::debug_details_of_error(err)
            ),
            auto_retry: false,
            telemetry: {
                let t = telemetry::create();
                let t = telemetry::string_(None, "kind", "Load_state_saved_state_loader_failure", t);
                let t = telemetry::string_(None, "category", &load_error::category_of_error(err), t);
                let t = telemetry::string_(
                    None,
                    "debug_details",
                    &load_error::debug_details_of_error(err),
                    t,
                );
                telemetry::string_opt(
                    None,
                    "saved_state_manifold_api_key",
                    load_error::saved_state_manifold_api_key_of_error(err).as_deref(),
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

