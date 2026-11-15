// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/saved_state_loader.ml` (the open-source build has no saved
//! state loader), as far as the ported modules use it: `LoadError`.

/// `LoadError`: every message is the same.
pub mod load_error {
    /// `t`
    pub type T = String;

    /// Please do not throw an exception here; it breaks hack for open source
    /// users.
    pub fn short_user_message_of_error(_: &str) -> String {
        "Saved states are not supported in this build.".to_string()
    }

    pub fn medium_user_message_of_error(_: &str) -> String {
        "Saved states are not supported in this build.".to_string()
    }

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

    pub fn is_error_actionable(_: &str) -> bool {
        false
    }
}
