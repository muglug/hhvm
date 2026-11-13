// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/extract_classish/extract_classish.ml`
//! (helpers: as for `extract_method`).
//!
//! Owned by **F8** (plan §7.3). Created empty by W0b.

// ---- stand-in written by F7 (F8: replace with the port) ----
// `Code_actions_refactors.find` calls this `find`, which returns no
// refactor until F8 ports `extract_classish.ml`.
pub fn find<'a>(
    _entry: &'a std::sync::Arc<crate::provider_context::Entry>,
    _pos: &crate::pos::Pos,
    _ctx: &'a crate::provider_context::T,
) -> Vec<super::code_action_types::Refactor<'a>> {
    vec![]
}
