// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/informant_notifier.ml`: only the type `repo_transition`
//! that `Informant.Revision_tracker` decides on. The notifier itself (`t`,
//! `init`, `get_change`, `has_more_messages`, and the exception
//! `Informant_edenfs_watcher_failed` of its Eden backend) is only used by the
//! `Active` informant, which is not ported.

use crate::hg;

/// `repo_transition`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RepoTransition {
    /// Watchman only: We have entered hg.update.
    StateEnter(hg::rev::T),
    /// Watchman only: We have left hg.update.
    StateLeave(hg::rev::T),
    /// Watchman only: We moved to a different mergebase.
    ChangedMergeBase(hg::rev::T),
    /// Eden only: We moved to a different commit. As a result, the mergebase may
    /// or may not have changed.
    ChangedCommit(hg::rev::T),
}

/// `show_repo_transition` (`[@@deriving show]`)
pub fn show_repo_transition(t: &RepoTransition) -> String {
    let (name, rev) = match t {
        RepoTransition::StateEnter(rev) => ("State_enter", rev),
        RepoTransition::StateLeave(rev) => ("State_leave", rev),
        RepoTransition::ChangedMergeBase(rev) => ("Changed_merge_base", rev),
        RepoTransition::ChangedCommit(rev) => ("Changed_commit", rev),
    };
    format!("(Informant_notifier.{} {:?})", name, rev)
}
