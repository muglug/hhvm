// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/hg/hg_states.ml`. See `hh/PORTING.md`.

/// Mercurial state names shared by Eden and Watchman notifications.
/// Asserted by hg while working.
pub const UPDATE: &str = "hg.update";

pub const TRANSACTION: &str = "hg.transaction";

pub fn is_hg_state(state: &str) -> bool {
    state == UPDATE || state == TRANSACTION
}
