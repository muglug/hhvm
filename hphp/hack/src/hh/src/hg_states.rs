// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/hg/hg_states.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

pub const update: &str = "hg.update";

pub const transaction: &str = "hg.transaction";

pub fn is_hg_state(state: &str) -> bool {
    state == update || state == transaction
}
