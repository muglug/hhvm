// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/agent_session_id.ml`: the open-source build has no agent
//! session, so `initialize` does nothing and `get` is always `None`.

pub fn initialize() {}

pub fn get() -> Option<String> {
    None
}
