// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/extract_method_plugins.ml`: the open-source build has no
//! plugin.

use std::sync::Arc;

use super::code_action_types as cat;
use super::extract_method_types as t;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;

pub fn find<'a>(
    _ctx: &provider_context::T,
    _entry: &Arc<provider_context::Entry>,
    _path: &RelativePath,
    _pos: &Pos,
    _candidate: &t::Candidate,
) -> Vec<cat::Refactor<'a>> {
    vec![]
}
