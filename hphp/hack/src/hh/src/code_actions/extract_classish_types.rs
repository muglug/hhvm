// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/extract_classish/extract_classish_types.ml`.

use crate::tast;

pub(crate) struct Candidate {
    pub(crate) class_: tast::Class_,
    pub(crate) selected_methods: Vec<tast::Method_>,
}
