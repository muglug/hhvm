// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/linting_service.ml`, the open-source stub: no linters.

use crate::linting_main::UntypedLinter;
use crate::tast_visitor;

pub fn untyped_linters() -> Vec<UntypedLinter> {
    vec![]
}

pub fn typed_linters<'a>() -> Vec<Box<dyn tast_visitor::Handler<'a> + 'a>> {
    vec![]
}
