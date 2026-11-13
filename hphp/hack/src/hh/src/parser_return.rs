// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `parser/parser_return.ml`. See `hh/PORTING.md`.

use bstr::BString;
use oxidized::file_info;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::prim_defs;

pub type Comments = Vec<(Pos, prim_defs::Comment)>;

#[derive(Clone, Debug)]
pub struct T {
    pub file_mode: Option<file_info::Mode>,
    pub comments: Comments,
    pub ast: nast::Program,
    pub content: BString,
}
