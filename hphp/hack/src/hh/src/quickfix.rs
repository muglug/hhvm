// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Quickfix` (`diagnostics/quickfix.ml`). See `hh/PORTING.md`.
//!
//! The types are those of `oxidized::quickfix`, re-exported here. `oxidized`
//! has none of the functions of `quickfix.ml`: this module has the ones the
//! port has needed so far (the constructors).

use oxidized::classish_positions_types;
pub use oxidized::quickfix::*;

pub fn make<P>(
    title: String,
    edits: Edits<P>,
    hint_styles: Vec<HintStyle<classish_positions_types::Pos<P>>>,
) -> Quickfix<P> {
    Quickfix {
        title,
        edits,
        hint_styles,
    }
}

pub fn make_eager<P>(
    title: String,
    new_text: String,
    hint_styles: Vec<HintStyle<classish_positions_types::Pos<P>>>,
    pos: P,
) -> Quickfix<P> {
    Quickfix {
        title,
        edits: Edits::Eager(vec![(new_text, pos)]),
        hint_styles,
    }
}

pub fn make_eager_default_hint_style<P>(title: String, new_text: String, pos: P) -> Quickfix<P> {
    make_eager(title, new_text, vec![], pos)
}
