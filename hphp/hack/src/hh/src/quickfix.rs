// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `diagnostics/quickfix.ml`. See `hh/PORTING.md`.
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

/// Helper for the Quickfix.Eager constructor
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

/// Helper for [`make_eager`] to create a quickfix with no additional hint
/// styles
pub fn make_eager_default_hint_style<P>(title: String, new_text: String, pos: P) -> Quickfix<P> {
    make_eager(title, new_text, vec![], pos)
}

/// `Quickfix.map_positions`
pub fn map_positions<A, B>(q: &Quickfix<A>, f: impl Fn(&A) -> B) -> Quickfix<B> {
    let Quickfix {
        title,
        edits,
        hint_styles,
    } = q;
    let transform_edits = |edits: &Edits<A>| match edits {
        Edits::Eager(edits) => {
            let edits = edits.iter().map(|(s, p)| (s.clone(), f(p))).collect();
            Edits::Eager(edits)
        }
        Edits::ClassishEnd { new_text, name } => Edits::ClassishEnd {
            new_text: new_text.clone(),
            name: name.clone(),
        },
        Edits::AddFunctionAttribute {
            function_pos,
            attribute_name,
        } => Edits::AddFunctionAttribute {
            function_pos: f(function_pos),
            attribute_name: attribute_name.clone(),
        },
    };
    let edits = transform_edits(edits);
    let transform_hint_style =
        |hint_style: &HintStyle<classish_positions_types::Pos<A>>| match hint_style {
            HintStyle::HintStyleSilent(p) => {
                HintStyle::HintStyleSilent(crate::classish_positions::map_pos(&f, p))
            }
            HintStyle::HintStyleHint(p) => {
                HintStyle::HintStyleHint(crate::classish_positions::map_pos(&f, p))
            }
        };
    let hint_styles = hint_styles.iter().map(transform_hint_style).collect();
    Quickfix {
        title: title.clone(),
        edits,
        hint_styles,
    }
}

/// `Quickfix.to_absolute`
pub fn to_absolute(q: &Quickfix<oxidized::pos::Pos>) -> Quickfix<crate::pos::Absolute> {
    map_positions(q, crate::pos::to_absolute)
}
