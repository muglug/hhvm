// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<a613a9bd2971444e71977ebcbb5e6adf>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

pub use crate::error_codes::Parsing as Error_code;
#[allow(unused_imports)]
use crate::*;

#[derive(
    Clone,
    Debug,
    Deserialize,
    Eq,
    EqModuloPos,
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(C, u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub enum ParsingError {
    FixmeFormat(pos::Pos),
    HhIgnoreComment(pos::Pos),
    ParsingError {
        pos: pos::Pos,
        msg: String,
        quickfixes: Vec<quickfix::Quickfix<pos::Pos>>,
    },
    XhpParsingError { pos: pos::Pos, msg: String },
    PackageConfigError {
        pos: pos::Pos,
        msg: String,
        reasons: Vec<message::Message<pos_or_decl::PosOrDecl>>,
    },
}
