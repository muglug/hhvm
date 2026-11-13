// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<9e6b57062425c26b9f88eb9673d8d763>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use arena_trait::TrivialDrop;
use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;
pub use user_diagnostic::Severity;

pub use crate::error_codes::GlobalAccessCheck;
pub use crate::error_codes::Naming;
pub use crate::error_codes::NastCheck;
pub use crate::error_codes::Parsing;
pub use crate::error_codes::Typing;
#[allow(unused_imports)]
use crate::*;

pub type ErrorCode = isize;

#[derive(
    Clone,
    Copy,
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
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Format {
    /// Underlined references and color
    Context,
    /// Compact format with color but no references
    Raw,
    /// Numbered and colored references
    Highlighted,
    /// Verbose positions and no color
    Plain,
    /// Verbose context showing expressions, statements, hints, and declarations involved in error
    Extended,
    /// Underlines error spans with `^^^` to simulate IDE squiggles
    PlainHighlighted,
    /// Compact format with complete ranges and no color
    Agent,
}
impl TrivialDrop for Format {}
arena_deserializer::impl_deserialize_in_arena!(Format);

pub type Diagnostic = user_diagnostic::UserDiagnostic<pos::Pos, pos_or_decl::PosOrDecl>;

/// Type representing the errors for a single file.
pub type PerFileDiagnostics = Vec<Diagnostic>;

/// The type of collections of errors
pub type Diagnostics = relative_path::map::Map<Vec<Diagnostic>>;

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
pub enum SuppressionKind {
    Fixme { forbidden_decl_fixme: bool },
    Ignore,
}

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
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct FixmeError {
    pub explanation: String,
    pub fixme_pos: pos::Pos,
}

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
pub enum FixmeOutcome {
    NotFixmed(Option<FixmeError>),
    Fixmed,
}
