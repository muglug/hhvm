// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated <<SignedSource::*O*zOeWoEQle#+L!plEphiEmie@IsG>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen
use arena_trait::TrivialDrop;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

/// These severity levels are based on those provided by Arcanist:
/// - Error: when it fires, it will require confirmation
/// - Warning: when it fires, it shows up visibly before landing
/// - Advice: Similar to warning, but implies lesser severity
/// - Disabled: Hidden from most UI, but it is useful for telemetry
#[derive(
    Clone,
    Copy,
    Debug,
    Deserialize,
    Eq,
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Severity {
    LintError,
    LintWarning,
    LintAdvice,
    LintDisabled,
}
impl TrivialDrop for Severity {}
arena_deserializer::impl_deserialize_in_arena!(Severity);

#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct LintsCore<Pos> {
    pub code: isize,
    pub severity: Severity,
    pub pos: Pos,
    pub message: String,
    /// Normally, lint warnings and lint advice only get shown by arcanist if the
    /// lines they are raised on overlap with lines changed in a diff. This
    /// flag bypasses that behavior
    pub bypass_changed_lines: bool,
    pub autofix: Option<(String, pos::Pos)>,
    pub check_status: Option<aast_defs::CheckStatus>,
}
