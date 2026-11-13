// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<b2e982f3d0d6d47dc92e3cdbd02a6bc7>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use arena_trait::TrivialDrop;
use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

/// This is used as a filter on top-level symbol searches, for both autocomplete and symbol-search.
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
pub enum AutocompleteType {
    /// satisfies [valid_for_acid], e.g. in autocomplete contexts like `|` at the start of a statement
    Acid,
    /// satisfies [valid_for_acclassish], currently only used for `nameof`
    Acclassish,
    /// satisfies [valid_for_acnew] AND isn't an abstract class, e.g. in autocomplete contexts like `$x = new |`
    Acnew,
    /// satisfies [valid_for_actype], e.g. in autocomplete contexts like `Foo<|`
    Actype,
    /// is [SI_Trait], e.g. in autocomplete contexts like `uses |`
    ActraitOnly,
    /// isn't [SI_Namespace]; repo-wide symbol search
    AcWorkspaceSymbol,
}
impl TrivialDrop for AutocompleteType {}
arena_deserializer::impl_deserialize_in_arena!(AutocompleteType);

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
pub enum SiFile {
    /// string represent Int64
    SIFilehash(String),
    SIPath(relative_path::RelativePath),
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
pub struct SiItem {
    pub name: String,
    pub kind: file_info::SiKind,
    /// needed so that local file deletes can "tombstone" the item
    pub file: SiFile,
    pub fullname: String,
}

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
pub enum SiComplete {
    Complete,
    Incomplete,
}
impl TrivialDrop for SiComplete {}
arena_deserializer::impl_deserialize_in_arena!(SiComplete);
