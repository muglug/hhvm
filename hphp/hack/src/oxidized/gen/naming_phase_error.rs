// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<71b65a371b2a0ad01b9154acfb9a0282>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

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
pub enum ExperimentalFeature {
    Supportdyn(pos::Pos),
    ConstAttr(pos::Pos),
    ConstStaticProp(pos::Pos),
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
pub enum NamingPhaseError {
    Naming(naming_error::NamingError),
    NastCheck(nast_check_error::NastCheckError),
    UnexpectedHint(pos::Pos),
    MalformedAccess(pos::Pos),
    ExperimentalFeature(ExperimentalFeature),
    Parsing(parsing_error::ParsingError),
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
pub struct Agg {
    pub naming: Vec<naming_error::NamingError>,
    pub nast_check: Vec<nast_check_error::NastCheckError>,
    pub unexpected_hints: Vec<pos::Pos>,
    pub malformed_accesses: Vec<pos::Pos>,
    pub experimental_features: Vec<ExperimentalFeature>,
    pub parsing: Vec<parsing_error::ParsingError>,
}
