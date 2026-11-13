// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<c0b26c7e833e957a56eba7af72694a90>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

/// A relative position specifier in a class. Can later be
/// evaluated to an actual position in a file.
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
pub enum Pos<P> {
    /// Use the precomputed position.
    Precomputed(P),
    /// Position at the end of the class body. Will return a zero-length
    /// position just before the closing brace.
    ClassishEndOfBody(String),
    /// Position at the start of the class body. Will return a zero-length
    /// position just after the opening brace.
    ClassishStartOfBody(String),
    /// Position encompassing the full range of the closing brace of
    /// the class body.
    ClassishClosingBrace(String),
}

/// Positional information for a single class
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
pub struct ClassishPositions<P> {
    /// Zero-length position indicating the start of the class body
    /// (should be right after the opening brace)
    pub start_of_body: P,
    /// Zero-length position indicating the end of the class body
    /// (should be right before the trivia before the closing brace)
    pub end_of_body: P,
    /// The actual range for the closing brace of the class body (length 1)
    pub closing_brace: P,
    /// A list of ranges for each class-body element. Positions outside these
    /// ranges indicate white-space between methods, properties, etc.
    pub body_elements: Vec<P>,
}

/// Positional information for a collection of classes
pub type ClassishPositionsTypes<P> = s_map::SMap<ClassishPositions<P>>;
