// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<3eb607af1201875dc69a56e302ce39be>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;
pub use typing_defs::*;

pub use crate::typing_set as ty_set;
#[allow(unused_imports)]
use crate::*;

pub type TparamBounds = ty_set::TySet;

/// The kind of a type, used to collect information about type paramters.
#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct Kind {
    pub lower_bounds: TparamBounds,
    pub upper_bounds: TparamBounds,
    /// = Reified if generic parameter is marked `reify`, = Erased otherwise
    pub reified: aast::ReifyKind,
    /// Set if generic parameter has attribute <<__Enforceable>>
    pub enforceable: bool,
    /// Set if generic parameter has attribute <<__Newable>>
    pub newable: bool,
    /// Set if class is marked <<__SupportDynamicType>> and
    /// generic parameter does *not* have attribute <<__NoRequireDynamic>>
    pub require_dynamic: bool,
    pub rank: isize,
}

#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct NamedKind(pub typing_defs::PosId, pub Kind);
