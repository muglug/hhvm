// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub struct OpaqueDigest(());
