// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Xrefs` (`write_symbol_info/xrefs.ml`).

use std::collections::BTreeMap;

use oxidized::pos::Pos;

use super::glean::fact_id;
use super::glean::hack::declaration;
use super::glean::hack::x_ref_target;

/// `PosMap`: a map keyed by `Pos.compare` (the `Ord` of `Pos`).
pub type PosMapOf<V> = BTreeMap<Pos, V>;

/// maps a target fact id to the json representation of the corresponding fact,
/// and the positions of symbol that reference it
pub type FactMap = fact_id::Map<(x_ref_target::T, Vec<Pos>)>;

#[derive(Clone, Debug)]
pub struct TargetInfo {
    pub target: x_ref_target::T,
    pub receiver_type: Option<declaration::T>,
    /// the fact_id of the target
    pub fact_id: fact_id::T,
}

/// maps a position to various info about the target
pub type PosMap = PosMapOf<Vec<TargetInfo>>;

/// records if any of the symbol occurrences of a given target fact_id has
/// SO.affects_prod_build = true
pub type UsedInProdBuildMap = fact_id::Map<bool>;

/// Maps of XRefs, constructed for a given file. (The lists of the OCaml
/// maps are built by consing: the head of each OCaml list is the LAST
/// element of its vector here.)
#[derive(Clone, Debug, Default)]
pub struct T {
    pub fact_map: FactMap,
    pub pos_map: PosMap,
    pub used_in_prod_build: UsedInProdBuildMap,
}

/// The head of the list of targets at a position of a [`PosMap`] (the
/// OCaml's `Some (ti :: _)`).
pub fn pos_map_find_first<'a>(pos_map: &'a PosMap, pos: &Pos) -> Option<&'a TargetInfo> {
    pos_map.get(pos).and_then(|tis| tis.last())
}

/// Updates both maps. It is expected that for a given fact_id, all json are equal.
pub fn add(t: &mut T, target_id: fact_id::T, pos: Pos, target_info: TargetInfo) {
    match t.fact_map.get_mut(&target_id) {
        None => {
            t.fact_map
                .insert(target_id, (target_info.target.clone(), vec![pos.clone()]));
        }
        Some((_json, refs)) => refs.push(pos.clone()),
    }
    t.pos_map.entry(pos).or_default().push(target_info);
}

/// given a target identified by its fact_id, update the used_in_prod_build_map with
/// the affects_prod_build information of a symbol occurrence of the target
/// Remark that a target, used_in_prod_build can be false only if all its symbol occurrences
/// have affetcs_prod_build = false
pub fn mark_target_used_in_prod_build(t: &mut T, fact_id: fact_id::T, affects_prod_build: bool) {
    let e = t.used_in_prod_build.entry(fact_id).or_insert(false);
    *e = *e || affects_prod_build;
}

pub fn empty() -> T {
    T::default()
}
