// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactor_sd/refactor_sd_solver.ml`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use super::refactor_sd_types::*;
use crate::pos::Pos;

type PointsToSet = BTreeSet<(Entity_, Entity_)>;
type EntityMap<V> = BTreeMap<Entity_, V>;
type EntitySet = BTreeSet<Entity_>;

#[derive(Default)]
struct Constraints {
    introductions: Vec<Pos>,
    subsets: Vec<(Entity_, Entity_)>,
    upcasts: Vec<(Entity_, Pos)>,
    calleds: Vec<Pos>,
}

fn transitive_closure(mut set: PointsToSet) -> PointsToSet {
    loop {
        // `PointsToSet.fold immediate_consequence set set`
        let mut new_set = set.clone();
        for (x, y) in &set {
            // `PointsToSet.fold add set set` (the set as it is then)
            let snapshot = new_set.clone();
            for (y_, z) in &snapshot {
                if y == y_ {
                    new_set.insert((x.clone(), z.clone()));
                }
            }
        }
        if new_set.len() == set.len() {
            return set;
        }
        set = new_set
    }
}

fn find_pointers(introductions: &[Pos], set: &PointsToSet) -> PointsToSet {
    let mut has_pointer_set = PointsToSet::new();
    for pointer_pos in introductions {
        has_pointer_set.extend(
            set.iter()
                .filter(|(sub, _)| matches!(sub, Entity_::Literal(pos) if pointer_pos == pos))
                .cloned(),
        )
    }
    has_pointer_set
}

fn find_calls(introductions: &[Pos], set: &PointsToSet) -> PointsToSet {
    let mut called_set = PointsToSet::new();
    for called_pos in introductions {
        called_set.extend(
            set.iter()
                .filter(|(_, sup)| matches!(sup, Entity_::Literal(pos) if called_pos == pos))
                .cloned(),
        )
    }
    called_set
}

/// (The positions are a list whose head is the last one added.)
fn remove_duplicates(mut positions: Vec<Pos>, (_entity, pos): (Entity_, Pos)) -> Vec<Pos> {
    if !positions.contains(&pos) {
        positions.insert(0, pos)
    }
    positions
}

fn partition_constraint(mut constraints: Constraints, c: &Constraint_) -> Constraints {
    match c {
        Constraint_::Introduction(pos) => constraints.introductions.insert(0, pos.clone()),
        Constraint_::Subset(sub, sup) => constraints.subsets.insert(0, (sub.clone(), sup.clone())),
        Constraint_::Upcast(entity, pos) => constraints.upcasts.insert(0, (entity.clone(), pos.clone())),
        Constraint_::Called(pos) => constraints.calleds.insert(0, pos.clone()),
    }
    constraints
}

type Collect = Box<dyn Fn(&(Entity_, Pos)) -> Vec<(Entity_, Pos)>>;

fn subset_lookups(subsets: &PointsToSet) -> (Collect, Collect) {
    let mut subset_map: EntityMap<EntitySet> = EntityMap::new();
    let mut superset_map: EntityMap<EntitySet> = EntityMap::new();
    for (e, e_) in subsets {
        subset_map.entry(e_.clone()).or_default().insert(e.clone());
        superset_map.entry(e.clone()).or_default().insert(e_.clone());
    }
    // Generate lookup functions. This code is different from shape_analysis.
    fn collect(map: EntityMap<EntitySet>) -> Collect {
        Box::new(move |(entity, pos)| match map.get(entity) {
            Some(entities) => entities.iter().map(|ent| (ent.clone(), pos.clone())).collect(),
            None => vec![],
        })
    }
    (collect(subset_map), collect(superset_map))
}

pub fn simplify(constraints: &[Constraint_]) -> Vec<RefactorSdResult> {
    let Constraints {
        introductions,
        upcasts,
        subsets,
        calleds,
    } = constraints.iter().fold(Constraints::default(), partition_constraint);
    let subsets = transitive_closure(subsets.into_iter().collect());
    // Limit upcasts to functions of interest
    let subsets_pointers = find_pointers(&introductions, &subsets);
    let (collect_subsets_to_pointers, _collect_supersets_to_pointers) = subset_lookups(&subsets_pointers);
    let upcasts: Vec<(Entity_, Pos)> = upcasts.iter().flat_map(|u| collect_subsets_to_pointers(u)).collect();
    // Limit upcasts to functions that are later called
    let subsets_calls = find_calls(&calleds, &subsets);
    let (_collect_subsets_to_calls, collect_supersets_to_calls) = subset_lookups(&subsets_calls);
    let upcasts: Vec<(Entity_, Pos)> = upcasts.iter().flat_map(|u| collect_supersets_to_calls(u)).collect();
    // Remove duplicates. Duplicates occur when reassigning variables or using a mutable collection.
    let upcast_pos = upcasts.into_iter().fold(vec![], remove_duplicates);
    // Convert to individual upcast results
    let exists_upcast_results: Vec<RefactorSdResult> =
        upcast_pos.into_iter().map(RefactorSdResult::ExistsUpcast).collect();
    if exists_upcast_results.is_empty() {
        vec![RefactorSdResult::NoUpcast]
    } else {
        exists_upcast_results
    }
}
