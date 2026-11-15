// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactor_sd/refactor_sd_env.ml`.

use std::sync::atomic::AtomicIsize;
use std::sync::atomic::Ordering;

use oxidized::local_id::LocalId;

use super::refactor_sd_types::*;
use crate::tast_env;
use crate::typing_continuations as cont;

static VAR_COUNTER: AtomicIsize = AtomicIsize::new(0);

pub fn fresh_var() -> Entity_ {
    Entity_::Variable(VAR_COUNTER.fetch_add(1, Ordering::SeqCst) + 1)
}

/// `WrappedMap.merge_env env s1 s2 ~combine`: the bindings of `s2`, then
/// those of `s1` that `s2` does not have.
fn merge_env<K: Ord + Clone, V: Clone, E>(
    env: &mut E,
    s1: &std::collections::BTreeMap<K, V>,
    s2: &std::collections::BTreeMap<K, V>,
    mut combine: impl FnMut(&mut E, &K, Option<&V>, Option<&V>) -> Option<V>,
) -> std::collections::BTreeMap<K, V> {
    let mut map = std::collections::BTreeMap::new();
    for (key, v2) in s2 {
        if let Some(v) = combine(env, key, s1.get(key), Some(v2)) {
            map.insert(key.clone(), v);
        }
    }
    for (key, v1) in s1 {
        if !s2.contains_key(key) {
            if let Some(v) = combine(env, key, Some(v1), None) {
                map.insert(key.clone(), v);
            }
        }
    }
    map
}

/// `new @ constraints`
fn prepend(constraints: &mut Vec<Constraint_>, new: Vec<Constraint_>) {
    constraints.splice(0..0, new);
}

fn union_continuation_at_lid(entity1: &Entity, entity2: &Entity) -> (Vec<Constraint_>, Entity) {
    match (entity1, entity2) {
        (Some(entity1_), Some(entity2_)) => {
            let var = fresh_var();
            let constraints = vec![
                Constraint_::Subset(entity1_.clone(), var.clone()),
                Constraint_::Subset(entity2_.clone(), var.clone()),
            ];
            (constraints, Some(var))
        }
        (entity, None) | (None, entity) => (vec![], entity.clone()),
    }
}

fn union_continuation(
    constraints: &mut Vec<Constraint_>,
    cont1: &LMap<Entity>,
    cont2: &LMap<Entity>,
) -> LMap<Entity> {
    merge_env(constraints, cont1, cont2, |constraints, _lid, entity1_opt, entity2_opt| {
        match (entity1_opt, entity2_opt) {
            (Some(entity1), Some(entity2)) => {
                let (new_constraints, entity) = union_continuation_at_lid(entity1, entity2);
                prepend(constraints, new_constraints);
                Some(entity)
            }
            (Some(entity), None) | (None, Some(entity)) => Some(entity.clone()),
            (None, None) => None,
        }
    })
}

pub mod lenv {
    use super::*;

    pub fn init(bindings: LMap<Entity>) -> Lenv {
        Lenv::from([(cont::T::Next, bindings)])
    }

    pub fn get_local_in_continuation(lenv: &Lenv, cont: cont::T, lid: &LocalId) -> Entity {
        lenv.get(&cont).and_then(|m| m.get(lid)).cloned().flatten()
    }

    pub fn get_local(lenv: &Lenv, lid: &LocalId) -> Entity {
        get_local_in_continuation(lenv, cont::T::Next, lid)
    }

    pub fn set_local_in_continuation(lenv: &mut Lenv, cont: cont::T, lid: LocalId, entity: Entity) {
        if let Some(lenv_per_cont) = lenv.get_mut(&cont) {
            lenv_per_cont.insert(lid, entity);
        }
    }

    pub fn set_local(lenv: &mut Lenv, lid: LocalId, entity: Entity) {
        set_local_in_continuation(lenv, cont::T::Next, lid, entity)
    }

    pub fn drop_cont(lenv: &mut Lenv, cont: cont::T) {
        lenv.remove(&cont);
    }

    pub fn drop_conts(lenv: &mut Lenv, conts: &[cont::T]) {
        for cont in conts {
            drop_cont(lenv, *cont)
        }
    }

    pub fn replace_cont(lenv: &mut Lenv, cont_key: cont::T, cont_opt: Option<LMap<Entity>>) {
        match cont_opt {
            None => drop_cont(lenv, cont_key),
            Some(cont) => {
                lenv.insert(cont_key, cont);
            }
        }
    }

    pub fn restore_cont_from(lenv: &mut Lenv, from: &Lenv, cont_key: cont::T) {
        let ctxopt = from.get(&cont_key).cloned();
        replace_cont(lenv, cont_key, ctxopt)
    }

    pub fn restore_conts_from(lenv: &mut Lenv, from: &Lenv, conts: &[cont::T]) {
        for cont in conts {
            restore_cont_from(lenv, from, *cont)
        }
    }

    /// `Cont.Map.union_env [] lenv1 lenv2 ~combine`
    pub fn union(lenv1: &Lenv, lenv2: &Lenv) -> (Vec<Constraint_>, Lenv) {
        let mut constraints = vec![];
        let lenv = merge_env(&mut constraints, lenv1, lenv2, |constraints, _, o1, o2| match (o1, o2) {
            (None, None) => None,
            (Some(v), None) | (None, Some(v)) => Some(v.clone()),
            (Some(cont1), Some(cont2)) => Some(union_continuation(constraints, cont1, cont2)),
        });
        (constraints, lenv)
    }
}

pub fn init(tast_env: tast_env::Env, constraints: Vec<Constraint_>, bindings: LMap<Entity>) -> Env {
    Env {
        constraints,
        lenv: lenv::init(bindings),
        tast_env,
    }
}

pub fn add_constraint(env: &mut Env, constraint_: Constraint_) {
    env.constraints.insert(0, constraint_)
}

pub fn reset_constraints(env: &Env) -> Env {
    Env {
        constraints: vec![],
        ..env.clone()
    }
}

pub fn get_local(env: &Env, lid: &LocalId) -> Entity {
    lenv::get_local(&env.lenv, lid)
}

pub fn set_local(env: &mut Env, lid: LocalId, entity: Entity) {
    lenv::set_local(&mut env.lenv, lid, entity)
}

pub fn union(parent_env: Env, env1: Env, env2: Env) -> Env {
    let (points_to_constraints, lenv) = lenv::union(&env1.lenv, &env2.lenv);
    let mut constraints = points_to_constraints;
    constraints.extend(env1.constraints);
    constraints.extend(env2.constraints);
    constraints.extend(parent_env.constraints);
    Env {
        lenv,
        constraints,
        tast_env: parent_env.tast_env,
    }
}

pub fn drop_cont(env: &mut Env, cont: cont::T) {
    lenv::drop_cont(&mut env.lenv, cont)
}

pub fn drop_conts(env: &mut Env, conts: &[cont::T]) {
    lenv::drop_conts(&mut env.lenv, conts)
}

pub fn replace_cont(env: &mut Env, cont_key: cont::T, cont_opt: Option<LMap<Entity>>) {
    lenv::replace_cont(&mut env.lenv, cont_key, cont_opt)
}

pub fn restore_conts_from(env: &mut Env, from: &Lenv, conts: &[cont::T]) {
    lenv::restore_conts_from(&mut env.lenv, from, conts)
}

pub fn stash_and_do(env: &mut Env, conts: &[cont::T], f: impl FnOnce(&mut Env)) {
    let parent_locals = env.lenv.clone();
    drop_conts(env, conts);
    f(env);
    restore_conts_from(env, &parent_locals, conts)
}

fn union_cont_opt(
    constraints: &mut Vec<Constraint_>,
    cont_opt1: Option<LMap<Entity>>,
    cont_opt2: Option<LMap<Entity>>,
) -> Option<LMap<Entity>> {
    match (cont_opt1, cont_opt2) {
        (None, opt) | (opt, None) => opt,
        (Some(cont1), Some(cont2)) => Some(union_continuation(constraints, &cont1, &cont2)),
    }
}

/// Union a list of continuations
fn union_conts(env: &mut Env, lenv: &Lenv, cont_keys: &[cont::T]) -> Option<LMap<Entity>> {
    let mut cont_opt = None;
    for cont_key in cont_keys {
        let cont_opt2 = lenv.get(cont_key).cloned();
        cont_opt = union_cont_opt(&mut env.constraints, cont_opt, cont_opt2);
    }
    cont_opt
}

/// Union a list of source continuations and store the result in a
/// destination continuation.
fn union_conts_and_update(env: &mut Env, from_conts: &[cont::T], to_cont: cont::T) {
    let lenv = env.lenv.clone();
    let unioned_cont = union_conts(env, &lenv, from_conts);
    replace_cont(env, to_cont, unioned_cont)
}

pub fn update_next_from_conts(env: &mut Env, from_conts: &[cont::T]) {
    union_conts_and_update(env, from_conts, cont::T::Next)
}

pub fn save_and_merge_next_in_cont(env: &mut Env, to_cont: cont::T) {
    union_conts_and_update(env, &[cont::T::Next, to_cont], to_cont)
}

pub fn move_and_merge_next_in_cont(env: &mut Env, cont_key: cont::T) {
    save_and_merge_next_in_cont(env, cont_key);
    drop_cont(env, cont::T::Next)
}

pub fn loop_continuation(cont_key: cont::T, env_before_iteration: &Env, mut env_after_iteration: Env) -> Env {
    let cont_before_iteration_opt = env_before_iteration.lenv.get(&cont_key);
    let cont_after_iteration_opt = env_after_iteration.lenv.get(&cont_key);
    let new_constraints = match (cont_before_iteration_opt, cont_after_iteration_opt) {
        (Some(cont_before_iteration), Some(cont_after_iteration)) => {
            let mut constraints = vec![];
            let _: LMap<Entity> = merge_env(
                &mut constraints,
                cont_before_iteration,
                cont_after_iteration,
                |constraints, _key, entity_before_opt, entity_after_opt| {
                    if let (Some(Some(entity_before)), Some(Some(entity_after))) =
                        (entity_before_opt, entity_after_opt)
                    {
                        prepend(
                            constraints,
                            vec![Constraint_::Subset(entity_after.clone(), entity_before.clone())],
                        )
                    }
                    None
                },
            );
            constraints
        }
        _ => vec![],
    };
    prepend(&mut env_after_iteration.constraints, new_constraints);
    env_after_iteration
}
