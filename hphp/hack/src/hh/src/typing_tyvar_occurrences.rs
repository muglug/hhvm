// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_tyvar_occurrences.ml`. See `hh/PORTING.md`.
//!
//! The two maps are persistent (`crate::pmap`), as the OCaml `Tvid.Map`s
//! are: the value is copied whenever the inference environment is, and
//! updated one variable at a time, so a copy must not cost the size of the
//! maps. (The `oxidized` type has `BTreeMap`s, which a function with many
//! type variables copied whole at every update.)

use crate::tvid;

/// `Tvid.Set.t`, as `oxidized` defines it: what the getters return.
type TvidSet = oxidized::tvid::set::Set;

/// `Tvid.Set.t`, persistent, as the values of the maps. The OCaml adds or
/// removes one variable at a time to a set that every saved environment
/// shares (`Tvid.Set.add v' (get_tyvar_occurrences x v)`): with a `BTreeSet`
/// each of these copied the whole set (a variable that occurs in N others
/// cost O(N^2) to record and to simplify away), and each update of a shared
/// map copied the sets of a whole node of the map.
pub type OccSet = crate::pmap::Set<tvid::T>;

/// `Tvid.Map.t`, persistent.
type TvidMap<V> = crate::pmap::IntMap<V>;

/// `Typing_tyvar_occurrences.t`.
#[derive(Clone, Debug, Default)]
pub struct TypingTyvarOccurrences {
    /// A map to track which type variables occur in other type variables,
    /// that is the tyvar_occurrences of a type variable v is the set of type
    /// variables whose type or bounds contain v.
    pub tyvar_occurrences: TvidMap<OccSet>,
    /// Mapping of type variables to the type variables contained in their
    /// types which are either unsolved or themselves contain unsolved type
    /// variables.
    pub tyvars_in_tyvar: TvidMap<OccSet>,
}

/// `Typing_tyvar_occurrences.t`.
pub type T = TypingTyvarOccurrences;

pub mod log {
    use super::OccSet;
    use super::T;
    use crate::tvid;
    use crate::typing_log_value::Value;
    use crate::typing_log_value::make_map;
    use crate::typing_log_value::var_as_string;
    use crate::typing_log_value::varset_as_value;

    fn iset_imap_as_value(map: &super::TvidMap<OccSet>) -> Value {
        Value::Map(
            map.iter()
                .map(|(i, vars): (&tvid::T, &OccSet)| {
                    (
                        var_as_string(*i),
                        varset_as_value(&vars.iter().copied().collect()),
                    )
                })
                .collect(),
        )
    }

    fn tyvar_occurrences_as_value(map: &super::TvidMap<OccSet>) -> Value {
        iset_imap_as_value(map)
    }

    fn tyvars_in_tyvar_as_value(map: &super::TvidMap<OccSet>) -> Value {
        iset_imap_as_value(map)
    }

    pub fn as_value(x: &T) -> Value {
        let T {
            tyvar_occurrences,
            tyvars_in_tyvar,
        } = x;
        make_map(vec![
            (
                "tyvar_occurrences".to_string(),
                tyvar_occurrences_as_value(tyvar_occurrences),
            ),
            (
                "tyvars_in_tyvar".to_string(),
                tyvars_in_tyvar_as_value(tyvars_in_tyvar),
            ),
        ])
    }
}

pub fn init() -> T {
    T {
        tyvar_occurrences: Default::default(),
        tyvars_in_tyvar: Default::default(),
    }
}

/// The set of `Tvid.Map.find_opt`, without copying it (`None` for the empty
/// set).
fn find_tyvar_occurrences(x: &T, v: tvid::T) -> Option<&OccSet> {
    x.tyvar_occurrences.get(&v)
}

fn find_tyvars_in_tyvar(x: &T, v: tvid::T) -> Option<&OccSet> {
    x.tyvars_in_tyvar.get(&v)
}

fn to_tvid_set(vars: Option<&OccSet>) -> TvidSet {
    vars.map_or_else(TvidSet::new, |vars| vars.iter().copied().collect())
}

/// `get_tyvar_occurrences`, as the persistent set (a copy costs nothing).
pub fn get_tyvar_occurrences_set(x: &T, v: tvid::T) -> OccSet {
    find_tyvar_occurrences(x, v).cloned().unwrap_or_default()
}

pub fn get_tyvar_occurrences(x: &T, v: tvid::T) -> TvidSet {
    to_tvid_set(find_tyvar_occurrences(x, v))
}

pub fn get_tyvars_in_tyvar(x: &T, v: tvid::T) -> TvidSet {
    to_tvid_set(find_tyvars_in_tyvar(x, v))
}

fn set_tyvar_occurrences(x: &mut T, v: tvid::T, vars: OccSet) {
    x.tyvar_occurrences.insert(v, vars);
}

/// Make v occur in v', i.e. add v' to the occurrences of v.
fn add_tyvar_occurrence(x: &mut T, v: tvid::T, occurs_in: tvid::T) {
    let v_ = occurs_in;
    // `set_tyvar_occurrences x v (ISet.add v' (get_tyvar_occurrences x v))`,
    // in place (the set and the nodes on its path are copied only if another
    // version of the map shares them).
    x.tyvar_occurrences
        .get_or_insert_with(v, OccSet::new)
        .insert(v_);
}

fn add_tyvar_occurrences(x: &mut T, vars: &TvidSet, occur_in: tvid::T) {
    let v = occur_in;
    for &v_ in vars {
        add_tyvar_occurrence(x, v_, v);
    }
}

fn set_tyvars_in_tyvar(x: &mut T, v: tvid::T, vars: OccSet) {
    x.tyvars_in_tyvar.insert(v, vars);
}

pub fn make_tyvars_occur_in_tyvar(x: &mut T, vars: TvidSet, occur_in: tvid::T) {
    let v = occur_in;
    add_tyvar_occurrences(x, &vars, v);
    set_tyvars_in_tyvar(x, v, vars.into_iter().collect());
}

fn remove_tyvar_occurrence(x: &mut T, v: tvid::T, no_more_occurs_in: tvid::T) {
    let v_ = no_more_occurs_in;
    // `set_tyvar_occurrences x v (ISet.remove v' (get_tyvar_occurrences x
    // v))`, in place (the binding is created, empty, if `v` has none); nothing
    // is copied when the set does not have `v'`.
    match find_tyvar_occurrences(x, v) {
        Some(vars) if vars.contains(&v_) => {
            x.tyvar_occurrences.get_mut(&v).unwrap().remove(&v_);
        }
        Some(_) => {}
        None => set_tyvar_occurrences(x, v, OccSet::new()),
    }
}

fn remove_tyvar_from_tyvar(x: &mut T, from: tvid::T, v_: tvid::T) {
    let v = from;
    // As `remove_tyvar_occurrence`.
    match find_tyvars_in_tyvar(x, v) {
        Some(vars) if vars.contains(&v_) => {
            x.tyvars_in_tyvar.get_mut(&v).unwrap().remove(&v_);
        }
        Some(_) => {}
        None => set_tyvars_in_tyvar(x, v, OccSet::new()),
    }
}

pub fn make_tyvar_no_more_occur_in_tyvar(x: &mut T, v: tvid::T, no_more_in: tvid::T) {
    let v_ = no_more_in;
    remove_tyvar_occurrence(x, v, v_);
    remove_tyvar_from_tyvar(x, v_, v);
}

pub fn contains_unsolved_tyvars(x: &T, v: tvid::T) -> bool {
    !find_tyvars_in_tyvar(x, v).is_none_or(|vars| vars.is_empty())
}

/// Update the tyvar occurrences after unbinding a type variable.
pub fn unbind_tyvar(x: &mut T, v: tvid::T) {
    // update tyvar_occurrences.
    match find_tyvars_in_tyvar(x, v) {
        Some(vars_in_v) if !vars_in_v.is_empty() => {
            let vars_in_v = vars_in_v.clone();
            for &v_ in &vars_in_v {
                remove_tyvar_occurrence(x, v_, v);
            }
        }
        // Already bound to the empty set: `set_tyvars_in_tyvar` would write
        // what is there.
        Some(_) => return,
        None => {}
    }
    // update tyvars_in_tyvar
    set_tyvars_in_tyvar(x, v, OccSet::new());
}

pub fn occurs_in(x: &T, occuring_tv: tvid::T, in_: tvid::T) -> bool {
    let containing_tv = in_;
    let occurs =
        find_tyvar_occurrences(x, occuring_tv).is_some_and(|vars| vars.contains(&containing_tv));
    let contains =
        find_tyvars_in_tyvar(x, containing_tv).is_some_and(|vars| vars.contains(&occuring_tv));
    assert!(occurs == contains);
    occurs
}

/// remove variable from the occurrence structure.
/// Does not try and be clever, especially does not perform any
/// type simplification.
pub fn remove_var(x: &mut T, v: tvid::T) {
    if let Some(occurrences) = find_tyvar_occurrences(x, v).cloned() {
        for &occ in &occurrences {
            make_tyvar_no_more_occur_in_tyvar(x, v, occ);
        }
    }
    x.tyvar_occurrences.remove_key(&v);
    if let Some(vars_in_v) = find_tyvars_in_tyvar(x, v).cloned() {
        for &var_in_v in &vars_in_v {
            make_tyvar_no_more_occur_in_tyvar(x, var_in_v, v);
        }
    }
    x.tyvars_in_tyvar.remove_key(&v);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(vs: &[tvid::T]) -> TvidSet {
        vs.iter().copied().collect()
    }

    #[test]
    fn init_is_empty() {
        let x = init();
        assert!(x.tyvar_occurrences.is_empty());
        assert!(x.tyvars_in_tyvar.is_empty());
        assert_eq!(get_tyvar_occurrences(&x, 1), set(&[]));
        assert_eq!(get_tyvars_in_tyvar(&x, 1), set(&[]));
        assert!(!contains_unsolved_tyvars(&x, 1));
        assert!(!occurs_in(&x, 1, 2));
    }

    /// The example of the OCaml comment: #1 := (#2 | int), then #2 := #3.
    #[test]
    fn occurrences_are_shallow_and_dual() {
        let mut x = init();
        make_tyvars_occur_in_tyvar(&mut x, set(&[2]), 1);
        make_tyvars_occur_in_tyvar(&mut x, set(&[3]), 2);
        assert_eq!(get_tyvar_occurrences(&x, 2), set(&[1]));
        assert_eq!(get_tyvar_occurrences(&x, 3), set(&[2]));
        assert_eq!(get_tyvars_in_tyvar(&x, 1), set(&[2]));
        assert_eq!(get_tyvars_in_tyvar(&x, 2), set(&[3]));
        assert!(occurs_in(&x, 2, 1));
        assert!(occurs_in(&x, 3, 2));
        // Shallow: #3 is not recorded as occurring in #1.
        assert!(!occurs_in(&x, 3, 1));
        assert!(contains_unsolved_tyvars(&x, 1));
        assert!(!contains_unsolved_tyvars(&x, 3));
    }

    #[test]
    fn make_tyvars_occur_replaces_tyvars_in_tyvar_but_not_occurrences() {
        let mut x = init();
        make_tyvars_occur_in_tyvar(&mut x, set(&[2, 3]), 1);
        // `set_tyvars_in_tyvar` overwrites, `add_tyvar_occurrences` only adds:
        // the OCaml leaves the stale occurrence of #2 in #1 behind (callers
        // unbind first).
        make_tyvars_occur_in_tyvar(&mut x, set(&[3]), 1);
        assert_eq!(get_tyvars_in_tyvar(&x, 1), set(&[3]));
        assert_eq!(get_tyvar_occurrences(&x, 2), set(&[1]));
        assert_eq!(get_tyvar_occurrences(&x, 3), set(&[1]));
    }

    #[test]
    fn unbind_tyvar_keeps_empty_entries() {
        let mut x = init();
        make_tyvars_occur_in_tyvar(&mut x, set(&[2, 3]), 1);
        unbind_tyvar(&mut x, 1);
        assert_eq!(get_tyvars_in_tyvar(&x, 1), set(&[]));
        assert!(!occurs_in(&x, 2, 1));
        assert!(!occurs_in(&x, 3, 1));
        // As in OCaml, the keys stay, bound to empty sets.
        assert_eq!(x.tyvars_in_tyvar.get(&1), Some(&OccSet::new()));
        assert_eq!(x.tyvar_occurrences.get(&2), Some(&OccSet::new()));
        assert_eq!(x.tyvar_occurrences.get(&3), Some(&OccSet::new()));
    }

    #[test]
    fn make_tyvar_no_more_occur_creates_entries_for_unknown_vars() {
        let mut x = init();
        make_tyvar_no_more_occur_in_tyvar(&mut x, 5, 6);
        assert_eq!(x.tyvar_occurrences.get(&5), Some(&OccSet::new()));
        assert_eq!(x.tyvars_in_tyvar.get(&6), Some(&OccSet::new()));
    }

    #[test]
    fn remove_var_removes_both_directions() {
        let mut x = init();
        // #1 := f(#2), #2 := g(#3)
        make_tyvars_occur_in_tyvar(&mut x, set(&[2]), 1);
        make_tyvars_occur_in_tyvar(&mut x, set(&[3]), 2);
        remove_var(&mut x, 2);
        assert!(!x.tyvar_occurrences.contains_key(&2));
        assert!(!x.tyvars_in_tyvar.contains_key(&2));
        assert_eq!(get_tyvars_in_tyvar(&x, 1), set(&[]));
        assert_eq!(get_tyvar_occurrences(&x, 3), set(&[]));
        assert!(!occurs_in(&x, 2, 1));
        assert!(!occurs_in(&x, 3, 2));
    }

    #[test]
    fn remove_var_of_self_occurrence() {
        let mut x = init();
        make_tyvars_occur_in_tyvar(&mut x, set(&[1]), 1);
        assert!(occurs_in(&x, 1, 1));
        remove_var(&mut x, 1);
        assert!(!x.tyvars_in_tyvar.contains_key(&1));
        assert!(!x.tyvar_occurrences.contains_key(&1));
    }

    #[test]
    #[should_panic]
    fn occurs_in_asserts_that_both_maps_agree() {
        let mut x = init();
        x.tyvar_occurrences.insert(2, OccSet::unit(1));
        occurs_in(&x, 2, 1);
    }
}
