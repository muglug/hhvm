// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/collections/wrapped_map.ml`. See `hh/PORTING.md`.
//!
//! The functions that `Wrapped_map.Make` adds to `Stdlib.Map`, for the
//! persistent maps of the port (`im::OrdMap`, and `crate::pmap::Map`: the
//! functions take either, through [`MapLike`]). `S_map`, `I_map`,
//! `Local_id.Map`... are instances of it: `crate::s_map` and the others
//! re-export these functions.
//!
//! Careful with the order: `keys`, `values` and `elements` are in
//! *decreasing* order of the keys, as in OCaml (they are folds that
//! accumulate a list); `ordered_keys` is in increasing order, like
//! `bindings`.
//!
//! Not here: `make_hash_fold_t`, `make_yojson_of_t` and
//! `map_env_ty_err_opt`.

use im::OrdMap;

/// The persistent maps that these functions work on: `im::OrdMap` and
/// `crate::pmap::Map`. `Rebind<W>` is the same kind of map with values of
/// type `W` (what `merge` and `map_env` return). OCaml's `Wrapped_map.Make`
/// is a functor over `Stdlib.Map`; the port's maps are `im::OrdMap` (cheap
/// clones, hh/PORTING.md) or, for the maps of the typing environment,
/// `crate::pmap::Map`, so the functions take either: `S_map.union` etc. keep
/// one name for both.
pub trait MapLike<K, V>: Sized + Clone {
    type Rebind<W: Clone>: MapLike<K, W>;
    type Iter<'a>: DoubleEndedIterator<Item = (&'a K, &'a V)>
    where
        Self: 'a,
        K: 'a,
        V: 'a;
    fn ml_new() -> Self;
    fn ml_is_empty(&self) -> bool;
    fn ml_get(&self, k: &K) -> Option<&V>;
    fn ml_insert(&mut self, k: K, v: V);
    fn ml_remove(&mut self, k: &K);
    fn ml_len(&self) -> usize;
    fn ml_iter(&self) -> Self::Iter<'_>;
}

impl<K: Ord + Clone, V: Clone> MapLike<K, V> for OrdMap<K, V> {
    type Rebind<W: Clone> = OrdMap<K, W>;
    type Iter<'a>
        = im::ordmap::Iter<'a, K, V>
    where
        K: 'a,
        V: 'a;
    #[inline]
    fn ml_new() -> Self {
        OrdMap::new()
    }
    #[inline]
    fn ml_is_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn ml_get(&self, k: &K) -> Option<&V> {
        self.get(k)
    }
    #[inline]
    fn ml_insert(&mut self, k: K, v: V) {
        self.insert(k, v);
    }
    #[inline]
    fn ml_remove(&mut self, k: &K) {
        self.remove(k);
    }
    #[inline]
    fn ml_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn ml_iter(&self) -> Self::Iter<'_> {
        self.iter()
    }
}

impl<K: crate::pmap::Key + Clone, V: Clone> MapLike<K, V> for crate::pmap::Map<K, V> {
    type Rebind<W: Clone> = crate::pmap::Map<K, W>;
    type Iter<'a>
        = crate::pmap::Iter<'a, K, V>
    where
        K: 'a,
        V: 'a;
    #[inline]
    fn ml_new() -> Self {
        crate::pmap::Map::new()
    }
    #[inline]
    fn ml_is_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn ml_get(&self, k: &K) -> Option<&V> {
        self.get(k)
    }
    #[inline]
    fn ml_insert(&mut self, k: K, v: V) {
        self.insert(k, v);
    }
    #[inline]
    fn ml_remove(&mut self, k: &K) {
        self.remove(k);
    }
    #[inline]
    fn ml_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn ml_iter(&self) -> Self::Iter<'_> {
        self.iter()
    }
}

/// `Stdlib.Map.merge`: `f` is called for each key of either map, with what
/// the maps have for the key.
///
/// (Here `f` is called in increasing order of the keys. In OCaml the order
/// depends on the shape of the trees: do not rely on it. The same goes for
/// `union` and `for_all2`, which are made of it.)
pub fn merge<K, A, B, C, M1, M2>(
    mut f: impl FnMut(&K, Option<&A>, Option<&B>) -> Option<C>,
    m1: &M1,
    m2: &M2,
) -> M1::Rebind<C>
where
    K: Ord + Clone,
    A: Clone,
    B: Clone,
    C: Clone,
    M1: MapLike<K, A>,
    M2: MapLike<K, B>,
{
    let mut res = <M1::Rebind<C>>::ml_new();
    let mut i1 = m1.ml_iter().peekable();
    let mut i2 = m2.ml_iter().peekable();
    loop {
        let (key, v1, v2) = match (i1.peek(), i2.peek()) {
            (None, None) => break,
            (Some(_), None) => {
                let (k, v1) = i1.next().unwrap();
                (k, Some(v1), None)
            }
            (None, Some(_)) => {
                let (k, v2) = i2.next().unwrap();
                (k, None, Some(v2))
            }
            (Some((k1, _)), Some((k2, _))) => match k1.cmp(k2) {
                std::cmp::Ordering::Less => {
                    let (k, v1) = i1.next().unwrap();
                    (k, Some(v1), None)
                }
                std::cmp::Ordering::Greater => {
                    let (k, v2) = i2.next().unwrap();
                    (k, None, Some(v2))
                }
                std::cmp::Ordering::Equal => {
                    let (k, v1) = i1.next().unwrap();
                    let (_, v2) = i2.next().unwrap();
                    (k, Some(v1), Some(v2))
                }
            },
        };
        if let Some(v) = f(key, v1, v2) {
            res.ml_insert(key.clone(), v);
        }
    }
    res
}

/// The bindings of both maps. For a key that both have, `combine` chooses
/// the value (`None` removes the key).
///
/// `combine` defaults to picking the first value argument.
pub fn union<K, A, M>(combine: Option<&dyn Fn(&K, &A, &A) -> Option<A>>, x: &M, y: &M) -> M
where
    K: Ord + Clone,
    A: Clone,
    M: MapLike<K, A, Rebind<A> = M>,
{
    union_into_larger(x, y, |k, v1, v2| match combine {
        None => Some(v1.clone()),
        Some(combine) => combine(k, v1, v2),
    })
}

/// The union of `x` and `y`, `combine` choosing the value of a key that both
/// have (`v1` is that of `x`), called for those keys in increasing order.
///
/// OCaml's `Map.union` shares the subtrees of its arguments; this starts from
/// (a clone of, which shares all of it) the larger map and adds the bindings
/// of the smaller one: as many insertions as the smaller map has keys, not
/// a rebuild of both maps entry by entry.
fn union_into_larger<K, A, M>(x: &M, y: &M, mut combine: impl FnMut(&K, &A, &A) -> Option<A>) -> M
where
    K: Ord + Clone,
    A: Clone,
    M: MapLike<K, A>,
{
    // The union of a map with the empty map is that map.
    if y.ml_is_empty() {
        return x.clone();
    }
    if x.ml_is_empty() {
        return y.clone();
    }
    let y_is_smaller = y.ml_len() <= x.ml_len();
    let (mut res, smaller) = if y_is_smaller { (x.clone(), y) } else { (y.clone(), x) };
    for (k, v_smaller) in smaller.ml_iter() {
        let v = match res.ml_get(k) {
            None => Some(v_smaller.clone()),
            Some(v_larger) => {
                if y_is_smaller {
                    combine(k, v_larger, v_smaller)
                } else {
                    combine(k, v_smaller, v_larger)
                }
            }
        };
        match v {
            Some(v) => res.ml_insert(k.clone(), v),
            None => res.ml_remove(k),
        }
    }
    res
}

/// `combine` is called for each key of `s2`, in increasing order, then for
/// each key that only `s1` has, in increasing order.
pub fn merge_env<Env, K, A, B, C, M1, M2>(
    env: &mut Env,
    s1: &M1,
    s2: &M2,
    mut combine: impl FnMut(&mut Env, &K, Option<&A>, Option<&B>) -> Option<C>,
) -> M1::Rebind<C>
where
    K: Ord + Clone,
    A: Clone,
    B: Clone,
    C: Clone,
    M1: MapLike<K, A>,
    M2: MapLike<K, B>,
{
    let mut map = <M1::Rebind<C>>::ml_new();
    for (key, v2) in s2.ml_iter() {
        let v1opt = s1.ml_get(key);
        let vopt = combine(env, key, v1opt, Some(v2));
        if let Some(v) = vopt {
            map.ml_insert(key.clone(), v);
        }
    }
    for (key, v1) in s1.ml_iter() {
        let v2opt = s2.ml_get(key);
        match v2opt {
            None => {
                let vopt = combine(env, key, Some(v1), None);
                if let Some(v) = vopt {
                    map.ml_insert(key.clone(), v);
                }
            }
            Some(_) => {}
        }
    }
    map
}

/// `combine` is called for the keys that both maps have, in increasing
/// order.
pub fn union_env<Env, K, A, M>(
    env: &mut Env,
    s1: &M,
    s2: &M,
    mut combine: impl FnMut(&mut Env, &K, &A, &A) -> Option<A>,
) -> M
where
    K: Ord + Clone,
    A: Clone,
    M: MapLike<K, A, Rebind<A> = M>,
{
    union_into_larger(s1, s2, |key, v1, v2| combine(env, key, v1, v2))
}

/// The keys, in decreasing order.
pub fn keys<K: Ord + Clone, A: Clone, M: MapLike<K, A>>(m: &M) -> Vec<K> {
    m.ml_iter().rev().map(|(k, _)| k.clone()).collect()
}

/// The keys, in increasing order.
pub fn ordered_keys<K: Ord + Clone, A: Clone, M: MapLike<K, A>>(m: &M) -> Vec<K> {
    m.ml_iter().map(|(k, _)| k.clone()).collect()
}

/// The values, in decreasing order of their keys.
pub fn values<K: Ord + Clone, A: Clone, M: MapLike<K, A>>(m: &M) -> Vec<A> {
    m.ml_iter().rev().map(|(_, v)| v.clone()).collect()
}

/// `f` is called for each binding, in increasing order of the keys.
pub fn fold_env<Env, K, B, C, M>(
    env: &mut Env,
    mut f: impl FnMut(&mut Env, &K, &B, C) -> C,
    m: &M,
    init: C,
) -> C
where
    K: Ord + Clone,
    B: Clone,
    M: MapLike<K, B>,
{
    let mut acc = init;
    for (key, v) in m.ml_iter() {
        acc = f(env, key, v, acc);
    }
    acc
}

/// The bindings, in decreasing order of the keys.
pub fn elements<K: Ord + Clone, A: Clone, M: MapLike<K, A>>(m: &M) -> Vec<(K, A)> {
    m.ml_iter()
        .rev()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect()
}

/// `f` is called for each binding, in increasing order of the keys.
pub fn map_env<Env, K, A, B, M>(
    mut f: impl FnMut(&mut Env, &K, &A) -> B,
    env: &mut Env,
    m: &M,
) -> M::Rebind<B>
where
    K: Ord + Clone,
    A: Clone,
    B: Clone,
    M: MapLike<K, A>,
{
    let mut map = <M::Rebind<B>>::ml_new();
    for (key, v) in m.ml_iter() {
        let v = f(env, key, v);
        map.ml_insert(key.clone(), v);
    }
    map
}

pub fn filter_opt<K: Ord + Clone, A: Clone, M: MapLike<K, Option<A>>>(m: &M) -> M::Rebind<A> {
    let mut map = <M::Rebind<A>>::ml_new();
    for (k, x) in m.ml_iter() {
        if let Some(x) = x {
            map.ml_insert(k.clone(), x.clone());
        }
    }
    map
}

/// When a key is there several times, its last value is kept.
pub fn of_list<K: Ord + Clone, A: Clone>(elts: Vec<(K, A)>) -> OrdMap<K, A> {
    let mut acc = OrdMap::new();
    for (key, value) in elts {
        acc.insert(key, value);
    }
    acc
}

pub fn of_function<K: Ord + Clone, A: Clone>(
    domain: &[K],
    mut f: impl FnMut(&K) -> A,
) -> OrdMap<K, A> {
    let mut acc = OrdMap::new();
    for key in domain {
        acc.insert(key.clone(), f(key));
    }
    acc
}

/// Adds the binding. When the key is already there and there is a
/// `combine`, the value is `combine old_value new_value`.
pub fn add<K, A, M>(combine: Option<&dyn Fn(&A, &A) -> A>, key: K, new_value: A, mut map: M) -> M
where
    K: Ord + Clone,
    A: Clone,
    M: MapLike<K, A>,
{
    let value = match combine {
        None => new_value,
        Some(combine) => match map.ml_get(&key) {
            None => new_value,
            Some(old_value) => combine(old_value, &new_value),
        },
    };
    map.ml_insert(key, value);
    map
}

/// `f` is called for each value, in increasing order of the keys.
///
/// (OCaml returns the map itself when no value changed, physically. The
/// result is the same map either way. No caller in the crate needs the
/// sharing.)
pub fn ident_map<K, A, M>(mut f: impl FnMut(&A) -> A, map: &M) -> M
where
    K: Ord + Clone,
    A: Clone,
    M: MapLike<K, A>,
{
    let mut map_ = M::ml_new();
    for (key, item) in map.ml_iter() {
        map_.ml_insert(key.clone(), f(item));
    }
    map_
}

/// `f` is called for each key, in increasing order. When two keys become the
/// same key, `combine` chooses the value (the last one, without `combine`).
pub fn ident_map_key<K, A, M>(
    combine: Option<&dyn Fn(&A, &A) -> A>,
    mut f: impl FnMut(&K) -> K,
    map: &M,
) -> M
where
    K: Ord + Clone,
    A: Clone,
    M: MapLike<K, A>,
{
    let mut map_ = M::ml_new();
    for (key, item) in map.ml_iter() {
        let new_key = f(key);
        map_ = add(combine, new_key, item.clone(), map_);
    }
    map_
}

/// `f` is called for each key of either map (for all of them, even after it
/// returned `false`).
pub fn for_all2<K, A, B, M1, M2>(
    mut f: impl FnMut(&K, Option<&A>, Option<&B>) -> bool,
    m1: &M1,
    m2: &M2,
) -> bool
where
    K: Ord + Clone,
    A: Clone,
    B: Clone,
    M1: MapLike<K, A>,
    M2: MapLike<K, B>,
{
    // `merge` into a map of booleans, then `for_all` over it: every key is
    // visited, in increasing order.
    let mut all = true;
    let _: M1::Rebind<()> = merge(
        |k, v1opt, v2opt| {
            all &= f(k, v1opt, v2opt);
            None
        },
        m1,
        m2,
    );
    all
}

pub fn make_pp<K, A, M>(
    pp_key: impl Fn(&mut crate::format::Formatter, &K),
    pp_data: impl Fn(&mut crate::format::Formatter, &A),
    fmt: &mut crate::format::Formatter,
    x: &M,
) where
    K: Ord + Clone,
    A: Clone,
    M: MapLike<K, A>,
{
    use crate::format;
    // "@[<hv 2>{"
    format::pp_open_hvbox(fmt, 2);
    format::pp_print_char(fmt, '{');
    if !x.ml_is_empty() {
        // " "
        format::pp_print_char(fmt, ' ');
    }
    let mut sep = false;
    for (key, data) in x.ml_iter() {
        if sep {
            // ";@ "
            format::pp_print_char(fmt, ';');
            format::pp_print_space(fmt);
        }
        // "@["
        format::pp_open_box(fmt, 0);
        pp_key(fmt, key);
        // " ->@ "
        format::pp_print_string(fmt, " ->");
        format::pp_print_space(fmt);
        pp_data(fmt, data);
        // "@]"
        format::pp_close_box(fmt);
        sep = true;
    }
    if !x.ml_is_empty() {
        // " "
        format::pp_print_char(fmt, ' ');
    }
    // "}@]"
    format::pp_print_char(fmt, '}');
    format::pp_close_box(fmt);
}

/// Find an element that satisfies some boolean predicate.
/// No other guarantees are given (decidability, ordering, ...).
pub fn find_one_opt<K, A, M>(map: &M, mut f: impl FnMut(&K) -> bool) -> Option<A>
where
    K: Ord + Clone,
    A: Clone,
    M: MapLike<K, A>,
{
    for (key, value) in map.ml_iter() {
        if f(key) {
            return Some(value.clone());
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(l: &[(isize, &str)]) -> OrdMap<isize, String> {
        l.iter().map(|(k, v)| (*k, v.to_string())).collect()
    }

    #[test]
    fn orders() {
        let map = m(&[(2, "b"), (1, "a"), (3, "c")]);
        assert_eq!(keys(&map), [3, 2, 1]);
        assert_eq!(ordered_keys(&map), [1, 2, 3]);
        assert_eq!(values(&map), ["c", "b", "a"]);
        assert_eq!(
            elements(&map),
            [(3, "c".to_string()), (2, "b".to_string()), (1, "a".to_string())]
        );
    }

    #[test]
    fn unions() {
        let m1 = m(&[(1, "a1"), (2, "b1")]);
        let m2 = m(&[(2, "b2"), (3, "c2")]);
        // The first map wins.
        assert_eq!(union(None, &m1, &m2), m(&[(1, "a1"), (2, "b1"), (3, "c2")]));
        assert_eq!(union(None, &m2, &m1), m(&[(1, "a1"), (2, "b2"), (3, "c2")]));
        let concat = |_: &isize, a: &String, b: &String| Some(format!("{}{}", a, b));
        assert_eq!(
            union(Some(&concat), &m1, &m2),
            m(&[(1, "a1"), (2, "b1b2"), (3, "c2")])
        );
        let drop = |_: &isize, _: &String, _: &String| None;
        assert_eq!(union(Some(&drop), &m1, &m2), m(&[(1, "a1"), (3, "c2")]));
    }

    #[test]
    fn merges() {
        let m1 = m(&[(1, "a1"), (2, "b1")]);
        let m2 = m(&[(2, "b2"), (3, "c2")]);
        let mut calls = vec![];
        let merged = merge(
            |k, v1, v2| {
                calls.push(*k);
                match (v1, v2) {
                    (Some(v1), Some(v2)) => Some(format!("{}+{}", v1, v2)),
                    (Some(_), None) => None,
                    (None, v2) => v2.cloned(),
                }
            },
            &m1,
            &m2,
        );
        assert_eq!(calls, [1, 2, 3]);
        assert_eq!(merged, m(&[(2, "b1+b2"), (3, "c2")]));

        // `merge_env`: the keys of the second map first, then the keys that
        // only the first one has.
        let mut env = vec![];
        let merged = merge_env(&mut env, &m1, &m2, |env: &mut Vec<isize>, k, v1, v2| {
            env.push(*k);
            Some((v1.is_some(), v2.is_some()))
        });
        assert_eq!(env, [2, 3, 1]);
        assert_eq!(
            merged,
            [
                (1isize, (true, false)),
                (2isize, (true, true)),
                (3isize, (false, true))
            ]
            .into_iter()
            .collect::<OrdMap<isize, (bool, bool)>>()
        );

        // `union_env`: `combine` only sees the keys of both.
        let mut env = vec![];
        let merged = union_env(&mut env, &m1, &m2, |env: &mut Vec<isize>, k, v1, v2| {
            env.push(*k);
            Some(format!("{}{}", v1, v2))
        });
        assert_eq!(env, [2]);
        assert_eq!(merged, m(&[(1, "a1"), (2, "b1b2"), (3, "c2")]));
    }

    #[test]
    fn folds_and_maps() {
        let map = m(&[(2, "b"), (1, "a")]);
        let mut env = 0;
        let acc = fold_env(
            &mut env,
            |env: &mut isize, k, v, mut acc: Vec<String>| {
                *env += k;
                acc.push(v.clone());
                acc
            },
            &map,
            vec![],
        );
        assert_eq!((env, acc), (3, vec!["a".to_string(), "b".to_string()]));

        let mut env = vec![];
        let mapped = map_env(
            |env: &mut Vec<isize>, k, v: &String| {
                env.push(*k);
                v.len()
            },
            &mut env,
            &map,
        );
        assert_eq!(env, [1, 2]);
        assert_eq!(
            mapped,
            [(1isize, 1usize), (2isize, 1usize)]
                .into_iter()
                .collect::<OrdMap<isize, usize>>()
        );

        assert_eq!(ident_map(|v: &String| v.to_uppercase(), &map), m(&[(1, "A"), (2, "B")]));
        // Keys that become the same key: the last value, or `combine`.
        assert_eq!(ident_map_key(None, |_| 0, &map), m(&[(0, "b")]));
        let concat = |a: &String, b: &String| format!("{}{}", a, b);
        assert_eq!(ident_map_key(Some(&concat), |_| 0, &map), m(&[(0, "ab")]));
    }

    #[test]
    fn construction() {
        assert_eq!(
            of_list(vec![(1, "a".to_string()), (2, "b".to_string()), (1, "c".to_string())]),
            m(&[(1, "c"), (2, "b")])
        );
        assert_eq!(of_function(&[2, 1], |k| k.to_string()), m(&[(1, "1"), (2, "2")]));
        let opt: OrdMap<isize, Option<String>> = [(1isize, Some("a".to_string())), (2isize, None)]
            .into_iter()
            .collect();
        assert_eq!(filter_opt(&opt), m(&[(1, "a")]));
        let map = m(&[(1, "a")]);
        assert_eq!(add(None, 1, "b".to_string(), map.clone()), m(&[(1, "b")]));
        let concat = |old: &String, new: &String| format!("{}{}", old, new);
        assert_eq!(
            add(Some(&concat), 1, "b".to_string(), map.clone()),
            m(&[(1, "ab")])
        );
        assert_eq!(
            add(Some(&concat), 2, "b".to_string(), map),
            m(&[(1, "a"), (2, "b")])
        );
    }

    #[test]
    fn predicates() {
        let m1 = m(&[(1, "a"), (2, "b")]);
        let m2 = m(&[(2, "b"), (3, "c")]);
        let mut calls = vec![];
        assert!(!for_all2(
            |k, v1, v2| {
                calls.push(*k);
                v1 == v2
            },
            &m1,
            &m2
        ));
        // Every key, even after the first `false`.
        assert_eq!(calls, [1, 2, 3]);
        assert!(for_all2(|_, v1, v2| v1 == v2, &m1, &m1));
        assert_eq!(find_one_opt(&m1, |k| *k > 1), Some("b".to_string()));
        assert_eq!(find_one_opt(&m1, |k| *k > 2), None);
    }
}
