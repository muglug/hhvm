// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/lfu_cache.ml`: a cache that, when it reaches twice its
//! capacity, keeps only its `capacity` most frequently used entries.
//!
//! Owned by **L0** (plan §7.3): the bounded caches of the `Local_memory`
//! provider backend (`crate::provider_backend`).
//!
//! The OCaml cache is heterogeneous (`'a Entry.key -> 'a Entry.value`, with
//! `Obj.magic`); here a cache has one key type and one value type, and a
//! cache of several kinds of values (`Decl_cache`) has an enum of them.
//!
//! Difference that nothing outside the process sees: among entries of the
//! same frequency, which ones a collection keeps depends on the iteration
//! order of the hash table (`Hashtbl.fold`), which is not the OCaml's.

use std::collections::BTreeMap;
use std::hash::Hash;

use crate::telemetry;

/// `size`
pub type Size = usize;

/// Whether two values are the same object (`phys_equal`): `add` keeps the
/// entry (and its frequency) when it is given the value it already has.
pub trait PhysEqual {
    fn phys_equal(&self, other: &Self) -> bool;
}

impl<T: ?Sized> PhysEqual for std::sync::Arc<T> {
    fn phys_equal(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(self, other)
    }
}

/// `entry`
struct Entry<V> {
    frequency: usize,
    value: V,
}

fn make_entry<V>(value: V) -> Entry<V> {
    Entry {
        frequency: 0,
        value,
    }
}

/// `Cache(Entry).t`
pub struct Cache<K, V> {
    capacity: Size,
    entries: hash::HashMap<K, Entry<V>>,
    can_collect: bool,
    num_added: usize,
    num_collected: usize,
    num_collections: usize,
}

impl<K, V> std::fmt::Debug for Cache<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Lfu_cache")
            .field("capacity", &self.capacity)
            .field("length", &self.entries.len())
            .finish()
    }
}

impl<K: Hash + Eq + Clone, V: Clone + PhysEqual> Cache<K, V> {
    /// `make ~max_size`
    pub fn make(max_size: Size) -> Self {
        Self {
            capacity: max_size,
            entries: hash::HashMap::default(),
            can_collect: true,
            num_added: 0,
            num_collected: 0,
            num_collections: 0,
        }
    }

    pub fn clear(&mut self) {
        self.entries.clear()
    }

    pub fn length(&self) -> usize {
        self.entries.len()
    }

    pub fn capacity(&self) -> Size {
        self.capacity
    }

    /// The collection function is called when we reach twice original
    /// capacity in size. When the collection is triggered, we only keep
    /// the most frequently used objects.
    /// So before collection: size = 2 * capacity
    /// After collection: size = capacity (with the most frequently
    /// used objects)
    fn collect(&mut self) {
        if !self.can_collect || self.entries.len() < 2 * self.capacity {
            return;
        }
        self.num_collections += 1;
        let prev_length = self.entries.len();
        // bucket sort (`RevIMap`: the highest frequency first)
        let mut sorted_by_freq: BTreeMap<std::cmp::Reverse<usize>, Vec<(K, V)>> = BTreeMap::new();
        for (key, Entry { frequency, value }) in self.entries.drain() {
            sorted_by_freq
                .entry(std::cmp::Reverse(frequency))
                .or_default()
                .push((key, value));
        }
        let mut count = 0;
        'done: for (_freq, values) in sorted_by_freq {
            for (key, value) in values {
                self.entries.insert(key, make_entry(value));
                count += 1;
                if count >= self.capacity {
                    break 'done;
                }
            }
        }
        self.num_collected += prev_length - self.entries.len();
    }

    /// `without_collections t ~f`. (The OCaml's `f` gets no argument and
    /// uses the cache through its handle; here `f` is given the cache.)
    pub fn without_collections<A>(&mut self, f: impl FnOnce(&mut Self) -> A) -> A {
        let prev = self.can_collect;
        self.can_collect = false;
        let res = f(self);
        self.can_collect = prev;
        res
    }

    /// Whether collections are allowed (see [`Cache::without_collections`]).
    pub fn set_can_collect(&mut self, can_collect: bool) -> bool {
        std::mem::replace(&mut self.can_collect, can_collect)
    }

    pub fn add(&mut self, key: K, value: V) {
        self.collect();
        match self.entries.get_mut(&key) {
            Some(entry) => {
                entry.frequency += 1;
                if entry.value.phys_equal(&value) {
                } else {
                    entry.value = value;
                }
            }
            None => {
                self.num_added += 1;
                self.entries.insert(key, make_entry(value));
            }
        }
    }

    /// `find t ~key` (does not count as a use).
    pub fn find(&self, key: &K) -> Option<V> {
        self.entries.get(key).map(|entry| entry.value.clone())
    }

    /// The `if_found` half of `find_or_add`: the value, counted as a use.
    pub fn find_and_count(&mut self, key: &K) -> Option<V> {
        match self.entries.get_mut(key) {
            Some(entry) => {
                entry.frequency += 1;
                Some(entry.value.clone())
            }
            None => None,
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.entries.keys()
    }

    pub fn remove(&mut self, key: &K) {
        self.entries.remove(key);
    }

    pub fn fold<A>(&self, init: A, mut f: impl FnMut(&K, &V, A) -> A) -> A {
        self.entries
            .iter()
            .fold(init, |acc, (key, entry)| f(key, &entry.value, acc))
    }

    pub fn get_telemetry(&self, key: &str, telemetry: telemetry::T) -> telemetry::T {
        let value = telemetry::create();
        let value = telemetry::int_("num_added", self.num_added as isize, value);
        let value = telemetry::int_("num_collected", self.num_collected as isize, value);
        let value = telemetry::int_("num_collections", self.num_collections as isize, value);
        let value = telemetry::int_("capacity", self.capacity as isize, value);
        let value = telemetry::int_("length", self.length() as isize, value);
        telemetry::object_(key, value, telemetry)
    }

    pub fn reset_telemetry(&mut self) {
        self.num_added = 0;
        self.num_collected = 0;
        self.num_collections = 0;
    }
}

/// `find_or_add t ~key ~default` on a cache behind a lock: the lock is not
/// held while `default` runs (it may look up and add other entries of the
/// same cache, as the OCaml's does).
pub fn find_or_add<K, V>(
    cache: &std::sync::Mutex<Cache<K, V>>,
    key: K,
    default: impl FnOnce() -> Option<V>,
) -> Option<V>
where
    K: Hash + Eq + Clone,
    V: Clone + PhysEqual,
{
    if let Some(value) = cache.lock().unwrap().find_and_count(&key) {
        return Some(value);
    }
    let value_opt = default();
    if let Some(value) = &value_opt {
        cache.lock().unwrap().add(key, value.clone());
    }
    value_opt
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    #[test]
    fn collects_at_twice_the_capacity_keeping_the_most_used() {
        let mut c: Cache<i32, Arc<i32>> = Cache::make(2);
        c.add(1, Arc::new(1));
        c.add(2, Arc::new(2));
        c.add(3, Arc::new(3));
        // 3 is the most used, then 1.
        for _ in 0..3 {
            c.find_and_count(&3);
        }
        c.find_and_count(&1);
        c.add(4, Arc::new(4));
        assert_eq!(c.length(), 4);
        // The next add collects first (4 >= 2 * 2): keeps 3 and 1.
        c.add(5, Arc::new(5));
        assert_eq!(c.length(), 3);
        assert!(c.find(&3).is_some() && c.find(&1).is_some() && c.find(&5).is_some());
        assert!(c.find(&2).is_none());
        let t = c.get_telemetry("k", telemetry::create());
        assert!(telemetry::to_string(None, &t).contains("\"num_collected\":2"), "{}", telemetry::to_string(None, &t));
        // Not while collections are off.
        c.without_collections(|c| {
            c.add(6, Arc::new(6));
            c.add(7, Arc::new(7));
        });
        assert_eq!(c.length(), 5);
        // The same value keeps the entry; another replaces it.
        let v = c.find(&3).unwrap();
        c.add(3, Arc::clone(&v));
        assert!(Arc::ptr_eq(&c.find(&3).unwrap(), &v));
        c.remove(&3);
        assert!(c.find(&3).is_none());
        let m = std::sync::Mutex::new(Cache::<i32, Arc<i32>>::make(10));
        assert_eq!(find_or_add(&m, 1, || None), None);
        assert_eq!(*find_or_add(&m, 1, || Some(Arc::new(9))).unwrap(), 9);
        assert_eq!(*find_or_add(&m, 1, || panic!()).unwrap(), 9);
    }
}
