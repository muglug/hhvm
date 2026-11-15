// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `heap/shared_mem.ml`: the configuration record, the typed heaps
//! over the shared heap of `crate::hh_shared` (`Heap`, `HeapWithLocalCache`
//! with its `FreqCache`, the old keys of `oldify`), the local caches and
//! `invalidate_local_caches`, `GC.collect` and `SMTelemetry`. See
//! `hh/PORTING.md`.
//!
//! The values are serialized with serde (bincode, with `intern::WithIntern`
//! so that the interned names of a value are written once and interned again
//! by the process that reads it) where the OCaml uses `Marshal`.
//!
//! A local cache is per thread here (`thread_local!`), the OCaml's per
//! process: a worker clone runs its job on one thread, and the master's
//! lookups are made by its world thread.

use crate::global_config;

/// Configuration object that initializes shared memory.
#[derive(Clone, Debug, PartialEq)]
pub struct Config {
    pub global_size: isize,
    pub heap_size: isize,
    pub hash_table_pow: isize,
    pub shm_use_sharded_hashtbl: bool,
    pub shm_cache_size: isize,
    pub shm_dirs: Vec<String>,
    pub shm_min_avail: isize,
    pub log_level: isize,
    pub sample_rate: f64,
    /// 0 - lz4, others -- compression level for zstd
    pub compression: isize,
}

/// Default configuration object
pub fn default_config() -> Config {
    let gig = 1024 * 1024 * 1024;
    Config {
        global_size: gig,
        heap_size: 20 * gig,
        hash_table_pow: 18,
        // 1 << 18
        shm_dirs: vec![
            global_config::SHM_DIR.clone(),
            global_config::TMP_DIR.clone(),
        ],
        shm_use_sharded_hashtbl: false,
        // eviction disabled
        shm_cache_size: -1,
        shm_min_avail: gig / 2,
        // Half a gig by default
        log_level: 0,
        sample_rate: 0.0,
        compression: 0,
    }
}

/// Empty configuration object.
///
/// There are places where we don't expect to write to shared memory, and doing
/// so would be a memory leak. But since shared memory is global, it's very easy
/// to accidentally call a function that will attempt such write. This config
/// initializes shared memory with zero sizes. As such, attempting to write to
/// shared memory that was initialized with this config, will make the program
/// fail immediately.
pub fn empty_config() -> Config {
    Config {
        global_size: 0,
        heap_size: 0,
        hash_table_pow: 0,
        shm_dirs: vec![],
        shm_use_sharded_hashtbl: false,
        shm_cache_size: -1,
        shm_min_avail: 0,
        log_level: 0,
        sample_rate: 0.0,
        compression: 0,
    }
}


// ~~ Heaps ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Shared_mem.Value`: what a heap stores, and its `description` (what the
/// telemetry and the MEM census name the heap by).
pub trait Value: serde::Serialize + serde::de::DeserializeOwned + Send + Sync + 'static {
    const DESCRIPTION: &'static str;
}

/// `KeyHasher`: the hashes of a heap's keys (`Prefix.make_key prefix key`
/// digested, see `hh_shared::hash_key`). `prefix` is the heap's (made of its
/// description and the namespace of its stores: two sets of stores of one
/// process, as the tests make, never share keys); the old keys of `oldify`
/// are under `old_` + prefix, as the OCaml's.
#[derive(Clone, Debug)]
pub struct KeyHasher {
    prefix: Vec<u8>,
    old_prefix: Vec<u8>,
}

impl KeyHasher {
    pub fn new(description: &str, namespace: u64) -> Self {
        let prefix = format!("{description}:{namespace}:").into_bytes();
        let mut old_prefix = b"old_".to_vec();
        old_prefix.extend_from_slice(&prefix);
        Self { prefix, old_prefix }
    }

    /// `hash`
    pub fn hash(&self, key: &[u8]) -> u64 {
        crate::hh_shared::hash_key(&self.prefix, key)
    }

    /// `hash_old`
    pub fn hash_old(&self, key: &[u8]) -> u64 {
        crate::hh_shared::hash_key(&self.old_prefix, key)
    }
}

/// Serializes a value as the heaps store it.
pub fn serialize<V: serde::Serialize>(v: &V) -> Vec<u8> {
    bincode::serde::encode_to_vec(intern::WithIntern(v), bincode::config::standard())
        .expect("Shared_mem: a value that cannot be serialized")
}

/// Deserializes what [`serialize`] wrote.
pub fn deserialize<V: serde::de::DeserializeOwned>(bytes: &[u8]) -> V {
    let (intern::WithIntern(v), _): (intern::WithIntern<V>, usize) =
        bincode::serde::decode_from_slice(bytes, bincode::config::standard())
            .expect("Shared_mem: a corrupt value");
    v
}

/// `Shared_mem.Heap (ImmediateBackend ...)`: a heap of the shared heap, without
/// a local cache. The keys are given as bytes (`Key.to_string`).
pub struct Heap<V> {
    hasher: KeyHasher,
    _v: std::marker::PhantomData<fn() -> V>,
}

impl<V: Value> Heap<V> {
    pub fn new(namespace: u64) -> Self {
        Self::new_named(V::DESCRIPTION, namespace)
    }

    /// A heap of values of `V` named `description` (several heaps can store
    /// one type: the blocked sets of `Naming_heap`).
    pub fn new_named(description: &str, namespace: u64) -> Self {
        Self {
            hasher: KeyHasher::new(description, namespace),
            _v: std::marker::PhantomData,
        }
    }

    pub fn hasher(&self) -> &KeyHasher {
        &self.hasher
    }

    /// `add`: the first value added for a key stays (`hh_add` does nothing
    /// when the key has a value).
    pub fn add(&self, key: &[u8], value: &V) {
        let hash = self.hasher.hash(key);
        self.add_hash(hash, value)
    }

    fn add_hash(&self, hash: u64, value: &V) {
        // (`hh_add` would not overwrite; checking first saves serializing.)
        if crate::hh_shared::mem_(hash) {
            return;
        }
        let bytes = serialize(value);
        let _ = crate::hh_shared::add(hash, &bytes, crate::hh_shared::Kind::Serialized);
    }

    /// `get`
    pub fn get(&self, key: &[u8]) -> Option<V> {
        crate::hh_shared::get(self.hasher.hash(key), |bytes, _| deserialize(bytes))
    }

    /// `get_old`
    pub fn get_old(&self, key: &[u8]) -> Option<V> {
        crate::hh_shared::get(self.hasher.hash_old(key), |bytes, _| deserialize(bytes))
    }

    /// `mem`
    pub fn mem(&self, key: &[u8]) -> bool {
        crate::hh_shared::mem_(self.hasher.hash(key))
    }

    /// `mem_old`
    pub fn mem_old(&self, key: &[u8]) -> bool {
        crate::hh_shared::mem_(self.hasher.hash_old(key))
    }

    /// `remove` (master only): nothing if the key has no value.
    pub fn remove(&self, key: &[u8]) {
        crate::hh_shared::remove_if_present(self.hasher.hash(key));
    }

    /// `remove_old`
    pub fn remove_old(&self, key: &[u8]) {
        crate::hh_shared::remove_if_present(self.hasher.hash_old(key));
    }

    /// `oldify`: the value moves to the old key (if the key has one).
    pub fn oldify(&self, key: &[u8]) {
        let hash = self.hasher.hash(key);
        if crate::hh_shared::mem_(hash) {
            crate::hh_shared::move_(hash, self.hasher.hash_old(key))
        }
    }

    /// `oldify_batch` on one key: `oldify` if the key has a value, else
    /// `remove_old` ("semantics of `oldify x` and `oldify_batch {x}` are
    /// different for some mysterious reason").
    pub fn oldify_batch_key(&self, key: &[u8]) {
        if self.mem(key) {
            // (An old value of the key, if any, goes first: `hh_move`
            // needs a free destination.)
            self.remove_old(key);
            self.oldify(key)
        } else {
            self.remove_old(key)
        }
    }

    /// `revive`: the old value comes back (if there is one).
    pub fn revive(&self, key: &[u8]) {
        if self.mem_old(key) {
            self.remove(key);
            crate::hh_shared::move_(self.hasher.hash_old(key), self.hasher.hash(key))
        }
    }

    /// `revive_batch` on one key: `revive`, else `remove`.
    pub fn revive_batch_key(&self, key: &[u8]) {
        if self.mem_old(key) {
            self.revive(key)
        } else {
            self.remove(key)
        }
    }

    /// The sizes of the key's entry (stored, marshalled, slot): the MEM census.
    pub fn census_entry(&self, key: &[u8]) -> Option<(u64, u64, u64)> {
        crate::hh_shared::census_entry(self.hasher.hash(key))
    }
}

/// `Shared_mem.Capacity` of the decl heaps (`Decl_heap.Capacity`,
/// `Shallow_classes_heap.Capacity`, `Decl_provider.Cache`).
pub const CAPACITY: usize = 1000;

/// `FreqCache`: an LFU cache of `capacity` entries (it holds up to twice
/// that, then keeps the `capacity` most used, whose counts start again).
pub struct FreqCache<V> {
    capacity: usize,
    cache: hash::HashMap<u64, (u64, std::sync::Arc<V>)>,
}

impl<V> FreqCache<V> {
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            cache: hash::HashMap::with_capacity_and_hasher(2 * capacity, Default::default()),
        }
    }

    pub fn clear(&mut self) {
        self.cache.clear()
    }

    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// The collection function is called when we reach twice original
    /// capacity in size. When the collection is triggered, we only keep
    /// the most frequently used objects.
    /// So before collection: size = 2 * capacity
    /// After collection: size = capacity (with the most frequently
    /// used objects)
    fn collect(&mut self) {
        if self.cache.len() < 2 * self.capacity {
            return;
        }
        let mut l: Vec<(u64, u64, std::sync::Arc<V>)> =
            self.cache.drain().map(|(k, (freq, v))| (k, freq, v)).collect();
        l.sort_by(|(_, x, _), (_, y, _)| y.cmp(x));
        for (k, _freq, v) in l.into_iter().take(self.capacity) {
            self.cache.insert(k, (0, v));
        }
    }

    pub fn add(&mut self, x: u64, y: std::sync::Arc<V>) {
        self.collect();
        match self.cache.get_mut(&x) {
            Some((freq, y_)) => {
                *freq += 1;
                if !std::sync::Arc::ptr_eq(y_, &y) {
                    *y_ = y;
                }
            }
            None => {
                self.cache.insert(x, (0, y));
            }
        }
    }

    pub fn get(&mut self, x: u64) -> Option<std::sync::Arc<V>> {
        match self.cache.get_mut(&x) {
            None => None,
            Some((freq, value)) => {
                *freq += 1;
                Some(std::sync::Arc::clone(value))
            }
        }
    }

    pub fn remove(&mut self, x: u64) {
        self.cache.remove(&x);
    }
}

/// A local cache of the registry of a thread, whatever its value type.
trait LocalCache {
    fn len(&self) -> usize;
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any;
}

impl<V: 'static> LocalCache for FreqCache<V> {
    fn len(&self) -> usize {
        FreqCache::len(self)
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

thread_local! {
    /// The local caches of this thread, by the description of their heap
    /// (the OCaml registers each with `invalidate_local_caches`).
    static LOCAL_CACHES: std::cell::RefCell<hash::HashMap<&'static str, Box<dyn LocalCache>>> =
        Default::default();
}

/// `f` on this thread's local cache of the heap of `V`.
fn with_cache<V: Value, T>(f: impl FnOnce(&mut FreqCache<V>) -> T) -> T {
    LOCAL_CACHES.with_borrow_mut(|caches| {
        let cache = caches
            .entry(V::DESCRIPTION)
            .or_insert_with(|| Box::new(FreqCache::<V>::new(CAPACITY)));
        f(cache.as_any_mut().downcast_mut::<FreqCache<V>>().unwrap())
    })
}

/// `Shared_mem.invalidate_local_caches`: the local caches of this thread (the
/// OCaml's of this process).
pub fn invalidate_local_caches() {
    LOCAL_CACHES.with_borrow_mut(|caches| caches.clear())
}

/// The entries of this thread's local caches, by heap (the MEM census).
pub fn local_cache_counts() -> Vec<(&'static str, usize)> {
    LOCAL_CACHES.with_borrow(|caches| {
        let mut v: Vec<(&'static str, usize)> = caches.iter().map(|(k, c)| (*k, c.len())).collect();
        v.sort();
        v
    })
}

/// `Shared_mem.HeapWithLocalCache`: a [`Heap`] behind this thread's
/// [`FreqCache`] of [`CAPACITY`] values. The values are handed out as `Arc`s
/// (the cache's).
pub struct HeapWithLocalCache<V> {
    direct: Heap<V>,
}

impl<V: Value> HeapWithLocalCache<V> {
    pub fn new(namespace: u64) -> Self {
        Self { direct: Heap::new(namespace) }
    }

    /// See [`Heap::new_named`].
    pub fn new_named(description: &str, namespace: u64) -> Self {
        Self {
            direct: Heap::new_named(description, namespace),
        }
    }

    pub fn direct(&self) -> &Heap<V> {
        &self.direct
    }

    /// `add`: to the heap and the local cache.
    pub fn add(&self, key: &[u8], value: std::sync::Arc<V>) {
        let hash = self.direct.hasher.hash(key);
        self.direct.add_hash(hash, &value);
        with_cache::<V, _>(|c| c.add(hash, value))
    }

    /// `write_around`: to the heap only.
    pub fn write_around(&self, key: &[u8], value: &V) {
        self.direct.add(key, value)
    }

    /// `get`: the local cache, else the heap (then cached).
    pub fn get(&self, key: &[u8]) -> Option<std::sync::Arc<V>> {
        let hash = self.direct.hasher.hash(key);
        if let Some(v) = with_cache::<V, _>(|c| c.get(hash)) {
            return Some(v);
        }
        let v = std::sync::Arc::new(crate::hh_shared::get(hash, |bytes, _| deserialize::<V>(bytes))?);
        with_cache::<V, _>(|c| c.add(hash, std::sync::Arc::clone(&v)));
        Some(v)
    }

    /// `get_no_cache`
    pub fn get_no_cache(&self, key: &[u8]) -> Option<V> {
        self.direct.get(key)
    }

    /// `get_old`: not cached ("we don't cache old objects, they are not
    /// accessed often enough").
    pub fn get_old(&self, key: &[u8]) -> Option<V> {
        self.direct.get_old(key)
    }

    /// `mem` (through the cache, as the OCaml's `mem x = match get x`).
    pub fn mem(&self, key: &[u8]) -> bool {
        let hash = self.direct.hasher.hash(key);
        with_cache::<V, _>(|c| c.cache.contains_key(&hash)) || crate::hh_shared::mem_(hash)
    }

    pub fn mem_old(&self, key: &[u8]) -> bool {
        self.direct.mem_old(key)
    }

    /// `remove`: from the heap and this thread's cache.
    pub fn remove(&self, key: &[u8]) {
        self.direct.remove(key);
        let hash = self.direct.hasher.hash(key);
        with_cache::<V, _>(|c| c.remove(hash))
    }

    pub fn remove_old(&self, key: &[u8]) {
        self.direct.remove_old(key)
    }

    /// `oldify_batch` on one key, and the cache entry goes.
    pub fn oldify_batch_key(&self, key: &[u8]) {
        self.direct.oldify_batch_key(key);
        let hash = self.direct.hasher.hash(key);
        with_cache::<V, _>(|c| c.remove(hash))
    }

    /// `revive_batch` on one key, and the cache entry goes.
    pub fn revive_batch_key(&self, key: &[u8]) {
        self.direct.revive_batch_key(key);
        let hash = self.direct.hasher.hash(key);
        with_cache::<V, _>(|c| c.remove(hash))
    }
}

/// `Shared_mem.SMTelemetry`
pub mod sm_telemetry {
    /// `heap_size`: the bytes allocated in the heap (freed ones included
    /// until a collection).
    pub fn heap_size() -> u64 {
        crate::hh_shared::used_heap_size()
    }

    /// `wasted_heap_size`
    pub fn wasted_heap_size() -> u64 {
        crate::hh_shared::wasted_heap_size()
    }

    /// `hash_used_slots`
    pub fn hash_used_slots() -> (u64, u64) {
        crate::hh_shared::hash_used_slots()
    }

    /// `hash_slots`
    pub fn hash_slots() -> u64 {
        crate::hh_shared::hash_slots()
    }

    /// `table_stats`
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct TableStats {
        pub nonempty_slots: u64,
        pub used_slots: u64,
        pub slots: u64,
    }

    /// `hash_stats ()`. (`hh_hash_used_slots` of the C gives
    /// `(hcounter_filled, hcounter)`, which the OCaml reads as
    /// `(used_slots, nonempty_slots)`; [`hash_used_slots`] gives them the
    /// other way round.)
    pub fn hash_stats() -> TableStats {
        let (hcounter, hcounter_filled) = hash_used_slots();
        TableStats {
            nonempty_slots: hcounter,
            used_slots: hcounter_filled,
            slots: hash_slots(),
        }
    }
}

/// `Shared_mem.GC`
pub mod gc {
    /// The effort of a collection.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Effort {
        Gentle,
        Aggressive,
        AlwaysTest,
    }

    /// `should_collect`
    pub fn should_collect(effort: Effort) -> bool {
        let overhead = match effort {
            Effort::AlwaysTest => 1.0,
            Effort::Aggressive => 1.2,
            Effort::Gentle => 2.0,
        };
        let used = super::sm_telemetry::heap_size();
        let wasted = super::sm_telemetry::wasted_heap_size();
        let reachable = used - wasted;
        used >= (reachable as f64 * overhead) as u64
    }

    /// `collect`
    pub fn collect(effort: Effort) {
        if !crate::hh_shared::is_initialized() {
            return;
        }
        let old_size = super::sm_telemetry::heap_size();
        let start_t = std::time::Instant::now();
        if should_collect(effort) {
            crate::hh_shared::collect()
        }
        let new_size = super::sm_telemetry::heap_size();
        if old_size != new_size {
            crate::hh_logger::log(&format!(
                "Sharedmem GC: {} bytes before; {} bytes after; in {:.6} seconds",
                old_size,
                new_size,
                start_t.elapsed().as_secs_f64()
            ));
        }
    }
}

/// serde of an `im::OrdSet` (the `im` crate is built without its serde
/// feature) as a sequence, for the inputs and outputs of the jobs.
pub mod serde_ord_set {
    use serde::Deserialize;
    use serde::Serialize;

    pub fn serialize<T: Serialize + Ord + Clone, S: serde::Serializer>(
        set: &im::OrdSet<T>,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        let v: Vec<&T> = set.iter().collect();
        v.serialize(s)
    }

    pub fn deserialize<'de, T: Deserialize<'de> + Ord + Clone, D: serde::Deserializer<'de>>(
        d: D,
    ) -> Result<im::OrdSet<T>, D::Error> {
        let v: Vec<T> = Vec::deserialize(d)?;
        Ok(v.into_iter().collect())
    }
}

/// serde of an `im::OrdMap`, as a sequence of pairs.
pub mod serde_ord_map {
    use serde::Deserialize;
    use serde::Serialize;

    pub fn serialize<K: Serialize + Ord + Clone, V: Serialize + Clone, S: serde::Serializer>(
        map: &im::OrdMap<K, V>,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        let v: Vec<(&K, &V)> = map.iter().collect();
        v.serialize(s)
    }

    pub fn deserialize<'de, K: Deserialize<'de> + Ord + Clone, V: Deserialize<'de> + Clone, D: serde::Deserializer<'de>>(
        d: D,
    ) -> Result<im::OrdMap<K, V>, D::Error> {
        let v: Vec<(K, V)> = Vec::deserialize(d)?;
        Ok(v.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn configs() {
        let c = default_config();
        assert_eq!(c.global_size, 1 << 30);
        assert_eq!(c.heap_size, 20 << 30);
        assert_eq!(c.shm_min_avail, 1 << 29);
        assert_eq!(
            c.shm_dirs,
            vec![
                global_config::SHM_DIR.clone(),
                global_config::TMP_DIR.clone()
            ]
        );
        assert_eq!(empty_config().shm_cache_size, -1);
        assert!(empty_config().shm_dirs.is_empty());
    }
}
