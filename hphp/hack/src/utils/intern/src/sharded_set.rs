/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::fmt;
use std::hash::BuildHasher;
use std::hash::Hash;

use hashbrown::HashTable;
use parking_lot::RwLock;
use parking_lot::RwLockWriteGuard;

const SHARD_SHIFT: usize = 8;
const SHARDS: usize = 1 << SHARD_SHIFT;

pub struct ShardedSet<T, S = RandomState> {
    build_hasher: S,
    shards: [RwLock<HashTable<T>>; SHARDS],
}

impl<T, S> fmt::Debug for ShardedSet<T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ShardedSet")
    }
}

impl<T, S: BuildHasher + Default> Default for ShardedSet<T, S> {
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<T, S: BuildHasher> ShardedSet<T, S> {
    pub fn with_hasher(h: S) -> Self {
        Self {
            build_hasher: h,
            shards: std::array::from_fn(|_| Default::default()),
        }
    }
}

pub struct InsertLock<'a, T, S = RandomState> {
    build_hasher: &'a S,
    hash: u64,
    shard: RwLockWriteGuard<'a, HashTable<T>>,
}

impl<'a, T, S> fmt::Debug for InsertLock<'a, T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "InsertLock(hash: {:x})", self.hash)
    }
}

impl<T: Eq + Hash, S: BuildHasher> ShardedSet<T, S> {
    /// Return the hash, the shard index corresponding to the hash.  Since
    /// hashbrown uses the upper 7 bits for disambiguation and the lower bits
    /// for bucket indexing, we take the bits just above the top 7.
    #[inline(always)]
    fn hash_and_shard<Q>(&self, q: &Q) -> (u64, &RwLock<HashTable<T>>)
    where
        T: Borrow<Q>,
        Q: ?Sized + Hash,
    {
        let hash = self.build_hasher.hash_one(q);
        (
            hash,
            &self.shards[(hash >> (64 - 7 - SHARD_SHIFT)) as usize & (SHARDS - 1)],
        )
    }

    /// Clone out the entry corresponding to `q` if it exists, otherwise return
    /// `Err(InsertLock)` so that it can subsequently be inserted.
    pub fn get_or_insert_lock<'a, Q>(&'a self, q: &Q) -> Result<T, InsertLock<'a, T, S>>
    where
        T: Borrow<Q> + Clone,
        Q: ?Sized + Hash + Eq,
    {
        let (hash, shard) = self.hash_and_shard(q);
        // Most lookups find an entry that is already there, and the same
        // entries (common names, the path of the file being parsed) are
        // looked up by every thread at once: look under a shared lock first,
        // so that those lookups do not exclude one another, and take the
        // write lock only to insert.
        if let Some(t) = shard.read().find(hash, |other| q == other.borrow()) {
            return Ok(t.clone());
        }
        let shard = shard.write();
        // Check again: another thread may have inserted it between the two
        // locks. We don't use an upgradable read lock because those are
        // exclusive from one another just like write locks.
        if let Some(t) = shard.find(hash, |other| q == other.borrow()) {
            return Ok(t.clone());
        }
        Err(InsertLock {
            build_hasher: &self.build_hasher,
            hash,
            shard,
        })
    }

    /// Clone out the entry corresponding to `q` if it exists.
    pub fn get<Q>(&self, q: &Q) -> Option<T>
    where
        T: Borrow<Q> + Clone,
        Q: ?Sized + Hash + Eq,
    {
        let (hash, shard) = self.hash_and_shard(q);
        shard
            .read()
            .find(hash, |other| q == other.borrow())
            .cloned()
    }

    /// Unconditionally insert `t` without checking if it's in the set.
    pub fn unchecked_insert(&self, t: T) {
        let build_hasher = &self.build_hasher;
        let (hash, shard) = self.hash_and_shard(&t);
        shard
            .write()
            .insert_unique(hash, t, |v| build_hasher.hash_one(v));
    }
}

impl<T: Sized + Hash, S: BuildHasher> InsertLock<'_, T, S> {
    /// Insert the given value into the set.  This value must borrow-match the
    /// original value from get_or_insert_lock.
    pub fn insert<Q: Into<T>>(&mut self, q: Q) {
        let build_hasher = self.build_hasher;
        self.shard
            .insert_unique(self.hash, q.into(), |v| build_hasher.hash_one(v));
    }
}
