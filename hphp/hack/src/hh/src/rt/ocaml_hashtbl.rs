// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the part of `Base`'s `Hashtbl` (`Core.Hashtbl`) that the ported
//! modules use: a table of Base (`Core.Hashtbl.create (module String)`)
//! filled with `Hashtbl.add_multi` and read with `Hashtbl.iteri`, whose order of
//! iteration shows in the order the TAST checks report errors
//! (`Class_parent_check.duplicated_used_traits`,
//! `Duplicate_properties.handler`).
//!
//! `Base.Hashtbl` is an array of buckets: a key goes in bucket
//! `String.hash key land (length - 1)`, and each bucket is an AVL tree
//! ordered by `String.compare`. The array starts with one bucket
//! (`?size` defaults to 0, which is rounded up to 1) and doubles when a new
//! key makes the number of keys exceed its length, so a table of `n` keys has
//! `ceil_pow2 n` buckets. `iteri` goes through the buckets in order and
//! through each tree in increasing order of the keys. `String.hash` is
//! `Base_hash_string`: MurmurHash3's mix of the string (OCaml's
//! `caml_hash_mix_string` with seed 0) and its final mix, masked to 30 bits
//! (the value `Stdlib.Hashtbl.hash` gives a string).

use std::collections::BTreeMap;

/// `Base_hash_string`
pub fn hash_string(s: &[u8]) -> u32 {
    fn mix(h: u32, d: u32) -> u32 {
        let d = d.wrapping_mul(0xcc9e2d51);
        let d = d.rotate_left(15);
        let d = d.wrapping_mul(0x1b873593);
        let h = h ^ d;
        let h = h.rotate_left(13);
        h.wrapping_mul(5).wrapping_add(0xe6546b64)
    }
    // `caml_hash_mix_string`
    let mut h: u32 = 0;
    let len = s.len();
    let mut i = 0;
    while i + 4 <= len {
        let w = u32::from_le_bytes([s[i], s[i + 1], s[i + 2], s[i + 3]]);
        h = mix(h, w);
        i += 4;
    }
    let mut w: u32 = 0;
    let rest = len & 3;
    if rest == 3 {
        w = (s[i + 2] as u32) << 16;
    }
    if rest >= 2 {
        w |= (s[i + 1] as u32) << 8;
    }
    if rest >= 1 {
        w |= s[i] as u32;
        h = mix(h, w);
    }
    h ^= len as u32;
    // `FINAL_MIX`
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h & 0x3FFF_FFFF
}

/// `(string, 'a list) Hashtbl.t`, filled by `add_multi`.
pub struct StringMultiTable<V> {
    /// The list of each key, head first.
    bindings: BTreeMap<String, Vec<V>>,
}

impl<V> StringMultiTable<V> {
    /// `Hashtbl.create (module String)`
    pub fn create() -> Self {
        StringMultiTable {
            bindings: BTreeMap::new(),
        }
    }

    /// `Hashtbl.add_multi t ~key ~data`: `data` goes at the head of the
    /// list of `key`.
    pub fn add_multi(&mut self, key: String, data: V) {
        self.bindings.entry(key).or_default().insert(0, data)
    }

    /// `Hashtbl.iteri t ~f:(fun ~key ~data -> ...)`, in Base's order.
    pub fn iteri(&self, mut f: impl FnMut(&str, &[V])) {
        let n = self.bindings.len();
        if n == 0 {
            return;
        }
        let buckets = n.next_power_of_two() as u32;
        let mut keys: Vec<(u32, &String)> = self
            .bindings
            .keys()
            .map(|k| (hash_string(k.as_bytes()) & (buckets - 1), k))
            .collect();
        // By bucket, then by key (`String.compare`, the order of the
        // `BTreeMap`); the sort is stable.
        keys.sort_by_key(|(slot, _)| *slot);
        for (_, k) in keys {
            f(k, &self.bindings[k])
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_string_is_ocaml_hash() {
        // `Hashtbl.hash s` in OCaml 5.1.1.
        assert_eq!(hash_string(b""), 0);
        assert_eq!(hash_string(b"a"), 721651713);
        assert_eq!(hash_string(b"abcd"), 65890154);
        assert_eq!(hash_string(b"\\T1"), 754484068);
        assert_eq!(hash_string(b"\\Foo\\Bar"), 558758832);
        assert_eq!(hash_string(b"prop"), 709159502);
        assert_eq!(hash_string(b"x"), 780510073);
    }

    #[test]
    fn iteration_order() {
        let mut t = StringMultiTable::create();
        for (k, v) in [("a", 1), ("x", 2), ("a", 3), ("prop", 4)] {
            t.add_multi(k.to_string(), v)
        }
        // Three keys: four buckets. "a" is in bucket 1, "x" in bucket 1,
        // "prop" in bucket 2.
        let mut seen = vec![];
        t.iteri(|k, d| seen.push((k.to_string(), d.to_vec())));
        assert_eq!(
            seen,
            vec![
                ("a".to_string(), vec![3, 1]),
                ("x".to_string(), vec![2]),
                ("prop".to_string(), vec![4]),
            ]
        );
    }
}
