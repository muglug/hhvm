// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/random_id.ml`. See `hh/PORTING.md`.
//!
//! OCaml's `Random.bits ()` (30 random bits from the self-initialised
//! generator) is taken from the standard library's randomly seeded hasher:
//! the ids are as random, but not the same sequence as OCaml's generator
//! would give.

use std::hash::BuildHasher;
use std::hash::Hasher;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;

/// Do not use / in random ids as they appear in filenames.
pub const ALPHANUMERIC_ALPHABET: &str =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";

/// `Random.bits ()`: 30 random bits.
fn random_bits() -> usize {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let mut hasher = std::collections::hash_map::RandomState::new().build_hasher();
    hasher.write_u64(COUNTER.fetch_add(1, Ordering::Relaxed));
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos() as u64);
    hasher.write_u64(now);
    (hasher.finish() & 0x3FFF_FFFF) as usize
}

pub fn short_string_with_alphabet(alphabet: &str) -> String {
    let alphabet = alphabet.as_bytes();
    let mut r = (random_bits() << 30) | random_bits();
    let mut cs: Vec<u8> = vec![];
    while r > 0 {
        let c = alphabet[r % alphabet.len()];
        cs.insert(0, c);
        r >>= 6;
    }
    String::from_utf8_lossy(&cs).into_owned()
}

/// Generates a short string with alphanumeric alphabet
pub fn short_string() -> String {
    short_string_with_alphabet(ALPHANUMERIC_ALPHABET)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ids_are_short_and_alphanumeric() {
        for _ in 0..100 {
            let id = short_string();
            assert!(id.len() <= 10, "{}", id);
            assert!(id.bytes().all(|c| c.is_ascii_alphanumeric()), "{}", id);
        }
        assert_ne!(short_string(), short_string());
    }
}
