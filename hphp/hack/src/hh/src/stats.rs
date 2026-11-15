// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/stats.ml`. See `hh/PORTING.md`.
//!
//! The type is the result of `Server_command_types.STATS`, so it is
//! `serde`. The global `stats` is a `Mutex`.
//!
//! `Gc.stat` (OCaml's standard library) is [`GcStat`], with the fields of
//! OCaml 5's record. A Rust process has no OCaml heap and no shared heap:
//! `Gc.quick_stat ()` is all zeros here, and nothing sets the sizes of the
//! shared heap (`init_parsing_heap_size`, `init_heap_size`,
//! `max_heap_size`, which the OCaml server takes from `SharedMem`), so
//! `hh_client --stats` prints the OCaml's keys with zeros.
//!
//! Not all stats are worth logging for every user. Things like the initial heap
//! size are pretty deterministic if you know the input (i.e. the files being
//! checked). In fact, it's *only* useful information if you know the input.
//! This file is for storing these types of stats: Things that would be useful
//! for a benchmark script to know, so it can say "for these inputs, under these
//! conditions, here's how hh_server behaves".

use std::sync::Mutex;

use serde::Deserialize;
use serde::Serialize;

use crate::yojson::safe as yojson;

/// `Gc.stat`
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct GcStat {
    pub minor_words: f64,
    pub promoted_words: f64,
    pub major_words: f64,
    pub minor_collections: isize,
    pub major_collections: isize,
    pub heap_words: isize,
    pub heap_chunks: isize,
    pub live_words: isize,
    pub live_blocks: isize,
    pub free_words: isize,
    pub free_blocks: isize,
    pub largest_free: isize,
    pub fragments: isize,
    pub compactions: isize,
    pub top_heap_words: isize,
    pub stack_size: isize,
    pub forced_major_collections: isize,
}

/// `Stats.t` (its `mutable` fields are those that `update_max_heap_size`
/// and the server's init change in the global `stats`).
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct T {
    pub init_parsing_heap_size: isize,
    pub init_heap_size: isize,
    pub max_heap_size: isize,
    pub gc_stat: GcStat,
}

impl GcStat {
    /// `Gc.quick_stat ()`: there is no OCaml heap (see the module's
    /// documentation).
    fn quick_stat() -> GcStat {
        GcStat {
            minor_words: 0.,
            promoted_words: 0.,
            major_words: 0.,
            minor_collections: 0,
            major_collections: 0,
            heap_words: 0,
            heap_chunks: 0,
            live_words: 0,
            live_blocks: 0,
            free_words: 0,
            free_blocks: 0,
            largest_free: 0,
            fragments: 0,
            compactions: 0,
            top_heap_words: 0,
            stack_size: 0,
            forced_major_collections: 0,
        }
    }
}

/// `stats`: the global record (its `gc_stat` is never read: `get_stats`
/// takes a fresh one).
static STATS: Mutex<Option<T>> = Mutex::new(None);

fn with_stats<A>(f: impl FnOnce(&mut T) -> A) -> A {
    let mut stats = STATS.lock().unwrap_or_else(|e| e.into_inner());
    let stats = stats.get_or_insert_with(|| T {
        init_parsing_heap_size: 0,
        init_heap_size: 0,
        max_heap_size: 0,
        gc_stat: GcStat::quick_stat(),
    });
    f(stats)
}

/// `get_stats ()`
pub fn get_stats() -> T {
    with_stats(|stats| T {
        gc_stat: GcStat::quick_stat(),
        ..*stats
    })
}

/// `update_max_heap_size x`
pub fn update_max_heap_size(x: isize) {
    with_stats(|stats| stats.max_heap_size = std::cmp::max(stats.max_heap_size, x))
}

/// `to_json stats`
pub fn to_json(stats: &T) -> yojson::T {
    yojson::T::Assoc(vec![
        (
            "init_parsing_heap_size".to_string(),
            yojson::T::Int(stats.init_parsing_heap_size),
        ),
        (
            "init_shared_heap_size".to_string(),
            yojson::T::Int(stats.init_heap_size),
        ),
        (
            "max_shared_heap_size".to_string(),
            yojson::T::Int(stats.max_heap_size),
        ),
        (
            "master_heap_words".to_string(),
            yojson::T::Int(stats.gc_stat.heap_words),
        ),
        (
            "master_top_heap_words".to_string(),
            yojson::T::Int(stats.gc_stat.top_heap_words),
        ),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_json_has_the_ocaml_keys() {
        update_max_heap_size(7);
        update_max_heap_size(3);
        let stats = get_stats();
        assert_eq!(stats.max_heap_size, 7);
        assert_eq!(
            crate::yojson::safe::pretty_to_string(&to_json(&stats)),
            "{\n  \"init_parsing_heap_size\": 0,\n  \"init_shared_heap_size\": 0,\n  \"max_shared_heap_size\": 7,\n  \"master_heap_words\": 0,\n  \"master_top_heap_words\": 0\n}"
        );
    }
}
