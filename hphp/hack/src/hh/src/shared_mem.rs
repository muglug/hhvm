// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Shared_mem` (`heap/shared_mem.ml`): its configuration record only. See
//! `hh/PORTING.md`.
//!
//! The Rust server has no shared memory (one process and threads: the design
//! of the server layer drops `heap/`). `Server_config` still computes this
//! record from `.hhconfig` as OCaml does, because that is observable: a
//! malformed `sharedmem_*` value fails the load, and a changed one makes the
//! new config incompatible with the old (`Server_config.is_compatible`).

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
            global_config::shm_dir.clone(),
            global_config::tmp_dir.clone(),
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
                global_config::shm_dir.clone(),
                global_config::tmp_dir.clone()
            ]
        );
        assert_eq!(empty_config().shm_cache_size, -1);
        assert!(empty_config().shm_dirs.is_empty());
    }
}
