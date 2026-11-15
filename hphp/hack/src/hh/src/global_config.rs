// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `globals/global_config.ml`: the values that the ported
//! modules need so far (`scuba_table_name` is not here). See
//! `hh/PORTING.md`.
//!
//! The values are computed when they are first read; OCaml computes them
//! when the program starts. They read the environment, which nothing changes
//! in between.

use std::sync::LazyLock;

pub const PROGRAM_NAME: &str = "hh_server";

/// `Gc.control`, the parameters of OCaml's garbage collector. The Rust
/// programs have no OCaml GC: only the two parameters that `.hhconfig` sets
/// (`gc_minor_heap_size` and `gc_space_overhead`, which
/// `Server_config.make_gc_control` reads) are kept, so that a config fails on
/// a malformed value and compares with another as in OCaml.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GcControl {
    /// In words.
    pub minor_heap_size: isize,
    pub space_overhead: isize,
}

/// Configures only the workers. Workers can have more relaxed GC configs as
/// they are short-lived processes
///
/// `Gc.get ()`: OCaml 5.2's defaults (256k words, 120). `OCAMLRUNPARAM`,
/// which can change them, is not read.
pub fn gc_control() -> GcControl {
    GcControl {
        minor_heap_size: 256 * 1024,
        space_overhead: 120,
    }
}

/// Where to write temp files
pub static TMP_DIR: LazyLock<String> = LazyLock::new(crate::tmp::hh_server_tmp_dir);

pub static SHM_DIR: LazyLock<String> =
    LazyLock::new(|| std::env::var("HH_SHMDIR").unwrap_or_else(|_| "/dev/shm".to_string()));
