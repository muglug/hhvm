// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<a3ddc1e34c80b273795762adb15c4469>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

#[derive(
    Clone,
    Debug,
    Deserialize,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct HhConfig {
    pub version: Option<String>,
    pub ignored_paths: Vec<String>,
    pub hash: String,
    pub opts: global_options::GlobalOptions,
    pub gc_minor_heap_size: usize,
    pub gc_space_overhead: usize,
    pub sharedmem_global_size: usize,
    pub sharedmem_hash_table_pow: usize,
    pub sharedmem_heap_size: usize,
    pub ide_fall_back_to_full_index: bool,
    pub hh_distc_should_disable_trace_store: bool,
    pub hh_distc_exponential_backoff_num_retries: usize,
    pub naming_table_compression_level: usize,
    pub naming_table_compression_threads: usize,
    pub eden_fetch_parallelism: usize,
    pub use_distc_crawl_dircache: bool,
}
