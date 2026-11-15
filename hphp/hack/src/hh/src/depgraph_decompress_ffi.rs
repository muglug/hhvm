// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/depgraph_decompress_ffi.ml`, the open-source build's.

use crate::client_decompress_zhhdg::Failure;

/// `decompress ~compressed_dg_path` (the outer `Err` is the exception
/// it raises)
pub fn decompress(compressed_dg_path: &str) -> Result<Result<String, String>, Failure> {
    let _ = compressed_dg_path;
    Err(Failure("decompress not implemented".to_string()))
}
