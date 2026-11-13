// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_logger.ml` (`stubs/logging/typing_logger.ml`, the version
//! of the open-source build, which logs nothing). See `hh/PORTING.md`.

/// `module InferenceCnstr`
pub mod inference_cnstr {
    pub fn log(_p_as_string: &str, _pos: &str, _size: isize, _n_disj: isize, _n_conj: isize) {}
}

pub fn flush_buffers() {}
