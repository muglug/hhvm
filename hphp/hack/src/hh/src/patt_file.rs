// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `custom_error/patt_file.ml`. See `hh/PORTING.md`.
//!
//! The types are `oxidized::patt_file`'s, re-exported: `t` is [`T`]
//! (`PattFile`) and `file_path` is [`FilePath`] (`Slash_opt` is `SlashOpt`).
//! (`[@@deriving compare, eq, sexp, show]` is their `Ord`, `Eq` and `Debug`.)
//!
//! The operators `( </> )` and `( </?> )` cannot be named in Rust: they are
//! [`slash`] and [`slash_opt`], after the constructors they build.

pub use oxidized::patt_file::*;

use crate::patt_string;

/// `Patt_file.t`
pub type T = PattFile;

pub const DOT: FilePath = FilePath::Dot;

/// `prefix </> segment`
pub fn slash(prefix: FilePath, segment: patt_string::T) -> FilePath {
    FilePath::Slash {
        prefix: Box::new(prefix),
        segment,
    }
}

/// `prefix </?> segment`
pub fn slash_opt(prefix: FilePath, segment: patt_string::T) -> FilePath {
    FilePath::SlashOpt {
        prefix: Box::new(prefix),
        segment,
    }
}
