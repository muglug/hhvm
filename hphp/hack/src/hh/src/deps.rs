// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Deps` (`typing/env/deps.ml`). See `hh/PORTING.md`.
//!
//! The module is ported inside `crate::typing_env`, as `typing_env::deps`
//! (it is part of the port of the environment); this re-exports it, so that
//! `Deps.make_depend_on_class` is `crate::deps::make_depend_on_class`.

pub use crate::typing_env::deps::*;
