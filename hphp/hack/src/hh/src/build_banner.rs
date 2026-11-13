// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `version/build_banner/build_banner.ml`. See `hh/PORTING.md`.
//!
//! `external get_build_banner` (`build_banner_stubs.c`) is `Some` of
//! `HH_BUILD_BANNER "-" HHVM_VERSION_C_STRING_LITERALS` when the build defines
//! `HH_BUILD_BANNER`, `None` otherwise. The build script (`hh/build.rs`)
//! passes the whole string as `HH_BUILD_BANNER` when it can compute it, as
//! `version/build_banner/dune` did.

use std::sync::LazyLock;

/// `external get_build_banner : unit -> string option = "hh_get_build_banner"`
fn get_build_banner() -> Option<String> {
    option_env!("HH_BUILD_BANNER").map(|banner| banner.to_string())
}

static BANNER: LazyLock<Option<String>> = LazyLock::new(get_build_banner);

pub fn banner() -> Option<String> {
    BANNER.clone()
}
