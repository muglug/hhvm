// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `options/build_options.mli`, as far as the ported modules use it:
//! the values that `options/discover.ml` writes into
//! `build_options.generated.ml`, here from the environment of the build.

/// Where we look for system-wide configuration files: the `sysconfdir` of the
/// build (`CMAKE_INSTALL_FULL_SYSCONFDIR`), `/etc` when the build does not
/// say.
///
/// Possible values include:
/// - "/etc": most linux systems
/// - "/usr/local/etc": MacOS homebrew
pub fn system_config_path() -> &'static str {
    option_env!("CMAKE_INSTALL_FULL_SYSCONFDIR").unwrap_or("/etc")
}
