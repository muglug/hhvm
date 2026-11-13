// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `custom_error_config.ml`. See `hh/PORTING.md`.
//!
//! The type is `oxidized::custom_error_config`'s, re-exported (`[@@deriving
//! eq, show]` is its `Eq` and `Debug`).

#![allow(non_upper_case_globals)]

pub use oxidized::custom_error_config::*;

/// `Custom_error_config.t`
pub type T = CustomErrorConfig;

pub const empty: T = T {
    valid: Vec::new(),
    invalid: Vec::new(),
};

pub fn is_valid(t: &T) -> bool {
    match t {
        T { invalid, .. } if invalid.is_empty() => true,
        _ => false,
    }
}

/// The argument of [`initialize`], ``[ `Absolute of string | `Relative of
/// Relative_path.t ]``.
#[derive(Clone, Debug)]
pub enum Path {
    Absolute(String),
    Relative(crate::relative_path::T),
}

/// `external initialize_custom_error_config`. The Rust function behind it
/// (`custom_error_config_ffi.rs`) was `CustomErrorConfig::from_path`, its
/// error printed with `{}`.
fn initialize_custom_error_config(path: String) -> Result<T, String> {
    CustomErrorConfig::from_path(std::path::Path::new(&path)).map_err(|e| format!("{}", e))
}

pub fn initialize(path: Path) -> Result<T, String> {
    let abs_path = match path {
        Path::Absolute(path) => path,
        Path::Relative(path) => crate::relative_path::to_absolute(&path),
    };
    initialize_custom_error_config(abs_path)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_is_valid() {
        assert!(is_valid(&empty));
        assert_eq!(empty, T::default());
    }

    #[test]
    fn missing_file_is_empty() {
        let cfg = initialize(Path::Absolute(
            "/this/file/does/not/exist/custom_errors.json".to_string(),
        ));
        assert_eq!(cfg, Ok(empty));
    }
}
