// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `packages/package_config.ml`. See `hh/PORTING.md`.
//!
//! Its two `external`s were `packages_ocaml_ffi.rs` (removed from this tree
//! with the OCaml build): they parse the file with the `packages` crate, give
//! the empty `Package_info` when it cannot be read or parsed (`TODO(T148525961)`
//! there), and convert the result with
//! `oxidized::package_info_impl::package_info_to_oxidized`, whose positions
//! are in the file (a `Dummy` path of the file's absolute name).

use std::sync::LazyLock;

use oxidized::package_info_impl::Errors;
use oxidized::package_info_impl::package_info_to_oxidized;
use oxidized::parsing_error::ParsingError;

use crate::config_file_common;
use crate::hh_logger;
use crate::package_info;
use crate::relative_path;

/// `extract_packages_from_text_strict_ffi` and
/// `extract_packages_from_text_non_strict_ffi`.
fn extract_packages_from_text(
    strict: bool,
    filename: &str,
    enable_implicit_packages: bool,
) -> Result<package_info::T, Errors> {
    let info = if strict {
        packages::PackageInfo::from_text_strict(enable_implicit_packages, filename)
    } else {
        packages::PackageInfo::from_text_non_strict(enable_implicit_packages, filename)
    };
    match info {
        Ok(info) => package_info_to_oxidized(filename, info),
        Err(_) => Ok(package_info::T::default()),
    }
}

pub static REPO_CONFIG_PATH: LazyLock<relative_path::T> =
    LazyLock::new(|| relative_path::from_root(&config_file_common::get_pkgconfig_path()));

fn log_debug(msg: &str) {
    hh_logger::debug(Some("packages"), None, msg)
}

/// `parse`. Errors in the config are a `failwith` of their rendering (a
/// panic).
fn parse(enable_implicit_packages: bool, strict: bool, path: &str) -> package_info::T {
    match extract_packages_from_text(strict, path, enable_implicit_packages) {
        Err(errors) if errors.is_empty() => panic!("Bad package specifiction"),
        Err(errors) => {
            let strings: Vec<String> = errors
                .into_iter()
                .map(|(pos, msg, reasons)| {
                    let reasons = reasons
                        .into_iter()
                        .map(|(p, s)| {
                            oxidized::message::Message(
                                crate::pos_or_decl::of_raw_pos(p),
                                bstr::BString::from(s),
                            )
                        })
                        .collect();
                    crate::user_diagnostic::to_string(&crate::user_diagnostic::to_absolute(
                        &crate::parsing_error::to_user_diagnostic(
                            ParsingError::PackageConfigError { pos, msg, reasons },
                        ),
                    ))
                })
                .collect();
            panic!("{}", strings.concat())
        }
        Ok(package_info) => package_info,
    }
}

/// `load_and_parse ~strict ~enable_implicit_packages ~pkgs_config_abs_path`
pub fn load_and_parse(
    strict: bool,
    enable_implicit_packages: bool,
    pkgs_config_abs_path: &str,
) -> package_info::T {
    if !std::path::Path::new(pkgs_config_abs_path).exists() {
        log_debug(&format!(
            "Package config at {} does not exist",
            pkgs_config_abs_path
        ));
        package_info::empty()
    } else {
        let result = parse(enable_implicit_packages, strict, pkgs_config_abs_path);
        log_debug(&format!("Parsed {}", pkgs_config_abs_path));
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_file_is_empty() {
        assert_eq!(
            load_and_parse(true, false, "/this/directory/does/not/exist/PACKAGES.toml"),
            package_info::empty()
        );
    }

    #[test]
    fn parses_a_config() {
        let dir = std::env::temp_dir().join(format!("hh_package_config_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("PACKAGES.toml");
        std::fs::write(
            &path,
            "[packages]\n[packages.foo]\ninclude_paths = [\"//\"]\n[packages.bar]\nincludes = [\"foo\"]\n",
        )
        .unwrap();
        let info = load_and_parse(false, false, path.to_str().unwrap());
        assert_eq!(
            info.existing_packages.keys().collect::<Vec<_>>(),
            vec!["bar", "foo"]
        );
        package_info::log_package_info(&info);
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
