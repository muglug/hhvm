// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/config_file/config_file.ml`. See `hh/PORTING.md`.
//!
//! Most of the module is `Config_file_common` and `Config_file_version`
//! again (`include Config_file_version`, `let empty =
//! Config_file_common.empty`...): those are re-exported.

pub use crate::config_file_common::apply_overrides;
pub use crate::config_file_common::empty;
pub use crate::config_file_common::FILE_PATH_RELATIVE_TO_REPO_ROOT;
pub use crate::config_file_common::getters;
pub use crate::config_file_common::keys;
pub use crate::config_file_common::of_list;
pub use crate::config_file_common::parse_contents;
pub use crate::config_file_common::parse_local_config;
pub use crate::config_file_common::print_to_stderr;
pub use crate::config_file_version::*;
use crate::exception;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::sys_utils;

pub type T = crate::config_file_common::T;

pub fn cat_packages_file(fn_: &str) -> Vec<u8> {
    // `Disk.file_exists`
    if std::path::Path::new(fn_).exists() {
        match sys_utils::cat(fn_) {
            Ok(contents) => contents,
            Err(exn) => {
                let e = exception::wrap(exn);
                hh_logger::exception_(Some(&format!("{} deleted: ", fn_)), &e);
                vec![]
            }
        }
    } else {
        vec![]
    }
}

pub fn cat_hhconfig_file(fn_: &str) -> Vec<u8> {
    match sys_utils::cat(fn_) {
        Ok(contents) => contents,
        Err(exn) => {
            let e = exception::wrap(exn);
            hh_logger::exception_(Some(".hhconfig deleted: "), &e);
            exit::exit(None, None, None, None, exit_status::T::HhconfigDeleted)
        }
    }
}

/// [parse_hhconfig file_path] parses the content of [file_path].
pub fn parse_hhconfig(fn_: &str) -> T {
    let contents = cat_hhconfig_file(fn_);
    crate::config_file_common::parse_contents(&contents)
}

pub mod utils {
    use crate::config_file_common;
    use crate::path;
    use crate::yojson::safe::T as Json;

    pub fn parse_hhconfig_and_hh_conf_to_json(
        root: &path::T,
        server_local_config_path: &str,
    ) -> Json {
        let server_local_config = super::parse_local_config(server_local_config_path);
        let hh_config = super::parse_local_config(&path::to_string(&path::concat(
            root,
            super::FILE_PATH_RELATIVE_TO_REPO_ROOT,
        )));
        // OCaml evaluates the elements of the list from the last to the first
        // (`to_json` raises on a value that is not JSON).
        let hhconfig_json = config_file_common::to_json(&hh_config);
        let hh_conf_json = config_file_common::to_json(&server_local_config);
        Json::Assoc(vec![
            ("hh.conf".to_string(), hh_conf_json),
            ("hhconfig".to_string(), hhconfig_json),
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn packages_file() {
        assert_eq!(
            cat_packages_file("/nonexistent/PACKAGES.toml"),
            Vec::<u8>::new()
        );
        let path = std::env::temp_dir().join(format!("hh_config_file_pkgs_{}", std::process::id()));
        std::fs::write(&path, b"[packages]\n").unwrap();
        assert_eq!(
            cat_packages_file(path.to_str().unwrap()),
            b"[packages]\n".to_vec()
        );
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn hhconfig_file() {
        let dir = std::env::temp_dir().join(format!("hh_config_file_root_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join(".hhconfig"), b"a = 1\n").unwrap();
        let hhconfig = dir.join(".hhconfig");
        let config = parse_hhconfig(hhconfig.to_str().unwrap());
        assert_eq!(getters::string_opt("a", &config), Some("1".to_string()));
        let json = utils::parse_hhconfig_and_hh_conf_to_json(
            &crate::path::make(dir.to_str().unwrap()),
            "/nonexistent/hh.conf",
        );
        assert_eq!(
            crate::yojson::safe::to_string(&json),
            r#"{"hh.conf":{},"hhconfig":{"a":"1"}}"#
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
