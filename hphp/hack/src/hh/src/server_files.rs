// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_files.ml`. See `hh/PORTING.md`.
//!
//! The names of the files of a root under the temporary directory
//! (`$HH_TMPDIR`, else `/tmp/hh_server`): `<tmp>/<root with / as zS...>`
//! followed by an extension (design 5.5). They are a contract with the tests
//! and with Slack's scripts, and are exactly OCaml's.

use std::sync::RwLock;

use crate::global_config;
use crate::path;
use crate::rt::ocaml_filename;

fn tmp() -> &'static RwLock<Option<path::T>> {
    static TMP: RwLock<Option<path::T>> = RwLock::new(None);
    &TMP
}

/// Normally, the ServerFiles.* functions use Global_config.tmp_dir
/// which is initialized at startup to be either HH_TMPDIR if defined
/// or /tmp/hh_server otherwise.
///
/// But some tests like to use these ServerFiles.* functions with a
/// different tmpdir chosen at runtime. These tests can call
/// ServerFiles.set_tmp_FOR_TESTING_ONLY, and all subsequent ServerFiles.*
/// will refer to that new tmp directory.
/// CARE! This is only to be used in limited circumstances. All the
/// rest of the codebase will continue to use HH_TMPDIR-or-/tmp/hh_server.
/// This only affects the ServerFiles.* functions; nothing else.
/// You have been warned.
pub fn set_tmp_for_testing_only(t: path::T) {
    *tmp().write().unwrap_or_else(|e| e.into_inner()) = Some(t);
}

pub fn get_tmp() -> String {
    match &*tmp().read().unwrap_or_else(|e| e.into_inner()) {
        Some(t) => path::to_string(t),
        None => global_config::TMP_DIR.clone(),
    }
}

/// Slash-escaped path in the system temp directory corresponding
/// with this root directory for this extension.
pub fn path_of_root(root: &path::T, extension: &str) -> String {
    // TODO: move this to places that write this file
    let dir = &get_tmp();
    if let Err(e) = crate::sys_utils::mkdir_no_fail(&dir) {
        panic!("{}", crate::rt::ocaml_unix::unix_error_to_string(&e, "mkdir", &dir))
    }
    let root_part = path::slash_escaped_string_of_path(root);
    ocaml_filename::concat(&get_tmp(), &format!("{}{}", root_part, extension))
}

pub fn is_of_root(root: &path::T, fn_: &str) -> bool {
    let root_part = path::slash_escaped_string_of_path(root);
    fn_.starts_with(&ocaml_filename::concat(&get_tmp(), &root_part))
}

/// Lock on this file will be held after the server has finished initializing.
pub fn lock_file(root: &path::T) -> String {
    path_of_root(root, ".lock")
}

pub fn log_link(root: &path::T) -> String {
    path_of_root(root, ".log")
}

pub fn pids_file(root: &path::T) -> String {
    path_of_root(root, ".pids")
}

pub fn socket_file(root: &path::T) -> String {
    path_of_root(root, ".sock")
}

pub fn dfind_log(root: &path::T) -> String {
    path_of_root(root, ".dfind")
}

pub fn client_log(root: &path::T) -> String {
    path_of_root(root, ".client_log")
}

pub fn client_lsp_log(root: &path::T) -> String {
    path_of_root(root, ".client_lsp_log")
}

pub fn client_ide_log(root: &path::T) -> String {
    path_of_root(root, ".client_ide_log")
}

pub fn client_ide_naming_table(root: &path::T) -> String {
    path_of_root(root, ".client_ide_naming_table")
}

pub fn monitor_log_link(root: &path::T) -> String {
    path_of_root(root, ".monitor_log")
}

pub fn errors_file_path(root: &path::T) -> String {
    path_of_root(root, ".errors.bin")
}

pub fn server_finale_file(pid: isize) -> String {
    ocaml_filename::concat(&get_tmp(), &format!("{}.fin", pid))
}

pub fn server_progress_file(root: &path::T) -> String {
    path_of_root(root, ".progress.json")
}

pub fn server_receipt_to_monitor_file(pid: isize) -> String {
    ocaml_filename::concat(
        &get_tmp(),
        &format!("server_receipt_to_monitor.{}.json", pid),
    )
}

pub fn saved_state_download_dir() -> String {
    ocaml_filename::concat(&get_tmp(), "hh_saved_states_sql")
}

pub fn saved_state_staging_dir() -> String {
    ocaml_filename::concat(&get_tmp(), "hh_saved_states_staging")
}

#[cfg(test)]
pub(crate) mod tests {
    use std::os::unix::fs::MetadataExt;

    use super::*;

    /// A temporary directory of its own for the tests of the server layer
    /// that write the files of a root: `set_tmp_for_testing_only` is global,
    /// so every test sets the same one. It is created world-writable here,
    /// once, as `path_of_root` would: `mkdir_no_fail` sets the mode after
    /// making the directory, and a test running alongside must not see it in
    /// between.
    pub(crate) fn testing_tmp() -> String {
        static DIR: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| {
            let dir = std::env::temp_dir().join(format!("hh_server_files_test_{}", std::process::id()));
            let dir = dir.to_str().unwrap().to_string();
            let _ = std::fs::remove_dir_all(&dir);
            if let Err(e) = crate::sys_utils::mkdir_no_fail(&dir) {
                panic!("{}", crate::rt::ocaml_unix::unix_error_to_string(&e, "mkdir", &dir))
            }
            dir
        });
        set_tmp_for_testing_only(DIR.clone());
        DIR.clone()
    }

    #[test]
    fn file_names() {
        let tmp = testing_tmp();
        let root = "/home/zed/www".to_string();
        let esc = "zShomezSzZedzSwww";
        assert_eq!(get_tmp(), tmp);
        assert_eq!(lock_file(&root), format!("{}/{}.lock", tmp, esc));
        // The temporary directory is world-writable.
        assert_eq!(std::fs::metadata(&tmp).unwrap().mode() & 0o777, 0o777);
        for (f, ext) in [
            (log_link as fn(&path::T) -> String, ".log"),
            (pids_file, ".pids"),
            (socket_file, ".sock"),
            (dfind_log, ".dfind"),
            (client_log, ".client_log"),
            (client_lsp_log, ".client_lsp_log"),
            (client_ide_log, ".client_ide_log"),
            (client_ide_naming_table, ".client_ide_naming_table"),
            (monitor_log_link, ".monitor_log"),
            (errors_file_path, ".errors.bin"),
            (server_progress_file, ".progress.json"),
        ] {
            assert_eq!(f(&root), format!("{}/{}{}", tmp, esc, ext));
        }
        assert_eq!(server_finale_file(123), format!("{}/123.fin", tmp));
        assert_eq!(
            server_receipt_to_monitor_file(9),
            format!("{}/server_receipt_to_monitor.9.json", tmp)
        );
        assert_eq!(saved_state_download_dir(), format!("{}/hh_saved_states_sql", tmp));
        assert_eq!(saved_state_staging_dir(), format!("{}/hh_saved_states_staging", tmp));
        assert!(is_of_root(&root, &socket_file(&root)));
        assert!(!is_of_root(&"/home/other".to_string(), &socket_file(&root)));
    }

    /// Slack's `webapp/bin/claude/hack/lsp_naming_table_util.py` finds the
    /// IDE naming table from `hh_client --ide-logname`: it takes
    /// `Path(<log>).stem` and looks for `<tmp>/<stem>.client_ide_naming_table`.
    #[test]
    fn naming_table_from_ide_logname() {
        testing_tmp();
        for root in ["/var/www", "/home/z.y/www-1", "/a:b/c\\d"] {
            let root = root.to_string();
            let log = std::path::PathBuf::from(client_ide_log(&root));
            let stem = log.file_stem().unwrap().to_str().unwrap();
            let derived = log.with_file_name(format!("{}.client_ide_naming_table", stem));
            assert_eq!(derived.to_str().unwrap(), client_ide_naming_table(&root));
        }
        assert_eq!(
            client_ide_naming_table(&"/var/www".to_string()),
            format!("{}/zSvarzSwww.client_ide_naming_table", get_tmp())
        );
    }
}
