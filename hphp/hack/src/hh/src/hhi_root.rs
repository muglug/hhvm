// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `hhi/hhi.ml` as the server uses it: the hhi root (`root`),
//! `get_hhi_root`, `set_custom_hhi_root` and `touch`. (The checker reads the
//! hhi files from the binary, `hhi::HHI_CONTENTS`; the extracted directory
//! names them, the `Hhi` prefix of `Relative_path`, and is what `touch`
//! keeps fresh.) The module is not called `hhi` because the crate `hhi`
//! holds the contents.
//!
//! Owned by **SRV** (created by SRV; `monitor_start.rs` has its own
//! `hhi_get_hhi_root` for check mode, MON may switch to this one).

#![allow(non_upper_case_globals)]

use std::sync::Mutex;

use crate::find;
use crate::path;
use crate::relative_path;
use crate::sys_utils;

/// `root`
static root: Mutex<Option<path::T>> = Mutex::new(None);

fn get_root() -> Option<path::T> {
    root.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

fn set_root(r: path::T) {
    *root.lock().unwrap_or_else(|e| e.into_inner()) = Some(r)
}

/// `extract_hhis dir` (`Sys_utils.write_file` raises `Sys_error`: a
/// panic).
fn extract_hhis(dir: &path::T) {
    if let Err(e) = hhi::write_hhi_files(std::path::Path::new(&path::to_string(dir))) {
        std::panic::panic_any(sys_utils::SysError(e.to_string()))
    }
}

/// Touch functionality for all hhis below root (`touch_root r`).
pub fn touch_root(r: &path::T) {
    let filter: Box<dyn Fn(&str) -> bool + Send + Sync> = Box::new(|file| file.ends_with(".hhi"));
    let mut next = find::make_next_files(None, None, Some(filter), None, r);
    loop {
        let files = next();
        if files.is_empty() {
            break;
        }
        for file in files {
            // `Sys_utils.try_touch`: errors are ignored.
            let _ = sys_utils::touch(
                sys_utils::TouchMode::TouchExisting {
                    follow_symlinks: true,
                },
                &file,
            );
        }
    }
}

/// `touch ()`
pub fn touch() {
    if let Some(r) = get_root() {
        touch_root(&r)
    }
}

/// Entry points to actually extract the files and set up the hhi path
/// (`get_hhi_root ?force_write ()`). Idempotent unless `force_write`.
pub fn get_hhi_root(force_write: bool) -> path::T {
    match (get_root(), force_write) {
        (Some(r), false) => r,
        _ => {
            let tmpdir = path::make(&crate::tmp::temp_dir(&crate::global_config::tmp_dir, "hhi"));
            extract_hhis(&tmpdir);
            set_root(tmpdir.clone());
            relative_path::set_path_prefix(
                relative_path::Prefix::Hhi,
                std::path::Path::new(&path::to_string(&tmpdir)),
            );
            tmpdir
        }
    }
}

/// `root := Some dir` without touching the prefix of `Relative_path`: for
/// a root that the monitor's entry wrapper chose
/// (`monitor_start::setup_hhi_root`).
pub fn record_root(dir: path::T) {
    set_root(dir)
}

/// `set_custom_hhi_root dir`
pub fn set_custom_hhi_root(dir: path::T) {
    relative_path::set_path_prefix(
        relative_path::Prefix::Hhi,
        std::path::Path::new(&path::to_string(&dir)),
    );
    set_root(dir);
}
