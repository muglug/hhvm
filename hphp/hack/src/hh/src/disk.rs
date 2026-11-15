// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/disk/disk.ml` (`Real_disk`, the disk of a program that is
//! not a test of the mocked disk), as far as the ported modules use it.

use crate::path;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_printf::sprintf_s;
use crate::rt::ocaml_unix;

/// `Disk.file_exists` (`Sys.file_exists`)
pub fn file_exists(file: &str) -> bool {
    path::file_exists(&file.to_string())
}

/// `Disk.is_directory` (`Real_disk.is_directory`: `Sys.is_directory`, false
/// where that raises `Sys_error`)
pub fn is_directory(x: &str) -> bool {
    path::is_directory(&x.to_string()).unwrap_or(false)
}

/// `Disk.mkdir_p` (`Real_disk.mkdir_p`): the directory
/// and its missing parents, each `0o777` under umask 0.
pub fn mkdir_p(d: &str) {
    if d.is_empty() {
        panic!("Unexpected empty directory, should never happen")
    } else if !path::file_exists(&d.to_string()) {
        mkdir_p(&ocaml_filename::dirname(d));
        match ocaml_unix::mkdir_with_umask(d, 0o777, 0) {
            Ok(()) => {}
            Err(e) if e.raw_os_error() == Some(libc::EEXIST) => {}
            Err(e) => panic!("{}", ocaml_unix::unix_error_to_string(&e, "mkdir", d)),
        }
    } else if std::fs::metadata(d).is_ok_and(|m| m.is_dir()) {
    } else {
        // raise (NotADirectory d)
        panic!("Disk_sig.Types.NotADirectory({})", sprintf_s(d))
    }
}
