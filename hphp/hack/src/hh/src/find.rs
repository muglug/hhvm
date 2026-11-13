// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `find/find.ml` (with its C stub `hh_readdir`): `make_next_files`,
//! which `Server_notifier`'s indexer lists the files of the root with. See
//! `hh/PORTING.md`. Ported by the file-watching assignment; not here yet:
//! `fold_files`, `iter_files`, `find`, `find_with_name`.
//!
//! The `Unix.Unix_error`s that OCaml lets through (a directory that cannot be
//! opened or read) are panics with the message OCaml's printer gives them.

use std::collections::VecDeque;

use crate::path;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_unix;

/// The kind of a file as `lstat` gives it, when it is one `make_next_files`
/// cares about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LstatKind {
    SReg,
    SDir,
    SLnk,
    Other,
}

fn lstat_kind(file: &str) -> Option<LstatKind> {
    match std::fs::symlink_metadata(file) {
        Ok(m) => {
            let t = m.file_type();
            Some(if t.is_symlink() {
                LstatKind::SLnk
            } else if t.is_dir() {
                LstatKind::SDir
            } else if t.is_file() {
                LstatKind::SReg
            } else {
                LstatKind::Other
            })
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            eprintln!("File not found: {}", file);
            None
        }
        Err(e) => panic!("{}", ocaml_unix::unix_error_to_string(&e, "lstat", file)),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]

pub enum DtKind {
    DtReg,
    DtDir,
    DtLnk,
}

/// `native_hh_readdir`: the entries of `path` (name, `d_type`), in the
/// reverse of the order `readdir` gives them (the C stub conses them onto a
/// list).
fn native_hh_readdir(path: &str) -> Vec<(String, Option<std::fs::FileType>)> {
    let rd = match std::fs::read_dir(path) {
        Ok(rd) => rd,
        Err(e) => panic!("{}", ocaml_unix::unix_error_to_string(&e, "opendir", path)),
    };
    let mut list = vec![];
    for ent in rd {
        let ent = match ent {
            Ok(ent) => ent,
            Err(e) => panic!("{}", ocaml_unix::unix_error_to_string(&e, "readdir", path)),
        };
        // `std::fs::DirEntry::file_type` is the `d_type` of the entry, or an
        // `lstat` when the file system does not give it (the `DT_UNKNOWN`
        // case below).
        let name = ent.file_name().to_string_lossy().into_owned();
        list.push((name, ent.file_type().ok()));
    }
    list.reverse();
    list
}

/// Sys.readdir only returns `string list`, but we need to know if we have files
/// or directories, so if we use Sys.readdir we need to do an lstat on every
/// file/subdirectory. The C readdir function gives us both the name and kind,
/// so this version does 1 syscall per directory, instead of 1 syscall per file
/// and 2 per directory.
pub fn hh_readdir(path: &str) -> Vec<(String, DtKind)> {
    native_hh_readdir(path)
        .into_iter()
        .filter_map(|(name, kind)| match name.as_str() {
            "." | ".." | ".git" | ".hg" => None,
            _ => match kind {
                Some(k) if k.is_dir() => Some((name, DtKind::DtDir)),
                Some(k) if k.is_file() => Some((name, DtKind::DtReg)),
                Some(k) if k.is_symlink() => Some((name, DtKind::DtLnk)),
                Some(_) => None,
                // DT_UNKNOWN - filesystem does not give us the type; do it slow
                None => match lstat_kind(&ocaml_filename::concat(path, &name)) {
                    Some(LstatKind::SDir) => Some((name, DtKind::DtDir)),
                    Some(LstatKind::SReg) => Some((name, DtKind::DtReg)),
                    Some(LstatKind::SLnk) => Some((name, DtKind::DtLnk)),
                    _ => None,
                },
            },
        })
        .collect()
}

/// `let max_files = 1000`
pub const MAX_FILES: usize = 1000;

/// `max_files`
pub fn max_files() -> usize {
    MAX_FILES
}

/// A frame of `type stack = Nil | Dir of (string * dt_kind) list * string *
/// stack`: the entries of a directory not looked at yet, and the directory.
/// The stack is a `Vec` of them, the innermost last (`Nil` is the empty
/// `Vec`).
struct Dir {
    files: VecDeque<(String, DtKind)>,
    dir: String,
}

/// `make_next_files ?include_symlinks ?name ?filter ?others root`: a function
/// that gives the next (at most `max_files`) files under `root` and `others`
/// that `filter` accepts, as `root`-prefixed paths, each time it is called,
/// and `[]` once there are none left. Like OCaml, a batch is in the reverse
/// of the order the files were found in. `include_symlinks` defaults to
/// `false`; `filter` to accepting everything; `name` is unused.
pub fn make_next_files(
    include_symlinks: Option<bool>,
    _name: Option<&str>,
    filter: Option<Box<dyn Fn(&str) -> bool + Send + Sync>>,
    others: Option<Vec<path::T>>,
    root: &path::T,
) -> Box<dyn FnMut() -> Vec<String> + Send> {
    let include_symlinks = include_symlinks.unwrap_or(false);
    let filter: Box<dyn Fn(&str) -> bool + Send + Sync> =
        filter.unwrap_or_else(|| Box::new(|_| true));
    let others = others.unwrap_or_default();
    let dirs: VecDeque<(String, DtKind)> = std::iter::once(path::to_string(root))
        .chain(others.iter().map(path::to_string))
        .filter_map(|path| match lstat_kind(&path) {
            Some(LstatKind::SReg) => Some((path, DtKind::DtReg)),
            Some(LstatKind::SDir) => Some((path, DtKind::DtDir)),
            Some(LstatKind::SLnk) if include_symlinks => Some((path, DtKind::DtLnk)),
            _ => None,
        })
        .collect();
    let mut state: Vec<Dir> = vec![Dir {
        files: dirs,
        dir: String::new(),
    }];
    Box::new(move || {
        // `process_stack 0 [] !state` (`process` and `process_stack` as a
        // loop over the stack).
        let mut sz = 0;
        let mut acc = vec![];
        loop {
            if sz >= MAX_FILES {
                break;
            }
            let Some(frame) = state.last_mut() else {
                break;
            };
            match frame.files.pop_front() {
                None => {
                    state.pop();
                }
                Some((name, kind)) => {
                    let name = if frame.dir.is_empty() {
                        name
                    } else {
                        ocaml_filename::concat(&frame.dir, &name)
                    };
                    match kind {
                        DtKind::DtReg if filter(&name) => {
                            sz += 1;
                            acc.push(name)
                        }
                        DtKind::DtLnk if include_symlinks && filter(&name) => {
                            sz += 1;
                            acc.push(name)
                        }
                        DtKind::DtDir => {
                            let dirfiles = hh_readdir(&name);
                            state.push(Dir {
                                files: dirfiles.into(),
                                dir: name,
                            })
                        }
                        _ => {}
                    }
                }
            }
        }
        // `name :: acc`
        acc.reverse();
        acc
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next_files_in_batches() {
        let dir = std::env::temp_dir().join(format!("hh_find_test_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("a/b")).unwrap();
        std::fs::create_dir_all(dir.join(".git")).unwrap();
        std::fs::write(dir.join(".git/x.php"), "").unwrap();
        std::fs::write(dir.join("a/b/c.php"), "").unwrap();
        std::fs::write(dir.join("a/d.txt"), "").unwrap();
        for i in 0..1001 {
            std::fs::write(dir.join(format!("f{i}.php")), "").unwrap();
        }
        std::os::unix::fs::symlink(dir.join("a/b/c.php"), dir.join("l.php")).unwrap();
        let root = dir.to_str().unwrap().to_string();
        let mut next = make_next_files(
            None,
            Some("root"),
            Some(Box::new(|f: &str| f.ends_with(".php"))),
            None,
            &root,
        );
        let mut all = vec![];
        let first = next();
        assert_eq!(first.len(), 1000);
        all.extend(first);
        let second = next();
        assert_eq!(second.len(), 2);
        all.extend(second);
        assert!(next().is_empty());
        assert!(next().is_empty());
        assert!(all.contains(&format!("{root}/a/b/c.php")));
        assert!(
            !all.iter()
                .any(|f| f.contains(".git") || f.ends_with("l.php"))
        );
        // With the symbolic links.
        let mut next = make_next_files(Some(true), None, None, None, &root);
        let mut all = vec![];
        loop {
            let batch = next();
            if batch.is_empty() {
                break;
            }
            all.extend(batch);
        }
        assert!(all.contains(&format!("{root}/l.php")));
        assert!(all.contains(&format!("{root}/a/d.txt")));
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
