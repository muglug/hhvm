// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/sys/tmp.ml`. See `hh/PORTING.md`.
//!
//! Handling where our temporary files go.

use std::sync::LazyLock;

use crate::path;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_unix;

/// `Random.bits ()`: 30 random bits (OCaml seeds `Random` with
/// `Random.self_init` in `Utils`, so they differ from run to run).
fn random_bits() -> u32 {
    use std::hash::BuildHasher;
    use std::hash::Hasher;
    let mut h = std::collections::hash_map::RandomState::new().build_hasher();
    h.write_u64(ocaml_unix::gettimeofday().to_bits());
    h.write_u32(std::process::id());
    (h.finish() & 0x3FFF_FFFF) as u32
}

/// [temp_dir parent_dir prefix ] creates a new temporary directory under parent_dir.
/// The name of that directory is made of the given prefix followed by a random integer.
pub fn temp_dir(parent_dir: &str, prefix: &str) -> String {
    let dir = parent_dir;
    if let Err(e) = crate::sys_utils::mkdir_no_fail(&dir) {
        panic!("{}", crate::rt::ocaml_unix::unix_error_to_string(&e, "mkdir", &dir))
    }
    let tmpdir = ocaml_filename::concat(parent_dir, &format!("{}_{:06x}", prefix, random_bits()));
    let dir = &tmpdir;
    if let Err(e) = crate::sys_utils::mkdir_no_fail(&dir) {
        panic!("{}", crate::rt::ocaml_unix::unix_error_to_string(&e, "mkdir", &dir))
    }
    tmpdir
}

/// `$HH_TMPDIR`, or `/tmp/hh_server` with `/tmp` resolved (`Path.make`, so
/// `/private/tmp/hh_server` on macOS). Computed once, like OCaml's toplevel
/// value.
pub fn hh_server_tmp_dir() -> String {
    static HH_SERVER_TMP_DIR: LazyLock<String> = LazyLock::new(|| {
        match std::env::var_os("HH_TMPDIR") {
            Some(dir) => dir.to_string_lossy().into_owned(),
            None => path::to_string(&path::concat(
                &path::make(crate::sys_utils::TEMP_DIR_NAME),
                "hh_server",
            )),
        }
    });
    HH_SERVER_TMP_DIR.clone()
}

/// Create subdirectory in [hh_server_tmp_dir] as [description_what_for]/zSpathzStozS[root]
pub fn make_dir_in_tmp(description_what_for: &str, root: Option<&path::T>) -> String {
    let tmp = hh_server_tmp_dir();
    assert!(!description_what_for.is_empty());
    let dir = ocaml_filename::concat(&tmp, description_what_for);
    let dir = match root {
        None => dir,
        Some(root) => ocaml_filename::concat(&dir, &path::slash_escaped_string_of_path(root)),
    };
    crate::disk::mkdir_p(&dir);
    dir
}

#[cfg(test)]
mod tests {
    use std::os::unix::fs::MetadataExt;

    use super::*;

    fn scratch_dir(name: &str) -> String {
        let dir = std::env::temp_dir().join(format!(
            "hh_tmp_test_{}_{}_{}",
            name,
            std::process::id(),
            random_bits()
        ));
        dir.to_str().unwrap().to_string()
    }

    #[test]
    fn temp_dirs_are_world_writable_and_random() {
        let parent = scratch_dir("temp_dir");
        let a = temp_dir(&parent, "files");
        let b = temp_dir(&parent, "files");
        assert_ne!(a, b);
        let name = ocaml_filename::basename(&a);
        assert!(name.starts_with("files_"), "{}", name);
        assert!(name.len() >= "files_".len() + 6, "{}", name);
        assert_eq!(std::fs::metadata(&parent).unwrap().mode() & 0o777, 0o777);
        assert_eq!(std::fs::metadata(&a).unwrap().mode() & 0o777, 0o777);
        std::fs::remove_dir_all(&parent).unwrap();
    }

    #[test]
    fn mkdir_p_makes_parents_and_rejects_files() {
        let base = scratch_dir("mkdir_p");
        let deep = format!("{}/a/b/c", base);
        crate::disk::mkdir_p(&deep);
        assert!(std::fs::metadata(&deep).unwrap().is_dir());
        // Again: nothing to do.
        crate::disk::mkdir_p(&deep);
        let file = format!("{}/f", base);
        std::fs::write(&file, "").unwrap();
        let err = std::panic::catch_unwind(|| crate::disk::mkdir_p(&file)).unwrap_err();
        assert_eq!(
            err.downcast_ref::<String>().unwrap(),
            &format!("Disk_sig.Types.NotADirectory(\"{}\")", file)
        );
        std::fs::remove_dir_all(&base).unwrap();
    }

    /// `<hh_server_tmp_dir>/<what for>[/<escaped root>]`, made with its
    /// parents, world-writable.
    #[test]
    fn dirs_in_tmp() {
        let what_for = format!("hh_tmp_test_{}_{}", std::process::id(), random_bits());
        let root = "/nonexistent/z/www".to_string();
        let dir = make_dir_in_tmp(&what_for, Some(&root));
        let base = format!("{}/{}", hh_server_tmp_dir(), what_for);
        assert_eq!(dir, format!("{}/zSnonexistentzSzZzSwww", base));
        assert!(std::fs::metadata(&dir).unwrap().is_dir());
        assert_eq!(std::fs::metadata(&dir).unwrap().mode() & 0o777, 0o777);
        assert_eq!(std::fs::metadata(&base).unwrap().mode() & 0o777, 0o777);
        assert_eq!(make_dir_in_tmp(&what_for, None), base);
        std::fs::remove_dir_all(&base).unwrap();
        // `assert (String.length description_what_for > 0)`
        assert!(std::panic::catch_unwind(|| make_dir_in_tmp("", None)).is_err());
    }

    #[test]
    fn the_server_tmp_dir() {
        let dir = hh_server_tmp_dir();
        match std::env::var("HH_TMPDIR") {
            Ok(d) => assert_eq!(dir, d),
            Err(_) => assert!(dir.ends_with("/hh_server"), "{}", dir),
        }
    }
}
