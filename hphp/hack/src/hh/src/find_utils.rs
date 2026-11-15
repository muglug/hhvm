// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/find_utils.ml`. See `hh/PORTING.md`.
//!
//! `crate::files` finds the Hack files of a directory for the driver, with
//! the same rules.

/// The file extensions we are interested in
pub const EXTENSIONS: &[&str] = &[
    // normal php file
    ".php",
    // our php template or test files
    ".phpt",
    // strict-mode files (Hack)
    ".hack",
    // partial-mode files (Hack)
    ".hackpartial",
    // open source hack: bikeshed entry
    ".hck",
    // open source hack: biekshed entry
    ".hh",
    // interface files only visible to the type checker
    ".hhi",
    // XHP extensions
    ".xhp",
];

/// `Filename.basename`
fn filename_basename(name: &str) -> &str {
    let name_bytes = name.as_bytes();
    if name.is_empty() {
        // `Filename.current_dir_name`
        return ".";
    }
    // `find_end`: skip the trailing separators.
    let mut n = name_bytes.len() as isize - 1;
    while n >= 0 && name_bytes[n as usize] == b'/' {
        n -= 1;
    }
    if n < 0 {
        return &name[0..1];
    }
    // `find_beg`
    let p = n + 1;
    while n >= 0 && name_bytes[n as usize] != b'/' {
        n -= 1;
    }
    &name[(n + 1) as usize..p as usize]
}

pub fn is_dot_file(path: &str) -> bool {
    let filename = filename_basename(path);
    !filename.is_empty() && filename.as_bytes()[0] == b'.'
}

pub fn is_hack(path: &str) -> bool {
    // `Filename.check_suffix`
    !is_dot_file(path) && EXTENSIONS.iter().any(|ext| path.ends_with(ext))
}

/// Returns whether one of the ancestral directories of path has the given
/// name.
pub fn has_ancestor(path: &str, ancestor_name: &str) -> bool {
    let dirname = crate::path::dirname(&path.to_string());
    if dirname == path {
        // Terminal condition
        false
    } else if crate::path::basename(&dirname) == ancestor_name {
        true
    } else {
        has_ancestor(&dirname, ancestor_name)
    }
}

/// Filter the relative path. This will reject files not in [extensions] and
/// maybe more.
pub fn file_filter(f: &str) -> bool {
    // Filter the relative path
    let f = crate::relative_path::strip_root_if_possible(f).unwrap_or_else(|| f.to_string());
    is_hack(&f) && !crate::files_to_ignore::should_ignore(&f)
}

pub fn path_filter(f: &crate::relative_path::T) -> bool {
    file_filter(&crate::relative_path::suffix(f))
}

/// It can be hard to be precise about what each filtering function does. This
/// function there is explained in the role it plays. Once the file watcher has
/// given us its raw updates, then we must put them through this function.
/// Note that Watchman and Edenfs_watcher only return files satisfying
/// FilesToIgnore.server_watch_spec, while dfind may return arbitrary
/// additional files. That's fine, since we will be filtering them away here.
/// If this function says there are any changes, then hh_server will
/// necessarily take some action in its recheck loop -- maybe do a recheck, or
/// maybe restart because .hhconfig has changed or similar.
///
/// This function takes as input a set of strings representing
/// fully-qualified pathnames that came out of the file watcher. They might be
/// symlinks, e.g. if we watch root ~/dir, and watchman tells us that
/// ~/dir/a.php has changed, it might be that a.php is really a symlink to
/// something outside the root. This function accordingly takes in the
/// fully-qualified pathnames from watchman, resolves symlinks, excludes the
/// ones where the resolved paths are outside root, and runs the same
/// file_filter as above.
pub fn post_file_watcher_filter_from_fully_qualified_raw_updates(
    root: &crate::path::T,
    raw_updates: &crate::s_set::T,
) -> crate::relative_path::set::T {
    let root = crate::path::to_string(root);
    // Because of symlinks, we can have updates from files that aren't in
    // the .hhconfig directory
    let updates: crate::s_set::T = raw_updates
        .iter()
        .filter(|p| p.starts_with(&root))
        .cloned()
        .collect();
    // `Relative_path.(relativize_set Root updates)`
    let updates: crate::relative_path::set::T = updates
        .iter()
        .map(|k| crate::relative_path::create(crate::relative_path::Prefix::Root, k))
        .collect();
    updates
        .into_iter()
        .filter(|update| file_filter(&crate::relative_path::to_absolute(update)))
        .collect()
}

/// `Base.String.hash`: `Base_hash_string`, OCaml's `caml_hash_mix_string`
/// with seed 0 and its final mix, masked to 30 bits (a copy of the one in
/// `crate::class_parent_check`, which is behind `port` alone).
fn base_string_hash(s: &[u8]) -> u32 {
    fn mix(h: u32, d: u32) -> u32 {
        let d = d.wrapping_mul(0xcc9e2d51);
        let d = d.rotate_left(15);
        let d = d.wrapping_mul(0x1b873593);
        let h = h ^ d;
        let h = h.rotate_left(13);
        h.wrapping_mul(5).wrapping_add(0xe6546b64)
    }
    let mut h: u32 = 0;
    let len = s.len();
    let mut i = 0;
    while i + 4 <= len {
        let w = u32::from_le_bytes([s[i], s[i + 1], s[i + 2], s[i + 3]]);
        h = mix(h, w);
        i += 4;
    }
    let mut w: u32 = 0;
    let rest = len & 3;
    if rest == 3 {
        w = (s[i + 2] as u32) << 16;
    }
    if rest >= 2 {
        w |= (s[i + 1] as u32) << 8;
    }
    if rest >= 1 {
        w |= s[i] as u32;
        h = mix(h, w);
    }
    h ^= len as u32;
    // `FINAL_MIX`
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h & 0x3FFF_FFFF
}

/// Hash file name and return true for [sample_rate] fraction of hashes
pub fn sample_filter(sample_rate: f64, x: &crate::relative_path::T) -> bool {
    let hash = base_string_hash(crate::relative_path::suffix(x).as_bytes()) as isize;
    ((hash % 1000000) as f64) <= sample_rate * 1000000.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basename() {
        assert_eq!(filename_basename(""), ".");
        assert_eq!(filename_basename("/"), "/");
        assert_eq!(filename_basename("a/b.php"), "b.php");
        assert_eq!(filename_basename("a/b/"), "b");
        assert_eq!(filename_basename("b.php"), "b.php");
    }

    #[test]
    fn ancestors() {
        assert!(has_ancestor("/a/b/c/d.php", "b"));
        assert!(has_ancestor("a/b/c/d.php", "a"));
        assert!(!has_ancestor("/a/b/c/d.php", "d.php"));
        assert!(!has_ancestor("/a/b/c/d.php", "x"));
        assert!(!has_ancestor("d.php", "d.php"));
    }

    #[test]
    fn sampling() {
        // `Hashtbl.hash` in OCaml 5.1.1 (see `crate::class_parent_check`).
        assert_eq!(base_string_hash(b"a"), 721651713);
        assert_eq!(base_string_hash(b"abcd"), 65890154);
        let p = crate::relative_path::from_root("a");
        // 721651713 mod 1000000 = 651713
        assert!(sample_filter(0.651713, &p));
        assert!(!sample_filter(0.651712, &p));
        assert!(sample_filter(1.0, &p));
        assert!(!sample_filter(0.0, &p));
    }

    #[test]
    fn watcher_updates() {
        crate::relative_path::set_prefixes_for_tests();
        let raw: crate::s_set::T = [
            "/data/www/a.php",
            "/data/www/dir",
            "/data/www/b.txt",
            "/data/www/.hhconfig",
            "/data/www/vendor/bin/x.php",
            "/data/www/vendor/lib/y.php",
            "/data/www/c/.d.php",
            "/elsewhere/e.php",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let updates = post_file_watcher_filter_from_fully_qualified_raw_updates(
            &"/data/www".to_string(),
            &raw,
        );
        let suffixes: Vec<String> = updates.iter().map(crate::relative_path::suffix).collect();
        assert_eq!(
            suffixes,
            vec!["a.php".to_string(), "vendor/lib/y.php".to_string()]
        );
    }

    #[test]
    fn hack_files() {
        assert!(is_hack("a/b.php"));
        assert!(is_hack("a/b.hhi"));
        assert!(is_hack("b.hack"));
        assert!(!is_hack("a/.b.php"));
        assert!(!is_hack("a/b.txt"));
        assert!(!is_hack("a/b.php/"));
    }
}
