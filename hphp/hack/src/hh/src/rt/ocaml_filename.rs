// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! OCaml's `Stdlib.Filename` on Unix (`stdlib/filename.ml`), the functions
//! that the ported modules use. They work on the bytes of the name, as OCaml
//! does; the separator is `/`, so a name is only ever cut next to one.

/// `Filename.current_dir_name`
pub fn current_dir_name() -> &'static str {
    "."
}

/// `Filename.parent_dir_name`
pub fn parent_dir_name() -> &'static str {
    ".."
}

/// `Filename.dir_sep`
pub fn dir_sep() -> &'static str {
    "/"
}

fn is_dir_sep(s: &[u8], i: usize) -> bool {
    s[i] == b'/'
}

/// `Filename.concat dirname filename`: `dirname ^ "/" ^ filename`, without
/// the `/` when `dirname` is empty or already ends with one.
pub fn concat(dirname: &str, filename: &str) -> String {
    let l = dirname.len();
    if l == 0 || is_dir_sep(dirname.as_bytes(), l - 1) {
        format!("{}{}", dirname, filename)
    } else {
        format!("{}{}{}", dirname, dir_sep(), filename)
    }
}

/// `Filename.basename` (`generic_basename`): the name without its directory
/// and trailing separators; `"."` for `""`, `"/"` for a name of separators.
pub fn basename(name: &str) -> String {
    let s = name.as_bytes();
    if s.is_empty() {
        return current_dir_name().to_string();
    }
    // find_end
    let mut n = s.len() as isize - 1;
    while n >= 0 && is_dir_sep(s, n as usize) {
        n -= 1;
    }
    if n < 0 {
        return name[..1].to_string();
    }
    // find_beg
    let p = (n + 1) as usize;
    while n >= 0 && !is_dir_sep(s, n as usize) {
        n -= 1;
    }
    if n < 0 {
        name[..p].to_string()
    } else {
        name[(n + 1) as usize..p].to_string()
    }
}

/// `Filename.dirname` (`generic_dirname`): the directory part of the name,
/// without trailing separators; `"."` when there is none, `"/"` at the root.
pub fn dirname(name: &str) -> String {
    let s = name.as_bytes();
    if s.is_empty() {
        return current_dir_name().to_string();
    }
    // trailing_sep
    let mut n = s.len() as isize - 1;
    while n >= 0 && is_dir_sep(s, n as usize) {
        n -= 1;
    }
    if n < 0 {
        return name[..1].to_string();
    }
    // base
    while n >= 0 && !is_dir_sep(s, n as usize) {
        n -= 1;
    }
    if n < 0 {
        return current_dir_name().to_string();
    }
    // intermediate_sep
    while n >= 0 && is_dir_sep(s, n as usize) {
        n -= 1;
    }
    if n < 0 {
        name[..1].to_string()
    } else {
        name[..(n + 1) as usize].to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concat_as_ocaml() {
        assert_eq!(concat("a", "b"), "a/b");
        assert_eq!(concat("a/", "b"), "a/b");
        assert_eq!(concat("", "b"), "b");
        assert_eq!(concat("/tmp/hh_server", "zSa.sock"), "/tmp/hh_server/zSa.sock");
    }

    #[test]
    fn dirname_as_ocaml() {
        assert_eq!(dirname(""), ".");
        assert_eq!(dirname("/"), "/");
        assert_eq!(dirname("//"), "/");
        assert_eq!(dirname("a"), ".");
        assert_eq!(dirname("/a"), "/");
        assert_eq!(dirname("a/b"), "a");
        assert_eq!(dirname("a//b"), "a");
        assert_eq!(dirname("/a/b/"), "/a");
        assert_eq!(dirname("//a"), "/");
        assert_eq!(dirname("/tmp/hh_server/x.pids"), "/tmp/hh_server");
    }

    #[test]
    fn basename_as_ocaml() {
        assert_eq!(basename(""), ".");
        assert_eq!(basename("/"), "/");
        assert_eq!(basename("a"), "a");
        assert_eq!(basename("a/b"), "b");
        assert_eq!(basename("a/b/"), "b");
        assert_eq!(basename("/a"), "a");
        assert_eq!(basename("été/ça"), "ça");
    }
}
