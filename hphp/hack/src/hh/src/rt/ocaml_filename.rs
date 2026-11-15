// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stdlib/filename.ml` (OCaml's `Stdlib.Filename` on Unix), the
//! functions
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

/// `Filename.quote` (Unix): between single quotes, a single quote written
/// `'\''`.
pub fn quote(s: &str) -> String {
    let mut b = String::with_capacity(s.len() + 20);
    b.push('\'');
    for c in s.chars() {
        if c == '\'' {
            b.push_str("'\\''");
        } else {
            b.push(c);
        }
    }
    b.push('\'');
    b
}

/// `Filename.is_relative`
pub fn is_relative(n: &str) -> bool {
    !n.starts_with('/')
}

fn random_bits() -> u32 {
    use std::hash::BuildHasher;
    use std::hash::Hasher;
    let mut h = std::collections::hash_map::RandomState::new().build_hasher();
    h.write_u64(crate::rt::ocaml_unix::gettimeofday().to_bits());
    h.write_u32(std::process::id());
    h.finish() as u32
}

/// `Filename.open_temp_file ~mode:[Open_binary] ~temp_dir prefix suffix`: a
/// new file `<temp_dir>/<prefix><6 hex digits><suffix>`, mode 0o600, made
/// with `O_EXCL`; up to 1000 names are tried.
pub fn open_temp_file(
    temp_dir: &str,
    prefix: &str,
    suffix: &str,
) -> std::io::Result<(String, std::fs::File)> {
    use std::os::unix::fs::OpenOptionsExt;
    let mut last = None;
    for _ in 0..1000 {
        let name = concat(
            temp_dir,
            &format!("{}{:06x}{}", prefix, random_bits() & 0xFFFFFF, suffix),
        );
        match std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&name)
        {
            Ok(f) => return Ok((name, f)),
            Err(e) => last = Some(e),
        }
    }
    Err(last.unwrap_or_else(|| std::io::Error::other("open_temp_file")))
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
