// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/relative_path.ml`. See `hh/PORTING.md`.
//!
//! The types are those of the `relative_path` crate, re-exported here
//! (`RelativePath` is `Relative_path.t`, `Prefix` is `Relative_path.prefix`).
//! This module has the functions of `relative_path.ml` that the typechecker
//! uses.
//!
//! As in OCaml, the directories that the prefixes stand for are global state:
//! [`set_path_prefix`] sets them (once, when the program starts) and
//! [`to_absolute`] reads them. `RelativePath::to_absolute` of the crate takes
//! them as an argument (`RelativePathCtx`) instead.

use std::path::Path;
use std::sync::RwLock;

pub use ::relative_path::*;

pub type T = RelativePath;

pub fn is_hhi(prefix: Prefix) -> bool {
    match prefix {
        Prefix::Hhi => true,
        Prefix::Root | Prefix::Dummy | Prefix::Tmp => false,
    }
}

pub fn is_root(prefix: Prefix) -> bool {
    match prefix {
        Prefix::Root => true,
        Prefix::Hhi | Prefix::Dummy | Prefix::Tmp => false,
    }
}

static ROOT: RwLock<Option<String>> = RwLock::new(None);

static HHI: RwLock<Option<String>> = RwLock::new(None);

static TMP: RwLock<Option<String>> = RwLock::new(None);

fn string_of_prefix(prefix: Prefix) -> &'static str {
    match prefix {
        Prefix::Root => "root",
        Prefix::Hhi => "hhi",
        Prefix::Tmp => "tmp",
        Prefix::Dummy => "",
    }
}

/// The exception `Invalid_argument`, which `path_of_prefix` raises for a
/// prefix that has not been set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvalidArgument(pub String);

impl std::fmt::Display for InvalidArgument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid_argument({:?})", self.0)
    }
}

impl std::error::Error for InvalidArgument {}

pub fn path_of_prefix(prefix: Prefix) -> Result<String, InvalidArgument> {
    let path = match prefix {
        Prefix::Root => ROOT.read().unwrap().clone(),
        Prefix::Hhi => HHI.read().unwrap().clone(),
        Prefix::Tmp => TMP.read().unwrap().clone(),
        Prefix::Dummy => Some(String::new()),
    };
    match path {
        Some(path) => Ok(path),
        None => Err(InvalidArgument(format!(
            "Prefix '{}' has not been set!",
            string_of_prefix(prefix)
        ))),
    }
}

/// `path_of_prefix`, where OCaml lets the exception propagate.
fn path_of_prefix_exn(prefix: Prefix) -> String {
    match path_of_prefix(prefix) {
        Ok(path) => path,
        Err(InvalidArgument(message)) => panic!("Invalid_argument: {}", message),
    }
}

fn enforce_trailing_slash(v: &str) -> String {
    // `Filename.dir_sep`
    if v.ends_with(std::path::MAIN_SEPARATOR) {
        v.to_string()
    } else {
        format!("{}{}", v, std::path::MAIN_SEPARATOR)
    }
}

/// `Path.to_string`: the paths of this port are UTF-8.
fn path_to_string(v: &Path) -> &str {
    v.to_str().expect("a path that is not UTF-8")
}

pub fn set_path_prefix(prefix: Prefix, v: &Path) {
    let v = path_to_string(v);
    assert!(!v.is_empty());

    let path_ref = match prefix {
        Prefix::Dummy => panic!("Dummy is always represented by an empty string"),
        Prefix::Root => &ROOT,
        Prefix::Hhi => &HHI,
        Prefix::Tmp => &TMP,
    };
    *path_ref.write().unwrap() = Some(enforce_trailing_slash(v));
}

pub fn prefix(p: &T) -> Prefix {
    p.prefix()
}

pub fn suffix(p: &T) -> String {
    p.path_str().to_string()
}

pub const DEFAULT: T = RelativePath::EMPTY;

pub fn equal(p1: &T, p2: &T) -> bool {
    p1 == p2
}

/// By prefix (`Root`, `Hhi`, `Dummy`, `Tmp`), then by suffix.
pub fn compare(p1: &T, p2: &T) -> std::cmp::Ordering {
    p1.cmp(p2)
}

pub fn prefix_to_enum(prefix: Prefix) -> isize {
    match prefix {
        Prefix::Root => 0,
        Prefix::Hhi => 1,
        Prefix::Dummy => 2,
        Prefix::Tmp => 3,
    }
}

pub fn prefix_of_enum(i: isize) -> Option<Prefix> {
    match i {
        0 => Some(Prefix::Root),
        1 => Some(Prefix::Hhi),
        2 => Some(Prefix::Dummy),
        3 => Some(Prefix::Tmp),
        _ => None,
    }
}

/// `[@@deriving show]` of `prefix`: the constructor, qualified by the module.
pub fn pp_prefix(fmt: &mut crate::format::Formatter, prefix: Prefix) {
    crate::format::pp_print_string(
        fmt,
        match prefix {
            Prefix::Root => "Relative_path.Root",
            Prefix::Hhi => "Relative_path.Hhi",
            Prefix::Dummy => "Relative_path.Dummy",
            Prefix::Tmp => "Relative_path.Tmp",
        },
    )
}

/// `[@@deriving show]` of `prefix`
pub fn show_prefix(prefix: Prefix) -> String {
    crate::format::asprintf(|fmt| pp_prefix(fmt, prefix))
}

/// `[@@deriving show]` of `t = prefix * string`: `"(@["`, `pp_prefix`,
/// `",@ "`, the suffix printed by `"%S"`, `"@])"`.
pub fn pp(fmt: &mut crate::format::Formatter, p: &T) {
    use crate::format;
    let suffix = crate::rt::ocaml_printf::sprintf_s(p.path_str());
    format::pp_print_string(fmt, "(");
    format::pp_open_box(fmt, 0);
    pp_prefix(fmt, p.prefix());
    format::pp_print_string(fmt, ",");
    format::pp_print_space(fmt);
    format::pp_print_string(fmt, &suffix);
    format::pp_close_box(fmt);
    format::pp_print_string(fmt, ")");
}

/// `[@@deriving show]` of `t`
pub fn show(p: &T) -> String {
    crate::format::asprintf(|fmt| pp(fmt, p))
}

/// We could have simply used Marshal.to_string here, but this does slightly
/// better on space usage.
pub fn storage_to_string(p: &T) -> String {
    format!("{}|{}", string_of_prefix(p.prefix()), p.path_str())
}

pub fn storage_of_string(str: &str) -> T {
    match str.find('|') {
        Some(idx) => {
            let prefix = &str[..idx];
            let content = &str[idx + 1..];
            let prefix = match prefix {
                "root" => Prefix::Root,
                "hhi" => Prefix::Hhi,
                "tmp" => Prefix::Tmp,
                "" => Prefix::Dummy,
                _ => panic!("invalid prefix"),
            };
            RelativePath::make(prefix, content.into())
        }
        None => panic!("not a Relative_path.t"),
    }
}

pub mod s {
    pub type T = super::T;

    pub fn compare(p1: &T, p2: &T) -> std::cmp::Ordering {
        super::compare(p1, p2)
    }

    pub fn equal(p1: &T, p2: &T) -> bool {
        super::equal(p1, p2)
    }

    pub fn to_string(p: &T) -> String {
        super::storage_to_string(p)
    }
}

/// The absolute path of `p`.
///
/// Raises `Invalid_argument` (panics) when the prefix of `p` has not been set
/// with `set_path_prefix`.
pub fn to_absolute(p: &T) -> String {
    format!("{}{}", path_of_prefix_exn(p.prefix()), p.path_str())
}

pub fn to_absolute_with_prefix(www: &Path, hhi_: &Path, p: &T) -> String {
    let path_concat =
        |p: &Path, rest: &str| format!("{}{}", enforce_trailing_slash(path_to_string(p)), rest);
    let rest = p.path_str();
    match p.prefix() {
        Prefix::Root => path_concat(www, rest),
        Prefix::Hhi => path_concat(hhi_, rest),
        Prefix::Dummy => rest.to_string(),
        Prefix::Tmp => panic!("invalid prefix"),
    }
}

pub fn to_tmp(p: &T) -> T {
    RelativePath::make(Prefix::Tmp, p.path().to_path_buf())
}

pub fn to_root(p: &T) -> T {
    RelativePath::make(Prefix::Root, p.path().to_path_buf())
}

/// `Relative_path.Set`: an `im::OrdSet` (see `crate::s_set` for why and for
/// the names of its methods); the functions are those of the collection.
pub mod set {
    pub type T = im::OrdSet<super::T>;
}

/// `Relative_path.Map`: an `im::OrdMap` (see `crate::s_map` for why and for
/// the names of its methods); the functions are those of the collection, and
/// of `crate::wrapped_map`.
pub mod map {
    pub use ::relative_path::map::*;

    pub type T<A> = im::OrdMap<super::T, A>;
}

/// Checks that the provided string indeed has the given prefix before
/// constructing path
pub fn create(prefix: Prefix, s: &str) -> T {
    let prefix_s = path_of_prefix_exn(prefix);
    let prefix_len = prefix_s.len();
    if !s.starts_with(&prefix_s) {
        eprint!("{} is not a prefix of {}", prefix_s, s);
        crate::utils::assert_false_log_backtrace(None);
    }
    RelativePath::make(prefix, s[prefix_len..].into())
}

/// Creates a new path, inferring the prefix. Will default to Dummy.
pub fn create_detect_prefix(s: &str) -> T {
    let file_prefix = [Prefix::Root, Prefix::Hhi, Prefix::Tmp]
        .into_iter()
        .find(|prefix| s.starts_with(&path_of_prefix_exn(*prefix)))
        .unwrap_or(Prefix::Dummy);
    create(file_prefix, s)
}

/// Strips the root and relativizes the file if possible, otherwise returns
/// original string
pub fn strip_root_if_possible(s: &str) -> Option<String> {
    let prefix_s = path_of_prefix_exn(Prefix::Root);
    let prefix_len = prefix_s.len();
    if !s.starts_with(&prefix_s) {
        None
    } else {
        Some(s[prefix_len..].to_string())
    }
}

/// Creates a Relative_path.t relative to the root. The argument must be
/// a *relative* path (the path suffix). If you wish to construct
/// a Relative_path.t from an absolute path, use
/// `create_detect_prefix` instead.
pub fn from_root(suffix: &str) -> T {
    RelativePath::make(Prefix::Root, suffix.into())
}

/// [from_root_opt ~suffix] is [from_root ~suffix] with the slashes at the end
/// of [suffix] dropped, or [None] when what remains is empty, absolute, or
/// has a [..] component.
pub fn from_root_opt(suffix: &str) -> Option<T> {
    let suffix = suffix.trim_end_matches('/');
    if suffix.is_empty() || suffix.starts_with('/') || suffix.split('/').any(|c| c == "..") {
        None
    } else {
        Some(from_root(suffix))
    }
}

/// [is_within ~dir path] is whether [path] is [dir] or lies under it. Paths
/// with different prefixes are never within one another.
pub fn is_within(dir: &T, path: &T) -> bool {
    prefix(dir) == prefix(path) && {
        let dir = suffix(dir);
        let path = suffix(path);
        path == dir || path.starts_with(&(dir + "/"))
    }
}

/// The prefixes are global: every test that needs them sets the same.
#[cfg(test)]
pub(crate) fn set_prefixes_for_tests() {
    set_path_prefix(Prefix::Root, Path::new("/data/www"));
    set_path_prefix(Prefix::Hhi, Path::new("/tmp/hhi/"));
    set_path_prefix(Prefix::Tmp, Path::new("/tmp/hh_tmp"));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(prefix: Prefix, suffix: &str) -> T {
        RelativePath::make(prefix, suffix.into())
    }

    fn set_prefixes() {
        set_prefixes_for_tests()
    }

    #[test]
    fn prefixes() {
        assert!(is_hhi(Prefix::Hhi) && !is_hhi(Prefix::Root));
        assert!(is_root(Prefix::Root) && !is_root(Prefix::Dummy));
        for (i, p) in [Prefix::Root, Prefix::Hhi, Prefix::Dummy, Prefix::Tmp]
            .into_iter()
            .enumerate()
        {
            assert_eq!(prefix_to_enum(p), i as isize);
            assert_eq!(prefix_of_enum(i as isize), Some(p));
        }
        assert_eq!(prefix_of_enum(4), None);
        assert_eq!(path_of_prefix(Prefix::Dummy), Ok(String::new()));
    }

    #[test]
    fn absolute() {
        set_prefixes();
        // A trailing slash is added when there is none.
        assert_eq!(path_of_prefix(Prefix::Root).unwrap(), "/data/www/");
        assert_eq!(path_of_prefix(Prefix::Hhi).unwrap(), "/tmp/hhi/");
        assert_eq!(to_absolute(&path(Prefix::Root, "a/b.php")), "/data/www/a/b.php");
        assert_eq!(to_absolute(&path(Prefix::Hhi, "c.hhi")), "/tmp/hhi/c.hhi");
        assert_eq!(to_absolute(&path(Prefix::Dummy, "a.php")), "a.php");
        assert_eq!(to_absolute(&DEFAULT), "");

        assert_eq!(create(Prefix::Root, "/data/www/a/b.php"), path(Prefix::Root, "a/b.php"));
        assert_eq!(
            create_detect_prefix("/data/www/a/b.php"),
            path(Prefix::Root, "a/b.php")
        );
        assert_eq!(create_detect_prefix("/tmp/hhi/c.hhi"), path(Prefix::Hhi, "c.hhi"));
        assert_eq!(
            create_detect_prefix("/tmp/hh_tmp/x.php"),
            path(Prefix::Tmp, "x.php")
        );
        assert_eq!(
            create_detect_prefix("/elsewhere/x.php"),
            path(Prefix::Dummy, "/elsewhere/x.php")
        );
        assert_eq!(
            strip_root_if_possible("/data/www/a.php"),
            Some("a.php".to_string())
        );
        assert_eq!(strip_root_if_possible("/data/other/a.php"), None);
    }

    #[test]
    fn absolute_with_prefix() {
        let www = Path::new("/www");
        let hhi_ = Path::new("/hhi/");
        assert_eq!(
            to_absolute_with_prefix(www, hhi_, &path(Prefix::Root, "a.php")),
            "/www/a.php"
        );
        assert_eq!(
            to_absolute_with_prefix(www, hhi_, &path(Prefix::Hhi, "a.hhi")),
            "/hhi/a.hhi"
        );
        assert_eq!(
            to_absolute_with_prefix(www, hhi_, &path(Prefix::Dummy, "a.php")),
            "a.php"
        );
    }

    #[test]
    fn storage() {
        let p = path(Prefix::Root, "a/b.php");
        assert_eq!(storage_to_string(&p), "root|a/b.php");
        assert_eq!(s::to_string(&path(Prefix::Dummy, "x")), "|x");
        assert_eq!(storage_of_string("root|a/b.php"), p);
        assert_eq!(storage_of_string("hhi|c|d"), path(Prefix::Hhi, "c|d"));
        assert_eq!(storage_of_string("|"), DEFAULT);
        assert_eq!(suffix(&p), "a/b.php");
        assert_eq!(prefix(&p), Prefix::Root);
        assert_eq!(to_tmp(&p), path(Prefix::Tmp, "a/b.php"));
        assert_eq!(to_root(&path(Prefix::Tmp, "x")), path(Prefix::Root, "x"));
        assert_eq!(from_root("x.php"), path(Prefix::Root, "x.php"));
    }

    #[test]
    fn order() {
        use std::cmp::Ordering;
        // The order of the prefixes, then of the suffixes as strings.
        assert_eq!(
            compare(&path(Prefix::Root, "z"), &path(Prefix::Hhi, "a")),
            Ordering::Less
        );
        assert_eq!(
            compare(&path(Prefix::Dummy, "a"), &path(Prefix::Tmp, "a")),
            Ordering::Less
        );
        assert_eq!(
            compare(&path(Prefix::Root, "foo.bar"), &path(Prefix::Root, "foo/bar")),
            Ordering::Less
        );
        assert!(equal(&path(Prefix::Root, "a"), &path(Prefix::Root, "a")));
        assert!(!equal(&path(Prefix::Root, "a"), &path(Prefix::Tmp, "a")));
    }

    #[test]
    fn from_root_opt_and_is_within() {
        assert_eq!(from_root_opt("a/b//"), Some(from_root("a/b")));
        assert_eq!(from_root_opt("a"), Some(from_root("a")));
        assert_eq!(from_root_opt("///"), None);
        assert_eq!(from_root_opt(""), None);
        assert_eq!(from_root_opt("/a"), None);
        assert_eq!(from_root_opt("a/../b"), None);
        assert_eq!(from_root_opt(".."), None);
        assert_eq!(from_root_opt("a/..b"), Some(from_root("a/..b")));
        let dir = from_root("a/b");
        assert!(is_within(&dir, &from_root("a/b")));
        assert!(is_within(&dir, &from_root("a/b/c.php")));
        assert!(!is_within(&dir, &from_root("a/bc.php")));
        assert!(!is_within(&dir, &path(Prefix::Hhi, "a/b/c.php")));
    }

}
