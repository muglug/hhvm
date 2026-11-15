// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: finding the Hack files of a directory for the driver
//! (`hh check`), with the rules of `Find_utils` (`utils/find_utils.ml`).

use std::path::Path;
use std::path::PathBuf;

use regex::Regex;

/// `Find_utils.extensions`: the extensions of the files the typechecker reads.
const EXTENSIONS: &[&str] = &[
    "php",
    "phpt",
    "hack",
    "hackpartial",
    "hck",
    "hh",
    "hhi",
    "xhp",
];

/// `Find_utils.is_hack`: a file with one of the [`EXTENSIONS`] whose name does
/// not start with a dot.
pub fn is_hack_file(path: &Path) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    !name.starts_with('.')
        && EXTENSIONS.iter().any(|ext| {
            name.len() > ext.len()
                && name.ends_with(ext)
                && name.as_bytes()[name.len() - ext.len() - 1] == b'.'
        })
}

/// The Hack files `hh_server` checks under `root`, in a stable order: those
/// that `Find.make_next_files ~filter:Find_utils.file_filter` finds. Every
/// directory is visited but `.git` and `.hg` (hidden ones too), symbolic
/// links are not followed, and a file is kept if it is a Hack file
/// ([`is_hack_file`]) and `Files_to_ignore.should_ignore` is false of its
/// root-relative path: none of `ignored` (the `ignored_paths` of the
/// `.hhconfig`) matches at its start, and it is not under `vendor/bin/`.
///
/// The paths are root-relative and sorted as `PathBuf`s are (component by
/// component): each directory's entries are sorted by name and the tree is
/// walked depth first, which gives that order without sorting the whole list.
/// A directory is not walked when no file under it can be kept (see
/// [`Walker::prunes`]): most of the directories of a repository are under
/// ignored ones (`node_modules/`, ...).
pub fn find_hack_files(root: &Path, ignored: &[Regex]) -> Vec<PathBuf> {
    let walker = Walker {
        ignored,
        // A pattern can exclude whole directories when what it matches at the
        // start of a path does not depend on what follows the matched text:
        // no `$` or word-boundary assertion (`\b`, `\B`) in it.
        prefix_ignored: ignored
            .iter()
            .filter(|re| {
                let s = re.as_str();
                !s.contains('$') && !s.contains("\\b") && !s.contains("\\B")
            })
            .collect(),
    };
    let mut files = vec![];
    walker.walk(root, PathBuf::new(), &mut files);
    files
}

struct Walker<'a> {
    ignored: &'a [Regex],
    prefix_ignored: Vec<&'a Regex>,
}

impl Walker<'_> {
    /// Whether no file under the root-relative directory `dir` can be kept:
    /// `dir/` is `vendor/bin/` or starts with something a prefix pattern
    /// matches (so every `dir/...` does too).
    fn prunes(&self, dir: &Path) -> bool {
        let Some(dir) = dir.to_str() else {
            return false;
        };
        let dir_slash = format!("{dir}/");
        dir_slash == "vendor/bin/" || self.prefix_ignored.iter().any(|re| re.is_match(&dir_slash))
    }

    fn keeps(&self, relative: &Path) -> bool {
        let relative = relative.to_string_lossy();
        !(self.ignored.iter().any(|re| re.is_match(&relative))
            || relative.starts_with("vendor/bin/"))
    }

    /// Appends the kept files under `abs` (whose root-relative path is `rel`)
    /// to `out`, in order. The subdirectories are walked in parallel.
    ///
    /// OCaml lists the files of a root one directory at a time
    /// (`find/find.ml`, `Find.make_next_files`). Here the entries of a
    /// directory are walked in parallel (rayon) to shorten the listing of a
    /// large root; the result is the sequential walk's, because the entries
    /// are sorted by name and the parts are concatenated in that order.
    fn walk(&self, abs: &Path, rel: PathBuf, out: &mut Vec<PathBuf>) {
        use rayon::prelude::*;
        let Ok(read_dir) = std::fs::read_dir(abs) else {
            return;
        };
        // Symbolic links are not followed: `file_type` is that of the entry
        // itself (from the directory, without a `stat` where the file system
        // gives it).
        let mut entries: Vec<(std::ffi::OsString, bool)> = read_dir
            .filter_map(|entry| {
                let entry = entry.ok()?;
                let file_type = entry.file_type().ok()?;
                let name = entry.file_name();
                if file_type.is_dir() {
                    if name == ".git" || name == ".hg" {
                        return None;
                    }
                    Some((name, true))
                } else if file_type.is_file() {
                    Some((name, false))
                } else {
                    None
                }
            })
            .collect();
        entries.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        let parts: Vec<Vec<PathBuf>> = entries
            .into_par_iter()
            .map(|(name, is_dir)| {
                let rel = rel.join(&name);
                if is_dir {
                    let mut sub = vec![];
                    if !self.prunes(&rel) {
                        self.walk(&abs.join(&name), rel, &mut sub);
                    }
                    sub
                } else if is_hack_file(&rel) && self.keeps(&rel) {
                    vec![rel]
                } else {
                    vec![]
                }
            })
            .collect();
        for part in parts {
            out.extend(part);
        }
    }
}

/// The `ignored_paths` of a `.hhconfig` (OCaml `Str` regular expressions) as
/// Rust regular expressions that match where `Str.string_match re path 0`
/// does: at the start of the path.
pub fn ignored_path_regexes(patterns: &[String]) -> anyhow::Result<Vec<Regex>> {
    patterns
        .iter()
        .map(|p| Ok(Regex::new(&format!("^(?:{})", str_regex_to_rust(p)?))?))
        .collect()
}

/// Translates the syntax of OCaml's `Str` regular expressions to that of the
/// `regex` crate. In `Str`, `\(`, `\)` and `\|` group and alternate while
/// `(`, `)`, `|`, `{` and `}` are ordinary characters, and a backslash in a
/// character class is an ordinary character.
fn str_regex_to_rust(pattern: &str) -> anyhow::Result<String> {
    let mut out = String::with_capacity(pattern.len() + 8);
    let mut chars = pattern.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' => match chars.next() {
                Some('(') => out.push('('),
                Some(')') => out.push(')'),
                Some('|') => out.push('|'),
                Some('b') => out.push_str("\\b"),
                Some(d) if d.is_ascii_digit() => {
                    anyhow::bail!("back-references are not supported: {pattern}")
                }
                Some(other) => out.push_str(&regex::escape(&other.to_string())),
                None => out.push_str("\\\\"),
            },
            '(' | ')' | '|' | '{' | '}' => {
                out.push('\\');
                out.push(c);
            }
            '[' => {
                out.push('[');
                if chars.peek() == Some(&'^') {
                    out.push('^');
                    chars.next();
                }
                // A `]` first in the class is one of its characters.
                if chars.peek() == Some(&']') {
                    out.push_str("\\]");
                    chars.next();
                }
                loop {
                    match chars.next() {
                        Some(']') => {
                            out.push(']');
                            break;
                        }
                        Some(c @ ('\\' | '[' | '&' | '~')) => {
                            out.push('\\');
                            out.push(c);
                        }
                        Some(c) => out.push(c),
                        None => anyhow::bail!("unterminated character class: {pattern}"),
                    }
                }
            }
            c => out.push(c),
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hack_files() {
        assert!(is_hack_file(Path::new("a/b.php")));
        assert!(is_hack_file(Path::new("a/b.hackpartial")));
        assert!(is_hack_file(Path::new("a/b.xhp")));
        assert!(!is_hack_file(Path::new("a/.b.php")));
        assert!(!is_hack_file(Path::new("a/b.js")));
        assert!(!is_hack_file(Path::new("a/php")));
        assert!(!is_hack_file(Path::new("a/bphp")));
    }

    #[test]
    fn str_regexes() {
        let res = ignored_path_regexes(&[
            "^[.]claude/worktrees/".to_string(),
            "js/\\(a\\|b\\)/".to_string(),
            "x(y)|z".to_string(),
        ])
        .unwrap();
        assert!(res[0].is_match(".claude/worktrees/x.php"));
        assert!(!res[0].is_match("a/.claude/worktrees/x.php"));
        assert!(res[1].is_match("js/a/x.php"));
        assert!(res[1].is_match("js/b/x.php"));
        assert!(!res[1].is_match("x/js/a/x.php"));
        assert!(res[2].is_match("x(y)|z/q.php"));
        assert!(!res[2].is_match("xy/q.php"));
    }
}
