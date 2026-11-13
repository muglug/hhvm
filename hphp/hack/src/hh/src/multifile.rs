// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the parts of `utils/multifile.ml` that the typechecker uses.
//!
//! The `multifile_rust` crate (used by hackc) splits multifiles too, but not
//! the way the OCaml does: it recognises a multifile with a `////` line
//! anywhere, keeps the newline before each `////` line in the previous part,
//! lets the header swallow blank lines after it, and treats two consecutive
//! header lines as two files. `hh single` has to split exactly as
//! `hh_single_type_check` did, since positions end up in the `.exp` files, so
//! the OCaml splitting is ported here.

/// `Multifile.strip_multifile_prefix`: reduces a multifile-test path
/// `<container>--<simulated/path.php>` to the path it simulates. The OCaml
/// removes the first match of the anchored, greedy `^.*--`, which is
/// everything up to the last `--`.
pub fn strip_multifile_prefix(path: &str) -> String {
    match path.rfind("--") {
        Some(i) => path[i + 2..].to_string(),
        None => path.to_string(),
    }
}

/// `Multifile.file_to_file_list` on the `content` of the file `path`: the
/// files the test simulates, with their paths and contents.
///
/// - A file starting with a `////` line is a series of parts, each introduced
///   by a `//// name` line: part `name` is `<path>--name`, or `rest` for a
///   name `~root/rest`.
/// - A file starting with `// @directory DIR [@file NAME]` is one file, moved
///   to `DIR/NAME` (`DIR/<path>` without `@file`), without its first line.
/// - Any other file is itself.
pub fn file_to_file_list(path: &str, content: &[u8]) -> Vec<(String, Vec<u8>)> {
    file_to_file_list_rooted(path, content)
        .into_iter()
        .map(|(_rooted, sub, c)| (sub, c))
        .collect()
}

/// [`file_to_file_list`], with whether each part is a `~root/` one: the
/// OCaml names those `Relative_path.from_root ~suffix` (a path under the
/// root), and the others by the path of the file.
pub fn file_to_file_list_rooted(path: &str, content: &[u8]) -> Vec<(bool, String, Vec<u8>)> {
    // `Str.string_match (Str.regexp "////.*\n") content 0`.
    if content.starts_with(b"////") && content[4..].contains(&b'\n') {
        return split_multifile_content(content)
            .into_iter()
            .map(|(sub, c)| match sub.strip_prefix("~root/") {
                Some(suffix) => (true, suffix.to_string(), c),
                None => (false, format!("{path}--{sub}"), c),
            })
            .collect();
    }
    file_to_file_list_unrooted(path, content)
        .into_iter()
        .map(|(sub, c)| (false, sub, c))
        .collect()
}

fn file_to_file_list_unrooted(path: &str, content: &[u8]) -> Vec<(String, Vec<u8>)> {
    if content.starts_with(b"// @directory ") {
        let first_end = content.iter().position(|&c| c == b'\n');
        let first_line = &content[..first_end.unwrap_or(content.len())];
        // `Str.split (Str.regexp "\n")` drops one trailing newline; the
        // lines after the first are joined back.
        let mut rest: &[u8] = match first_end {
            Some(i) => &content[i + 1..],
            None => b"",
        };
        if let Some(r) = rest.strip_suffix(b"\n") {
            rest = r;
        }
        let (dir, file) = parse_directory_line(first_line);
        let file = file.unwrap_or_else(|| path.to_string());
        return vec![(join_path(&dir, &file), rest.to_vec())];
    }
    vec![(path.to_string(), content.to_vec())]
}

/// `Multifile.read_file_from_multifile`: for a path of the form
/// `sample/file/name.php--another/file/name.php`, the lines of the part
/// `another/file/name.php` of the multifile `sample/file/name.php`; no lines
/// if the path has no `.php--`, or the multifile has no such part.
///
/// The OCaml reads the multifile with `Sys_utils.cat`, whose `Sys_error`
/// (an unreadable file) its caller (`Diagnostics.read_lines`) catches and
/// turns into no lines: here that is the `Err`.
pub fn read_file_from_multifile(path: &str) -> std::io::Result<Vec<String>> {
    let splitter = ".php--";
    let Some(ix) = path.find(splitter) else {
        return Ok(vec![]);
    };
    let abs_fn = &path[..ix + ".php".len()];
    let content = std::fs::read(abs_fn)?;
    // Parts are named `<abs_fn>--<name>` (or are root-relative, for
    // `~root/` names, which then cannot contain `.php--` and so cannot be
    // `path`).
    Ok(file_to_file_list(abs_fn, &content)
        .into_iter()
        .find(|(name, _)| name == path)
        .map_or_else(Vec::new, |(_, content)| {
            str_split_newlines(&String::from_utf8_lossy(&content))
        }))
}

/// `Str.split (Str.regexp "\n") s`: a newline at the very start is skipped,
/// and the text after the last newline is the last line (nothing if the text
/// ends with one), but two newlines in a row give an empty line.
fn str_split_newlines(s: &str) -> Vec<String> {
    let s = s.strip_prefix('\n').unwrap_or(s);
    let mut lines: Vec<String> = s.split('\n').map(str::to_string).collect();
    if s.is_empty() || s.ends_with('\n') {
        lines.pop();
    }
    lines
}

/// `Multifile.split_multifile_content`: `Str.full_split` of `"\n" ^ content`
/// on `\n////.*\n`, each delimiter naming the text after it.
fn split_multifile_content(content: &[u8]) -> Vec<(String, Vec<u8>)> {
    let mut text = Vec::with_capacity(content.len() + 1);
    text.push(b'\n');
    text.extend_from_slice(content);
    enum Piece {
        Delim(usize, usize),
        Text(usize, usize),
    }
    let mut pieces = vec![];
    let mut start = 0;
    while start < text.len() {
        // The leftmost match: the first `\n////` that a newline follows (if
        // the first has none after it, no later one has).
        let found = find(&text[start..], b"\n////").and_then(|p| {
            let p = start + p;
            find(&text[p + 5..], b"\n").map(|q| (p, p + 5 + q + 1))
        });
        match found {
            None => {
                pieces.push(Piece::Text(start, text.len()));
                break;
            }
            Some((p, end)) => {
                if p > start {
                    pieces.push(Piece::Text(start, p));
                }
                pieces.push(Piece::Delim(p, end));
                start = end;
            }
        }
    }
    let mut files = vec![];
    let mut pieces = pieces.into_iter().peekable();
    while let Some(piece) = pieces.next() {
        match piece {
            Piece::Delim(h0, h1) => {
                let name = file_name_of_header(&text[h0..h1]);
                let body = match pieces.peek() {
                    Some(&Piece::Text(t0, t1)) => {
                        pieces.next();
                        text[t0..t1].to_vec()
                    }
                    _ => vec![],
                };
                files.push((name, body));
            }
            Piece::Text(t0, t1) => panic!(
                "unexpected split result `Text ({})`",
                String::from_utf8_lossy(&text[t0..t1])
            ),
        }
    }
    files
}

/// The name in a `\n//// name\n` header: without the `\n////`, the slashes
/// after it, and every space, `|` and newline.
fn file_name_of_header(header: &[u8]) -> String {
    let header = String::from_utf8_lossy(header).replace("\n////", "");
    header
        .trim_start_matches('/')
        .chars()
        .filter(|c| !matches!(c, ' ' | '|' | '\n'))
        .collect()
}

/// The groups of `^// @directory *\([^ ]*\) *\(@file *\([^ ]*\)*\)?` in the
/// first line: the directory, and the file name if there is an `@file`.
fn parse_directory_line(line: &[u8]) -> (String, Option<String>) {
    let line = String::from_utf8_lossy(line);
    let rest = line["// @directory ".len()..].trim_start_matches(' ');
    let dir_end = rest.find(' ').unwrap_or(rest.len());
    let dir = rest[..dir_end].to_string();
    let rest = rest[dir_end..].trim_start_matches(' ');
    let file = rest.strip_prefix("@file").map(|f| {
        let f = f.trim_start_matches(' ');
        f[..f.find(' ').unwrap_or(f.len())].to_string()
    });
    (dir, file)
}

/// `join_path` of `Multifile.file_to_file_list`: one `/` between the two.
fn join_path(p1: &str, p2: &str) -> String {
    if p1.is_empty() || p2.is_empty() {
        return format!("{p1}{p2}");
    }
    match (p1.ends_with('/'), p2.starts_with('/')) {
        (true, true) => format!("{p1}{}", &p2[1..]),
        (false, false) => format!("{p1}/{p2}"),
        _ => format!("{p1}{p2}"),
    }
}

fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn split(s: &str) -> Vec<(String, String)> {
        file_to_file_list("t.php", s.as_bytes())
            .into_iter()
            .map(|(p, c)| (p, String::from_utf8(c).unwrap()))
            .collect()
    }

    fn owned(v: &[(&str, &str)]) -> Vec<(String, String)> {
        v.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect()
    }

    #[test]
    fn splits_like_the_ocaml() {
        assert_eq!(
            split("//// a.php\n<?hh\nA\n//// b.php\n<?hh\nB\n"),
            owned(&[("t.php--a.php", "<?hh\nA"), ("t.php--b.php", "<?hh\nB\n")])
        );
        // Blank lines after a header belong to the part.
        assert_eq!(
            split("//// a.php\n\n<?hh\n"),
            owned(&[("t.php--a.php", "\n<?hh\n")])
        );
        // The second of two consecutive headers is text of the first part.
        assert_eq!(
            split("//// a.php\n//// b.php\nB"),
            owned(&[("t.php--a.php", "//// b.php\nB")])
        );
        // A header last in the file names an empty part.
        assert_eq!(
            split("//// a.php\nA\n//// b.php\n"),
            owned(&[("t.php--a.php", "A"), ("t.php--b.php", "")])
        );
        // Spaces and extra slashes go from names; `~root/` names are rooted.
        assert_eq!(
            split("///// my file.php \nA\n//// ~root/x/y.php\nB"),
            owned(&[("t.php--myfile.php", "A"), ("x/y.php", "B")])
        );
        // Only a file that starts with `////` is a multifile.
        assert_eq!(
            split("<?hh\n//// a.php\nA\n"),
            owned(&[("t.php", "<?hh\n//// a.php\nA\n")])
        );
    }

    #[test]
    fn str_split_like_ocaml() {
        let v = |xs: &[&str]| xs.iter().map(|x| x.to_string()).collect::<Vec<_>>();
        assert_eq!(str_split_newlines("a\n\nb\n"), v(&["a", "", "b"]));
        assert_eq!(str_split_newlines("\n\na"), v(&["", "a"]));
        assert_eq!(str_split_newlines(""), v(&[]));
        assert_eq!(str_split_newlines("\n"), v(&[]));
        assert_eq!(str_split_newlines("a"), v(&["a"]));
    }

    #[test]
    fn reads_a_part_of_a_multifile() {
        let dir = std::env::temp_dir().join(format!("hh_multifile_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("t.php");
        std::fs::write(&file, "//// a.php\n<?hh\nA\n//// b.php\n<?hh\nB\n").unwrap();
        let file = file.to_str().unwrap().to_string();
        assert_eq!(
            read_file_from_multifile(&format!("{file}--b.php")).unwrap(),
            vec!["<?hh".to_string(), "B".to_string()]
        );
        assert!(read_file_from_multifile(&format!("{file}--c.php")).unwrap().is_empty());
        assert!(read_file_from_multifile(&file).unwrap().is_empty());
        assert!(read_file_from_multifile("/nonexistent/x.php--a.php").is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn directory_files() {
        assert_eq!(
            split("// @directory foo/bar @file x.php\n<?hh\nA\n\n"),
            owned(&[("foo/bar/x.php", "<?hh\nA\n")])
        );
        assert_eq!(
            split("// @directory foo/\n<?hh\n"),
            owned(&[("foo/t.php", "<?hh")])
        );
    }

    #[test]
    fn strips_up_to_the_last_separator() {
        assert_eq!(strip_multifile_prefix("a/b.php--c/d.php"), "c/d.php");
        assert_eq!(strip_multifile_prefix("a--b--c.php"), "c.php");
        assert_eq!(strip_multifile_prefix("plain.php"), "plain.php");
    }
}
