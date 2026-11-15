// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/string/string_utils.ml`. See `hh/PORTING.md`.
//!
//! The functions of `string_utils.ml` that the typechecker uses. OCaml
//! strings are bytes: lengths, indices and edit distances are in bytes here
//! too.

/// Return a copy of the string with prefixing string removed.
/// The function is a no-op if it s does not start with prefix.
/// Modeled after Python's string.lstrip.
pub fn lstrip<'a>(s: &'a str, prefix: &str) -> &'a str {
    s.strip_prefix(prefix).unwrap_or(s)
}

/// If s is longer than length len, return a copy of s truncated to length
/// len.
///
/// (Bytes, as in OCaml. Where OCaml cuts a character in two, the bytes that
/// are left of it become U+FFFD: a `String` cannot hold them.)
pub fn truncate(len: isize, s: &str) -> String {
    if s.len() as isize <= len {
        s.to_string()
    } else {
        // `String.sub s ~pos:0 ~len`
        if len < 0 {
            panic!("Invalid_argument: pos + len past end: 0 + {} > {}", len, s.len());
        }
        String::from_utf8_lossy(&s.as_bytes()[..len as usize]).into_owned()
    }
}

/// Splits a string into a list of strings using "\n", "\r" or "\r\n" as
/// delimiters. If the string starts or ends with a delimiter, there WILL be an
/// empty string at the beginning or end of the list, like Str.split_delim does
pub fn split_into_lines(str: &str) -> Vec<String> {
    let bytes = str.as_bytes();
    let mut start = 0;
    let mut lines: Vec<(usize, usize)> = vec![];
    for (idx, &c) in bytes.iter().enumerate() {
        // For \r\n, we've already processed the newline
        if c == b'\n' && idx > 0 && bytes[idx - 1] == b'\r' {
            start = idx + 1;
        } else if c == b'\n' || c == b'\r' {
            lines.push((start, idx - start));
            start = idx + 1;
        }
    }
    lines.push((start, bytes.len() - start));
    lines
        .into_iter()
        .map(|(start, len)| str[start..start + len].to_string())
        .collect()
}

/// Splits a string into lines, indents each non-empty line, and concats with
/// newlines
pub fn indent(indent_size: isize, str: &str) -> String {
    // `String.make` raises on a negative length.
    if indent_size < 0 {
        panic!("Invalid_argument: String.make");
    }
    let padding = " ".repeat(indent_size as usize);
    split_into_lines(str)
        .into_iter()
        .map(|str| {
            if str.is_empty() {
                String::new()
            } else {
                format!("{}{}", padding, str)
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Splits a string into a list of strings using only "\n" as a delimiter.
/// If the string ends with a delimiter, an empty string representing the
/// contents after the final delimiter is NOT included (unlike
/// Str.split_delim).
pub fn split_on_newlines(content: &str) -> Vec<String> {
    // `Str.split_delim` of the empty string is the empty list.
    if content.is_empty() {
        return vec![];
    }
    let mut lines: Vec<String> = content.split('\n').map(str::to_string).collect();
    // don't create a list entry for the line after a trailing newline
    if lines.last().is_some_and(|line| line.is_empty()) {
        lines.pop();
    }
    lines
}

/// Levenshtein distance algorithm.
///
/// `upper_bound` defaults to `Int.max_value`. The distances that reach it
/// are all reported as `upper_bound`.
pub fn levenshtein_distance(upper_bound: Option<isize>, xs: &str, ys: &str) -> isize {
    let upper_bound = upper_bound.unwrap_or(isize::MAX);
    let xs = xs.as_bytes();
    let ys = ys.as_bytes();
    let xs_len = xs.len();
    let ys_len = ys.len();
    // `d i j`, row by row. OCaml computes the same values on demand (the
    // function is memoized and has no effect).
    let mut prev: Vec<isize> = (0..=ys_len as isize).collect();
    for i in 1..=xs_len {
        let mut row: Vec<isize> = Vec::with_capacity(ys_len + 1);
        row.push(i as isize);
        for j in 1..=ys_len {
            let upleft = prev[j - 1];
            let res = if upleft >= upper_bound {
                upper_bound
            } else {
                // `abs (Char.compare xs.[i'] ys.[j'])`: `Base.Char.compare`
                // is -1, 0 or 1.
                let cost = if xs[i - 1] == ys[j - 1] { 0 } else { 1 };
                let upleft = upleft + cost;
                if upleft >= upper_bound {
                    upper_bound
                } else {
                    (prev[j] + 1).min(row[j - 1] + 1).min(upleft)
                }
            };
            row.push(res);
        }
        prev = row;
    }
    prev[ys_len].min(upper_bound)
}

/// The candidate whose name (given by `f`) is the closest to `name`, among
/// those within `max_edit_distance` of it. The first one, if several are
/// equally close.
pub fn most_similar<A: Clone>(
    max_edit_distance: Option<isize>,
    name: &str,
    candidates: &[A],
    f: impl Fn(&A) -> String,
) -> Option<A> {
    // Compare strings case-insensitively.
    let name = name.to_ascii_lowercase();
    let f = |x: &A| f(x).to_ascii_lowercase();

    let max_distance = match max_edit_distance {
        Some(n) => n,
        None => isize::MAX,
    };
    let upper_bound = match max_edit_distance {
        // 10 was a pre-existing hard-coded upper bound "optimization"
        // Distances >= 10 are indistinguishable, so we may return a candidate
        // whose true edit distance exceeds 10 if no closer match exists.
        // Keeping so we don't change behavior
        Some(n) => n.wrapping_add(1).min(10),
        None => 10,
    };
    let distance = |xs: &str, ys: &str| levenshtein_distance(Some(upper_bound), xs, ys);

    let mut best_candidate = None;
    let mut best_d = isize::MAX;
    for candidate in candidates {
        let d = distance(&f(candidate), &name);
        if d < best_d && d <= max_distance {
            best_candidate = Some(candidate);
            best_d = d;
        }
    }
    best_candidate.cloned()
}

/// The string that `Str.regexp (Char.escaped c)` matches, when it matches
/// one string literally: `Char.escaped` gives `c` itself for the printable
/// characters, and `\\`, `\'`, `\n`, `\t`, `\r` for the others it escapes,
/// which `Str` reads as the literal character after the backslash (so `\n`
/// matches `n`). `None` for the characters that are special in `Str`
/// (`$^.*+?[`), for `\b` (`Char.escaped` gives `\b`, a word boundary in
/// `Str`) and for the non-printable ones (`\ddd`, back-references).
fn str_literal_of_escaped_char(c: char) -> Option<char> {
    match c {
        '$' | '^' | '.' | '*' | '+' | '?' | '[' => None,
        '\\' | '\'' => Some(c),
        '\n' => Some('n'),
        '\t' => Some('t'),
        '\r' => Some('r'),
        ' '..='~' => Some(c),
        _ => None,
    }
}

/// `String_utils.split c s` (`Str.split (Str.regexp (Char.escaped c)) s`):
/// the pieces between the matches of the delimiter, skipping one at the very
/// start and without the empty piece after one at the end (`Str.split`).
pub fn split(c: char, s: &str) -> Vec<String> {
    let Some(delim) = str_literal_of_escaped_char(c) else {
        todo!(
            "String_utils.split: the delimiter {:?} is not a literal for Str (needs crate::rt::ocaml_str, which is server-only)",
            c
        )
    };
    let delim_len = delim.len_utf8();
    let mut start = if s.starts_with(delim) { delim_len } else { 0 };
    let mut accu = vec![];
    while start < s.len() {
        match s[start..].find(delim) {
            None => {
                accu.push(s[start..].to_string());
                break;
            }
            Some(i) => {
                accu.push(s[start..start + i].to_string());
                start = start + i + delim_len;
            }
        }
    }
    accu
}

/// `String_utils.split2 c s`: the two pieces of `split c s`, if there are
/// exactly two.
pub fn split2(c: char, s: &str) -> Option<(String, String)> {
    let parts = split(c, s);
    match parts.as_slice() {
        [first, second] => Some((first.clone(), second.clone())),
        _ => None,
    }
}

#[cfg(test)]
mod split_tests {
    use super::*;

    #[test]
    fn split2_as_in_ocaml() {
        assert_eq!(split2('=', "a=b"), Some(("a".to_string(), "b".to_string())));
        assert_eq!(split2('=', "a=b=c"), None);
        assert_eq!(split2('=', "=b"), None);
        assert_eq!(split2('=', "a="), None);
        assert_eq!(split2('=', "a==b"), None);
        assert_eq!(split2('=', "=a=b"), Some(("a".to_string(), "b".to_string())));
        assert_eq!(split2('=', "a=b="), Some(("a".to_string(), "b".to_string())));
        assert_eq!(split('=', ""), Vec::<String>::new());
        assert_eq!(split('\n', "anb"), vec!["a", "b"]);
    }
}

/// `String_utils.Incorrect_format`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IncorrectFormat;

/// `String_utils.split2_exn c s`: raises `Incorrect_format` unless `s`
/// splits in exactly two (`split2`).
pub fn split2_exn(c: char, s: &str) -> Result<(String, String), IncorrectFormat> {
    split2(c, s).ok_or(IncorrectFormat)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip_and_truncate() {
        assert_eq!(lstrip("foobar", "foo"), "bar");
        assert_eq!(lstrip("foobar", "bar"), "foobar");
        assert_eq!(lstrip("foofoobar", "foo"), "foobar");
        assert_eq!(lstrip("foo", ""), "foo");
        assert_eq!(truncate(3, "abcdef"), "abc");
        assert_eq!(truncate(6, "abcdef"), "abcdef");
        assert_eq!(truncate(10, "abcdef"), "abcdef");
        assert_eq!(truncate(0, "abcdef"), "");
    }

    #[test]
    fn lines() {
        let l = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        assert_eq!(split_into_lines(""), l(&[""]));
        assert_eq!(split_into_lines("a"), l(&["a"]));
        assert_eq!(split_into_lines("a\nb\r\nc\rd"), l(&["a", "b", "c", "d"]));
        assert_eq!(split_into_lines("\na\n"), l(&["", "a", ""]));
        assert_eq!(split_into_lines("a\r\n"), l(&["a", ""]));
        // `\n\r` is two delimiters; `\r\n` is one.
        assert_eq!(split_into_lines("a\n\rb"), l(&["a", "", "b"]));
        assert_eq!(split_into_lines("a\r\n\r\nb"), l(&["a", "", "b"]));

        assert_eq!(indent(2, "a\n\nb\n"), "  a\n\n  b\n");
        assert_eq!(indent(0, "a\r\nb"), "a\nb");
        assert_eq!(indent(8, ""), "");

        assert_eq!(split_on_newlines(""), l(&[]));
        assert_eq!(split_on_newlines("a"), l(&["a"]));
        assert_eq!(split_on_newlines("a\n"), l(&["a"]));
        assert_eq!(split_on_newlines("a\n\n"), l(&["a", ""]));
        assert_eq!(split_on_newlines("\n"), l(&[""]));
        assert_eq!(split_on_newlines("\na\r\nb"), l(&["", "a\r", "b"]));
    }

    #[test]
    fn levenshtein() {
        let d = |xs, ys| levenshtein_distance(None, xs, ys);
        assert_eq!(d("", ""), 0);
        assert_eq!(d("abc", ""), 3);
        assert_eq!(d("", "abc"), 3);
        assert_eq!(d("kitten", "sitting"), 3);
        assert_eq!(d("flaw", "lawn"), 2);
        assert_eq!(d("abc", "abc"), 0);
        // The cost of a substitution is 1 whatever the characters are.
        assert_eq!(d("a", "z"), 1);
        // With an upper bound, the distances that reach it are the bound.
        assert_eq!(levenshtein_distance(Some(2), "kitten", "sitting"), 2);
        assert_eq!(levenshtein_distance(Some(3), "kitten", "sitting"), 3);
        assert_eq!(levenshtein_distance(Some(10), "kitten", "sitting"), 3);
        assert_eq!(levenshtein_distance(Some(2), "abcdef", ""), 2);
        assert_eq!(levenshtein_distance(Some(0), "abc", "abc"), 0);
    }

    #[test]
    fn similar() {
        let candidates = ["foo", "Bar", "bazz", "baz"];
        let f = |s: &&str| s.to_string();
        // Case-insensitive, and the first of the closest candidates.
        assert_eq!(most_similar(None, "BAR", &candidates, f), Some("Bar"));
        assert_eq!(most_similar(None, "ba", &candidates, f), Some("Bar"));
        assert_eq!(most_similar(None, "bazzz", &candidates, f), Some("bazz"));
        // Without a maximum, anything is similar: distances are capped at 10.
        assert_eq!(
            most_similar(None, "completely_different_name", &candidates, f),
            Some("foo")
        );
        assert_eq!(most_similar(Some(1), "qux", &candidates, f), None);
        assert_eq!(most_similar(Some(2), "fxx", &candidates, f), Some("foo"));
        assert_eq!(most_similar(Some(1), "fxx", &candidates, f), None);
        assert_eq!(most_similar(Some(0), "FOO", &candidates, f), Some("foo"));
        assert_eq!(most_similar::<&str>(None, "x", &[], f), None);
    }
}
