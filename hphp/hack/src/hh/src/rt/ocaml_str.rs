// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of OCaml's `Str` library (`otherlibs/str/str.ml`): its regular
//! expressions, as far as the server layer
//! needs them. See `hh/PORTING.md`, "The server layer".
//!
//! [`regexp`] parses the syntax of `Str.regexp` exactly as `str.ml` does
//! (same constructs, same `Failure` messages) and translates the result to a
//! `regex::bytes::Regex` with Unicode off, so that, as in OCaml, a pattern
//! and the strings it is matched against are bytes. The matching functions
//! only report whether, and where, a match starts; for that, the leftmost
//! match of the `regex` crate and the backtracking matcher of `Str` agree.
//!
//! Where they do not agree:
//!
//! - `\1` .. `\9` (back-references) have no `regex` equivalent: [`regexp`]
//!   stops with a `todo!` on them.
//! - `\b` uses the ASCII word characters (`[0-9A-Za-z_]`); `Str` also counts
//!   the Latin-1 letters `\xC0`..`\xFF` (except `\xD7` and `\xF7`).

use std::fmt;

/// `Str.regexp`: a compiled regular expression.
///
/// It is serialised as its source (the string given to [`regexp`]), and
/// compiled again when it is deserialised.
#[derive(Clone)]
pub struct Regexp {
    source: String,
    re: regex::bytes::Regex,
}

impl fmt::Debug for Regexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Regexp").field(&self.source).finish()
    }
}

impl serde::Serialize for Regexp {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.source)
    }
}

impl<'de> serde::Deserialize<'de> for Regexp {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let source = String::deserialize(deserializer)?;
        regexp(&source).map_err(|Failure(message)| serde::de::Error::custom(message))
    }
}

/// The exception `Failure` that `Str.regexp` raises on a malformed regular
/// expression, with its message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure(pub String);

/// `Str.regexp`: compile a regular expression. The following constructs are
/// recognized:
///
/// - `.` matches any character except newline.
/// - `*` (postfix) matches the preceding expression zero, one or several
///   times
/// - `+` (postfix) matches the preceding expression one or several times
/// - `?` (postfix) matches the preceding expression once or not at all
/// - `[..]` character set. Ranges are denoted with `-`, as in `[a-z]`. An
///   initial `^`, as in `[^0-9]`, complements the set. To include a `]`
///   character in a set, make it the first character of the set. To include
///   a `-` character in a set, make it the first or the last character of
///   the set.
/// - `^` matches at beginning of line: either at the beginning of the
///   matched string, or just after a `'\n'` character.
/// - `$` matches at end of line: either at the end of the matched string, or
///   just before a `'\n'` character.
/// - `\|` (infix) alternative between two expressions.
/// - `\(..\)` grouping and naming of the enclosed expression.
/// - `\1` the text matched by the first `\(...\)` expression (`\2` for the
///   second expression, and so on up to `\9`).
/// - `\b` matches word boundaries.
/// - `\` quotes special characters. The special characters are
///   `$^\.*+?[]`.
pub fn regexp(s: &str) -> Result<Regexp, Failure> {
    let parsed = parse(s.as_bytes())?;
    let mut pattern = String::from("(?-u)");
    emit(&parsed, &mut pattern);
    match regex::bytes::Regex::new(&pattern) {
        Ok(re) => Ok(Regexp {
            source: s.to_string(),
            re,
        }),
        // Every regular expression that `parse` accepts translates to a valid
        // `regex` pattern; a pattern too big for the `regex` crate is the
        // only way to get here.
        Err(e) => panic!("Str.regexp: {s:?} cannot be compiled by the regex crate: {e}"),
    }
}

/// `Str.search_forward r s start` searches the string `s` for a substring
/// matching the regular expression `r`. The search starts at position `start`
/// and proceeds towards the end of the string. Return the position of the
/// first character of the matched substring, or `None` where `Str` raises
/// `Not_found` (no substring matches).
///
/// Panics as `Str` raises `Invalid_argument` when `start` is not a valid
/// position in `s`.
pub fn search_forward(r: &Regexp, s: &str, start: usize) -> Option<usize> {
    if start > s.len() {
        panic!("Invalid_argument: Str.search_forward");
    }
    r.re.find_at(s.as_bytes(), start).map(|m| m.start())
}

/// `Str.string_match r s start` tests whether a substring of `s` that starts
/// at position `start` matches the regular expression `r`.
///
/// Panics as `Str` raises `Invalid_argument` when `start` is not a valid
/// position in `s`.
pub fn string_match(r: &Regexp, s: &str, start: usize) -> bool {
    if start > s.len() {
        panic!("Invalid_argument: Str.string_match");
    }
    // The leftmost match from `start` starts at `start` exactly when some
    // match starts there.
    r.re.find_at(s.as_bytes(), start)
        .is_some_and(|m| m.start() == start)
}

// ~~ The parser of `str.ml` ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// A set of bytes (`Charset.t`).
type Charset = [bool; 256];

/// `Str.regexp` (the abstract syntax of `str.ml`).
#[derive(Debug)]
enum Re {
    Char(u8),
    CharClass(Box<Charset>, bool),
    Seq(Vec<Re>),
    Alt(Box<Re>, Box<Re>),
    Star(Box<Re>),
    Plus(Box<Re>),
    Option(Box<Re>),
    Bol,
    Eol,
    Wordboundary,
    /// The group number is not used: the translation needs no captures.
    Group(#[allow(dead_code)] usize, Box<Re>),
    Refgroup(usize),
}

struct Parser<'a> {
    s: &'a [u8],
    group_counter: usize,
}

fn parse(s: &[u8]) -> Result<Re, Failure> {
    let mut p = Parser {
        s,
        group_counter: 1,
    };
    let (r, j) = p.regexp0(0)?;
    if j == s.len() {
        Ok(r)
    } else {
        Err(Failure("spurious \\) in regular expression".to_string()))
    }
}

impl Parser<'_> {
    fn len(&self) -> usize {
        self.s.len()
    }

    fn regexp0(&mut self, i: usize) -> Result<(Re, usize), Failure> {
        let (r, j) = self.regexp1(i)?;
        self.regexp0cont(r, j)
    }

    fn regexp0cont(&mut self, r1: Re, i: usize) -> Result<(Re, usize), Failure> {
        if i + 2 <= self.len() && self.s[i] == b'\\' && self.s[i + 1] == b'|' {
            let (r2, j) = self.regexp1(i + 2)?;
            self.regexp0cont(Re::Alt(Box::new(r1), Box::new(r2)), j)
        } else {
            Ok((r1, i))
        }
    }

    fn regexp1(&mut self, i: usize) -> Result<(Re, usize), Failure> {
        self.regexp1cont(vec![], i)
    }

    fn regexp1cont(&mut self, mut sq: Vec<Re>, mut i: usize) -> Result<(Re, usize), Failure> {
        loop {
            if i >= self.len()
                || (i + 2 <= self.len()
                    && self.s[i] == b'\\'
                    && (self.s[i + 1] == b'|' || self.s[i + 1] == b')'))
            {
                // `Seq (List.rev sq)`: `sq` is in order here.
                return Ok((Re::Seq(sq), i));
            }
            let (r, j) = self.regexp2(i)?;
            sq.push(r);
            i = j;
        }
    }

    fn regexp2(&mut self, i: usize) -> Result<(Re, usize), Failure> {
        let (r, j) = self.regexp3(i)?;
        Ok(self.regexp2cont(r, j))
    }

    fn regexp2cont(&mut self, mut r: Re, mut i: usize) -> (Re, usize) {
        loop {
            if i >= self.len() {
                return (r, i);
            }
            r = match self.s[i] {
                b'?' => Re::Option(Box::new(r)),
                b'*' => Re::Star(Box::new(r)),
                b'+' => Re::Plus(Box::new(r)),
                _ => return (r, i),
            };
            i += 1;
        }
    }

    fn regexp3(&mut self, i: usize) -> Result<(Re, usize), Failure> {
        match self.s[i] {
            b'\\' => self.regexpbackslash(i + 1),
            b'[' => {
                let (c, compl, j) = self.regexpclass0(i + 1)?;
                Ok((Re::CharClass(c, compl), j))
            }
            b'^' => Ok((Re::Bol, i + 1)),
            b'$' => Ok((Re::Eol, i + 1)),
            b'.' => {
                // `dotclass`: every character but newline.
                let mut c = Box::new([true; 256]);
                c[b'\n' as usize] = false;
                Ok((Re::CharClass(c, false), i + 1))
            }
            c => Ok((Re::Char(c), i + 1)),
        }
    }

    fn regexpbackslash(&mut self, i: usize) -> Result<(Re, usize), Failure> {
        if i >= self.len() {
            return Ok((Re::Char(b'\\'), i));
        }
        match self.s[i] {
            // `regexp1cont` stops before these.
            b'|' | b')' => panic!("Assert_failure: str.ml"),
            b'(' => {
                let group_no = self.group_counter;
                self.group_counter += 1;
                let (r, j) = self.regexp0(i + 1)?;
                if j + 1 < self.len() && self.s[j] == b'\\' && self.s[j + 1] == b')' {
                    Ok((Re::Group(group_no, Box::new(r)), j + 2))
                } else {
                    Err(Failure("\\( group not closed by \\)".to_string()))
                }
            }
            c @ b'1'..=b'9' => Ok((Re::Refgroup((c - b'0') as usize), i + 1)),
            b'b' => Ok((Re::Wordboundary, i + 1)),
            c => Ok((Re::Char(c), i + 1)),
        }
    }

    fn regexpclass0(&mut self, i: usize) -> Result<(Box<Charset>, bool, usize), Failure> {
        if i < self.len() && self.s[i] == b'^' {
            let (c, j) = self.regexpclass1(i + 1)?;
            Ok((c, true, j))
        } else {
            let (c, j) = self.regexpclass1(i)?;
            Ok((c, false, j))
        }
    }

    fn regexpclass1(&mut self, i: usize) -> Result<(Box<Charset>, usize), Failure> {
        let mut c = Box::new([false; 256]);
        let j = self.regexpclass2(&mut c, i, i)?;
        Ok((c, j))
    }

    fn regexpclass2(
        &mut self,
        c: &mut Charset,
        start: usize,
        mut i: usize,
    ) -> Result<usize, Failure> {
        loop {
            if i >= self.len() {
                return Err(Failure("[ class not closed by ]".to_string()));
            }
            if self.s[i] == b']' && i > start {
                return Ok(i + 1);
            }
            let c1 = self.s[i];
            if i + 2 < self.len() && self.s[i + 1] == b'-' && self.s[i + 2] != b']' {
                let c2 = self.s[i + 2];
                // `Charset.add_range`: nothing when `c1 > c2`.
                for b in c1..=c2 {
                    c[b as usize] = true;
                }
                i += 3;
            } else {
                c[c1 as usize] = true;
                i += 1;
            }
        }
    }
}

// ~~ Translation to the syntax of the `regex` crate ~~~~~~~~~~~~~~~~~~~~~~~~~

fn push_byte(out: &mut String, b: u8) {
    out.push_str(&format!("\\x{b:02X}"));
}

fn emit(re: &Re, out: &mut String) {
    match re {
        Re::Char(c) => push_byte(out, *c),
        Re::CharClass(set, compl) => {
            // The bytes of the class (`Charset.complement` applied), so that
            // a class with no byte, which `[]` cannot express, is
            // `[^\x00-\xFF]`.
            let set: Vec<bool> = set.iter().map(|b| *b != *compl).collect();
            if !set.contains(&true) {
                out.push_str("[^\\x00-\\xFF]");
                return;
            }
            out.push('[');
            let mut b = 0usize;
            while b < 256 {
                if set[b] {
                    let first = b;
                    while b + 1 < 256 && set[b + 1] {
                        b += 1;
                    }
                    push_byte(out, first as u8);
                    if b > first {
                        out.push('-');
                        push_byte(out, b as u8);
                    }
                }
                b += 1;
            }
            out.push(']');
        }
        Re::Seq(l) => {
            out.push_str("(?:");
            for r in l {
                emit(r, out);
            }
            out.push(')');
        }
        Re::Alt(r1, r2) => {
            out.push_str("(?:");
            emit(r1, out);
            out.push('|');
            emit(r2, out);
            out.push(')');
        }
        Re::Star(r) => {
            out.push_str("(?:");
            emit(r, out);
            out.push_str(")*");
        }
        Re::Plus(r) => {
            out.push_str("(?:");
            emit(r, out);
            out.push_str(")+");
        }
        Re::Option(r) => {
            out.push_str("(?:");
            emit(r, out);
            out.push_str(")?");
        }
        Re::Bol => out.push_str("(?m:^)"),
        Re::Eol => out.push_str("(?m:$)"),
        Re::Wordboundary => out.push_str("\\b"),
        Re::Group(_, r) => {
            out.push_str("(?:");
            emit(r, out);
            out.push(')');
        }
        Re::Refgroup(n) => {
            todo!("Str.regexp: the back-reference \\{n} has no equivalent in the regex crate")
        }
    }
}

/// `Str.split (Str.regexp delim) s` for a literal delimiter: the pieces
/// between the delimiters, skipping one delimiter at the very start and
/// nothing after the last one (`"a::b:"` split on `":"` is `["a"; ""; "b"]`).
pub fn split(delim: &str, s: &str) -> Vec<String> {
    let mut start = if s.starts_with(delim) { delim.len() } else { 0 };
    let mut pieces = vec![];
    while start < s.len() {
        match s[start..].find(delim) {
            None => {
                pieces.push(s[start..].to_string());
                break;
            }
            Some(i) => {
                pieces.push(s[start..start + i].to_string());
                start = start + i + delim.len();
            }
        }
    }
    pieces
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Str.split (Str.regexp d)`: one delimiter skipped at the start, none
    /// kept at the end, empty pieces in between.
    #[test]
    fn split_on_longer_delimiters() {
        assert_eq!(split(":", "a.php:1:2"), vec!["a.php", "1", "2"]);
        assert_eq!(split(":", ":a::b:"), vec!["a", "", "b"]);
        assert_eq!(split(":", ""), Vec::<String>::new());
        assert_eq!(split("::", "C::m"), vec!["C", "m"]);
        assert_eq!(split("::", "\\N\\C"), vec!["\\N\\C"]);
    }

    #[test]
    fn str_split_as_in_ocaml() {
        assert_eq!(split("|", "a|b"), vec!["a", "b"]);
        assert_eq!(split("|", "|a|b|"), vec!["a", "b"]);
        assert_eq!(split("|", "a||b"), vec!["a", "", "b"]);
        assert_eq!(split("|", ""), Vec::<String>::new());
        assert_eq!(split("|", "|"), Vec::<String>::new());
        assert_eq!(split("|", "||"), vec![""]);
        assert_eq!(split("|", "bogus"), vec!["bogus"]);
    }

    fn re(s: &str) -> Regexp {
        regexp(s).unwrap()
    }

    fn search(r: &str, s: &str) -> Option<usize> {
        search_forward(&re(r), s, 0)
    }

    #[test]
    fn literals_and_specials() {
        assert_eq!(search("b", "abc"), Some(1));
        assert_eq!(search("x", "abc"), None);
        assert_eq!(search("", "abc"), Some(0));
        // `(`, `)`, `|`, `{`, `}` are ordinary characters.
        assert_eq!(search("a(b)|c{2}", "xa(b)|c{2}"), Some(1));
        assert_eq!(search("a(b)|c", "ab"), None);
        // `\.` quotes; `\n` (backslash, n) is an `n`.
        assert_eq!(search("a\\.b", "axb a.b"), Some(4));
        assert_eq!(search("\\n", "a\nn"), Some(2));
        // A trailing backslash is a backslash.
        assert_eq!(search("a\\", "xa\\"), Some(1));
        // `.` does not match a newline.
        assert_eq!(search("a.b", "a\nb"), None);
        assert_eq!(search("a.b", "a\tb"), Some(0));
        // A postfix operator at the start is an ordinary character.
        assert_eq!(search("*a", "b*a"), Some(1));
        assert_eq!(search("+", "a+"), Some(1));
        assert_eq!(search("ab*c", "ac"), Some(0));
        assert_eq!(search("ab+c", "ac"), None);
        assert_eq!(search("ab?c", "abc"), Some(0));
    }

    #[test]
    fn groups_and_alternatives() {
        assert_eq!(search("js/\\(a\\|b\\)/", "x/js/b/y"), Some(2));
        assert_eq!(search("js/\\(a\\|b\\)/", "x/js/c/y"), None);
        assert_eq!(search("a\\|b", "xxb"), Some(2));
        assert_eq!(search("\\(ab\\)*c", "ababc"), Some(0));
    }

    #[test]
    fn anchors() {
        assert_eq!(search("^b", "ab"), None);
        assert_eq!(search("^b", "a\nb"), Some(2));
        assert_eq!(search("a$", "ab"), None);
        assert_eq!(search("a$", "a\nb"), Some(0));
        // `^` and `$` are anchors anywhere in the expression.
        assert_eq!(search("a^b", "a^b"), None);
        assert_eq!(search("\\bfoo\\b", "a foo b"), Some(2));
        assert_eq!(search("\\bfoo\\b", "afoob"), None);
    }

    #[test]
    fn classes() {
        assert_eq!(search("[0-9]+", "ab12"), Some(2));
        assert_eq!(search("[^a-z]", "abC"), Some(2));
        // `]` first is a character of the set, `-` last too.
        assert_eq!(search("[]a]", "x]"), Some(1));
        assert_eq!(search("[a-]", "x-"), Some(1));
        // A complemented set matches a newline.
        assert_eq!(search("[^a]", "a\n"), Some(1));
        // `\` is ordinary in a set.
        assert_eq!(search("[\\]", "a\\"), Some(1));
        // A range whose ends are reversed is empty.
        assert_eq!(search("[z-a]", "abz"), None);
        assert_eq!(search("x[z-a]*y", "xy"), Some(0));
        // Its complement is every byte.
        assert_eq!(search("[^z-a]", "\n"), Some(0));
        assert_eq!(search("[.]claude/", "a/.claude/x"), Some(2));
    }

    #[test]
    fn bytes() {
        // Patterns and strings are bytes: `.` is one byte of `é`.
        assert_eq!(search("^..$", "é"), Some(0));
        assert_eq!(search("é", "café"), Some(3));
    }

    #[test]
    fn failures() {
        let fail = |s: &str| regexp(s).unwrap_err().0;
        assert_eq!(fail("[abc"), "[ class not closed by ]");
        assert_eq!(fail("[]"), "[ class not closed by ]");
        assert_eq!(fail("\\(ab"), "\\( group not closed by \\)");
        assert_eq!(fail("ab\\)"), "spurious \\) in regular expression");
    }

    #[test]
    fn match_at() {
        let r = re("b+");
        assert!(string_match(&r, "abb", 1));
        assert!(!string_match(&r, "abb", 0));
        assert_eq!(search_forward(&r, "abab", 2), Some(3));
        assert!(!string_match(&re("^b"), "ab", 1));
        assert!(string_match(&re("^b"), "a\nb", 2));
    }

    #[test]
    #[should_panic(expected = "Invalid_argument: Str.search_forward")]
    fn search_out_of_bounds() {
        search_forward(&re("a"), "a", 2);
    }

    #[test]
    fn serde_round_trip() {
        let r = re("js/\\(a\\|b\\)/");
        let json = serde_json::to_string(&r).unwrap();
        assert_eq!(json, "\"js/\\\\(a\\\\|b\\\\)/\"");
        let r2: Regexp = serde_json::from_str(&json).unwrap();
        assert_eq!(search_forward(&r2, "js/b/", 0), Some(0));
        assert!(serde_json::from_str::<Regexp>("\"[a\"").is_err());
    }
}

/// `Str.split (Str.regexp delim) s` for a `delim` that matches itself only
/// (no special character): the substrings between the delimiters; a
/// delimiter at the beginning of the string and one at its end are ignored.
pub fn split_literal<'a>(delim: &str, s: &'a str) -> Vec<&'a str> {
    let mut start = if !delim.is_empty() && s.starts_with(delim) { delim.len() } else { 0 };
    let mut accu = vec![];
    while start < s.len() {
        match s[start..].find(delim) {
            Some(i) => {
                accu.push(&s[start..start + i]);
                start += i + delim.len()
            }
            None => {
                accu.push(&s[start..]);
                break;
            }
        }
    }
    accu
}

#[cfg(test)]
mod split_literal_tests {
    use super::split_literal;

    /// The results of `Str.split (Str.regexp ...)` in OCaml.
    #[test]
    fn it_splits_as_str_split_does() {
        assert_eq!(split_literal("::", "A::b"), vec!["A", "b"]);
        assert_eq!(split_literal("::", "A"), vec!["A"]);
        assert_eq!(split_literal("::", ""), Vec::<&str>::new());
        // A delimiter at the beginning, and one at the end, are ignored.
        assert_eq!(split_literal("::", "::A::b::"), vec!["A", "b"]);
        // Two delimiters in a row give an empty string.
        assert_eq!(split_literal(":", "a::b"), vec!["a", "", "b"]);
        assert_eq!(split_literal(":", "f.php:1:2"), vec!["f.php", "1", "2"]);
        assert_eq!(split_literal("|", "Method|C::m"), vec!["Method", "C::m"]);
    }
}
