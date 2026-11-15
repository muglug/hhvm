// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the functions of `Base`'s `String` (`Core.String`) that the
//! ported modules use and that Rust's `str` has no method for.

/// `String.capitalize`: the first byte, if it is an ASCII lowercase letter,
/// in upper case.
pub fn capitalize(s: &str) -> String {
    let mut s = s.to_string();
    if let Some(first) = s.get_mut(0..1) {
        first.make_ascii_uppercase();
    }
    s
}

/// `String.split_lines` (Base): the lines without their `\n` or `\r\n`, and
/// no empty last line after a final newline. A last line that no `\n` ends
/// keeps a trailing `\r` (only `\r\n` is a line end).
pub fn split_lines_bytes(s: &[u8]) -> Vec<&[u8]> {
    if s.is_empty() {
        return vec![];
    }
    let mut pieces: Vec<&[u8]> = s.split(|&c| c == b'\n').collect();
    let last = pieces.pop().unwrap_or(b"");
    let mut lines: Vec<&[u8]> = pieces
        .into_iter()
        .map(|line| line.strip_suffix(b"\r").unwrap_or(line))
        .collect();
    if !last.is_empty() {
        lines.push(last);
    }
    lines
}

/// [`split_lines_bytes`] of a string.
pub fn split_lines(s: &str) -> Vec<String> {
    split_lines_bytes(s.as_bytes())
        .into_iter()
        .map(|l| String::from_utf8_lossy(l).into_owned())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_lines_is_that_of_base() {
        assert_eq!(split_lines_bytes(b""), Vec::<&[u8]>::new());
        assert_eq!(split_lines_bytes(b"a\n"), vec![b"a" as &[u8]]);
        assert_eq!(split_lines_bytes(b"a\n\nb"), vec![b"a" as &[u8], b"", b"b"]);
        assert_eq!(split_lines_bytes(b"a\r\nb\n"), vec![b"a" as &[u8], b"b"]);
        assert_eq!(split_lines_bytes(b"a\nb\r"), vec![b"a" as &[u8], b"b\r"]);
        assert_eq!(split_lines("\n"), vec![""]);
    }

    #[test]
    fn capitalize_is_that_of_base() {
        assert_eq!(capitalize(""), "");
        assert_eq!(capitalize("foo bar"), "Foo bar");
        assert_eq!(capitalize("Foo"), "Foo");
        assert_eq!(capitalize("éa"), "éa");
    }
}
