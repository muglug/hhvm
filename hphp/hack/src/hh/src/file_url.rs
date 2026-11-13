// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `File_url` (`utils/file_url/file_url.ml`). See `hh/PORTING.md`.
//!
//! File urls: https://tools.ietf.org/html/rfc8089
//! Related definitions: https://tools.ietf.org/html/rfc3986
//! Notes on UNC file urls and edge-cases:
//! https://foswiki.org/Support/Faq72
//! https://blogs.msdn.microsoft.com/ie/2006/12/06/file-uris-in-windows/
//! https://msdn.microsoft.com/en-us/library/windows/desktop/ff819129(v=vs.85).aspx
//!
//! The `Str` regular expressions are matched by hand; `failwith` is a panic
//! with the same message.

/// `percent_re`: `%\([0-9a-fA-F]?[0-9a-fA-F]?\)`, matched at `i`: the end of
/// the match.
fn percent_re(s: &[u8], i: usize) -> Option<usize> {
    if s.get(i) != Some(&b'%') {
        return None;
    }
    let mut end = i + 1;
    // Each `[0-9a-fA-F]?` takes a hex digit when there is one.
    for _ in 0..2 {
        if s.get(end).is_some_and(u8::is_ascii_hexdigit) {
            end += 1;
        }
    }
    Some(end)
}

/// `.*$` at `s`: `.` takes any character but a newline, and `$` matches
/// before a newline or at the end, so the group ends at the first newline.
fn dot_star_eol(s: &str) -> &str {
    &s[..s.find('\n').unwrap_or(s.len())]
}

/// `dos_url_re` (e.g. `c:\` or `z|/`): `^\([a-zA-Z]\)[:|]\([/\].*\)$`. Gives
/// the drive letter and the rest.
fn dos_url_re(s: &str) -> Option<(&str, &str)> {
    let b = s.as_bytes();
    if b.len() >= 3 && b[0].is_ascii_alphabetic() && matches!(b[1], b':' | b'|') && matches!(b[2], b'/' | b'\\') {
        Some((&s[0..1], dot_star_eol(&s[2..])))
    } else {
        None
    }
}

/// `url_re`: `^file://\([^/?#]*\)/\([^?#]*\)\(.*\)$`. Gives the host, the
/// path and the query and fragment. (A complemented set takes newlines; `.`
/// does not.)
fn url_re(uri: &str) -> Option<(&str, &str, &str)> {
    let rest = uri.strip_prefix("file://")?;
    let host_len = rest.find(|c| matches!(c, '/' | '?' | '#')).unwrap_or(rest.len());
    let host = &rest[..host_len];
    let rest = rest[host_len..].strip_prefix('/')?;
    let path_len = rest.find(|c| matches!(c, '?' | '#')).unwrap_or(rest.len());
    let path = &rest[..path_len];
    let query_fragment = dot_star_eol(&rest[path_len..]);
    Some((host, path, query_fragment))
}

/// `dos_re` (e.g. `c:\` or `z:/`): `^\([a-zA-Z]\):\([/\].*\)$`. Gives the
/// drive letter and the rest.
fn dos_re(s: &str) -> Option<(&str, &str)> {
    let b = s.as_bytes();
    if b.len() >= 3 && b[0].is_ascii_alphabetic() && b[1] == b':' && matches!(b[2], b'/' | b'\\') {
        Some((&s[0..1], dot_star_eol(&s[2..])))
    } else {
        None
    }
}

const PATH_SAFE_CHARS: &str =
    "/-._~!$&'()*+,;=@0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

/// `path_safe_chars`
pub fn path_safe_chars() -> &'static str {
    PATH_SAFE_CHARS
}

/// Unescapes %-escapes like "foo%4Abar", and normalizes path separators to `\`
/// on Windows.
///
/// Throws if there are incorrect %-escapes (not followed by two hex digits)
/// and for %-escapes that are outside 7-bit printable ascii.
pub fn decode(s: &str) -> String {
    // `Str.global_substitute percent_re subst s`
    let b = s.as_bytes();
    let mut res: Vec<u8> = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        match percent_re(b, i) {
            Some(end) => {
                let hex = &s[i + 1..end];
                if hex.len() != 2 {
                    panic!("incorrect %-escape in {}", s)
                }
                let code = u8::from_str_radix(hex, 16).unwrap();
                if !(32..=127).contains(&code) {
                    panic!("only 7bit ascii allowed in {}", s)
                }
                res.push(code);
                i = end;
            }
            None => {
                res.push(b[i]);
                i += 1;
            }
        }
    }
    // The escapes are ASCII, and what is between them comes from `s`.
    String::from_utf8(res).unwrap()
}

/// Escapes characters that are not allowed in URIs using %-escaping, and
/// converts path separators to `/`.
///
/// Throws if asked to escape something outside 7-bit printable ascii.
pub fn encode(safe_chars: &str, s: &str) -> String {
    let mut buf = String::with_capacity(s.len() * 2);
    for c in s.bytes() {
        if safe_chars.as_bytes().contains(&c) {
            buf.push(c as char)
        } else {
            let code = c;
            if !(32..=127).contains(&code) {
                panic!("only 7bit ascii allowed in {}", s);
            }
            buf.push_str(&format!("%{:02X}", code))
        }
    }
    buf
}

/// Turns a file url into an absolute path.
///
/// - It will turn a unix-style url "file://localhost/path" into "/path", and will
///   turn a dos-style url "file://localhost/C|/path" into "C:/path".
/// - It rejects unc urls that use five-slash encoding "file://///server/path".
/// - The host can be either "localhost" or empty.
/// - It will unescape %-encoding, but throws if that was used to encode something
///   outside 7-bit ascii.
/// - It doesn't attempt to validate the escaping of the url:
///   doesn't complain if the uri has %-encoding where it wasn't needed, nor if
///   the uri fails to %-encode where it should.
pub fn parse(uri: &str) -> String {
    let (host, path, query_fragment) = match url_re(uri) {
        Some(m) => m,
        None => panic!("not a file url - {}", uri),
    };
    let path = decode(path);
    if !host.is_empty() && host != "localhost" {
        panic!("not localhost - {}", uri);
    }
    if !query_fragment.is_empty() {
        panic!("file url can't have query/fragment - {}", uri);
    }
    if let Some((drive_letter, rest)) = dos_url_re(&path) {
        format!("{}:{}", drive_letter, rest)
    } else if !path.is_empty() && path.as_bytes()[0] == b'/' {
        panic!("UNC file urls not supported - {}", uri)
    } else {
        format!("/{}", path)
    }
}

/// Turns an absolute path into a file uri
///
/// The absolute path must be either unix-style absolute path "/path" or
/// dos-style "c:\path" (in which case it treats both forward- and back-slashes
/// as path separators, and converts both to forward-slash, as per URL rules).
///
/// It rejects unc-style paths "\\?\c:\path" or "\\server\share\path".
/// This function merely guarantees that valid absolute paths will give valid
/// file URLs; it doesn't also validate that what's been given is a perfectly
/// well-formed path. For instance, if the path has ? or * or : characters,
/// it will accept them and render them as %3F and * and :. This function also
/// doesn't do escaping - e.g.  if given "he\\o" it treats this as a filename
/// with two backslashes rather than one. It's therefore impossible to create
/// a file url which has forward slashes as part of a file/directory-name; all
/// slashes will be interpreted as path separators.
pub fn create(path: &str) -> String {
    let absolute_path = if let Some((drive_letter, rest)) = dos_re(path) {
        format!("{}:{}", drive_letter, rest)
    } else if path.starts_with('/') {
        crate::string_utils::lstrip(path, "/").to_string()
    } else {
        panic!("Not an absolute filepath - {}", path)
    };
    format!("file:///{}", encode(path_safe_chars(), &absolute_path))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn failure(f: impl FnOnce() -> String + std::panic::UnwindSafe) -> String {
        let payload = std::panic::catch_unwind(f).unwrap_err();
        payload.downcast::<String>().map(|s| *s).unwrap()
    }

    #[test]
    fn parse_urls() {
        assert_eq!(parse("file:///a/b%20c.php"), "/a/b c.php");
        assert_eq!(parse("file://localhost/path"), "/path");
        assert_eq!(parse("file://localhost/C|/path"), "C:/path");
        assert_eq!(parse("file:///c:/x"), "c:/x");
        assert_eq!(parse("file:///"), "/");
        assert_eq!(
            failure(|| parse("http://x/y")),
            "not a file url - http://x/y"
        );
        assert_eq!(failure(|| parse("file://")), "not a file url - file://");
        assert_eq!(
            failure(|| parse("file://host/a")),
            "not localhost - file://host/a"
        );
        assert_eq!(
            failure(|| parse("file:///a?b")),
            "file url can't have query/fragment - file:///a?b"
        );
        assert_eq!(
            failure(|| parse("file://///server/path")),
            "UNC file urls not supported - file://///server/path"
        );
        assert_eq!(
            failure(|| parse("file:///a%2")),
            "incorrect %-escape in a%2"
        );
        assert_eq!(
            failure(|| parse("file:///a%0A")),
            "only 7bit ascii allowed in a%0A"
        );
        // A `%` alone is an incorrect escape too.
        assert_eq!(failure(|| parse("file:///%")), "incorrect %-escape in %");
    }

    #[test]
    fn create_urls() {
        assert_eq!(create("/a/b c.php"), "file:///a/b%20c.php");
        assert_eq!(create("/x/y?z#w"), "file:///x/y%3Fz%23w");
        assert_eq!(create("c:\\x"), "file:///c%3A%5Cx");
        assert_eq!(create("//a"), "file:////a");
        assert_eq!(
            failure(|| create("rel/path")),
            "Not an absolute filepath - rel/path"
        );
        assert_eq!(
            failure(|| create("/a/\u{e9}")),
            "only 7bit ascii allowed in a/\u{e9}"
        );
        // A round trip.
        assert_eq!(parse(&create("/tmp/a b/c%d.php")), "/tmp/a b/c%d.php");
    }
}
