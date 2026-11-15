// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/http_lite/http_lite.ml`. See `hh/PORTING.md`.
//!
//! This is a lightweight library for reading and writing messages in the HTTP
//! format, with headers and body. So far it only supports the small set of
//! features needed by the Language Server Protocol. It follows the internet
//! robustness principle of being as permissive as possible in what it expects,
//! i.e. no validation beyond what it essentially needs.
//!
//! `exception Malformed of string` is caught by the caller that reads LSP
//! messages (`Jsonrpc`), with the exceptions of `Buffered_line_reader` that
//! the readers let through: the readers return them as an [`Error`].

use std::io::Read;
use std::io::Write;

use crate::buffered_line_reader;
use crate::rt::ocaml_stdlib::int_of_string_opt;
use crate::s_map;

/// `exception Malformed of string`
#[derive(Clone, PartialEq, Eq)]
pub struct Malformed(pub String);

impl std::fmt::Debug for Malformed {
    /// `Printexc.to_string`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Http_lite.Malformed({})", crate::rt::ocaml_printf::sprintf_s(&self.0))
    }
}

/// What the readers raise: `Malformed`, or what `Buffered_line_reader`
/// raised. `Debug` gives what `Printexc.to_string` gives in OCaml.
pub enum Error {
    Malformed(Malformed),
    Reader(buffered_line_reader::Error),
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Malformed(e) => e.fmt(f),
            Error::Reader(e) => e.fmt(f),
        }
    }
}

impl From<buffered_line_reader::Error> for Error {
    fn from(e: buffered_line_reader::Error) -> Self {
        Error::Reader(e)
    }
}

fn malformed(s: &str) -> Error {
    Error::Malformed(Malformed(s.to_string()))
}

/// `Base.String.strip`
fn strip(s: &str) -> &str {
    s.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\u{b}' | '\u{c}' | '\r'))
}

/// `Str.bounded_split (Str.regexp_string delim) text n` (`n = 0` for
/// `Str.split`): the pieces between the delimiters, at most `n` of them (the
/// last one has the rest of the text), a delimiter at the start or at the end
/// of the text being ignored.
fn str_bounded_split(delim: char, text: &str, num: usize) -> Vec<String> {
    let start = if text.starts_with(delim) {
        delim.len_utf8()
    } else {
        0
    };
    let mut accu = vec![];
    let mut start = start;
    let mut n = num;
    loop {
        if start >= text.len() {
            break;
        }
        if n == 1 {
            accu.push(text[start..].to_string());
            break;
        }
        match text[start..].find(delim) {
            None => {
                accu.push(text[start..].to_string());
                break;
            }
            Some(pos) => {
                accu.push(text[start..start + pos].to_string());
                start = start + pos + delim.len_utf8();
                n = n.wrapping_sub(1);
            }
        }
    }
    accu
}

/// read_headers: reads LF/CRLF-terminated lines until it gets an empty line
///
/// (The lines are bytes in OCaml; a header that is not UTF-8 has U+FFFD in
/// place of the bytes that are not.)
pub fn read_headers<R: Read>(
    reader: &mut buffered_line_reader::T<R>,
) -> Result<Vec<String>, Error> {
    let mut acc = vec![];
    loop {
        match buffered_line_reader::get_next_line(reader) {
            Err(buffered_line_reader::Error::UnixError(_)) => {
                return Err(malformed("Can't read next header"));
            }
            Err(e) => return Err(e.into()),
            Ok(line) if line.is_empty() => break,
            Ok(line) => acc.push(String::from_utf8_lossy(&line).into_owned()),
        }
    }
    Ok(acc)
}

/// parse_headers_to_lowercase_map: turns list of "Key: Value" string headers
/// into a map, with keys normalized to lower-case. HTTP actually allows
/// multiple headers of the same key, but we prefer the simplicity of
/// returning just a string map so we only take the last header for
/// a given key. Note: if any header isn't in Key:Value format, we ignore it.
pub fn parse_headers_to_lowercase_map(headers: &[String]) -> s_map::T<String> {
    let mut acc = s_map::T::new();
    for line in headers {
        if let [k, v] = &str_bounded_split(':', line, 2)[..] {
            let (k_, v_) = (k.to_ascii_lowercase(), strip(v).to_string());
            acc.insert(k_, v_);
        }
    }
    acc
}

/// parse_charset: given a Content-Type value like "mime/type; charset=foo"
/// it returns the "foo" bit of it, if present.
/// https://www.w3.org/Protocols/rfc1341/4_Content-Type.html
/// Note: RFC822 allows comments in this string, but we don't handle them.
pub fn parse_charset(header_value: &str) -> Option<String> {
    // charset_value: if given a param string "charset=b" then it returns Some b
    let charset_value = |param: &String| match &str_bounded_split('=', param, 2)[..] {
        [k, v] if strip(k) == "charset" => Some(strip(v).to_string()),
        _ => None,
    };
    match &str_bounded_split(';', header_value, 0)[..] {
        [_mime_type, params @ ..] => params.iter().find_map(charset_value),
        _ => None,
    }
}

/// read_message_utf8: reads an http-style message "Headers...Body"
/// The headers must include at least Content-Length (to know how long is
/// the body). If they also include Content-Type, then the charset must be utf-8
/// or absent. Errors in these respects produce a Malformed exception.
/// The content of all other headers are ignored.
/// This function returns an OCaml string, which is a sequence of 8bit bytes,
/// so it's up to the caller to handle any unicode characters and their
/// encoding.
pub fn read_message_utf8<R: Read>(
    reader: &mut buffered_line_reader::T<R>,
) -> Result<Vec<u8>, Error> {
    let headers = parse_headers_to_lowercase_map(&read_headers(reader)?);
    let len = match headers.get("content-length").and_then(|s| int_of_string_opt(s)) {
        Some(len) => len,
        None => return Err(malformed("Missing Content-Length")),
    };
    let charset = match headers.get("content-type") {
        Some(v) => parse_charset(v),
        None => None,
    };
    let body = buffered_line_reader::get_next_bytes(reader, len)?;
    match charset {
        Some(s) if s == "utf-8" => {}
        None => {}
        Some(_) => return Err(malformed("Charset not utf-8")),
    }
    Ok(body)
}

/// write_message: writes "Content-Length:...body"
pub fn write_message(outchan: &mut dyn Write, body: &str) -> std::io::Result<()> {
    // Without this, Windows will change the \r\n to \r\r\n
    // (`set_binary_mode_out`: a Rust stream is always binary.)
    write!(outchan, "Content-Length: {}\r\n", body.len())?;
    write!(outchan, "\r\n")?;
    write!(outchan, "{}", body)?;
    outchan.flush()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reader(s: &str) -> buffered_line_reader::T<std::io::Cursor<Vec<u8>>> {
        buffered_line_reader::create(std::io::Cursor::new(s.as_bytes().to_vec()))
    }

    #[test]
    fn headers() {
        let m = parse_headers_to_lowercase_map(&[
            "Content-Length: 12".to_string(),
            "Content-Type: x".to_string(),
            "content-type:  application/json; charset=utf-8 ".to_string(),
            "no colon".to_string(),
            ":leading".to_string(),
            "trailing:".to_string(),
            "a::b".to_string(),
        ]);
        assert_eq!(m.get("content-length").map(|s| s.as_str()), Some("12"));
        assert_eq!(
            m.get("content-type").map(|s| s.as_str()),
            Some("application/json; charset=utf-8")
        );
        assert_eq!(m.get("a").map(|s| s.as_str()), Some(":b"));
        assert_eq!(m.len(), 3);
        assert_eq!(parse_charset("text/html; charset = utf-8"), Some("utf-8".to_string()));
        assert_eq!(parse_charset("text/html;x=y;charset=latin1"), Some("latin1".to_string()));
        assert_eq!(parse_charset("text/html"), None);
        assert_eq!(parse_charset(";charset=utf-8"), None);
        assert_eq!(parse_charset(""), None);
    }

    #[test]
    fn messages() {
        let mut r = reader("Content-Length: 2\r\n\r\n{}Content-Length: 0x3\nX: y\n\n[1]");
        assert_eq!(read_message_utf8(&mut r).unwrap(), b"{}");
        assert_eq!(read_message_utf8(&mut r).unwrap(), b"[1]");
        assert!(matches!(
            read_message_utf8(&mut r),
            Err(Error::Reader(buffered_line_reader::Error::EndOfFile))
        ));
        let mut r = reader("Content-Type: text; charset=latin1\nContent-Length: 1\n\nx");
        assert_eq!(
            format!("{:?}", read_message_utf8(&mut r).unwrap_err()),
            "Http_lite.Malformed(\"Charset not utf-8\")"
        );
        let mut r = reader("Content-Length: x\n\n");
        assert_eq!(
            format!("{:?}", read_message_utf8(&mut r).unwrap_err()),
            "Http_lite.Malformed(\"Missing Content-Length\")"
        );
        let mut r = reader("Content-Length: 0\n\n");
        assert!(matches!(
            read_message_utf8(&mut r),
            Err(Error::Reader(buffered_line_reader::Error::AssertFailure))
        ));
        let mut out = vec![];
        write_message(&mut out, "{}\r\n\r\n").unwrap();
        assert_eq!(out, b"Content-Length: 6\r\n\r\n{}\r\n\r\n");
    }
}
