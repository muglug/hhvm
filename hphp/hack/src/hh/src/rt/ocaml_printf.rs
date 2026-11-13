// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Conversions of OCaml's `Printf` whose output Rust's `format!` does not
//! reproduce: `%S` and `%.<n>f`.

/// `Printf.sprintf "%S" s` (and `Format`'s `%S`): the string as an OCaml
/// string literal, `"` ^ `String.escaped s` ^ `"`. `String.escaped` works on
/// bytes: those outside the printable ASCII range become `\ddd`.
#[allow(non_snake_case)]
pub fn sprintf_S(s: &str) -> String {
    let mut res = String::with_capacity(s.len() + 2);
    res.push('"');
    for &c in s.as_bytes() {
        match c {
            b'"' => res.push_str("\\\""),
            b'\\' => res.push_str("\\\\"),
            b'\n' => res.push_str("\\n"),
            b'\t' => res.push_str("\\t"),
            b'\r' => res.push_str("\\r"),
            b'\x08' => res.push_str("\\b"),
            b' '..=b'~' => res.push(c as char),
            _ => res.push_str(&format!("\\{:03}", c)),
        }
    }
    res.push('"');
    res
}

/// `Printf.sprintf "%.<precision>f" x`. OCaml formats floats with the C
/// library (`caml_format_float` calls `snprintf`), so this does too: the
/// digits are those of Rust's exact formatting, but the infinities and NaNs
/// are spelled as the C library spells them (`inf`, `-nan` with glibc...).
pub fn sprintf_f(precision: usize, x: f64) -> String {
    let fmt = std::ffi::CString::new(format!("%.{}f", precision)).unwrap();
    // `%f` of a finite double has at most 309 digits before the point.
    let mut buf = vec![0u8; 320 + precision];
    // SAFETY: `buf` is writable for its length, which is passed; the format
    // is NUL-terminated and takes one double.
    let n = unsafe {
        libc::snprintf(
            buf.as_mut_ptr() as *mut libc::c_char,
            buf.len(),
            fmt.as_ptr(),
            x,
        )
    };
    if n < 0 {
        // Cannot happen for `%f`; Rust's formatting gives the same digits.
        return format!("{:.*}", precision, x);
    }
    buf.truncate((n as usize).min(buf.len() - 1));
    String::from_utf8_lossy(&buf).into_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quoted() {
        assert_eq!(sprintf_S("a\"b\\c\n\t\r\x08"), r#""a\"b\\c\n\t\r\b""#);
        assert_eq!(sprintf_S("\x01\u{e9}~"), "\"\\001\\195\\169~\"");
        assert_eq!(sprintf_S(""), "\"\"");
    }

    #[test]
    fn floats() {
        assert_eq!(sprintf_f(1, 0.), "0.0");
        assert_eq!(sprintf_f(1, 12.3), "12.3");
        assert_eq!(sprintf_f(1, 99.9), "99.9");
        assert_eq!(sprintf_f(1, 0.05), "0.1");
        assert_eq!(sprintf_f(1, 0.25), "0.2");
        assert_eq!(sprintf_f(3, -1.5), "-1.500");
        assert_eq!(sprintf_f(1, f64::INFINITY), "inf");
        assert_eq!(sprintf_f(1, f64::NEG_INFINITY), "-inf");
        assert!(sprintf_f(1, f64::NAN).ends_with("nan"));
        assert_eq!(sprintf_f(0, 1e300).len(), 301);
    }
}
