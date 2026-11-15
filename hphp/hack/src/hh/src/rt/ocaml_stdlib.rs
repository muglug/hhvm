// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the functions of OCaml's `Stdlib` (the initially opened module)
//! that the ported modules use and whose result depends on how they are
//! written: the integer literals of `int_of_string`, `string_of_float`.

/// `int_of_string_opt`: `caml_int_of_string` (`parse_intnat` with 63 bits in
/// `runtime/ints.c`): an optional `-` or `+`, an optional base prefix (`0x`,
/// `0o`, `0b`, `0u`, in either case), a digit, then digits and `_`. Decimal
/// literals must fit a signed 63-bit integer; the others an unsigned one
/// (and wrap around).
pub fn int_of_string_opt(x: &str) -> Option<isize> {
    const NBITS: u32 = 63;
    let p = x.as_bytes();
    let mut i = 0;
    let mut sign: i128 = 1;
    if p.first() == Some(&b'-') {
        sign = -1;
        i += 1;
    } else if p.first() == Some(&b'+') {
        i += 1;
    }
    let mut base: u64 = 10;
    let mut signedness = true;
    if p.get(i) == Some(&b'0') {
        match p.get(i + 1) {
            Some(b'x' | b'X') => {
                base = 16;
                signedness = false;
                i += 2;
            }
            Some(b'o' | b'O') => {
                base = 8;
                signedness = false;
                i += 2;
            }
            Some(b'b' | b'B') => {
                base = 2;
                signedness = false;
                i += 2;
            }
            Some(b'u' | b'U') => {
                signedness = false;
                i += 2;
            }
            _ => {}
        }
    }
    let parse_digit = |c: u8| -> Option<u64> {
        match c {
            b'0'..=b'9' => Some((c - b'0') as u64),
            b'A'..=b'F' => Some((c - b'A') as u64 + 10),
            b'a'..=b'f' => Some((c - b'a') as u64 + 10),
            _ => None,
        }
    };
    let threshold: u64 = u64::MAX / base;
    let d = parse_digit(*p.get(i)?)?;
    if d >= base {
        return None;
    }
    let mut res: u64 = d;
    i += 1;
    while i < p.len() {
        let c = p[i];
        if c == b'_' {
            i += 1;
            continue;
        }
        let d = match parse_digit(c) {
            Some(d) if d < base => d,
            _ => break,
        };
        // Detect overflow in multiplication base * res
        if res > threshold {
            return None;
        }
        res = base * res + d;
        // Detect overflow in addition (base * res) + d
        if res < d {
            return None;
        }
        i += 1;
    }
    if i != p.len() {
        return None;
    }
    if signedness {
        // Signed representation expected, allow -2^(nbits-1) to 2^(nbits-1) - 1
        if sign >= 0 {
            if res >= 1u64 << (NBITS - 1) {
                return None;
            }
        } else if res > 1u64 << (NBITS - 1) {
            return None;
        }
    } else {
        // Unsigned representation expected, allow 0 to 2^nbits - 1
        // and tolerate -(2^nbits - 1) to 0
        if res >= 1u64 << NBITS {
            return None;
        }
    }
    // `Val_long` keeps the low 63 bits of the result.
    let n = (sign * res as i128) as i64;
    Some(((n << 1) >> 1) as isize)
}

/// `int_of_string`: [`int_of_string_opt`], raising `Failure "int_of_string"`
/// (the panic payload is the message of the `Failure`).
pub fn int_of_string(s: &str) -> isize {
    match int_of_string_opt(s) {
        Some(n) => n,
        None => panic!("int_of_string"),
    }
}


/// `Int64.of_string`: decimal (optionally signed), or `0x`/`0o`/`0b`
/// prefixed (wrapping to the 64-bit range as OCaml does for those), `_`
/// allowed after the first digit. Raises `Failure "Int64.of_string"` (the
/// panic payload is the message of the `Failure`).
pub fn int64_of_string(s: &str) -> i64 {
    let fail = || -> ! { panic!("Int64.of_string") };
    let (neg, rest) = match s.as_bytes().first() {
        Some(b'-') => (true, &s[1..]),
        Some(b'+') => (false, &s[1..]),
        _ => (false, s),
    };
    let (radix, digits, unsigned) = if let Some(d) = rest.strip_prefix("0x").or(rest.strip_prefix("0X")) {
        (16, d, true)
    } else if let Some(d) = rest.strip_prefix("0o").or(rest.strip_prefix("0O")) {
        (8, d, true)
    } else if let Some(d) = rest.strip_prefix("0b").or(rest.strip_prefix("0B")) {
        (2, d, true)
    } else if let Some(d) = rest.strip_prefix("0u").or(rest.strip_prefix("0U")) {
        (10, d, true)
    } else {
        (10, rest, false)
    };
    if digits.is_empty() || digits.starts_with('_') {
        fail()
    }
    let digits: String = digits.chars().filter(|c| *c != '_').collect();
    let v = match u64::from_str_radix(&digits, radix) {
        Ok(v) => v,
        Err(_) => fail(),
    };
    if unsigned {
        let v = v as i64;
        if neg { v.wrapping_neg() } else { v }
    } else if neg {
        if v > (i64::MAX as u64) + 1 {
            fail()
        }
        (v as i64).wrapping_neg()
    } else {
        if v > i64::MAX as u64 {
            fail()
        }
        v as i64
    }
}

/// `string_of_float` (`valid_float_lexem (format_float "%.12g" f)`): `%.12g`,
/// with a `.` added when that looks like an integer. Also what `Printf`'s
/// `%F` (and so `[@@deriving show]`) prints a float with.
pub fn string_of_float(f: f64) -> String {
    let fmt = c"%.12g";
    let mut buf = vec![0u8; 64];
    // SAFETY: `buf` is writable for its length, which is passed; the format
    // takes one double.
    let n = unsafe {
        libc::snprintf(
            buf.as_mut_ptr() as *mut libc::c_char,
            buf.len(),
            fmt.as_ptr(),
            f,
        )
    };
    buf.truncate((n.max(0) as usize).min(buf.len() - 1));
    let s = String::from_utf8_lossy(&buf).into_owned();
    // `valid_float_lexem`
    if s.bytes().all(|b| b == b'-' || b.is_ascii_digit()) {
        s + "."
    } else {
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ints_as_in_ocaml() {
        assert_eq!(int_of_string_opt("12"), Some(12));
        assert_eq!(int_of_string_opt("-12"), Some(-12));
        assert_eq!(int_of_string_opt("+12"), Some(12));
        assert_eq!(int_of_string_opt("1_000"), Some(1000));
        assert_eq!(int_of_string_opt("_1"), None);
        assert_eq!(int_of_string_opt("0x_1"), None);
        assert_eq!(int_of_string_opt("0b101"), Some(5));
        assert_eq!(int_of_string_opt("0o17"), Some(15));
        assert_eq!(int_of_string_opt("0u17"), Some(17));
        assert_eq!(int_of_string_opt(""), None);
        assert_eq!(int_of_string_opt("-"), None);
        assert_eq!(int_of_string_opt("1 "), None);
        assert_eq!(int_of_string_opt(" 1"), None);
        assert_eq!(int_of_string_opt("4611686018427387903"), Some(4611686018427387903));
        assert_eq!(int_of_string_opt("4611686018427387904"), None);
        assert_eq!(int_of_string_opt("-4611686018427387904"), Some(-4611686018427387904));
        assert_eq!(int_of_string_opt("0x7FFFFFFFFFFFFFFF"), Some(-1));
        assert_eq!(int_of_string_opt("0x8000000000000000"), None);
        assert_eq!(int_of_string_opt("99999999"), Some(99999999));
    }

    /// Values given by OCaml 5.1's `int_of_string_opt`.
    #[test]
    fn unsigned_literals_wrap_as_in_ocaml() {
        assert_eq!(int_of_string_opt("017"), Some(17));
        assert_eq!(int_of_string_opt("0x4000000000000000"), Some(-4611686018427387904));
        assert_eq!(int_of_string_opt("-0x4000000000000000"), Some(-4611686018427387904));
        assert_eq!(int_of_string_opt("-0x7FFFFFFFFFFFFFFF"), Some(1));
        assert_eq!(int_of_string_opt("-0u4611686018427387904"), Some(-4611686018427387904));
        assert_eq!(int_of_string_opt("1.5"), None);
        assert_eq!(int_of_string_opt("0x"), None);
    }

    #[test]
    fn string_of_float_as_in_ocaml() {
        assert_eq!(string_of_float(1e20), "1e+20");
        assert_eq!(string_of_float(0.1), "0.1");
        assert_eq!(string_of_float(-3.0), "-3.");
        assert_eq!(string_of_float(1.0 / 3.0), "0.333333333333");
    }

    #[test]
    fn int64_of_string_as_in_ocaml() {
        assert_eq!(int64_of_string("0"), 0);
        assert_eq!(int64_of_string("-12"), -12);
        assert_eq!(int64_of_string("9223372036854775807"), i64::MAX);
        assert_eq!(int64_of_string("-9223372036854775808"), i64::MIN);
        assert_eq!(int64_of_string("0xffffffffffffffff"), -1);
    }

    #[test]
    #[should_panic(expected = "int_of_string")]
    fn int_of_string_fails_out_of_range() {
        int_of_string("4611686018427387904");
    }
}
