// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Yojson` (the OCaml library): the JSON values that `Telemetry` and
//! `Pos.json` build, and their compact printer. See `hh/PORTING.md`.
//!
//! `serde_json::Value` is not used for them because an `` `Assoc`` is a list:
//! its keys stay in the order they were given, and a key can be there twice.

/// `Yojson.Json_error`: what `Yojson.Safe.from_string` raises on input that
/// is not JSON, with a message in Yojson's form (`Line 1, bytes 0-3:` and a
/// newline, then the description).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonError(pub String);

impl std::fmt::Display for JsonError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Yojson.Json_error({:?})", self.0)
    }
}

impl std::error::Error for JsonError {}

pub mod safe {
    /// `Yojson.Safe.t`, without the non-standard `` `Tuple`` and
    /// `` `Variant``.
    #[derive(Clone, Debug, PartialEq)]
    pub enum T {
        Null,
        Bool(bool),
        Int(isize),
        Intlit(String),
        Float(f64),
        String(String),
        Assoc(Vec<(String, T)>),
        List(Vec<T>),
    }

    /// `write_string`: the bytes of the string, with `"`, `\` and the control
    /// characters escaped. Everything else is written as it is.
    fn write_string(ob: &mut String, s: &str) {
        ob.push('"');
        for c in s.chars() {
            match c {
                '"' => ob.push_str("\\\""),
                '\\' => ob.push_str("\\\\"),
                '\u{8}' => ob.push_str("\\b"),
                '\u{c}' => ob.push_str("\\f"),
                '\n' => ob.push_str("\\n"),
                '\r' => ob.push_str("\\r"),
                '\t' => ob.push_str("\\t"),
                '\u{0}'..='\u{1f}' | '\u{7f}' => {
                    ob.push_str(&format!("\\u00{:02x}", c as u32));
                }
                c => ob.push(c),
            }
        }
        ob.push('"');
    }

    /// `Printf.sprintf "%.<precision>g" x`, for a finite `x`.
    fn sprintf_g(precision: usize, x: f64) -> String {
        // The exponent of `x` once it is rounded to `precision` digits.
        let e = format!("{:.*e}", precision - 1, x);
        let (mantissa, exponent) = e.split_once('e').unwrap();
        let exponent: i32 = exponent.parse().unwrap();
        let strip_zeros = |s: &str| -> String {
            if s.contains('.') {
                s.trim_end_matches('0').trim_end_matches('.').to_string()
            } else {
                s.to_string()
            }
        };
        if -4 <= exponent && exponent < precision as i32 {
            let decimals = (precision as i32 - 1 - exponent) as usize;
            strip_zeros(&format!("{:.*}", decimals, x))
        } else {
            format!(
                "{}e{}{:02}",
                strip_zeros(mantissa),
                if exponent < 0 { '-' } else { '+' },
                exponent.abs()
            )
        }
    }

    fn float_needs_period(s: &str) -> bool {
        s.bytes().all(|c| c.is_ascii_digit() || c == b'-')
    }

    fn write_float(ob: &mut String, x: f64) {
        if x.is_nan() {
            ob.push_str("NaN")
        } else if x.is_infinite() {
            ob.push_str(if x > 0. { "Infinity" } else { "-Infinity" })
        } else {
            let s1 = sprintf_g(16, x);
            let s = if s1.parse::<f64>() == Ok(x) {
                s1
            } else {
                sprintf_g(17, x)
            };
            ob.push_str(&s);
            if float_needs_period(&s) {
                ob.push_str(".0")
            }
        }
    }

    fn write_json(ob: &mut String, x: &T) {
        match x {
            T::Null => ob.push_str("null"),
            T::Bool(b) => ob.push_str(if *b { "true" } else { "false" }),
            T::Int(i) => ob.push_str(&i.to_string()),
            T::Intlit(s) => ob.push_str(s),
            T::Float(f) => write_float(ob, *f),
            T::String(s) => write_string(ob, s),
            T::Assoc(l) => {
                ob.push('{');
                for (i, (k, v)) in l.iter().enumerate() {
                    if i > 0 {
                        ob.push(',');
                    }
                    write_string(ob, k);
                    ob.push(':');
                    write_json(ob, v);
                }
                ob.push('}');
            }
            T::List(l) => {
                ob.push('[');
                for (i, v) in l.iter().enumerate() {
                    if i > 0 {
                        ob.push(',');
                    }
                    write_json(ob, v);
                }
                ob.push(']');
            }
        }
    }

    /// The compact form of the value: no space, no newline.
    pub fn to_string(x: &T) -> String {
        let mut ob = String::new();
        write_json(&mut ob, x);
        ob
    }

    /// `Yojson.Safe.from_string`: one JSON value, possibly surrounded by
    /// blanks, with the extensions Yojson accepts: `NaN`, `Infinity` and
    /// `-Infinity`, `/* */` and `//` comments, field names that are bare
    /// identifiers, and `.` with no digit after it in a float (`1.`). An
    /// integer that does not fit an OCaml `int` (63 bits) is an `Intlit` of
    /// its text. The fields of an object stay in their order, duplicates
    /// included.
    ///
    /// Not accepted: Yojson's `` `Tuple`` and `` `Variant`` syntax (`(...)`,
    /// `<...>`), which `T` does not have. A `\u` escape of a lone low
    /// surrogate, which Yojson writes as three (invalid UTF-8) bytes, is
    /// U+FFFD here. The positions in the error messages follow Yojson's form
    /// (`Line L, bytes B1-B2:`) but not always its exact bytes.
    pub fn from_string(s: &str) -> Result<T, super::JsonError> {
        let mut p = Parser {
            s: s.as_bytes(),
            pos: 0,
            lnum: 1,
            bol: 0,
        };
        p.read_space()?;
        if p.pos >= p.s.len() {
            return Err(super::JsonError("Blank input data".to_string()));
        }
        let x = p.read_json()?;
        p.read_space()?;
        if p.pos < p.s.len() {
            return Err(p.long_error("Junk after end of JSON value:", p.pos));
        }
        Ok(x)
    }

    /// The state of Yojson's lexer that its messages use: the line number and
    /// where the line begins.
    struct Parser<'a> {
        s: &'a [u8],
        pos: usize,
        lnum: usize,
        bol: usize,
    }

    /// `max_int` of OCaml (63-bit integers).
    const OCAML_MAX_INT: i128 = (1 << 62) - 1;

    impl Parser<'_> {
        fn peek(&self) -> Option<u8> {
            self.s.get(self.pos).copied()
        }

        fn looking_at(&self, lit: &str) -> bool {
            self.s[self.pos..].starts_with(lit.as_bytes())
        }

        /// `custom_error`: the description, after the line and the bytes
        /// (relative to the line) from `start` to the current position.
        fn custom_error(&self, descr: &str, start: usize) -> super::JsonError {
            let pos1 = start.saturating_sub(self.bol);
            let pos2 = self.pos.max(start).saturating_sub(self.bol);
            super::JsonError(format!(
                "Line {}, bytes {}-{}:\n{}",
                self.lnum, pos1, pos2, descr
            ))
        }

        /// `long_error`: the description followed by the text found at
        /// `start` (up to the next blank, at most 32 more bytes).
        fn long_error(&mut self, descr: &str, start: usize) -> super::JsonError {
            let mut end = (start + 1).min(self.s.len()).max(self.pos);
            let limit = (end + 32).min(self.s.len());
            while end < limit && !matches!(self.s[end], b' ' | b'\t' | b'\r' | b'\n') {
                end += 1;
            }
            // Do not cut a character in two.
            while end < self.s.len() && (self.s[end] & 0xC0) == 0x80 {
                end += 1;
            }
            self.pos = end;
            let junk = String::from_utf8_lossy(&self.s[start..end]).into_owned();
            self.custom_error(&format!("{} '{}'", descr, junk), start)
        }

        fn unexpected_end(&self) -> super::JsonError {
            self.custom_error("Unexpected end of input", self.pos)
        }

        fn newline(&mut self) {
            self.lnum += 1;
            self.bol = self.pos;
        }

        /// `read_space`: blanks and comments.
        fn read_space(&mut self) -> Result<(), super::JsonError> {
            loop {
                match self.peek() {
                    Some(b' ' | b'\t' | b'\r') => self.pos += 1,
                    Some(b'\n') => {
                        self.pos += 1;
                        self.newline();
                    }
                    Some(b'/') if self.looking_at("//") => {
                        while !matches!(self.peek(), None | Some(b'\n')) {
                            self.pos += 1;
                        }
                    }
                    Some(b'/') if self.looking_at("/*") => {
                        let start = self.pos;
                        self.pos += 2;
                        loop {
                            if self.looking_at("*/") {
                                self.pos += 2;
                                break;
                            }
                            match self.peek() {
                                None => return Err(self.long_error("Unterminated comment", start)),
                                Some(b'\n') => {
                                    self.pos += 1;
                                    self.newline();
                                }
                                Some(_) => self.pos += 1,
                            }
                        }
                    }
                    _ => return Ok(()),
                }
            }
        }

        fn read_json(&mut self) -> Result<T, super::JsonError> {
            let start = self.pos;
            let literal = |p: &mut Self, lit: &str, v: T| {
                p.pos += lit.len();
                Ok(v)
            };
            match self.peek() {
                None => Err(self.unexpected_end()),
                Some(b't') if self.looking_at("true") => literal(self, "true", T::Bool(true)),
                Some(b'f') if self.looking_at("false") => literal(self, "false", T::Bool(false)),
                Some(b'n') if self.looking_at("null") => literal(self, "null", T::Null),
                Some(b'N') if self.looking_at("NaN") => literal(self, "NaN", T::Float(f64::NAN)),
                Some(b'I') if self.looking_at("Infinity") => {
                    literal(self, "Infinity", T::Float(f64::INFINITY))
                }
                Some(b'-') if self.looking_at("-Infinity") => {
                    literal(self, "-Infinity", T::Float(f64::NEG_INFINITY))
                }
                Some(b'"') => {
                    self.pos += 1;
                    Ok(T::String(self.finish_string()?))
                }
                Some(b'[') => {
                    self.pos += 1;
                    self.read_array()
                }
                Some(b'{') => {
                    self.pos += 1;
                    self.read_object()
                }
                Some(c) if c.is_ascii_digit() => self.read_number(start),
                Some(b'-') if self.s.get(self.pos + 1).is_some_and(u8::is_ascii_digit) => {
                    self.read_number(start)
                }
                Some(_) => Err(self.long_error("Invalid token", start)),
            }
        }

        /// `'-'? positive_int` with an optional fraction (`.` and digits) and
        /// exponent: a float if either is there, else an int (`Intlit` if it
        /// overflows).
        fn read_number(&mut self, start: usize) -> Result<T, super::JsonError> {
            if self.peek() == Some(b'-') {
                self.pos += 1;
            }
            // `positive_int = (digit | nonzero digit+)`
            if self.peek() == Some(b'0') {
                self.pos += 1;
            } else {
                while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    self.pos += 1;
                }
            }
            let mut is_float = false;
            if self.peek() == Some(b'.') {
                is_float = true;
                self.pos += 1;
                while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    self.pos += 1;
                }
            }
            if matches!(self.peek(), Some(b'e' | b'E')) {
                let mut i = self.pos + 1;
                if matches!(self.s.get(i), Some(b'+' | b'-')) {
                    i += 1;
                }
                if self.s.get(i).is_some_and(u8::is_ascii_digit) {
                    is_float = true;
                    self.pos = i;
                    while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                        self.pos += 1;
                    }
                }
            }
            // The bytes are ASCII.
            let text = std::str::from_utf8(&self.s[start..self.pos]).unwrap();
            if is_float {
                // `float_of_string`, which takes `1.` and `1.e5` as Rust does.
                Ok(T::Float(text.parse().unwrap()))
            } else {
                match text.parse::<i128>() {
                    Ok(n) if (-OCAML_MAX_INT - 1..=OCAML_MAX_INT).contains(&n) => {
                        Ok(T::Int(n as isize))
                    }
                    _ => Ok(T::Intlit(text.to_string())),
                }
            }
        }

        fn hex4(&self, at: usize) -> Option<u32> {
            let digits = self.s.get(at..at + 4)?;
            let digits = std::str::from_utf8(digits).ok()?;
            if !digits.bytes().all(|c| c.is_ascii_hexdigit()) {
                return None;
            }
            u32::from_str_radix(digits, 16).ok()
        }

        /// The rest of a string literal, after its `"`.
        fn finish_string(&mut self) -> Result<String, super::JsonError> {
            let mut buf: Vec<u8> = vec![];
            loop {
                match self.peek() {
                    None => return Err(self.unexpected_end()),
                    Some(b'"') => {
                        self.pos += 1;
                        // The input is UTF-8, and so is what the escapes add.
                        return Ok(String::from_utf8(buf).unwrap());
                    }
                    Some(b'\\') => {
                        let esc = self.pos;
                        self.pos += 1;
                        let c = match self.peek() {
                            None => return Err(self.unexpected_end()),
                            Some(c) => c,
                        };
                        self.pos += 1;
                        match c {
                            b'"' | b'\\' | b'/' => buf.push(c),
                            b'b' => buf.push(b'\x08'),
                            b'f' => buf.push(b'\x0c'),
                            b'n' => buf.push(b'\n'),
                            b'r' => buf.push(b'\r'),
                            b't' => buf.push(b'\t'),
                            b'u' => {
                                let x = match self.hex4(self.pos) {
                                    Some(x) => x,
                                    None => {
                                        self.pos = esc;
                                        return Err(self.long_error("Invalid escape sequence", esc));
                                    }
                                };
                                self.pos += 4;
                                let code = if (0xD800..=0xDBFF).contains(&x) {
                                    // `finish_surrogate_pair`
                                    if !self.looking_at("\\u") {
                                        return Err(self.long_error(
                                            "Missing escape sequence representing low surrogate for code point beyond U+FFFF",
                                            self.pos,
                                        ));
                                    }
                                    match self.hex4(self.pos + 2) {
                                        Some(y) if (0xDC00..=0xDFFF).contains(&y) => {
                                            self.pos += 6;
                                            0x10000 + ((x - 0xD800) << 10) + (y - 0xDC00)
                                        }
                                        _ => {
                                            return Err(self.long_error(
                                                "Invalid low surrogate for code point beyond U+FFFF",
                                                self.pos,
                                            ));
                                        }
                                    }
                                } else {
                                    x
                                };
                                let c = char::from_u32(code).unwrap_or('\u{FFFD}');
                                let mut tmp = [0; 4];
                                buf.extend_from_slice(c.encode_utf8(&mut tmp).as_bytes());
                            }
                            _ => {
                                self.pos = esc;
                                return Err(self.long_error("Invalid escape sequence", esc));
                            }
                        }
                    }
                    Some(c) => {
                        buf.push(c);
                        self.pos += 1;
                    }
                }
            }
        }

        fn read_array(&mut self) -> Result<T, super::JsonError> {
            let mut acc = vec![];
            self.read_space()?;
            if self.peek() == Some(b']') {
                self.pos += 1;
                return Ok(T::List(acc));
            }
            loop {
                acc.push(self.read_json()?);
                self.read_space()?;
                match self.peek() {
                    None => return Err(self.unexpected_end()),
                    Some(b',') => self.pos += 1,
                    Some(b']') => {
                        self.pos += 1;
                        return Ok(T::List(acc));
                    }
                    Some(_) => {
                        return Err(self.long_error("Expected ',' or ']' but found", self.pos));
                    }
                }
                self.read_space()?;
            }
        }

        /// `read_ident`: a field name, a string or an identifier.
        fn read_ident(&mut self) -> Result<String, super::JsonError> {
            let start = self.pos;
            match self.peek() {
                None => Err(self.unexpected_end()),
                Some(b'"') => {
                    self.pos += 1;
                    self.finish_string()
                }
                Some(c) if c.is_ascii_alphabetic() || c == b'_' => {
                    while self
                        .peek()
                        .is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_')
                    {
                        self.pos += 1;
                    }
                    Ok(String::from_utf8(self.s[start..self.pos].to_vec()).unwrap())
                }
                Some(_) => Err(self.long_error("Expected string or identifier but found", start)),
            }
        }

        fn read_object(&mut self) -> Result<T, super::JsonError> {
            let mut acc = vec![];
            self.read_space()?;
            if self.peek() == Some(b'}') {
                self.pos += 1;
                return Ok(T::Assoc(acc));
            }
            loop {
                let field_name = self.read_ident()?;
                self.read_space()?;
                match self.peek() {
                    None => return Err(self.unexpected_end()),
                    Some(b':') => self.pos += 1,
                    Some(_) => return Err(self.long_error("Expected ':' but found", self.pos)),
                }
                self.read_space()?;
                acc.push((field_name, self.read_json()?));
                self.read_space()?;
                match self.peek() {
                    None => return Err(self.unexpected_end()),
                    Some(b',') => self.pos += 1,
                    Some(b'}') => {
                        self.pos += 1;
                        return Ok(T::Assoc(acc));
                    }
                    Some(_) => {
                        return Err(self.long_error("Expected ',' or '}' but found", self.pos));
                    }
                }
                self.read_space()?;
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn compact() {
            let json = T::Assoc(vec![
                ("b".to_string(), T::Int(-3)),
                ("a".to_string(), T::List(vec![T::Null, T::Bool(true), T::Bool(false)])),
                ("b".to_string(), T::String("x".to_string())),
                ("big".to_string(), T::Intlit("123456789012345678901234567890".to_string())),
                ("o".to_string(), T::Assoc(vec![])),
                ("l".to_string(), T::List(vec![])),
            ]);
            assert_eq!(
                to_string(&json),
                r#"{"b":-3,"a":[null,true,false],"b":"x","big":123456789012345678901234567890,"o":{},"l":[]}"#
            );
        }

        #[test]
        fn strings() {
            let s = |s: &str| to_string(&T::String(s.to_string()));
            assert_eq!(s(""), r#""""#);
            assert_eq!(s("a\"b\\c"), r#""a\"b\\c""#);
            assert_eq!(s("\u{8}\u{c}\n\r\t"), r#""\b\f\n\r\t""#);
            assert_eq!(s("\u{0}\u{1}\u{1f}\u{7f}"), r#""\u0000\u0001\u001f\u007f""#);
            // `/` and the characters that are not ASCII are not escaped.
            assert_eq!(s("a/b é ✓"), "\"a/b é ✓\"");
        }

        #[test]
        fn floats() {
            let f = |x: f64| to_string(&T::Float(x));
            assert_eq!(f(0.), "0.0");
            assert_eq!(f(-0.), "-0.0");
            assert_eq!(f(1.), "1.0");
            assert_eq!(f(-12.), "-12.0");
            assert_eq!(f(1.5), "1.5");
            assert_eq!(f(0.1), "0.1");
            assert_eq!(f(123456.789), "123456.789");
            assert_eq!(f(0.0001), "0.0001");
            assert_eq!(f(0.00001), "1e-05");
            assert_eq!(f(1.5e-7), "1.5e-07");
            assert_eq!(f(1e15), "1000000000000000.0");
            assert_eq!(f(1e16), "1e+16");
            assert_eq!(f(1.5e300), "1.5e+300");
            // 16 digits are not enough for these.
            assert_eq!(f(0.1 + 0.2), "0.30000000000000004");
            assert_eq!(f(1. / 3.), "0.3333333333333333");
            assert_eq!(f(f64::MAX), "1.7976931348623157e+308");
            assert_eq!(f(f64::NAN), "NaN");
            assert_eq!(f(f64::INFINITY), "Infinity");
            assert_eq!(f(f64::NEG_INFINITY), "-Infinity");
        }
    }

    #[cfg(test)]
    mod parse_tests {
        use super::*;

        fn parse(s: &str) -> T {
            from_string(s).unwrap()
        }

        fn error(s: &str) -> String {
            from_string(s).unwrap_err().0
        }

        fn string(s: &str) -> T {
            T::String(s.to_string())
        }

        #[test]
        fn values() {
            assert_eq!(parse(" null "), T::Null);
            assert_eq!(parse("true"), T::Bool(true));
            assert_eq!(parse("false"), T::Bool(false));
            assert_eq!(parse("0"), T::Int(0));
            assert_eq!(parse("-12"), T::Int(-12));
            assert_eq!(parse("1.5"), T::Float(1.5));
            assert_eq!(parse("1."), T::Float(1.));
            assert_eq!(parse("-2e3"), T::Float(-2000.));
            assert_eq!(parse("1E-2"), T::Float(0.01));
            assert_eq!(parse("Infinity"), T::Float(f64::INFINITY));
            assert_eq!(parse("-Infinity"), T::Float(f64::NEG_INFINITY));
            assert!(matches!(parse("NaN"), T::Float(x) if x.is_nan()));
            assert_eq!(parse(r#""a\"b\\c\/\n\t\u00e9""#), string("a\"b\\c/\n\té"));
            // A surrogate pair.
            assert_eq!(parse(r#""\ud83d\ude00""#), string("\u{1F600}"));
            assert_eq!(parse("\"é ✓\""), string("é ✓"));
        }

        #[test]
        fn ints_that_overflow() {
            assert_eq!(parse("4611686018427387903"), T::Int(4611686018427387903));
            assert_eq!(parse("-4611686018427387904"), T::Int(-4611686018427387904));
            assert_eq!(
                parse("4611686018427387904"),
                T::Intlit("4611686018427387904".to_string())
            );
            assert_eq!(
                parse("-123456789012345678901234567890"),
                T::Intlit("-123456789012345678901234567890".to_string())
            );
        }

        #[test]
        fn collections() {
            assert_eq!(parse("[]"), T::List(vec![]));
            assert_eq!(parse("{ }"), T::Assoc(vec![]));
            assert_eq!(
                parse("[1, [2], {\"a\": null}]"),
                T::List(vec![
                    T::Int(1),
                    T::List(vec![T::Int(2)]),
                    T::Assoc(vec![("a".to_string(), T::Null)])
                ])
            );
            // Fields keep their order, duplicates included; a field name can
            // be an identifier.
            assert_eq!(
                parse(r#"{"b": 1, "a": 2, b: 3}"#),
                T::Assoc(vec![
                    ("b".to_string(), T::Int(1)),
                    ("a".to_string(), T::Int(2)),
                    ("b".to_string(), T::Int(3)),
                ])
            );
            // Comments are blanks.
            assert_eq!(
                parse("/* x */ [1, // y\n 2]"),
                T::List(vec![T::Int(1), T::Int(2)])
            );
        }

        #[test]
        fn errors() {
            assert_eq!(error(""), "Blank input data");
            assert_eq!(error("  \n "), "Blank input data");
            assert_eq!(error("abc"), "Line 1, bytes 0-3:\nInvalid token 'abc'");
            assert_eq!(error("[1"), "Line 1, bytes 2-2:\nUnexpected end of input");
            assert_eq!(error("1 2"), "Line 1, bytes 2-3:\nJunk after end of JSON value: '2'");
            assert_eq!(
                error("[1 2]"),
                "Line 1, bytes 3-5:\nExpected ',' or ']' but found '2]'"
            );
            assert_eq!(
                error("{\"a\" 1}"),
                "Line 1, bytes 5-7:\nExpected ':' but found '1}'"
            );
            assert_eq!(
                error("{\"a\": 1,}"),
                "Line 1, bytes 8-9:\nExpected string or identifier but found '}'"
            );
            assert_eq!(
                error("\n{\"a\": 1 2}"),
                "Line 2, bytes 8-10:\nExpected ',' or '}' but found '2}'"
            );
            assert_eq!(
                error(r#""\x""#),
                "Line 1, bytes 1-4:\nInvalid escape sequence '\\x\"'"
            );
        }
    }
}
