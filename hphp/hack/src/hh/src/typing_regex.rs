// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_regex.ml`. See `hh/PORTING.md`.
//!
//! The exceptions of the module (`Empty_regex_pattern`, `Missing_delimiter`,
//! `Invalid_global_option`), and the `Pcre.Error (Pcre.BadPattern (msg,
//! offset))` that `type_pattern` lets through, are caught by its caller:
//! they are the variants of [`Error`], returned in a `Result`. The other
//! failures (`internal_error`, and the `Pcre` errors that the caller does not
//! catch) panic, as nothing catches them in OCaml.
//!
//! The pattern is a byte string (an `Aast.String`), as in OCaml; PCRE
//! compiles it through `crate::pcre`, the binding of `libpcre` that OCaml's
//! `Pcre` is.

use bstr::BString;
use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::naming_special_names as sn;
use crate::pcre;
use crate::pcre::Cflag;
use crate::pos_or_decl;
use crate::typing_defs_core::PosByteString;
use crate::typing_defs_core::PosString;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_map;
use crate::typing_defs_core::t_shape_map::TShapeField;
use crate::typing_make_type as make_type;
use crate::typing_reason as reason;

/// The exceptions of `type_pattern` that its caller catches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// `exception Empty_regex_pattern`
    EmptyRegexPattern,
    /// `exception Missing_delimiter`
    MissingDelimiter,
    /// `exception Invalid_global_option`
    InvalidGlobalOption,
    /// `Pcre.Error (Pcre.BadPattern (msg, offset))`
    BadPattern(String, isize),
}

fn internal_error(s: &str) -> ! {
    panic!(
        "Something (internal) went wrong while typing a regex string: {}",
        s
    )
}

/// bottom is non-inclusive
fn int_keys(
    p: &Pos,
    top: isize,
    bottom: isize,
    acc_i: Vec<TshapeFieldName>,
) -> Vec<TshapeFieldName> {
    // A loop for the tail calls of OCaml; `acc_i` is a list, consed onto.
    let mut top = top;
    let mut acc_i = acc_i;
    while top > bottom {
        acc_i.insert(
            0,
            TshapeFieldName::TSFregexGroup(PosString(
                pos_or_decl::of_raw_pos(p.clone()),
                top.to_string(),
            )),
        );
        top -= 1;
    }
    acc_i
}

/// Assumes that names_numbers is sorted in DECREASING order of numbers
fn keys_aux(
    p: &Pos,
    top: isize,
    names_numbers: &[(String, isize)],
    acc: Vec<TshapeFieldName>,
) -> Vec<TshapeFieldName> {
    match names_numbers {
        [] => {
            let mut res = int_keys(p, top, 0, vec![]);
            res.extend(acc);
            res
        }
        [(name, number), t @ ..] => {
            let mut new_acc = vec![TshapeFieldName::TSFlitStr(PosByteString(
                pos_or_decl::of_raw_pos(p.clone()),
                BString::from(name.as_str()),
            ))];
            new_acc.extend(int_keys(p, top, *number, vec![]));
            new_acc.extend(acc);
            keys_aux(p, number - 1, t, new_acc)
        }
    }
}

/// Any shape keys for our match type except 0. For re"Hel(\D)(?'o'\D)", this is
/// [ TSFregex_group (p, "1"); TSFlit_str (p, 'o') ].
fn keys(p: &Pos, s: &[u8], flags: &[Cflag]) -> Result<Vec<TshapeFieldName>, Error> {
    // Compile `re`-prefixed string for use in Pcre functions
    let pattern = match pcre::regexp(None, Some(flags), s) {
        Ok(pattern) => pattern,
        Err(pcre::Error::BadPattern(msg, i)) => return Err(Error::BadPattern(msg, i)),
        Err(e) => panic!("Pcre.Error({:?})", e),
    };
    // For re"Hel(\D)(?'o'\D)", this is 2.
    let count = match pcre::capturecount(&pattern) {
        Ok(count) => count,
        Err(pcre::Error::InternalError(s)) => internal_error(&s),
        Err(e) => panic!("Pcre.Error({:?})", e),
    };
    // For re"Hel(\D)(?'o'\D)", this is ['o'].
    let names = match pcre::names(&pattern) {
        Ok(names) => names,
        Err(pcre::Error::InternalError(s)) => internal_error(&s),
        Err(e) => panic!("Pcre.Error({:?})", e),
    };
    //  For re"Hel(\D)(?'o'\D)", this is [2]
    let numbers: Vec<isize> = match names
        .iter()
        .map(|name| pcre::get_stringnumber(&pattern, name))
        .collect::<Result<Vec<isize>, pcre::InvalidArgument>>()
    {
        Ok(numbers) => numbers,
        Err(pcre::InvalidArgument(s)) => internal_error(&s),
    };
    let mut names_numbers_sorted: Vec<(String, isize)> = names.into_iter().zip(numbers).collect();
    // `List.sort` (stable), in decreasing order of numbers
    names_numbers_sorted.sort_by(|nn1, nn2| nn2.1.cmp(&nn1.1));
    Ok(keys_aux(p, count, &names_numbers_sorted, vec![]))
}

fn type_match(p: &Pos, s: &[u8], flags: &[Cflag]) -> Result<Ty, Error> {
    let r = reason::regex(p.clone());
    let sft = ShapeFieldType {
        optional: false,
        ty: make_type::string(r.clone()),
    };
    let keys = keys(p, s, flags)?;
    let mut shape_map: t_shape_map::T<ShapeFieldType> = t_shape_map::T::new();
    for key in keys {
        // `TShapeMap.add` (the keys are distinct)
        shape_map.insert(TShapeField(key), sft.clone());
    }
    // Any Regex\Match will contain the entire matched substring at key 0
    shape_map.insert(
        TShapeField(TshapeFieldName::TSFregexGroup(PosString(
            pos_or_decl::of_raw_pos(p.clone()),
            "0".to_string(),
        ))),
        sft,
    );
    Ok(make_type::closed_shape(r, shape_map))
}

/// The flags after the closing delimiter. (`String.to_list_rev`, folded:
/// the characters from the last to the first, consed onto the flags.)
fn get_global_options(s: &[u8]) -> Result<Vec<Cflag>, Error> {
    let mut acc: Vec<Cflag> = vec![];
    for x in s.iter().rev() {
        match x {
            b'u' => acc.insert(0, Cflag::Utf8),
            b'i' => acc.insert(0, Cflag::Caseless),
            b'm' => acc.insert(0, Cflag::Multiline),
            b's' => acc.insert(0, Cflag::Dotall),
            b'x' => acc.insert(0, Cflag::Extended),
            b'A' => acc.insert(0, Cflag::Anchored),
            b'D' => acc.insert(0, Cflag::DollarEndonly),
            b'U' => acc.insert(0, Cflag::Ungreedy),
            b'X' => acc.insert(0, Cflag::Extra),
            b'S' => {}
            _ => return Err(Error::InvalidGlobalOption),
        }
    }
    Ok(acc)
}

fn complement(c: u8) -> u8 {
    match c {
        b'(' => b')',
        b'{' => b'}',
        b'<' => b'>',
        b'[' => b']',
        _ => c,
    }
}

/// Takes in delimiter-stripped string, checks brace-like delimiters
fn check_balanced_delimiters(s: &[u8], delim: u8) -> Result<&[u8], Error> {
    let length = s.len();
    let delim_closed = complement(delim);
    // A loop for the tail calls of OCaml.
    let mut d: isize = 0;
    let mut i: usize = 0;
    loop {
        if d < 0 {
            return Err(Error::MissingDelimiter);
        } else if i < length {
            let (d2, i2) = match s[i] {
                x if x == delim => (d + 1, i + 1),
                x if x == delim_closed => (d - 1, i + 1),
                // Skip escape characters
                b'\\' => (d, i + 2),
                _ => (d, i + 1),
            };
            d = d2;
            i = i2;
        } else if d > 0 {
            return Err(Error::MissingDelimiter);
        } else {
            return Ok(s);
        }
    }
}

/// `Str.string_match (Str.regexp "[^a-zA-Z0-9\t\n\r\x0b\x0c \\]") (String.make 1 c) 0`:
/// non-alphanumeric, non-whitespace, non-backslash characters.
fn is_delimiter(c: u8) -> bool {
    !(c.is_ascii_alphanumeric() || matches!(c, b'\t' | b'\n' | b'\r' | 0x0b | 0x0c | b' ' | b'\\'))
}

/// Takes in regex string and strips outer delimiters, checks and strips
/// nested brace-like delimiters.
fn check_and_strip_delimiters(s: &[u8]) -> Result<(Vec<u8>, Vec<Cflag>), Error> {
    //  Non-alphanumeric, non-whitespace, non-backslash characters are delimiter-eligible
    let length = s.len();
    if length == 0 {
        Err(Error::EmptyRegexPattern)
    } else {
        let first = s[0];
        if is_delimiter(first) {
            let closed_delim = complement(first);
            let no_first_delim = &s[1..];
            // `String.rindex_from no_first_delim (length - 2) closed_delim`
            match no_first_delim.iter().rposition(|c| *c == closed_delim) {
                Some(i) => {
                    let flags = get_global_options(&s[i + 2..])?;
                    let stripped_string = &s[1..1 + i];
                    if closed_delim != first {
                        Ok((
                            check_balanced_delimiters(stripped_string, first)?.to_vec(),
                            flags,
                        ))
                    } else {
                        Ok((stripped_string.to_vec(), flags))
                    }
                }
                None => Err(Error::MissingDelimiter),
            }
        } else {
            Err(Error::MissingDelimiter)
        }
    }
}

pub fn type_pattern(e: &nast::Expr) -> Result<Ty, Error> {
    let aast::Expr(_, p, e_) = e;
    match e_ {
        aast::Expr_::String(s) => {
            let (s, flags) = check_and_strip_delimiters(s)?;
            let match_type = type_match(p, &s, &flags)?;
            let r = reason::regex(p.clone());
            Ok(mk((
                r.clone(),
                Ty_::Tnewtype(
                    sn::regex::T_PATTERN.to_string(),
                    vec![match_type],
                    make_type::string(r),
                ),
            )))
        }
        _ => panic!("Should have caught non-Ast_defs.String prefixed expression!"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn delimiters() {
        let strip = |s: &str| check_and_strip_delimiters(s.as_bytes());
        assert_eq!(strip(""), Err(Error::EmptyRegexPattern));
        assert_eq!(strip("Hello"), Err(Error::MissingDelimiter));
        assert_eq!(strip("/Hello"), Err(Error::MissingDelimiter));
        assert_eq!(strip("#Hello/"), Err(Error::MissingDelimiter));
        assert_eq!(strip("(Hello("), Err(Error::MissingDelimiter));
        assert_eq!(strip("\\Hello\\"), Err(Error::MissingDelimiter));
        assert_eq!(strip("[][]x"), Err(Error::MissingDelimiter));
        assert_eq!(strip("(()"), Err(Error::MissingDelimiter));
        assert_eq!(strip("<<<>>"), Err(Error::MissingDelimiter));
        assert_eq!(strip("/Hello/q"), Err(Error::InvalidGlobalOption));
        assert_eq!(strip("/Hello/").unwrap().0, b"Hello".to_vec());
        assert_eq!(strip(")Hello)").unwrap().0, b"Hello".to_vec());
        assert_eq!(
            strip("(()(<>)((()(<>))))x").unwrap().0,
            b"()(<>)((()(<>)))".to_vec()
        );
        assert_eq!(strip("<\\>>x").unwrap().0, b"\\>".to_vec());
        assert_eq!(strip("[[]]").unwrap().0, b"[]".to_vec());
        assert_eq!(
            strip("/a/uiS").unwrap().1,
            vec![Cflag::Utf8, Cflag::Caseless]
        );
    }

    #[test]
    fn keys_of_groups() {
        let p = Pos::NONE;
        let ks = keys(&p, b"Hel(\\D)(?'o'\\D)", &[]).unwrap();
        let names: Vec<String> = ks
            .iter()
            .map(|k| crate::typing_defs_core::t_shape_field::name(k).to_string())
            .collect();
        assert_eq!(names, vec!["1".to_string(), "o".to_string()]);
        assert_eq!(
            keys(&p, b"He(?'42'\\D)lo", &[]),
            Err(Error::BadPattern(
                "group name must start with a non-digit".to_string(),
                5
            ))
        );
    }
}
