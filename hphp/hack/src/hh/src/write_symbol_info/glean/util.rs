// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Util` of the `glean_schema` library (`write_symbol_info/glean/util.ml`),
//! and the `Base64` functions (of the ocaml-base64 library) that the schema
//! and `Sym_hash` use.

use crate::yojson::safe::T as Json;

use super::fact_id;

pub fn key(v: Json) -> Json {
    Json::Assoc(vec![("key".to_string(), v)])
}

pub fn id(fact_id: fact_id::T) -> Json {
    Json::Assoc(vec![("id".to_string(), fact_id::to_json_number(fact_id))])
}

const BASE64_ALPHABET: &[u8; 64] =
    b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// `Base64.encode_string` (default alphabet, with padding).
pub fn base64_encode_string(s: &[u8]) -> String {
    let mut out = String::with_capacity(s.len().div_ceil(3) * 4);
    for chunk in s.chunks(3) {
        let b = [
            chunk[0],
            chunk.get(1).copied().unwrap_or(0),
            chunk.get(2).copied().unwrap_or(0),
        ];
        let n = ((b[0] as u32) << 16) | ((b[1] as u32) << 8) | (b[2] as u32);
        out.push(BASE64_ALPHABET[(n >> 18) as usize & 63] as char);
        out.push(BASE64_ALPHABET[(n >> 12) as usize & 63] as char);
        out.push(if chunk.len() > 1 {
            BASE64_ALPHABET[(n >> 6) as usize & 63] as char
        } else {
            '='
        });
        out.push(if chunk.len() > 2 {
            BASE64_ALPHABET[n as usize & 63] as char
        } else {
            '='
        });
    }
    out
}

/// `Base64.decode_exn` (default alphabet, padding required): `Err` with
/// the message of the `Invalid_argument` it raises.
pub fn base64_decode_exn(s: &[u8]) -> Result<Vec<u8>, String> {
    fn value(c: u8) -> Option<u32> {
        BASE64_ALPHABET.iter().position(|&a| a == c).map(|i| i as u32)
    }
    if s.len() % 4 != 0 {
        return Err("Wrong padding".to_string());
    }
    let mut out = Vec::with_capacity(s.len() / 4 * 3);
    for (i, chunk) in s.chunks(4).enumerate() {
        let last = (i + 1) * 4 == s.len();
        let pad = if last {
            chunk.iter().rev().take_while(|&&c| c == b'=').count()
        } else {
            0
        };
        if pad > 2 {
            return Err("Wrong padding".to_string());
        }
        let mut n = 0u32;
        for &c in &chunk[..4 - pad] {
            match value(c) {
                Some(v) => n = (n << 6) | v,
                None => return Err(format!("Malformed input: {}", c as char)),
            }
        }
        n <<= 6 * pad as u32;
        out.push((n >> 16) as u8);
        if pad < 2 {
            out.push((n >> 8) as u8);
        }
        if pad < 1 {
            out.push(n as u8);
        }
    }
    Ok(out)
}

/// Tests only: readers of the JSON of the facts, for the `of_json`
/// functions that the generated modules have in their tests (the OCaml has
/// no readers: the round trip `to_json (of_json j) = j` on facts written by
/// the OCaml checks the Rust serialisers).
#[cfg(test)]
pub mod test_json {
    use crate::yojson::safe::T as Json;

    pub fn string(j: &Json) -> String {
        match j {
            Json::String(s) => s.clone(),
            _ => panic!("not a string: {j:?}"),
        }
    }

    pub fn bool(j: &Json) -> bool {
        match j {
            Json::Bool(b) => *b,
            _ => panic!("not a bool: {j:?}"),
        }
    }

    pub fn int(j: &Json) -> isize {
        match j {
            Json::Int(i) => *i,
            _ => panic!("not an int: {j:?}"),
        }
    }

    /// A string of concatenated base64-encoded md5 hashes.
    pub fn binaries(j: &Json) -> Vec<Vec<u8>> {
        string(j)
            .as_bytes()
            .chunks(24)
            .map(|c| super::base64_decode_exn(c).unwrap())
            .collect()
    }

    pub fn list(j: &Json) -> &Vec<Json> {
        match j {
            Json::List(l) => l,
            _ => panic!("not a list: {j:?}"),
        }
    }

    pub fn single(j: &Json) -> (&str, &Json) {
        match j {
            Json::Assoc(l) if l.len() == 1 => (l[0].0.as_str(), &l[0].1),
            _ => panic!("not an object of one field: {j:?}"),
        }
    }

    pub fn field_opt<'a>(j: &'a Json, k: &str) -> Option<&'a Json> {
        match j {
            Json::Assoc(l) => l.iter().find(|(k1, _)| k1 == k).map(|(_, v)| v),
            _ => panic!("not an object: {j:?}"),
        }
    }

    pub fn field<'a>(j: &'a Json, k: &str) -> &'a Json {
        field_opt(j, k).unwrap_or_else(|| panic!("no field {k} in {j:?}"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base64_round_trip() {
        for s in [&b""[..], b"f", b"fo", b"foo", b"foob", b"fooba", b"foobar", &[0, 255, 128, 7]] {
            let e = base64_encode_string(s);
            assert_eq!(base64_decode_exn(e.as_bytes()).unwrap(), s);
        }
        assert_eq!(base64_encode_string(b"foobar"), "Zm9vYmFy");
        assert_eq!(base64_encode_string(b"fooba"), "Zm9vYmE=");
        assert_eq!(base64_encode_string(b"foob"), "Zm9vYg==");
    }
}
