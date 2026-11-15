// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The parts of `config_file` (utils/config_file/rust/config_file.rs) that
//! hackfmt uses: OCaml hackfmt reads `.hhconfig` through that crate's FFI.
//! They are copied here to keep hackfmt free of the crate's dependency on
//! `oxidized`.

use std::collections::BTreeMap;

use bstr::ByteSlice;

#[derive(Debug, Clone, Default)]
pub struct ConfigFile {
    map: BTreeMap<String, String>,
}

impl ConfigFile {
    fn parse_line(line: &[u8]) -> Option<(String, String)> {
        let mut key_value_iter = line.splitn(2, |&c| c == b'=');
        let key = key_value_iter.next()?.trim();
        let value = key_value_iter.next()?.trim();
        Some((
            String::from_utf8_lossy(key).into_owned(),
            String::from_utf8_lossy(value).into_owned(),
        ))
    }

    pub fn from_slice(bytes: &[u8]) -> Self {
        let mut map = BTreeMap::new();
        let mut current: Option<(String, String)> = None;
        let flush = |current: &mut Option<(String, String)>, map: &mut BTreeMap<String, String>| {
            if let Some((k, v)) = current.take() {
                map.insert(k, v);
            }
        };

        for line in bytes.lines() {
            let trimmed = line.trim();

            if trimmed.is_empty() || line.first() == Some(&b'#') {
                flush(&mut current, &mut map);
                continue;
            }

            if matches!(line.first(), Some(b' ' | b'\t'))
                && let Some((_, ref mut val)) = current
            {
                if trimmed.first() != Some(&b'#') {
                    val.push_str(&String::from_utf8_lossy(trimmed));
                }
                continue;
            }

            flush(&mut current, &mut map);
            current = Self::parse_line(line);
        }

        flush(&mut current, &mut map);
        Self { map }
    }

    pub fn get_int(&self, key: &str) -> Option<Result<isize, std::num::ParseIntError>> {
        self.map.get(key).map(|s| parse_int(s))
    }

    pub fn get_bool(&self, key: &str) -> Option<Result<bool, std::str::ParseBoolError>> {
        self.map.get(key).map(|s| s.parse())
    }
}

// Intended to behave like `caml_int_of_string`.
fn parse_int(input: &str) -> Result<isize, std::num::ParseIntError> {
    use std::borrow::Cow;

    let input = if input.contains('_') {
        Cow::Owned(input.chars().filter(|&c| c != '_').collect())
    } else {
        Cow::Borrowed(input)
    };

    if input.starts_with("0b") {
        isize::from_str_radix(input.trim_start_matches("0b"), 2)
    } else if input.starts_with("0o") {
        isize::from_str_radix(input.trim_start_matches("0o"), 8)
    } else if input.starts_with("0x") {
        isize::from_str_radix(input.trim_start_matches("0x"), 16)
    } else {
        input.parse()
    }
}
