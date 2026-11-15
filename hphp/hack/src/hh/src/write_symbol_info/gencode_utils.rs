// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Gencode_utils` (`write_symbol_info/gencode_utils.ml`).

use std::sync::LazyLock;

use regex::bytes::Captures;
use regex::bytes::Regex;

use crate::hh_logger;

/// The OCaml record has mutable fields: `get_gencode_status` builds it and
/// updates it in place.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct T {
    pub is_generated: bool,
    pub fully_generated: bool,
    pub source: Option<String>,
    pub command: Option<String>,
    pub class_: Option<String>,
    pub signature: Option<String>,
}

/// `regex_sig ^ {|\||} ^ regex_codegen`, an OCaml `Str` regexp: in `Str`,
/// `^` and `$` match at the beginning and end of every line, `.` is any byte
/// but a newline, and `\(...\)` are the groups. The same expression in the
/// `regex` crate's syntax, on bytes (`(?-u)`) with `(?m)`; the groups keep
/// their numbers.
static REGEX: LazyLock<Regex> = LazyLock::new(|| {
    let regex_sig = r"(^.*@(partially-)?generated( SignedSource<<([0-9a-f]+)>>)?.*$)";
    let regex_codegen = r"(^.*@codegen-(command|class|source).*: *(.*)$)";
    Regex::new(&format!("(?m-u){}|{}", regex_sig, regex_codegen)).unwrap()
});

fn has_group(caps: &Captures<'_>, i: usize) -> bool {
    caps.get(i).is_some()
}

fn extract_group(caps: &Captures<'_>, i: usize) -> Option<String> {
    caps.get(i)
        .map(|m| String::from_utf8_lossy(m.as_bytes()).into_owned())
}

fn update_fields(t: &mut T, caps: &Captures<'_>) {
    t.is_generated = true;
    if has_group(caps, 1) {
        t.fully_generated = !has_group(caps, 2);
        t.signature = extract_group(caps, 4)
    } else {
        match extract_group(caps, 6).as_deref() {
            Some("command") => t.command = extract_group(caps, 7),
            Some("source") => t.source = extract_group(caps, 7),
            Some("class") => t.class_ = extract_group(caps, 7),
            _ => hh_logger::log("WARNING: this shouldn't happen."),
        }
    }
}

fn search_and_update(t: &mut T, text: &[u8], pos: usize) -> (bool, usize) {
    // (`Str.search_forward` raises `Invalid_argument` for a start beyond
    // the end of the text; the loop below never asks for one.)
    match REGEX.captures_at(text, pos) {
        Some(caps) => {
            let found_pos = caps.get(0).unwrap().start();
            update_fields(t, &caps);
            (true, found_pos)
        }
        None => (false, 0),
    }
}

pub fn get_gencode_status(text: &[u8]) -> T {
    let mut t = T {
        is_generated: false,
        fully_generated: true,
        source: None,
        command: None,
        class_: None,
        signature: None,
    };
    let mut cur_pos = 0;
    let mut matched = true;
    while matched {
        if cur_pos > text.len() {
            break;
        }
        let (m, cp) = search_and_update(&mut t, text, cur_pos);
        cur_pos = cp + 1;
        matched = m
    }
    t
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gencode_status() {
        let t = get_gencode_status(
            b"<?hh\n/**\n * This file is generated. Do not modify it manually!\n *\n * @generated SignedSource<<1234abcd>>\n * @codegen-command : buck run foo\n * @codegen-source : a/b.thrift\n */\n",
        );
        assert!(t.is_generated);
        assert!(t.fully_generated);
        assert_eq!(t.signature.as_deref(), Some("1234abcd"));
        assert_eq!(t.command.as_deref(), Some("buck run foo"));
        assert_eq!(t.source.as_deref(), Some("a/b.thrift"));
        let t = get_gencode_status(b"// @partially-generated\n");
        assert!(t.is_generated && !t.fully_generated);
        let t = get_gencode_status(b"<?hh\nclass C {}\n");
        assert!(!t.is_generated);
    }
}
