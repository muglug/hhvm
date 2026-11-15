// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Sym_hash` (`write_symbol_info/sym_hash.ml`).

use std::collections::BTreeSet;
use std::io::Read;

use super::glean::util::base64_decode_exn;
use super::predicate::Failure;
use crate::hh_logger;

/// Set of Md5.t hashes: the concatenation of hashes, sorted in lexicographic
/// order.
pub type T = Vec<u8>;

/// `Md5.t`: the 16 bytes of the digest.
pub type Md5 = [u8; 16];

pub fn mem(t: &T, h: &Md5) -> bool {
    let md5_bin: &[u8] = h;
    fn binary_search(t: &T, md5_bin: &[u8], i: usize, j: usize) -> bool {
        // assume inclusive bound
        assert!(i <= j);
        let m = (i + j) / 2;
        let m_h = &t[m * 16..m * 16 + 16];
        if i == j {
            m_h == md5_bin
        } else if m_h < md5_bin {
            binary_search(t, md5_bin, m + 1, j)
        } else {
            binary_search(t, md5_bin, i, m)
        }
    }
    // (`(String.length t / 16) - 1` is -1 for an empty table, and the
    // `assert` fails; `read` never makes one.)
    if t.len() < 16 {
        panic!("Assert_failure write_symbol_info/sym_hash.ml")
    }
    binary_search(t, md5_bin, 0, (t.len() / 16) - 1)
}

/// Construct a [t] from file [path]. File is a string of concatenated
/// base64-encoded md5 hash. Fails if file doesn't exist or unable to
/// deserialize
pub fn read(path: &str) -> Result<T, Failure> {
    hh_logger::log(&format!("Reading hash table {}", path));
    let mut channel = match std::fs::File::open(path) {
        Ok(f) => f,
        Err(e) => {
            // `Sys_utils.open_in_no_fail`
            eprint!(
                "Could not In_channel.create: '{}' (Sys_error(\"{}: {}\"))\n",
                path,
                path,
                strerror(&e)
            );
            std::process::exit(3)
        }
    };
    let mut set = BTreeSet::new();
    loop {
        let mut buf = [0u8; 24];
        // `really_input_string channel 24`: `End_of_file` when fewer than 24
        // bytes are left.
        if read_exact_or_eof(&mut channel, &mut buf) {
            break;
        }
        let decoded = base64_decode_exn(&buf).map_err(|m| Failure(format!("Invalid_argument {:?}", m)))?;
        if decoded.len() < 16 {
            return Err(Failure("Invalid_argument \"String.sub / Bytes.sub\"".to_string()));
        }
        set.insert(decoded[..16].to_vec());
    }
    let res: Vec<u8> = set.iter().flatten().copied().collect();
    hh_logger::log(&format!("Sym table has {} element", set.len() / 16));
    if res.is_empty() {
        return Err(Failure("Hash table is empty".to_string()));
    }
    if res.len() % 16 != 0 {
        return Err(Failure("Hash table has incorrect format".to_string()));
    }
    Ok(res)
}

/// Fills `buf`; true at the end of the file (fewer bytes than `buf` left).
fn read_exact_or_eof(r: &mut impl Read, buf: &mut [u8]) -> bool {
    let mut n = 0;
    while n < buf.len() {
        match r.read(&mut buf[n..]) {
            Ok(0) => return true,
            Ok(k) => n += k,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(_) => return true,
        }
    }
    false
}

/// `Unix.error_message` of the error of an `open`: the text of `Display`
/// without its ` (os error N)`.
fn strerror(e: &std::io::Error) -> String {
    let s = e.to_string();
    match s.find(" (os error") {
        Some(i) => s[..i].to_string(),
        None => s,
    }
}
