// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `search/local_search_service.ml`. See `hh/PORTING.md`.
//!
//! The index of the `LocalIndex` provider: the `si_fullitem`s of each file
//! (`lss_fullitems`), searched with `Str.string_partial_match` of
//! `Str.regexp_case_fold (Str.quote query_text)` at 0 (`Str` folds case with
//! `Char.lowercase_ascii`): an ASCII case-insensitive comparison of bytes in
//! which a name matches if it starts with the query, and also if the query
//! starts with it (the "partial" match: the name `t` matches the query
//! `team_bi`).

use std::sync::Arc;

use crate::file_info;
use crate::file_info::SiAddendum;
use crate::file_info::SiKind;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::search_types;
use crate::search_types::AutocompleteType;
use crate::search_types::SiFile;
use crate::search_types::SiItem;
use crate::search_utils;
use crate::search_utils::SiCapture;
use crate::search_utils::SiEnv;
use crate::search_utils::SiFullitem;
use crate::utils;

/// How many locally changed files are in this env?
pub fn count_local_fileinfos(sienv: &SiEnv) -> isize {
    sienv.lss_fullitems.len() as isize
}

/// Relative paths sometimes produce doubled-up slashes, as in
/// "/path/to/root//subpath/file".  When we extract the suffix
/// from a relative_path.t, clear out any preceding slash.
pub fn strip_first_char(char: u8, s: &str) -> &str {
    if s.is_empty() || s.as_bytes()[0] != char {
        s
    } else {
        // `String.sub s ~pos:1 ~len:(String.length s - 1)` (bytes)
        // (The first byte is the ASCII `char`, so the slice is at a
        // character boundary.)
        &s[1..]
    }
}

/// `Shared_mem_hash.hash_string`: the first 8 bytes of the MD5 digest of
/// the string (`Digest.string`), read as a native-endian (little-endian on
/// the platforms the OCaml supports) `int64` (`hh_get_hash_ocaml`).
fn shared_mem_hash_string(s: &str) -> i64 {
    use md5::Digest;
    let digest = md5::Md5::digest(s.as_bytes());
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&digest[..8]);
    i64::from_ne_bytes(bytes)
}

/// Determine a tombstone for a file path
pub fn get_tombstone(path: &RelativePath) -> i64 {
    let rel_path_str = relative_path::suffix(path);
    let fixed_path_str = strip_first_char(b'/', &rel_path_str);
    shared_mem_hash_string(fixed_path_str)
}

/// Updates symbol index from [si_addendum] generated from a previous parse of the file.
pub fn update_file_from_addenda(sienv: &SiEnv, path: &RelativePath, addenda: &[SiAddendum]) -> SiEnv {
    let mut sienv = sienv.clone();
    update_file_from_addenda_in_place(&mut sienv, path, addenda);
    sienv
}

/// [`update_file_from_addenda`] on an environment that the caller owns
/// (`Symbol_index_core.update_from_addenda` folds over many files: the
/// persistent maps are then changed in place instead of copied, which is
/// what makes building the index of a large root take a fraction of a
/// second; the result is the same).
pub fn update_file_from_addenda_in_place(sienv: &mut SiEnv, path: &RelativePath, addenda: &[SiAddendum]) {
    let tombstone = get_tombstone(path);
    let filepath: Arc<str> = Arc::from(relative_path::suffix(path));
    let contents: SiCapture = addenda
        .iter()
        .map(|addendum| SiFullitem {
            name: addendum.name.clone(),
            kind: addendum.kind,
            filepath: Arc::clone(&filepath),
            is_abstract: addendum.is_abstract,
            is_final: addendum.is_final,
        })
        .collect();
    sienv.lss_fullitems.insert(path.clone(), Arc::new(contents));
    sienv.lss_tombstones.insert(path.clone());
    sienv.lss_tombstone_hashes.insert(tombstone);
}

/// Remove files from local when they are deleted
pub fn remove_file(sienv: &SiEnv, path: &RelativePath) -> SiEnv {
    let mut sienv = sienv.clone();
    remove_file_in_place(&mut sienv, path);
    sienv
}

/// [`remove_file`] on an environment that the caller owns (see
/// [`update_file_from_addenda_in_place`]).
pub fn remove_file_in_place(sienv: &mut SiEnv, path: &RelativePath) {
    let tombstone = get_tombstone(path);
    sienv.lss_fullitems.remove(path);
    sienv.lss_tombstones.insert(path.clone());
    sienv.lss_tombstone_hashes.insert(tombstone);
}

/// `Str.string_partial_match (Str.regexp_case_fold (Str.quote query_text)) s 0`:
/// the regexp matches a prefix of `s`, or `s` is a prefix of a string that
/// the regexp matches (`s` ends before the match is complete). For a quoted
/// literal: case-insensitively, `s` starts with `query_text` or
/// `query_text` starts with `s`.
fn partial_match_case_fold(query_text: &[u8], s: &[u8]) -> bool {
    let n = std::cmp::min(query_text.len(), s.len());
    s[..n].eq_ignore_ascii_case(&query_text[..n])
}

/// Search local changes for symbols matching this prefix
pub fn search_local_symbols(
    sienv: &SiEnv,
    query_text: &str,
    max_results: isize,
    context: AutocompleteType,
    kind_filter: Option<SiKind>,
) -> Vec<SiItem> {
    // case insensitive search, must include namespace, escaped for regex
    let query_text_regex_case_insensitive = query_text.as_bytes();
    // case insensitive search, break out if max results reached
    //
    // The OCaml accumulates the matches of a file by prepending them (so
    // newest first) and raises `BreakOutOfScan acc_new` when that file's
    // accumulator alone reaches `max_results`; the accumulator here is
    // built in the reverse order (oldest first) and reversed when it is
    // returned.
    enum Scan {
        Continue,
        BreakOutOfScan,
    }
    let check_symbol_and_add_to_accumulator_and_break_if_max_reached =
        |acc: &mut Vec<SiItem>,
         symbol: &SiFullitem,
         context: AutocompleteType,
         kind_filter: Option<SiKind>,
         path: &RelativePath|
         -> Scan {
            let is_valid_match = match (context, kind_filter) {
                (AutocompleteType::Actype, _) => search_types::valid_for_actype(symbol.kind),
                (AutocompleteType::Acnew, _) => {
                    search_types::valid_for_acnew(symbol.kind) && !symbol.is_abstract
                }
                (AutocompleteType::Acclassish, _) => {
                    search_types::valid_for_acclassish(symbol.kind)
                }
                (AutocompleteType::Acid, _) => search_types::valid_for_acid(symbol.kind),
                (AutocompleteType::ActraitOnly, _) => search_utils::is_si_trait(symbol.kind),
                (AutocompleteType::AcWorkspaceSymbol, Some(kind_match)) => {
                    file_info::equal_si_kind(symbol.kind, kind_match)
                }
                (AutocompleteType::AcWorkspaceSymbol, None) => true,
            };
            if is_valid_match
                && partial_match_case_fold(query_text_regex_case_insensitive, symbol.name.as_bytes())
            {
                // Only strip Hack namespaces. XHP must have a preceding colon
                let fullname = utils::strip_ns(&symbol.name);
                acc.push(SiItem {
                    name: fullname.to_string(),
                    kind: symbol.kind,
                    file: SiFile::SIPath(path.clone()),
                    fullname: fullname.to_string(),
                });
                if acc.len() as isize >= max_results {
                    Scan::BreakOutOfScan
                } else {
                    Scan::Continue
                }
            } else {
                Scan::Continue
            }
        };
    let mut acc: Vec<SiItem> = vec![];
    for (path, fullitems) in sienv.lss_fullitems.iter() {
        let mut matches: Vec<SiItem> = vec![];
        for symbol in fullitems.iter() {
            match check_symbol_and_add_to_accumulator_and_break_if_max_reached(
                &mut matches,
                symbol,
                context,
                kind_filter,
                path,
            ) {
                Scan::Continue => {}
                Scan::BreakOutOfScan => {
                    // `BreakOutOfScan acc_new`: only this file's matches.
                    matches.reverse();
                    return matches;
                }
            }
        }
        matches.reverse();
        // `List.append acc matches`
        acc.extend(matches);
    }
    acc
}

/// Filter the results to extract any dead objects
pub fn extract_dead_results(sienv: &SiEnv, results: Vec<SiItem>) -> Vec<SiItem> {
    results
        .into_iter()
        .filter(|item| match &item.file {
            SiFile::SIPath(path) => !sienv.lss_tombstones.contains(path),
            SiFile::SIFilehash(hash_str) => {
                // `Int64.of_string` (raises `Failure "Int64.of_string"` on
                // a malformed string).
                let hash = crate::rt::ocaml_stdlib::int64_of_string(hash_str);
                !sienv.lss_tombstone_hashes.contains(&hash)
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn case_fold_prefix() {
        assert!(partial_match_case_fold(b"foo", b"FooBar"));
        assert!(partial_match_case_fold(b"", b"x"));
        // A name that is a prefix of the query is a partial match.
        assert!(partial_match_case_fold(b"foob", b"FOO"));
        assert!(partial_match_case_fold(b"team_bi", b"t"));
        assert!(!partial_match_case_fold(b"bar", b"FooBar"));
    }
}
