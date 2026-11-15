// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Indexer_options` (`write_symbol_info/indexer_options.ml`).

use oxidized::global_options::GlobalOptions;

use super::predicate::Failure;
use super::sym_hash;
use crate::hh_logger;
use crate::sys_utils;

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct T {
    /// if provided, create a file containing all php files referenced by the indexed files
    pub referenced_file: Option<String>,
    /// if provided, create a file containing all files actually reindexed within that run.
    pub reindexed_file: Option<String>,
    /// if true, will generate hack.IndexerInputsHash
    pub gen_sym_hash: bool,
    /// if true, generate ownership units
    pub ownership: bool,
    /// dir containing indexer facts
    pub out_dir: String,
    /// prefix for files in www, e.g. www
    pub root_path: String,
    /// prefix for files in fbcode, e.g. fbsource
    pub hhi_path: String,
    /// incremental runs (and only them) need an IndexerInputsHash table
    pub incremental: Option<sym_hash::T>,
}

pub fn create(writeopt: &GlobalOptions, out_dir: &str) -> Result<T, Failure> {
    // Ensure we are writing to fresh files
    let is_invalid = match std::fs::metadata(out_dir) {
        Ok(m) if !m.is_dir() => true,
        Ok(_) => match std::fs::read_dir(out_dir) {
            Ok(mut d) => d.next().is_some(),
            Err(_) => {
                let _ = sys_utils::mkdir_p(out_dir);
                false
            }
        },
        Err(_) => {
            let _ = sys_utils::mkdir_p(out_dir);
            false
        }
    };
    if is_invalid {
        return Err(Failure("JSON write directory is invalid or non-empty".to_string()));
    }
    Ok(T {
        referenced_file: writeopt.symbol_write_referenced_out.clone(),
        reindexed_file: writeopt.symbol_write_reindexed_out.clone(),
        gen_sym_hash: writeopt.symbol_write_sym_hash_out,
        ownership: writeopt.symbol_write_ownership,
        out_dir: out_dir.to_string(),
        root_path: writeopt.symbol_write_root_path.clone(),
        hhi_path: writeopt.symbol_write_hhi_path.clone(),
        incremental: match &writeopt.symbol_write_sym_hash_in {
            None => None,
            Some(path) => Some(sym_hash::read(path)?),
        },
    })
}

pub fn default(out_dir: &str) -> T {
    T {
        referenced_file: None,
        reindexed_file: None,
        ownership: false,
        out_dir: out_dir.to_string(),
        root_path: "www".to_string(),
        hhi_path: "hhi".to_string(),
        gen_sym_hash: false,
        incremental: None,
    }
}

pub fn log(opts: &T) {
    hh_logger::log(&format!("Ownership mode: {}", opts.ownership));
    hh_logger::log(&format!("Gen_sym_hash: {}", opts.gen_sym_hash));
    hh_logger::log(&format!("Writing JSON to: {}", opts.out_dir));
}
