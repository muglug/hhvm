// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Indexable` (`write_symbol_info/indexable.ml`).

use relative_path::Prefix;

use super::predicate::Failure;
use crate::naming_table;
use crate::path;
use crate::relative_path;
use crate::yojson::safe as yojson;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct T {
    pub path: relative_path::T,
    pub fanout: bool,
}

pub fn from_file(path: relative_path::T) -> T {
    T { path, fanout: true }
}

fn parse_line(s: &str) -> Result<T, Failure> {
    if s.starts_with('{') {
        match yojson::from_string(s) {
            Ok(yojson::T::Assoc(l)) => match l.as_slice() {
                [(k1, yojson::T::String(p)), (k2, yojson::T::Bool(f))] if k1 == "path" && k2 == "fanout" => Ok(T {
                    path: relative_path::storage_of_string(p),
                    fanout: *f,
                }),
                _ => Err(Failure("Can't parse paths file".to_string())),
            },
            Ok(_) => Err(Failure("Can't parse paths file".to_string())),
            Err(e) => Err(Failure(e.to_string())),
        }
    } else {
        // for backward compatibility
        Ok(T {
            path: relative_path::storage_of_string(s),
            fanout: false,
        })
    }
}

/// Compute files to index based on list of files provided on the CLI, and
/// from a paths file. Two forms are accepted for lines in [paths_file].
///
/// Legacy format: "prefix|rel_path", e.g.
///
///     hhi|builtins_fb.hhi
///     root|scripts/whatsapp/erl/regd/cfg/list_fb_car
///
/// JSON: { path = "prefix|rel_path", fanout = bool }
///
/// If [with_hhi] is provided, results include the built-in hhi files.
///
/// See also [symbol_file_info.mli] for role of [fanout] flag
pub fn from_options(paths: &[String], paths_file: Option<&str>, include_hhi: bool) -> Result<Vec<T>, Failure> {
    let hhi_root = path::make(&relative_path::path_of_prefix(Prefix::Hhi).map_err(|e| Failure(e.0))?);
    let hhi_files: Vec<T> = if include_hhi {
        hhi_contents_names(&path::to_string(&hhi_root))
            .iter()
            .filter(|fn_| !fn_.starts_with("hsl_generated"))
            .map(|fn_| {
                from_file(relative_path::create(
                    Prefix::Hhi,
                    &path::to_string(&path::concat(&hhi_root, fn_)),
                ))
            })
            .collect()
    } else {
        vec![]
    };
    let relative_path_exists = |r: &relative_path::T| std::path::Path::new(&relative_path::to_absolute(r)).exists();
    let mut res = vec![];
    if let Some(paths_file) = paths_file {
        let contents = std::fs::read_to_string(paths_file)
            .map_err(|e| Failure(format!("{}: {}", paths_file, e)))?;
        // (`In_channel.read_lines`: the lines without their `\n`, and no
        // empty last line after a final newline.)
        for line in contents.lines() {
            res.push(parse_line(line)?);
        }
    }
    res.extend(hhi_files);
    res.extend(
        paths
            .iter()
            .map(|path| relative_path::from_root(path))
            .filter(relative_path_exists)
            .map(from_file),
    );
    Ok(res)
}

/// The names of `Hhi.get_raw_hhi_contents ()`, in its order. The OCaml's
/// array is made when the OCaml is built (`Hhi_get.get_hhis`), in the order
/// in which its directory walk (`get_recursive_files`, which conses the
/// directories and the files it finds, then `get_hhis_in_dir`, which conses
/// them again) meets the files: that of `Sys.readdir` on the hhi directory
/// of the build. The crate's `hhi::HHI_CONTENTS` are sorted by name instead.
/// Here the same walk is made over the hhi files extracted at startup (the
/// directory of the `Hhi` prefix, which has the same files): where the order
/// of `readdir` depends only on the names (APFS, where the oracle was built,
/// lists the extracted directory as the sources), the order is the OCaml's.
fn hhi_contents_names(root: &str) -> Vec<String> {
    let root = root.trim_end_matches('/');
    let mut dirs: Vec<String> = vec![root.to_string()];
    // `files`, the head of the OCaml list last.
    let mut files: Vec<String> = vec![];
    while let Some(d) = (!dirs.is_empty()).then(|| dirs.remove(0)) {
        let curr_files: Vec<String> = match std::fs::read_dir(&d) {
            Ok(rd) => rd.filter_map(|e| e.ok()).map(|e| e.file_name().to_string_lossy().into_owned()).collect(),
            Err(_) => vec![],
        };
        let mut d_acc = vec![];
        for f in curr_files {
            let f = format!("{}/{}", d, f);
            if std::path::Path::new(&f).is_dir() {
                d_acc.insert(0, f)
            } else {
                files.push(f)
            }
        }
        d_acc.extend(dirs);
        dirs = d_acc;
    }
    // `get_hhis_in_dir`: the fold over the OCaml list (from its head, the
    // last file found) conses: the files in the order they were found.
    let dir_offset = root.len() + 1;
    files
        .into_iter()
        .filter(|f| f.ends_with("hhi"))
        .map(|f| f[dir_offset..].to_string())
        .collect()
}

/// Get the list of files from the naming table, with possible exclusions.
/// hh should be run in full-init mode if we want the list of all files to index
pub fn from_naming_table(naming_table: &naming_table::T, include_hhi: bool, ignore_paths: &[String]) -> Vec<T> {
    let defs_per_file = naming_table::to_defs_per_file(naming_table, None);
    // (`Relative_path.Map.fold` consing: the files in decreasing order.)
    let mut acc = vec![];
    for path in defs_per_file.keys() {
        match naming_table::get_file_info(naming_table, path) {
            None => {}
            Some(_) => {
                let path_str = relative_path::storage_to_string(path);
                if relative_path::is_hhi(path.prefix())
                    && (!include_hhi || path_str.starts_with("hhi|hsl_generated"))
                    || ignore_paths.iter().any(|ignore| path_str == *ignore)
                {
                } else {
                    acc.push(from_file(path.clone()))
                }
            }
        }
    }
    acc.reverse();
    acc
}
