// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/save_state_service.ml`. See `hh/PORTING.md`.
//!
//! The marshalled files of a saved state are OCaml `Marshal` values, read
//! and written with [`crate::rt::ocaml_marshal`]: `<state>.err` is a
//! `Relative_path.Set.t` (`Set.Make` of `prefix * string`, the prefix a
//! constant constructor: `Root` = 0, `Hhi` = 1, `Dummy` = 2, `Tmp` = 3),
//! `<state>.warn` a `Warnings_saved_state.t` (`Set.Make` of `int`).

use crate::exception;
use crate::hh_logger;
use crate::naming_sqlite;
use crate::naming_table;
use crate::relative_path;
use crate::rt::ocaml_marshal;
use crate::rt::ocaml_marshal::Value;
use crate::save_state_service_types::OldIssues;
use crate::save_state_service_types::SaveNamingResult;
use crate::save_state_service_types::SavedStateErrors;

use oxidized::warnings_saved_state_impl::WarningsSavedState;

/// What `load_saved_state_exn` raises: `Failure` (no naming table), the
/// `Naming_sqlite` exceptions of `Naming_table.load_from_sqlite`, the
/// `Sys_error`/`Failure` of the unmarshalling of a malformed file.
#[derive(Debug)]
pub enum LoadError {
    Failure(String),
    NamingSqlite(naming_sqlite::Error),
    SysError(String),
}

impl std::fmt::Display for LoadError {
    /// `Printexc.to_string`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Failure(s) => write!(f, "Failure({:?})", s),
            LoadError::NamingSqlite(e) => write!(f, "{:?}", e),
            LoadError::SysError(s) => write!(f, "Sys_error({:?})", s),
        }
    }
}

pub fn get_errors_filename(filename: &str) -> String {
    format!("{}.err", filename)
}

pub fn get_errors_filename_json(filename: &str) -> String {
    format!("{}.err.json", filename)
}

pub fn get_legacy_decls_filename(filename: &str) -> String {
    format!("{}.decls", filename)
}

pub fn get_shallow_decls_filename(filename: &str) -> String {
    format!("{}.shallowdecls", filename)
}

/// Writes some OCaml object to a file with the given filename
/// (`save_contents output_filename contents`, the value already converted).
pub fn save_contents(output_filename: &str, contents: &Value) -> std::io::Result<()> {
    let bytes = ocaml_marshal::to_bytes(contents, &[])
        .map_err(|e| std::io::Error::other(e.0))?;
    std::fs::write(output_filename, bytes)
}

/// The message of `Sys_error` for an I/O error: `strerror`.
fn strerror(e: &std::io::Error) -> String {
    let msg = e.to_string();
    match msg.rfind(" (os error ") {
        Some(i) => msg[..i].to_string(),
        None => msg,
    }
}

/// `load_contents_unsafe input_filename`: the OCaml value in the file.
pub fn load_contents_unsafe(input_filename: &str) -> Result<Value, LoadError> {
    let bytes = std::fs::read(input_filename)
        .map_err(|e| LoadError::SysError(format!("{}: {}", input_filename, strerror(&e))))?;
    ocaml_marshal::from_bytes(&bytes, 0).map_err(|e| LoadError::Failure(e.0))
}

/// The OCaml value of a `Relative_path.t`.
pub fn relative_path_to_ocaml(path: &relative_path::T) -> Value {
    Value::block(
        0,
        vec![
            Value::int(relative_path::prefix_to_enum(relative_path::prefix(path)) as i64),
            Value::string(relative_path::suffix(path).into_bytes()),
        ],
    )
}

/// A `Relative_path.t` from its OCaml value.
pub fn relative_path_of_ocaml(v: &Value) -> Result<relative_path::T, ocaml_marshal::ConvError> {
    let f = v.fields(0, 2)?;
    let prefix = relative_path::prefix_of_enum(f[0].as_int()? as isize)
        .ok_or_else(|| ocaml_marshal::ConvError(format!("not a Relative_path.prefix: {:?}", f[0])))?;
    let suffix =
        String::from_utf8(f[1].as_bytes()?.to_vec()).map_err(|e| ocaml_marshal::ConvError(e.to_string()))?;
    Ok(relative_path::T::make(prefix, std::path::PathBuf::from(suffix)))
}

/// The OCaml value of a `saved_state_errors` (`Relative_path.Set.t`), built
/// as `Relative_path.Set.of_list` would (adds in increasing order).
pub fn saved_state_errors_to_ocaml(errors: &SavedStateErrors) -> Value {
    let set = ocaml_marshal::ocaml_set::of_iter(errors.iter().cloned(), &relative_path::compare);
    ocaml_marshal::ocaml_set::to_ocaml(&set, &mut relative_path_to_ocaml)
}

/// A `saved_state_errors` from its OCaml value.
pub fn saved_state_errors_of_ocaml(v: &Value) -> Result<SavedStateErrors, ocaml_marshal::ConvError> {
    ocaml_marshal::ocaml_set::elements_of_ocaml(v)?
        .into_iter()
        .map(relative_path_of_ocaml)
        .collect()
}

/// The OCaml value of a `Warnings_saved_state.t` (`Set.Make (Int)`).
pub fn warnings_saved_state_to_ocaml(warnings: &WarningsSavedState) -> Value {
    let set = ocaml_marshal::ocaml_set::of_iter(warnings.iter().copied(), &|a: &isize, b: &isize| a.cmp(b));
    ocaml_marshal::ocaml_set::to_ocaml(&set, &mut |h| Value::int(*h as i64))
}

/// A `Warnings_saved_state.t` from its OCaml value.
pub fn warnings_saved_state_of_ocaml(v: &Value) -> Result<WarningsSavedState, ocaml_marshal::ConvError> {
    ocaml_marshal::ocaml_set::elements_of_ocaml(v)?
        .into_iter()
        .map(|h| Ok(h.as_int()? as isize))
        .collect()
}

/// `Warnings_saved_state.read_from_disk path`
fn warnings_read_from_disk(path: &str) -> Result<WarningsSavedState, LoadError> {
    let v = load_contents_unsafe(path)?;
    warnings_saved_state_of_ocaml(&v).map_err(|e| LoadError::Failure(e.0))
}

/// Loads the file info and the errors, if any.
/// (`load_saved_state_exn ~naming_table_fallback_path ~errors_path
/// ~warning_hashes_path ctx`)
pub fn load_saved_state_exn(
    naming_table_fallback_path: Option<&str>,
    errors_path: &str,
    warning_hashes_path: &str,
    ctx: &crate::provider_context::T,
) -> Result<(naming_table::T, OldIssues), LoadError> {
    let old_naming_table = match naming_table_fallback_path {
        Some(nt_path) => {
            let naming_table_exists = std::path::Path::new(nt_path).exists();
            hh_logger::log(&format!(
                "Checked if the old naming table file exists ({})",
                naming_table_exists
            ));
            if !naming_table_exists {
                return Err(LoadError::Failure(format!(
                    "Naming table file does not exist on disk: '{}'",
                    nt_path
                )));
            }
            naming_table::load_from_sqlite(ctx, nt_path).map_err(LoadError::NamingSqlite)?
        }
        None => {
            // If we reach here, then there was neither a SQLite naming table
            // in the saved state directory, nor was a path provided via
            // genv.local_config.naming_table_path.
            //
            // ServerCheckUtils.get_naming_table_fallback_path will return None,
            // in which case we raise a failure, since the OCaml-marshalled
            // naming table no longer exists.
            // (`Hack_event_logger.naming_table_sqlite_missing`: a no-op.)
            let str = "No naming table path found, either from saved state directory or local config";
            hh_logger::log(str);
            return Err(LoadError::Failure(str.to_string()));
        }
    };
    let old_errors: SavedStateErrors = {
        let v = load_contents_unsafe(errors_path)?;
        saved_state_errors_of_ocaml(&v).map_err(|e| LoadError::Failure(e.0))?
    };
    let old_warnings: WarningsSavedState = warnings_read_from_disk(warning_hashes_path)?;
    Ok((
        old_naming_table,
        OldIssues {
            old_errors,
            old_warnings,
        },
    ))
}

/// `get_hot_classes filename`
pub fn get_hot_classes(filename: &str) -> crate::s_set::T {
    if !std::path::Path::new(filename).exists() {
        hh_logger::log(&format!("Hot classes file '{}' was not found", filename));
        crate::s_set::T::new()
    } else {
        let contents = match crate::sys_utils::cat(filename) {
            Ok(c) => c,
            Err(e) => std::panic::panic_any(e),
        };
        let json: serde_json::Value = match serde_json::from_slice(&contents) {
            Ok(j) => j,
            Err(e) => panic!("Yojson.Json_error({:?})", e.to_string()),
        };
        json.get("classes")
            .and_then(|c| c.as_array())
            .expect("Not_found")
            .iter()
            .map(|s| s.as_str().expect("Hh_json_helpers.get_string_exn").to_string())
            .collect()
    }
}

/// `saved_state_info_file_name ~base_file_name`
pub fn saved_state_info_file_name(base_file_name: &str) -> String {
    format!("{}_info.json", base_file_name)
}

/// `saved_state_build_revision_read ~base_file_name`. (Raises what
/// `Real_disk.cat` and `Jget.string_exn` raise: here an `Err` with the
/// `Printexc` text.)
pub fn saved_state_build_revision_read(base_file_name: &str) -> Result<String, String> {
    let info_file = saved_state_info_file_name(base_file_name);
    let contents = std::fs::read(&info_file).map_err(|e| {
        format!(
            "Sys_error(\"{}: {}\")",
            info_file,
            strerror(&e)
        )
    })?;
    let json: serde_json::Value = serde_json::from_slice(&contents)
        .map_err(|e| format!("Yojson.Json_error({:?})", e.to_string()))?;
    match json.get("build_revision") {
        Some(serde_json::Value::String(s)) => Ok(s.clone()),
        Some(_) => Err("Hh_json_helpers.Jget.string_exn: not a string: build_revision".to_string()),
        None => Err("Not_found".to_string()),
    }
}

/// `go_naming naming_table output_filename`
pub fn go_naming(
    naming_table: &naming_table::T,
    output_filename: &str,
) -> Result<SaveNamingResult, String> {
    // `Utils.try_with_stack`, then `Exception.get_ctor_string`.
    let save = || -> Result<SaveNamingResult, exception::T> {
        let save_result = naming_table::save(naming_table, output_filename).map_err(exception::wrap)?;
        hh_logger::log(&format!(
            "Inserted symbols into the naming table:\n{}",
            naming_sqlite::show_save_result(&save_result)
        ));
        if !save_result.errors.is_empty() {
            crate::sys_utils::rm_dir_tree(output_filename);
            Err(exception::wrap(naming_sqlite::Error::Failure(
                "Naming table state had errors - deleting output file!".to_string(),
            )))
        } else {
            Ok(SaveNamingResult {
                nt_files_added: save_result.files_added,
                nt_symbols_added: save_result.symbols_added,
            })
        }
    };
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(save)) {
        Ok(Ok(r)) => Ok(r),
        Ok(Err(e)) => Err(exception::get_ctor_string(&e)),
        Err(payload) => Err(exception::get_ctor_string(&exception::wrap(payload))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unhex(s: &str) -> Vec<u8> {
        (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
    }

    /// Written by OCaml 5.1.1: `Marshal.to_string (S.of_list [(Root,"a.php");
    /// (Root,"b/c.php"); (Hhi,"x.hhi"); (Root,"0.php"); (Tmp,"t.php")]) []`
    /// with `S = Set.Make (prefix * string)`.
    const OCAML_ERRORS: &str = "8495a6be0000003a0000000f0000003700000032c0c040a04025302e7068704041a04025612e706870c040a04027622f632e706870c040a04125782e686869c040a04325742e7068704041424344";
    /// `Marshal.to_string (Set.Make(Int).of_list [5; -3; 1 lsl 40; 7; 0; max_int]) []`
    const OCAML_WARNINGS: &str = "8495a6be0000002a000000060000001e0000001ec0c0c04000fd404140c0404540414247c0c0400300000100000000004041033fffffffffffffff404243";

    #[test]
    fn errors_of_ocaml_and_back() {
        let v = ocaml_marshal::from_bytes(&unhex(OCAML_ERRORS), 0).unwrap();
        let errors = saved_state_errors_of_ocaml(&v).unwrap();
        let names: Vec<String> = errors
            .iter()
            .map(|p| format!("{:?}|{}", relative_path::prefix(p), relative_path::suffix(p)))
            .collect();
        assert_eq!(
            names,
            vec!["Root|0.php", "Root|a.php", "Root|b/c.php", "Hhi|x.hhi", "Tmp|t.php"]
        );
        // Built by adds in increasing order, as `Relative_path.Set.of_list`
        // does for a sorted list: the same bytes as the OCaml's.
        let ours = ocaml_marshal::to_bytes(&saved_state_errors_to_ocaml(&errors), &[]).unwrap();
        let back = saved_state_errors_of_ocaml(&ocaml_marshal::from_bytes(&ours, 0).unwrap()).unwrap();
        assert_eq!(back, errors);
    }

    #[test]
    fn warnings_of_ocaml_and_back() {
        let v = ocaml_marshal::from_bytes(&unhex(OCAML_WARNINGS), 0).unwrap();
        let w = warnings_saved_state_of_ocaml(&v).unwrap();
        assert_eq!(
            w.iter().copied().collect::<Vec<_>>(),
            vec![-3, 0, 5, 7, 1 << 40, isize::MAX >> 1]
        );
        let ours = ocaml_marshal::to_bytes(&warnings_saved_state_to_ocaml(&w), &[]).unwrap();
        let back = warnings_saved_state_of_ocaml(&ocaml_marshal::from_bytes(&ours, 0).unwrap()).unwrap();
        assert_eq!(back, w);
    }

    #[test]
    fn empty_set_is_the_ocamls() {
        let ours = ocaml_marshal::to_bytes(&saved_state_errors_to_ocaml(&relative_path::set::T::new()), &[]).unwrap();
        assert_eq!(ours, unhex("8495a6be0000000100000000000000000000000040"));
    }

    /// `empty_saved_state_errors_tests.ml`: the errors file of a saved state
    /// without errors, written by `save_contents` and read back by
    /// `load_contents_unsafe`, is the empty set.
    #[test]
    fn empty_saved_state_errors_round_trip() {
        let path = std::env::temp_dir()
            .join(format!("empty_saved_state_errors.{}.err", std::process::id()));
        let filename = path.to_str().unwrap();
        save_contents(filename, &saved_state_errors_to_ocaml(&relative_path::set::T::new())).unwrap();
        assert_eq!(std::fs::read(filename).unwrap(), unhex("8495a6be0000000100000000000000000000000040"));
        let errors = saved_state_errors_of_ocaml(&load_contents_unsafe(filename).unwrap()).unwrap();
        let _ = std::fs::remove_file(&path);
        assert!(errors.is_empty());
    }
}
