// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/cli_args.ml`. See `hh/PORTING.md`.
//!
//! The command-line arguments that describe saved states: the
//! `--with-mini-state` JSON (`get_saved_state_spec`) and the paths of the
//! files of a saved state, derived from its base path.
//!
//! The types are those of `Cli_args_sig.Types`, which `cli_args.ml`
//! includes. `Hg.Rev.t` is `string` (`Hg.Rev.of_string` is the identity).
//!
//! The exceptions that OCaml lets through to the callers of
//! `get_saved_state_spec` and `get_save_state_spec` (a far-away catch-all
//! handler, `Monitor_start.start`) are [`CliArgsError`], the error of the
//! outer `Result` of those functions (the inner one is the OCaml
//! `(_, string) result`): the `Yojson.Json_error` of input that is not JSON,
//! the `Sys_error` of a `from_file` that cannot be read, and the
//! `Assert_failure` of `Hh_json_helpers.get_string_exn` on an element of
//! `changes`, `prechecked_changes` or `naming_changes` that is not a string.

use std::sync::LazyLock;

use crate::hh_json_helpers;
use crate::hh_json_helpers::access;
use crate::hh_json_helpers::access::Keytrace;
use crate::hh_logger;
use crate::relative_path;
use crate::sys_utils;
use crate::yojson::safe as yojson;

// ~~ Cli_args_sig.Types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SavedStateTargetInfo {
    pub changes: Vec<relative_path::T>,
    pub naming_changes: Vec<relative_path::T>,
    /// `Hg.Rev.t`
    pub corresponding_base_revision: String,
    pub deptable_fn: String,
    pub compressed_deptable_fn: Option<String>,
    pub prechecked_changes: Vec<relative_path::T>,
    pub naming_table_path: String,
}

/// The idea of a file range necessarily means that the hypothetical list
/// of them is sorted in some way. It is valid to have None as either endpoint
/// because that simply makes it open-ended. For example, a range of files
/// { None - "/some/path" } includes all files with path less than /some/path
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FilesToCheckRange {
    pub from_prefix_incl: Option<relative_path::T>,
    pub to_prefix_excl: Option<relative_path::T>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FilesToCheckSpec {
    Range(FilesToCheckRange),
    Prefix(relative_path::T),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaveStateSpecInfo {
    pub files_to_check: Vec<FilesToCheckSpec>,
    /// The base name of the file into which we should save the naming table.
    pub filename: String,
    /// Indicates whether we should generate a state in the presence of errors.
    pub gen_with_errors: bool,
}

/// The exceptions that `get_saved_state_spec` and `get_save_state_spec` let
/// through.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CliArgsError {
    /// `Yojson.Json_error`
    JsonError(crate::yojson::JsonError),
    /// `Sys_error`
    SysError(sys_utils::SysError),
    /// `Assert_failure` (of `Hh_json_helpers.get_string_exn`)
    AssertFailure(hh_json_helpers::AssertFailure),
}

// ~~ Functions of `Hh_json_helpers` that `crate::hh_json_helpers` lacks ~~~~~~

/// `Access.(>>=)` when the function may also raise: what it raises is the
/// outer error.
fn access_bind_exn<A, B>(
    m: access::M<A>,
    f: impl FnOnce((A, Keytrace)) -> Result<access::M<B>, CliArgsError>,
) -> Result<access::M<B>, CliArgsError> {
    match m {
        Err(x) => Ok(Err(x)),
        Ok(x) => f(x),
    }
}

/// `Hh_json_helpers.get_string_exn`, whose `Assert_failure` is let through.
fn get_string_exn_or_raise(v: &yojson::T) -> Result<String, CliArgsError> {
    hh_json_helpers::get_string_exn(v)
        .cloned()
        .map_err(CliArgsError::AssertFailure)
}

/// `Yojson.Safe.from_string`, whose `Json_error` is let through.
fn yojson_from_string_or_raise(s: &str) -> Result<yojson::T, CliArgsError> {
    yojson::from_string(s).map_err(CliArgsError::JsonError)
}

// ~~ Cli_args ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn files_to_check_range_to_json(range: &FilesToCheckRange) -> yojson::T {
    let range_properties = match &range.to_prefix_excl {
        Some(to_prefix_excl) => vec![(
            "to_prefix_excl".to_string(),
            yojson::T::String(relative_path::suffix(to_prefix_excl)),
        )],
        None => vec![],
    };
    let range_properties = match &range.from_prefix_incl {
        Some(from_prefix_incl) => {
            let from_prefix_incl = (
                "from_prefix_incl".to_string(),
                yojson::T::String(relative_path::suffix(from_prefix_incl)),
            );
            let mut l = vec![from_prefix_incl];
            l.extend(range_properties);
            l
        }
        None => range_properties,
    };
    yojson::T::Assoc(range_properties)
}

pub fn files_to_check_spec_to_json(files_to_check_spec: &FilesToCheckSpec) -> yojson::T {
    match files_to_check_spec {
        FilesToCheckSpec::Range(range) => files_to_check_range_to_json(range),
        FilesToCheckSpec::Prefix(prefix) => yojson::T::String(relative_path::suffix(prefix)),
    }
}

pub fn get_save_state_spec_json(spec: &SaveStateSpecInfo) -> String {
    let files_to_check_spec_list = spec
        .files_to_check
        .iter()
        .map(files_to_check_spec_to_json)
        .collect();
    let properties: Vec<(String, yojson::T)> = vec![
        (
            "gen_with_errors".to_string(),
            yojson::T::Bool(spec.gen_with_errors),
        ),
        (
            "files_to_check".to_string(),
            yojson::T::List(files_to_check_spec_list),
        ),
        (
            "filename".to_string(),
            yojson::T::String(spec.filename.clone()),
        ),
    ];
    crate::yojson::safe::pretty_to_string(&yojson::T::Assoc(properties))
}

pub fn save_state_spec_json_example() -> SaveStateSpecInfo {
    SaveStateSpecInfo {
        files_to_check: vec![
            FilesToCheckSpec::Prefix(relative_path::from_root("/some/path/prefix1")),
            FilesToCheckSpec::Range(FilesToCheckRange {
                from_prefix_incl: Some(relative_path::from_root("/from/path/prefix1")),
                to_prefix_excl: Some(relative_path::from_root("/to/path/prefix1")),
            }),
            FilesToCheckSpec::Range(FilesToCheckRange {
                from_prefix_incl: Some(relative_path::from_root("/from/path/prefix2")),
                to_prefix_excl: Some(relative_path::from_root("/to/path/prefix2")),
            }),
            FilesToCheckSpec::Range(FilesToCheckRange {
                from_prefix_incl: Some(relative_path::from_root("/from/path/only")),
                to_prefix_excl: None,
            }),
            FilesToCheckSpec::Range(FilesToCheckRange {
                from_prefix_incl: None,
                to_prefix_excl: Some(relative_path::from_root("/to/path/only")),
            }),
        ],
        filename: "/some/dir/some_filename".to_string(),
        gen_with_errors: true,
    }
}

/// Computed once, like OCaml's toplevel value.
pub static SAVE_STATE_SPEC_JSON_DESCR: LazyLock<String> = LazyLock::new(|| {
    format!(
        "A JSON specification of how and what to save, e.g.:\n{}\n",
        get_save_state_spec_json(&save_state_spec_json_example())
    )
});

// TODO: gen examples
pub const SAVED_STATE_JSON_DESCR: &str = r#"A JSON specification for how to initialize with a saved state.

Saved state JSON looks like this:
{
  "state": <saved state filename>,
  "corresponding_base_revision" : <Mercurial commit hash>,
  "deptable": <dependency table filename>,
  "changes": [array of files changed since that saved state]
}

For example:
{
  "deptable": "/home/unixname/saved-states/ss1.sql",
  "state": "/home/unixname/saved-states/ss1",
  "changes": [],
  "prechecked_changes": [],
  "corresponding_base_revision": "bab0de0041defb4d7a5d520d224aa4922ed04d37"
}

You can put this saved state JSON into a file and pass this JSON as the argument:
{
  "from_file": "/home/unixname/saved-states/ss1.json"
}

Alternatively, you can pass this JSON as the argument, with the saved state JSON embedded:
{
  "data_dump":
  {
    "deptable": "/home/unixname/saved-states/ss1.sql",
    "state": "/home/unixname/saved-states/ss1",
    "changes": [],
    "prechecked_changes": [],
    "corresponding_base_revision": "bab0de0041defb4d7a5d520d224aa4922ed04d37"
  }
}
"#;

pub fn get_path(key: &str, json_obj: (&yojson::T, &Keytrace)) -> Option<relative_path::T> {
    let value = access::get_string(key, json_obj);
    match value {
        Ok((value, _keytrace)) => Some(relative_path::from_root(&value)),
        Err(_) => None,
    }
}

pub fn get_spec(spec_json: &yojson::T) -> FilesToCheckSpec {
    // `try ... with _ ->`: the `Assert_failure` of a value that is not a
    // string.
    match hh_json_helpers::get_string_exn(spec_json) {
        Ok(suffix) => FilesToCheckSpec::Prefix(relative_path::from_root(suffix)),
        Err(_) => {
            let from_prefix_incl = get_path("from_prefix_incl", (spec_json, &vec![]));
            let to_prefix_excl = get_path("to_prefix_excl", (spec_json, &vec![]));
            FilesToCheckSpec::Range(FilesToCheckRange {
                from_prefix_incl,
                to_prefix_excl,
            })
        }
    }
}

pub fn parse_save_state_json(
    (json, _keytrace): (&yojson::T, &Keytrace),
) -> access::M<SaveStateSpecInfo> {
    let files_to_check = crate::hh_json_helpers::get_field_opt(
        |v_keytrace| access::get_array("files_to_check", v_keytrace),
        json,
    )
    .unwrap_or_default();
    let files_to_check: Vec<FilesToCheckSpec> = files_to_check.iter().map(get_spec).collect();
    let json = access::return_(json.clone());
    access::bind(
        access::bind(json.clone(), |(v, k)| {
            access::get_string("filename", (&v, &k))
        }),
        |(filename, _filename_keytrace)| {
            access::bind(
                access::bind(json, |(v, k)| access::get_bool("gen_with_errors", (&v, &k))),
                |(gen_with_errors, _gen_with_errors_keytrace)| {
                    access::return_(SaveStateSpecInfo {
                        files_to_check,
                        filename,
                        gen_with_errors,
                    })
                },
            )
        },
    )
}

pub fn get_save_state_spec(
    v: Option<&str>,
) -> Result<Result<Option<SaveStateSpecInfo>, String>, CliArgsError> {
    Ok(match v {
        None => Ok(None),
        Some(blob) => {
            let json = yojson_from_string_or_raise(blob)?;
            let json = access::return_(json);
            let parsed_spec_result = access::bind(json, |(v, k)| parse_save_state_json((&v, &k)));
            match parsed_spec_result {
                Ok((parsed_spec, _keytrace)) => {
                    hh_logger::log("Parsed save state spec, everything's good");
                    Ok(Some(parsed_spec))
                }
                Err(spec_failure) => {
                    let message = format!(
                        "Parsing failed:\n{}\nSee input: {}\n",
                        access::access_failure_to_string(&spec_failure),
                        blob
                    );
                    Err(message)
                }
            }
        }
    })
}

/// What `get_string_exn` raises on an element of a list of changes is the
/// outer error.
pub fn parse_saved_state_json(
    (json, _keytrace): (&yojson::T, &Keytrace),
) -> Result<access::M<SavedStateTargetInfo>, CliArgsError> {
    let array_to_path_list = |files: &[yojson::T]| -> Result<Vec<relative_path::T>, CliArgsError> {
        files
            .iter()
            .map(|file| Ok(relative_path::from_root(&get_string_exn_or_raise(file)?)))
            .collect()
    };
    let prechecked_changes = crate::hh_json_helpers::get_field_opt(
        |v_keytrace| access::get_array("prechecked_changes", v_keytrace),
        json,
    );
    let prechecked_changes = prechecked_changes.unwrap_or_default();
    let json = access::return_(json.clone());
    let get = |key: &str| {
        let key = key.to_string();
        access::bind(json.clone(), move |(v, k)| {
            access::get_string(&key, (&v, &k))
        })
    };
    access_bind_exn(get("state"), |(state, _state_keytrace)| {
        access_bind_exn(
            get("corresponding_base_revision"),
            |(for_base_rev, _for_base_rev_keytrace)| {
                access_bind_exn(get("deptable"), |(deptable, _deptable_keytrace)| {
                    let compressed_deptable =
                        match access::to_option(access::bind(json.clone(), |(v, k)| {
                            access::get_val("compressed_deptable", (&v, &k))
                        })) {
                            Some(yojson::T::String(path)) => Some(path),
                            _ => None,
                        };
                    access_bind_exn(
                        access::bind(json.clone(), |(v, k)| {
                            access::get_array("changes", (&v, &k))
                        }),
                        |(changes, _)| {
                            let naming_changes = match access::bind(json.clone(), |(v, k)| {
                                access::get_val("naming_changes", (&v, &k))
                            }) {
                                Ok((yojson::T::List(files), _)) => array_to_path_list(&files)?,
                                _ => vec![],
                            };
                            let prechecked_changes = array_to_path_list(&prechecked_changes)?;
                            let changes = array_to_path_list(&changes)?;
                            Ok(access::return_(SavedStateTargetInfo {
                                naming_table_path: state,
                                // `Hg.Rev.of_string`
                                corresponding_base_revision: for_base_rev,
                                deptable_fn: deptable,
                                compressed_deptable_fn: compressed_deptable,
                                prechecked_changes,
                                changes,
                                naming_changes,
                            }))
                        },
                    )
                })
            },
        )
    })
}

pub fn get_saved_state_spec(
    v: Option<&str>,
) -> Result<Result<Option<SavedStateTargetInfo>, String>, CliArgsError> {
    Ok(match v {
        None => Ok(None),
        Some(blob) => {
            let json = yojson_from_string_or_raise(blob)?;
            let json = access::return_(json);
            let data_dump_parse_result = access_bind_exn(
                access::bind(json.clone(), |(v, k)| {
                    access::get_obj("data_dump", (&v, &k))
                }),
                |(v, k)| parse_saved_state_json((&v, &k)),
            )?;
            let from_file_parse_result = access_bind_exn(
                access::bind(json, |(v, k)| access::get_string("from_file", (&v, &k))),
                |(filename, _filename_keytrace)| {
                    let contents = sys_utils::cat(&filename).map_err(CliArgsError::SysError)?;
                    let json = yojson_from_string_or_raise(&String::from_utf8_lossy(&contents))?;
                    access_bind_exn(access::return_(json), |(v, k)| {
                        parse_saved_state_json((&v, &k))
                    })
                },
            )?;
            match (data_dump_parse_result, from_file_parse_result) {
                (Ok((parsed_data_dump, _)), Ok((_parsed_from_file, _))) => {
                    hh_logger::log(&format!(
                        "Warning - {}",
                        "Parsed saved state target from both JSON blob data dump".to_string()
                            + " and from contents of file."
                    ));
                    hh_logger::log("Preferring data dump result");
                    Ok(Some(parsed_data_dump))
                }
                (Ok((parsed_data_dump, _)), Err(_)) => Ok(Some(parsed_data_dump)),
                (Err(_), Ok((parsed_from_file, _))) => Ok(Some(parsed_from_file)),
                (Err(data_dump_failure), Err(from_file_failure)) => {
                    let message = format!(
                        "Parsing failed:\n  data dump failure: {}\n  from_file failure: {}\nSee input: {}\n",
                        access::access_failure_to_string(&data_dump_failure),
                        access::access_failure_to_string(&from_file_failure),
                        blob
                    );
                    Err(message)
                }
            }
        }
    })
}

pub fn legacy_hot_decls_path_for_target_info(info: &SavedStateTargetInfo) -> String {
    info.naming_table_path.clone() + ".decls"
}

pub fn shallow_hot_decls_path_for_target_info(info: &SavedStateTargetInfo) -> String {
    info.naming_table_path.clone() + ".shallowdecls"
}

pub fn naming_sqlite_path_for_target_info(info: &SavedStateTargetInfo) -> String {
    info.naming_table_path.clone() + "_naming.sql"
}

pub fn errors_path_for_target_info(info: &SavedStateTargetInfo) -> String {
    info.naming_table_path.clone() + ".err"
}

pub fn warnings_path_for_target_info(info: &SavedStateTargetInfo) -> String {
    info.naming_table_path.clone() + ".warn"
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rp(s: &str) -> relative_path::T {
        relative_path::from_root(s)
    }

    fn info() -> SavedStateTargetInfo {
        SavedStateTargetInfo {
            changes: vec![rp("a.php")],
            naming_changes: vec![],
            corresponding_base_revision: "abc".to_string(),
            deptable_fn: "/ss/b.hhdg".to_string(),
            compressed_deptable_fn: None,
            prechecked_changes: vec![],
            naming_table_path: "/ss/b".to_string(),
        }
    }

    const STATE: &str = r#"{"state": "/ss/b", "corresponding_base_revision": "abc", "deptable": "/ss/b.hhdg", "changes": ["a.php"]}"#;

    fn scratch_file(name: &str, contents: &str) -> String {
        let path =
            std::env::temp_dir().join(format!("hh_cli_args_{}_{}", name, std::process::id()));
        std::fs::write(&path, contents).unwrap();
        path.to_str().unwrap().to_string()
    }

    fn failure(blob: &str) -> String {
        get_saved_state_spec(Some(blob)).unwrap().unwrap_err()
    }

    #[test]
    fn saved_state_spec_forms() {
        assert_eq!(get_saved_state_spec(None).unwrap(), Ok(None));
        // data_dump
        let blob = format!(r#"{{"data_dump": {}}}"#, STATE);
        assert_eq!(get_saved_state_spec(Some(&blob)).unwrap(), Ok(Some(info())));
        // The optional keys.
        let blob = r#"{"data_dump": {"state": "/ss/b", "corresponding_base_revision": "abc",
            "deptable": "/ss/b.hhdg", "changes": [], "prechecked_changes": ["p.php"],
            "naming_changes": ["n.php", "m.php"], "compressed_deptable": "/ss/b.zhhdg"}}"#;
        assert_eq!(
            get_saved_state_spec(Some(blob)).unwrap(),
            Ok(Some(SavedStateTargetInfo {
                changes: vec![],
                naming_changes: vec![rp("n.php"), rp("m.php")],
                compressed_deptable_fn: Some("/ss/b.zhhdg".to_string()),
                prechecked_changes: vec![rp("p.php")],
                ..info()
            }))
        );
        // Optional keys of the wrong kind are ignored.
        let blob = r#"{"data_dump": {"state": "/ss/b", "corresponding_base_revision": "abc",
            "deptable": "/ss/b.hhdg", "changes": ["a.php"], "prechecked_changes": "p.php",
            "naming_changes": {}, "compressed_deptable": 1}}"#;
        assert_eq!(get_saved_state_spec(Some(blob)).unwrap(), Ok(Some(info())));
        // from_file
        let file = scratch_file("from_file", STATE);
        let blob = format!(r#"{{"from_file": "{}"}}"#, file);
        assert_eq!(get_saved_state_spec(Some(&blob)).unwrap(), Ok(Some(info())));
        // Both: data_dump wins.
        let blob = format!(
            r#"{{"from_file": "{}", "data_dump": {}}}"#,
            file,
            STATE.replace("/ss/b\"", "/dd/b\"")
        );
        assert_eq!(
            get_saved_state_spec(Some(&blob)).unwrap(),
            Ok(Some(SavedStateTargetInfo {
                naming_table_path: "/dd/b".to_string(),
                ..info()
            }))
        );
        // A broken data_dump falls back to from_file.
        let blob = format!(r#"{{"from_file": "{}", "data_dump": {{}}}}"#, file);
        assert_eq!(get_saved_state_spec(Some(&blob)).unwrap(), Ok(Some(info())));
        std::fs::remove_file(&file).unwrap();
    }

    #[test]
    fn saved_state_spec_errors() {
        assert_eq!(
            failure("{}"),
            "Parsing failed:\n  data dump failure: Missing key: data_dump\n  from_file failure: Missing key: from_file\nSee input: {}\n"
        );
        assert_eq!(
            failure("[]"),
            "Parsing failed:\n  data dump failure: Value is not an object \n  from_file failure: Value is not an object \nSee input: []\n"
        );
        // The keys are looked for in order; the keytrace is relative to the
        // inner object.
        let blob =
            r#"{"data_dump": {"state": "/b", "deptable": "/d", "changes": []}, "from_file": 3}"#;
        assert_eq!(
            failure(blob),
            format!(
                "Parsing failed:\n  data dump failure: Missing key: corresponding_base_revision\n  from_file failure: Value expected to be String (at field `from_file`)\nSee input: {}\n",
                blob
            )
        );
        let blob = r#"{"data_dump": {"state": "/b", "corresponding_base_revision": "r", "deptable": "/d", "changes": "a.php"}}"#;
        assert_eq!(
            failure(blob),
            format!(
                "Parsing failed:\n  data dump failure: Value expected to be Array (at field `changes`)\n  from_file failure: Missing key: from_file\nSee input: {}\n",
                blob
            )
        );
        let blob = r#"{"data_dump": 1}"#;
        assert_eq!(
            failure(blob),
            format!(
                "Parsing failed:\n  data dump failure: Value expected to be Object (at field `data_dump`)\n  from_file failure: Missing key: from_file\nSee input: {}\n",
                blob
            )
        );
    }

    #[test]
    fn saved_state_spec_exceptions() {
        // Not JSON: Yojson.Json_error.
        let e = get_saved_state_spec(Some("{")).unwrap_err();
        assert!(matches!(e, CliArgsError::JsonError(_)));
        // A from_file that cannot be read: Sys_error, even when data_dump is
        // good (both are parsed).
        let blob = format!(
            r#"{{"data_dump": {}, "from_file": "/nonexistent/ss.json"}}"#,
            STATE
        );
        let e = get_saved_state_spec(Some(&blob)).unwrap_err();
        assert_eq!(
            e,
            CliArgsError::SysError(sys_utils::SysError(
                "/nonexistent/ss.json: No such file or directory".to_string()
            ))
        );
        // A change that is not a string: Assert_failure.
        let blob = r#"{"data_dump": {"state": "/b", "corresponding_base_revision": "r", "deptable": "/d", "changes": [1]}}"#;
        let e = get_saved_state_spec(Some(blob)).unwrap_err();
        assert_eq!(
            e,
            CliArgsError::AssertFailure(hh_json_helpers::AssertFailure)
        );
    }

    #[test]
    fn saved_state_paths() {
        let info = info();
        assert_eq!(legacy_hot_decls_path_for_target_info(&info), "/ss/b.decls");
        assert_eq!(
            shallow_hot_decls_path_for_target_info(&info),
            "/ss/b.shallowdecls"
        );
        assert_eq!(
            naming_sqlite_path_for_target_info(&info),
            "/ss/b_naming.sql"
        );
        assert_eq!(errors_path_for_target_info(&info), "/ss/b.err");
        assert_eq!(warnings_path_for_target_info(&info), "/ss/b.warn");
    }

    #[test]
    fn save_state_spec() {
        assert_eq!(get_save_state_spec(None).unwrap(), Ok(None));
        let blob = r#"{"files_to_check": ["/p", {"from_prefix_incl": "/f"}, {"to_prefix_excl": 3}],
            "filename": "/out", "gen_with_errors": false}"#;
        assert_eq!(
            get_save_state_spec(Some(blob)).unwrap(),
            Ok(Some(SaveStateSpecInfo {
                files_to_check: vec![
                    FilesToCheckSpec::Prefix(rp("/p")),
                    FilesToCheckSpec::Range(FilesToCheckRange {
                        from_prefix_incl: Some(rp("/f")),
                        to_prefix_excl: None,
                    }),
                    FilesToCheckSpec::Range(FilesToCheckRange {
                        from_prefix_incl: None,
                        to_prefix_excl: None,
                    }),
                ],
                filename: "/out".to_string(),
                gen_with_errors: false,
            }))
        );
        let blob = r#"{"filename": "/out"}"#;
        assert_eq!(
            get_save_state_spec(Some(blob)).unwrap(),
            Err(format!(
                "Parsing failed:\nMissing key: gen_with_errors\nSee input: {}\n",
                blob
            ))
        );
        // The JSON of a spec reads back as the spec.
        let example = save_state_spec_json_example();
        assert_eq!(
            get_save_state_spec(Some(&get_save_state_spec_json(&example))).unwrap(),
            Ok(Some(example))
        );
        assert_eq!(
            *SAVE_STATE_SPEC_JSON_DESCR,
            r#"A JSON specification of how and what to save, e.g.:
{
  "gen_with_errors": true,
  "files_to_check": [
    "/some/path/prefix1",
    {
      "from_prefix_incl": "/from/path/prefix1",
      "to_prefix_excl": "/to/path/prefix1"
    },
    {
      "from_prefix_incl": "/from/path/prefix2",
      "to_prefix_excl": "/to/path/prefix2"
    },
    { "from_prefix_incl": "/from/path/only" },
    { "to_prefix_excl": "/to/path/only" }
  ],
  "filename": "/some/dir/some_filename"
}
"#
        );
    }

    #[test]
    fn saved_state_json_descr_is_the_ocaml_text() {
        assert!(SAVED_STATE_JSON_DESCR.starts_with(
            "A JSON specification for how to initialize with a saved state.\n\nSaved state JSON looks like this:\n{\n"
        ));
        assert!(SAVED_STATE_JSON_DESCR.ends_with(
            "    \"corresponding_base_revision\": \"bab0de0041defb4d7a5d520d224aa4922ed04d37\"\n  }\n}\n"
        ));
    }
}
