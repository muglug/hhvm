// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_check_utils.ml`.
//!
//! Owned by **S1** (plan §3.1).
//!
//! `get_check_info` gives the typing service's [`CheckInfo`]: the fields of
//! the OCaml's `check_info` that only the OCaml's workers, profiling,
//! memtrace or decl prefetching read (`init_id`, `recheck_id`,
//! `per_file_profiling`, `memtrace_dir`, `heartbeat_interval`,
//! `prefetch_decls_*`) have no counterpart there; the daemon keeps the
//! diagnostics an `HH_FIXME` suppresses (`~drop_fixmed:false`).

use crate::file_info;
use crate::hh_logger;
use crate::naming_table;
use crate::relative_path;
use crate::rt::ocaml_str;
use crate::rt::ocaml_unix::gettimeofday;
use crate::s_set;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::typing_check_service::CheckInfo;
use crate::yojson::safe as yojson;

type RPSet = crate::relative_path::set::T;
type RPMap<A> = crate::relative_path::map::T<A>;

/// `get_naming_table_fallback_path genv`
pub fn get_naming_table_fallback_path(genv: &Genv) -> Option<String> {
    match &genv.local_config.naming_sqlite_path {
        Some(path) => {
            hh_logger::log(&format!("Loading naming table path from config: {}", path));
            Some(path.clone())
        }
        None => {
            hh_logger::log("No path set in config, using the loaded naming table");
            None
        }
    }
}

/// [extend_defs_per_file_sequential defs_per_file naming_table additional_files]
/// extends [defs_per_file] file-to-defs table with definitions in [additional_files]
/// by querying [naming_table] for their definitions.
/// Does so sequentially file by file.
fn extend_defs_per_file_sequential(
    defs_per_file: &RPMap<file_info::Names>,
    naming_table: &naming_table::T,
    additional_files: &RPSet,
) -> RPMap<file_info::Names> {
    hh_logger::log("Extending file-to-defs table sequentially (in memory)...");
    let mut acc = defs_per_file.clone();
    for path in additional_files {
        match defs_per_file.get(path) {
            None => match naming_table::get_file_info_exn(naming_table, path) {
                Ok(info) => {
                    let info_names = file_info::simplify(&info);
                    acc.insert(path.clone(), info_names);
                }
                Err(naming_table::FileInfoNotFound) => {}
            },
            Some(_) => {}
        }
    }
    acc
}

/// [extend_defs_per_file_batch genv defs_per_file naming_table additional_files bucket_size]
/// extends [defs_per_file] file-to-defs table with definitions in [additional_files]
/// by querying [naming_table] for their definitions.
/// Does so in batches of size [bucket_size].
///
/// (The OCaml's workers each fold a bucket into an empty map, merged with
/// `Relative_path.Map.union`; the result is the same map, computed here on
/// the calling thread.)
fn extend_defs_per_file_batch(
    defs_per_file: &RPMap<file_info::Names>,
    naming_table: &naming_table::T,
    additional_files: &RPSet,
) -> RPMap<file_info::Names> {
    hh_logger::log("Extending file-to-defs table in batch mode...");
    let mut extended_defs_per_file: RPMap<file_info::Names> = RPMap::new();
    for x in additional_files {
        match naming_table::get_file_info_exn(naming_table, x) {
            Ok(info) => {
                extended_defs_per_file.insert(x.clone(), file_info::simplify(&info));
            }
            Err(naming_table::FileInfoNotFound) => {}
        }
    }
    // `Relative_path.Map.union defs_per_file extended_defs_per_file`: the
    // bindings of the first map win.
    let mut result = extended_defs_per_file;
    for (k, v) in defs_per_file {
        result.insert(k.clone(), v.clone());
    }
    result
}

/// [extend_defs_per_file genv defs_per_file naming_table additional_files]
/// extends [defs_per_file] file-to-defs table with definitions in [additional_files]
/// by querying [naming_table] for their definitions.
/// Does so either sequentially or in batches depending on how many files to add.
pub fn extend_defs_per_file(
    genv: &Genv,
    defs_per_file: RPMap<file_info::Names>,
    naming_table: &naming_table::T,
    additional_files: &RPSet,
) -> RPMap<file_info::Names> {
    let additional_count = additional_files.len() as isize;
    if additional_count == 0 {
        defs_per_file
    } else {
        hh_logger::log(&format!(
            "Extending the file-to-defs table by {} additional files",
            additional_count
        ));
        let t = gettimeofday();
        let bucket_size = genv.local_config.extend_defs_per_file_bucket_size;
        let extended_defs_per_file = match naming_table::get_forward_naming_fallback_path(naming_table)
        {
            Some(_sqlite_path) if additional_count >= bucket_size => {
                extend_defs_per_file_batch(&defs_per_file, naming_table, additional_files)
            }
            _ => extend_defs_per_file_sequential(&defs_per_file, naming_table, additional_files),
        };
        let _t = hh_logger::log_duration(None, None, "Extended file-to-defs table", t);
        extended_defs_per_file
    }
}

/// `get_check_info ~check_reason ~log_errors ~discard_warnings genv env`
pub fn get_check_info(
    check_reason: &str,
    log_errors: bool,
    discard_warnings: bool,
    genv: &Genv,
    env: &Env,
) -> CheckInfo {
    let _ = (genv, env);
    CheckInfo {
        // The daemon: `Typing_check_service.process_file ~drop_fixmed:false`.
        keep_fixmed: true,
        check_reason: check_reason.to_string(),
        discard_warnings,
        log_errors,
    }
}

/// `user_filter`
pub enum UserFilter {
    UserFilterInclude(Vec<ocaml_str::Regexp>),
    UserFilterExclude(Vec<ocaml_str::Regexp>),
    UserFilterFiles(s_set::T),
}

/// `Yojson.Safe.Util.Type_error (msg, _)`: the message, as `Failure`'s.
fn type_error(msg: &str) -> String {
    msg.to_string()
}

/// `Yojson.Safe.Util.member`
fn member<'a>(name: &str, json: &'a yojson::T) -> Result<&'a yojson::T, String> {
    match json {
        yojson::T::Assoc(fields) => Ok(fields
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| v)
            .unwrap_or(&yojson::T::Null)),
        _ => Err(type_error(&format!("Can't get member '{}' of non-object type", name))),
    }
}

/// `Yojson.Safe.Util.to_string`
fn to_string(json: &yojson::T) -> Result<String, String> {
    match json {
        yojson::T::String(s) => Ok(s.clone()),
        _ => Err(type_error("Expected string, got something else")),
    }
}

/// `Yojson.Safe.Util.to_list`
fn to_list(json: &yojson::T) -> Result<&[yojson::T], String> {
    match json {
        yojson::T::List(l) => Ok(l),
        _ => Err(type_error("Expected array, got something else")),
    }
}

fn regexes_of_json(json: &yojson::T) -> Result<Vec<ocaml_str::Regexp>, String> {
    let regexes = to_list(member("regexes", json)?)?
        .iter()
        .map(to_string)
        .collect::<Result<Vec<String>, String>>()?;
    regexes
        .iter()
        .map(|re| {
            ocaml_str::regexp(re).map_err(|ocaml_str::Failure(explanation)| {
                format!("Could not parse regex \"{}\": {}", re, explanation)
            })
        })
        .collect()
}

/// `user_filter_of_json json` (a raised `Failure` is the `Err`).
pub fn user_filter_of_json(json: &yojson::T) -> Result<UserFilter, String> {
    let type_ = to_string(member("type", json)?)?;
    if type_ == "include" {
        Ok(UserFilter::UserFilterInclude(regexes_of_json(json)?))
    } else if type_ == "exclude" {
        Ok(UserFilter::UserFilterExclude(regexes_of_json(json)?))
    } else if type_ == "specific_files" {
        let file_list = to_list(member("files", json)?)?
            .iter()
            .map(to_string)
            .collect::<Result<Vec<String>, String>>()?;
        Ok(UserFilter::UserFilterFiles(file_list.into_iter().collect()))
    } else {
        Err(format!("Unknown filter type: '{}'", type_))
    }
}

/// `user_filter_should_type_check user_filter path`
pub fn user_filter_should_type_check(user_filter: &UserFilter, path: &relative_path::T) -> bool {
    let suffix = relative_path::suffix(path);
    let matches_any = |regexes: &[ocaml_str::Regexp]| {
        regexes
            .iter()
            .any(|re| ocaml_str::search_forward(re, &suffix, 0).is_some())
    };
    match user_filter {
        UserFilter::UserFilterInclude(regexes) => matches_any(regexes),
        UserFilter::UserFilterExclude(regexes) => !matches_any(regexes),
        UserFilter::UserFilterFiles(files) => files.contains(&suffix),
    }
}

/// `user_filters_should_type_check user_filters path`
pub fn user_filters_should_type_check(user_filters: &[UserFilter], path: &relative_path::T) -> bool {
    user_filters
        .iter()
        .all(|f| user_filter_should_type_check(f, path))
}

/// `Sys_utils.expanduser`: a leading `~` (or `~user`) is the home directory.
fn expanduser(path: &str) -> String {
    match path.strip_prefix('~') {
        None => path.to_string(),
        Some(rest) => {
            let (user, rest) = match rest.find('/') {
                Some(i) => (&rest[..i], &rest[i..]),
                None => (rest, ""),
            };
            let home = if user.is_empty() {
                std::env::var("HOME").ok().or_else(|| home_of_uid(None))
            } else {
                home_of_uid(Some(user))
            };
            match home {
                Some(home) => format!("{}{}", home, rest),
                None => path.to_string(),
            }
        }
    }
}

/// `(Unix.getpwuid (Unix.getuid ())).pw_dir`, or `getpwnam` of `user`.
fn home_of_uid(user: Option<&str>) -> Option<String> {
    unsafe {
        let pw = match user {
            None => libc::getpwuid(libc::getuid()),
            Some(user) => {
                let user = std::ffi::CString::new(user).ok()?;
                libc::getpwnam(user.as_ptr())
            }
        };
        if pw.is_null() || (*pw).pw_dir.is_null() {
            None
        } else {
            Some(
                std::ffi::CStr::from_ptr((*pw).pw_dir)
                    .to_string_lossy()
                    .into_owned(),
            )
        }
    }
}

/// `user_filter_type_check_files ~to_recheck ~reparsed`
pub fn user_filter_type_check_files(to_recheck: &RPSet, reparsed: &RPSet) -> RPSet {
    hh_logger::log("Filtering files to type check using user-defined predicates");
    let config_file_path = expanduser("~/.hack_type_check_files_filter");
    let read_config_file_once = || -> Result<Vec<UserFilter>, String> {
        let contents = crate::sys_utils::cat(&config_file_path).map_err(|e| e.0)?;
        let json = yojson::from_string(&String::from_utf8_lossy(&contents))
            .map_err(|e| format!("{:?}", e))?;
        let filters = to_list(&json)?;
        filters.iter().map(user_filter_of_json).collect()
    };
    let read_config_file = || -> Vec<UserFilter> {
        loop {
            hh_logger::log(&format!("Reading in config file at {}", config_file_path));
            match read_config_file_once() {
                Ok(filters) => return filters,
                Err(e) => {
                    #[cfg(feature = "server")]
                    crate::server_progress::write(
                        Some(false),
                        None,
                        "error while applying user file filter, see logs to continue",
                    );
                    eprint!("{}", e);
                    hh_logger::log(&format!(
                        "An exception occurred while reading {}, retrying in 5s...",
                        config_file_path
                    ));
                    std::thread::sleep(std::time::Duration::from_secs(5));
                }
            }
        }
    };
    let filters = read_config_file();
    let to_recheck_original_count = to_recheck.len();
    let to_recheck: RPSet = to_recheck
        .iter()
        .filter(|path| reparsed.contains(*path) || user_filters_should_type_check(&filters, path))
        .cloned()
        .collect();
    let passed_filter_count = to_recheck.len();
    hh_logger::log(&format!(
        "Filtered files to recheck from {} to {}",
        to_recheck_original_count, passed_filter_count
    ));
    to_recheck
}
