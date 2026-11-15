// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_config.ml`. See `hh/PORTING.md`.
//!
//! Parses and gathers information from the .hhconfig in the repo.
//!
//! # The typechecker and parser options
//!
//! The options are computed as `Server_config` computes them: `load_config`
//! applies the keys of `.hhconfig` (and `--config`) to the options it is
//! given, and `load_with_dynamic_overrides` gives it the defaults with the
//! fields that hh.conf decides. `hh check` takes its options from [`load`]
//! (as `hh_server --check` does) and `hh single` from `load_config` (as
//! `hh_single_type_check` does). The `hh_config` crate (which `hackc` and
//! `hackrs` use) computes the options in its own way, and the two disagree
//! on keys that change what is reported (Slack's `.hhconfig` has
//! `disallow_discarded_nullable_awaitables=true`, which `hh_config`
//! ignores): see the test `hh_config_differs`.
//!
//! `Global_options.set ~a ?b options` is written as the copy of `options`
//! with the fields that are given replaced (`setting`, `setting_opt`), plus
//! what `set` does besides: it resets `tco_dynamic_inference` to its default
//! (its optional argument has one) (`global_options_set_rest`).
//!
//! OCaml evaluates the arguments of a call and the fields of a record from
//! right to left, in the order in which the function declares its
//! parameters and the type declares its fields (not the order in which the
//! call or the record expression writes them: the type checker puts labelled
//! arguments and fields in their declared order first). Several of them
//! raise on a malformed value (which message is printed then depends on the
//! order), so they are bound from the last declared to the first.
//!
//! # What is compiled where
//!
//! `load_with_dynamic_overrides` and `load` need `Custom_error_config_loader`,
//! `Package_config` and `Package_info.log_package_info`, which are `port`
//! modules: they are compiled with `port`. `update_config_with_ai_options`
//! needs `Ai_options` (the OSS stub, whose `modify_shared_mem` returns its
//! argument), a `server` module: it is compiled with `server`.

use std::sync::LazyLock;

use oxidized::global_options::ExtendedReasonsConfig;
use oxidized::global_options::GlobalOptions;
use oxidized::global_options::NoneOrAllExcept;
use oxidized::i_set::ISet;
use oxidized::parser_options::ParserOptions;
use oxidized::s_map::SMap;
use oxidized::s_set::SSet;

use crate::config_file;
use crate::config_file::getters::*;
use crate::config_file_common;
use crate::config_keys;
use crate::config_keys::hhconfig;
use crate::experimental_features;
use crate::global_config;
use crate::hh_logger;
use crate::path;
use crate::relative_path;
use crate::rt::ocaml_stdlib::int_of_string;
use crate::rt::ocaml_stdlib;
use crate::rt::ocaml_str;
use crate::shared_mem;
use crate::utils;
use crate::yojson;
use crate::yojson::safe::T as Json;

/// `Server_config.t` (abstract in the `.mli`: read it with the functions
/// below).
#[derive(Clone, Debug, PartialEq)]
pub struct T {
    version: config_file::Version,
    /// in seconds
    load_script_timeout: isize,
    /// Configures only the workers. Workers can have more relaxed GC configs as
    /// they are short-lived processes
    gc_control: global_config::GcControl,
    sharedmem_config: shared_mem::Config,
    tc_options: GlobalOptions,
    parser_options: ParserOptions,
    glean_options: GlobalOptions,
    symbol_write_options: GlobalOptions,
    formatter_override: Option<path::T>,
    config_hash: Option<String>,
    /// A list of regexps for paths to ignore
    ignored_paths: Vec<String>,
    /// A list of extra paths to search for declarations
    extra_paths: Vec<path::T>,
    warn_on_non_opt_build: bool,
    /// clientIdeDaemon will fall back to performing a full index of files to construct a naming table if it fails to load one.
    ide_fall_back_to_full_index: bool,
    naming_table_compression_level: isize,
    naming_table_compression_threads: isize,
    /// List of regex patterns for file paths for which any warning will be ignored.
    /// Useful to ignore warnings from certain generated files.
    /// Passing `-Wgenerated` on the command line will override this behavior
    /// and show warnings from those files.
    /// These are sent to Rust via FFI so are not stored as regexes here.
    warnings_generated_files: Vec<String>,
}

/// The exceptions that `load` and `load_with_dynamic_overrides` let through
/// to their callers (besides the `failwith`s and `Invalid_argument`s of
/// malformed values, which are panics).
#[derive(Clone, PartialEq, Eq)]
pub enum ServerConfigError {
    /// `Yojson.Json_error`, of a value that is not JSON
    JsonError(yojson::JsonError),
    /// `Sys_error`, from `Server_local_config_load.load`
    SysError(crate::sys_utils::SysError),
}

impl std::fmt::Debug for ServerConfigError {
    /// `Printexc.to_string`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ServerConfigError::JsonError(yojson::JsonError(msg)) => write!(
                f,
                "Yojson.Json_error({})",
                crate::rt::ocaml_printf::sprintf_s(msg)
            ),
            ServerConfigError::SysError(e) => write!(f, "{}", e),
        }
    }
}

impl From<yojson::JsonError> for ServerConfigError {
    fn from(e: yojson::JsonError) -> Self {
        ServerConfigError::JsonError(e)
    }
}

impl From<crate::sys_utils::SysError> for ServerConfigError {
    fn from(e: crate::sys_utils::SysError) -> Self {
        ServerConfigError::SysError(e)
    }
}

pub static REPO_CONFIG_PATH: LazyLock<relative_path::T> =
    LazyLock::new(|| relative_path::from_root(config_file::FILE_PATH_RELATIVE_TO_REPO_ROOT));

pub fn is_compatible(c1: &T, c2: &T) -> bool {
    // This comparison can eventually be made more complex; we may not always
    // need to restart hh_server, e.g. changing the path to the load script
    // is immaterial
    // (`Poly.equal`)
    c1 == c2
}

/// Used by `load_with_dynamic_overrides`.
#[allow(dead_code)]
fn make_gc_control(config: &config_file::T) -> global_config::GcControl {
    let global_config::GcControl {
        minor_heap_size,
        space_overhead,
    } = global_config::gc_control();
    let minor_heap_size = int_(hhconfig::GC_MINOR_HEAP_SIZE, minor_heap_size, config);
    let space_overhead = int_(hhconfig::GC_SPACE_OVERHEAD, space_overhead, config);
    global_config::GcControl {
        minor_heap_size,
        space_overhead,
        ..global_config::gc_control()
    }
}

pub fn make_sharedmem_config(
    config: &config_file::T,
    local_config: &crate::server_local_config::T,
) -> shared_mem::Config {
    let shared_mem::Config {
        global_size,
        heap_size,
        shm_min_avail,
        ..
    } = shared_mem::default_config();
    let shm_dirs = local_config.shm_dirs.clone();
    let global_size = int_(hhconfig::SHAREDMEM_GLOBAL_SIZE, global_size, config);
    let heap_size = int_(hhconfig::SHAREDMEM_HEAP_SIZE, heap_size, config);
    let hash_table_pow = int_(hhconfig::SHAREDMEM_HASH_TABLE_POW, 18, config);
    let log_level = int_(hhconfig::SHAREDMEM_LOG_LEVEL, 0, config);
    let sample_rate = float_(hhconfig::SHAREDMEM_SAMPLE_RATE, 0.0, config);
    let compression = int_(hhconfig::SHAREDMEM_COMPRESSION, 0, config);
    let shm_dirs = string_list(hhconfig::SHAREDMEM_DIRS, shm_dirs, config);
    let shm_use_sharded_hashtbl = bool_(
        hhconfig::SHM_USE_SHARDED_HASHTBL,
        local_config.shm_use_sharded_hashtbl,
        config,
    );
    let shm_cache_size = int_(
        hhconfig::SHM_CACHE_SIZE,
        local_config.shm_cache_size,
        config,
    );
    let shm_min_avail = int_(hhconfig::SHAREDMEM_MINIMUM_AVAILABLE, shm_min_avail, config);
    shared_mem::Config {
        global_size,
        heap_size,
        hash_table_pow,
        log_level,
        sample_rate,
        shm_dirs,
        shm_use_sharded_hashtbl,
        shm_cache_size,
        shm_min_avail,
        compression,
    }
}

static CONFIG_LIST_REGEXP: LazyLock<regex::Regex> =
    LazyLock::new(|| regex::Regex::new("[, \t]+").unwrap());

/// `Str.split config_list_regexp s`: the pieces between the delimiters,
/// without the empty ones that delimiters at the start or the end of `s`
/// would make.
fn split_config_list(s: &str) -> Vec<String> {
    CONFIG_LIST_REGEXP
        .split(s)
        .filter(|piece| !piece.is_empty())
        .map(str::to_string)
        .collect()
}

fn process_experimental(sl: &[String]) -> SSet {
    let features: Vec<String> = sl.iter().map(|s| s.to_ascii_lowercase()).collect();
    match features.as_slice() {
        [s] if s == "false" => SSet::new(),
        [s] if s == "true" => crate::typechecker_options::EXPERIMENTAL_ALL.clone(),
        features => features.iter().fold(SSet::new(), |mut acc, feature| {
            acc.insert(feature.clone());
            acc
        }),
    }
}

fn config_experimental_tc_features(config: &config_file::T) -> Option<SSet> {
    string_opt(hhconfig::ENABLE_EXPERIMENTAL_TC_FEATURES, config).map(|list_str| {
        let sl = split_config_list(&list_str);
        process_experimental(&sl)
    })
}

fn config_experimental_stx_features(
    config: &config_file::T,
) -> Result<Option<SMap<experimental_features::FeatureStatus>>, yojson::JsonError> {
    string_opt(hhconfig::ENABLE_EXPERIMENTAL_STX_FEATURES, config)
        .map(|str| {
            let json = yojson::safe::from_string(&str)?;
            let pairs = match json {
                Json::Assoc(pairs) => pairs,
                _ => panic!("expected JSON object"),
            };
            // `S_map.of_list`: the last of the features given twice wins.
            Ok(pairs
                .iter()
                .map(experimental_features::parse_experimental_feature)
                .collect())
        })
        .transpose()
}

fn process_migration_flags(sl: &[String]) -> SSet {
    match sl {
        [s] if s == "false" => SSet::new(),
        [s] if s == "true" => crate::typechecker_options::MIGRATION_FLAGS_ALL.clone(),
        flags => {
            for s in flags {
                if !crate::typechecker_options::MIGRATION_FLAGS_ALL.clone().contains(s) {
                    panic!("{}", format!("invalid migration flag: {}", s));
                }
            }
            flags.iter().fold(SSet::new(), |mut acc, flag| {
                acc.insert(flag.clone());
                acc
            })
        }
    }
}

fn config_tc_migration_flags(config: &config_file::T) -> Option<SSet> {
    string_opt(hhconfig::ENABLE_TC_MIGRATION_FLAGS, config).map(|list_str| {
        let flags: Vec<String> = split_config_list(&list_str)
            .iter()
            .map(|s| s.to_ascii_lowercase())
            .collect();
        process_migration_flags(&flags)
    })
}

fn convert_paths(str: &str) -> Result<Vec<String>, yojson::JsonError> {
    let json = yojson::safe::from_string(str)?;
    let l = match json {
        Json::List(l) => l,
        _ => panic!("expected JSON array"),
    };
    Ok(l.into_iter()
        .filter_map(|s| match s {
            Json::String(path) => Some(path),
            _ => None,
        })
        .collect())
}

/// Used by `load_with_dynamic_overrides`.
#[allow(dead_code)]
fn process_ignored_paths(config: &config_file::T) -> Result<Vec<String>, yojson::JsonError> {
    string_opt(hhconfig::IGNORED_PATHS, config).map_or_else(|| Ok(Vec::new()), |s| convert_paths(&s))
}

fn maybe_relative_path(fn_: &str) -> path::T {
    // Note: this is not the same as calling realpath; the cwd is not
    // necessarily the same as hh_server's root!!!
    path::make(&if crate::rt::ocaml_filename::is_relative(fn_) {
        relative_path::to_absolute(&relative_path::from_root(fn_))
    } else {
        fn_.to_string()
    })
}

/// Used by `load_with_dynamic_overrides`.
#[allow(dead_code)]
fn process_extra_paths(config: &config_file::T) -> Vec<path::T> {
    match string_opt(hhconfig::EXTRA_PATHS, config) {
        Some(s) => split_config_list(&s)
            .iter()
            .map(|s| maybe_relative_path(s))
            .collect(),
        _ => vec![],
    }
}

/// `bool_of_string`: `Invalid_argument "bool_of_string"` unless `s` is
/// `true` or `false`. (Used by `process_untrusted_mode`.)
#[allow(dead_code)]
fn bool_of_string(s: &str) -> bool {
    match s {
        "true" => true,
        "false" => false,
        _ => panic!("Invalid_argument: bool_of_string"),
    }
}

/// Fails whenever `untrusted_mode` is `true`: with the keys that it does not
/// permit, or (when there are none) with "can only be enabled, not
/// disabled". `untrusted_mode = false` passes. Used by
/// `load_with_dynamic_overrides`.
#[allow(dead_code)]
fn process_untrusted_mode(config: &config_file::T) {
    match string_opt(hhconfig::UNTRUSTED_MODE, config) {
        Some(s) => {
            if bool_of_string(&s) {
                let blacklist = [
                    // out of tree file access
                    "extra_paths",
                    // potential resource abuse
                    "language_feature_logging",
                ];
                let prefix_blacklist = [/* potential resource abuse */ "gc_", "sharedmem_"];
                let invalid_keys: Vec<String> = config_file::keys(config)
                    .into_iter()
                    .filter(|ck| {
                        let ck = ck.to_ascii_lowercase();
                        let exact_match = blacklist.iter().find(|bli| **bli == ck);
                        let prefix_match =
                            prefix_blacklist.iter().find(|blp| ck.starts_with(**blp));
                        match (exact_match, prefix_match) {
                            (None, None) => false,
                            _ => true,
                        }
                    })
                    .collect();
                if !invalid_keys.is_empty() {
                    panic!(
                        "{}",
                        format!(
                            "option not permitted in untrusted_mode: {}",
                            invalid_keys.join(", ")
                        )
                    )
                } else {
                    panic!("untrusted_mode can only be enabled, not disabled")
                }
            }
        }
        _ => {}
    }
}

fn extract_auto_namespace_element(
    mut ns_map: Vec<(String, String)>,
    element: &(String, Json),
) -> Vec<(String, String)> {
    match element {
        (source, Json::String(target)) => {
            ns_map.insert(0, (source.clone(), target.clone()));
            ns_map
        }
        _ => {
            // This means the JSON we received is incorrect
            ns_map
        }
    }
}

/// The aliases in the reverse of their order in the JSON object (OCaml
/// conses them onto the list as it folds over the object), duplicates
/// included; those whose target is not a string are dropped.
pub fn convert_auto_namespace_to_map(
    map: &str,
) -> Result<Vec<(String, String)>, yojson::JsonError> {
    let json = yojson::safe::from_string(map)?;
    let pairs = match json {
        Json::Assoc(pairs) => pairs,
        _ => panic!("expected JSON object"),
    };
    // We do a fold instead of a map to filter
    // out the incorrect entrie as we look at each item
    Ok(pairs.iter().fold(vec![], extract_auto_namespace_element))
}

fn prepare_auto_namespace_map(
    config: &config_file::T,
) -> Result<Option<Vec<(String, String)>>, yojson::JsonError> {
    string_opt(hhconfig::AUTO_NAMESPACE_MAP, config)
        .map(|s| convert_auto_namespace_to_map(&s))
        .transpose()
}

fn extract_log_level((log_key, log_level): &(String, Json)) -> (String, isize) {
    match log_level {
        Json::Int(log_level) => (log_key.clone(), *log_level),
        Json::Intlit(log_level) => match ocaml_stdlib::int_of_string_opt(log_level) {
            Some(log_level) => (log_key.clone(), log_level),
            None => panic!("non-integer log level value"),
        },
        _ => panic!("non-integer log level value"),
    }
}

/// `S_map.of_list`: the last of the keys given twice wins.
fn convert_log_levels_to_map(map: &str) -> Result<SMap<isize>, yojson::JsonError> {
    let json = yojson::safe::from_string(map)?;
    let pairs = match json {
        Json::Assoc(pairs) => pairs,
        _ => panic!("expected JSON object"),
    };
    Ok(pairs.iter().map(extract_log_level).collect())
}

fn prepare_log_levels(config: &config_file::T) -> Result<Option<SMap<isize>>, yojson::JsonError> {
    string_opt(hhconfig::LOG_LEVELS, config)
        .map(|s| convert_log_levels_to_map(&s))
        .transpose()
}

fn prepare_iset(config: &config_file::T, config_name: &str) -> Option<ISet> {
    string_opt(config_name, config).map(|list_str| {
        split_config_list(&list_str)
            .iter()
            .map(|s| int_of_string(s))
            .collect()
    })
}

fn prepare_allowed_decl_fixme_codes(config: &config_file::T) -> Option<ISet> {
    prepare_iset(config, hhconfig::ALLOWED_DECL_FIXME_CODES)
}

fn reasons_config_opt(config: &config_file::T) -> Option<ExtendedReasonsConfig> {
    string_opt(hhconfig::EXTENDED_REASONS, config).and_then(|data_str| {
        if data_str == "debug" {
            Some(ExtendedReasonsConfig::Debug)
        } else if data_str == "legacy" {
            Some(ExtendedReasonsConfig::Legacy)
        } else {
            ocaml_stdlib::int_of_string_opt(&data_str).map(ExtendedReasonsConfig::Extended)
        }
    })
}

/// `setting setting option` of `Global_options.set`: the field becomes the
/// value given, if one is.
fn setting<A>(field: &mut A, setting: Option<A>) {
    if let Some(value) = setting {
        *field = value
    }
}

/// `setting_opt setting option` of `Global_options.set`, for a field that is
/// an option: it becomes the value given, if one is.
fn setting_opt<A>(field: &mut Option<A>, setting: Option<A>) {
    if setting.is_some() {
        *field = setting
    }
}

/// What `Global_options.set` does to the fields that are not among its
/// arguments: `tco_dynamic_inference` takes its default (its optional
/// argument has one). `opts` is the copy of the argument of `set` being
/// updated.
fn global_options_set_rest(opts: &mut GlobalOptions) {
    opts.tco_dynamic_inference = GlobalOptions::default().tco_dynamic_inference;
}

/// The `Yojson.Json_error` of a value that is not JSON is the `Err`.
pub fn load_config(
    config: &config_file::T,
    options: &GlobalOptions,
) -> Result<GlobalOptions, yojson::JsonError> {
    // `x >?? y` is `Option.value x ~default:y`.
    let po_opt = &options.po;
    let experimental_features = config_experimental_stx_features(config)?;
    // The fields of the record, from the last to the first in the order of
    // their declaration in `Parser_options.t`.
    let allow_single_statement_concurrent =
        bool_opt(hhconfig::ALLOW_SINGLE_STATEMENT_CONCURRENT, config)
            .unwrap_or(po_opt.allow_single_statement_concurrent);
    let expression_tree_shape_no_unwrap =
        bool_opt(hhconfig::EXPRESSION_TREE_SHAPE_NO_UNWRAP, config)
            .unwrap_or(po_opt.expression_tree_shape_no_unwrap);
    let ignore_string_methods =
        bool_opt(hhconfig::IGNORE_STRING_METHODS, config).unwrap_or(po_opt.ignore_string_methods);
    let treat_non_annotated_memoize_as_kbic =
        bool_opt(hhconfig::TREAT_NON_ANNOTATED_MEMOIZE_AS_KBIC, config)
            .unwrap_or(po_opt.treat_non_annotated_memoize_as_kbic);
    let disallow_non_annotated_memoize = bool_opt(hhconfig::DISALLOW_NON_ANNOTATED_MEMOIZE, config)
        .unwrap_or(po_opt.disallow_non_annotated_memoize);
    let package_support_multifile_tests =
        bool_opt(hhconfig::PACKAGE_SUPPORT_MULTIFILE_TESTS, config)
            .unwrap_or(po_opt.package_support_multifile_tests);
    let allowed_decl_fixme_codes = prepare_allowed_decl_fixme_codes(config)
        .unwrap_or_else(|| po_opt.allowed_decl_fixme_codes.clone());
    let union_intersection_type_hints = bool_opt(hhconfig::UNION_INTERSECTION_TYPE_HINTS, config)
        .unwrap_or(po_opt.union_intersection_type_hints);
    let deregister_php_stdlib =
        bool_opt(hhconfig::DEREGISTER_PHP_STDLIB, config).unwrap_or(po_opt.deregister_php_stdlib);
    let keep_user_attributes =
        bool_opt(hhconfig::KEEP_USER_ATTRIBUTES, config).unwrap_or(po_opt.keep_user_attributes);
    let check_duplicate_runtime_shape_keys =
        bool_opt(hhconfig::CHECK_DUPLICATE_RUNTIME_SHAPE_KEYS, config)
            .unwrap_or(po_opt.check_duplicate_runtime_shape_keys);
    let include_const_shape_key_values =
        bool_opt(hhconfig::INCLUDE_CONST_SHAPE_KEY_VALUES, config)
            .unwrap_or(po_opt.include_const_shape_key_values);
    let include_enum_member_values = bool_opt(hhconfig::INCLUDE_ENUM_MEMBER_VALUES, config)
        .unwrap_or(po_opt.include_enum_member_values);
    let everything_sdt =
        bool_opt(hhconfig::EVERYTHING_SDT, config).unwrap_or(po_opt.everything_sdt);
    let auto_namespace_map =
        prepare_auto_namespace_map(config)?.unwrap_or_else(|| po_opt.auto_namespace_map.clone());
    let is_systemlib = bool_opt(hhconfig::IS_SYSTEMLIB, config).unwrap_or(po_opt.is_systemlib);
    let interpret_soft_types_as_like_types =
        bool_opt(hhconfig::INTERPRET_SOFT_TYPES_AS_LIKE_TYPES, config)
            .unwrap_or(po_opt.interpret_soft_types_as_like_types);
    let disable_xhp_children_declarations =
        bool_opt(hhconfig::DISABLE_XHP_CHILDREN_DECLARATIONS, config)
            .unwrap_or(po_opt.disable_xhp_children_declarations);
    let disable_xhp_element_mangling = bool_opt(hhconfig::DISABLE_XHP_ELEMENT_MANGLING, config)
        .unwrap_or(po_opt.disable_xhp_element_mangling);
    let enable_xhp_class_modifier = bool_opt(hhconfig::ENABLE_XHP_CLASS_MODIFIER, config)
        .unwrap_or(po_opt.enable_xhp_class_modifier);
    let abstract_static_props =
        bool_opt(hhconfig::ABSTRACT_STATIC_PROPS, config).unwrap_or(po_opt.abstract_static_props);
    let const_static_props =
        bool_opt(hhconfig::CONST_STATIC_PROPS, config).unwrap_or(po_opt.const_static_props);
    let po = ParserOptions {
        // These aren't set in the config file, so init them to their defaults.
        hhvm_compat_mode: po_opt.hhvm_compat_mode,
        allow_unstable_features: po_opt.allow_unstable_features,
        hhi_mode: po_opt.hhi_mode,
        codegen: po_opt.codegen,
        stack_size: po_opt.stack_size,
        no_parser_readonly_check: po_opt.no_parser_readonly_check,
        unwrap_concurrent: po_opt.unwrap_concurrent,
        // Never use the legacy mode for hh_server
        use_legacy_experimental_feature_config: false,
        // The remainder are set in the config file
        is_systemlib,
        const_static_props,
        abstract_static_props,
        disable_xhp_element_mangling,
        disable_xhp_children_declarations,
        enable_xhp_class_modifier,
        interpret_soft_types_as_like_types,
        auto_namespace_map,
        everything_sdt,
        include_enum_member_values,
        include_const_shape_key_values,
        check_duplicate_runtime_shape_keys,
        keep_user_attributes,
        deregister_php_stdlib,
        union_intersection_type_hints,
        allowed_decl_fixme_codes,
        // If there was no experimental features status list in configuration,
        // consider all existing experimental features to be released and hence
        // usable.
        consider_unspecified_experimental_features_released: experimental_features.is_none(),
        experimental_features: experimental_features
            .unwrap_or_else(|| po_opt.experimental_features.clone()),
        package_info: po_opt.package_info.clone(),
        package_support_multifile_tests,
        disallow_non_annotated_memoize,
        treat_non_annotated_memoize_as_kbic,
        ignore_string_methods,
        enable_intrinsics_extension: po_opt.enable_intrinsics_extension,
        expression_tree_shape_no_unwrap,
        allow_single_statement_concurrent,
    };
    // `Global_options.set ~po ?tco_language_feature_logging:(...) ... options`:
    // the arguments, from the last to the first in the order of the
    // parameters of `Global_options.set` (`?po ?tco_saved_state
    // ?po_disallow_toplevel_requires ... ?tco_tests_bypass_visibility_static_properties`).
    let tco_xhp_attribute_reads_not_refined =
        bool_opt(hhconfig::XHP_ATTRIBUTE_READS_NOT_REFINED, config);
    let tco_ban_memoize_erased_generic_return =
        bool_opt(hhconfig::BAN_MEMOIZE_ERASED_GENERIC_RETURN, config);
    let tco_missing_targs_as_fresh_generics =
        bool_opt(hhconfig::MISSING_TARGS_AS_FRESH_GENERICS, config);
    let tco_tests_bypass_visibility_static_properties =
        bool_opt(hhconfig::TESTS_BYPASS_VISIBILITY_STATIC_PROPERTIES, config);
    let tco_permits_bypassing_visibility =
        string_list_opt(hhconfig::PERMITS_BYPASSING_VISIBILITY, config)
            .map(|l| l.iter().map(|s| utils::add_ns(s)).collect::<Vec<_>>());
    let class_pointer_ban_class_array_key =
        bool_opt(hhconfig::CLASS_POINTER_BAN_CLASS_ARRAY_KEY, config);
    let allow_class_string_cast = bool_opt(hhconfig::ALLOW_CLASS_STRING_CAST, config);
    let strict_consistent_construct = bool_opt(hhconfig::STRICT_CONSISTENT_CONSTRUCT, config);
    let needs_concrete_class_function_pointer_check =
        int_opt(hhconfig::NEEDS_CONCRETE_CLASS_FUNCTION_POINTER_CHECK, config).map(|value| {
            if value < 0 || value > 2 {
                panic!(
                    "Invalid_argument: needs_concrete_class_function_pointer_check must be 0, 1, or 2"
                );
            }
            value
        });
    let class_class_type = bool_opt(hhconfig::CLASS_CLASS_TYPE, config);
    let class_sub_classname = bool_opt(hhconfig::CLASS_SUB_CLASSNAME, config);
    let recursive_case_types = bool_opt(hhconfig::RECURSIVE_CASE_TYPES, config);
    let hh_distc_exponential_backoff_num_retries =
        int_opt(hhconfig::HH_DISTC_EXPONENTIAL_BACKOFF_NUM_RETRIES, config);
    let hh_distc_should_disable_trace_store =
        bool_opt(hhconfig::HH_DISTC_SHOULD_DISABLE_TRACE_STORE, config);
    let re_no_cache = bool_opt(hhconfig::RE_NO_CACHE, config);
    let tco_package_allow_enforceable_enum_violations =
        bool_opt(hhconfig::PACKAGE_ALLOW_ENFORCEABLE_ENUM_VIOLATIONS, config);
    let tco_package_allow_all_tconst_violations =
        bool_opt(hhconfig::PACKAGE_ALLOW_ALL_TCONST_VIOLATIONS, config);
    let tco_package_allow_classconst_violations =
        bool_opt(hhconfig::PACKAGE_ALLOW_CLASSCONST_VIOLATIONS, config);
    let tco_package_exclude_patterns = string_list_opt(hhconfig::PACKAGE_EXCLUDE_PATTERNS, config);
    let tco_allowed_files_for_ignore_readonly =
        string_list_opt(hhconfig::ALLOWED_FILES_FOR_IGNORE_READONLY, config);
    let warnings_in_sandcastle = bool_opt(hhconfig::WARNINGS_IN_SANDCASTLE, config);
    let warnings_default_all = bool_opt(hhconfig::WARNINGS_DEFAULT_ALL, config);
    let hack_warnings =
        bool_opt(hhconfig::HACK_WARNINGS, config).map(|hack_warnings| match hack_warnings {
            true => NoneOrAllExcept::AllExcept(
                int_list_opt(hhconfig::DISABLED_WARNINGS, config).unwrap_or_default(),
            ),
            false => NoneOrAllExcept::NNone,
        });
    let tco_disable_physical_equality = bool_opt(hhconfig::DISABLE_PHYSICAL_EQUALITY, config);
    let tco_extended_reasons = reasons_config_opt(config);
    let dump_tast_hashes = bool_opt(hhconfig::DUMP_TAST_HASHES, config);
    let tco_populate_dead_unsafe_cast_heap =
        bool_opt(hhconfig::POPULATE_DEAD_UNSAFE_CAST_HEAP, config);
    let tco_allowed_files_for_module_declarations =
        string_list_opt(hhconfig::ALLOWED_FILES_FOR_MODULE_DECLARATIONS, config);
    let tco_allow_all_files_for_module_declarations =
        bool_opt(hhconfig::ALLOW_ALL_FILES_FOR_MODULE_DECLARATIONS, config);
    let tco_typecheck_if_name_matches_regexp =
        string_opt(hhconfig::TYPECHECK_IF_NAME_MATCHES_REGEXP, config);
    let tco_profile_top_level_definitions =
        bool_opt(hhconfig::PROFILE_TOP_LEVEL_DEFINITIONS, config);
    let tco_type_printer_fuel = int_opt(hhconfig::TYPE_PRINTER_FUEL, config);
    let tco_require_types_class_consts = int_opt(
        hhconfig::REQUIRE_TYPES_TCO_REQUIRE_TYPES_CLASS_CONSTS,
        config,
    );
    let tco_explicit_consistent_constructors =
        int_opt(hhconfig::EXPLICIT_CONSISTENT_CONSTRUCTORS, config);
    let tco_repo_stdlib_path = string_opt(hhconfig::REPO_STDLIB_PATH, config);
    let tco_implicit_inherit_sdt = bool_opt(hhconfig::IMPLICIT_INHERIT_SDT, config);
    let tco_require_extends_implements_ancestors =
        bool_opt(hhconfig::REQUIRE_EXTENDS_IMPLEMENTS_ANCESTORS, config);
    let tco_meth_caller_only_public_visibility =
        bool_opt(hhconfig::METH_CALLER_ONLY_PUBLIC_VISIBILITY, config);
    let tco_typeconst_concrete_concrete_error =
        bool_opt(hhconfig::TYPECONST_CONCRETE_CONCRETE_ERROR, config);
    let tco_allowed_expression_tree_visitors =
        string_list_opt(hhconfig::ALLOWED_EXPRESSION_TREE_VISITORS, config)
            .map(|l| l.iter().map(|s| utils::add_ns(s)).collect::<Vec<_>>());
    let tco_variadic_named_parameters = bool_opt(hhconfig::VARIADIC_NAMED_PARAMETERS, config);
    let tco_named_variadic_type = bool_opt(hhconfig::NAMED_VARIADIC_TYPE, config);
    let tco_typed_open_shapes = bool_opt(hhconfig::TYPED_OPEN_SHAPES, config);
    let tco_skip_check_under_dynamic = bool_opt(hhconfig::SKIP_CHECK_UNDER_DYNAMIC, config);
    let tco_enable_no_auto_dynamic = bool_opt(hhconfig::ENABLE_NO_AUTO_DYNAMIC, config);
    let tco_pessimise_builtins = bool_opt(hhconfig::PESSIMISE_BUILTINS, config);
    let tco_typecheck_sample_rate = float_opt(hhconfig::TYPECHECK_SAMPLE_RATE, config);
    let tco_check_duplicate_enum_values = bool_opt(hhconfig::CHECK_DUPLICATE_ENUM_VALUES, config);
    let tco_disallow_discarded_nullable_awaitables =
        bool_opt(hhconfig::DISALLOW_DISCARDED_NULLABLE_AWAITABLES, config);
    let symbol_write_sym_hash_out = bool_opt(hhconfig::SYMBOL_WRITE_SYM_HASH_OUT, config);
    let symbol_write_reindexed_out = string_opt(hhconfig::SYMBOL_WRITE_REINDEXED_OUT, config);
    let symbol_write_referenced_out = string_opt(hhconfig::SYMBOL_WRITE_REFERENCED_OUT, config);
    let symbol_write_exclude_out = string_opt(hhconfig::SYMBOL_WRITE_EXCLUDE_OUT, config);
    let symbol_write_sym_hash_in = string_opt(hhconfig::SYMBOL_WRITE_SYM_HASH_IN, config);
    let symbol_write_include_hhi = bool_opt(hhconfig::SYMBOL_WRITE_INCLUDE_HHI, config);
    let symbol_write_index_paths_file_output =
        string_opt(hhconfig::SYMBOL_WRITE_INDEX_PATHS_FILE_OUTPUT, config);
    let symbol_write_index_paths_file = string_opt(hhconfig::SYMBOL_WRITE_INDEX_PATHS_FILE, config);
    let symbol_write_index_paths = string_list_opt(hhconfig::SYMBOL_WRITE_INDEX_PATHS, config);
    let symbol_write_ignore_paths = string_list_opt(hhconfig::SYMBOL_WRITE_IGNORE_PATHS, config);
    let symbol_write_hhi_path = string_opt(hhconfig::SYMBOL_WRITE_HHI_PATH, config);
    let symbol_write_root_path = string_opt(hhconfig::SYMBOL_WRITE_ROOT_PATH, config);
    let symbol_write_ownership = bool_opt(hhconfig::SYMBOL_WRITE_OWNERSHIP, config);
    let symbol_write_index_inherited_members =
        bool_opt(hhconfig::SYMBOL_WRITE_INDEX_INHERITED_MEMBERS, config);
    let glean_reponame = string_opt(hhconfig::GLEAN_REPONAME, config);
    let tco_const_attribute = bool_opt(hhconfig::CONST_ATTRIBUTE, config);
    let tco_disallow_unresolved_type_variables =
        bool_opt(hhconfig::DISALLOW_UNRESOLVED_TYPE_VARIABLES, config);
    let tco_like_casts = bool_opt(hhconfig::LIKE_CASTS, config);
    let tco_reject_promoted_property_redeclaration =
        bool_opt(hhconfig::REJECT_PROMOTED_PROPERTY_REDECLARATION, config);
    let tco_silence_errors_under_dynamic = bool_opt(hhconfig::SILENCE_ERRORS_UNDER_DYNAMIC, config);
    let log_levels = prepare_log_levels(config)?;
    let allowed_fixme_codes_strict = prepare_iset(config, hhconfig::ALLOWED_FIXME_CODES_STRICT);
    let code_agnostic_fixme = bool_opt(hhconfig::CODE_AGNOSTIC_FIXME, config);
    let tco_constraint_method_call = bool_opt(hhconfig::CONSTRAINT_METHOD_CALL, config);
    let tco_constraint_array_index_assign =
        bool_opt(hhconfig::CONSTRAINT_ARRAY_INDEX_ASSIGN, config);
    let tco_timeout = int_opt(hhconfig::TIMEOUT, config);
    let tco_language_feature_logging = bool_opt(hhconfig::LANGUAGE_FEATURE_LOGGING, config);
    let tco_locl_cache_node_threshold = int_opt(hhconfig::LOCL_CACHE_NODE_THRESHOLD, config);
    let tco_locl_cache_capacity = int_opt(hhconfig::LOCL_CACHE_CAPACITY, config);
    let tco_migration_flags = config_tc_migration_flags(config);
    let tco_legacy_experimental_features = config_experimental_tc_features(config);
    let po_disallow_toplevel_requires = bool_opt(hhconfig::DISALLOW_TOPLEVEL_REQUIRES, config);
    let mut opts = options.clone();
    opts.po = po;
    setting(
        &mut opts.tco_language_feature_logging,
        tco_language_feature_logging,
    );
    setting(&mut opts.tco_timeout, tco_timeout);
    setting(
        &mut opts.tco_constraint_array_index_assign,
        tco_constraint_array_index_assign,
    );
    setting(
        &mut opts.tco_constraint_method_call,
        tco_constraint_method_call,
    );
    setting(&mut opts.code_agnostic_fixme, code_agnostic_fixme);
    setting(
        &mut opts.allowed_fixme_codes_strict,
        allowed_fixme_codes_strict,
    );
    setting(
        &mut opts.tco_legacy_experimental_features,
        tco_legacy_experimental_features,
    );
    setting(&mut opts.tco_migration_flags, tco_migration_flags);
    setting(&mut opts.tco_like_casts, tco_like_casts);
    setting(
        &mut opts.tco_disallow_unresolved_type_variables,
        tco_disallow_unresolved_type_variables,
    );
    setting(&mut opts.tco_locl_cache_capacity, tco_locl_cache_capacity);
    setting(
        &mut opts.tco_locl_cache_node_threshold,
        tco_locl_cache_node_threshold,
    );
    setting(
        &mut opts.po_disallow_toplevel_requires,
        po_disallow_toplevel_requires,
    );
    setting(&mut opts.tco_const_attribute, tco_const_attribute);
    setting(&mut opts.glean_reponame, glean_reponame);
    setting(
        &mut opts.symbol_write_index_inherited_members,
        symbol_write_index_inherited_members,
    );
    setting(&mut opts.symbol_write_ownership, symbol_write_ownership);
    setting(&mut opts.symbol_write_root_path, symbol_write_root_path);
    setting(&mut opts.symbol_write_hhi_path, symbol_write_hhi_path);
    setting(
        &mut opts.symbol_write_ignore_paths,
        symbol_write_ignore_paths,
    );
    setting(&mut opts.symbol_write_index_paths, symbol_write_index_paths);
    setting_opt(
        &mut opts.symbol_write_index_paths_file,
        symbol_write_index_paths_file,
    );
    setting_opt(
        &mut opts.symbol_write_index_paths_file_output,
        symbol_write_index_paths_file_output,
    );
    setting(&mut opts.symbol_write_include_hhi, symbol_write_include_hhi);
    setting_opt(&mut opts.symbol_write_sym_hash_in, symbol_write_sym_hash_in);
    setting_opt(&mut opts.symbol_write_exclude_out, symbol_write_exclude_out);
    setting_opt(
        &mut opts.symbol_write_referenced_out,
        symbol_write_referenced_out,
    );
    setting_opt(
        &mut opts.symbol_write_reindexed_out,
        symbol_write_reindexed_out,
    );
    setting(
        &mut opts.symbol_write_sym_hash_out,
        symbol_write_sym_hash_out,
    );
    setting(
        &mut opts.tco_disallow_discarded_nullable_awaitables,
        tco_disallow_discarded_nullable_awaitables,
    );
    setting(
        &mut opts.tco_check_duplicate_enum_values,
        tco_check_duplicate_enum_values,
    );
    setting(
        &mut opts.tco_typecheck_sample_rate,
        tco_typecheck_sample_rate,
    );
    setting(&mut opts.tco_pessimise_builtins, tco_pessimise_builtins);
    setting(
        &mut opts.tco_enable_no_auto_dynamic,
        tco_enable_no_auto_dynamic,
    );
    setting(
        &mut opts.tco_skip_check_under_dynamic,
        tco_skip_check_under_dynamic,
    );
    setting(&mut opts.tco_typed_open_shapes, tco_typed_open_shapes);
    setting(&mut opts.tco_named_variadic_type, tco_named_variadic_type);
    setting(
        &mut opts.tco_variadic_named_parameters,
        tco_variadic_named_parameters,
    );
    setting(
        &mut opts.tco_silence_errors_under_dynamic,
        tco_silence_errors_under_dynamic,
    );
    setting(
        &mut opts.tco_reject_promoted_property_redeclaration,
        tco_reject_promoted_property_redeclaration,
    );
    setting(
        &mut opts.tco_allowed_expression_tree_visitors,
        tco_allowed_expression_tree_visitors,
    );
    setting(
        &mut opts.tco_typeconst_concrete_concrete_error,
        tco_typeconst_concrete_concrete_error,
    );
    setting(
        &mut opts.tco_meth_caller_only_public_visibility,
        tco_meth_caller_only_public_visibility,
    );
    setting(
        &mut opts.tco_require_extends_implements_ancestors,
        tco_require_extends_implements_ancestors,
    );
    setting(&mut opts.tco_implicit_inherit_sdt, tco_implicit_inherit_sdt);
    setting_opt(&mut opts.tco_repo_stdlib_path, tco_repo_stdlib_path);
    setting(
        &mut opts.tco_explicit_consistent_constructors,
        tco_explicit_consistent_constructors,
    );
    setting(
        &mut opts.tco_require_types_class_consts,
        tco_require_types_class_consts,
    );
    setting(&mut opts.tco_type_printer_fuel, tco_type_printer_fuel);
    setting(
        &mut opts.tco_profile_top_level_definitions,
        tco_profile_top_level_definitions,
    );
    setting_opt(
        &mut opts.tco_typecheck_if_name_matches_regexp,
        tco_typecheck_if_name_matches_regexp,
    );
    setting(&mut opts.log_levels, log_levels);
    setting(
        &mut opts.tco_allowed_files_for_module_declarations,
        tco_allowed_files_for_module_declarations,
    );
    setting(
        &mut opts.tco_allow_all_files_for_module_declarations,
        tco_allow_all_files_for_module_declarations,
    );
    setting(
        &mut opts.tco_populate_dead_unsafe_cast_heap,
        tco_populate_dead_unsafe_cast_heap,
    );
    setting(&mut opts.dump_tast_hashes, dump_tast_hashes);
    setting(&mut opts.warnings_default_all, warnings_default_all);
    setting(&mut opts.warnings_in_sandcastle, warnings_in_sandcastle);
    setting(
        &mut opts.tco_allowed_files_for_ignore_readonly,
        tco_allowed_files_for_ignore_readonly,
    );
    setting(
        &mut opts.tco_package_allow_classconst_violations,
        tco_package_allow_classconst_violations,
    );
    setting(
        &mut opts.tco_package_allow_all_tconst_violations,
        tco_package_allow_all_tconst_violations,
    );
    setting(
        &mut opts.tco_package_allow_enforceable_enum_violations,
        tco_package_allow_enforceable_enum_violations,
    );
    setting(
        &mut opts.tco_package_exclude_patterns,
        tco_package_exclude_patterns,
    );
    setting_opt(&mut opts.tco_extended_reasons, tco_extended_reasons);
    setting(
        &mut opts.tco_disable_physical_equality,
        tco_disable_physical_equality,
    );
    setting(&mut opts.re_no_cache, re_no_cache);
    setting(
        &mut opts.hh_distc_should_disable_trace_store,
        hh_distc_should_disable_trace_store,
    );
    setting(
        &mut opts.hh_distc_exponential_backoff_num_retries,
        hh_distc_exponential_backoff_num_retries,
    );
    setting(&mut opts.hack_warnings, hack_warnings);
    setting(&mut opts.recursive_case_types, recursive_case_types);
    setting(&mut opts.class_sub_classname, class_sub_classname);
    setting(&mut opts.class_class_type, class_class_type);
    setting(
        &mut opts.needs_concrete_class_function_pointer_check,
        needs_concrete_class_function_pointer_check,
    );
    setting(
        &mut opts.strict_consistent_construct,
        strict_consistent_construct,
    );
    setting(&mut opts.allow_class_string_cast, allow_class_string_cast);
    setting(
        &mut opts.class_pointer_ban_class_array_key,
        class_pointer_ban_class_array_key,
    );
    setting(
        &mut opts.tco_permits_bypassing_visibility,
        tco_permits_bypassing_visibility,
    );
    setting(
        &mut opts.tco_tests_bypass_visibility_static_properties,
        tco_tests_bypass_visibility_static_properties,
    );
    setting(
        &mut opts.tco_missing_targs_as_fresh_generics,
        tco_missing_targs_as_fresh_generics,
    );
    setting(
        &mut opts.tco_ban_memoize_erased_generic_return,
        tco_ban_memoize_erased_generic_return,
    );
    setting(
        &mut opts.tco_xhp_attribute_reads_not_refined,
        tco_xhp_attribute_reads_not_refined,
    );
    global_options_set_rest(&mut opts);
    Ok(opts)
}

fn warn_on_did_you_mean(source: &str, key: &str, result: Result<(), config_keys::DidYouMean>) {
    match result {
        Ok(()) => (),
        Err(config_keys::DidYouMean(suggestion)) => {
            let msg = match suggestion {
                None => format!("Unrecognized {} config option: {}", source, key),
                Some(s) => format!(
                    "Unrecognized {} config option: {}. Did you mean {}?",
                    source, key, s
                ),
            };
            hh_logger::warn(None, None, &msg)
        }
    }
}

/// Validate CLI --config key=value overrides.
/// Logs a warning for each key that is not a recognized config option.
/// Warn-only (not fatal): unrecognized keys can occur during
/// rollouts/rollbacks.
pub fn warn_on_invalid_config_keys(cli_config_overrides: &[(String, String)]) {
    for (key, _value) in cli_config_overrides {
        warn_on_did_you_mean("--config", key, config_keys::validate(key));
    }
}

/// Validate keys in a parsed .hhconfig file.
/// Logs a warning for each key that is not recognized.
pub fn warn_on_invalid_hhconfig_keys(config: &config_file::T) {
    let config_keys = config_file_common::keys(config);
    for key in &config_keys {
        warn_on_did_you_mean(".hhconfig", key, config_keys::validate_hhconfig_key(key));
    }
}

/// Load local config from the following sources:
///
///   * /etc/hh.conf
///   * overridden by Knobs
///   * overridden by ExperimentsConfig
///   * overridden by command line overrides
///
/// If not silent, then prints what it's doing to stderr.
/// Used by `load_with_dynamic_overrides`.
#[allow(dead_code)]
fn load_local_config(
    config: &config_file::T,
    version: &config_file::Version,
    command_line_overrides: &config_file::T,
    apply_dynamic_overrides: &impl Fn(bool, &config_file::T) -> config_file::T,
    silent: bool,
    from: &str,
) -> Result<crate::server_local_config::T, crate::sys_utils::SysError> {
    let current_rolled_out_flag_idx =
        int_(hhconfig::CURRENT_SAVED_STATE_ROLLOUT_FLAG_INDEX, 0, config);
    let deactivate_saved_state_rollout =
        bool_(hhconfig::DEACTIVATE_SAVED_STATE_ROLLOUT, false, config);
    crate::server_local_config_load::load_with_dynamic_overrides(
        apply_dynamic_overrides,
        silent,
        version,
        current_rolled_out_flag_idx,
        deactivate_saved_state_rollout,
        from,
        command_line_overrides,
    )
}

/// As [load], with [apply_dynamic_overrides] applied after JustKnobs and before
/// SandboxExperiment while loading the local config.
#[cfg(feature = "port")] // `Package_config` and `Custom_error_config_loader` are `port` modules.
pub fn load_with_dynamic_overrides(
    apply_dynamic_overrides: impl Fn(bool, &config_file::T) -> config_file::T,
    silent: bool,
    from: &str,
    cli_config_overrides: &[(String, String)],
) -> Result<(T, crate::server_local_config::T), ServerConfigError> {
    let command_line_overrides = config_file::of_list(cli_config_overrides);
    let hhconfig_abs_path = relative_path::to_absolute(&REPO_CONFIG_PATH);
    let hhconfig = config_file::parse_hhconfig(&hhconfig_abs_path);
    warn_on_invalid_hhconfig_keys(&hhconfig);
    let config = config_file::apply_overrides(&hhconfig, &command_line_overrides, None);
    process_untrusted_mode(&config);
    let version = config_file::parse_version(string_opt(hhconfig::VERSION, &config).as_deref());
    let local_config = load_local_config(
        &config,
        &version,
        &command_line_overrides,
        &apply_dynamic_overrides,
        silent,
        from,
    )?;
    if let Some(fn_) = string_opt(hhconfig::PACKAGES_CONFIG_PATH, &config) {
        config_file_common::set_pkgconfig_path(&fn_);
    }
    let pkgs_config_abs_path = relative_path::to_absolute(&relative_path::from_root(
        &config_file_common::get_pkgconfig_path(),
    ));
    // The arguments of `hash`, from the last to the first.
    let pkgconfig_contents = config_file::cat_packages_file(&pkgs_config_abs_path);
    let hhconfig_contents = config_file::cat_hhconfig_file(&hhconfig_abs_path);
    let config_hash = config_file_common::hash(&hhconfig, &hhconfig_contents, &pkgconfig_contents);
    let global_opts_without_package_info = {
        let tco_custom_error_config = crate::custom_error_config_loader::load_and_parse(None);
        let local_config_opts = {
            // `Global_options.set ~po:... ?so_naming_sqlite_path:... ...
            // Global_options.default`
            let default = GlobalOptions::default();
            let mut opts = default.clone();
            opts.po = ParserOptions {
                allow_unstable_features: local_config.allow_unstable_features,
                ..default.po.clone()
            };
            setting_opt(
                &mut opts.so_naming_sqlite_path,
                local_config.naming_sqlite_path.clone(),
            );
            setting_opt(
                &mut opts.tco_log_large_fanouts_threshold,
                local_config.log_large_fanouts_threshold,
            );
            opts.tco_fetch_remote_old_decls = local_config.fetch_remote_old_decls;
            opts.tco_only_fetch_remote_old_decl_during_init =
                local_config.only_fetch_remote_old_decl_during_init;
            opts.tco_remote_old_decl_fetching_include_non_class =
                local_config.remote_old_decl_fetching_include_non_class;
            opts.tco_disable_rust_provider_shallow_decl_invalidation =
                local_config.disable_rust_provider_shallow_decl_invalidation;
            opts.tco_enable_annotation_agnostic_decl_diffing =
                local_config.enable_annotation_agnostic_decl_diffing;
            opts.tco_populate_member_heaps = local_config.populate_member_heaps;
            opts.tco_skip_hierarchy_checks = local_config.skip_hierarchy_checks;
            opts.tco_skip_tast_checks = local_config.skip_tast_checks;
            opts.tco_silence_errors_under_dynamic = local_config.silence_errors_under_dynamic;
            opts.tco_saved_state = local_config.saved_state.clone();
            opts.tco_log_inference_constraints = local_config.log_inference_constraints;
            opts.tco_global_access_check_enabled = local_config.enable_global_access_check;
            opts.dump_tast_hashes = local_config.dump_tast_hashes;
            opts.dump_tasts = local_config.dump_tasts.clone();
            opts.tco_custom_error_config = tco_custom_error_config;
            opts.hack_warnings = if local_config.hack_warnings {
                NoneOrAllExcept::AllExcept(
                    int_list_opt(hhconfig::DISABLED_WARNINGS, &config).unwrap_or_default(),
                )
            } else {
                NoneOrAllExcept::NNone
            };
            opts.warnings_default_all = local_config.warnings_default_all;
            opts.warnings_in_sandcastle = local_config.warnings_in_sandcastle;
            opts.warnings_generated_files =
                string_list(hhconfig::WARNINGS_GENERATED_FILES, vec![], &config);
            opts.hh_distc_exponential_backoff_num_retries =
                local_config.hh_distc_exponential_backoff_num_retries;
            global_options_set_rest(&mut opts);
            opts
        };
        load_config(&config, &local_config_opts)?
    };
    hh_logger::log(&format!(
        "Parsing and loading packages config at {}",
        pkgs_config_abs_path
    ));
    // The arguments, from the last to the first.
    let enable_implicit_packages = bool_(hhconfig::ENABLE_IMPLICIT_PACKAGES, false, &config);
    let package_info = crate::package_config::load_and_parse(
        local_config.package_config_strict_validation,
        enable_implicit_packages,
        &pkgs_config_abs_path,
    );
    crate::package_info::log_package_info(&package_info);
    let global_opts = {
        // `Global_options.set ~po:{... with package_info} global_opts_without_package_info`
        let mut opts = global_opts_without_package_info.clone();
        opts.po = ParserOptions {
            package_info,
            ..global_opts_without_package_info.po.clone()
        };
        global_options_set_rest(&mut opts);
        opts
    };

    // `Diagnostics.allowed_fixme_codes_strict := ...` and
    // `Diagnostics.code_agnostic_fixme := ...` (`diagnostics` is
    // compiled with `server` too).
    crate::diagnostics::set_allowed_fixme_codes_strict(
        global_opts.allowed_fixme_codes_strict.clone(),
    );
    crate::diagnostics::set_code_agnostic_fixme(global_opts.code_agnostic_fixme);
    // The fields of the record, from the last to the first.
    let warnings_generated_files = string_list(hhconfig::WARNINGS_GENERATED_FILES, vec![], &config);
    let naming_table_compression_threads =
        int_(hhconfig::NAMING_TABLE_COMPRESSION_THREADS, 1, &config);
    let naming_table_compression_level = int_(hhconfig::NAMING_TABLE_COMPRESSION_LEVEL, 6, &config);
    let ide_fall_back_to_full_index = bool_(hhconfig::IDE_FALL_BACK_TO_FULL_INDEX, true, &config);
    let warn_on_non_opt_build = bool_(hhconfig::WARN_ON_NON_OPT_BUILD, false, &config);
    let extra_paths = process_extra_paths(&config);
    let ignored_paths = process_ignored_paths(&config)?;
    let formatter_override =
        string_opt(hhconfig::FORMATTER_OVERRIDE, &config).map(|s| maybe_relative_path(&s));
    let sharedmem_config = make_sharedmem_config(&config, &local_config);
    let gc_control = make_gc_control(&config);
    // Since we use the unix alarm() for our timeouts, a timeout value of 0 means
    // to wait indefinitely
    let load_script_timeout = int_(hhconfig::LOAD_SCRIPT_TIMEOUT, 0, &config);
    Ok((
        T {
            version,
            load_script_timeout,
            gc_control,
            sharedmem_config,
            tc_options: global_opts.clone(),
            parser_options: global_opts.po.clone(),
            glean_options: global_opts.clone(),
            symbol_write_options: global_opts,
            formatter_override,
            config_hash: Some(config_hash),
            ignored_paths,
            extra_paths,
            warn_on_non_opt_build,
            ide_fall_back_to_full_index,
            naming_table_compression_level,
            naming_table_compression_threads,
            warnings_generated_files,
        },
        local_config,
    ))
}

/// Load config from these sources (last overrides first):
///   - .hhconfig file in the root directory.
///   - Flags passed via CLI option `--config`. These are retrieved from [cli_config_overrides].
///
/// Also calls into `ServerLocalConfigLoad.load`.
///
/// Those two configs get mingled to make a `TypecheckerOptions.t`,
/// `ParserOptions.t` and `Glean_options.t` which can
/// then be retrieved using the `typechecker_options`,  `parser_options`,
/// `glean_options` helpers.
#[cfg(feature = "port")] // `Package_config` and `Custom_error_config_loader` are `port` modules.
pub fn load(
    silent: bool,
    from: &str,
    cli_config_overrides: &[(String, String)],
) -> Result<(T, crate::server_local_config::T), ServerConfigError> {
    load_with_dynamic_overrides(
        |_silent, config| config.clone(),
        silent,
        from,
        cli_config_overrides,
    )
}

/// useful in testing code
pub fn default_config() -> T {
    T {
        version: config_file::Version::OpaqueVersion(None),
        load_script_timeout: 0,
        gc_control: global_config::gc_control(),
        sharedmem_config: shared_mem::default_config(),
        // `Typechecker_options.default`, `Glean_options.default` and
        // `Symbol_write_options.default` are all `Global_options.default`.
        tc_options: GlobalOptions::default(),
        glean_options: GlobalOptions::default(),
        symbol_write_options: GlobalOptions::default(),
        parser_options: ParserOptions::default(),
        formatter_override: None,
        config_hash: None,
        ignored_paths: vec![],
        extra_paths: vec![],
        warn_on_non_opt_build: false,
        ide_fall_back_to_full_index: false,
        naming_table_compression_level: 6,
        naming_table_compression_threads: 1,
        warnings_generated_files: vec![],
    }
}

pub fn set_parser_options(config: T, popt: ParserOptions) -> T {
    T {
        parser_options: popt,
        ..config
    }
}

pub fn set_tc_options(config: T, tcopt: GlobalOptions) -> T {
    T {
        tc_options: tcopt,
        ..config
    }
}

pub fn set_glean_options(config: T, gleanopt: GlobalOptions) -> T {
    T {
        glean_options: gleanopt,
        ..config
    }
}

pub fn set_symbol_write_options(config: T, swriteopt: GlobalOptions) -> T {
    T {
        symbol_write_options: swriteopt,
        ..config
    }
}

pub fn gc_control(config: &T) -> global_config::GcControl {
    config.gc_control.clone()
}

pub fn sharedmem_config(config: &T) -> shared_mem::Config {
    config.sharedmem_config.clone()
}

pub fn typechecker_options(config: &T) -> GlobalOptions {
    config.tc_options.clone()
}

pub fn parser_options(config: &T) -> ParserOptions {
    config.parser_options.clone()
}

pub fn glean_options(config: &T) -> GlobalOptions {
    config.glean_options.clone()
}

pub fn symbol_write_options(config: &T) -> GlobalOptions {
    config.symbol_write_options.clone()
}

pub fn formatter_override(config: &T) -> Option<path::T> {
    config.formatter_override.clone()
}

pub fn config_hash(config: &T) -> Option<String> {
    config.config_hash.clone()
}

/// `List.map ~f:Str.regexp` (`crate::rt::ocaml_str`). A pattern that `Str`
/// cannot compile raises its `Failure` (a panic with its message).
pub fn ignored_paths(config: &T) -> Vec<ocaml_str::Regexp> {
    config
        .ignored_paths
        .iter()
        .map(|s| match ocaml_str::regexp(s) {
            Ok(re) => re,
            Err(ocaml_str::Failure(msg)) => panic!("{}", msg),
        })
        .collect()
}

/// The patterns of [`ignored_paths`], uncompiled (not in the OCaml: `hh
/// check` compiles them with the `regex` crate, `crate::files`).
pub fn ignored_path_patterns(config: &T) -> &[String] {
    &config.ignored_paths
}

pub fn extra_paths(config: &T) -> Vec<path::T> {
    config.extra_paths.clone()
}

pub fn version(config: &T) -> config_file::Version {
    config.version.clone()
}

pub fn warn_on_non_opt_build(config: &T) -> bool {
    config.warn_on_non_opt_build
}

pub fn ide_fall_back_to_full_index(config: &T) -> bool {
    config.ide_fall_back_to_full_index
}

pub fn warnings_generated_files(config: &T) -> Vec<String> {
    config.warnings_generated_files.clone()
}

/// `Ai_options` (`--ai`) is Meta-only: in OSS, `Ai_options.modify_shared_mem`
/// returns the config it is given.
#[cfg(feature = "server")] // `Ai_options` is a `server` module.
pub fn update_config_with_ai_options(
    config: T,
    local_config: crate::server_local_config::T,
    ai_options: Option<crate::ai_options::T>,
) -> (T, crate::server_local_config::T) {
    match ai_options {
        None => (config, local_config),
        Some(ai) => {
            let watchman = crate::server_local_config::watchman::T {
                enabled: false,
                subscribe: false,
                ..local_config.watchman.clone()
            };
            let edenfs_file_watcher = crate::server_local_config::edenfs_file_watcher::T {
                enabled: false,
                ..local_config.edenfs_file_watcher.clone()
            };
            let local_config = crate::server_local_config::T {
                watchman,
                edenfs_file_watcher,
                interrupt_on_file_changes: false,
                interrupt_on_client: false,
                trace_parsing: false,
                ..local_config
            };
            let sharedmem_config =
                crate::ai_options::modify_shared_mem(&ai, &config.sharedmem_config);
            (
                T {
                    sharedmem_config,
                    ..config
                },
                local_config,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use oxidized::experimental_features::FeatureStatus;

    use super::*;

    fn config(s: &str) -> config_file::T {
        config_file::parse_contents(s.as_bytes())
    }

    fn strings(l: &[&str]) -> Vec<String> {
        l.iter().map(|s| s.to_string()).collect()
    }

    fn load(s: &str) -> GlobalOptions {
        load_config(&config(s), &GlobalOptions::default()).unwrap()
    }

    /// Slack's `.hhconfig` (webapp), as of this port.
    const SLACK_HHCONFIG: &str = r#"sharedmem_hash_table_pow=22
sharedmem_dep_table_pow=22
ignored_paths=["^[.]claude/worktrees/", "^[.]codex/worktrees/", "^[.]scratch/", "^bazel-webapp/", "^db_schemas/", "^fonts/", "^gen-py/", "^gen-rs/", "^img/", "^js/modern/", "^js/app/", "^js/projects/", "^node_modules/", "^proto_idl/", "^sounds/", "^spacesuit/", "^static/", "^style/", "^translations/", "^rspack/", "^rspack-next/", "^include/gen_autoload_map.php$", "^tests/playwright/node_modules/"]
disable_lval_as_an_expression=true
hackfmt.indent_width=4
hackfmt.tabs=true
hackfmt.line_width=120
hackfmt.add_trailing_commas=true
hackfmt.version=0
user_attributes=Codegen
disable_modes=true
disallow_array_literal=true
disallow_invalid_arraykey=true
disallow_discarded_nullable_awaitables=true
allowed_decl_fixme_codes=1002,2053,3012,4035,4070,4341
allowed_fixme_codes_strict=4128,4035,2049,4070,4107,3012,4341,2053
enable_xhp_class_modifier=true
disable_xhp_element_mangling=true
const_default_func_args=true
const_default_lambda_args=true
disallow_fun_and_cls_meth_pseudo_funcs=true
disallow_inst_meth=true
enable_strict_string_concat_interp=true
disallow_hash_comments=true
auto_namespace_map = { "Vec": "HH\\Lib\\Vec", "Dict": "HH\\Lib\\Dict", "Str": "HH\\Lib\\Str", "C": "HH\\Lib\\C", "Keyset": "HH\\Lib\\Keyset" , "Math": "HH\\Lib\\Math" , "Asio": "HH\\Asio" }
type_printer_fuel = 1000
enable_sound_dynamic_type = true
everything_sdt = true
silence_errors_under_dynamic = true
strict_wellformedness = 2
check_bool_for_condition = 2
disallow_bool_cast = true
class_pointer_array_write_keys = 2
class_pointer_array_literal_keys = 2
class_pointer_tyvar_lower_bound = 5
class_pointer_tyvar_upper_bound = 5
class_pointer_ban_classname_new = 2
class_pointer_ban_classname_static_meth = 2
class_pointer_ban_classname_class_const = 2
class_pointer_ban_class_array_key = true
class_pointer_ban_classname_type_structure = 2
allow_class_string_cast = false
"#;

    #[test]
    fn empty_config_keeps_the_options() {
        let expected = GlobalOptions {
            po: ParserOptions {
                // Never use the legacy mode for hh_server
                use_legacy_experimental_feature_config: false,
                ..ParserOptions::default()
            },
            ..GlobalOptions::default()
        };
        assert_eq!(load(""), expected);
        // What is not in the config is taken from the options given.
        let options = GlobalOptions {
            tco_timeout: 7,
            tco_extended_reasons: Some(ExtendedReasonsConfig::Legacy),
            needs_concrete_class_function_pointer_check: 1,
            ..GlobalOptions::default()
        };
        let opts = load_config(&config(""), &options).unwrap();
        assert_eq!(opts.tco_timeout, 7);
        assert_eq!(
            opts.tco_extended_reasons,
            Some(ExtendedReasonsConfig::Legacy)
        );
        assert_eq!(opts.needs_concrete_class_function_pointer_check, 1);
        // `Global_options.set` resets `tco_dynamic_inference`.
        let options = GlobalOptions {
            tco_dynamic_inference: true,
            ..GlobalOptions::default()
        };
        assert!(!load_config(&config(""), &options).unwrap().tco_dynamic_inference);
    }

    #[test]
    fn keys_are_read() {
        let opts = load(
            r#"timeout = 30
disallow_discarded_nullable_awaitables = true
allowed_fixme_codes_strict = 4128,4035 2049
allowed_decl_fixme_codes = 1002
enable_experimental_stx_features = {"pipe_await": "Preview", "case_types": "Unstable", "pipe_await": "Unstable"}
log_levels = {"pessimise": 1, "sub": 2}
extended_reasons = 3
hack_warnings = true
disabled_warnings = 12001, 12002
allowed_expression_tree_visitors = Foo, \Bar
permits_bypassing_visibility = A
typecheck_sample_rate = 0.5
repo_stdlib_path = /x
glean_reponame = repo
symbol_write_index_paths_file = f
is_systemlib = true
keep_user_attributes = true
"#,
        );
        assert_eq!(opts.tco_timeout, 30);
        assert!(opts.tco_disallow_discarded_nullable_awaitables);
        assert_eq!(
            opts.allowed_fixme_codes_strict,
            [2049, 4035, 4128].into_iter().collect()
        );
        assert_eq!(
            opts.po.allowed_decl_fixme_codes,
            [1002].into_iter().collect()
        );
        // The last of a feature given twice wins.
        assert_eq!(
            opts.po.experimental_features,
            [
                ("case_types".to_string(), FeatureStatus::Unstable),
                ("pipe_await".to_string(), FeatureStatus::Unstable)
            ]
            .into_iter()
            .collect()
        );
        assert!(!opts.po.consider_unspecified_experimental_features_released);
        assert_eq!(
            opts.log_levels,
            [("pessimise".to_string(), 1), ("sub".to_string(), 2)]
                .into_iter()
                .collect()
        );
        assert_eq!(
            opts.tco_extended_reasons,
            Some(ExtendedReasonsConfig::Extended(3))
        );
        assert_eq!(
            opts.hack_warnings,
            NoneOrAllExcept::AllExcept(vec![12001, 12002])
        );
        assert_eq!(
            opts.tco_allowed_expression_tree_visitors,
            strings(&["\\Foo", "\\Bar"])
        );
        assert_eq!(opts.tco_permits_bypassing_visibility, strings(&["\\A"]));
        assert_eq!(opts.tco_typecheck_sample_rate, 0.5);
        assert_eq!(opts.tco_repo_stdlib_path, Some("/x".to_string()));
        assert_eq!(opts.glean_reponame, "repo");
        assert_eq!(opts.symbol_write_index_paths_file, Some("f".to_string()));
        assert!(opts.po.is_systemlib);
        assert!(opts.po.keep_user_attributes);
        // `hack_warnings = false` is no warnings at all; a list of disabled
        // warnings that does not parse is no list.
        assert_eq!(
            load("hack_warnings = false").hack_warnings,
            NoneOrAllExcept::NNone
        );
        assert_eq!(
            load("hack_warnings = true\ndisabled_warnings = 1,x").hack_warnings,
            NoneOrAllExcept::AllExcept(vec![])
        );
    }

    #[test]
    fn needs_concrete() {
        // The check for function pointers errors unless it is configured.
        let opts = load("");
        assert_eq!(opts.needs_concrete_class_function_pointer_check, 2);
        let opts = load("needs_concrete_class_function_pointer_check = 1");
        assert_eq!(opts.needs_concrete_class_function_pointer_check, 1);
    }

    #[test]
    #[should_panic(
        expected = "Invalid_argument: needs_concrete_class_function_pointer_check must be 0, 1, or 2"
    )]
    fn needs_concrete_out_of_range() {
        load("needs_concrete_class_function_pointer_check = 3");
    }

    #[test]
    #[should_panic(expected = "Invalid_argument: invalid digit found in string")]
    fn malformed_int() {
        load("timeout = abc");
    }

    #[test]
    #[should_panic(expected = "int_of_string")]
    fn malformed_code_list() {
        load("allowed_fixme_codes_strict = 1,x");
    }

    #[test]
    #[should_panic(expected = "non-integer log level value")]
    fn malformed_log_levels() {
        load(r#"log_levels = {"a": "b"}"#);
    }

    #[test]
    #[should_panic(expected = "expected JSON object")]
    fn auto_namespace_map_not_an_object() {
        load("auto_namespace_map = [1]");
    }

    #[test]
    #[should_panic(expected = "Invalid experimental feature name: bad")]
    fn bad_experimental_feature() {
        load(r#"enable_experimental_stx_features = {"bad": "Preview"}"#);
    }

    #[test]
    fn json_errors_are_yojson_errors() {
        let r = load_config(&config("log_levels = {"), &GlobalOptions::default());
        assert_eq!(
            r.unwrap_err(),
            // (Oracle: `{` gives `bytes 0-1`.)
            yojson::JsonError("Line 1, bytes 0-1:\nUnexpected end of input".to_string())
        );
    }

    /// OCaml evaluates the arguments of `Global_options.set` and the fields
    /// of the parser options from the last to the first in the order of
    /// their declaration (in `global_options.ml` and `parser_options.ml`),
    /// after `experimental_features`: of several malformed values, the first
    /// that raises is the last declared of its group.
    #[test]
    fn errors_come_in_the_order_of_ocaml() {
        let message = |s: &str| {
            let payload = std::panic::catch_unwind(|| load(s)).unwrap_err();
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap()
        };
        // The last argument of `set` (a bool) before the second (an int).
        assert_eq!(
            message("timeout = abc\ntests_bypass_visibility_static_properties = x"),
            "Invalid_argument: provided string was not `true` or `false`"
        );
        // `set` declares `?log_levels` (18th) before `?tco_typecheck_sample_rate`
        // (52nd), although `load_config` passes them the other way round: the
        // sample rate is evaluated first.
        assert_eq!(
            message("typecheck_sample_rate = x\nlog_levels = [1]"),
            "Invalid_argument: invalid float literal"
        );
        // Likewise `?hack_warnings` (86th) before
        // `?hh_distc_exponential_backoff_num_retries` (98th).
        assert_eq!(
            message("hack_warnings = x\nhh_distc_exponential_backoff_num_retries = y"),
            "Invalid_argument: invalid digit found in string"
        );
        // And `?allowed_fixme_codes_strict` (17th) before `?log_levels`
        // (18th), passed in the same order.
        assert_eq!(
            message("allowed_fixme_codes_strict = x\nlog_levels = [1]"),
            "expected JSON object"
        );
        // The parser options before the arguments of `set`.
        assert_eq!(
            message("tests_bypass_visibility_static_properties = x\nallowed_decl_fixme_codes = y"),
            "int_of_string"
        );
        // `experimental_features` before all.
        assert_eq!(
            message("allowed_decl_fixme_codes = y\nenable_experimental_stx_features = []"),
            "expected JSON object"
        );
    }

    #[test]
    fn auto_namespace_map() {
        // In the reverse order, duplicates kept, targets that are not strings
        // dropped.
        assert_eq!(
            convert_auto_namespace_to_map(
                r#"{"Vec": "HH\\Lib\\Vec", "Bad": 1, "C": "HH\\Lib\\C", "Vec": "V"}"#
            )
            .unwrap(),
            vec![
                ("Vec".to_string(), "V".to_string()),
                ("C".to_string(), "HH\\Lib\\C".to_string()),
                ("Vec".to_string(), "HH\\Lib\\Vec".to_string()),
            ]
        );
    }

    #[test]
    fn helpers() {
        assert_eq!(split_config_list(" a, b,,c\t"), strings(&["a", "b", "c"]));
        assert_eq!(split_config_list(""), Vec::<String>::new());
        assert_eq!(process_experimental(&strings(&["False"])), SSet::new());
        assert_eq!(
            process_experimental(&strings(&["a", "B"])),
            ["a".to_string(), "b".to_string()].into_iter().collect()
        );
        assert_eq!(process_migration_flags(&strings(&["false"])), SSet::new());
        assert_eq!(process_migration_flags(&[]), SSet::new());
        assert_eq!(convert_paths(r#"["a", 1, "b"]"#).unwrap(), strings(&["a", "b"]));
        let reasons = |s: &str| reasons_config_opt(&config(&format!("extended_reasons = {}", s)));
        assert_eq!(reasons("debug"), Some(ExtendedReasonsConfig::Debug));
        assert_eq!(reasons("legacy"), Some(ExtendedReasonsConfig::Legacy));
        assert_eq!(reasons("0x10"), Some(ExtendedReasonsConfig::Extended(16)));
        assert_eq!(reasons("x"), None);
        assert_eq!(reasons_config_opt(&config("")), None);
        assert_eq!(
            prepare_iset(&config("k = 3, 1"), "k"),
            Some([1, 3].into_iter().collect())
        );
        assert_eq!(process_ignored_paths(&config("")).unwrap(), Vec::<String>::new());
        assert_eq!(process_extra_paths(&config("")), Vec::<String>::new());
    }

    #[test]
    #[should_panic(expected = "expected JSON array")]
    fn paths_not_a_list() {
        let _ = convert_paths("{}");
    }

    #[test]
    fn paths_relative_to_the_root() {
        relative_path::set_prefixes_for_tests();
        assert_eq!(maybe_relative_path("foo/bar"), "/data/www/foo/bar");
        assert_eq!(maybe_relative_path("/nonexistent/x"), "/nonexistent/x");
        assert_eq!(
            process_extra_paths(&config("extra_paths = a, /nonexistent/b")),
            strings(&["/data/www/a", "/nonexistent/b"])
        );
        assert_eq!(
            REPO_CONFIG_PATH.clone(),
            relative_path::from_root(".hhconfig")
        );
    }

    #[test]
    fn untrusted_mode() {
        let failure = |s: &str| {
            let c = config(s);
            let payload = std::panic::catch_unwind(|| process_untrusted_mode(&c)).err()?;
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
        };
        assert_eq!(failure("untrusted_mode = false\nextra_paths = x"), None);
        assert_eq!(failure(""), None);
        assert_eq!(
            failure("untrusted_mode = true\nsharedmem_heap_size = 1\nextra_paths = x\nGC_minor = 1\ntimeout = 1"),
            Some("option not permitted in untrusted_mode: GC_minor, extra_paths, sharedmem_heap_size".to_string())
        );
        // Enabled without any forbidden key: it fails all the same.
        assert_eq!(
            failure("untrusted_mode = true"),
            Some("untrusted_mode can only be enabled, not disabled".to_string())
        );
        assert_eq!(
            failure("untrusted_mode = yes"),
            Some("Invalid_argument: bool_of_string".to_string())
        );
    }

    #[test]
    fn gc_control_keys() {
        let gc = make_gc_control(&config(
            "gc_minor_heap_size = 1_000\ngc_space_overhead = 80",
        ));
        assert_eq!(
            gc,
            global_config::GcControl {
                minor_heap_size: 1000,
                space_overhead: 80
            }
        );
        assert_eq!(make_gc_control(&config("")), global_config::gc_control());
    }

    #[test]
    fn config_record() {
        let c = default_config();
        assert!(is_compatible(&c, &default_config()));
        assert_eq!(version(&c), config_file::Version::OpaqueVersion(None));
        assert_eq!(config_hash(&c), None);
        assert!(!ide_fall_back_to_full_index(&c));
        assert_eq!(sharedmem_config(&c), shared_mem::default_config());
        let tcopt = GlobalOptions {
            tco_timeout: 3,
            ..GlobalOptions::default()
        };
        let c2 = set_tc_options(c.clone(), tcopt.clone());
        assert_eq!(typechecker_options(&c2), tcopt);
        assert!(!is_compatible(&c, &c2));
        let popt = ParserOptions {
            everything_sdt: true,
            ..ParserOptions::default()
        };
        assert_eq!(
            parser_options(&set_parser_options(c.clone(), popt.clone())),
            popt
        );
        assert_eq!(
            glean_options(&set_glean_options(c.clone(), tcopt.clone())),
            tcopt
        );
        assert_eq!(
            symbol_write_options(&set_symbol_write_options(c.clone(), tcopt.clone())),
            tcopt
        );
        assert!(ignored_paths(&c).is_empty());
        let c3 = T {
            ignored_paths: strings(&["^foo/", r"bar\(x\|y\)"]),
            ..c
        };
        let res = ignored_paths(&c3);
        assert!(ocaml_str::string_match(&res[0], "foo/a.php", 0));
        assert!(!ocaml_str::string_match(&res[0], "a/foo/a.php", 0));
        assert!(ocaml_str::string_match(&res[1], "bary", 0));
    }

    #[test]
    fn slack_hhconfig() {
        let c = config(SLACK_HHCONFIG);
        let opts = load_config(&c, &GlobalOptions::default()).unwrap();
        assert!(opts.tco_disallow_discarded_nullable_awaitables);
        assert!(opts.po.everything_sdt);
        assert!(opts.po.enable_xhp_class_modifier);
        assert!(opts.po.disable_xhp_element_mangling);
        assert!(opts.tco_silence_errors_under_dynamic);
        assert!(!opts.allow_class_string_cast);
        assert!(opts.class_pointer_ban_class_array_key);
        assert_eq!(opts.tco_type_printer_fuel, 1000);
        assert_eq!(
            opts.po.allowed_decl_fixme_codes,
            [1002, 2053, 3012, 4035, 4070, 4341].into_iter().collect()
        );
        assert_eq!(opts.allowed_fixme_codes_strict.len(), 8);
        assert_eq!(
            opts.po.auto_namespace_map.first(),
            Some(&("Asio".to_string(), "HH\\Asio".to_string()))
        );
        assert_eq!(opts.po.auto_namespace_map.len(), 7);
        assert_eq!(process_ignored_paths(&c).unwrap().len(), 23);
        assert_eq!(make_gc_control(&c), global_config::gc_control());
        process_untrusted_mode(&c);
        warn_on_invalid_hhconfig_keys(&c);
        // Several of its keys are not keys of this version of hh.
        assert_eq!(
            config_keys::validate_hhconfig_key("disable_lval_as_an_expression"),
            Err(config_keys::DidYouMean(None))
        );
    }

    /// What the `hh_config` crate computes from a `.hhconfig` (with an empty
    /// hh.conf) and `load_config` from the same file differ on these fields
    /// (checked here on a config that sets every `.hhconfig` key that
    /// `load_config` reads to a value both accept). `hh check` and `hh single`
    /// no longer take their options from `hh_config` (only `hackc` and
    /// `hackrs` do), so this documents where `hh_config` departs from the
    /// OCaml: these keys are ignored or read differently by those users.
    #[test]
    fn hh_config_differs() {
        let all_keys = r#"abstract_static_props = true
allowed_decl_fixme_codes = 1,2
auto_namespace_map = {"A": "HH\\A", "B": "HH\\B"}
const_static_props = true
deregister_php_stdlib = true
disable_xhp_children_declarations = true
disable_xhp_element_mangling = true
disallow_non_annotated_memoize = true
disallow_static_constants_in_default_func_args = true
enable_class_pointer_hint = false
enable_experimental_stx_features = {"pipe_await": "Preview"}
enable_xhp_class_modifier = true
expression_tree_shape_no_unwrap = true
everything_sdt = true
ignore_string_methods = false
interpret_soft_types_as_like_types = true
is_systemlib = true
keep_user_attributes = true
package_support_multifile_tests = true
treat_non_annotated_memoize_as_kbic = true
union_intersection_type_hints = true
allow_all_files_for_module_declarations = false
allow_class_string_cast = false
allowed_expression_tree_visitors = A, B
allowed_files_for_ignore_readonly = a, b
allowed_files_for_module_declarations = c, d
allowed_fixme_codes_strict = 3,4
call_coeffects = false
class_class_type = false
class_pointer_array_literal_keys = 1
class_pointer_array_write_keys = 1
class_pointer_tyvar_lower_bound = 1
class_pointer_tyvar_upper_bound = 1
class_pointer_ban_class_array_key = true
class_pointer_ban_classname_static_meth = 1
class_sub_classname = false
code_agnostic_fixme = true
const_attribute = true
constraint_array_index_assign = true
constraint_method_call = true
disable_physical_equality = true
disallow_discarded_nullable_awaitables = true
disallow_specialized_function_refs = true
check_duplicate_enum_values = true
include_enum_member_values = true
disallow_toplevel_requires = true
disallow_unresolved_type_variables = true
dump_tast_hashes = true
enable_experimental_tc_features = A, b
enable_no_auto_dynamic = true
explicit_consistent_constructors = 1
extended_reasons = 2
glean_reponame = r
hack_warnings = true
disabled_warnings = 5
hh_distc_exponential_backoff_num_retries = 3
hh_distc_should_disable_trace_store = true
ignore_unsafe_cast = true
implicit_inherit_sdt = true
language_feature_logging = true
like_casts = true
local_coeffects = false
locl_cache_capacity = 5
locl_cache_node_threshold = 6
log_levels = {"a": 1}
meth_caller_only_public_visibility = false
needs_concrete = true
needs_concrete_override_check = 1
package_allow_as_expression_violations = false
package_allow_enforceable_enum_violations = false
package_allow_all_tconst_violations = false
package_allow_classconst_violations = false
package_exclude_patterns = x, y
permits_bypassing_visibility = P
tests_bypass_visibility_static_properties = true
pessimise_builtins = true
populate_dead_unsafe_cast_heap = true
profile_top_level_definitions = true
re_no_cache = true
recursive_case_types = true
repo_stdlib_path = /s
require_extends_implements_ancestors = true
require_types_tco_require_types_class_consts = 1
silence_errors_under_dynamic = true
reject_promoted_property_redeclaration = true
skip_check_under_dynamic = true
typed_open_shapes = true
named_variadic_type = true
variadic_named_parameters = true
strict_consistent_construct = true
symbol_write_exclude_out = e
symbol_write_hhi_path = h
symbol_write_ignore_paths = i
symbol_write_include_hhi = true
symbol_write_index_inherited_members = false
symbol_write_index_paths = j
symbol_write_index_paths_file = k
symbol_write_index_paths_file_output = l
symbol_write_ownership = true
symbol_write_referenced_out = m
symbol_write_reindexed_out = n
symbol_write_root_path = o
symbol_write_sym_hash_in = p
symbol_write_sym_hash_out = true
timeout = 9
typecheck_if_name_matches_regexp = q
typecheck_sample_rate = 0.25
typeconst_concrete_concrete_error = true
type_printer_fuel = 7
use_module_error_for_member_access = true
warnings_default_all = true
warnings_in_sandcastle = false
codegen = true
tco_global_access_check_enabled = true
"#;
        let c = config(all_keys);
        let ours = load_config(&c, &GlobalOptions::default()).unwrap();
        let theirs = hh_config::HhConfig::from_configs(
            std::path::PathBuf::new(),
            c,
            ::config_file::ConfigFile::default(),
            Default::default(),
        )
        .unwrap()
        .common
        .opts;
        let fields = |opts: &GlobalOptions| -> Vec<(String, serde_json::Value)> {
            let mut fields = vec![];
            let json = serde_json::to_value(opts).unwrap();
            for (k, v) in json.as_object().unwrap() {
                if k == "po" {
                    for (k, v) in v.as_object().unwrap() {
                        fields.push((format!("po.{}", k), v.clone()));
                    }
                } else {
                    fields.push((k.clone(), v.clone()));
                }
            }
            fields
        };
        let differences: Vec<String> = fields(&ours)
            .into_iter()
            .zip(fields(&theirs))
            .filter(|((_, a), (_, b))| a != b)
            .map(|((k, _), _)| k)
            .collect();
        // In `serde`'s order (sorted).
        let expected = [
            "glean_reponame",
            "po.auto_namespace_map",
            "po.codegen",
            "po.keep_user_attributes",
            "symbol_write_exclude_out",
            "symbol_write_hhi_path",
            "symbol_write_ignore_paths",
            "symbol_write_include_hhi",
            "symbol_write_index_inherited_members",
            "symbol_write_index_paths",
            "symbol_write_index_paths_file",
            "symbol_write_index_paths_file_output",
            "symbol_write_ownership",
            "symbol_write_referenced_out",
            "symbol_write_reindexed_out",
            "symbol_write_root_path",
            "symbol_write_sym_hash_in",
            "symbol_write_sym_hash_out",
            "tco_allow_all_files_for_module_declarations",
            "tco_disable_physical_equality",
            "tco_disallow_discarded_nullable_awaitables",
            "tco_disallow_unresolved_type_variables",
            "tco_global_access_check_enabled",
            "tco_implicit_inherit_sdt",
            "tco_language_feature_logging",
            "tco_legacy_experimental_features",
            "tco_meth_caller_only_public_visibility",
            "tco_populate_dead_unsafe_cast_heap",
            "tco_typecheck_if_name_matches_regexp",
        ];
        assert_eq!(differences, expected);
    }
}
