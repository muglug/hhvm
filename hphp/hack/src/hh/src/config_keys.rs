// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/config_keys.ml`. See `hh/PORTING.md`.
//!
//! Configuration keys organized by which config file they belong to.
//!
//! - [`hhconfig`]: keys for .hhconfig files
//! - [`hhconf`]: keys for hh.conf (ServerLocalConfig)
//!
//! All tools (hh_server, hh_client, hh_single_type_check) accept both
//! .hhconfig and hh.conf keys via `--config KEY=VALUE`.
//!
//! To add a new config option:
//! 1. Add a new key in the appropriate submodule
//! 2. Use the key constant (e.g. `config_keys::hhconfig::TIMEOUT`) in
//!    server_config.rs or server_local_config_load.rs instead of a raw string
//!
//! Each key is a `pub const` whose value is its name, as every key of the
//! OCaml is (`let timeout = key "timeout"`): the constant is the OCaml value's
//! name in upper case, the string is the OCaml's.
//!
//! OCaml registers each key in a global set as it defines it (`key` and
//! `hhconf_key` add the name to `registered_keys` and
//! `registered_hhconf_keys`), and reads the sets once both submodules are
//! defined (`all_hhconfig_keys = !registered_keys`). Here each submodule
//! lists its keys (`KEYS`, made by the macro that defines the constants, so
//! that the list cannot miss one), and the sets are made from those lists:
//! the same sets, without the global mutable state.

use std::collections::BTreeSet;
use std::sync::LazyLock;

use crate::string_utils;

/// Defines one `pub const` per key, whose value is the key's name, and
/// `KEYS`: every key of the submodule, in the order of the OCaml.
///
/// The key strings are what `.hhconfig`, `hh.conf` and `--config` use; each
/// is the lower case of its constant's name (`NAMES` lets a test check it).
macro_rules! keys {
    ($($name:ident = $key:literal,)*) => {
        $(pub const $name: &str = $key;)*

        /// The keys of this module, in the order they are defined.
        pub(super) const KEYS: &[&str] = &[$($name),*];

        /// The names of the constants, in the order of `KEYS`.
        #[cfg(test)]
        pub(super) const NAMES: &[&str] = &[$(stringify!($name)),*];
    };
}

/// Keys valid in .hhconfig files.
pub mod hhconfig {
    keys! {
        // parser options
        ABSTRACT_STATIC_PROPS = "abstract_static_props",
        ALLOWED_DECL_FIXME_CODES = "allowed_decl_fixme_codes",
        AUTO_NAMESPACE_MAP = "auto_namespace_map",
        BAN_MEMOIZE_ERASED_GENERIC_RETURN = "ban_memoize_erased_generic_return",
        CONST_STATIC_PROPS = "const_static_props",
        DEREGISTER_PHP_STDLIB = "deregister_php_stdlib",
        DISABLE_XHP_CHILDREN_DECLARATIONS = "disable_xhp_children_declarations",
        DISABLE_XHP_ELEMENT_MANGLING = "disable_xhp_element_mangling",
        DISALLOW_NON_ANNOTATED_MEMOIZE = "disallow_non_annotated_memoize",
        ENABLE_EXPERIMENTAL_STX_FEATURES = "enable_experimental_stx_features",
        ENABLE_XHP_CLASS_MODIFIER = "enable_xhp_class_modifier",
        EXPRESSION_TREE_SHAPE_NO_UNWRAP = "expression_tree_shape_no_unwrap",
        ALLOW_SINGLE_STATEMENT_CONCURRENT = "allow_single_statement_concurrent",
        EVERYTHING_SDT = "everything_sdt",
        IGNORE_STRING_METHODS = "ignore_string_methods",
        INTERPRET_SOFT_TYPES_AS_LIKE_TYPES = "interpret_soft_types_as_like_types",
        IS_SYSTEMLIB = "is_systemlib",
        KEEP_USER_ATTRIBUTES = "keep_user_attributes",
        MISSING_TARGS_AS_FRESH_GENERICS = "missing_targs_as_fresh_generics",
        PACKAGE_SUPPORT_MULTIFILE_TESTS = "package_support_multifile_tests",
        TREAT_NON_ANNOTATED_MEMOIZE_AS_KBIC = "treat_non_annotated_memoize_as_kbic",
        UNION_INTERSECTION_TYPE_HINTS = "union_intersection_type_hints",

        // global options and typechecker options
        ALLOW_ALL_FILES_FOR_MODULE_DECLARATIONS = "allow_all_files_for_module_declarations",
        ALLOW_CLASS_STRING_CAST = "allow_class_string_cast",
        ALLOWED_EXPRESSION_TREE_VISITORS = "allowed_expression_tree_visitors",
        ALLOWED_FILES_FOR_IGNORE_READONLY = "allowed_files_for_ignore_readonly",
        ALLOWED_FILES_FOR_MODULE_DECLARATIONS = "allowed_files_for_module_declarations",
        ALLOWED_FIXME_CODES_STRICT = "allowed_fixme_codes_strict",
        CLASS_CLASS_TYPE = "class_class_type",
        CLASS_POINTER_BAN_CLASS_ARRAY_KEY = "class_pointer_ban_class_array_key",
        CLASS_SUB_CLASSNAME = "class_sub_classname",
        CODE_AGNOSTIC_FIXME = "code_agnostic_fixme",
        CONST_ATTRIBUTE = "const_attribute",
        CONSTRAINT_ARRAY_INDEX_ASSIGN = "constraint_array_index_assign",
        CONSTRAINT_METHOD_CALL = "constraint_method_call",
        DISABLE_PHYSICAL_EQUALITY = "disable_physical_equality",
        DISALLOW_DISCARDED_NULLABLE_AWAITABLES = "disallow_discarded_nullable_awaitables",
        CHECK_DUPLICATE_ENUM_VALUES = "check_duplicate_enum_values",
        CHECK_DUPLICATE_RUNTIME_SHAPE_KEYS = "check_duplicate_runtime_shape_keys",
        INCLUDE_ENUM_MEMBER_VALUES = "include_enum_member_values",
        INCLUDE_CONST_SHAPE_KEY_VALUES = "include_const_shape_key_values",
        DISALLOW_TOPLEVEL_REQUIRES = "disallow_toplevel_requires",
        DISALLOW_UNRESOLVED_TYPE_VARIABLES = "disallow_unresolved_type_variables",
        DUMP_TAST_HASHES = "dump_tast_hashes",
        ENABLE_EXPERIMENTAL_TC_FEATURES = "enable_experimental_tc_features",
        ENABLE_NO_AUTO_DYNAMIC = "enable_no_auto_dynamic",
        ENABLE_TC_MIGRATION_FLAGS = "enable_tc_migration_flags",
        EXPLICIT_CONSISTENT_CONSTRUCTORS = "explicit_consistent_constructors",
        EXTENDED_REASONS = "extended_reasons",
        GLEAN_REPONAME = "glean_reponame",
        HACK_WARNINGS = "hack_warnings",
        HH_DISTC_EXPONENTIAL_BACKOFF_NUM_RETRIES = "hh_distc_exponential_backoff_num_retries",
        HH_DISTC_SHOULD_DISABLE_TRACE_STORE = "hh_distc_should_disable_trace_store",
        IMPLICIT_INHERIT_SDT = "implicit_inherit_sdt",
        LANGUAGE_FEATURE_LOGGING = "language_feature_logging",
        LIKE_CASTS = "like_casts",
        LOCL_CACHE_CAPACITY = "locl_cache_capacity",
        LOCL_CACHE_NODE_THRESHOLD = "locl_cache_node_threshold",
        LOG_LEVELS = "log_levels",
        METH_CALLER_ONLY_PUBLIC_VISIBILITY = "meth_caller_only_public_visibility",
        NEEDS_CONCRETE_CLASS_FUNCTION_POINTER_CHECK = "needs_concrete_class_function_pointer_check",
        PACKAGE_ALLOW_ENFORCEABLE_ENUM_VIOLATIONS = "package_allow_enforceable_enum_violations",
        PACKAGE_ALLOW_ALL_TCONST_VIOLATIONS = "package_allow_all_tconst_violations",
        PACKAGE_ALLOW_CLASSCONST_VIOLATIONS = "package_allow_classconst_violations",
        PACKAGE_EXCLUDE_PATTERNS = "package_exclude_patterns",
        PERMITS_BYPASSING_VISIBILITY = "permits_bypassing_visibility",
        TESTS_BYPASS_VISIBILITY_STATIC_PROPERTIES = "tests_bypass_visibility_static_properties",
        PESSIMISE_BUILTINS = "pessimise_builtins",
        POPULATE_DEAD_UNSAFE_CAST_HEAP = "populate_dead_unsafe_cast_heap",
        PROFILE_TOP_LEVEL_DEFINITIONS = "profile_top_level_definitions",
        RE_NO_CACHE = "re_no_cache",
        RECURSIVE_CASE_TYPES = "recursive_case_types",
        REPO_STDLIB_PATH = "repo_stdlib_path",
        REQUIRE_EXTENDS_IMPLEMENTS_ANCESTORS = "require_extends_implements_ancestors",
        REQUIRE_TYPES_TCO_REQUIRE_TYPES_CLASS_CONSTS =
            "require_types_tco_require_types_class_consts",
        SILENCE_ERRORS_UNDER_DYNAMIC = "silence_errors_under_dynamic",
        REJECT_PROMOTED_PROPERTY_REDECLARATION = "reject_promoted_property_redeclaration",
        SKIP_CHECK_UNDER_DYNAMIC = "skip_check_under_dynamic",
        TYPED_OPEN_SHAPES = "typed_open_shapes",
        NAMED_VARIADIC_TYPE = "named_variadic_type",
        VARIADIC_NAMED_PARAMETERS = "variadic_named_parameters",
        STRICT_CONSISTENT_CONSTRUCT = "strict_consistent_construct",
        SYMBOL_WRITE_EXCLUDE_OUT = "symbol_write_exclude_out",
        SYMBOL_WRITE_HHI_PATH = "symbol_write_hhi_path",
        SYMBOL_WRITE_IGNORE_PATHS = "symbol_write_ignore_paths",
        SYMBOL_WRITE_INCLUDE_HHI = "symbol_write_include_hhi",
        SYMBOL_WRITE_INDEX_INHERITED_MEMBERS = "symbol_write_index_inherited_members",
        SYMBOL_WRITE_INDEX_PATHS = "symbol_write_index_paths",
        SYMBOL_WRITE_INDEX_PATHS_FILE = "symbol_write_index_paths_file",
        SYMBOL_WRITE_INDEX_PATHS_FILE_OUTPUT = "symbol_write_index_paths_file_output",
        SYMBOL_WRITE_OWNERSHIP = "symbol_write_ownership",
        SYMBOL_WRITE_REFERENCED_OUT = "symbol_write_referenced_out",
        SYMBOL_WRITE_REINDEXED_OUT = "symbol_write_reindexed_out",
        SYMBOL_WRITE_ROOT_PATH = "symbol_write_root_path",
        SYMBOL_WRITE_SYM_HASH_IN = "symbol_write_sym_hash_in",
        SYMBOL_WRITE_SYM_HASH_OUT = "symbol_write_sym_hash_out",
        TIMEOUT = "timeout",
        TYPECHECK_IF_NAME_MATCHES_REGEXP = "typecheck_if_name_matches_regexp",
        TYPECHECK_SAMPLE_RATE = "typecheck_sample_rate",
        TYPECONST_CONCRETE_CONCRETE_ERROR = "typeconst_concrete_concrete_error",
        TYPE_PRINTER_FUEL = "type_printer_fuel",
        WARNINGS_DEFAULT_ALL = "warnings_default_all",
        WARNINGS_IN_SANDCASTLE = "warnings_in_sandcastle",

        // server options
        CURRENT_SAVED_STATE_ROLLOUT_FLAG_INDEX = "current_saved_state_rollout_flag_index",
        DEACTIVATE_SAVED_STATE_ROLLOUT = "deactivate_saved_state_rollout",
        DISABLED_WARNINGS = "disabled_warnings",
        EXTRA_PATHS = "extra_paths",
        FORMATTER_OVERRIDE = "formatter_override",
        GC_MINOR_HEAP_SIZE = "gc_minor_heap_size",
        GC_SPACE_OVERHEAD = "gc_space_overhead",
        IDE_FALL_BACK_TO_FULL_INDEX = "ide_fall_back_to_full_index",
        IGNORED_PATHS = "ignored_paths",
        LOAD_SCRIPT_TIMEOUT = "load_script_timeout",
        NAMING_TABLE_COMPRESSION_LEVEL = "naming_table_compression_level",
        NAMING_TABLE_COMPRESSION_THREADS = "naming_table_compression_threads",
        PACKAGES_CONFIG_PATH = "packages_config_path",
        ENABLE_IMPLICIT_PACKAGES = "enable_implicit_packages",
        SHAREDMEM_COMPRESSION = "sharedmem_compression",
        SHAREDMEM_DIRS = "sharedmem_dirs",
        SHAREDMEM_GLOBAL_SIZE = "sharedmem_global_size",
        SHAREDMEM_HASH_TABLE_POW = "sharedmem_hash_table_pow",
        SHAREDMEM_HEAP_SIZE = "sharedmem_heap_size",
        SHAREDMEM_LOG_LEVEL = "sharedmem_log_level",
        SHAREDMEM_MINIMUM_AVAILABLE = "sharedmem_minimum_available",
        SHAREDMEM_SAMPLE_RATE = "sharedmem_sample_rate",
        SHM_CACHE_SIZE = "shm_cache_size",
        SHM_USE_SHARDED_HASHTBL = "shm_use_sharded_hashtbl",
        TYPECHECKER_IMPLEMENTATION = "typechecker_implementation",
        UNTRUSTED_MODE = "untrusted_mode",
        VERSION = "version",
        WARN_ON_NON_OPT_BUILD = "warn_on_non_opt_build",
        WARNINGS_GENERATED_FILES = "warnings_generated_files",
        XHP_ATTRIBUTE_READS_NOT_REFINED = "xhp_attribute_reads_not_refined",
    }
}

/// Keys valid in hh.conf (ServerLocalConfig).
/// These keys are accepted by hh_server and hh_client via --config overrides,
/// but NOT by hh_single_type_check.
pub mod hhconf {
    keys! {
        // distc
        ENABLE_FANOUT_AWARE_DISTC = "enable_fanout_aware_distc",
        HH_DISTC_FANOUT_FULL_INIT_THRESHOLD = "hh_distc_fanout_full_init_threshold",
        HH_DISTC_FANOUT_THRESHOLD = "hh_distc_fanout_threshold",
        USE_COMPRESSED_DEP_GRAPH = "use_compressed_dep_graph",
        USE_DISTC = "use_distc",
        USE_DISTC_CRAWL_DIRCACHE = "use_distc_crawl_dircache",
        EDEN_PREFETCH_ENABLED = "eden_prefetch_enabled",
        EDEN_PREFETCH_FANOUT_THRESHOLD = "eden_prefetch_fanout_threshold",
        EDEN_PREFETCH_WORKERS = "eden_prefetch_workers",

        // edenfs file watcher
        EDENFS_FILE_WATCHER_DEBUG_LOGGING = "edenfs_file_watcher_debug_logging",
        EDENFS_FILE_WATCHER_ENABLED = "edenfs_file_watcher_enabled",
        EDENFS_FILE_WATCHER_REPORT_TELEMETRY = "edenfs_file_watcher_report_telemetry",
        EDENFS_FILE_WATCHER_STATE_TRACKING = "edenfs_file_watcher_state_tracking",
        EDENFS_FILE_WATCHER_SYNC_QUERIES_OBEY_DEFERRAL =
            "edenfs_file_watcher_sync_queries_obey_deferral",
        EDENFS_FILE_WATCHER_THROTTLE_TIME_MS = "edenfs_file_watcher_throttle_time_ms",
        EDENFS_FILE_WATCHER_TIMEOUT_SECS = "edenfs_file_watcher_timeout_secs",
        EDENFS_FILE_WATCHER_TRACKED_STATES = "edenfs_file_watcher_tracked_states",

        // experiments / infrastructure
        ART_CLI_LITE_EXIT_STATUS_ENABLED = "art_cli_lite_exit_status_enabled",
        EXPERIMENTS = "experiments",
        EXPERIMENTS_CONFIG_ENABLED = "experiments_config_enabled",
        EXPERIMENTS_CONFIG_PATH = "experiments_config_path",
        EXPERIMENTS_CONFIG_SOURCE = "experiments_config_source",
        EXPERIMENTS_CONFIG_TTL_SECONDS = "experiments_config_ttl_seconds",
        EXPERIMENTS_CONFIG_UPDATE = "experiments_config_update",
        LOG_CATEGORIES = "log_categories",
        LOG_INFERENCE_CONSTRAINTS = "log_inference_constraints",
        LOG_INIT_PROC_STACK_ALSO_ON_ABSENT_FROM = "log_init_proc_stack_also_on_absent_from",
        LOG_LARGE_FANOUTS_THRESHOLD = "log_large_fanouts_threshold",
        MIN_LOG_LEVEL = "min_log_level",
        USE_JUSTKNOBS = "use_justknobs",

        // IDE
        GO_TO_IMPLEMENTATION = "go_to_implementation",
        IDE_FILE_WATCHER_ENABLED = "ide_file_watcher_enabled",
        IDE_FILE_WATCHER_MAX_CHANGED_FILES = "ide_file_watcher_max_changed_files",
        IDE_LOAD_NAMING_TABLE_ON_DISK = "ide_load_naming_table_on_disk",
        IDE_NAMING_TABLE_UPDATE_THRESHOLD = "ide_naming_table_update_threshold",
        IDE_PARSER_CACHE = "ide_parser_cache",
        IDE_SYMBOLINDEX_SEARCH_PROVIDER = "ide_symbolindex_search_provider",
        SYMBOLINDEX_QUIET = "symbolindex_quiet",

        // misc
        DUMP_TASTS = "dump_tasts",
        EDEN_FETCH_PARALLELISM = "eden_fetch_parallelism",
        PACKAGE_CONFIG_STRICT_VALIDATION = "package_config_strict_validation",
        ROLLOUT_GROUP = "rollout_group",
        STATUS_SINGLE_USE_CACHED_DIAGNOSTICS = "status_single_use_cached_diagnostics",
        WORKLOAD_QUANTILE = "workload_quantile",
        ZSTD_DECOMPRESS_BY_FILE = "zstd_decompress_by_file",

        // profiling
        MEMTRACE_DIR = "memtrace_dir",
        PROFILE_DECLING = "profile_decling",
        PROFILE_DESC = "profile_desc",
        PROFILE_LOG = "profile_log",
        PROFILE_OWNER = "profile_owner",
        PROFILE_SLOW_THRESHOLD = "profile_slow_threshold",
        PROFILE_TYPE_CHECK_DURATION_THRESHOLD = "profile_type_check_duration_threshold",
        PROFILE_TYPE_CHECK_MEMORY_THRESHOLD_MB = "profile_type_check_memory_threshold_mb",
        PROFILE_TYPE_CHECK_TWICE = "profile_type_check_twice",

        // provider backend
        ALLOW_UNSTABLE_FEATURES = "allow_unstable_features",
        CACHE_REMOTE_DECLS = "cache_remote_decls",
        RUST_PROVIDER_BACKEND = "rust_provider_backend",
        SET_GLOBAL_PROVIDER_BACKEND_IN_WORKERS = "set_global_provider_backend_in_workers",
        ISOLATION_ALLOW_DECL_REPACKAGING = "isolation_allow_decl_repackaging",

        // saved state
        LOAD_STATE_NATIVELY_DIRTY_FILES_TIMEOUT = "load_state_natively_dirty_files_timeout",
        LOAD_STATE_NATIVELY_DOWNLOAD_TIMEOUT = "load_state_natively_download_timeout",
        LOAD_STATE_NATIVELY_V4 = "load_state_natively_v4",
        SAVED_STATE_MAX_EXPECTED_AGE_DAYS = "saved_state_max_expected_age_days",
        SAVED_STATE_LOOKUP_USE_EDEN = "saved_state_lookup_use_eden",
        SAVED_STATE_DATABASE_SHARD_NAME = "saved_state_database_shard_name",
        SAVED_STATE_MANIFOLD_LOCAL_PORT = "saved_state_manifold_local_port",
        PROJECT_METADATA_W_FLAGS = "project_metadata_w_flags",
        REQUIRE_SAVED_STATE = "require_saved_state",
        SAVED_STATE_CACHE_LIMIT = "saved_state_cache_limit",
        SAVED_STATE_MANIFOLD_API_KEY = "saved_state_manifold_api_key",
        SPECIFY_MANIFOLD_API_KEY = "specify_manifold_api_key",
        SS_FORCE = "ss_force",
        STORE_DECLS_IN_SAVED_STATE = "store_decls_in_saved_state",
        USE_MANIFOLD_CYTHON_CLIENT = "use_manifold_cython_client",
        USE_MINI_STATE = "use_mini_state",
        USE_MINI_STATE_WHEN_INDEXING = "use_mini_state_when_indexing",

        // server operations
        ATTEMPT_FIX_CREDENTIALS = "attempt_fix_credentials",
        CONSUME_STREAMING_ERRORS = "consume_streaming_errors",
        USE_AGENT_ERROR_FORMAT = "use_agent_error_format",
        CPU_PRIORITY = "cpu_priority",
        ENABLE_FUZZY_SEARCH = "enable_fuzzy_search",
        ENABLE_GLOBAL_ACCESS_CHECK = "enable_global_access_check",
        ENABLE_NAMING_TABLE_FALLBACK = "enable_naming_table_fallback",
        ENABLE_ON_NFS = "enable_on_nfs",
        ENABLE_TYPE_CHECK_FILTER_FILES = "enable_type_check_filter_files",
        EXTEND_DEFS_PER_FILE_BUCKET_SIZE = "extend_defs_per_file_bucket_size",
        FETCH_REMOTE_OLD_DECLS = "fetch_remote_old_decls",
        ONLY_FETCH_REMOTE_OLD_DECL_DURING_INIT = "only_fetch_remote_old_decl_during_init",
        REMOTE_OLD_DECL_FETCHING_INCLUDE_NON_CLASS = "remote_old_decl_fetching_include_non_class",
        DISABLE_RUST_PROVIDER_SHALLOW_DECL_INVALIDATION =
            "disable_rust_provider_shallow_decl_invalidation",
        ENABLE_ANNOTATION_AGNOSTIC_DECL_DIFFING = "enable_annotation_agnostic_decl_diffing",
        HEARTBEAT_INTERVAL = "heartbeat_interval",
        PREFETCH_DECLS_ENABLED = "prefetch_decls_enabled",
        PREFETCH_DECLS_THRESHOLD = "prefetch_decls_threshold",
        BLOCK_CLIENT_CONNECTIONS_WHILE_DEFERRING = "block_client_connections_while_deferring",
        HG_AWARE = "hg_aware",
        ALLOW_RESTART_FROM_PRECOMPUTED_SAVED_STATE = "allow_restart_from_precomputed_saved_state",
        HG_AWARE_PARSING_RESTART_THRESHOLD = "hg_aware_parsing_restart_threshold",
        HG_AWARE_REDECL_RESTART_THRESHOLD = "hg_aware_redecl_restart_threshold",
        HG_AWARE_RECHECK_RESTART_THRESHOLD = "hg_aware_recheck_restart_threshold",
        IDLE_GC_SLICE = "idle_gc_slice",
        INFORMANT_MIN_DISTANCE_RESTART = "informant_min_distance_restart",
        INTERRUPT_ON_CLIENT = "interrupt_on_client",
        INTERRUPT_ON_FILE_CHANGES = "interrupt_on_file_changes",
        INTERRUPT_ON_WATCHMAN = "interrupt_on_watchman",
        IO_PRIORITY = "io_priority",
        LONGLIVED_WORKERS = "longlived_workers",
        MAX_PURGATORY_CLIENTS = "max_purgatory_clients",
        MAX_WORKERS = "max_workers",
        NAMING_SQLITE_PATH = "naming_sqlite_path",
        NUM_LOCAL_WORKERS = "num_local_workers",
        POPULATE_MEMBER_HEAPS = "populate_member_heaps",
        PRECHECKED_FILES = "prechecked_files",
        PREDECLARE_IDE = "predeclare_ide",
        PRODUCE_STREAMING_ERRORS = "produce_streaming_errors",
        SEARCH_CHUNK_SIZE = "search_chunk_size",
        SHM_DIRS = "shm_dirs",
        SKIP_HIERARCHY_CHECKS = "skip_hierarchy_checks",
        SKIP_TAST_CHECKS = "skip_tast_checks",
        TICO_INVALIDATE_FILES = "tico_invalidate_files",
        TICO_INVALIDATE_SMART = "tico_invalidate_smart",
        TRACE_PARSING = "trace_parsing",
        TYPE_DECL_BUCKET_SIZE = "type_decl_bucket_size",
        USE_DUMMY_INFORMANT = "use_dummy_informant",
        USE_FULL_FIDELITY_PARSER = "use_full_fidelity_parser",

        // watchman
        USE_WATCHMAN = "use_watchman",
        WATCHMAN_DEBUG_LOGGING = "watchman_debug_logging",
        WATCHMAN_ENABLED = "watchman_enabled",
        WATCHMAN_INIT_TIMEOUT = "watchman_init_timeout",
        WATCHMAN_SOCKNAME = "watchman_sockname",
        WATCHMAN_SUBSCRIBE_V2 = "watchman_subscribe_v2",
        WATCHMAN_SYNCHRONOUS_TIMEOUT = "watchman_synchronous_timeout",
    }
}

// validation

/// When a configuration key looks like a typo, we make a suggestion
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DidYouMean(pub Option<String>);

/// `!registered_keys` once `Hhconfig` is defined: the .hhconfig keys.
pub static ALL_HHCONFIG_KEYS: LazyLock<BTreeSet<&'static str>> =
    LazyLock::new(|| hhconfig::KEYS.iter().copied().collect());

/// `!registered_hhconf_keys` once `Hhconf` is defined: the hh.conf keys.
pub static ALL_HHCONF_KEYS: LazyLock<BTreeSet<&'static str>> =
    LazyLock::new(|| hhconf::KEYS.iter().copied().collect());

pub static ALL_KEYS: LazyLock<BTreeSet<&'static str>> =
    LazyLock::new(|| ALL_HHCONFIG_KEYS.union(&ALL_HHCONF_KEYS).copied().collect());

/// `S_set.elements`: in increasing order.
pub static ALL_HHCONFIG_KEYS_LIST: LazyLock<Vec<&'static str>> =
    LazyLock::new(|| ALL_HHCONFIG_KEYS.iter().copied().collect());

pub static ALL_HHCONF_KEYS_LIST: LazyLock<Vec<&'static str>> =
    LazyLock::new(|| ALL_HHCONF_KEYS.iter().copied().collect());

pub static ALL_KEYS_LIST: LazyLock<Vec<&'static str>> =
    LazyLock::new(|| ALL_KEYS.iter().copied().collect());

/// The key of `candidates` closest to `config_key` (`String_utils.most_similar
/// ~max_edit_distance:3 config_key candidates Fun.id`).
fn most_similar(config_key: &str, candidates: &[&'static str]) -> Option<String> {
    string_utils::most_similar(Some(3), config_key, candidates, |s| s.to_string())
        .map(str::to_string)
}

/// Validate a key against hhconfig keys only
pub fn validate_hhconfig_key(config_key: &str) -> Result<(), DidYouMean> {
    if ALL_HHCONFIG_KEYS.contains(config_key) {
        Ok(())
    } else {
        let suggestion = most_similar(config_key, &ALL_HHCONFIG_KEYS_LIST);
        Err(DidYouMean(suggestion))
    }
}

/// Validate a key against hhconf keys only
pub fn validate_hhconf_key(config_key: &str) -> Result<(), DidYouMean> {
    if ALL_HHCONF_KEYS.contains(config_key) {
        Ok(())
    } else {
        let suggestion = most_similar(config_key, &ALL_HHCONF_KEYS_LIST);
        Err(DidYouMean(suggestion))
    }
}

/// Validate a --config CLI override key against all known keys
/// (both .hhconfig and hh.conf).
pub fn validate(config_key: &str) -> Result<(), DidYouMean> {
    if ALL_KEYS.contains(config_key) {
        Ok(())
    } else {
        let suggestion = most_similar(config_key, &ALL_KEYS_LIST);
        Err(DidYouMean(suggestion))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn did_you_mean(s: Option<&str>) -> Result<(), DidYouMean> {
        Err(DidYouMean(s.map(str::to_string)))
    }

    #[test]
    fn keys_are_their_names() {
        assert_eq!(hhconfig::TIMEOUT, "timeout");
        assert_eq!(
            hhconfig::REQUIRE_TYPES_TCO_REQUIRE_TYPES_CLASS_CONSTS,
            "require_types_tco_require_types_class_consts"
        );
        assert_eq!(hhconf::USE_WATCHMAN, "use_watchman");
        // Every key is the lower case of its constant's name.
        for (keys, names) in [
            (hhconfig::KEYS, hhconfig::NAMES),
            (hhconf::KEYS, hhconf::NAMES),
        ] {
            assert_eq!(keys.len(), names.len());
            for (key, name) in keys.iter().zip(names.iter()) {
                assert_eq!(*key, name.to_ascii_lowercase());
            }
        }
        assert_eq!(hhconfig::KEYS.len(), 133);
        assert_eq!(hhconf::KEYS.len(), 132);
        // No key is in both files, so `ALL_KEYS` has them all.
        assert_eq!(ALL_KEYS.len(), 133 + 132);
        assert_eq!(hhconfig::KEYS.first(), Some(&"abstract_static_props"));
        assert_eq!(hhconf::KEYS.last(), Some(&"watchman_synchronous_timeout"));
    }

    #[test]
    fn validation() {
        assert_eq!(validate_hhconfig_key("timeout"), Ok(()));
        assert_eq!(validate_hhconf_key("max_workers"), Ok(()));
        // hh.conf keys are not .hhconfig keys, and the other way round.
        assert_eq!(validate_hhconfig_key("max_workers"), did_you_mean(None));
        assert_eq!(validate_hhconf_key("timeout"), did_you_mean(None));
        // `validate` takes both.
        assert_eq!(validate("timeout"), Ok(()));
        assert_eq!(validate("max_workers"), Ok(()));
    }

    #[test]
    fn suggestions() {
        // The expectations of test/invalid_config (hh_single_type_check
        // prints them as "Unknown config option: ...").
        assert_eq!(validate("tymeout"), did_you_mean(Some("timeout")));
        assert_eq!(validate("xyzabc"), did_you_mean(None));
        // Case-insensitive, and within 3 edits.
        assert_eq!(validate("TIMEOUT"), did_you_mean(Some("timeout")));
        assert_eq!(
            validate_hhconf_key("use_watchmen"),
            did_you_mean(Some("use_watchman"))
        );
        assert_eq!(
            validate_hhconfig_key("ignored_path"),
            did_you_mean(Some("ignored_paths"))
        );
        // Among keys equally close (one edit from both), the first in
        // increasing order.
        assert_eq!(
            validate("enable_experimental_tx_features"),
            did_you_mean(Some("enable_experimental_stx_features"))
        );
        // More than 3 edits from every key.
        assert_eq!(
            validate_hhconf_key("hg_aware_x_restart_threshold"),
            did_you_mean(None)
        );
        assert_eq!(
            validate_hhconf_key("profile_dec"),
            did_you_mean(Some("profile_desc"))
        );
    }
}
