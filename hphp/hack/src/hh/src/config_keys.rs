// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `config_keys.ml`. See `hh/PORTING.md`.
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
//! 2. Use the key constant (e.g. `config_keys::hhconfig::timeout`) in
//!    server_config.rs or server_local_config_load.rs instead of a raw string
//!
//! Each key is a `pub const` whose value is its name, as every key of the
//! OCaml is (`let timeout = key "timeout"`).
//!
//! OCaml registers each key in a global set as it defines it (`key` and
//! `hhconf_key` add the name to `registered_keys` and
//! `registered_hhconf_keys`), and reads the sets once both submodules are
//! defined (`all_hhconfig_keys = !registered_keys`). Here each submodule
//! lists its keys (`KEYS`, made by the macro that defines the constants, so
//! that the list cannot miss one), and the sets are made from those lists:
//! the same sets, without the global mutable state.

#![allow(non_upper_case_globals)]

use std::collections::BTreeSet;
use std::sync::LazyLock;

use crate::string_utils;

/// Defines one `pub const` per key, whose value is the key's name, and
/// `KEYS`: every key of the submodule, in the order of the OCaml.
macro_rules! keys {
    ($($name:ident,)*) => {
        $(pub const $name: &str = stringify!($name);)*

        /// The keys of this module, in the order they are defined.
        pub(super) const KEYS: &[&str] = &[$($name),*];
    };
}

/// Keys valid in .hhconfig files.
pub mod hhconfig {
    keys! {
        // parser options
        abstract_static_props,
        allowed_decl_fixme_codes,
        auto_namespace_map,
        ban_memoize_erased_generic_return,
        ban_this_escape_in_overridable_constructors,
        ban_this_refinement_in_generic_class,
        const_static_props,
        deregister_php_stdlib,
        disable_xhp_children_declarations,
        disable_xhp_element_mangling,
        disallow_non_annotated_memoize,
        enable_experimental_stx_features,
        enable_xhp_class_modifier,
        expression_tree_shape_no_unwrap,
        allow_single_statement_concurrent,
        everything_sdt,
        forget_one_branch_tconst_refinements,
        foreach_key_after_value,
        ignore_string_methods,
        interpret_soft_types_as_like_types,
        is_systemlib,
        keep_user_attributes,
        list_assign_right_to_left,
        missing_targs_as_fresh_generics,
        package_support_multifile_tests,
        treat_non_annotated_memoize_as_kbic,
        type_structure_fields_may_be_absent,
        union_intersection_type_hints,
        // global options and typechecker options
        allow_all_files_for_module_declarations,
        allow_class_string_cast,
        allowed_expression_tree_visitors,
        allowed_files_for_ignore_readonly,
        allowed_files_for_module_declarations,
        allowed_fixme_codes_strict,
        class_class_type,
        class_pointer_ban_class_array_key,
        class_sub_classname,
        code_agnostic_fixme,
        const_attribute,
        constraint_array_index_assign,
        constraint_method_call,
        disable_physical_equality,
        disallow_discarded_nullable_awaitables,
        check_duplicate_enum_values,
        include_enum_member_values,
        include_const_shape_key_values,
        disallow_toplevel_requires,
        disallow_unresolved_type_variables,
        dump_tast_hashes,
        enable_experimental_tc_features,
        enable_no_auto_dynamic,
        enable_tc_migration_flags,
        explicit_consistent_constructors,
        extended_reasons,
        glean_reponame,
        hack_warnings,
        hh_distc_exponential_backoff_num_retries,
        hh_distc_should_disable_trace_store,
        implicit_inherit_sdt,
        language_feature_logging,
        like_casts,
        locl_cache_capacity,
        locl_cache_node_threshold,
        log_levels,
        meth_caller_only_public_visibility,
        needs_concrete_class_call_check,
        needs_concrete_class_function_pointer_check,
        package_allow_enforceable_enum_violations,
        package_allow_all_tconst_violations,
        package_allow_classconst_violations,
        package_exclude_patterns,
        permits_bypassing_visibility,
        tests_bypass_visibility_static_properties,
        pessimise_builtins,
        populate_dead_unsafe_cast_heap,
        profile_top_level_definitions,
        re_no_cache,
        recursive_case_types,
        repo_stdlib_path,
        require_extends_implements_ancestors,
        require_types_tco_require_types_class_consts,
        silence_errors_under_dynamic,
        reject_promoted_property_redeclaration,
        skip_check_under_dynamic,
        typed_open_shapes,
        named_variadic_type,
        variadic_named_parameters,
        strict_consistent_construct,
        symbol_write_exclude_out,
        symbol_write_hhi_path,
        symbol_write_ignore_paths,
        symbol_write_include_hhi,
        symbol_write_index_inherited_members,
        symbol_write_index_paths,
        symbol_write_index_paths_file,
        symbol_write_index_paths_file_output,
        symbol_write_ownership,
        symbol_write_referenced_out,
        symbol_write_reindexed_out,
        symbol_write_root_path,
        symbol_write_sym_hash_in,
        symbol_write_sym_hash_out,
        timeout,
        typecheck_if_name_matches_regexp,
        typecheck_sample_rate,
        typeconst_concrete_concrete_error,
        type_printer_fuel,
        warnings_default_all,
        warnings_in_sandcastle,
        // server options
        current_saved_state_rollout_flag_index,
        deactivate_saved_state_rollout,
        disabled_warnings,
        extra_paths,
        formatter_override,
        gc_minor_heap_size,
        gc_space_overhead,
        ide_fall_back_to_full_index,
        ignored_paths,
        load_script_timeout,
        naming_table_compression_level,
        naming_table_compression_threads,
        packages_config_path,
        enable_implicit_packages,
        sharedmem_compression,
        sharedmem_dirs,
        sharedmem_global_size,
        sharedmem_hash_table_pow,
        sharedmem_heap_size,
        sharedmem_log_level,
        sharedmem_minimum_available,
        sharedmem_sample_rate,
        shm_cache_size,
        shm_use_sharded_hashtbl,
        untrusted_mode,
        version,
        warn_on_non_opt_build,
        warnings_generated_files,
        xhp_attribute_reads_not_refined,
    }
}

/// Keys valid in hh.conf (ServerLocalConfig).
/// These keys are accepted by hh_server and hh_client via --config overrides,
/// but NOT by hh_single_type_check.
pub mod hhconf {
    keys! {
        // distc
        enable_fanout_aware_distc,
        hh_distc_fanout_full_init_threshold,
        hh_distc_fanout_threshold,
        use_compressed_dep_graph,
        use_distc,
        use_distc_crawl_dircache,
        eden_prefetch_enabled,
        eden_prefetch_fanout_threshold,
        eden_prefetch_workers,
        // edenfs file watcher
        edenfs_file_watcher_debug_logging,
        edenfs_file_watcher_enabled,
        edenfs_file_watcher_report_telemetry,
        edenfs_file_watcher_state_tracking,
        edenfs_file_watcher_sync_queries_obey_deferral,
        edenfs_file_watcher_throttle_time_ms,
        edenfs_file_watcher_timeout_secs,
        edenfs_file_watcher_tracked_states,
        // experiments / infrastructure
        art_cli_lite_exit_status_enabled,
        experiments,
        experiments_config_enabled,
        experiments_config_path,
        experiments_config_source,
        experiments_config_ttl_seconds,
        experiments_config_update,
        log_categories,
        log_inference_constraints,
        log_init_proc_stack_also_on_absent_from,
        log_large_fanouts_threshold,
        min_log_level,
        use_justknobs,
        // IDE
        go_to_implementation,
        ide_file_watcher_enabled,
        ide_file_watcher_max_changed_files,
        ide_load_naming_table_on_disk,
        ide_naming_table_update_threshold,
        ide_parser_cache,
        ide_symbolindex_search_provider,
        symbolindex_quiet,
        // misc
        dump_tasts,
        eden_fetch_parallelism,
        package_config_strict_validation,
        rollout_group,
        status_single_use_cached_diagnostics,
        workload_quantile,
        zstd_decompress_by_file,
        // profiling
        memtrace_dir,
        profile_decling,
        profile_desc,
        profile_log,
        profile_owner,
        profile_slow_threshold,
        profile_type_check_duration_threshold,
        profile_type_check_memory_threshold_mb,
        profile_type_check_twice,
        // provider backend
        allow_unstable_features,
        cache_remote_decls,
        rust_provider_backend,
        set_global_provider_backend_in_workers,
        isolation_allow_decl_repackaging,
        // saved state
        load_state_natively_dirty_files_timeout,
        load_state_natively_download_timeout,
        load_state_natively_v4,
        saved_state_max_expected_age_days,
        saved_state_lookup_use_eden,
        saved_state_database_shard_name,
        saved_state_manifold_local_port,
        project_metadata_w_flags,
        require_saved_state,
        saved_state_cache_limit,
        saved_state_manifold_api_key,
        specify_manifold_api_key,
        ss_force,
        store_decls_in_saved_state,
        use_manifold_cython_client,
        use_mini_state,
        use_mini_state_when_indexing,
        // server operations
        attempt_fix_credentials,
        consume_streaming_errors,
        use_agent_error_format,
        cpu_priority,
        enable_fuzzy_search,
        enable_global_access_check,
        enable_naming_table_fallback,
        enable_on_nfs,
        enable_type_check_filter_files,
        extend_defs_per_file_bucket_size,
        fetch_remote_old_decls,
        only_fetch_remote_old_decl_during_init,
        disable_rust_provider_shallow_decl_invalidation,
        enable_annotation_agnostic_decl_diffing,
        heartbeat_interval,
        prefetch_decls_enabled,
        prefetch_decls_threshold,
        block_client_connections_while_deferring,
        hg_aware,
        allow_restart_from_precomputed_saved_state,
        hg_aware_parsing_restart_threshold,
        hg_aware_redecl_restart_threshold,
        hg_aware_recheck_restart_threshold,
        idle_gc_slice,
        informant_min_distance_restart,
        interrupt_on_client,
        interrupt_on_file_changes,
        interrupt_on_watchman,
        io_priority,
        longlived_workers,
        max_purgatory_clients,
        max_workers,
        naming_sqlite_path,
        num_local_workers,
        populate_member_heaps,
        prechecked_files,
        predeclare_ide,
        produce_streaming_errors,
        search_chunk_size,
        shm_dirs,
        skip_hierarchy_checks,
        skip_tast_checks,
        tico_invalidate_files,
        tico_invalidate_smart,
        trace_parsing,
        type_decl_bucket_size,
        use_dummy_informant,
        use_full_fidelity_parser,
        // watchman
        use_watchman,
        watchman_debug_logging,
        watchman_enabled,
        watchman_init_timeout,
        watchman_sockname,
        watchman_subscribe_v2,
        watchman_synchronous_timeout,
    }
}

// validation

/// When a configuration key looks like a typo, we make a suggestion
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DidYouMean(pub Option<String>);

/// `!registered_keys` once `Hhconfig` is defined: the .hhconfig keys.
pub static all_hhconfig_keys: LazyLock<BTreeSet<&'static str>> =
    LazyLock::new(|| hhconfig::KEYS.iter().copied().collect());

/// `!registered_hhconf_keys` once `Hhconf` is defined: the hh.conf keys.
pub static all_hhconf_keys: LazyLock<BTreeSet<&'static str>> =
    LazyLock::new(|| hhconf::KEYS.iter().copied().collect());

pub static all_keys: LazyLock<BTreeSet<&'static str>> =
    LazyLock::new(|| all_hhconfig_keys.union(&all_hhconf_keys).copied().collect());

/// `S_set.elements`: in increasing order.
pub static all_hhconfig_keys_list: LazyLock<Vec<&'static str>> =
    LazyLock::new(|| all_hhconfig_keys.iter().copied().collect());

pub static all_hhconf_keys_list: LazyLock<Vec<&'static str>> =
    LazyLock::new(|| all_hhconf_keys.iter().copied().collect());

pub static all_keys_list: LazyLock<Vec<&'static str>> =
    LazyLock::new(|| all_keys.iter().copied().collect());

/// The key of `candidates` closest to `config_key` (`String_utils.most_similar
/// ~max_edit_distance:3 config_key candidates Fun.id`).
fn most_similar(config_key: &str, candidates: &[&'static str]) -> Option<String> {
    string_utils::most_similar(Some(3), config_key, candidates, |s| s.to_string())
        .map(str::to_string)
}

/// Validate a key against hhconfig keys only
pub fn validate_hhconfig_key(config_key: &str) -> Result<(), DidYouMean> {
    if all_hhconfig_keys.contains(config_key) {
        Ok(())
    } else {
        let suggestion = most_similar(config_key, &all_hhconfig_keys_list);
        Err(DidYouMean(suggestion))
    }
}

/// Validate a key against hhconf keys only
pub fn validate_hhconf_key(config_key: &str) -> Result<(), DidYouMean> {
    if all_hhconf_keys.contains(config_key) {
        Ok(())
    } else {
        let suggestion = most_similar(config_key, &all_hhconf_keys_list);
        Err(DidYouMean(suggestion))
    }
}

/// Validate a --config CLI override key against all known keys
/// (both .hhconfig and hh.conf).
pub fn validate(config_key: &str) -> Result<(), DidYouMean> {
    if all_keys.contains(config_key) {
        Ok(())
    } else {
        let suggestion = most_similar(config_key, &all_keys_list);
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
        assert_eq!(hhconfig::timeout, "timeout");
        assert_eq!(
            hhconfig::require_types_tco_require_types_class_consts,
            "require_types_tco_require_types_class_consts"
        );
        assert_eq!(hhconf::use_watchman, "use_watchman");
        assert_eq!(hhconfig::KEYS.len(), 138);
        assert_eq!(hhconf::KEYS.len(), 131);
        // No key is in both files, so `all_keys` has them all.
        assert_eq!(all_keys.len(), 138 + 131);
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
