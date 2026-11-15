// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_local_config_load.ml`.
//! See `hh/PORTING.md`.
//!
//! Load configuration flags with the following effective precedence:
//!   - /etc/hh.conf
//!   - JustKnobs
//!   - SandboxExperiment
//!   - ExperimentsConfig
//!   - [overrides]
//!
//! [overrides] are also applied initially so dynamic configuration sources can
//! observe them, then reapplied at the end to retain final precedence.
//!
//! If not [silent], then prints what it's doing to stderr.
//!
//! JustKnobs, the sandbox experiments and the updater of the experiments
//! config are Meta-only: their modules are the OSS stubs, which return the
//! config they are given (`crate::server_local_config_knobs`,
//! `crate::server_local_config_sandbox_experiment`,
//! `crate::experiments_config_file`).
//!
//! Exceptions: OCaml lets all of them through to the callers of `load`. The
//! `Sys_error` of `In_channel.read_lines` (`dump_tasts`) and of reading
//! `/etc/devserver.owners` is the `Err` of `load` and the functions that
//! lead to it. The getters raise `Invalid_argument` on a malformed value (a
//! panic, see `crate::config_file_common`) and `failwith` panics with its
//! message: like the `failwith`s of the rest of the port, they have no
//! handler but the catch-all of the program.

use std::sync::LazyLock;

use oxidized::global_options::SavedState;
use oxidized::global_options::SavedStateLoading;

use crate::config_file;
use crate::config_file::getters::*;
use crate::config_file_common;
use crate::config_keys;
use crate::experiments_config_file;
use crate::global_config;
use crate::hack_event_logger_types::RolloutFlags;
use crate::hack_event_logger_types::per_file_profiling_config;
use crate::hack_event_logger_types::per_file_profiling_config::profile_decling;
use crate::hh_logger;
use crate::path;
use crate::rt::ocaml_filename;
use crate::saved_state_rollouts;
use crate::server_local_config::AgentErrorFormatConfig;
use crate::server_local_config::Quantile;
use crate::server_local_config::T;
use crate::server_local_config::edenfs_file_watcher;
use crate::server_local_config::watchman;
use crate::server_local_config_knobs;
use crate::server_local_config_sandbox_experiment;
use crate::sys_utils;
use crate::sys_utils::SysError;
use crate::yojson;

fn output_config_section(title: &str, output_config: impl FnOnce()) {
    use std::io::Write;
    eprint!("** {}:\n", title);
    let _ = std::io::stderr().flush();
    output_config();
    eprint!("\n");
    let _ = std::io::stderr().flush();
}

fn output_build_and_test_mode() {
    output_config_section("Build and test mode", || {
        eprint!(
            "is_dev_build = {}\nHH_TEST_MODE = {}\nprod_telemetry = {}\n",
            crate::build_id::is_dev_build(),
            match std::env::var_os("HH_TEST_MODE") {
                None => "<unset>".to_string(),
                Some(value) => crate::rt::ocaml_printf::sprintf_s_bytes(value.as_encoded_bytes()),
            },
            sys_utils::prod_telemetry()
        );
    })
}

pub fn default() -> T {
    T {
        saved_state: SavedState::default(),
        min_log_level: hh_logger::level::T::Info,
        attempt_fix_credentials: false,
        log_categories: vec![],
        log_large_fanouts_threshold: None,
        log_init_proc_stack_also_on_absent_from: false,
        art_cli_lite_exit_status_enabled: false,
        log_inference_constraints: false,
        experiments: vec![],
        experiments_config_meta: "".to_string(),
        use_saved_state: false,
        use_saved_state_when_indexing: false,
        require_saved_state: true,
        load_state_natively: false,
        load_state_natively_download_timeout: 60,
        load_state_natively_dirty_files_timeout: 200,
        type_decl_bucket_size: 1000,
        extend_defs_per_file_bucket_size: 2000,
        enable_on_nfs: false,
        enable_fuzzy_search: true,
        max_purgatory_clients: 400,
        search_chunk_size: 0,
        io_priority: 7,
        cpu_priority: 10,
        shm_dirs: vec![
            global_config::SHM_DIR.clone(),
            global_config::TMP_DIR.clone(),
        ],
        shm_use_sharded_hashtbl: false,
        shm_cache_size: -1,
        max_workers: None,
        use_dummy_informant: true,
        edenfs_informant_enabled: false,
        informant_min_distance_restart: 100,
        use_full_fidelity_parser: true,
        interrupt_on_file_changes: false,
        interrupt_on_client: false,
        trace_parsing: false,
        prechecked_files: true,
        enable_global_access_check: false,
        enable_type_check_filter_files: false,
        predeclare_ide: false,
        longlived_workers: false,
        block_client_connections_while_deferring: true,
        hg_aware: false,
        allow_restart_from_precomputed_saved_state: false,
        hg_aware_parsing_restart_threshold: 0,
        hg_aware_redecl_restart_threshold: 0,
        hg_aware_recheck_restart_threshold: 0,
        ide_parser_cache: false,
        store_decls_in_saved_state: false,
        idle_gc_slice: 0,
        populate_member_heaps: true,
        fetch_remote_old_decls: true,
        only_fetch_remote_old_decl_during_init: true,
        remote_old_decl_fetching_include_non_class: false,
        disable_rust_provider_shallow_decl_invalidation: false,
        enable_annotation_agnostic_decl_diffing: false,
        skip_hierarchy_checks: false,
        skip_tast_checks: false,
        silence_errors_under_dynamic: false,
        num_local_workers: None,
        heartbeat_interval: None,
        prefetch_decls_enabled: false,
        prefetch_decls_threshold: 0,
        produce_streaming_errors: true,
        consume_streaming_errors: false,
        use_agent_error_format: AgentErrorFormatConfig::AgentErrorFormatUnconfigured,
        rust_provider_backend: true,
        set_global_provider_backend_in_workers: true,
        isolation_allow_decl_repackaging: false,
        naming_sqlite_path: None,
        enable_naming_table_fallback: false,
        ide_symbolindex_search_provider: "LocalIndex".to_string(),
        symbolindex_quiet: false,
        tico_invalidate_files: false,
        tico_invalidate_smart: false,
        per_file_profiling: per_file_profiling_config::default(),
        memtrace_dir: None,
        go_to_implementation: true,
        allow_unstable_features: false,
        watchman: watchman::default(),
        edenfs_file_watcher: edenfs_file_watcher::default(),
        eden_prefetch_enabled: false,
        eden_prefetch_fanout_threshold: 1000,
        eden_prefetch_workers: 4,
        workload_quantile: None,
        rollout_group: None,
        status_single_use_cached_diagnostics: false,
        specify_manifold_api_key: false,
        cache_remote_decls: false,
        use_compressed_dep_graph: true,
        use_distc: true,
        enable_fanout_aware_distc: false,
        hh_distc_fanout_threshold: 250_000,
        hh_distc_fanout_full_init_threshold: 250_000,
        hh_distc_exponential_backoff_num_retries: 10,
        ide_file_watcher_enabled: false,
        ide_file_watcher_max_changed_files: 1000,
        ide_load_naming_table_on_disk: true,
        ide_naming_table_update_threshold: 1000,
        dump_tast_hashes: false,
        dump_tasts: vec![],
        hack_warnings: true,
        warnings_default_all: false,
        warnings_in_sandcastle: true,
        package_config_strict_validation: false,
        // Fields primarily for hh_conf equivalence testing
        sharedmem_global_size: 0,
        sharedmem_hash_table_pow: 0,
        sharedmem_heap_size: 0,
        eden_fetch_parallelism: 0,
        use_distc_crawl_dircache: false,
        gc_minor_heap_size: 0,
        gc_space_overhead: 0,
        ide_fall_back_to_full_index: false,
        naming_table_compression_level: 0,
        naming_table_compression_threads: 0,
        config_version: None,
        ignored_paths: vec![],
    }
}

/// `$HH_LOCALCONF_PATH/hh.conf`, or the `hh.conf` of the build's
/// `sysconfdir`. Computed once, like OCaml's toplevel value.
pub static SYSTEM_CONFIG_PATH: LazyLock<String> = LazyLock::new(|| {
    let dir = match std::env::var_os("HH_LOCALCONF_PATH") {
        Some(dir) => dir.to_string_lossy().into_owned(),
        None => crate::build_options::system_config_path().to_string(),
    };
    ocaml_filename::concat(&dir, "hh.conf")
});

fn warn_on_invalid_hhconf_keys(config: &config_file_common::T) {
    let config_keys = config_file_common::keys(config);
    for key in config_keys {
        match config_keys::validate_hhconf_key(&key) {
            Ok(()) => {}
            Err(config_keys::DidYouMean(suggestion)) => {
                let msg = match suggestion {
                    None => format!("Unrecognized hh.conf config option: {}", key),
                    Some(s) => format!(
                        "Unrecognized hh.conf config option: {}. Did you mean {}?",
                        key, s
                    ),
                };
                hh_logger::warn(None, None, &msg)
            }
        }
    }
}

/// What `apply_experiments_config_overrides` raises (`Err`) is let through.
fn apply_overrides_in_order<E>(
    silent: bool,
    config: &config_file_common::T,
    overrides: &config_file_common::T,
    apply_justknobs_overrides: impl FnOnce(config_file_common::T) -> config_file_common::T,
    apply_dynamic_overrides: impl FnOnce(config_file_common::T) -> config_file_common::T,
    apply_sandbox_experiment_overrides: impl FnOnce(config_file_common::T) -> config_file_common::T,
    apply_experiments_config_overrides: impl FnOnce(
        config_file_common::T,
    ) -> Result<(String, config_file_common::T), E>,
) -> Result<(String, config_file_common::T), E> {
    // We'll apply CLI overrides now at the start so that the dynamic config
    // sources can be informed about them, e.g. "--config rollout_group=foo" will
    // guide the manner in which JustKnobs picks up values, and
    // "--config use_justknobs=false" will disable it. Don't worry though -- we'll
    // apply CLI overrides again at the end, so they overwrite any changes brought
    // by dynamic config.
    let config = config_file::apply_overrides(config, overrides, None);
    let config = apply_justknobs_overrides(config);
    let config = apply_dynamic_overrides(config);
    let config = apply_sandbox_experiment_overrides(config);
    let (experiments_meta, config) = apply_experiments_config_overrides(config)?;
    // Finally, reapply the CLI overrides, since they should take
    // precedence over dynamic config.
    let config = config_file::apply_overrides(
        &config,
        overrides,
        if !silent { Some("--config") } else { None },
    );
    Ok((experiments_meta, config))
}

/// `module For_test`
pub mod for_test {
    use crate::config_file_common;

    pub fn apply_overrides_in_order(
        silent: bool,
        config: &config_file_common::T,
        overrides: &config_file_common::T,
        apply_justknobs_overrides: impl FnOnce(config_file_common::T) -> config_file_common::T,
        apply_dynamic_overrides: impl FnOnce(config_file_common::T) -> config_file_common::T,
        apply_sandbox_experiment_overrides: impl FnOnce(config_file_common::T) -> config_file_common::T,
        apply_experiments_config_overrides: impl FnOnce(
            config_file_common::T,
        ) -> (String, config_file_common::T),
    ) -> (String, config_file_common::T) {
        match super::apply_overrides_in_order(
            silent,
            config,
            overrides,
            apply_justknobs_overrides,
            apply_dynamic_overrides,
            apply_sandbox_experiment_overrides,
            |config| Ok::<_, std::convert::Infallible>(apply_experiments_config_overrides(config)),
        ) {
            Ok(res) => res,
            Err(e) => match e {},
        }
    }
}

// ~~ `In_channel` ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The lines of `In_channel.read_lines` (`In_channel.input_line
/// ~fix_win_eol:true` until the end): as `Core.String.split_lines`, but a
/// trailing `\r` is removed from every line, the last one too.
fn in_channel_lines(s: &str) -> Vec<String> {
    if s.is_empty() {
        return vec![];
    }
    let s = s.strip_suffix('\n').unwrap_or(s);
    s.split('\n')
        .map(|line| line.strip_suffix('\r').unwrap_or(line).to_string())
        .collect()
}

/// `In_channel.read_lines path`; raises `Sys_error` (the `Err`) when the
/// file cannot be read.
fn in_channel_read_lines(path: &str) -> Result<Vec<String>, SysError> {
    let contents = sys_utils::cat(path)?;
    Ok(in_channel_lines(&String::from_utf8_lossy(&contents)))
}

// ~~ Loading ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Apply the following overrides in order:
///   * JustKnobs
///   * caller-provided dynamic overrides
///   * SandboxExperiment
///   * Legacy experiments config
///   * `overrides`
fn apply_overrides(
    silent: bool,
    current_version: &config_file::Version,
    config: &config_file_common::T,
    from: &str,
    overrides: &config_file_common::T,
    apply_dynamic_overrides_fn: &impl Fn(bool, &config_file_common::T) -> config_file_common::T,
) -> Result<(String, config_file_common::T), SysError> {
    let deterministic_behavior_for_tests = crate::sys_utils::deterministic_behavior_for_tests();
    let apply_justknobs_overrides = |config: config_file_common::T| {
        let use_justknobs = bool_opt(config_keys::hhconf::USE_JUSTKNOBS, &config);
        match (use_justknobs, deterministic_behavior_for_tests) {
            // --config use_justknobs=false (or in hh.conf) will force JK off, regardless of anything else
            (Some(false), _)
            // if use_justknobs isn't set, HH_TEST_MODE=1 (used in tests) will still turn JK off
            | (None, true) => config,
            // --config use_justknobs=true (or in hh.conf) will force JK on, regardless of anything else
            (Some(true), _)
            // if use_justknobs isn't set, then HH_TEST_MODE unset or =0 will leave JK on
            | (None, false) => {
                server_local_config_knobs::apply_justknobs_overrides(silent, config, from)
            }
        }
    };
    let apply_dynamic_overrides = |config: config_file_common::T| {
        if deterministic_behavior_for_tests {
            config
        } else {
            apply_dynamic_overrides_fn(silent, &config)
        }
    };
    let apply_sandbox_experiment_overrides = |config: config_file_common::T| {
        if deterministic_behavior_for_tests {
            config
        } else {
            server_local_config_sandbox_experiment::apply_sandbox_experiment_overrides(
                silent, config,
            )
        }
    };
    let apply_experiments_config_overrides = |config: config_file_common::T| -> Result<_, SysError> {
        let experiments_enabled = bool_if_min_version(
            config_keys::hhconf::EXPERIMENTS_CONFIG_ENABLED,
            false,
            current_version,
            &config,
        );
        if experiments_enabled {
            crate::disk::mkdir_p(&global_config::TMP_DIR);
            let dir = string_(
                config_keys::hhconf::EXPERIMENTS_CONFIG_PATH,
                &global_config::TMP_DIR,
                &config,
            );
            let owner = crate::sys_utils::get_primary_owner()?;
            let file = ocaml_filename::concat(&dir, &format!("hh.{}.experiments", owner));
            let update = bool_if_min_version(
                config_keys::hhconf::EXPERIMENTS_CONFIG_UPDATE,
                false,
                current_version,
                &config,
            );
            let ttl = int_(
                config_keys::hhconf::EXPERIMENTS_CONFIG_TTL_SECONDS,
                86400,
                &config,
            ) as f64;
            let source = string_opt(config_keys::hhconf::EXPERIMENTS_CONFIG_SOURCE, &config);
            let meta = if update {
                match experiments_config_file::update(silent, &file, source.as_deref(), ttl) {
                    Ok(meta) => meta,
                    Err(message) => message,
                }
            } else {
                "Updating experimental config not enabled".to_string()
            };
            if crate::disk::file_exists(&file) {
                // Apply the experiments overrides
                let experiment_overrides = config_file::parse_local_config(&file);
                let config = config_file::apply_overrides(
                    &config,
                    &experiment_overrides,
                    if !silent {
                        Some("Experiment_overrides")
                    } else {
                        None
                    },
                );
                Ok((meta, config))
            } else {
                Ok(("Experimental config not found on disk".to_string(), config))
            }
        } else {
            Ok(("Experimental config not enabled".to_string(), config))
        }
    };
    apply_overrides_in_order(
        silent,
        config,
        overrides,
        apply_justknobs_overrides,
        apply_dynamic_overrides,
        apply_sandbox_experiment_overrides,
        apply_experiments_config_overrides,
    )
}

/// `load_ ?config system_config_path ...`: load configuration flags with the
/// following effective precedence: /etc/hh.conf, JustKnobs,
/// SandboxExperiment, ExperimentsConfig, [overrides]. [overrides] are also
/// applied initially so dynamic configuration sources can observe them, then
/// reapplied at the end to retain final precedence. If not [silent], then
/// prints what it's doing to stderr.
///
/// With `config`, the config is that
/// one (the file is not read and no override is applied). (The parameter
/// `system_config_path` is `config_path`: Rust does not let a parameter
/// shadow a static.)
fn load_(
    config: Option<&config_file_common::T>,
    config_path: &str,
    apply_dynamic_overrides: &impl Fn(bool, &config_file_common::T) -> config_file_common::T,
    silent: bool,
    current_version: &config_file::Version,
    current_rolled_out_flag_idx: isize,
    deactivate_saved_state_rollout: bool,
    from: &str,
    overrides: &config_file_common::T,
) -> Result<T, SysError> {
    if !silent {
        output_build_and_test_mode();
    }
    let default = default();
    let (experiments_config_meta, config) = match config {
        // Config provided directly - skip file read and overrides
        Some(c) => ("".to_string(), c.clone()),
        None => {
            let parsed = config_file::parse_local_config(config_path);
            warn_on_invalid_hhconf_keys(&parsed);
            apply_overrides(
                silent,
                current_version,
                &parsed,
                from,
                overrides,
                apply_dynamic_overrides,
            )?
        }
    };
    if !silent {
        output_config_section("Combined config", || config_file::print_to_stderr(&config));
    }

    let experiments = string_list(
        config_keys::hhconf::EXPERIMENTS,
        default.experiments.clone(),
        &config,
    );

    let log_categories = string_list(
        config_keys::hhconf::LOG_CATEGORIES,
        default.log_categories.clone(),
        &config,
    );
    let log_large_fanouts_threshold =
        int_opt(config_keys::hhconf::LOG_LARGE_FANOUTS_THRESHOLD, &config);
    let log_init_proc_stack_also_on_absent_from = bool_(
        config_keys::hhconf::LOG_INIT_PROC_STACK_ALSO_ON_ABSENT_FROM,
        default.log_init_proc_stack_also_on_absent_from,
        &config,
    );
    let art_cli_lite_exit_status_enabled = bool_(
        config_keys::hhconf::ART_CLI_LITE_EXIT_STATUS_ENABLED,
        default.art_cli_lite_exit_status_enabled,
        &config,
    );
    let log_inference_constraints = bool_(
        config_keys::hhconf::LOG_INFERENCE_CONSTRAINTS,
        default.log_inference_constraints,
        &config,
    );
    let min_log_level = match hh_logger::level::of_enum_string(
        // `String.lowercase` (Core): ASCII only.
        &string_(
            config_keys::hhconf::MIN_LOG_LEVEL,
            &hh_logger::level::to_enum_string(default.min_log_level),
            &config,
        )
        .to_ascii_lowercase(),
    ) {
        Some(level) => level,
        None => hh_logger::level::T::Debug,
    };

    let use_saved_state = bool_if_min_version(
        config_keys::hhconf::USE_MINI_STATE,
        default.use_saved_state,
        current_version,
        &config,
    );
    let use_saved_state_when_indexing = bool_if_min_version(
        config_keys::hhconf::USE_MINI_STATE_WHEN_INDEXING,
        default.use_saved_state_when_indexing,
        current_version,
        &config,
    );
    let require_saved_state = bool_if_min_version(
        config_keys::hhconf::REQUIRE_SAVED_STATE,
        default.require_saved_state,
        current_version,
        &config,
    );
    // The labelled arguments, from the last to the first.
    let force_flag_value = string_opt(config_keys::hhconf::SS_FORCE, &config);
    let saved_state_flags = saved_state_rollouts::make(
        current_rolled_out_flag_idx,
        deactivate_saved_state_rollout,
        |name| bool_(name, false, &config),
        force_flag_value.as_deref(),
    );
    if !silent {
        output_config_section("Saved state rollout flags", || {
            saved_state_rollouts::output(&saved_state_flags)
        });
    }
    let project_metadata_w_flags = bool_(
        config_keys::hhconf::PROJECT_METADATA_W_FLAGS,
        default.saved_state.project_metadata_w_flags,
        &config,
    );
    let attempt_fix_credentials = bool_if_min_version(
        config_keys::hhconf::ATTEMPT_FIX_CREDENTIALS,
        default.attempt_fix_credentials,
        current_version,
        &config,
    );
    let enable_on_nfs = bool_if_min_version(
        config_keys::hhconf::ENABLE_ON_NFS,
        default.enable_on_nfs,
        current_version,
        &config,
    );
    let enable_fuzzy_search = bool_if_min_version(
        config_keys::hhconf::ENABLE_FUZZY_SEARCH,
        default.enable_fuzzy_search,
        current_version,
        &config,
    );
    let enable_global_access_check = bool_(
        config_keys::hhconf::ENABLE_GLOBAL_ACCESS_CHECK,
        default.enable_global_access_check,
        &config,
    );
    let max_purgatory_clients = int_(
        config_keys::hhconf::MAX_PURGATORY_CLIENTS,
        default.max_purgatory_clients,
        &config,
    );
    let search_chunk_size = int_(
        config_keys::hhconf::SEARCH_CHUNK_SIZE,
        default.search_chunk_size,
        &config,
    );
    let load_state_natively = bool_if_min_version(
        config_keys::hhconf::LOAD_STATE_NATIVELY_V4,
        default.load_state_natively,
        current_version,
        &config,
    );
    let load_state_natively_download_timeout = int_(
        config_keys::hhconf::LOAD_STATE_NATIVELY_DOWNLOAD_TIMEOUT,
        default.load_state_natively_download_timeout,
        &config,
    );
    let load_state_natively_dirty_files_timeout = int_(
        config_keys::hhconf::LOAD_STATE_NATIVELY_DIRTY_FILES_TIMEOUT,
        default.load_state_natively_dirty_files_timeout,
        &config,
    );
    let use_dummy_informant = bool_if_min_version(
        config_keys::hhconf::USE_DUMMY_INFORMANT,
        default.use_dummy_informant,
        current_version,
        &config,
    );
    let edenfs_informant_enabled = bool_if_min_version(
        "edenfs_informant_enabled",
        default.edenfs_informant_enabled,
        current_version,
        &config,
    );
    let informant_min_distance_restart = int_(
        config_keys::hhconf::INFORMANT_MIN_DISTANCE_RESTART,
        default.informant_min_distance_restart,
        &config,
    );
    let type_decl_bucket_size = int_(
        config_keys::hhconf::TYPE_DECL_BUCKET_SIZE,
        default.type_decl_bucket_size,
        &config,
    );
    let extend_defs_per_file_bucket_size = int_(
        config_keys::hhconf::EXTEND_DEFS_PER_FILE_BUCKET_SIZE,
        default.extend_defs_per_file_bucket_size,
        &config,
    );
    let io_priority = int_(
        config_keys::hhconf::IO_PRIORITY,
        default.io_priority,
        &config,
    );
    let cpu_priority = int_(
        config_keys::hhconf::CPU_PRIORITY,
        default.cpu_priority,
        &config,
    );
    let shm_dirs = string_list(
        config_keys::hhconf::SHM_DIRS,
        default.shm_dirs.clone(),
        &config,
    )
    .iter()
    .map(|dir| path::to_string(&path::make(dir)))
    .collect::<Vec<_>>();
    let shm_use_sharded_hashtbl = bool_if_min_version(
        config_keys::hhconfig::SHM_USE_SHARDED_HASHTBL,
        default.shm_use_sharded_hashtbl,
        current_version,
        &config,
    );
    let shm_cache_size = int_(
        config_keys::hhconfig::SHM_CACHE_SIZE,
        default.shm_cache_size,
        &config,
    );
    let max_workers = int_opt(config_keys::hhconf::MAX_WORKERS, &config);
    // interrupt_on_watchman is a deprecated alias of interrupt_on_file_changes
    let interrupt_on_file_changes = bool_if_min_version(
        config_keys::hhconf::INTERRUPT_ON_WATCHMAN,
        default.interrupt_on_file_changes,
        current_version,
        &config,
    );
    let interrupt_on_file_changes = bool_if_min_version(
        config_keys::hhconf::INTERRUPT_ON_FILE_CHANGES,
        interrupt_on_file_changes,
        current_version,
        &config,
    );
    let interrupt_on_client = bool_if_min_version(
        config_keys::hhconf::INTERRUPT_ON_CLIENT,
        default.interrupt_on_client,
        current_version,
        &config,
    );
    let use_full_fidelity_parser = bool_if_min_version(
        config_keys::hhconf::USE_FULL_FIDELITY_PARSER,
        default.use_full_fidelity_parser,
        current_version,
        &config,
    );
    let trace_parsing = bool_if_min_version(
        config_keys::hhconf::TRACE_PARSING,
        default.trace_parsing,
        current_version,
        &config,
    );
    let prechecked_files = bool_if_min_version(
        config_keys::hhconf::PRECHECKED_FILES,
        default.prechecked_files,
        current_version,
        &config,
    );
    let enable_type_check_filter_files = bool_if_min_version(
        config_keys::hhconf::ENABLE_TYPE_CHECK_FILTER_FILES,
        default.enable_type_check_filter_files,
        current_version,
        &config,
    );
    let predeclare_ide = bool_if_min_version(
        config_keys::hhconf::PREDECLARE_IDE,
        default.predeclare_ide,
        current_version,
        &config,
    );
    let longlived_workers = bool_if_min_version(
        config_keys::hhconf::LONGLIVED_WORKERS,
        default.longlived_workers,
        current_version,
        &config,
    );
    let block_client_connections_while_deferring = bool_if_min_version(
        config_keys::hhconf::BLOCK_CLIENT_CONNECTIONS_WHILE_DEFERRING,
        default.block_client_connections_while_deferring,
        current_version,
        &config,
    );
    let hg_aware = bool_if_min_version(
        config_keys::hhconf::HG_AWARE,
        default.hg_aware,
        current_version,
        &config,
    );
    let allow_restart_from_precomputed_saved_state = bool_if_min_version(
        config_keys::hhconf::ALLOW_RESTART_FROM_PRECOMPUTED_SAVED_STATE,
        default.allow_restart_from_precomputed_saved_state,
        current_version,
        &config,
    );
    let store_decls_in_saved_state = bool_if_min_version(
        config_keys::hhconf::STORE_DECLS_IN_SAVED_STATE,
        default.store_decls_in_saved_state,
        current_version,
        &config,
    );
    let hg_aware_parsing_restart_threshold = int_(
        config_keys::hhconf::HG_AWARE_PARSING_RESTART_THRESHOLD,
        default.hg_aware_parsing_restart_threshold,
        &config,
    );
    let hg_aware_redecl_restart_threshold = int_(
        config_keys::hhconf::HG_AWARE_REDECL_RESTART_THRESHOLD,
        default.hg_aware_redecl_restart_threshold,
        &config,
    );
    let hg_aware_recheck_restart_threshold = int_(
        config_keys::hhconf::HG_AWARE_RECHECK_RESTART_THRESHOLD,
        default.hg_aware_recheck_restart_threshold,
        &config,
    );
    let ide_parser_cache = bool_if_min_version(
        config_keys::hhconf::IDE_PARSER_CACHE,
        default.ide_parser_cache,
        current_version,
        &config,
    );
    let idle_gc_slice = int_(
        config_keys::hhconf::IDLE_GC_SLICE,
        default.idle_gc_slice,
        &config,
    );
    let populate_member_heaps = bool_if_min_version(
        config_keys::hhconf::POPULATE_MEMBER_HEAPS,
        default.populate_member_heaps,
        current_version,
        &config,
    );
    let fetch_remote_old_decls = bool_if_min_version(
        config_keys::hhconf::FETCH_REMOTE_OLD_DECLS,
        default.fetch_remote_old_decls,
        current_version,
        &config,
    );
    let only_fetch_remote_old_decl_during_init = bool_if_min_version(
        config_keys::hhconf::ONLY_FETCH_REMOTE_OLD_DECL_DURING_INIT,
        default.only_fetch_remote_old_decl_during_init,
        current_version,
        &config,
    );
    let remote_old_decl_fetching_include_non_class = bool_if_min_version(
        config_keys::hhconf::REMOTE_OLD_DECL_FETCHING_INCLUDE_NON_CLASS,
        default.remote_old_decl_fetching_include_non_class,
        current_version,
        &config,
    );
    let disable_rust_provider_shallow_decl_invalidation = bool_if_min_version(
        config_keys::hhconf::DISABLE_RUST_PROVIDER_SHALLOW_DECL_INVALIDATION,
        default.disable_rust_provider_shallow_decl_invalidation,
        current_version,
        &config,
    );
    let enable_annotation_agnostic_decl_diffing = bool_if_min_version(
        config_keys::hhconf::ENABLE_ANNOTATION_AGNOSTIC_DECL_DIFFING,
        default.enable_annotation_agnostic_decl_diffing,
        current_version,
        &config,
    );
    let skip_hierarchy_checks = bool_if_min_version(
        config_keys::hhconf::SKIP_HIERARCHY_CHECKS,
        default.skip_hierarchy_checks,
        current_version,
        &config,
    );
    let skip_tast_checks = bool_if_min_version(
        config_keys::hhconf::SKIP_TAST_CHECKS,
        default.skip_tast_checks,
        current_version,
        &config,
    );
    let silence_errors_under_dynamic = bool_if_min_version(
        config_keys::hhconfig::SILENCE_ERRORS_UNDER_DYNAMIC,
        default.silence_errors_under_dynamic,
        current_version,
        &config,
    );
    let num_local_workers = int_opt(config_keys::hhconf::NUM_LOCAL_WORKERS, &config);
    let heartbeat_interval = int_opt(config_keys::hhconf::HEARTBEAT_INTERVAL, &config);
    let prefetch_decls_enabled = bool_(
        config_keys::hhconf::PREFETCH_DECLS_ENABLED,
        default.prefetch_decls_enabled,
        &config,
    );
    let prefetch_decls_threshold = int_(
        config_keys::hhconf::PREFETCH_DECLS_THRESHOLD,
        default.prefetch_decls_threshold,
        &config,
    );
    let produce_streaming_errors = bool_(
        config_keys::hhconf::PRODUCE_STREAMING_ERRORS,
        default.produce_streaming_errors,
        &config,
    );
    let consume_streaming_errors = bool_(
        config_keys::hhconf::CONSUME_STREAMING_ERRORS,
        default.consume_streaming_errors,
        &config,
    );
    let use_agent_error_format =
        match bool_opt(config_keys::hhconf::USE_AGENT_ERROR_FORMAT, &config) {
            None => AgentErrorFormatConfig::AgentErrorFormatUnconfigured,
            Some(false) => AgentErrorFormatConfig::AgentErrorFormatDisabled,
            Some(true) => AgentErrorFormatConfig::AgentErrorFormatEnabled,
        };
    let watchman = watchman::load(current_version, &default.watchman, &config);
    let edenfs_file_watcher =
        edenfs_file_watcher::load(current_version, &default.edenfs_file_watcher, &config);
    let eden_prefetch_enabled = bool_if_min_version(
        config_keys::hhconf::EDEN_PREFETCH_ENABLED,
        default.eden_prefetch_enabled,
        current_version,
        &config,
    );
    let eden_prefetch_fanout_threshold = int_(
        config_keys::hhconf::EDEN_PREFETCH_FANOUT_THRESHOLD,
        default.eden_prefetch_fanout_threshold,
        &config,
    );
    let eden_prefetch_workers = int_(
        config_keys::hhconf::EDEN_PREFETCH_WORKERS,
        default.eden_prefetch_workers,
        &config,
    );
    let enable_naming_table_fallback = bool_if_min_version(
        config_keys::hhconf::ENABLE_NAMING_TABLE_FALLBACK,
        default.enable_naming_table_fallback,
        current_version,
        &config,
    );
    let naming_sqlite_path = if enable_naming_table_fallback {
        string_opt(config_keys::hhconf::NAMING_SQLITE_PATH, &config)
    } else {
        None
    };
    let ide_symbolindex_search_provider = string_(
        config_keys::hhconf::IDE_SYMBOLINDEX_SEARCH_PROVIDER,
        &default.ide_symbolindex_search_provider,
        &config,
    );
    let symbolindex_quiet = bool_if_min_version(
        config_keys::hhconf::SYMBOLINDEX_QUIET,
        default.symbolindex_quiet,
        current_version,
        &config,
    );
    let tico_invalidate_files = bool_if_min_version(
        config_keys::hhconf::TICO_INVALIDATE_FILES,
        default.tico_invalidate_files,
        current_version,
        &config,
    );
    let tico_invalidate_smart = bool_if_min_version(
        config_keys::hhconf::TICO_INVALIDATE_SMART,
        default.tico_invalidate_smart,
        current_version,
        &config,
    );
    let profiling_default = per_file_profiling_config::default();
    let profile_log = bool_if_min_version(
        config_keys::hhconf::PROFILE_LOG,
        profiling_default.profile_log,
        current_version,
        &config,
    );
    let profile_type_check_duration_threshold = float_(
        config_keys::hhconf::PROFILE_TYPE_CHECK_DURATION_THRESHOLD,
        profiling_default.profile_type_check_duration_threshold,
        &config,
    );
    let profile_type_check_memory_threshold_mb = int_(
        config_keys::hhconf::PROFILE_TYPE_CHECK_MEMORY_THRESHOLD_MB,
        profiling_default.profile_type_check_memory_threshold_mb,
        &config,
    );
    let profile_type_check_twice = bool_if_min_version(
        config_keys::hhconf::PROFILE_TYPE_CHECK_TWICE,
        profiling_default.profile_type_check_twice,
        current_version,
        &config,
    );
    let profile_decling = match string_opt(config_keys::hhconf::PROFILE_DECLING, &config) {
        None => default.per_file_profiling.profile_decling,
        Some(value_s) => match profile_decling::of_config_value(&value_s) {
            Some(x) => x,
            None => panic!(
                "Unrecognized value {} for profile_decling. Allowed values ar 'off', 'top_counts', 'all_telemetry', 'all_telemetry_callstacks'",
                value_s
            ),
        },
    };
    let profile_owner = string_opt(config_keys::hhconf::PROFILE_OWNER, &config);
    let profile_desc = string_opt(config_keys::hhconf::PROFILE_DESC, &config);
    let profile_slow_threshold = float_(
        config_keys::hhconf::PROFILE_SLOW_THRESHOLD,
        profiling_default.profile_slow_threshold,
        &config,
    );
    let memtrace_dir = string_opt(config_keys::hhconf::MEMTRACE_DIR, &config);
    let go_to_implementation = bool_if_min_version(
        config_keys::hhconf::GO_TO_IMPLEMENTATION,
        default.go_to_implementation,
        current_version,
        &config,
    );
    let allow_unstable_features = bool_if_min_version(
        config_keys::hhconf::ALLOW_UNSTABLE_FEATURES,
        default.allow_unstable_features,
        current_version,
        &config,
    );
    let default_saved_state_loading = SavedStateLoading::default();
    let saved_state_max_expected_age_days = {
        let days = int_(
            config_keys::hhconf::SAVED_STATE_MAX_EXPECTED_AGE_DAYS,
            default_saved_state_loading.saved_state_max_expected_age_days,
            &config,
        );
        if days > 0 {
            days
        } else {
            panic!(
                "{} must be positive, got {}",
                config_keys::hhconf::SAVED_STATE_MAX_EXPECTED_AGE_DAYS,
                days
            )
        }
    };
    let use_eden = bool_(
        config_keys::hhconf::SAVED_STATE_LOOKUP_USE_EDEN,
        default_saved_state_loading.use_eden,
        &config,
    );
    let database_shard_name = string_opt(
        config_keys::hhconf::SAVED_STATE_DATABASE_SHARD_NAME,
        &config,
    );
    let use_manifold_cython_client = bool_if_min_version(
        config_keys::hhconf::USE_MANIFOLD_CYTHON_CLIENT,
        default_saved_state_loading.use_manifold_cython_client,
        current_version,
        &config,
    );
    let workload_quantile =
        int_list_opt(config_keys::hhconf::WORKLOAD_QUANTILE, &config).and_then(|l| match l[..] {
            [m, n] => {
                if 0 <= m && m <= n {
                    Some(Quantile { count: n, index: m })
                } else if 0 <= n && n <= m {
                    Some(Quantile { count: m, index: n })
                } else {
                    None
                }
            }
            _ => None,
        });
    let rollout_group = string_opt(config_keys::hhconf::ROLLOUT_GROUP, &config);
    let status_single_use_cached_diagnostics = bool_(
        config_keys::hhconf::STATUS_SINGLE_USE_CACHED_DIAGNOSTICS,
        default.status_single_use_cached_diagnostics,
        &config,
    );
    let specify_manifold_api_key = bool_if_min_version(
        config_keys::hhconf::SPECIFY_MANIFOLD_API_KEY,
        default.specify_manifold_api_key,
        current_version,
        &config,
    );
    let saved_state_manifold_api_key =
        // overriding the local_config value so consumers of saved_state_manifold_api_key
        // don't need to explicitly check for specify_manifold_api_key.
        if specify_manifold_api_key {
            string_opt(config_keys::hhconf::SAVED_STATE_MANIFOLD_API_KEY, &config)
        } else {
            None
        };
    let manifold_local_port = int_opt(
        config_keys::hhconf::SAVED_STATE_MANIFOLD_LOCAL_PORT,
        &config,
    );
    let rust_provider_backend = bool_if_min_version(
        config_keys::hhconf::RUST_PROVIDER_BACKEND,
        default.rust_provider_backend,
        current_version,
        &config,
    );
    let set_global_provider_backend_in_workers = bool_if_min_version(
        config_keys::hhconf::SET_GLOBAL_PROVIDER_BACKEND_IN_WORKERS,
        default.set_global_provider_backend_in_workers,
        current_version,
        &config,
    );
    let isolation_allow_decl_repackaging = bool_if_min_version(
        config_keys::hhconf::ISOLATION_ALLOW_DECL_REPACKAGING,
        default.isolation_allow_decl_repackaging,
        current_version,
        &config,
    );
    let rust_provider_backend = if rust_provider_backend && !shm_use_sharded_hashtbl {
        hh_logger::warn(
            None,
            None,
            "You have rust_provider_backend=true but shm_use_sharded_hashtbl=false. This is incompatible. Turning off rust_provider_backend",
        );
        false
    } else {
        rust_provider_backend
    };
    let rust_provider_backend = if rust_provider_backend && populate_member_heaps {
        hh_logger::warn(
            None,
            None,
            "You have rust_provider_backend=true but populate_member_heaps=true. This is incompatible. Turning off rust_provider_backend",
        );
        false
    } else {
        rust_provider_backend
    };
    let cache_remote_decls = bool_if_min_version(
        config_keys::hhconf::CACHE_REMOTE_DECLS,
        default.cache_remote_decls,
        current_version,
        &config,
    );
    let use_distc = bool_if_min_version(
        config_keys::hhconf::USE_DISTC,
        default.use_distc,
        current_version,
        &config,
    );
    let enable_fanout_aware_distc = bool_if_min_version(
        config_keys::hhconf::ENABLE_FANOUT_AWARE_DISTC,
        default.enable_fanout_aware_distc,
        current_version,
        &config,
    );
    let use_compressed_dep_graph = bool_if_min_version(
        config_keys::hhconf::USE_COMPRESSED_DEP_GRAPH,
        default.use_compressed_dep_graph,
        current_version,
        &config,
    );
    let hh_distc_fanout_threshold = int_(
        config_keys::hhconf::HH_DISTC_FANOUT_THRESHOLD,
        default.hh_distc_fanout_threshold,
        &config,
    );
    let hh_distc_fanout_full_init_threshold = int_(
        config_keys::hhconf::HH_DISTC_FANOUT_FULL_INIT_THRESHOLD,
        default.hh_distc_fanout_full_init_threshold,
        &config,
    );
    let hh_distc_exponential_backoff_num_retries = int_(
        config_keys::hhconfig::HH_DISTC_EXPONENTIAL_BACKOFF_NUM_RETRIES,
        default.hh_distc_exponential_backoff_num_retries,
        &config,
    );
    let ide_file_watcher_enabled = bool_if_min_version(
        config_keys::hhconf::IDE_FILE_WATCHER_ENABLED,
        default.ide_file_watcher_enabled,
        current_version,
        &config,
    );
    let ide_file_watcher_max_changed_files = int_(
        config_keys::hhconf::IDE_FILE_WATCHER_MAX_CHANGED_FILES,
        default.ide_file_watcher_max_changed_files,
        &config,
    );
    let ide_load_naming_table_on_disk = bool_if_min_version(
        config_keys::hhconf::IDE_LOAD_NAMING_TABLE_ON_DISK,
        default.ide_load_naming_table_on_disk,
        current_version,
        &config,
    );
    let ide_naming_table_update_threshold = int_(
        config_keys::hhconf::IDE_NAMING_TABLE_UPDATE_THRESHOLD,
        default.ide_naming_table_update_threshold,
        &config,
    );
    let dump_tast_hashes = bool_(
        config_keys::hhconfig::DUMP_TAST_HASHES,
        default.dump_tast_hashes,
        &config,
    );
    let dump_tasts = {
        let path_opt = string_opt(config_keys::hhconf::DUMP_TASTS, &config);
        match path_opt {
            None => default.dump_tasts.clone(),
            Some(path) => in_channel_read_lines(&path)?,
        }
    };
    let hack_warnings = bool_(
        config_keys::hhconfig::HACK_WARNINGS,
        default.hack_warnings,
        &config,
    );
    let zstd_decompress_by_file = bool_(
        config_keys::hhconf::ZSTD_DECOMPRESS_BY_FILE,
        default_saved_state_loading.zstd_decompress_by_file,
        &config,
    );
    let saved_state_cache_limit = int_(
        config_keys::hhconf::SAVED_STATE_CACHE_LIMIT,
        default_saved_state_loading.saved_state_cache_limit,
        &config,
    );
    let warnings_default_all = bool_(
        config_keys::hhconfig::WARNINGS_DEFAULT_ALL,
        default.warnings_default_all,
        &config,
    );
    let warnings_in_sandcastle = bool_(
        config_keys::hhconfig::WARNINGS_IN_SANDCASTLE,
        default.warnings_in_sandcastle,
        &config,
    );
    let package_config_strict_validation = bool_(
        config_keys::hhconf::PACKAGE_CONFIG_STRICT_VALIDATION,
        default.package_config_strict_validation,
        &config,
    );
    // Fields primarily for hh_conf equivalence testing
    let sharedmem_global_size = int_(
        config_keys::hhconfig::SHAREDMEM_GLOBAL_SIZE,
        default.sharedmem_global_size,
        &config,
    );
    let sharedmem_hash_table_pow = int_(
        config_keys::hhconfig::SHAREDMEM_HASH_TABLE_POW,
        default.sharedmem_hash_table_pow,
        &config,
    );
    let sharedmem_heap_size = int_(
        config_keys::hhconfig::SHAREDMEM_HEAP_SIZE,
        default.sharedmem_heap_size,
        &config,
    );
    let eden_fetch_parallelism = int_(
        config_keys::hhconf::EDEN_FETCH_PARALLELISM,
        default.eden_fetch_parallelism,
        &config,
    );
    let use_distc_crawl_dircache = bool_(
        config_keys::hhconf::USE_DISTC_CRAWL_DIRCACHE,
        default.use_distc_crawl_dircache,
        &config,
    );
    let gc_minor_heap_size = int_(
        config_keys::hhconfig::GC_MINOR_HEAP_SIZE,
        default.gc_minor_heap_size,
        &config,
    );
    let gc_space_overhead = int_(
        config_keys::hhconfig::GC_SPACE_OVERHEAD,
        default.gc_space_overhead,
        &config,
    );
    let ide_fall_back_to_full_index = bool_(
        config_keys::hhconfig::IDE_FALL_BACK_TO_FULL_INDEX,
        default.ide_fall_back_to_full_index,
        &config,
    );
    let naming_table_compression_level = int_(
        config_keys::hhconfig::NAMING_TABLE_COMPRESSION_LEVEL,
        default.naming_table_compression_level,
        &config,
    );
    let naming_table_compression_threads = int_(
        config_keys::hhconfig::NAMING_TABLE_COMPRESSION_THREADS,
        default.naming_table_compression_threads,
        &config,
    );
    let config_version = string_opt(config_keys::hhconfig::VERSION, &config);
    let parse_string_list = |s: &str| -> Vec<String> {
        // `try ... with _ -> []`: a value that is not JSON, and a list with
        // an element that is not a string (`failwith "expected string"`),
        // give `[]`.
        match yojson::safe::from_string(s) {
            Ok(yojson::safe::T::List(l)) => l
                .into_iter()
                .map(|v| match v {
                    yojson::safe::T::String(s) => Some(s),
                    _ => None, // failwith "expected string"
                })
                .collect::<Option<Vec<String>>>()
                .unwrap_or_default(),
            Ok(_) => vec![],
            Err(_) => vec![],
        }
    };
    let ignored_paths = match string_opt(config_keys::hhconfig::IGNORED_PATHS, &config) {
        None => default.ignored_paths.clone(),
        Some(s) => parse_string_list(&s),
    };
    Ok(T {
        saved_state: SavedState {
            loading: SavedStateLoading {
                saved_state_manifold_api_key,
                manifold_local_port,
                use_eden,
                database_shard_name,
                saved_state_max_expected_age_days,
                use_manifold_cython_client,
                zstd_decompress_by_file,
                use_compressed_dep_graph,
                saved_state_cache_limit,
            },
            rollouts: saved_state_flags,
            project_metadata_w_flags,
        },
        min_log_level,
        attempt_fix_credentials,
        log_categories,
        log_large_fanouts_threshold,
        log_init_proc_stack_also_on_absent_from,
        art_cli_lite_exit_status_enabled,
        log_inference_constraints,
        experiments,
        experiments_config_meta,
        use_saved_state,
        use_saved_state_when_indexing,
        require_saved_state,
        load_state_natively,
        load_state_natively_download_timeout,
        load_state_natively_dirty_files_timeout,
        max_purgatory_clients,
        type_decl_bucket_size,
        extend_defs_per_file_bucket_size,
        enable_on_nfs,
        enable_fuzzy_search,
        enable_global_access_check,
        search_chunk_size,
        io_priority,
        cpu_priority,
        shm_dirs,
        shm_use_sharded_hashtbl,
        shm_cache_size,
        max_workers,
        use_dummy_informant,
        edenfs_informant_enabled,
        informant_min_distance_restart,
        use_full_fidelity_parser,
        interrupt_on_file_changes,
        interrupt_on_client,
        trace_parsing,
        prechecked_files,
        enable_type_check_filter_files,
        ide_symbolindex_search_provider,
        predeclare_ide,
        longlived_workers,
        block_client_connections_while_deferring,
        hg_aware,
        allow_restart_from_precomputed_saved_state,
        hg_aware_parsing_restart_threshold,
        hg_aware_redecl_restart_threshold,
        hg_aware_recheck_restart_threshold,
        ide_parser_cache,
        store_decls_in_saved_state,
        idle_gc_slice,
        populate_member_heaps,
        fetch_remote_old_decls,
        only_fetch_remote_old_decl_during_init,
        remote_old_decl_fetching_include_non_class,
        disable_rust_provider_shallow_decl_invalidation,
        enable_annotation_agnostic_decl_diffing,
        skip_hierarchy_checks,
        skip_tast_checks,
        silence_errors_under_dynamic,
        num_local_workers,
        heartbeat_interval,
        prefetch_decls_enabled,
        prefetch_decls_threshold,
        produce_streaming_errors,
        consume_streaming_errors,
        use_agent_error_format,
        rust_provider_backend,
        set_global_provider_backend_in_workers,
        isolation_allow_decl_repackaging,
        naming_sqlite_path,
        enable_naming_table_fallback,
        symbolindex_quiet,
        tico_invalidate_files,
        tico_invalidate_smart,
        per_file_profiling: per_file_profiling_config::T {
            profile_log,
            profile_type_check_duration_threshold,
            profile_type_check_memory_threshold_mb,
            profile_type_check_twice,
            profile_decling,
            profile_owner,
            profile_desc,
            profile_slow_threshold,
        },
        memtrace_dir,
        go_to_implementation,
        allow_unstable_features,
        watchman,
        edenfs_file_watcher,
        eden_prefetch_enabled,
        eden_prefetch_fanout_threshold,
        eden_prefetch_workers,
        workload_quantile,
        rollout_group,
        status_single_use_cached_diagnostics,
        specify_manifold_api_key,
        cache_remote_decls,
        use_compressed_dep_graph,
        use_distc,
        enable_fanout_aware_distc,
        hh_distc_fanout_threshold,
        hh_distc_fanout_full_init_threshold,
        hh_distc_exponential_backoff_num_retries,
        ide_file_watcher_enabled,
        ide_file_watcher_max_changed_files,
        ide_load_naming_table_on_disk,
        ide_naming_table_update_threshold,
        dump_tast_hashes,
        dump_tasts,
        hack_warnings,
        warnings_default_all,
        warnings_in_sandcastle,
        package_config_strict_validation,
        sharedmem_global_size,
        sharedmem_hash_table_pow,
        sharedmem_heap_size,
        eden_fetch_parallelism,
        use_distc_crawl_dircache,
        gc_minor_heap_size,
        gc_space_overhead,
        ide_fall_back_to_full_index,
        naming_table_compression_level,
        naming_table_compression_threads,
        config_version,
        ignored_paths,
    })
}

/// As [load], additionally applying [apply_dynamic_overrides] after JustKnobs
/// and before SandboxExperiment. The callback observes the initially applied
/// [overrides], which are reapplied afterward.
pub fn load_with_dynamic_overrides(
    apply_dynamic_overrides: &impl Fn(bool, &config_file_common::T) -> config_file_common::T,
    silent: bool,
    current_version: &config_file::Version,
    current_rolled_out_flag_idx: isize,
    deactivate_saved_state_rollout: bool,
    from: &str,
    overrides: &config_file_common::T,
) -> Result<T, SysError> {
    load_(
        None,
        &SYSTEM_CONFIG_PATH,
        apply_dynamic_overrides,
        silent,
        current_version,
        current_rolled_out_flag_idx,
        deactivate_saved_state_rollout,
        from,
        overrides,
    )
}

/// Load configuration flags with the following effective precedence:
///   - /etc/hh.conf
///   - JustKnobs
///   - SandboxExperiment
///   - ExperimentsConfig
///   - [overrides]
///
/// [overrides] are also applied initially so dynamic configuration sources can
/// observe them, then reapplied at the end to retain final precedence.
///
/// If not [silent], then prints what it's doing to stderr.
pub fn load(
    silent: bool,
    current_version: &config_file::Version,
    current_rolled_out_flag_idx: isize,
    deactivate_saved_state_rollout: bool,
    from: &str,
    overrides: &config_file_common::T,
) -> Result<T, SysError> {
    load_with_dynamic_overrides(
        &|_silent, config: &config_file_common::T| config.clone(),
        silent,
        current_version,
        current_rolled_out_flag_idx,
        deactivate_saved_state_rollout,
        from,
        overrides,
    )
}

/// Load ServerLocalConfig from already-parsed config contents.
/// This is intended for testing, bypassing file reads and overrides.
/// Now delegates to load_ to avoid code duplication.
pub fn load_from_config(
    silent: bool,
    current_version: &config_file::Version,
    current_rolled_out_flag_idx: isize,
    deactivate_saved_state_rollout: bool,
    config: &config_file_common::T,
) -> Result<T, SysError> {
    load_(
        Some(config),
        "", /* system_config_path unused when config is provided */
        &|_silent, config: &config_file_common::T| config.clone(),
        silent,
        current_version,
        current_rolled_out_flag_idx,
        deactivate_saved_state_rollout,
        "",
        &config_file_common::empty(),
    )
}

pub fn to_rollout_flags(options: &T) -> RolloutFlags {
    RolloutFlags {
        saved_state_lookup_use_eden: options.saved_state.loading.use_eden,
        fetch_remote_old_decls: options.fetch_remote_old_decls,
        only_fetch_remote_old_decl_during_init: options.only_fetch_remote_old_decl_during_init,
        remote_old_decl_fetching_include_non_class: options
            .remote_old_decl_fetching_include_non_class,
        disable_rust_provider_shallow_decl_invalidation: options
            .disable_rust_provider_shallow_decl_invalidation,
        enable_annotation_agnostic_decl_diffing: options.enable_annotation_agnostic_decl_diffing,
        specify_manifold_api_key: options.specify_manifold_api_key,
        populate_member_heaps: options.populate_member_heaps,
        shm_use_sharded_hashtbl: options.shm_use_sharded_hashtbl,
        shm_cache_size: options.shm_cache_size,
        use_manifold_cython_client: options.saved_state.loading.use_manifold_cython_client,
        load_state_natively_v4: options.load_state_natively,
        rust_provider_backend: options.rust_provider_backend,
        set_global_provider_backend_in_workers: options.set_global_provider_backend_in_workers,
        use_distc: options.use_distc,
        enable_fanout_aware_distc: options.enable_fanout_aware_distc,
        use_compressed_dep_graph: options.use_compressed_dep_graph,
        consume_streaming_errors: options.consume_streaming_errors,
        status_single_use_cached_diagnostics: options.status_single_use_cached_diagnostics,
        hh_distc_fanout_threshold: options.hh_distc_fanout_threshold,
        hh_distc_fanout_full_init_threshold: options.hh_distc_fanout_full_init_threshold,
        ide_file_watcher_enabled: options.ide_file_watcher_enabled,
        ide_load_naming_table_on_disk: options.ide_load_naming_table_on_disk,
        ide_naming_table_update_threshold: options.ide_naming_table_update_threshold,
        saved_state_rollouts: options.saved_state.rollouts.clone(),
        zstd_decompress_by_file: options.saved_state.loading.zstd_decompress_by_file,
        warnings_default_all: options.warnings_default_all,
        watchman_enabled: options.watchman.enabled,
        edenfs_file_watcher_enabled: options.edenfs_file_watcher.enabled,
        edenfs_file_watcher_sync_queries_obey_deferral: options
            .edenfs_file_watcher
            .sync_queries_obey_deferral,
        edenfs_file_watcher_state_tracking: options.edenfs_file_watcher.state_tracking,
        edenfs_informant_enabled: options.edenfs_informant_enabled,
        eden_prefetch_enabled: options.eden_prefetch_enabled,
        eden_prefetch_fanout_threshold: options.eden_prefetch_fanout_threshold,
        prefetch_decls_enabled: options.prefetch_decls_enabled,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> config_file::T {
        config_file::parse_contents(s.as_bytes())
    }

    fn version() -> config_file::Version {
        config_file::parse_version(None)
    }

    fn from_config(s: &str) -> T {
        load_from_config(true, &version(), 0, false, &parse(s)).unwrap()
    }

    fn scratch_dir(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "hh_server_local_config_load_{}_{}",
            name,
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn panic_message(e: Box<dyn std::any::Any + Send>) -> String {
        match e.downcast::<String>() {
            Ok(s) => *s,
            Err(e) => e.downcast_ref::<&str>().unwrap().to_string(),
        }
    }

    #[test]
    fn empty_config_is_the_default() {
        // But for rust_provider_backend: its default is true, but loading
        // turns it off (with a warning) because shm_use_sharded_hashtbl is
        // false by default.
        assert!(default().rust_provider_backend);
        assert_eq!(
            from_config(""),
            T {
                rust_provider_backend: false,
                ..default()
            }
        );
        let d = default();
        assert!(d.require_saved_state);
        assert!(!d.use_saved_state);
        assert_eq!(d.shm_dirs.len(), 2);
        assert_eq!(d.saved_state, SavedState::default());
    }

    /// Slack's `hh.conf` (`webapp/hh.conf`): `use_mini_state` is the only
    /// key that has an effect. `lazy_decl`, `lazy_parse` and `lazy_init2` are
    /// not hh.conf keys (they are only warned about), and without
    /// `load_state_natively_v4` or `--with-mini-state` the server does a full
    /// init (`Server_main.resolve_init_approach`).
    #[test]
    fn slack_hh_conf() {
        const SLACK_HH_CONF: &str =
            "use_mini_state = true\nlazy_decl = true\nlazy_parse = true\nlazy_init2 = true";
        let dir = scratch_dir("slack");
        let path = dir.join("hh.conf");
        std::fs::write(&path, SLACK_HH_CONF).unwrap();
        let parsed = config_file::parse_local_config(path.to_str().unwrap());
        assert_eq!(
            config_file::keys(&parsed),
            vec!["lazy_decl", "lazy_init2", "lazy_parse", "use_mini_state"]
        );
        for key in ["lazy_decl", "lazy_init2", "lazy_parse"] {
            assert!(config_keys::validate_hhconf_key(key).is_err());
        }
        let loaded = load_(
            None,
            path.to_str().unwrap(),
            &|_silent, config: &config_file::T| config.clone(),
            true,
            &version(),
            0,
            false,
            "",
            &config_file::empty(),
        )
        .unwrap();
        assert!(loaded.use_saved_state);
        assert!(!loaded.load_state_natively);
        assert!(loaded.require_saved_state);
        assert!(!loaded.watchman.enabled);
        assert_eq!(
            loaded,
            T {
                use_saved_state: true,
                experiments_config_meta: "Experimental config not enabled".to_string(),
                rust_provider_backend: false,
                ..default()
            }
        );
        // `hh_server ROOT` passes no `--with-mini-state`.
        #[cfg(feature = "server")]
        assert!(!crate::server_args::is_using_precomputed_saved_state(
            &crate::server_args::default_options("/")
        ));
    }

    /// `test/config_parsing` (`test_hh_conf_equivalence.ml`): the OCaml
    /// parsing (`Server_config.load_config` and `load_from_config`) and the
    /// Rust `hh_config` crate agree on each config of
    /// `test/config_parsing/configs`, passed as `.hhconfig` with an empty
    /// hh.conf. The OCaml test ran in that directory (`dump_tasts` is
    /// relative to it); here `dump_tasts` is made absolute.
    #[test]
    fn hh_conf_equivalence_with_hh_config() {
        let configs = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../test/config_parsing/configs");
        for name in [
            "bad_hh.conf",
            "complete_hh.conf",
            "empty_hh.conf",
            "real_hh.conf",
        ] {
            let contents = std::fs::read(configs.join(name)).unwrap();
            let mut config = config_file::parse_contents(&contents);
            if let Some(file) = string_opt(config_keys::hhconf::DUMP_TASTS, &config) {
                let abs = configs.join(file).to_str().unwrap().to_string();
                config = config_file::apply_overrides(
                    &config,
                    &config_file::of_list(&[("dump_tasts".to_string(), abs)]),
                    None,
                );
            }
            let opts = crate::server_config::load_config(
                &config,
                &oxidized::global_options::GlobalOptions::default(),
            )
            .unwrap();
            let local_config = load_from_config(true, &version(), 0, false, &config).unwrap();
            let rust = hh_config::HhConfig::from_configs(
                std::path::PathBuf::new(),
                ::config_file::ConfigFile::from_slice(&contents),
                ::config_file::ConfigFile::from_slice(b""),
                Default::default(),
            )
            .unwrap();
            let ocaml = (
                local_config.config_version.clone(),
                local_config.ignored_paths.clone(),
                opts.clone(),
            );
            let ocaml_sizes = (
                local_config.gc_minor_heap_size as usize,
                local_config.gc_space_overhead as usize,
                local_config.sharedmem_global_size as usize,
                local_config.sharedmem_hash_table_pow as usize,
                local_config.sharedmem_heap_size as usize,
                local_config.ide_fall_back_to_full_index,
                opts.hh_distc_should_disable_trace_store,
                local_config.hh_distc_exponential_backoff_num_retries as usize,
                local_config.naming_table_compression_level as usize,
                local_config.naming_table_compression_threads as usize,
                local_config.eden_fetch_parallelism as usize,
                local_config.use_distc_crawl_dircache,
            );
            let rust_sizes = (
                rust.common.gc_minor_heap_size,
                rust.common.gc_space_overhead,
                rust.common.sharedmem_global_size,
                rust.common.sharedmem_hash_table_pow,
                rust.common.sharedmem_heap_size,
                rust.common.ide_fall_back_to_full_index,
                rust.common.hh_distc_should_disable_trace_store,
                rust.common.hh_distc_exponential_backoff_num_retries,
                rust.common.naming_table_compression_level,
                rust.common.naming_table_compression_threads,
                rust.common.eden_fetch_parallelism,
                rust.common.use_distc_crawl_dircache,
            );
            let rust = (rust.common.version, rust.common.ignored_paths, rust.common.opts);
            assert_eq!(ocaml, rust, "{}", name);
            assert_eq!(ocaml_sizes, rust_sizes, "{}", name);
            if name == "complete_hh.conf" {
                assert_eq!(
                    local_config.dump_tasts,
                    vec!["src/main.php", "src/test.php"]
                );
            }
        }
    }

    #[test]
    fn complete_hh_conf() {
        let configs = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../test/config_parsing/configs");
        let mut config =
            config_file::parse_local_config(configs.join("complete_hh.conf").to_str().unwrap());
        config = config_file::apply_overrides(
            &config,
            &config_file::of_list(&[(
                "dump_tasts".to_string(),
                configs
                    .join("dump_tasts_list.txt")
                    .to_str()
                    .unwrap()
                    .to_string(),
            )]),
            None,
        );
        let t = load_from_config(true, &version(), 0, false, &config).unwrap();
        assert_eq!(t.min_log_level, hh_logger::level::T::Debug);
        assert_eq!(
            t.saved_state.loading,
            SavedStateLoading {
                saved_state_manifold_api_key: Some("test_manifold_api_key_12345".to_string()),
                manifold_local_port: None,
                use_eden: false,
                database_shard_name: None,
                saved_state_max_expected_age_days: 7,
                use_manifold_cython_client: true,
                zstd_decompress_by_file: false,
                use_compressed_dep_graph: false,
                saved_state_cache_limit: 5,
            }
        );
        assert!(!t.saved_state.project_metadata_w_flags);
        assert_eq!(t.log_categories, vec!["typing", "decl", "naming"]);
        assert_eq!(t.log_large_fanouts_threshold, Some(500));
        assert!(t.use_saved_state && t.use_saved_state_when_indexing);
        assert!(!t.require_saved_state && t.load_state_natively);
        assert_eq!(t.max_workers, Some(8));
        assert_eq!(t.shm_cache_size, 4294967296);
        // `interrupt_on_watchman` is the default of `interrupt_on_file_changes`.
        assert!(t.interrupt_on_file_changes);
        // shm_use_sharded_hashtbl is true, but populate_member_heaps is false:
        // rust_provider_backend stays on.
        assert!(t.rust_provider_backend);
        assert_eq!(
            t.naming_sqlite_path,
            Some("/path/to/naming.sqlite".to_string())
        );
        assert_eq!(
            t.per_file_profiling,
            per_file_profiling_config::T {
                profile_log: true,
                profile_type_check_duration_threshold: 2.5,
                profile_type_check_memory_threshold_mb: 500,
                profile_type_check_twice: true,
                profile_decling: per_file_profiling_config::ProfileDecling::DeclingAllTelemetry {
                    callstacks: false
                },
                profile_owner: Some("test_owner".to_string()),
                profile_desc: Some("test_description".to_string()),
                profile_slow_threshold: 1.5,
            }
        );
        assert_eq!(
            t.watchman,
            watchman::T {
                enabled: true,
                debug_logging: true,
                init_timeout: 20,
                sockname: Some("/custom/watchman.sock".to_string()),
                subscribe: true,
                synchronous_timeout: 180,
            }
        );
        assert_eq!(
            t.edenfs_file_watcher.tracked_states,
            vec!["hg.update", "hg.transaction", "custom.state"]
        );
        assert_eq!(t.workload_quantile, Some(Quantile { count: 4, index: 2 }));
        assert_eq!(t.rollout_group, Some("test_group".to_string()));
        assert!(!t.use_distc && t.enable_fanout_aware_distc);
        assert_eq!(t.hh_distc_exponential_backoff_num_retries, 3);
        assert!(!t.hack_warnings && t.warnings_default_all && !t.warnings_in_sandcastle);
        // The config is given: no file read, no experiments config.
        assert_eq!(t.experiments_config_meta, "");
        let flags = to_rollout_flags(&t);
        assert!(flags.edenfs_file_watcher_enabled);
        assert!(flags.load_state_natively_v4);
        assert_eq!(flags.shm_cache_size, 4294967296);
    }

    #[test]
    fn values_and_their_rules() {
        // min_log_level is case-insensitive; an unknown level is Debug.
        assert_eq!(
            from_config("min_log_level = WARN").min_log_level,
            hh_logger::level::T::Warn
        );
        assert_eq!(
            from_config("min_log_level = loud").min_log_level,
            hh_logger::level::T::Debug
        );
        // workload_quantile: either order, both non-negative.
        let q = |s: &str| from_config(&format!("workload_quantile = {}", s)).workload_quantile;
        assert_eq!(q("1,3"), Some(Quantile { count: 3, index: 1 }));
        assert_eq!(q("3,1"), Some(Quantile { count: 3, index: 1 }));
        assert_eq!(q("-1,3"), None);
        assert_eq!(q("1,2,3"), None);
        assert_eq!(q("1,x"), None);
        // naming_sqlite_path needs enable_naming_table_fallback.
        assert_eq!(
            from_config("naming_sqlite_path = /n").naming_sqlite_path,
            None
        );
        // rust_provider_backend needs shm_use_sharded_hashtbl and no member heaps.
        assert!(!from_config("rust_provider_backend = true").rust_provider_backend);
        assert!(
            !from_config("shm_use_sharded_hashtbl = true\nrust_provider_backend = true")
                .rust_provider_backend
        );
        assert!(
            from_config(
                "shm_use_sharded_hashtbl = true\npopulate_member_heaps = false\nrust_provider_backend = true"
            )
            .rust_provider_backend
        );
        // interrupt_on_file_changes overrides its deprecated alias.
        assert!(
            !from_config("interrupt_on_watchman = true\ninterrupt_on_file_changes = false")
                .interrupt_on_file_changes
        );
        // ignored_paths is a JSON list of strings; anything else is [].
        let ignored = |s: &str| from_config(&format!("ignored_paths = {}", s)).ignored_paths;
        assert_eq!(ignored(r#"["a", "b\\.php"]"#), vec!["a", "b\\.php"]);
        assert_eq!(ignored(r#"["a", 1]"#), Vec::<String>::new());
        assert_eq!(ignored(r#"{"a": 1}"#), Vec::<String>::new());
        assert_eq!(ignored("not json"), Vec::<String>::new());
        // A saved-state rollout flag being rolled out reads its key.
        assert!(
            from_config("new_naming_table = true")
                .saved_state
                .rollouts
                .new_naming_table
                == false
        );
        let t = load_from_config(
            true,
            &version(),
            7,
            false,
            &parse("new_naming_table = true"),
        )
        .unwrap();
        assert!(t.saved_state.rollouts.new_naming_table);
        assert!(t.saved_state.rollouts.optimized_member_fanout);
        // edenfs_informant_enabled is read with a literal key.
        assert!(from_config("edenfs_informant_enabled = true").edenfs_informant_enabled);
        // shm_dirs go through Path.make.
        let dir = scratch_dir("shm");
        let t = from_config(&format!(
            "shm_dirs = {},/nonexistent/x",
            dir.to_str().unwrap()
        ));
        assert_eq!(
            t.shm_dirs,
            vec![
                path::make(dir.to_str().unwrap()),
                "/nonexistent/x".to_string()
            ]
        );
    }

    #[test]
    fn failures() {
        let e = std::panic::catch_unwind(|| from_config("profile_decling = all")).unwrap_err();
        assert_eq!(
            panic_message(e),
            "Unrecognized value all for profile_decling. Allowed values ar 'off', 'top_counts', 'all_telemetry', 'all_telemetry_callstacks'"
        );
        let e = std::panic::catch_unwind(|| from_config("saved_state_max_expected_age_days = 0"))
            .unwrap_err();
        assert_eq!(
            panic_message(e),
            "saved_state_max_expected_age_days must be positive, got 0"
        );
        let e = std::panic::catch_unwind(|| from_config("io_priority = high")).unwrap_err();
        assert_eq!(
            panic_message(e),
            "Invalid_argument: invalid digit found in string"
        );
        // The first malformed value in the order of the OCaml is the one
        // reported: `experiments` and `log_categories` cannot fail, so
        // `log_large_fanouts_threshold` comes before `io_priority`.
        // (The two values fail with different messages, so the one reported
        // shows which key was read first.)
        let e = std::panic::catch_unwind(|| {
            from_config("io_priority = high\nlog_large_fanouts_threshold = 99999999999999999999999")
        })
        .unwrap_err();
        assert_eq!(
            panic_message(e),
            "Invalid_argument: number too large to fit in target type"
        );
        // `ss_force` is read (and rejected by `Saved_state_rollouts.make`)
        // after `log_inference_constraints` and before
        // `project_metadata_w_flags`.
        let e = std::panic::catch_unwind(|| {
            from_config("log_inference_constraints = maybe\nss_force = bogus")
        })
        .unwrap_err();
        assert_eq!(
            panic_message(e),
            "Invalid_argument: provided string was not `true` or `false`"
        );
        let e = std::panic::catch_unwind(|| {
            from_config("ss_force = bogus\nproject_metadata_w_flags = maybe")
        })
        .unwrap_err();
        assert!(panic_message(e).contains("ForceFlagError(\"bogus\")"));
        let e = load_from_config(
            true,
            &version(),
            0,
            false,
            &parse("dump_tasts = /nonexistent/dump_tasts"),
        )
        .unwrap_err();
        assert_eq!(
            e,
            sys_utils::SysError("/nonexistent/dump_tasts: No such file or directory".to_string())
        );
    }

    #[test]
    fn overrides_in_order() {
        let calls = std::cell::RefCell::new(vec![]);
        let set = |config: config_file::T, step: &str| {
            calls.borrow_mut().push(step.to_string());
            config_file::apply_overrides(
                &config,
                &config_file::of_list(&[("k".to_string(), step.to_string())]),
                None,
            )
        };
        let (meta, config) = for_test::apply_overrides_in_order(
            true,
            &parse("k = file\nother = 1"),
            &config_file::of_list(&[("cli".to_string(), "x".to_string())]),
            |c| {
                // The CLI overrides are applied first, so that this layer
                // sees them.
                assert_eq!(string_opt("cli", &c), Some("x".to_string()));
                set(c, "jk")
            },
            |c| set(c, "dynamic"),
            |c| set(c, "sandbox"),
            |c| ("meta".to_string(), set(c, "experiments")),
        );
        assert_eq!(
            *calls.borrow(),
            vec!["jk", "dynamic", "sandbox", "experiments"]
        );
        assert_eq!(meta, "meta");
        assert_eq!(string_opt("k", &config), Some("experiments".to_string()));
        // The CLI overrides are applied again last: they win.
        let (_, config) = for_test::apply_overrides_in_order(
            true,
            &parse(""),
            &config_file::of_list(&[("k".to_string(), "cli".to_string())]),
            |c| set(c, "jk"),
            |c| set(c, "dynamic"),
            |c| set(c, "sandbox"),
            |c| ("".to_string(), set(c, "experiments")),
        );
        assert_eq!(string_opt("k", &config), Some("cli".to_string()));
    }

    /// `run_override_pipeline` of `test/integration_ml/test_server_config_overrides.ml`.
    fn run_override_pipeline(
        overrides: &config_file::T,
    ) -> (String, String, Vec<(String, String)>) {
        let key = "test_override_precedence";
        let get_value = |config: &config_file::T| string_(key, "missing", config);
        let observed_inputs = std::cell::RefCell::new(vec![]);
        let apply = |source: &str, config: config_file::T| {
            observed_inputs
                .borrow_mut()
                .push((source.to_string(), get_value(&config)));
            config_file::apply_overrides(
                &config,
                &config_file::of_list(&[(key.to_string(), source.to_string())]),
                None,
            )
        };
        let (experiments_meta, config) = for_test::apply_overrides_in_order(
            true,
            &config_file::of_list(&[(key.to_string(), "hh.conf".to_string())]),
            overrides,
            |c| apply("justknobs", c),
            |c| apply("qe", c),
            |c| apply("sandbox_experiment", c),
            |c| ("gatekeeper metadata".to_string(), apply("gatekeeper", c)),
        );
        let final_value = get_value(&config);
        (experiments_meta, final_value, observed_inputs.into_inner())
    }

    fn inputs(l: &[(&str, &str)]) -> Vec<(String, String)> {
        l.iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect()
    }

    /// `test_override_precedence` of `test_server_config_overrides.ml`.
    #[test]
    fn test_override_precedence() {
        let (experiments_meta, final_value, observed_inputs) =
            run_override_pipeline(&config_file::empty());
        assert_eq!(
            observed_inputs,
            inputs(&[
                ("justknobs", "hh.conf"),
                ("qe", "justknobs"),
                ("sandbox_experiment", "qe"),
                ("gatekeeper", "sandbox_experiment"),
            ]),
            "Configuration override sources were applied out of order"
        );
        assert_eq!(
            experiments_meta, "gatekeeper metadata",
            "Experiments metadata was not preserved"
        );
        assert_eq!(
            final_value, "gatekeeper",
            "GateKeeper override did not take precedence"
        );
    }

    /// `test_cli_override_precedence` of `test_server_config_overrides.ml`.
    #[test]
    fn test_cli_override_precedence() {
        let (experiments_meta, final_value, observed_inputs) =
            run_override_pipeline(&config_file::of_list(&[(
                "test_override_precedence".to_string(),
                "cli".to_string(),
            )]));
        assert_eq!(
            observed_inputs,
            inputs(&[
                ("justknobs", "cli"),
                ("qe", "justknobs"),
                ("sandbox_experiment", "qe"),
                ("gatekeeper", "sandbox_experiment"),
            ]),
            "CLI override was not visible before dynamic overrides"
        );
        assert_eq!(
            experiments_meta, "gatekeeper metadata",
            "Experiments metadata was not preserved"
        );
        assert_eq!(
            final_value, "cli",
            "CLI override did not take final precedence"
        );
    }

    #[test]
    fn experiments_config_file() {
        let dir = scratch_dir("experiments");
        let hh_conf = dir.join("hh.conf");
        let load_file = |overrides: &[(&str, &str)]| {
            load_(
                None,
                hh_conf.to_str().unwrap(),
                &|_silent, config: &config_file::T| config.clone(),
                true,
                &version(),
                0,
                false,
                "",
                &config_file::of_list(
                    &overrides
                        .iter()
                        .map(|(k, v)| (k.to_string(), v.to_string()))
                        .collect::<Vec<_>>(),
                ),
            )
            .unwrap()
        };
        std::fs::write(
            &hh_conf,
            format!(
                "experiments_config_enabled = true\nexperiments_config_path = {}\n",
                dir.to_str().unwrap()
            ),
        )
        .unwrap();
        let t = load_file(&[]);
        assert_eq!(
            t.experiments_config_meta,
            "Experimental config not found on disk"
        );
        let owner = crate::sys_utils::get_primary_owner().unwrap();
        std::fs::write(
            dir.join(format!("hh.{}.experiments", owner)),
            "use_mini_state = true\nrollout_group = exp\n",
        )
        .unwrap();
        let t = load_file(&[]);
        assert_eq!(
            t.experiments_config_meta,
            "Updating experimental config not enabled"
        );
        assert!(t.use_saved_state);
        assert_eq!(t.rollout_group, Some("exp".to_string()));
        let t = load_file(&[
            ("experiments_config_update", "true"),
            ("rollout_group", "cli"),
        ]);
        assert_eq!(
            t.experiments_config_meta,
            "Experiments config update: nothing to do"
        );
        // The CLI overrides win over the experiments config.
        assert_eq!(t.rollout_group, Some("cli".to_string()));
        let t = load_file(&[("experiments_config_enabled", "false")]);
        assert_eq!(t.experiments_config_meta, "Experimental config not enabled");
        assert!(!t.use_saved_state);
        // A missing hh.conf is an empty one.
        let t = load_(
            None,
            dir.join("missing.conf").to_str().unwrap(),
            &|_silent, config: &config_file::T| config.clone(),
            true,
            &version(),
            0,
            false,
            "",
            &config_file::empty(),
        )
        .unwrap();
        assert_eq!(
            t,
            T {
                experiments_config_meta: "Experimental config not enabled".to_string(),
                rust_provider_backend: false,
                ..default()
            }
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn sys_utils_helpers() {
        // Core.String.split_lines
        assert_eq!(crate::rt::ocaml_string::split_lines(""), Vec::<String>::new());
        assert_eq!(crate::rt::ocaml_string::split_lines("\n"), vec![""]);
        assert_eq!(crate::rt::ocaml_string::split_lines("a\r\n\nb\n"), vec!["a", "", "b"]);
        assert_eq!(crate::rt::ocaml_string::split_lines("a\n\n"), vec!["a", ""]);
        assert_eq!(crate::rt::ocaml_string::split_lines("a"), vec!["a"]);
        assert_eq!(crate::rt::ocaml_string::split_lines("a\rb\r"), vec!["a\rb\r"]);
        assert_eq!(crate::rt::ocaml_string::split_lines("x\na\r"), vec!["x", "a\r"]);
        // In_channel.read_lines (fix_win_eol): the last line loses its `\r`.
        assert_eq!(in_channel_lines(""), Vec::<String>::new());
        assert_eq!(in_channel_lines("\n"), vec![""]);
        assert_eq!(in_channel_lines("a\r\n\nb\n"), vec!["a", "", "b"]);
        assert_eq!(in_channel_lines("x\na\r"), vec!["x", "a"]);
        assert_eq!(
            crate::sys_utils::exec_try_read("printf 'x\\ny'"),
            Some("x".to_string())
        );
        assert_eq!(crate::sys_utils::exec_try_read("printf 'x'; exit 1"), None);
        assert_eq!(crate::sys_utils::exec_try_read("true"), None);
        assert!(!crate::sys_utils::logname().is_empty());
        assert!(SYSTEM_CONFIG_PATH.ends_with("/hh.conf"));
    }

}
