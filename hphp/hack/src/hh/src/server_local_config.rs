// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server_local_config.ml`. See `hh/PORTING.md`.
//!
//! The record of the hh.conf flags (`t`) and its two sub-records, the
//! watchman and Eden file-watcher settings, with their loaders.
//! `Server_local_config_load` builds `t`.
//!
//! `Hack_event_logger.PerFileProfilingConfig.t` is
//! `crate::hack_event_logger_types::per_file_profiling_config::T`, and
//! `Global_options.saved_state` is `oxidized::global_options::SavedState`.

use oxidized::global_options::SavedState;

use crate::hack_event_logger_types::per_file_profiling_config;
use crate::hh_logger;

/// `module Watchman`
pub mod watchman {
    use crate::config_file::Version;
    use crate::config_file::getters::*;
    use crate::config_file_common;
    use crate::config_keys;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        /// use_watchman
        pub enabled: bool,
        /// in seconds
        pub debug_logging: bool,
        pub init_timeout: isize,
        pub sockname: Option<String>,
        pub subscribe: bool,
        /// in seconds
        pub synchronous_timeout: isize,
    }

    pub fn default() -> T {
        T {
            debug_logging: false,
            enabled: false,
            // buck and hgwatchman use a 10 second timeout, too
            init_timeout: 10,
            sockname: None,
            subscribe: false,
            synchronous_timeout: 120,
        }
    }

    pub fn load(current_version: &Version, default: &T, config: &config_file_common::T) -> T {
        let use_watchman = bool_if_min_version(
            config_keys::hhconf::use_watchman,
            default.enabled,
            current_version,
            config,
        );
        let enabled = bool_if_min_version(
            config_keys::hhconf::watchman_enabled,
            use_watchman,
            current_version,
            config,
        );
        let init_timeout = int_(
            config_keys::hhconf::watchman_init_timeout,
            default.init_timeout,
            config,
        );
        let sockname = string_opt(config_keys::hhconf::watchman_sockname, config);
        let subscribe = bool_if_min_version(
            config_keys::hhconf::watchman_subscribe_v2,
            default.subscribe,
            current_version,
            config,
        );
        let synchronous_timeout = int_(
            config_keys::hhconf::watchman_synchronous_timeout,
            default.synchronous_timeout,
            config,
        );
        let debug_logging = bool_if_min_version(
            config_keys::hhconf::watchman_debug_logging,
            default.debug_logging,
            current_version,
            config,
        );
        T {
            debug_logging,
            enabled,
            init_timeout,
            sockname,
            subscribe,
            synchronous_timeout,
        }
    }
}

/// `module EdenfsFileWatcher`
pub mod edenfs_file_watcher {
    use crate::config_file::Version;
    use crate::config_file::getters::*;
    use crate::config_file_common;
    use crate::config_keys;
    use crate::hg_states;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub enabled: bool,
        pub debug_logging: bool,
        /// Timeout, in seconds
        pub timeout_secs: isize,
        /// If false, ServerNotifier.get_changes_sync backed by Edenfs_watcher will return
        /// file changes even when we are currently deferring changes (e.g. because meerkat is
        /// running).
        pub sync_queries_obey_deferral: bool,
        /// Value of throttle_time_ms parameter passed to Eden's stream_changes_since API.
        /// This means that this is the minimum period (in milliseconds) between each time
        /// Eden will send us a change notification.
        pub throttle_time_ms: isize,
        /// If true, will log additional telemetry collected from within Edenfs_watcher
        pub report_telemetry: bool,
        /// Whether to use Eden's state tracking feature for deferring file changes
        pub state_tracking: bool,
        /// List of state names to track for deferring file changes.
        /// Only used when state_tracking is enabled.
        pub tracked_states: Vec<String>,
    }

    pub fn default() -> T {
        T {
            debug_logging: false,
            enabled: false,
            timeout_secs: 60,
            throttle_time_ms: 50,
            sync_queries_obey_deferral: true,
            report_telemetry: false,
            state_tracking: false,
            tracked_states: vec![
                hg_states::transaction.to_string(),
                hg_states::update.to_string(),
                "meerkat-build".to_string(),
            ],
        }
    }

    pub fn load(current_version: &Version, default: &T, config: &config_file_common::T) -> T {
        let enabled = bool_if_min_version(
            config_keys::hhconf::edenfs_file_watcher_enabled,
            default.enabled,
            current_version,
            config,
        );
        let debug_logging = bool_if_min_version(
            config_keys::hhconf::edenfs_file_watcher_debug_logging,
            default.debug_logging,
            current_version,
            config,
        );
        let timeout_secs = int_(
            config_keys::hhconf::edenfs_file_watcher_timeout_secs,
            default.timeout_secs,
            config,
        );
        let sync_queries_obey_deferral = bool_if_min_version(
            config_keys::hhconf::edenfs_file_watcher_sync_queries_obey_deferral,
            default.sync_queries_obey_deferral,
            current_version,
            config,
        );
        let throttle_time_ms = int_(
            config_keys::hhconf::edenfs_file_watcher_throttle_time_ms,
            default.throttle_time_ms,
            config,
        );
        let report_telemetry = bool_(
            config_keys::hhconf::edenfs_file_watcher_report_telemetry,
            default.report_telemetry,
            config,
        );
        let state_tracking = bool_(
            config_keys::hhconf::edenfs_file_watcher_state_tracking,
            default.state_tracking,
            config,
        );
        let tracked_states = string_list(
            config_keys::hhconf::edenfs_file_watcher_tracked_states,
            default.tracked_states.clone(),
            config,
        );
        T {
            debug_logging,
            enabled,
            timeout_secs,
            sync_queries_obey_deferral,
            throttle_time_ms,
            report_telemetry,
            state_tracking,
            tracked_states,
        }
    }
}

/// Allows to typecheck only a certain quantile of the workload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Quantile {
    /// The number of quantiles we want.
    /// If this is n, we'll divide the workload in n groups.
    pub count: isize,
    /// The index of the subgroup we'll process.
    /// If this is i, we'll typecheck group number i out of the n groups.
    /// this should be in interval [0; n]
    pub index: isize,
}

/// These are the flags loaded from the following sources:
///   - /etc/hh.conf
///   - overridden by Knobs
///   - overridden by ExperimentsConfig
///   - overridden by CLI --config flags
#[derive(Clone, Debug, PartialEq)]
pub struct T {
    pub saved_state: SavedState,
    pub min_log_level: hh_logger::level::T,
    /// Indicates whether we attempt to fix the credentials if they're broken
    pub attempt_fix_credentials: bool,
    pub log_categories: Vec<String>,
    /// If a fanout is greater than this value, log stats about that fanout.
    pub log_large_fanouts_threshold: Option<isize>,
    /// A few select events like to log the init_proc_stack, but it's voluminous!
    /// The default behavior is to log init_proc_stack only when "--from" is absent.
    /// This flag lets us log it also when "--from" is present.
    pub log_init_proc_stack_also_on_absent_from: bool,
    /// log type inference constraints into HackEventLogger
    pub log_inference_constraints: bool,
    /// the list of experiments from the experiments config
    pub experiments: Vec<String>,
    /// a free-form diagnostic string
    pub experiments_config_meta: String,
    /// should we attempt to load saved-state? (subject to further options)
    pub use_saved_state: bool,
    /// should we attempt to load saved-state when running glean indexing?
    pub use_saved_state_when_indexing: bool,
    /// if attempting saved-state, should we fail upon failure?
    pub require_saved_state: bool,
    /// make hh_server query and download saved state.
    pub load_state_natively: bool,
    /// in seconds
    pub load_state_natively_download_timeout: isize,
    /// in seconds
    pub load_state_natively_dirty_files_timeout: isize,
    pub type_decl_bucket_size: isize,
    pub extend_defs_per_file_bucket_size: isize,
    pub enable_on_nfs: bool,
    pub enable_fuzzy_search: bool,
    /// Monitor: Limit the number of clients that can sit in purgatory waiting
    /// for a server to be started because we don't want this to grow unbounded.
    pub max_purgatory_clients: isize,
    pub search_chunk_size: isize,
    pub io_priority: isize,
    pub cpu_priority: isize,
    pub shm_dirs: Vec<String>,
    pub shm_use_sharded_hashtbl: bool,
    /// Maximum shared memory cache size for evictable data.
    ///
    /// If this is set to a negative value, eviction is disabled.
    pub shm_cache_size: isize,
    pub max_workers: Option<isize>,
    /// See Informant.
    pub use_dummy_informant: bool,
    /// If true, the Informant uses Edenfs_watcher instead of Watchman
    pub edenfs_informant_enabled: bool,
    pub informant_min_distance_restart: isize,
    pub use_full_fidelity_parser: bool,
    /// Whether to interrupt an active type-checking job as soon as any relevant files change.
    /// Deprecated alias: interrupt_on_watchman
    pub interrupt_on_file_changes: bool,
    pub interrupt_on_client: bool,
    pub trace_parsing: bool,
    /// Whether we use the prechecked algorithm, which only includes the fanout of
    /// changes since the mergebase when initializing
    pub prechecked_files: bool,
    /// run global access checker to check global writes and reads
    pub enable_global_access_check: bool,
    /// Let the user configure which files to type check and
    /// which files to ignore. This flag is not expected to be
    /// rolled out broadly, rather it is meant to be used by
    /// power users only.
    pub enable_type_check_filter_files: bool,
    /// Selects a search provider for autocomplete and symbol search
    pub ide_symbolindex_search_provider: String,
    pub predeclare_ide: bool,
    pub longlived_workers: bool,
    /// Block client admission while Eden defers file changes. Hg states only
    /// block when [hg_aware] is also enabled.
    pub block_client_connections_while_deferring: bool,
    pub hg_aware: bool,
    pub hg_aware_parsing_restart_threshold: isize,
    pub hg_aware_redecl_restart_threshold: isize,
    pub hg_aware_recheck_restart_threshold: isize,
    pub ide_parser_cache: bool,
    /// When enabled, save hot class declarations (for now, specified in a special
    /// file in the repository) when generating a saved state.
    pub store_decls_in_saved_state: bool,
    /// Size of Gc.major_slice to be performed when server is idle. 0 to disable
    pub idle_gc_slice: isize,
    /// Populate the member signature heaps.
    ///
    /// If disabled, instead load lazily from shallow classes.
    pub populate_member_heaps: bool,
    /// Option to fetch old decls from remote decl store
    pub fetch_remote_old_decls: bool,
    /// Restrict remote old decl fetches to init-time fanout.
    pub only_fetch_remote_old_decl_during_init: bool,
    /// Preserve Rust shallow decls when invalidating folded decls.
    pub disable_rust_provider_shallow_decl_invalidation: bool,
    /// Ignore user-defined class attributes when computing fanout.
    pub enable_annotation_agnostic_decl_diffing: bool,
    /// Skip checks on hierarchy e.g. overrides, require extend, etc.
    /// Set to true only for debugging purposes!
    pub skip_hierarchy_checks: bool,
    /// Skip checks implemented using TAST visitors.
    /// Set to true only for debugging purposes!
    pub skip_tast_checks: bool,
    /// Do not report errors under the dynamic pass of the typechecker
    pub silence_errors_under_dynamic: bool,
    /// If None, only the type check delegate's logic will be used.
    /// If the delegate fails to type check, the typing check service as a whole
    /// will fail.
    pub num_local_workers: Option<isize>,
    /// If set, periodically log which file is being type-checked, every this many seconds
    pub heartbeat_interval: Option<isize>,
    /// If true, prefetch class declarations in parallel before type-checking files
    /// with many class references.
    pub prefetch_decls_enabled: bool,
    /// Minimum number of class name references in a file to trigger parallel decl prefetching.
    pub prefetch_decls_threshold: isize,
    /// whether hh_server should write errors to errors.bin file
    pub produce_streaming_errors: bool,
    /// whether hh_client should read errors from errors.bin file
    pub consume_streaming_errors: bool,
    /// Use Provider_backend.Rust_provider_backend as the global provider
    /// backend, servicing File_provider, Naming_provider, and Decl_provider
    /// using the hackrs implementation.
    pub rust_provider_backend: bool,
    /// Enables the reverse naming table to fall back to SQLite for queries.
    pub naming_sqlite_path: Option<String>,
    pub enable_naming_table_fallback: bool,
    pub symbolindex_quiet: bool,
    /// Allows hh_server to invalidate units in hhvm based on local changes
    pub tico_invalidate_files: bool,
    /// Use finer grain hh_server dependencies
    pub tico_invalidate_smart: bool,
    /// turns on memtrace .ctf writes to this directory
    pub per_file_profiling: per_file_profiling_config::T,
    pub memtrace_dir: Option<String>,
    /// Allows the IDE to show the 'find all implementations' button
    pub go_to_implementation: bool,
    /// Allows unstable features to be enabled within a file via the '__EnableUnstableFeatures' attribute
    pub allow_unstable_features: bool,
    pub watchman: watchman::T,
    pub edenfs_file_watcher: edenfs_file_watcher::T,
    /// Allows to typecheck only a certain quantile of the workload.
    pub workload_quantile: Option<Quantile>,
    /// A string from hh.conf, written to HackEventLogger telemetry. Before it got
    /// into here, [t], it was first used as a lookup in ServerLocalConfigKnobs.
    /// Intended meaning: what class of user is running hh_server, hence what experiments
    /// should they be subject to.
    pub rollout_group: Option<String>,
    /// Reuse already-computed global diagnostics for hh --single when the server
    /// has completed typechecking.
    pub status_single_use_cached_diagnostics: bool,
    pub specify_manifold_api_key: bool,
    /// Configure whether fetch and cache remote decls
    pub cache_remote_decls: bool,
    /// Whether a Distc_failed server exit is treated as non-retryable.
    pub abort_on_distc_failure: bool,
    /// use remote type-checking (hh_distc) rather than only local type-checking
    pub use_distc: bool,
    /// use fanout-aware remote type-checking (hh_distc)
    pub enable_fanout_aware_distc: bool,
    /// fanout threshold where we trigger hh_distc
    pub hh_distc_fanout_threshold: isize,
    /// fanout threshold above which full-init hh_distc is triggered
    pub hh_distc_fanout_full_init_threshold: isize,
    pub hh_distc_exponential_backoff_num_retries: isize,
    /// POC: @nzthomas - allow ClientIdeDaemon to grab any naming table from disk before trying Watchman / Manifold
    pub ide_load_naming_table_on_disk: bool,
    /// POC: @nzthomas, if clientIDEDaemon is loading a naming table from disk instead of Manifold, set a globalrev distance threshold
    pub ide_naming_table_update_threshold: isize,
    /// Dump tast hashes into /tmp/hh_server/tast_hashes
    pub dump_tast_hashes: bool,
    /// List of files whose TASTs to be dumped in /tmp/hh_server/tasts.
    pub dump_tasts: Vec<String>,
    /// POC: @bobren, use new fancy compressed dep graph that is 25% the size of the old one
    pub use_compressed_dep_graph: bool,
    /// POC: @catg - turn on hack warnings.
    pub hack_warnings: bool,
    /// If true, `hh` is equivalent to `hh -Wall`, i.e. warnings are shown.
    /// Otherwise, `hh` is equivalent to `hh -Wnone`, i.e. warnings are not shown.
    pub warnings_default_all: bool,
    pub warnings_in_sandcastle: bool,
    /// POC: @fzn, if true, `hh` fatals if paths specified in PACAKGES.toml `include_paths` do not exists
    pub package_config_strict_validation: bool,
    // Fields below are primarily for hh_conf equivalence testing
    /// sharedmem_global_size config key
    pub sharedmem_global_size: isize,
    /// sharedmem_hash_table_pow config key
    pub sharedmem_hash_table_pow: isize,
    /// sharedmem_heap_size config key
    pub sharedmem_heap_size: isize,
    /// eden_fetch_parallelism config key
    pub eden_fetch_parallelism: isize,
    /// use_distc_crawl_dircache config key
    pub use_distc_crawl_dircache: bool,
    /// gc_minor_heap_size config key
    pub gc_minor_heap_size: isize,
    /// gc_space_overhead config key
    pub gc_space_overhead: isize,
    /// ide_fall_back_to_full_index config key
    pub ide_fall_back_to_full_index: bool,
    /// naming_table_compression_level config key
    pub naming_table_compression_level: isize,
    /// naming_table_compression_threads config key
    pub naming_table_compression_threads: isize,
    /// version config key - renamed to avoid shadowing
    pub config_version: Option<String>,
    /// ignored_paths config key, parsed from JSON
    pub ignored_paths: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config_file;
    use crate::config_file_version;

    fn config(s: &str) -> config_file::T {
        config_file::parse_contents(s.as_bytes())
    }

    fn version(major: isize, minor: isize, build: isize) -> config_file::Version {
        config_file::Version::VersionComponents(config_file_version::VersionComponents {
            major,
            minor,
            build,
        })
    }

    #[test]
    fn watchman_defaults_and_aliases() {
        let v = version(4, 0, 0);
        let d = watchman::default();
        assert_eq!(watchman::load(&v, &d, &config("")), d);
        // `use_watchman` is the default of `watchman_enabled`.
        let w = watchman::load(&v, &d, &config("use_watchman = true"));
        assert!(w.enabled);
        let w = watchman::load(
            &v,
            &d,
            &config("use_watchman = true\nwatchman_enabled = false"),
        );
        assert!(!w.enabled);
        // Versions: enabled from 3.0.0 on, not from 5.0.0 on.
        assert!(watchman::load(&v, &d, &config("use_watchman = ^3.0.0")).enabled);
        assert!(!watchman::load(&v, &d, &config("use_watchman = ^5.0.0")).enabled);
        let w = watchman::load(
            &v,
            &d,
            &config(
                "watchman_init_timeout = 20\nwatchman_sockname = /s\nwatchman_subscribe_v2 = true\nwatchman_synchronous_timeout = 180\nwatchman_debug_logging = true",
            ),
        );
        assert_eq!(
            w,
            watchman::T {
                enabled: false,
                debug_logging: true,
                init_timeout: 20,
                sockname: Some("/s".to_string()),
                subscribe: true,
                synchronous_timeout: 180,
            }
        );
    }

    #[test]
    fn edenfs_file_watcher_defaults() {
        let v = version(4, 0, 0);
        let d = edenfs_file_watcher::default();
        assert_eq!(
            d.tracked_states,
            vec!["hg.transaction", "hg.update", "meerkat-build"]
        );
        assert_eq!(edenfs_file_watcher::load(&v, &d, &config("")), d);
        let e = edenfs_file_watcher::load(
            &v,
            &d,
            &config(
                "edenfs_file_watcher_enabled = true\nedenfs_file_watcher_tracked_states = a,b\nedenfs_file_watcher_throttle_time_ms = 7",
            ),
        );
        assert!(e.enabled);
        assert_eq!(e.tracked_states, vec!["a", "b"]);
        assert_eq!(e.throttle_time_ms, 7);
    }

    #[test]
    #[should_panic(expected = "Invalid_argument")]
    fn edenfs_file_watcher_bad_bool() {
        let v = version(4, 0, 0);
        edenfs_file_watcher::load(
            &v,
            &edenfs_file_watcher::default(),
            &config("edenfs_file_watcher_report_telemetry = maybe"),
        );
    }
}
