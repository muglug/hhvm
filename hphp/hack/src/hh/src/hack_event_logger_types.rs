// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `logging/hack_event_logger_types.ml`. See `hh/PORTING.md`.
//!
//! `Hack_event_logger` includes this module (`include
//! Hack_event_logger_types`), so OCaml writes these types
//! `Hack_event_logger.PerFileProfilingConfig.t` and
//! `Hack_event_logger.rollout_flags`. `crate::hack_event_logger` (the stub
//! of the typing port) does not re-export them yet; use them from here.

/// `module PerFileProfilingConfig`
pub mod per_file_profiling_config {
    /// `profile_decling`
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum ProfileDecling {
        DeclingOff,
        DeclingTopCounts,
        DeclingAllTelemetry { callstacks: bool },
    }

    /// `module ProfileDecling`
    pub mod profile_decling {
        use super::ProfileDecling;

        pub type T = ProfileDecling;

        pub fn of_config_value(s: &str) -> Option<T> {
            match s {
                "off" => Some(ProfileDecling::DeclingOff),
                "top_counts" => Some(ProfileDecling::DeclingTopCounts),
                "all_telemetry" => Some(ProfileDecling::DeclingAllTelemetry { callstacks: false }),
                "all_telemetry_callstacks" => {
                    Some(ProfileDecling::DeclingAllTelemetry { callstacks: true })
                }
                _ => None,
            }
        }

        pub fn to_config_value(t: T) -> String {
            match t {
                ProfileDecling::DeclingOff => "off".to_string(),
                ProfileDecling::DeclingTopCounts => "top_counts".to_string(),
                ProfileDecling::DeclingAllTelemetry { callstacks } => format!(
                    "all_telemetry{}",
                    if callstacks { "_callstacks" } else { "" }
                ),
            }
        }

        pub fn of_int(i: isize) -> T {
            match i {
                0 => ProfileDecling::DeclingOff,
                1 => ProfileDecling::DeclingTopCounts,
                2 => ProfileDecling::DeclingAllTelemetry { callstacks: false },
                _ => ProfileDecling::DeclingAllTelemetry { callstacks: true },
            }
        }

        pub fn config_value_of_int(i: isize) -> String {
            to_config_value(of_int(i))
        }
    }

    /// `PerFileProfilingConfig.t`
    #[derive(Clone, Debug, PartialEq)]
    pub struct T {
        pub profile_log: bool,
        pub profile_type_check_duration_threshold: f64,
        pub profile_type_check_memory_threshold_mb: isize,
        pub profile_type_check_twice: bool,
        pub profile_decling: ProfileDecling,
        pub profile_owner: Option<String>,
        pub profile_desc: Option<String>,
        pub profile_slow_threshold: f64,
    }

    pub fn default() -> T {
        T {
            profile_log: false,
            profile_type_check_duration_threshold: 0.05, /* seconds */
            profile_type_check_memory_threshold_mb: 100,
            profile_type_check_twice: false,
            profile_decling: ProfileDecling::DeclingOff,
            profile_owner: None,
            profile_desc: None,
            // `Float.max_value` (Base): infinity.
            profile_slow_threshold: f64::INFINITY,
        }
    }
}

/// `rollout_flags`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RolloutFlags {
    /// POC: @nzthomas. Collects the age of a saved state (in seconds)
    /// and distance (in globalrevs) for telemetry
    /// Whether to use Eden rather than Watchman to look up saved states.
    pub saved_state_lookup_use_eden: bool,
    /// POC: @bobren - Fetching old decls remotely to reduce fanout
    pub fetch_remote_old_decls: bool,
    /// POC: @mojpc2, whether remote old decl fetches are restricted to init
    pub only_fetch_remote_old_decl_during_init: bool,
    /// POC: @mojpc2, preserve Rust shallow decls when invalidating folded decls
    pub disable_rust_provider_shallow_decl_invalidation: bool,
    /// Whether user-defined class attributes are ignored when computing fanout.
    pub enable_annotation_agnostic_decl_diffing: bool,
    /// POC: @nzthomas, whether the API key in hh.conf should be used for saved state downloads
    pub specify_manifold_api_key: bool,
    /// POC: @hverr, disable writing signatures to method/property heaps.
    pub populate_member_heaps: bool,
    /// POC: @hverr, new shared memory backend.
    pub shm_use_sharded_hashtbl: bool,
    /// POC: @hverr, evictability cache size, -1 if evictability disabled
    pub shm_cache_size: isize,
    /// POC: @nzthomas, Required for Hedwig support for saved state downloads
    pub use_manifold_cython_client: bool,
    /// POC: @jakebailey, started Dec 2022.
    /// Use Provider_backend.Rust_provider_backend as the global provider
    /// backend, servicing File_provider, Naming_provider, and Decl_provider
    /// queries using the hackrs implementation.
    pub rust_provider_backend: bool,
    /// POC: @bobren, use hh_distc instead of hulk for remote typechecking
    pub use_distc: bool,
    /// POC: @fzn, use fanout-aware hh_distc if hh_distc_fanout_threshold <= fanout < hh_distc_fanout_full_init_threshold
    pub enable_fanout_aware_distc: bool,
    /// POC: @ljw, hh_client should read errors from errors.bin
    pub consume_streaming_errors: bool,
    /// Whether hh --single may reuse cached server diagnostics.
    pub status_single_use_cached_diagnostics: bool,
    /// POC: @bobren - fanout threshold where we trigger hh_distc
    pub hh_distc_fanout_threshold: isize,
    /// POC: @fzn - fanout threshold where we trigger fanout-aware hh_distc
    pub hh_distc_fanout_full_init_threshold: isize,
    /// POC: @nzthomas - allow ClientIdeDaemon to grab any naming table from disk before trying Watchman / Manifold
    pub ide_load_naming_table_on_disk: bool,
    /// POC: @nzthomas, if clientIDEDaemon is loading a naming table from disk instead of Manifold, set a globalrev distance threshold
    pub ide_naming_table_update_threshold: isize,
    /// POC: @bobren, use new fancy compressed dep graph that is 25% the size of the old one
    pub use_compressed_dep_graph: bool,
    /// POC: @bobren, whether to allow hh_server to fetch saved state (thus overriding load_state_natively setting on Sandcastle)
    pub load_state_natively_v4: bool,
    pub saved_state_rollouts: crate::saved_state_rollouts::T,
    /// POC: @nzthomas, if true then saved state loading will only pass specific files to zstd shellout
    pub zstd_decompress_by_file: bool,
    /// POC: @catg - whether the client shows warnings by default.
    pub warnings_default_all: bool,
    /// POC: @frankemrich - if true, use Edenfs_watcher to power ServerNotifier (= file watching in server)
    pub edenfs_file_watcher_enabled: bool,
    /// POC: @frankemrich -  If false, ServerNotifier.get_changes_sync backed by Edenfs_watcher will return
    /// file changes even when we are currently deferring changes (e.g. because meerkat is running).
    pub edenfs_file_watcher_sync_queries_obey_deferral: bool,
    /// POC: @frankemrich - Whether to use Eden's state tracking API
    pub edenfs_file_watcher_state_tracking: bool,
    /// POC: @frankemrich - If true, use Eden backend for InformantNotifier (= file watching in monitor process)
    pub edenfs_informant_enabled: bool,
    /// POC: @izorin - If true, prefetch class declarations in parallel before type-checking files with many class references
    pub prefetch_decls_enabled: bool,
}

#[cfg(test)]
mod tests {
    use super::per_file_profiling_config::profile_decling::*;
    use super::per_file_profiling_config::*;

    #[test]
    fn profile_decling_config_values() {
        for s in [
            "off",
            "top_counts",
            "all_telemetry",
            "all_telemetry_callstacks",
        ] {
            assert_eq!(to_config_value(of_config_value(s).unwrap()), s);
        }
        assert_eq!(of_config_value("all"), None);
        assert_eq!(config_value_of_int(0), "off");
        assert_eq!(config_value_of_int(9), "all_telemetry_callstacks");
        assert_eq!(default().profile_slow_threshold, f64::INFINITY);
    }
}
