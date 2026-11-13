// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/informant.ml` (the `Resigned` path; the `Active`
//! revision tracker is P2-INF's, after MON).
//!
//! Owned by **MON** (plan §3.1), then **P2-INF** (plan §7.3).
//!
//! The informant collects information to tell the monitor when to
//! intelligently kill and restart the server daemon.
//!
//! For example: An informant may want to watch the repo state and tell
//! the monitor to restart the server when a significant change in
//! repo revision occurs since a fresh initialization could be faster
//! than an incremental type check.
//!
//! The `Active` informant (`use_dummy_informant = false`, Watchman
//! subscriptions on, an `Informant_notifier` that starts) tracks hg
//! revisions: not ported yet (P2-INF). Where the OCaml would make it, this
//! one logs that it is not ported and resigns (plan §3.4).

use crate::hh_logger;
use crate::path;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Report {
    /// Nothing to see here.
    MoveAlong,
    /// Kill the server (if one is running) and start a new one.
    RestartServer,
}

/// `show_report` (`[@@deriving show]`)
pub fn show_report(r: Report) -> &'static str {
    match r {
        Report::MoveAlong => "Informant.Move_along",
        Report::RestartServer => "Informant.Restart_server",
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ServerState {
    ServerNotYetStarted,
    ServerAlive,
    ServerDead,
}

/// `show_server_state` (`[@@deriving show]`)
pub fn show_server_state(s: ServerState) -> &'static str {
    match s {
        ServerState::ServerNotYetStarted => "Informant.Server_not_yet_started",
        ServerState::ServerAlive => "Informant.Server_alive",
        ServerState::ServerDead => "Informant.Server_dead",
    }
}

#[derive(Debug)]
pub enum T {
    /// Informant is active.
    Active(()),
    /// We don't want to use the informant.
    Resigned,
}

#[derive(Clone, Debug)]
pub struct Options {
    pub root: path::T,
    /// Disable the informant - use the dummy instead.
    pub allow_subscriptions: bool,
    /// Don't trigger a server restart if the distance between two
    /// revisions we are moving between is less than this.
    pub use_dummy: bool,
    pub min_distance_restart: isize,
    pub watchman_debug_logging: bool,
    /// If true, the informant uses Edenfs_watcher instead of Watchman.
    pub use_eden: bool,
    /// Informant should ignore the hh_version when doing version checks.
    pub ignore_hh_version: bool,
    /// Was the server initialized with a precomputed saved-state?
    pub is_saved_state_precomputed: bool,
}

pub type InitEnv = Options;

pub fn init(options: &InitEnv) -> T {
    let Options {
        root: _,
        allow_subscriptions,
        use_dummy,
        min_distance_restart: _,
        watchman_debug_logging: _,
        use_eden: _,
        ignore_hh_version: _,
        is_saved_state_precomputed: _,
    } = options;
    if *use_dummy {
        eprint!("Informant using dummy - resigning\n");
        T::Resigned
    }
    // Active informant requires Watchman subscriptions.
    else if !*allow_subscriptions {
        eprint!("Not using subscriptions - Informant resigning\n");
        T::Resigned
    } else {
        // `Informant_notifier.init ~use_eden ~watchman_debug_logging root`,
        // then `Active { revision_tracker = Revision_tracker.init ... }`:
        // not ported (P2-INF).
        hh_logger::log("informant not ported, resigning");
        T::Resigned
    }
}

/// Same as init, except it preserves internal Revision_map cache.
/// This is used when server decides to restart itself due to rebase - we don't
/// want Informant to then restart the server again. Reinitializing will discard
/// the pending queue of state changes, and issue new query for base revision,
/// in order to "synchronize" base revision understanding between server and
/// monitor.
pub fn reinit(t: &T) {
    match t {
        T::Resigned => {}
        T::Active(()) => {
            hh_logger::log("Reinitializing Informant");
        }
    }
}

pub fn should_start_first_server(_t: &T) -> bool {
    true
}

pub fn should_ignore_hh_version(init_env: &InitEnv) -> bool {
    init_env.ignore_hh_version
}

/// Returns true if the informant is actually running and will
/// manage server lifetime.
pub fn is_managing(t: &T) -> bool {
    match t {
        T::Resigned => false,
        T::Active(_) => true,
    }
}

pub fn report(informant: &T, server_state: ServerState) -> Report {
    match (informant, server_state) {
        (T::Resigned, ServerState::ServerNotYetStarted) => {
            // Actually, this case should never happen. But we force a restart
            // to avoid accidental wedged states anyway.
            hh_logger::log(
                "Unexpected Resigned informant without a server started, restarting server",
            );
            Report::RestartServer
        }
        (T::Resigned, _) => Report::MoveAlong,
        // `Revision_tracker.make_report`: not ported (P2-INF); no informant
        // is ever `Active` here.
        (T::Active(()), _) => Report::MoveAlong,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resigned() {
        let t = T::Resigned;
        assert_eq!(report(&t, ServerState::ServerNotYetStarted), Report::RestartServer);
        assert_eq!(report(&t, ServerState::ServerAlive), Report::MoveAlong);
        assert_eq!(report(&t, ServerState::ServerDead), Report::MoveAlong);
        assert!(!is_managing(&t));
        assert!(should_start_first_server(&t));
    }
}
