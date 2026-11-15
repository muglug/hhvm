// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `monitor/informant.ml` (the `Resigned` path; the `Active`
//! revision tracker is not ported).
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
//! revisions: not ported. Where the OCaml would make it, this one logs that
//! it is not ported and resigns. Of its `Revision_tracker`, only the decision
//! on a transition is (`revision_tracker::form_decision` and what it needs).

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
    /// Whether the first server is started with a precomputed saved-state.
    pub initial_saved_state_is_precomputed: bool,
    /// Allow restarting with the precomputed state and changed-file list discarded.
    pub allow_restart_from_precomputed_saved_state: bool,
}

pub type InitEnv = Options;

/// `Revision_tracker`: the decision it takes on a transition. The tracker
/// itself (its `instance`, the `Revision_map` of hg queries, the queue of
/// state changes) belongs to the `Active` informant, which is not ported.
pub mod revision_tracker {
    use super::Report;
    use super::ServerState;
    use crate::hh_logger;
    use crate::informant_notifier::RepoTransition;
    use crate::path;

    /// `init_settings`, without its `notifier: Informant_notifier.t` (not
    /// ported).
    #[derive(Clone, Debug)]
    pub struct InitSettings {
        pub root: path::T,
        pub min_distance_restart: isize,
        pub initial_saved_state_is_precomputed: bool,
        pub allow_restart_from_precomputed_saved_state: bool,
    }

    /// The fields of `env` that the decision reads; `rev_map`,
    /// `state_changes` and the hg state flags are not ported.
    #[derive(Clone, Debug)]
    pub struct Env {
        pub inits: InitSettings,
        /// The 'current' base revision (from the tracker's perspective of the
        /// repo. This is used to make calculations on distance. This is changed
        /// when a State_leave is handled.
        pub current_base_revision: crate::hg::GlobalRev,
    }

    pub fn get_jump_distance(global_rev: crate::hg::GlobalRev, env: &Env) -> isize {
        (global_rev - env.current_base_revision).abs()
    }

    pub fn is_significant(min_distance_restart: isize, jump_distance: isize, elapsed_t: f64) -> bool {
        hh_logger::log(&format!(
            "Informant: jump distance {}. elapsed_t: {:.6}",
            jump_distance, elapsed_t
        ));
        // Allow up to 2 revisions per second for incremental. More than that,
        // prefer a server restart.
        jump_distance > min_distance_restart
            && (elapsed_t <= 0.0 || jump_distance as f64 / elapsed_t > 2.0)
    }

    /// Form a decision about whether or not we'd like to start a new server.
    /// transition: The state transition for which we are forming a decision
    /// global_rev: The corresponding global rev for this transition's hg rev.
    pub fn form_decision(
        significant: bool,
        transition: &RepoTransition,
        server_state: ServerState,
        env: &Env,
    ) -> Report {
        match (significant, transition, server_state) {
            (_, RepoTransition::StateLeave(_), ServerState::ServerNotYetStarted) => {
                // This is reachable when server stopped in the middle of rebase. Instead
                // of restarting immediately, we go back to Server_not_yet_started, and want
                // to restart only when hg.update state is vacated
                Report::RestartServer
            }
            (_, RepoTransition::StateLeave(_), ServerState::ServerDead) => {
                // Regardless of whether we had a significant change or not, when the
                // server is not alive, we restart it on a state leave.
                Report::RestartServer
            }
            (false, _, _) => {
                hh_logger::log("Informant insignificant transition");
                Report::MoveAlong
            }
            (true, RepoTransition::StateEnter(_), _) | (true, RepoTransition::StateLeave(_), _) => {
                // We use the State enter and leave events to kick off asynchronous
                // computations off the hg revisions when they arrive (during preprocess)
                // But actual actions are taken only on changed_merge_base below.
                Report::MoveAlong
            }
            (true, RepoTransition::ChangedMergeBase(_), _)
            | (true, RepoTransition::ChangedCommit(_), _) => {
                // When using a precomputed saved-state, we only restart if explicitly
                // allowed to. Note that [initial_saved_state_is_precomputed] does not tell
                // us whether the *current* server used a precomputed saved state.
                // But it doesn't matter: If we already restarted the server before, then
                // [allow_restart_from_precomputed_saved_state] must be true anyway.
                if env.inits.initial_saved_state_is_precomputed
                    && !env.inits.allow_restart_from_precomputed_saved_state
                {
                    hh_logger::log(
                        "Server was started using a precomputed saved-state, not restarting.",
                    );
                    Report::MoveAlong
                } else {
                    Report::RestartServer
                }
            }
        }
    }
}

pub fn init(options: &InitEnv) -> T {
    let Options {
        root: _,
        allow_subscriptions,
        use_dummy,
        min_distance_restart: _,
        watchman_debug_logging: _,
        use_eden: _,
        ignore_hh_version: _,
        initial_saved_state_is_precomputed: _,
        allow_restart_from_precomputed_saved_state: _,
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
        // not ported.
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
        // `Revision_tracker.make_report`: not ported; no informant
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

    #[test]
    fn form_decision_precomputed_saved_state() {
        use crate::informant_notifier::RepoTransition;
        use revision_tracker::*;
        let env = |precomputed, allow| Env {
            inits: InitSettings {
                root: "/".to_string(),
                min_distance_restart: 100,
                initial_saved_state_is_precomputed: precomputed,
                allow_restart_from_precomputed_saved_state: allow,
            },
            current_base_revision: 0,
        };
        let mb = RepoTransition::ChangedMergeBase("abc".to_string());
        let commit = RepoTransition::ChangedCommit("abc".to_string());
        for t in [&mb, &commit] {
            let alive = ServerState::ServerAlive;
            assert_eq!(form_decision(true, t, alive, &env(false, false)), Report::RestartServer);
            assert_eq!(form_decision(true, t, alive, &env(true, false)), Report::MoveAlong);
            assert_eq!(form_decision(true, t, alive, &env(true, true)), Report::RestartServer);
            assert_eq!(form_decision(true, t, alive, &env(false, true)), Report::RestartServer);
            assert_eq!(form_decision(false, t, alive, &env(false, false)), Report::MoveAlong);
        }
        let leave = RepoTransition::StateLeave("abc".to_string());
        let e = env(true, false);
        assert_eq!(
            form_decision(false, &leave, ServerState::ServerDead, &e),
            Report::RestartServer
        );
        assert_eq!(
            form_decision(false, &leave, ServerState::ServerNotYetStarted, &e),
            Report::RestartServer
        );
        assert_eq!(form_decision(true, &leave, ServerState::ServerAlive, &e), Report::MoveAlong);
        let enter = RepoTransition::StateEnter("abc".to_string());
        assert_eq!(form_decision(true, &enter, ServerState::ServerDead, &e), Report::MoveAlong);
    }

    #[test]
    fn significance() {
        use revision_tracker::*;
        assert!(!is_significant(100, 100, 0.0));
        assert!(is_significant(100, 101, 0.0));
        assert!(is_significant(100, 101, 50.0));
        assert!(!is_significant(100, 101, 51.0));
        let env = Env {
            inits: InitSettings {
                root: "/".to_string(),
                min_distance_restart: 100,
                initial_saved_state_is_precomputed: false,
                allow_restart_from_precomputed_saved_state: false,
            },
            current_base_revision: 50,
        };
        assert_eq!(get_jump_distance(20, &env), 30);
        assert_eq!(get_jump_distance(80, &env), 30);
    }
}
