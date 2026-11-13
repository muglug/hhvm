// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server_notifier.ml`. See `hh/PORTING.md`.
//!
//! The backends are those of the design (section 7.6): `Dfind` is the native
//! watcher of `crate::rt::notifier_native` (the `notify` crate, the default),
//! `Watchman` that of `crate::rt::notifier_watchman` (when `use_watchman` /
//! `watchman_enabled`), `IndexOnly` is for `--check`. The decisions are the
//! OCaml's: which backend `init` picks and what it logs, what each function
//! returns for each backend, the timeouts and the exit codes.
//!
//! - The Eden watcher is Meta-only: in the open-source build its `init`
//!   (`stubs/edenfs_watcher.ml`) fails with `Failure "not implemented"`, so
//!   `try_init_edenfs_watcher` panics with that message, as OCaml raises it,
//!   and no `EdenfsFileWatcher` notifier can exist. The functions that only
//!   such a notifier uses (`handle_edenfs_watcher_result`,
//!   `eden_add_oldest_change_age_telemetry`,
//!   `convert_edenfs_watcher_changes`) and its branches are not here.
//! - `Server_revision_tracker` is Meta-only (it follows hg's mergebase; the
//!   design marks it M): its calls are left out of
//!   `convert_watchman_changes`. `files_changed` does nothing until
//!   `initialize` is called with an hg global revision (from a Meta saved
//!   state). The state handlers only matter with `hg_aware = true` (false by
//!   default): they track `hg.update`/`hg.transaction` for `is_hg_updating`
//!   (which nothing outside the tracker reads), and on leaving `hg.update` log
//!   "ServerRevisionTracker: leaving hg.update" and query hg for the global
//!   revision of the new commit. That line and those queries are lost.
//! - `notification_fd` is the file descriptor of the Watchman connection,
//!   to `poll`/`select` on (never to read from), as in OCaml.
//!
//! A notifier is meant to be used from one thread at a time, as OCaml uses
//! it; the instance of a Watchman notifier is behind a mutex.
//!
//! The exceptions that `Server_main` and `Server_utils.exit_on_exception`
//! catch, those of `Watchman` (`Timeout`, `Watchman_error`,
//! `Watchman_restarted`, ...) and `Exit_status.Exit_with`, are the
//! `notifier_watchman::Exn` that the functions here return
//! (`Exn::ExitWith` for `Exit_with`). The `failwith`s (and the `Failure
//! "not implemented"` of the Eden watcher) are panics.

use std::os::fd::RawFd;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use crate::bucket;
use crate::exit;
use crate::exit_status;
use crate::files_to_ignore;
use crate::find;
use crate::hack_event_logger;
use crate::hh_logger;
use crate::path;
use crate::rt::notifier_native as dfind_lib;
use crate::rt::notifier_watchman as watchman;
use crate::rt::ocaml_unix;
use crate::s_set;
use crate::server_args;
use crate::server_files;
use crate::server_local_config;
use crate::sys_utils;
use crate::telemetry;

/// `changes`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Changes {
    /// e.g. because DFind is not available, or watchman subscription is down
    Unavailable,
    /// contains all changes up to the point that the notifier was invoked
    SyncChanges(s_set::T),
    /// contains some of the changes up to the point that the notifier was invoked,
    /// but there may be more pending changes that have not been included
    AsyncChanges(s_set::T),
}

/// `type clock = Server_notifier_types.clock = Watchman of Watchman.clock |
/// Eden of Edenfs_watcher.clock [@@deriving show, eq]`
pub use crate::server_notifier_types::Clock;
pub use crate::server_notifier_types::equal_clock;
pub use crate::server_notifier_types::pp_clock;
pub use crate::server_notifier_types::show_clock;

/// Prints the name of the file watcher used to create the clock.
pub fn show_file_watcher_name(clock: &Clock) -> String {
    match clock {
        Clock::Watchman(_) => "Watchman",
        Clock::Eden(_) => "Edenfs_watcher",
    }
    .to_string()
}

/// `t`. Cheap to clone: the clones share their backend.
#[derive(Clone)]
pub enum T {
    IndexOnly {
        root: path::T,
    },
    Dfind {
        root: path::T,
        ready: Arc<AtomicBool>,
        dfind: Arc<dfind_lib::T>,
    },
    Watchman {
        wenv: watchman::Env,
        /// Watchman state can change during requests (see Watchamn.Watchman_dead and Watchman_alive).
        /// This reference will be updated as necessary to the new instance.
        watchman: Arc<Mutex<watchman::WatchmanInstance>>,
        root: path::T,
        local_config: Arc<server_local_config::T>,
        num_workers: isize,
    },
    MockChanges {
        get_changes_async: Arc<dyn Fn() -> Changes + Send + Sync>,
        get_changes_sync: Arc<dyn Fn() -> s_set::T + Send + Sync>,
    },
}

/// The filter an [`Indexer`] is given: `string -> bool`.
pub type Filter = Box<dyn Fn(&str) -> bool + Send + Sync>;

/// What an [`Indexer`] gives: `unit -> string list`, the next files each
/// time, `[]` when there are no more.
pub type Next = Box<dyn FnMut() -> Vec<String> + Send>;

/// This takes a filter, and returns all files under root that match
/// (`type indexer = (string -> bool) -> unit -> string list`; what it raises
/// is the `Err`).
pub type Indexer = Box<dyn Fn(Filter) -> Result<Next, watchman::Exn> + Send + Sync>;

fn lock<A>(m: &Mutex<A>) -> MutexGuard<'_, A> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

/// This returns an "indexer", i.e. unit -> string list, which when invoked
/// will return all files under root.
pub fn indexer(t: &T, filter: Filter) -> Result<Next, watchman::Exn> {
    Ok(match t {
        T::Dfind { root, .. } | T::IndexOnly { root } => {
            find::make_next_files(None, Some("root"), Some(filter), None, root)
        }
        T::MockChanges { .. } => panic!("indexer not mocked"),
        T::Watchman {
            wenv, num_workers, ..
        } => {
            let files = watchman::get_all_files(wenv)?;
            bucket::make_list(
                *num_workers,
                None,
                None,
                files.into_iter().filter(|f| filter(f)).collect(),
            )
        }
    })
}

/// `Daemon.fd_of_path`: the file, created or truncated, read-write, with mode
/// 0o666 under umask 0o111 (its directory exists: `make_link_of_timestamped`
/// made it).
fn daemon_fd_of_path(path: &str) -> std::io::Result<std::fs::File> {
    use crate::rt::ocaml_unix::OpenFlag;
    ocaml_unix::openfile_with_umask(
        path,
        &[OpenFlag::ORdwr, OpenFlag::OCreat, OpenFlag::OTrunc],
        0o666,
        0o111,
    )
}

pub fn init(
    options: &server_args::Options,
    local_config: &server_local_config::T,
    num_workers: isize,
) -> Result<(T, Indexer), watchman::Exn> {
    let root = server_args::root(options);
    let watchman_config = &local_config.watchman;
    let watchman_enabled = watchman_config.enabled;
    let edenfs_watcher_config = &local_config.edenfs_file_watcher;
    let edenfs_watcher_enabled = edenfs_watcher_config.enabled;

    let init_dfind = || {
        hh_logger::log("Using dfind");
        let log_link = server_files::dfind_log(&root);
        let log_file = match sys_utils::make_link_of_timestamped(&log_link) {
            Ok(log_file) => log_file,
            Err(e) => panic!(
                "{}",
                ocaml_unix::unix_error_to_string(&e, "symlink", &log_link)
            ),
        };
        let log_fd = match daemon_fd_of_path(&log_file) {
            Ok(log_fd) => log_fd,
            Err(e) => panic!(
                "{}",
                ocaml_unix::unix_error_to_string(&e, "open", &log_file)
            ),
        };
        let dfind = dfind_lib::init(log_fd, std::slice::from_ref(&root));
        hack_event_logger::set_file_watcher_dfind();
        T::Dfind {
            root: root.clone(),
            ready: Arc::new(AtomicBool::new(false)),
            dfind: Arc::new(dfind),
        }
    };

    // helper to try to construct Watchman, or return None if failed
    let try_init_watchman = || -> Result<Option<T>, watchman::Exn> {
        hh_logger::log("Using watchman");
        let server_local_config::watchman::T {
            sockname,
            subscribe,
            init_timeout,
            debug_logging,
            ..
        } = watchman_config;

        let wenv = watchman::init(
            None,
            &watchman::InitSettings {
                init_timeout: watchman::TimeoutSetting::ExplicitTimeout(*init_timeout as f64),
                subscribe_mode: if *subscribe {
                    Some(watchman::SubscribeMode::DeferChanges)
                } else {
                    None
                },
                expression_terms: files_to_ignore::watchman_server_expression_terms(),
                debug_logging: server_args::watchman_debug_logging(options) || *debug_logging,
                sockname: sockname.clone(),
                subscription_prefix: "hh_type_check_watcher".to_string(),
                roots: vec![root.clone()],
            },
        )?;
        Ok(wenv.map(|wenv| {
            hack_event_logger::set_file_watcher_watchman();
            T::Watchman {
                watchman: Arc::new(Mutex::new(watchman::WatchmanInstance::WatchmanAlive(
                    wenv.clone(),
                ))),
                wenv,
                root: root.clone(),
                local_config: Arc::new(local_config.clone()),
                num_workers,
            }
        }))
    };

    let try_init_edenfs_watcher = || -> Option<T> {
        hh_logger::log("Using EdenFS file watcher");
        let _watch_spec = files_to_ignore::server_watch_spec();
        let server_local_config::edenfs_file_watcher::T {
            state_tracking,
            tracked_states,
            ..
        } = &local_config.edenfs_file_watcher;
        // If state tracking and hg_aware are both enabled, verify that tracked_states
        // includes the hg states.
        if *state_tracking && local_config.hg_aware {
            if !(tracked_states
                .iter()
                .any(|s| s == crate::hg_states::transaction)
                && tracked_states.iter().any(|s| s == crate::hg_states::update))
            {
                panic!(
                    "state_tracking and hg_aware are enabled, but not tracking hg.update and hg.transaction"
                )
            }
        }
        // `Edenfs_watcher.init init_settings`: the open-source stub
        // (`stubs/edenfs_watcher.ml`) begins with `require_test_stubbing ()`,
        // which raises `Failure "not implemented"` outside the tests.
        panic!("not implemented")
    };

    if edenfs_watcher_enabled && watchman_enabled {
        hh_logger::warn(
            None,
            None,
            "Both Watchman and EdenFS file watching enabled in server config, will prefer the latter",
        );
    }

    // The lazy values of OCaml: each is forced at most once below.
    let notifier = if server_args::check_mode(options) {
        // check_mode
        hh_logger::log("Not using any file watching mechanism");
        T::IndexOnly { root: root.clone() }
    } else if let Some(notifier) = if edenfs_watcher_enabled {
        try_init_edenfs_watcher()
    } else {
        None
    } {
        notifier
    } else if let Some(notifier) = if watchman_enabled {
        try_init_watchman()?
    } else {
        None
    } {
        notifier
    } else {
        init_dfind()
    };

    let indexer_notifier = notifier.clone();
    let notifier_indexer: Indexer = Box::new(move |filter| indexer(&indexer_notifier, filter));
    Ok((notifier, notifier_indexer))
}

pub fn init_mock(
    get_changes_async: impl Fn() -> Changes + Send + Sync + 'static,
    get_changes_sync: impl Fn() -> s_set::T + Send + Sync + 'static,
) -> T {
    T::MockChanges {
        get_changes_async: Arc::new(get_changes_async),
        get_changes_sync: Arc::new(get_changes_sync),
    }
}

pub fn init_null() -> T {
    let f = || Changes::SyncChanges(s_set::T::new());
    let g = s_set::T::new;
    init_mock(f, g)
}

pub fn wait_until_ready(t: &T) {
    match t {
        T::Dfind { ready, dfind, .. } => {
            if ready.load(Ordering::SeqCst) {
            } else {
                // `Dfind_lib.wait_until_ready` reads the `Ready` message of
                // dfind; it raises `End_of_file` if dfind died first.
                if dfind_lib::wait_until_ready(dfind).is_err() {
                    panic!("End_of_file")
                }
                ready.store(true, Ordering::SeqCst)
            }
        }
        T::IndexOnly { .. } => {}
        T::MockChanges { .. } => {}
        T::Watchman { .. } => {
            // The initial watch-project command blocks until watchman's crawl is
            // done, so we don't have anything else to wait for here.
        }
    }
}

/// Helper conversion function, from a single watchman-changes to a set of changed
/// files. Also handles informing ServerRevisionTracker about changes
pub fn convert_watchman_changes(
    _root: &path::T,
    local_config: &server_local_config::T,
    watchman_changes: watchman::PushedChanges,
) -> Result<s_set::T, watchman::Exn> {
    Ok(match watchman_changes {
        watchman::PushedChanges::ChangedMergeBase(..) => {
            hh_logger::log("Error: Typechecker does not use Source Control Aware mode");
            return Err(watchman::Exn::ExitWith(exit_status::T::WatchmanInvalidResult));
        }
        watchman::PushedChanges::StateEnter(_name, _metadata) => {
            if local_config.hg_aware {
                // `Server_revision_tracker.Watchman.on_state_enter name`:
                // Meta-only, left out (see the module documentation).
            }
            s_set::T::new()
        }
        watchman::PushedChanges::StateLeave(_name, _metadata) => {
            if local_config.hg_aware {
                // `Server_revision_tracker.Watchman.on_state_leave root name
                // metadata`: Meta-only, left out.
            }
            s_set::T::new()
        }
        watchman::PushedChanges::FilesChanged(changes) => {
            // `Server_revision_tracker.files_changed local_config
            // (S_set.cardinal changes)`: Meta-only, left out.
            changes
        }
    })
}

/// Returns all changes up to the point this was invoked, represented as a set
/// of changed files. This will raise an exception if the file watching service
/// is unavailable
pub fn get_changes_sync(
    t: &T,
    telemetry: telemetry::T,
) -> Result<(s_set::T, Option<Clock>, telemetry::T), watchman::Exn> {
    let (changes, new_clock, telemetry) = match t {
        T::IndexOnly { .. } => (s_set::T::new(), None, telemetry),
        T::MockChanges {
            get_changes_sync, ..
        } => (get_changes_sync(), None, telemetry),
        T::Dfind { dfind, .. } => {
            // `Timeout.with_timeout ~timeout:120 ~on_timeout:(Exit.exit
            // Dfind_unresponsive)`, and `Dfind_died` on any exception.
            let set = match dfind_lib::get_changes(dfind, std::time::Duration::from_secs(120)) {
                Ok(set) => set,
                Err(dfind_lib::GetChangesError::Timeout) => {
                    exit::exit(None, None, None, exit_status::T::DfindUnresponsive)
                }
                Err(dfind_lib::GetChangesError::Died(_)) => {
                    exit::exit(None, None, None, exit_status::T::DfindDied)
                }
            };
            (set, None, telemetry)
        }
        T::Watchman {
            local_config,
            watchman,
            root,
            ..
        } => {
            let start_time = ocaml_unix::gettimeofday();
            let mut instance = lock(watchman);
            let (watchman_, changes) = watchman::get_changes_synchronously(
                local_config.watchman.synchronous_timeout,
                instance.clone(),
            )?;
            let telemetry =
                telemetry::add_duration(Some("sync_watcher"), start_time, None, telemetry);
            *instance = watchman_;
            let mut acc = s_set::T::new();
            for c in changes {
                acc = acc.union(convert_watchman_changes(root, local_config, c)?);
            }
            let clock = watchman::get_clock(&instance);
            (acc, Some(Clock::Watchman(clock)), telemetry)
        }
    };

    if hh_logger::level::passes_min_level(hh_logger::level::T::Debug) && !changes.is_empty() {
        hh_logger::log_with(
            Some(hh_logger::level::T::Debug),
            None,
            &format!(
                "ServerNotifier.get_changes_sync got {} changes",
                changes.len()
            ),
        );
        for file in changes.iter() {
            hh_logger::log_with(
                Some(hh_logger::level::T::Debug),
                None,
                &format!("ServerNotifier.get_changes_sync: changed file {}", file),
            );
        }
    }
    Ok((changes, new_clock, telemetry))
}

/// This might return AsyncChanges the ones that we happen to have received by now,
/// or SyncChanges, depending on the underlying notifier's state
pub fn get_changes_async(
    t: &T,
    telemetry: telemetry::T,
) -> Result<(Changes, Option<Clock>, telemetry::T), watchman::Exn> {
    let (changes, new_clock, telemetry) = match t {
        T::IndexOnly { .. } => (Changes::SyncChanges(s_set::T::new()), None, telemetry),
        T::MockChanges {
            get_changes_async, ..
        } => (get_changes_async(), None, telemetry),
        T::Dfind { .. } => {
            let (changes, _, telemetry) = get_changes_sync(t, telemetry)?;
            (Changes::SyncChanges(changes), None, telemetry)
        }
        T::Watchman {
            watchman,
            root,
            local_config,
            ..
        } => {
            let start_time = ocaml_unix::gettimeofday();
            let mut instance = lock(watchman);
            let (watchman_, changes) = watchman::get_changes(None, instance.clone())?;
            let telemetry =
                telemetry::add_duration(Some("async_watcher"), start_time, None, telemetry);
            *instance = watchman_;
            let changes =
                match changes {
                    watchman::Changes::WatchmanUnavailable => Changes::Unavailable,
                    watchman::Changes::WatchmanPushed(changes) => Changes::AsyncChanges(
                        convert_watchman_changes(root, local_config, changes)?,
                    ),
                    watchman::Changes::WatchmanSynchronous(changes) => {
                        let mut accumulated_changes = s_set::T::new();
                        for c in changes {
                            accumulated_changes = accumulated_changes
                                .union(convert_watchman_changes(root, local_config, c)?);
                        }
                        Changes::SyncChanges(accumulated_changes)
                    }
                };
            let clock = watchman::get_clock(&instance);

            (changes, Some(Clock::Watchman(clock)), telemetry)
        }
    };

    if hh_logger::level::passes_min_level(hh_logger::level::T::Debug) {
        let change_set = match &changes {
            Changes::Unavailable => s_set::T::new(),
            Changes::AsyncChanges(set) | Changes::SyncChanges(set) => set.clone(),
        };
        if !change_set.is_empty() {
            hh_logger::log_with(
                Some(hh_logger::level::T::Debug),
                None,
                &format!(
                    "ServerNotifier.get_changes_async got {} changes",
                    change_set.len()
                ),
            );
            for file in change_set.iter() {
                hh_logger::log_with(
                    Some(hh_logger::level::T::Debug),
                    None,
                    &format!("ServerNotifier.get_changes_async: changed file {}", file),
                );
            }
        }
    }
    Ok((changes, new_clock, telemetry))
}

/// If supported by the backend, returns a file descriptor that can be used to
/// be notified about file system changes. The FD being read-ready is a
/// necessary condition for a subsequent call to `get_changes_{sync,async}`
/// returning any changes. Note that this FD must only be used to
/// `poll`/`select` on, but never actually read from.
pub fn notification_fd(t: &T) -> Option<RawFd> {
    match t {
        T::Dfind { .. } | T::IndexOnly { .. } => None,
        T::MockChanges { .. } => None,
        T::Watchman { watchman, .. } => watchman::get_reader(&lock(watchman)),
    }
}

/// If supported by the backend, returns a value acting as a necessary condition
/// for a subsequent call to `get_changes_{sync,async}` returning any changes.
pub fn maybe_changes_available(t: &T) -> Option<bool> {
    let fd_opt = notification_fd(t);
    // `Caml_unix.select [fd] [] [] 0.0`
    fd_opt.map(|fd| watchman::fd_is_readable(fd, 0.0))
}

/// Returns the asserted states causing Eden to defer asynchronous file changes,
/// sorted by name. Watchman deferral tracking is unsupported; all non-Eden
/// backends return an empty list. Watcher errors are handled as in
/// [get_changes_sync].
pub fn get_deferring_states(t: &T) -> Vec<String> {
    match t {
        T::Watchman { .. } => {
            // Watchman deferral tracking is intentionally unsupported.
            vec![]
        }
        T::IndexOnly { .. } | T::Dfind { .. } | T::MockChanges { .. } => vec![],
    }
}

/// Returns telemetry about asserted repo states
pub fn get_repo_states_telemetry(t: &T) -> telemetry::T {
    let (current_states, past_states) = match t {
        T::Watchman { .. } => watchman::repo_states_get(),
        T::IndexOnly { .. } | T::Dfind { .. } | T::MockChanges { .. } => {
            (vec![], crate::s_map::T::new())
        }
    };
    let mut past_states_telemetry = telemetry::create();
    // `S_map.fold`: in increasing order of the names.
    for (name, ts) in past_states.iter() {
        past_states_telemetry = telemetry::float_(name, *ts, past_states_telemetry);
    }
    let t = telemetry::create();
    let t = telemetry::string_list(None, None, "current_states", &current_states, t);
    telemetry::object_("past_states", past_states_telemetry, t)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(l: &[&str]) -> s_set::T {
        l.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn file_watcher_names() {
        assert_eq!(
            show_file_watcher_name(&Clock::Watchman("c".to_string())),
            "Watchman"
        );
        assert_eq!(
            show_file_watcher_name(&Clock::Eden("c".to_string())),
            "Edenfs_watcher"
        );
    }

    #[test]
    fn null_and_mock_notifiers() {
        let t = init_null();
        wait_until_ready(&t);
        let (changes, clock, _) = get_changes_async(&t, telemetry::create()).unwrap();
        assert_eq!(changes, Changes::SyncChanges(s_set::T::new()));
        assert_eq!(clock, None);
        let (changes, clock, _) = get_changes_sync(&t, telemetry::create()).unwrap();
        assert!(changes.is_empty() && clock.is_none());
        assert_eq!(notification_fd(&t), None);
        assert_eq!(maybe_changes_available(&t), None);
        assert!(get_deferring_states(&t).is_empty());
        assert_eq!(
            telemetry::to_string(None, &get_repo_states_telemetry(&t)),
            r#"{"current_states":[],"past_states":{}}"#
        );
        let t = init_mock(
            || Changes::AsyncChanges(set(&["/a.php"])),
            || set(&["/b.php"]),
        );
        assert_eq!(
            get_changes_async(&t, telemetry::create()).unwrap().0,
            Changes::AsyncChanges(set(&["/a.php"]))
        );
        assert_eq!(
            get_changes_sync(&t, telemetry::create()).unwrap().0,
            set(&["/b.php"])
        );
        let r = std::panic::catch_unwind(|| {
            let _ = indexer(&init_null(), Box::new(|_| true));
        });
        assert_eq!(
            r.err()
                .and_then(|p| p.downcast_ref::<&str>().map(|s| s.to_string())),
            Some("indexer not mocked".to_string())
        );
    }

    #[test]
    fn watchman_changes() {
        let local_config = crate::server_local_config_load::default();
        let root = "/r".to_string();
        assert_eq!(
            convert_watchman_changes(
                &root,
                &local_config,
                watchman::PushedChanges::FilesChanged(set(&["/r/a.php"]))
            )
            .unwrap(),
            set(&["/r/a.php"])
        );
        assert!(
            convert_watchman_changes(
                &root,
                &local_config,
                watchman::PushedChanges::StateEnter("hg.update".to_string(), None)
            )
            .unwrap()
            .is_empty()
        );
        let r = convert_watchman_changes(
            &root,
            &local_config,
            watchman::PushedChanges::ChangedMergeBase(
                "m".to_string(),
                s_set::T::new(),
                "c".to_string(),
            ),
        );
        assert!(matches!(
            r,
            Err(watchman::Exn::ExitWith(exit_status::T::WatchmanInvalidResult))
        ));
    }

    fn all_files(mut next: Next) -> Vec<String> {
        let mut all = vec![];
        loop {
            let batch = next();
            if batch.is_empty() {
                return all;
            }
            all.extend(batch);
        }
    }

    #[test]
    fn index_only_in_check_mode() {
        let dir =
            std::env::temp_dir().join(format!("hh_server_notifier_check_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("a.php"), "").unwrap();
        std::fs::write(dir.join("b.txt"), "").unwrap();
        // Canonical, as `Server_args.root` is (`Path.make`).
        let dir = std::fs::canonicalize(&dir).unwrap();
        let root = dir.to_str().unwrap();
        let options = server_args::default_options_with_check_mode(root);
        let (t, indexer) = init(&options, &crate::server_local_config_load::default(), 2).unwrap();
        assert!(matches!(t, T::IndexOnly { .. }));
        assert_eq!(
            all_files(indexer(Box::new(crate::find_utils::is_hack)).unwrap()),
            vec![format!("{root}/a.php")]
        );
        assert_eq!(
            get_changes_async(&t, telemetry::create()).unwrap().0,
            Changes::SyncChanges(s_set::T::new())
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn edenfs_watcher_is_tried_first() {
        fn panic_message(
            r: std::thread::Result<Result<(T, Indexer), watchman::Exn>>,
        ) -> Option<String> {
            let p = r.err()?;
            p.downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| p.downcast_ref::<String>().cloned())
        }
        let options = server_args::default_options("/nonexistent/hh_root");
        // Eden is preferred to Watchman, and the open-source
        // `Edenfs_watcher.init` fails with `Failure "not implemented"`.
        let mut local_config = crate::server_local_config_load::default();
        local_config.edenfs_file_watcher.enabled = true;
        local_config.watchman.enabled = true;
        let r = std::panic::catch_unwind(|| init(&options, &local_config, 1));
        assert_eq!(panic_message(r), Some("not implemented".to_string()));
        // State tracking with hg_aware needs the hg states.
        local_config.edenfs_file_watcher.state_tracking = true;
        local_config.hg_aware = true;
        local_config.edenfs_file_watcher.tracked_states = vec![];
        let r = std::panic::catch_unwind(|| init(&options, &local_config, 1));
        assert_eq!(
            panic_message(r),
            Some(
                "state_tracking and hg_aware are enabled, but not tracking hg.update and hg.transaction"
                    .to_string()
            )
        );
        // Check mode comes before every watcher.
        let options = server_args::default_options_with_check_mode("/nonexistent/hh_root");
        let (t, _) = init(&options, &local_config, 1).unwrap();
        assert!(matches!(t, T::IndexOnly { .. }));
    }

    #[test]
    fn native_notifier() {
        let dir =
            std::env::temp_dir().join(format!("hh_server_notifier_native_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let root = std::fs::canonicalize(&dir)
            .unwrap()
            .to_str()
            .unwrap()
            .to_string();
        std::fs::write(format!("{root}/a.php"), "1").unwrap();
        let log_dir = format!("{root}.logs");
        std::fs::create_dir_all(&log_dir).unwrap();
        let log = daemon_fd_of_path(&format!("{log_dir}/x.dfind")).unwrap();
        let t = T::Dfind {
            root: root.clone(),
            ready: Arc::new(AtomicBool::new(false)),
            dfind: Arc::new(dfind_lib::init(log, std::slice::from_ref(&root))),
        };
        wait_until_ready(&t);
        assert_eq!(notification_fd(&t), None);
        std::fs::write(format!("{root}/a.php"), "2").unwrap();
        std::fs::write(format!("{root}/.hhconfig"), "").unwrap();
        let (changes, clock, _) = get_changes_async(&t, telemetry::create()).unwrap();
        match changes {
            Changes::SyncChanges(c) => {
                assert!(c.contains(&format!("{root}/a.php")), "{c:?}");
                assert!(c.contains(&format!("{root}/.hhconfig")), "{c:?}");
            }
            c => panic!("unexpected {c:?}"),
        }
        assert_eq!(clock, None);
        assert_eq!(
            all_files(indexer(&t, Box::new(crate::find_utils::is_hack)).unwrap()),
            vec![format!("{root}/a.php")]
        );
        if let T::Dfind { dfind, .. } = &t {
            dfind_lib::stop(dfind)
        }
        let _ = std::fs::remove_dir_all(&root);
        let _ = std::fs::remove_dir_all(&log_dir);
    }

    #[test]
    fn watchman_notifier() {
        use crate::rt::notifier_watchman::tests as wt;
        if !wt::watchman_is_installed() {
            return;
        }
        let root = wt::scratch_root("server_notifier");
        let options = server_args::default_options(&root);
        let mut local_config = crate::server_local_config_load::default();
        local_config.watchman.enabled = true;
        // `watchman_subscribe_v2 = true`, as the integration tests have it.
        local_config.watchman.subscribe = true;
        let (t, indexer) = init(&options, &local_config, 2).unwrap();
        assert!(matches!(t, T::Watchman { .. }));
        let mut files = all_files(indexer(Box::new(crate::find_utils::is_hack)).unwrap());
        files.sort();
        assert_eq!(
            files,
            vec![
                format!("{root}/a.php"),
                format!("{root}/b.php"),
                format!("{root}/c.php")
            ]
        );
        let fd = notification_fd(&t).expect("the fd of the connection");
        wt::edit(&root);
        let (changes, clock, telemetry) = get_changes_sync(&t, telemetry::create()).unwrap();
        wt::check_edits(&root, &changes);
        assert!(matches!(clock, Some(Clock::Watchman(_))));
        assert!(telemetry::to_string(None, &telemetry).contains(r#""sync_watcher":"#));
        // A pushed change.
        std::fs::write(format!("{root}/a.php"), "4").unwrap();
        assert!(crate::rt::notifier_watchman::fd_is_readable(fd, 30.0));
        assert_eq!(maybe_changes_available(&t), Some(true));
        let mut seen = s_set::T::new();
        while maybe_changes_available(&t) == Some(true) {
            match get_changes_async(&t, telemetry::create()).unwrap().0 {
                Changes::AsyncChanges(c) => seen = seen.union(c),
                c => panic!("unexpected {c:?}"),
            }
        }
        assert!(seen.contains(&format!("{root}/a.php")), "{seen:?}");
        assert!(get_deferring_states(&t).is_empty());
        assert!(
            telemetry::to_string(None, &get_repo_states_telemetry(&t))
                .starts_with(r#"{"current_states":["#)
        );
        if let T::Watchman { wenv, .. } = &t {
            crate::rt::notifier_watchman::close(wenv)
        }
        wt::watch_del(&root);
    }
}
