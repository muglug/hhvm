// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/client_ide_eden_watcher.ml`. See
//! `hh/PORTING.md`.
//!
//! Starts an Eden watcher synchronously, then polls for small commit transitions.
//! Transitions exceeding [max_changed_files] after filtering and deduplication
//! are skipped.
//! [on_changes] receives filtered, deduplicated Hack source paths; returning
//! [false] stops polling. Native initialization errors leave the watcher
//! disabled; subsequent watcher failures stop polling without propagating to
//! the caller. Whenever polling ends, the native watcher is destroyed.
//!
//! The Eden watcher is Meta-only: in the open-source build its `init`
//! (`stubs/edenfs_watcher.ml`) fails with `Failure "not implemented"`, so
//! `start` panics with that message, as OCaml raises it (the IDE daemon's
//! initialization then fails, as in OCaml), and no watcher instance can
//! exist. What only an instance uses (`t`, `destroy`, `stop`, `poll` and its
//! `[ide-eden-watcher]` log lines other than those of `process_change`) is
//! not here.

use oxidized::edenfs_watcher_types::Changes;

use crate::files_to_ignore;
use crate::find_utils;
use crate::hh_logger;
use crate::path;
use crate::relative_path;

fn log(s: &str) {
    hh_logger::log(&format!("[ide-eden-watcher] {}", s))
}

/// `process_change ~max_changed_files ~on_changes change`: whether to keep
/// polling.
pub fn process_change(
    max_changed_files: isize,
    on_changes: &mut dyn FnMut(relative_path::set::T) -> bool,
    change: &Changes,
) -> bool {
    match change {
        Changes::FileChanges { .. } | Changes::StateEnter(_) | Changes::StateLeave(_) => true,
        Changes::CommitTransition { file_changes, .. } => {
            let changes: relative_path::set::T = file_changes
                .iter()
                .filter(|f| find_utils::file_filter(f))
                .map(|f| relative_path::create_detect_prefix(f))
                .collect();
            let count = changes.len() as isize;
            if count == 0 {
                true
            } else if count > max_changed_files {
                // Edenfs_watcher has already expanded the commit diff; this limit only
                // bounds naming-table and cache-invalidation work in the daemon.
                log(&format!(
                    "Skipping commit transition with {} relevant files",
                    count
                ));
                true
            } else {
                log(&format!(
                    "Enqueuing commit transition with {} relevant files",
                    count
                ));
                on_changes(changes)
            }
        }
    }
}

pub fn start(
    _root: &path::T,
    _max_changed_files: isize,
    _on_changes: impl FnMut(relative_path::set::T) -> bool + Send + 'static,
) {
    let _watch_spec = files_to_ignore::WatchSpec {
        include_file_names: vec![],
        ..files_to_ignore::server_watch_spec()
    };
    // `Edenfs_watcher.init ~destroy_on_exit:false settings` (with
    // `timeout_secs = 60`, `state_tracking = true`, `tracked_states =
    // ["hg.update"; "hg.transaction"]`): the open-source stub
    // (`stubs/edenfs_watcher.ml`) begins with `require_test_stubbing ()`,
    // which raises `Failure "not implemented"` outside the tests.
    panic!("not implemented")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn transition(files: &[&str]) -> Changes {
        Changes::CommitTransition {
            from_commit: "a".to_string(),
            to_commit: "b".to_string(),
            file_changes: files.iter().map(|s| s.to_string()).collect(),
            translated_at: 0.0,
        }
    }

    #[test]
    fn process_change_filters_and_bounds() {
        // `create_detect_prefix` needs the prefixes set (the paths here are
        // under none of them, so whatever another test set them to will do).
        for prefix in [
            relative_path::Prefix::Root,
            relative_path::Prefix::Hhi,
            relative_path::Prefix::Tmp,
        ] {
            if relative_path::path_of_prefix(prefix).is_err() {
                relative_path::set_path_prefix(
                    prefix,
                    std::path::Path::new("/nonexistent_ide_eden_watcher_test"),
                );
            }
        }
        let mut got: Vec<relative_path::set::T> = vec![];
        let mut on_changes = |s: relative_path::set::T| {
            got.push(s);
            false
        };
        assert!(process_change(
            10,
            &mut on_changes,
            &Changes::StateEnter("hg.update".to_string())
        ));
        // No Hack files: nothing to do.
        assert!(process_change(
            10,
            &mut on_changes,
            &transition(&["/r/README.md"])
        ));
        // Over the bound: skipped.
        assert!(process_change(
            1,
            &mut on_changes,
            &transition(&["/r/a.php", "/r/b.php"])
        ));
        // Deduplicated, and the callback decides whether to go on.
        assert!(!process_change(
            2,
            &mut on_changes,
            &transition(&["/r/a.php", "/r/a.php", "/r/b.php", "/r/c.txt"])
        ));
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].len(), 2);
    }
}
