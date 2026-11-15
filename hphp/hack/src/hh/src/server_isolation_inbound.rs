// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_isolation_inbound.ml`. See `hh/PORTING.md`.
//!
//! Inbound closure: every file that transitively depends on a given file.
//!
//! Upward-closed over files — not merely over symbols — so nothing outside a
//! closure references into it and it is safe to take whole. Take part of one
//! and that stops being true.

use std::collections::HashSet;
use std::sync::LazyLock;
use std::sync::Mutex;
use std::sync::atomic::AtomicIsize;
use std::sync::atomic::Ordering;

use crate::naming_table;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::typing_deps;
use crate::typing_deps::dep_set;

/// `ClosureHeap` (a `Shared_mem.Heap (ImmediateBackend (NonEvictable))`,
/// description `Server_isolation_inbound`) on the shared heap when the server
/// has one (`ctx::shared_memory_stores`); otherwise a map of the process.
mod closure_heap {
    use std::collections::HashMap;
    use std::sync::LazyLock;
    use std::sync::Mutex;

    use super::RelativePath;
    use super::relative_path;

    static HEAP: LazyLock<Mutex<HashMap<RelativePath, relative_path::set::T>>> =
        LazyLock::new(|| Mutex::new(HashMap::new()));

    /// `ClosureValue.t`, in the order of the set.
    #[derive(serde::Serialize, serde::Deserialize)]
    struct ClosureValue(Vec<RelativePath>);

    impl crate::shared_mem::Value for ClosureValue {
        const DESCRIPTION: &'static str = "Server_isolation_inbound";
    }

    fn shared_heap() -> Option<&'static crate::shared_mem::Heap<ClosureValue>> {
        static HEAP: std::sync::OnceLock<crate::shared_mem::Heap<ClosureValue>> =
            std::sync::OnceLock::new();
        crate::ctx::shared_memory_stores()
            .then(|| HEAP.get_or_init(|| crate::shared_mem::Heap::new(0)))
    }

    /// `PathKey.to_string` (`Relative_path.to_absolute`)
    fn key(path: &RelativePath) -> Vec<u8> {
        relative_path::to_absolute(path).into_bytes()
    }

    pub fn add(path: &RelativePath, files: &relative_path::set::T) {
        if let Some(heap) = shared_heap() {
            return heap.add(&key(path), &ClosureValue(files.iter().cloned().collect()));
        }
        HEAP.lock()
            .unwrap()
            .entry(path.clone())
            .or_insert_with(|| files.clone());
    }

    pub fn get(path: &RelativePath) -> Option<relative_path::set::T> {
        if let Some(heap) = shared_heap() {
            return heap.get(&key(path)).map(|v| v.0.into_iter().collect());
        }
        HEAP.lock().unwrap().get(path).cloned()
    }

    pub fn remove_batch(paths: &[RelativePath]) {
        if let Some(heap) = shared_heap() {
            for path in paths {
                heap.remove(&key(path));
            }
            return;
        }
        let mut heap = HEAP.lock().unwrap();
        for path in paths {
            heap.remove(path);
        }
    }
}

// Budget for the walk, in dep hashes rather than the files the caller bounds.
// Firing early can refuse a closure that would have fitted, never return an
// incomplete one. The floor matters because growth clamps [max] to the cluster
// cap, which alone would put the budget below closures that do fit.
//
// Neither figure is measured. Twenty hashes per permitted file is a guess at
// what a Hack file defines, and the floor is a round number above the closures
// a run actually returns. Both err towards refusing, so setting either too low
// costs recall — a lower isolatability figure — and never a wrong closure.
const DEPS_PER_FILE_ALLOWANCE: isize = 20;

const MIN_DEPS_ALLOWANCE: isize = 5000;

// A refusal costs a full walk to recompute and one path to hold, so refusals
// outlive a batch; accepted closures are the reverse.
static REFUSED: LazyLock<Mutex<HashSet<RelativePath>>> =
    LazyLock::new(|| Mutex::new(HashSet::new()));

// The heap is keyed by a hash of the path and cannot be enumerated.
static CACHED: LazyLock<Mutex<HashSet<RelativePath>>> =
    LazyLock::new(|| Mutex::new(HashSet::new()));

static COMPUTED_COUNT: AtomicIsize = AtomicIsize::new(0);

static SERVED_COUNT: AtomicIsize = AtomicIsize::new(0);

/// `grow_to_fixpoint deps_mode ~max_deps ~acc frontier`
///
/// [add_all_deps] chains these two but cannot be used here: it returns its
/// input, re-expanding the whole set each iteration, and it runs the recursive
/// extends walk first, which completes inside the graph before the bound can
/// refuse it. [None] means the walk passed [max_deps], not that there is no
/// closure.
fn grow_to_fixpoint(
    deps_mode: &typing_deps::mode::T,
    max_deps: isize,
    acc: dep_set::T,
    frontier: dep_set::T,
) -> Option<dep_set::T> {
    let over = |s: &dep_set::T| dep_set::cardinal(s) > max_deps;
    let mut acc = acc;
    let mut frontier = frontier;
    loop {
        // A truncated result is strictly larger than [max_deps], so it fails
        // [over] exactly as the complete one would.
        let typed = dep_set::union(
            &acc,
            &typing_deps::add_typing_deps_bounded(deps_mode, &frontier, max_deps),
        );
        if over(&typed) {
            return None;
        }
        let next = dep_set::union(&typed, &typing_deps::add_extend_deps(deps_mode, &frontier));
        if over(&next) {
            return None;
        }
        let new_frontier = dep_set::diff(&next, &acc);
        if dep_set::is_empty(&new_frontier) {
            return Some(acc);
        }
        acc = next;
        frontier = new_frontier;
    }
}

/// `symbols_of_files naming_table files`: every top-level symbol defined by
/// any of [files].
fn symbols_of_files(naming_table: &naming_table::T, files: &relative_path::set::T) -> dep_set::T {
    files.iter().fold(
        dep_set::make(),
        |acc, path| match naming_table::get_file_info(naming_table, path) {
            None => acc,
            Some(file_info) => dep_set::union(
                &acc,
                &dep_set::of_list(&typing_deps::deps_of_file_info(&file_info)),
            ),
        },
    )
}

/// `compute ctx naming_table ~max path`
fn compute(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    max: isize,
    path: &RelativePath,
) -> Option<relative_path::set::T> {
    match naming_table::get_file_info(naming_table, path) {
        None => None,
        Some(file_info) => {
            let deps_mode = provider_context::get_deps_mode(ctx);
            let own = dep_set::of_list(&typing_deps::deps_of_file_info(&file_info));
            let max_deps = std::cmp::max(MIN_DEPS_ALLOWANCE, max * DEPS_PER_FILE_ALLOWANCE);
            // Upward-closed in hash space, but the caller absorbs whole files:
            // a resolved file brings symbols the walk never reached, and
            // whatever depends on those is missing. So resolved symbols feed
            // back until a round resolves no new file, which terminates because
            // [max_deps] bounds the growth.
            let mut acc = own.clone();
            let mut frontier = own;
            loop {
                // `close acc frontier`
                match grow_to_fixpoint(&deps_mode, max_deps, acc, frontier) {
                    None => return None,
                    Some(hashes) => {
                        let files = crate::naming_provider::get_files(ctx, &hashes);
                        if files.len() as isize > max {
                            return None;
                        }
                        let symbols = symbols_of_files(naming_table, &files);
                        let new_frontier = dep_set::diff(&symbols, &hashes);
                        if dep_set::is_empty(&new_frontier) {
                            return Some(files);
                        }
                        acc = dep_set::union(&hashes, &symbols);
                        frontier = new_frontier;
                    }
                }
            }
        }
    }
}

/// [get ctx naming_table ~max path] is the closure of [path], including [path]
/// itself; [None] when it passes [max] files, or when the naming table does
/// not know [path].
///
/// Memoised on [path] alone, so a caller that varies [max] must [reset]
/// between.
///
/// Master-only: a forked worker sees the memory-mapped [base] graph but not
/// the [delta] on the master's heap, so it may be trusted to say a closure is
/// too large, never that one is complete.
pub fn get(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    max: isize,
    path: &relative_path::T,
) -> Option<relative_path::set::T> {
    if REFUSED.lock().unwrap().contains(path) {
        SERVED_COUNT.fetch_add(1, Ordering::Relaxed);
        None
    } else {
        match closure_heap::get(path) {
            Some(closure) => {
                SERVED_COUNT.fetch_add(1, Ordering::Relaxed);
                Some(closure)
            }
            None => {
                COMPUTED_COUNT.fetch_add(1, Ordering::Relaxed);
                match compute(ctx, naming_table, max, path) {
                    None => {
                        REFUSED.lock().unwrap().insert(path.clone());
                        None
                    }
                    Some(files) => {
                        closure_heap::add(path, &files);
                        CACHED.lock().unwrap().insert(path.clone());
                        Some(files)
                    }
                }
            }
        }
    }
}

/// Closures computed rather than served from the memo, [None] included.
pub fn closures_computed() -> isize {
    COMPUTED_COUNT.load(Ordering::Relaxed)
}

/// Requests the memo served.
pub fn closures_served() -> isize {
    SERVED_COUNT.load(Ordering::Relaxed)
}

/// Refusals held; one path each, the cheap half of the memo.
pub fn refusals_held() -> isize {
    REFUSED.lock().unwrap().len() as isize
}

/// Drop the accepted closures, keep the refusals. Closures are expensive to
/// hold and cheap to recompute; refusals are the reverse.
pub fn release_closures() {
    let mut cached = CACHED.lock().unwrap();
    if !cached.is_empty() {
        let paths: Vec<RelativePath> = cached.drain().collect();
        closure_heap::remove_batch(&paths);
    }
}

/// Drop everything, refusals included, and zero the counters. Entries outlive
/// a call, so a caller must reset before a run or risk a closure computed from
/// a file's earlier contents, or under a different [max].
pub fn reset() {
    release_closures();
    REFUSED.lock().unwrap().clear();
    COMPUTED_COUNT.store(0, Ordering::Relaxed);
    SERVED_COUNT.store(0, Ordering::Relaxed);
}

// The files outside [candidate] that reference a symbol defined in [files].
fn dependents_outside(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    candidate: &relative_path::set::T,
    files: &relative_path::set::T,
) -> relative_path::set::T {
    let deps_mode = provider_context::get_deps_mode(ctx);
    let own = symbols_of_files(naming_table, files);
    let dependents = typing_deps::add_typing_deps(&deps_mode, &own);
    crate::naming_provider::get_files(ctx, &dependents).relative_complement(candidate.clone())
}

/// [referrers ctx naming_table candidate] is every file outside [candidate]
/// that references a symbol defined inside it. Direct references only, where
/// [get] walks the closure. Not memoised, unlike [get]. Master-only, like
/// [get].
pub fn referrers(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    candidate: &relative_path::set::T,
) -> relative_path::set::T {
    dependents_outside(ctx, naming_table, candidate, candidate)
}

/// [referrers_by_target ctx naming_table candidate] is each of the files that
/// [referrers] gives, with the files of [candidate] that it references. It asks
/// once for each file of [candidate], where [referrers] asks once for all of
/// them, so it is for saying why a set is blocked, not for deciding it.
pub fn referrers_by_target(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    candidate: &relative_path::set::T,
) -> relative_path::map::T<relative_path::set::T> {
    let mut acc: relative_path::map::T<relative_path::set::T> = relative_path::map::T::new();
    for target in candidate.iter() {
        let files: relative_path::set::T = std::iter::once(target.clone()).collect();
        for referrer in dependents_outside(ctx, naming_table, candidate, &files).iter() {
            let mut targets = acc.get(referrer).cloned().unwrap_or_default();
            targets.insert(target.clone());
            acc.insert(referrer.clone(), targets);
        }
    }
    acc
}
