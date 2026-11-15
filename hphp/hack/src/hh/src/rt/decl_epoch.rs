// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The decl epoch: the invalidation of the per-thread memos and caches of
//! the typing core when declarations change. No OCaml module of
//! its own: it stands for what the OCaml gets from its process model.
//!
//! # What the OCaml does, and what stands for it here
//!
//! An OCaml worker runs each job (a batch of files) in a process forked
//! afresh (`procs/worker.ml`), so everything a worker caches on its own heap
//! (`Typing_phase`'s alias cache, `Typing_data_type`'s special interfaces,
//! the regexps of `Typing_packages`...) starts again at every batch, and its
//! caches in front of shared memory are emptied at the start of each batch
//! (`Shared_mem.invalidate_local_caches`, `typing_check_service.ml:644`), and
//! again by the master after redecl (`decl_redecl_service.ml:112, 572`) and
//! when a quarantine ends (`provider_utils.ml:265, 273`). The heaps in shared
//! memory (`ParserHeap`, `Fixme_provider`'s tables, `FileHeap`) are one for
//! all the processes: `Ast_provider.remove_batch` and
//! `Fixme_provider.remove_batch` in `Server_type_check.indexing` remove a
//! changed file for every worker.
//!
//! Here a worker is a thread that lives as long as the process and checks
//! many generations of the same files, and those heaps are per thread. So:
//!
//! - [`bump`] (the world thread, when declarations or files changed) starts
//!   a new epoch; [`sync_thread`] (every thread, at the start of each unit
//!   of work: a file in `Typing_check_service`) sees it and forgets
//!   everything the thread derived from declarations or file contents
//!   ([`forget_thread_memos`]): the local caches, the per-thread memos the
//!   port added (which the OCaml does not have), and the per-thread
//!   stand-ins for the shared heaps (as if the world thread's
//!   `remove_batch` had removed every file from them). The stacks of local
//!   changes of those heaps are kept (emptied, at the same depth), so that a
//!   thread inside a push still pops.
//! - [`invalidate_local_caches`] is `Shared_mem.invalidate_local_caches` for
//!   the calling thread: its local caches and the port's memos, not the
//!   heaps.
//! - [`after_panic`] resets the per-file state of a thread after a panic
//!   was caught in the check of a file.
//!
//! In a batch check the epoch never moves: [`sync_thread`] is one Relaxed
//! load and a thread-local compare per file, and nothing is forgotten.
//!
//! # Test hooks
//!
//! - `HH_FORGET_EVERY_FILE=1`: [`sync_thread`] forgets at every call, as if
//!   the declarations had changed before each file (the results must not
//!   change).
//! - `HH_NO_MEMOS=1` ([`no_memos`]): the memos of the typing core that the
//!   OCaml does not have and that answer a typing question across calls are
//!   bypassed (the subtype "ask" and "tell" memos, `dynamic_memo`, the
//!   `localize_` memo, the `extra` tier of the alias cache, the disposable
//!   memos), so that the dependency edges recorded with and without them can
//!   be compared. The caches the OCaml has (the class cache, the alias cache
//!   with the OCaml's settings) and the caches of values that depend on
//!   nothing else (interned names, constant types) stay.
//!
//! # Quarantine
//!
//! `Provider_utils.respect_but_quarantine_unsaved_changes` changes the decl
//! and naming stores for the time of one entry, on one thread: it calls
//! [`invalidate_local_caches`] when it enters and when it leaves, as the
//! OCaml does.

use std::cell::Cell;
use std::sync::atomic::AtomicU8;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;

/// The current epoch. Only the world thread changes it ([`bump`]).
static EPOCH: AtomicU64 = AtomicU64::new(0);

thread_local! {
    /// The epoch the memos of this thread were made in.
    static THREAD_EPOCH: Cell<u64> = const { Cell::new(0) };
}

/// World thread, after naming and redecl of a recheck, before typing (and
/// whenever files or declarations changed before other threads do work that
/// reads them: see the module documentation).
pub fn bump() {
    EPOCH.fetch_add(1, Ordering::Release);
}

pub fn current() -> u64 {
    EPOCH.load(Ordering::Acquire)
}

/// At the start of every unit of work of a thread (each file in
/// `Typing_check_service`): when the epoch moved since this thread last
/// synced, the per-thread memos and caches of this thread are forgotten.
#[inline]
pub fn sync_thread() {
    let epoch = EPOCH.load(Ordering::Relaxed);
    if THREAD_EPOCH.get() != epoch || forget_every_file() {
        // The Acquire load that pairs with `bump`: what the world thread
        // changed before bumping is seen after forgetting.
        THREAD_EPOCH.set(current());
        forget_thread_memos();
    }
}

/// The daemon, when a check is over (the end of
/// `Server_type_check.type_check`): every pool thread and the calling one
/// forget their memos and caches now (a new epoch), instead of keeping them
/// until their next unit of work. An OCaml worker's heap does not outlive
/// its job; here a pool thread that gets no work in the next rechecks would
/// otherwise keep what it cached in this one for as long as the daemon runs.
/// Nothing is lost: every recheck starts a new epoch before typing anyway
/// (`Server_type_check` bumps after indexing and after redecl), so these
/// caches would be
/// forgotten at the first file of the next check. Not for the batch check
/// (which ends the process).
///
/// Then, unless switched off for measurements (`NAME=0`; the switches are
/// read once). The daemon's typing and decling run on the threads of the
/// pool (the OCaml runs them in worker clones that exit after each job,
/// taking their heaps with them; `HH_RUST_WORKERS=1` does that here too, and
/// then these act only on what the master's own threads keep):
/// - `HH_MEM_THREAD_TABLES`: the per-thread tables that do not derive from
///   declarations go too ([`release_thread_tables`]). OCaml counterpart: a
///   worker's clone exits after each job (`Worker.unix_worker_main`), taking
///   its heap with it; these tables are Rust-only structures (the front
///   table of interned symbols, `typing_packages`' answers).
/// - `HH_MEM_COLLECT`: the threads return their free memory to the system
///   once the daemon is idle ([`return_free_memory_when_idle`]). OCaml
///   counterpart: none for the master's malloc heap (the OCaml's workers
///   call `Gc.compact` and `malloc_trim` when they pass their memory cap,
///   `Typing_check_service.process_one_workitem`); it manages mimalloc's
///   per-thread free pages, a Rust-only structure. Its cost is on an idle
///   daemon only.
/// - `HH_MEM_SHRINK`: the hash-consing table is collected and shrunk in the
///   background ([`collect_hash_consed_types`]). The table is a Rust-only
///   structure (the OCaml has no process-wide table of decl types).
///
/// `files_checked`: the number of files the check typechecked.
pub fn release_after_check(files_checked: usize) {
    use crate::rt::heap_stats::switch;
    let start = std::time::Instant::now();
    bump();
    let tables = switch("HH_MEM_THREAD_TABLES", true);
    let release = || {
        sync_thread();
        if tables {
            release_thread_tables();
        }
    };
    rayon::broadcast(|_| release());
    release();
    if switch("HH_MEM_COLLECT", true) {
        return_free_memory_when_idle();
        MAIN_COLLECT_DUE.store(current(), Ordering::Relaxed);
    }
    collect_hash_consed_types(files_checked);
    if switch("HH_HEAP_STATS", false) {
        crate::hh_logger::log(&format!(
            "HEAP_STATS release_after_check: {:.1} ms",
            start.elapsed().as_secs_f64() * 1e3
        ));
    }
}

/// The tables a thread keeps that do not derive from declarations (so
/// that an epoch change does not forget them) and that the daemon drops
/// when a check is over, as the caches of [`release_after_check`]: the
/// thread's table of interned symbols in front of the global one
/// (`ctx::symbol`: about 3.5 MB a thread on Slack's code) and the answers
/// of `typing_packages::is_excluded` (up to 1.6 MB a thread).
fn release_thread_tables() {
    crate::ctx::forget_thread_symbols();
    crate::typing_packages::forget_thread_excluded();
}

/// Every pool thread and this one return their free memory to the
/// system (`mi_collect(true)`): mimalloc returns the free pages of a
/// thread only when that thread allocates or frees again (after a delay),
/// so a pool thread that is idle after a check would keep, for as long as
/// the daemon is idle, all it freed when its caches went (on Slack's code,
/// about 640 MB of the 5.1 GB of the daemon's footprint after the init's
/// full check; about 100 ms for the 14 threads then, a few ms after a
/// small recheck).
fn return_free_memory() {
    rayon::broadcast(|_| crate::rt::heap_stats::collect(true));
    crate::rt::heap_stats::collect(true);
}

/// [`return_free_memory`] once the daemon has been idle for a second
/// after this check (no check started since: the epoch did not move), on a
/// thread of its own: a collection visits every page of every thread (about
/// 100 ms on Slack's code, 15 ms on stripe-hack), which a recheck's reply
/// does not wait for this way, and a burst of rechecks pays it once. (A
/// recheck that starts while it runs waits for it, at most that long.)
fn return_free_memory_when_idle() {
    static REQUESTS: std::sync::LazyLock<Option<std::sync::Mutex<std::sync::mpsc::Sender<u64>>>> =
        std::sync::LazyLock::new(|| {
            let (send, recv) = std::sync::mpsc::channel::<u64>();
            std::thread::Builder::new()
                .name("mem-release".to_string())
                .spawn(move || {
                    while let Ok(mut epoch) = recv.recv() {
                        // Wait for a second without a newer request.
                        loop {
                            match recv.recv_timeout(std::time::Duration::from_secs(1)) {
                                Ok(newer) => epoch = newer,
                                Err(std::sync::mpsc::RecvTimeoutError::Timeout) => break,
                                Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => return,
                            }
                        }
                        if current() == epoch {
                            return_free_memory();
                        }
                    }
                })
                .ok()
                .map(|_| std::sync::Mutex::new(send))
        });
    match &*REQUESTS {
        Some(send) => {
            let _ = send.lock().unwrap().send(current());
        }
        None => return_free_memory(),
    }
}

/// The epoch after which the server's main thread still has to return its
/// free memory (0: nothing to do; see [`return_main_thread_free_memory`]).
static MAIN_COLLECT_DUE: AtomicU64 = AtomicU64::new(0);

/// The idle server's main thread (`Server_idle`'s `ALWAYS` job) returns
/// its free memory to the system once after each check: what it frees after
/// [`release_after_check`] returns (the check's results and the
/// environment it replaces: on Slack's code 70-140 MB) stays in its own
/// pages, which only it can return (mimalloc's per-thread heaps; the threads
/// of [`return_free_memory`] are the pool's).
/// Rust-only, as `HH_MEM_COLLECT`; nothing if a check started since.
pub fn return_main_thread_free_memory() {
    let due = MAIN_COLLECT_DUE.load(Ordering::Relaxed);
    if due != 0 && due == current() && MAIN_COLLECT_DUE.compare_exchange(due, 0, Ordering::AcqRel, Ordering::Relaxed).is_ok() {
        let before = crate::rt::heap_stats::phys_footprint();
        crate::rt::heap_stats::collect(true);
        if switch_heap_stats() {
            crate::hh_logger::log(&format!(
                "HEAP_STATS main thread collect: footprint {:.1} -> {:.1} MB",
                before as f64 / 1e6,
                crate::rt::heap_stats::phys_footprint() as f64 / 1e6
            ));
        }
    }
}

/// The files typechecked since the hash-consing table of decl types was
/// last collected, and the most files one check typechecked (the full check:
/// about the size of the tree).
static CHECKED_SINCE_GC: AtomicU64 = AtomicU64::new(0);
static LARGEST_CHECK: AtomicU64 = AtomicU64::new(0);
static GC_RUNNING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// The table that hash-conses decl types (`hcons::Conser`, of
/// `ty::reason::Reason::decl_ty_conser`) holds a `Weak` for every type it
/// ever made, and a `Weak` keeps the memory of a dead type (its `Arc`
/// allocation) until the entry is replaced or collected. The hash of a type
/// includes the addresses of its children, so a type made again after its
/// children died and were made again gets a new entry: every recheck adds
/// entries (and keeps the dead types they point to) for the decls it parsed
/// again and the hints it typed. The table is never collected otherwise (in
/// the batch check it does not matter: the process ends), so the daemon's
/// memory grew with every recheck (about 1 MB per cycle of edits on
/// stripe-hack, 75 MB on Slack's code; 156 MB of dead types after the
/// init's full check there). Collecting takes about a second on Slack's
/// tree (a pass over the whole table), so it happens on a thread of its own,
/// off the recheck's path, once the checks since the last collection have
/// typechecked an eighth as many files as the largest check (the full
/// one): the table then never holds more than a bounded share of dead
/// entries, at an amortised cost per file typechecked. The table's shards
/// are locked one at a time, so typing that runs meanwhile waits at most
/// for one shard.
fn collect_hash_consed_types(files_checked: usize) {
    let files_checked = files_checked as u64;
    let largest = LARGEST_CHECK.fetch_max(files_checked, Ordering::Relaxed).max(files_checked);
    let since = CHECKED_SINCE_GC.fetch_add(files_checked, Ordering::Relaxed) + files_checked;
    if since.saturating_mul(8) < largest || GC_RUNNING.swap(true, Ordering::AcqRel) {
        return;
    }
    CHECKED_SINCE_GC.store(0, Ordering::Relaxed);
    let spawned = std::thread::Builder::new()
        .name("hcons-gc".to_string())
        .spawn(|| {
            use ty::reason::Reason;
            let conser = crate::ctx::R::decl_ty_conser();
            let log = switch_heap_stats();
            let start = std::time::Instant::now();
            let before = conser.len_and_capacity();
            conser.gc();
            // The table keeps the room of its largest population (the
            // types the check made, live and dead): on Slack's code after
            // the init, 3.6 M entries in room for 14.1 M (214 MB spare).
            if crate::rt::heap_stats::switch("HH_MEM_SHRINK", true) {
                conser.shrink_to_fit();
            }
            // What the collection freed was allocated by the pool threads.
            if crate::rt::heap_stats::switch("HH_MEM_COLLECT", true) {
                return_free_memory();
            }
            if log {
                crate::hh_logger::log(&format!(
                    "HEAP_STATS hcons gc: {:?} -> {:?} (entries, capacity) in {:.0} ms; footprint {:.1} MB",
                    before,
                    conser.len_and_capacity(),
                    start.elapsed().as_secs_f64() * 1e3,
                    crate::rt::heap_stats::phys_footprint() as f64 / 1e6
                ));
            }
            GC_RUNNING.store(false, Ordering::Release);
        });
    if spawned.is_err() {
        GC_RUNNING.store(false, Ordering::Release);
    }
}

/// `HH_HEAP_STATS=1`: the `HEAP_STATS` lines in the server log.
fn switch_heap_stats() -> bool {
    crate::rt::heap_stats::switch("HH_HEAP_STATS", false)
}

/// Waits until a collection of [`collect_hash_consed_types`] that is
/// running is over (for measurements and tests).
pub fn wait_for_hash_consed_gc() {
    while GC_RUNNING.load(Ordering::Acquire) {
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
}

/// `Shared_mem.invalidate_local_caches ()`, on this thread only: the caches
/// in front of the heaps and every memo the port added, including those
/// keyed by the identity of a `Ctx` (a context with entries keeps its
/// identity across a quarantine), not the heaps (whose stacks of local
/// changes the quarantine pushes and pops). What
/// `Provider_utils.respect_but_quarantine_unsaved_changes` calls when it
/// enters and leaves a quarantine (and the local changes when they replace
/// a declaration), so that nothing this thread derived from the
/// declarations of the quarantine is used after it. The epoch does not
/// move. Not to be called while a declaration is being looked up.
pub fn invalidate_local_caches() {
    forget_local_caches_and_memos()
}

/// Everything a thread keeps that derives from declarations or from file
/// contents (see the module documentation).
fn forget_thread_memos() {
    forget_local_caches_and_memos();
    // The per-thread stand-ins for the OCaml's shared heaps.
    crate::ast_provider::forget_thread_heaps();
    crate::file_provider::file_heap::forget_thread_heap();
    crate::fixme_provider::forget_thread_tables();
}

fn forget_local_caches_and_memos() {
    // The caches the OCaml has (local caches in front of shared memory, or
    // on the heap of a worker, which a job starts afresh).
    crate::shared_mem::invalidate_local_caches();
    crate::decl_provider::forget_thread_memos();
    crate::ast_provider::forget_thread_local_caches();
    crate::typing_phase::forget_thread_memos();
    crate::typing_data_type::forget_thread_memos();
    crate::tast_logger_util::generated_file_utils::forget_thread_memos();
    crate::tast_env::clear_merge_memo();
    // The memos the port added.
    crate::naming_provider::forget_thread_memos();
    crate::typing_subtype::subtype_ask::memo::forget_thread_memos();
    crate::typing_subtype::dynamic_memo::forget_thread_memos();
    crate::typing_disposable::forget_thread_memos();
}

/// The typing service, after catching a panic in the check of a file: the
/// reset of the
/// per-thread, per-file state that the unwinding may have left in the
/// middle of a change (the state of `Diagnostics`, the warning-check flag,
/// the quarantine flag of `Provider_context`, the recordings of
/// `Type_expansions`), and of the memos (a panic may have stopped one in
/// the middle of an update). `diagnostics::added_count` is a counter
/// that only goes up: it is not reset (a memo compares two of its values).
///
/// (The OCaml's worker process fails then, and is started afresh.)
pub fn after_panic() {
    crate::diagnostics::reset_thread_after_panic();
    crate::provider_context::reset_quarantine_after_panic();
    crate::type_expansions::recording::reset_after_panic();
    forget_local_caches_and_memos();
}

/// `HH_FORGET_EVERY_FILE` is set.
fn forget_every_file() -> bool {
    static FORGET: std::sync::LazyLock<bool> =
        std::sync::LazyLock::new(|| std::env::var_os("HH_FORGET_EVERY_FILE").is_some());
    *FORGET
}

/// 0: not read yet; 1: off; 2: on.
static NO_MEMOS: AtomicU8 = AtomicU8::new(0);

/// `HH_NO_MEMOS` is set (or [`set_no_memos`] said so): see the module
/// documentation.
#[inline]
pub fn no_memos() -> bool {
    match NO_MEMOS.load(Ordering::Relaxed) {
        1 => false,
        2 => true,
        _ => {
            let on = std::env::var_os("HH_NO_MEMOS").is_some_and(|v| v != "0");
            NO_MEMOS.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
    }
}

/// For tests: bypass the memos (see [`no_memos`]) or not, for every thread
/// from now on.
pub fn set_no_memos(on: bool) {
    NO_MEMOS.store(if on { 2 } else { 1 }, Ordering::Relaxed);
}

/// The definition that the dependency edges recorded now are for (edge
/// safety): a memo that answers across definitions skips the
/// lookups (`Typing_env.get_class` and friends) that record "the definition
/// being checked depends on C". When edges are recorded, such a memo keeps
/// its answers apart for each dependent ([`Dependent::of_env`] when the
/// memo's context is made, [`Dependent::is_for`] when it is looked up):
/// within one dependent, the edges of the computation that made an entry
/// were recorded for that same dependent (edges only add up), so a hit
/// loses none. When nothing is recorded (a batch check) every dependent is
/// the same, [`Dependent::NONE`], and the memos answer as before. (Measured
/// on a 2,196-file sample of Slack's code with edges recorded: the 227,508
/// edges are the same with the memos and with `HH_NO_MEMOS=1`; without the
/// keying 63 were missing. The keying costs about 1% of instructions when
/// edges are recorded.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Dependent(
    Option<(
        Option<crate::typing_deps::dep::Variant>,
        Option<crate::typing_pessimisation_deps::DependentMember>,
    )>,
);

impl Dependent {
    pub(crate) const NONE: Dependent = Dependent(None);

    pub(crate) fn of_env(env: &crate::typing_env_types::Env) -> Self {
        if !crate::deps::records_dependency_edges(env) {
            return Self::NONE;
        }
        let decl_env = &env.decl_env;
        // (Only the fine-grained dependencies are recorded for the member.)
        let member = if env.genv.tcopt.tco_record_fine_grained_dependencies {
            decl_env.droot_member.clone()
        } else {
            None
        };
        Dependent(Some((decl_env.droot.clone(), member)))
    }

    /// `self == Dependent::of_env(env)`, without copying anything.
    #[inline]
    pub(crate) fn is_for(&self, env: &crate::typing_env_types::Env) -> bool {
        let records = crate::deps::records_dependency_edges(env);
        match &self.0 {
            None => !records,
            Some((root, member)) => {
                records
                    && env.decl_env.droot == *root
                    && (!env.genv.tcopt.tco_record_fine_grained_dependencies
                        || env.decl_env.droot_member == *member)
            }
        }
    }
}

#[cfg(test)]
mod tests;
