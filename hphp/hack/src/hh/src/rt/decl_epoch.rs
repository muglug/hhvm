// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The decl epoch: the invalidation of the per-thread memos and caches of
//! the typing core when declarations change (plan D5.2). No OCaml module of
//! its own: it stands for what the OCaml gets from its process model.
//!
//! Owned by **MEMO** (plan §3.1).
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
//!   change: plan §4.2).
//! - `HH_NO_MEMOS=1` ([`no_memos`]): the memos of the typing core that the
//!   OCaml does not have and that answer a typing question across calls are
//!   bypassed (the subtype "ask" and "tell" memos, `dynamic_memo`, the
//!   `localize_` memo, the `extra` tier of the alias cache, the disposable
//!   memos), so that the dependency edges recorded with and without them can
//!   be compared. The caches the OCaml has (the class cache, the alias cache
//!   with the OCaml's settings) and the caches of values that depend on
//!   nothing else (interned names, constant types) stay.
//!
//! # Quarantine (plan §7.3, P0)
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

/// `Shared_mem.invalidate_local_caches ()`, on this thread only: the caches
/// in front of the heaps and every memo the port added, including those
/// keyed by the identity of a `Ctx` (a context with entries keeps its
/// identity across a quarantine), not the heaps (whose stacks of local
/// changes the quarantine pushes and pops). What
/// `Provider_utils.respect_but_quarantine_unsaved_changes` calls when it
/// enters and leaves a quarantine (and P0's local changes when they replace
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
    crate::diagnostics_state::fixme_provider::forget_thread_tables();
}

fn forget_local_caches_and_memos() {
    // The caches the OCaml has (local caches in front of shared memory, or
    // on the heap of a worker, which a job starts afresh).
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

/// TCS, after catching a panic in the check of a file: the reset of the
/// per-thread, per-file state that the unwinding may have left in the
/// middle of a change (the state of `Diagnostics`, the warning-check flag,
/// the quarantine flag of `Provider_context`, the recordings of
/// `Type_expansions`), and of the memos (a panic may have stopped one in
/// the middle of an update). `diagnostics_state::added_count` is a counter
/// that only goes up: it is not reset (a memo compares two of its values).
///
/// (The OCaml's worker process fails then, and is started afresh.)
pub fn after_panic() {
    crate::diagnostics_state::reset_thread_after_panic();
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
/// safety, plan D5.3): a memo that answers across definitions skips the
/// lookups (`Typing_env.get_class` and friends) that record "the definition
/// being checked depends on C". When edges are recorded, such a memo keeps
/// its answers apart for each dependent ([`Dependent::of_env`] when the
/// memo's context is made, [`Dependent::is_for`] when it is looked up):
/// within one dependent, the edges of the computation that made an entry
/// were recorded for that same dependent (edges only add up), so a hit
/// loses none. When nothing is recorded (a batch check) every dependent is
/// the same, [`Dependent::NONE`], and the memos answer as before.
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
        if !crate::typing_env::deps::records_dependency_edges(env) {
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
        let records = crate::typing_env::deps::records_dependency_edges(env);
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
