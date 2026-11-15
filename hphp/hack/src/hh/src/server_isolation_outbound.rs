// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_isolation_outbound.ml`. See `hh/PORTING.md`.
//!
//! Outbound edges: the files a given file statically references.
//!
//! The dependency graph only stores dependents, so this direction comes from
//! the AST. An edge is a reference to a top-level definition — a class,
//! function or global constant — since naming a member also names its class.

use std::collections::HashSet;
use std::sync::LazyLock;
use std::sync::Mutex;
use std::sync::atomic::AtomicIsize;
use std::sync::atomic::Ordering;

use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_isolation_memory::BelowFloor;
use crate::symbol_occurrence;

/// `OutboundHeap` (a `Shared_mem.Heap (ImmediateBackend (NonEvictable))`,
/// description `Server_isolation_outbound`) on the shared heap when the server
/// has one (`ctx::shared_memory_stores`); otherwise a map of the process,
/// which the threads that index write to as the OCaml's workers write to the
/// shared heap.
mod outbound_heap {
    use std::collections::HashMap;
    use std::sync::LazyLock;
    use std::sync::Mutex;

    use super::RelativePath;
    use super::relative_path;

    static HEAP: LazyLock<Mutex<HashMap<RelativePath, relative_path::set::T>>> =
        LazyLock::new(|| Mutex::new(HashMap::new()));

    /// `PathSetValue.t`, in the order of the set.
    #[derive(serde::Serialize, serde::Deserialize)]
    struct PathSetValue(Vec<RelativePath>);

    impl crate::shared_mem::Value for PathSetValue {
        const DESCRIPTION: &'static str = "Server_isolation_outbound";
    }

    fn shared_heap() -> Option<&'static crate::shared_mem::Heap<PathSetValue>> {
        static HEAP: std::sync::OnceLock<crate::shared_mem::Heap<PathSetValue>> =
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
            return heap.add(&key(path), &PathSetValue(files.iter().cloned().collect()));
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

    pub fn mem(path: &RelativePath) -> bool {
        if let Some(heap) = shared_heap() {
            return heap.mem(&key(path));
        }
        HEAP.lock().unwrap().contains_key(path)
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

/// `is_top_level_reference occ`
///
/// Members are left out: on a typed receiver the [Class] occurrence beside
/// them carries the edge. A dynamic receiver has none, so that edge is missed
/// — fewer candidates offered, which costs recall and not correctness.
/// [Attribute None] is kept because it is the one class reference with no
/// [Class] occurrence of its own; [Attribute (Some _)] is only [__Override],
/// which resolves to a method's class instead.
fn is_top_level_reference<P>(occ: &symbol_occurrence::T<P>) -> bool {
    use symbol_occurrence::Kind;
    match &occ.type_ {
        Kind::Class(_) | Kind::Function | Kind::GConst | Kind::Attribute(None) => true,
        Kind::Module
        | Kind::Attribute(Some(_))
        | Kind::Method(..)
        | Kind::Property(..)
        | Kind::XhpLiteralAttr(..)
        | Kind::ClassConst(..)
        | Kind::Typeconst(..)
        | Kind::EnumClassLabel(..)
        | Kind::LocalVar
        | Kind::TypeVar
        | Kind::BuiltInType(_)
        | Kind::Keyword(_)
        | Kind::PureFunctionContext
        | Kind::BestEffortArgument(..)
        | Kind::HhFixme
        | Kind::HhIgnore => false,
    }
}

/// The files [path] statically references, excluding itself.
fn outbound_of_file(ctx: &provider_context::T, path: &RelativePath) -> relative_path::set::T {
    let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
    // `Server_deps_util.get_ast_getdef ctx entry`: the AST, and
    // `Server_symbol_definition.go ctx (Some ast)` applied to it below.
    let ast = crate::ast_provider::compute_ast(provider_context::get_popt(&ctx), &entry);
    crate::identify_symbol_service::all_symbols_ctx(&ctx, &entry)
        .iter()
        .filter(|occ| occ.is_declaration.is_none() && is_top_level_reference(occ))
        .filter_map(|occ| crate::server_symbol_definition::go(&ctx, Some(&ast), occ))
        .map(|def| crate::pos::filename(&def.pos))
        .filter(|target| !relative_path::equal(target, path))
        // A builtin resolves to an .hhi in hh_server's own bundle, which no
        // package could contain.
        .filter(|target| relative_path::is_root(relative_path::prefix(target)))
        .collect()
}

static INDEXED_COUNT: AtomicIsize = AtomicIsize::new(0);

// Which paths are in the heap, so [reset] can drop them.
static CACHED: LazyLock<Mutex<HashSet<RelativePath>>> =
    LazyLock::new(|| Mutex::new(HashSet::new()));

/// Whether a panic payload is `Disk.No_such_file_or_directory _`, as the
/// disk's panics spell its exceptions (`Disk_sig.Types.NotADirectory(..)` in
/// `crate::disk`). Reading a missing source file raises `Sys_error` on the
/// real disk, in the OCaml as here, so that is re-raised.
fn is_no_such_file_or_directory(e: &(dyn std::any::Any + Send)) -> bool {
    let message = if let Some(s) = e.downcast_ref::<String>() {
        s.as_str()
    } else if let Some(s) = e.downcast_ref::<&str>() {
        s
    } else {
        ""
    };
    message.starts_with("Disk_sig.Types.No_such_file_or_directory")
}

fn index_one(ctx: &provider_context::T, path: &RelativePath) -> relative_path::set::T {
    let outbound = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        outbound_of_file(ctx, path)
    })) {
        Ok(outbound) => outbound,
        // Only an unreadable file becomes an empty edge set. An empty set is
        // not neutral — a file that depends on nothing absorbs into a cluster
        // for free — so swallowing a naming-table or dependency-graph failure
        // turns it into a wrong cluster. Those fail for everything, not for
        // this file.
        Err(e) if is_no_such_file_or_directory(&*e) => {
            crate::hh_logger::log(&format!(
                "[isolation] outbound: no such file {}",
                relative_path::suffix(path)
            ));
            relative_path::set::T::new()
        }
        Err(e) => std::panic::resume_unwind(e),
    };
    outbound_heap::add(path, &outbound);
    CACHED.lock().unwrap().insert(path.clone());
    outbound
}

/// Indexes [paths] one at a time, and stops at the first one where
/// [check_memory] says the machine is low, returning why. Checked here, in the
/// worker, before every file: a worker's memory grows with each file it
/// indexes, and the master is waiting for the call to return and cannot look
/// until then.
fn index_batch(
    ctx: &provider_context::T,
    check_memory: &(dyn Fn() -> Result<(), BelowFloor> + Sync),
    _acc: Option<String>,
    paths: &[RelativePath],
) -> Option<String> {
    for path in paths {
        match check_memory() {
            Err(BelowFloor(reason)) => return Some(reason),
            Ok(()) => {
                let _: relative_path::set::T = index_one(ctx, path);
            }
        }
    }
    None
}

/// [ensure_indexed ~ctx ~workers paths] indexes [paths] across workers,
/// skipping those already cached. Batch widely: the pool only pays for itself
/// once there are enough files to fill it.
///
/// Safe on workers because indexing only reads source. Anything reading the
/// dependency graph would not be: a forked worker sees the memory-mapped
/// [base] but not the [delta] on the master's heap.
///
/// [check_memory] is called by each worker before every file. When it raises
/// [Server_isolation_memory.Below_floor] that worker stops, the others stop at
/// their next file, and the exception is re-raised here once the call
/// returns. The files not reached are not indexed.
pub fn ensure_indexed(
    ctx: &provider_context::T,
    workers: Option<usize>,
    check_memory: &(dyn Fn() -> Result<(), BelowFloor> + Sync),
    paths: &[relative_path::T],
) -> Result<(), BelowFloor> {
    // [mem] rather than [get], which would deserialise every hit's edge set
    // only to discard it.
    let mut missing: Vec<RelativePath> = paths
        .iter()
        .filter(|p| !outbound_heap::mem(p))
        .cloned()
        .collect();
    // Deduplicated so a repeated path is not indexed twice, and sorted for
    // EdenFS: buckets are carved from this list in order, so each worker
    // materializes a contiguous run of the tree rather than scattered reads.
    missing.sort_by(relative_path::compare);
    missing.dedup_by(|a, b| relative_path::equal(a, b));
    if !missing.is_empty() {
        // Before the call, not after: if [Multi_worker.call] raises partway,
        // what the workers already wrote would otherwise sit in a
        // non-evictable heap that no [reset] can find. Naming a path never
        // written is harmless.
        CACHED.lock().unwrap().extend(missing.iter().cloned());
        INDEXED_COUNT.fetch_add(missing.len() as isize, Ordering::Relaxed);
        // A worker that finds memory low ends its bucket, and every other does
        // the same at its next file, so the call returns within a file's time
        // rather than raising with workers still busy.
        //
        // `Multi_worker.call workers ~job ~neutral:None ~merge ~next:
        // (Multi_worker.next workers missing)`: the buckets on the threads of
        // the pool, merged in bucket order (the first reason wins); without
        // workers, one after the other on this thread.
        let mut next =
            crate::bucket::make_list(workers.map_or(1, |n| n as isize), None, None, missing);
        let mut buckets = vec![];
        loop {
            let bucket = next();
            if bucket.is_empty() {
                break;
            }
            buckets.push(bucket);
        }
        let job = |bucket: &Vec<RelativePath>| index_batch(ctx, check_memory, None, bucket);
        let reasons: Vec<Option<String>> = match workers {
            None => buckets.iter().map(job).collect(),
            Some(_) => {
                use rayon::prelude::*;
                buckets
                    .par_iter()
                    .map(|bucket| {
                        crate::rt::decl_epoch::sync_thread();
                        job(bucket)
                    })
                    .collect()
            }
        };
        let stopped = reasons
            .into_iter()
            .fold(None, |so_far, reason| match so_far {
                Some(_) => so_far,
                None => reason,
            });
        if let Some(reason) = stopped {
            return Err(BelowFloor(reason));
        }
    }
    Ok(())
}

/// [get ctx path] is the files referenced by [path], excluding itself,
/// computed and cached on first call. Master-only: the cache records what it
/// wrote in process-local state, so a worker calling this would leave entries
/// [reset] cannot drop.
///
/// An unreadable file yields no edges rather than raising, and that empty
/// result is cached; failures that put the whole run in doubt are re-raised.
///
/// The fallback for anything [ensure_indexed] has not pre-warmed.
pub fn get(ctx: &provider_context::T, path: &relative_path::T) -> relative_path::set::T {
    match outbound_heap::get(path) {
        Some(outbound) => outbound,
        None => {
            let outbound = index_one(ctx, path);
            INDEXED_COUNT.fetch_add(1, Ordering::Relaxed);
            outbound
        }
    }
}

/// Drop every cached entry, keeping the [files_indexed] tally. Nothing evicts
/// otherwise, so a caller done with a set of files should release; a dropped
/// entry is recomputed if asked for again.
pub fn release_cache() {
    let mut cached = CACHED.lock().unwrap();
    let n = cached.len();
    if n > 0 {
        let paths: Vec<RelativePath> = cached.drain().collect();
        outbound_heap::remove_batch(&paths);
        drop(cached);
        crate::hh_logger::log(&format!(
            "[isolation] outbound: released {} cached files",
            n
        ));
    }
}

/// How many files have been through indexing, including unreadable ones.
pub fn files_indexed() -> isize {
    INDEXED_COUNT.load(Ordering::Relaxed)
}

/// Drop every cached edge set and zero the tally. Entries are keyed by path
/// alone and outlive a call, so a caller must reset before a run or risk edges
/// derived from a file's earlier contents. Only paths recorded as they were
/// added are dropped — the heap has no iteration, so a future writer must
/// record what it wrote.
pub fn reset() {
    release_cache();
    INDEXED_COUNT.store(0, Ordering::Relaxed);
}
