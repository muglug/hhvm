// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_isolation_growth.ml`. See `hh/PORTING.md`.
//!
//! Growing a set of files that nothing outside it references.
//!
//! A set is safe when every file referencing one of its members is also in
//! it. Growth starts from a seed's closure and adds a file only when
//! everything referencing it is already inside, or when it arrives together
//! with everything referencing it — so the set is safe at every step, not only
//! at the end, which is what makes a truncated result still correct.
//!
//! Which files are tried is a separate question from which are safe to take.
//! Getting the first wrong finds fewer sets; only the second finds a wrong
//! one.
//!
//! Everything here is scoped to one batch: the rounds, the two rules they
//! apply, and the caches those rules fill. Choosing the seeds, running batch
//! after batch, and reporting what came out belong to the caller.

use crate::naming_table;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_isolation_inbound;
use crate::server_isolation_memory as memory;
use crate::server_isolation_memory::BelowFloor;
use crate::server_isolation_outbound;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;

/// What a batch of growth spent and where. Indexing and absorption have
/// entirely different fixes, and one elapsed figure cannot tell them apart.
pub mod stats {
    use std::sync::Mutex;

    #[derive(Clone, Debug, PartialEq)]
    pub struct T {
        pub index_seconds: f64,
        pub absorb_seconds: f64,
        pub candidates_tested: isize,
        /// Candidates whose blocker has not moved, so not retested this
        /// round.
        pub candidates_skipped: isize,
        /// Taken because everything referencing them was already inside.
        pub absorbed_by_subset: isize,
        /// Taken along with everything referencing them — growth getting past
        /// a narrowly-shared file, which the cheap rule cannot do.
        pub absorbed_by_closure: isize,
    }

    pub const ZERO: T = T {
        index_seconds: 0.0,
        absorb_seconds: 0.0,
        candidates_tested: 0,
        candidates_skipped: 0,
        absorbed_by_subset: 0,
        absorbed_by_closure: 0,
    };

    static CURRENT: Mutex<T> = Mutex::new(ZERO);

    pub fn get() -> T {
        CURRENT.lock().unwrap().clone()
    }

    pub fn reset() {
        *CURRENT.lock().unwrap() = ZERO
    }

    /// Runs [f] and hands its duration to [add].
    pub fn timed<R>(add: impl FnOnce(f64), f: impl FnOnce() -> R) -> R {
        let t0 = crate::rt::ocaml_unix::gettimeofday();
        let result = f();
        add(crate::rt::ocaml_unix::gettimeofday() - t0);
        result
    }

    pub fn add_index_seconds(s: f64) {
        CURRENT.lock().unwrap().index_seconds += s
    }

    pub fn add_absorb_seconds(s: f64) {
        CURRENT.lock().unwrap().absorb_seconds += s
    }

    pub fn record_candidate_tested() {
        CURRENT.lock().unwrap().candidates_tested += 1
    }

    pub fn add_candidates_skipped(n: isize) {
        CURRENT.lock().unwrap().candidates_skipped += n
    }

    pub fn record_absorbed_by_subset() {
        CURRENT.lock().unwrap().absorbed_by_subset += 1
    }

    pub fn record_absorbed_by_closure() {
        CURRENT.lock().unwrap().absorbed_by_closure += 1
    }
}

/// What depends on a candidate, minus what it defines itself. Asked once per
/// candidate rather than once per cluster reaching it, and memoised: the walk
/// is expensive and the files that recur on frontiers recur everywhere.
mod dependents {
    use std::sync::LazyLock;
    use std::sync::Mutex;

    use super::*;

    #[derive(Clone, Debug)]
    pub enum T {
        Outside(dep_set::T),
        /// Past [cap], and not stored. This does not refuse the candidate: it
        /// falls through to the closure rule, which may still take it.
        TooMany,
    }

    // Bounds both the walk and what the memo holds, so one candidate cannot
    // keep thousands of hashes alive for the rest of the batch. Not measured —
    // a round number above the clusters a run produces. Too low costs only
    // the cheap rule, and with it the witness that would have let the
    // candidate be skipped next round.
    const CAP: isize = 4096;

    static CACHE: LazyLock<Mutex<relative_path::map::T<T>>> =
        LazyLock::new(|| Mutex::new(relative_path::map::T::new()));

    /// [outside deps_mode candidate own own_set], where [own] is what the
    /// candidate defines and [own_set] the same as a set.
    pub fn outside(
        deps_mode: &typing_deps::mode::T,
        candidate: &RelativePath,
        own: &[dep::T],
        own_set: &dep_set::T,
    ) -> T {
        if let Some(cached) = CACHE.lock().unwrap().get(candidate) {
            return cached.clone();
        }
        // [DepSet.diff] below drops the candidate's own symbols from each
        // answer, at most [cardinal own_set] of them, so ask the graph for
        // [cap] plus that many. A truncated answer then still exceeds [cap]
        // after the drop.
        let graph_cap = CAP + dep_set::cardinal(own_set);
        // `List.fold_until own ~init:(DepSet.make ()) ~f ~finish:Outside`
        let result = (|| {
            let mut acc = dep_set::make();
            for dep in own {
                acc = dep_set::union(
                    &acc,
                    &dep_set::diff(
                        &typing_deps::get_ideps_from_hash_bounded(deps_mode, *dep, graph_cap),
                        own_set,
                    ),
                );
                if dep_set::cardinal(&acc) > CAP {
                    return T::TooMany;
                }
            }
            T::Outside(acc)
        })();
        CACHE
            .lock()
            .unwrap()
            .insert(candidate.clone(), result.clone());
        result
    }

    /// The first dependent lying outside the cluster. Callers keep it as a
    /// witness: while it stays outside, the candidate cannot have become
    /// absorbable.
    pub fn first_outside(cluster_deps: &dep_set::T, dependents: &dep_set::T) -> Option<dep::T> {
        match dep_set::fold_result(dependents, (), |dependent, ()| {
            if dep_set::mem(cluster_deps, dependent) {
                Ok(())
            } else {
                Err(dependent)
            }
        }) {
            Ok(()) => None,
            Err(dependent) => Some(dependent),
        }
    }

    pub fn cached_count() -> isize {
        CACHE.lock().unwrap().len() as isize
    }

    pub fn release() {
        *CACHE.lock().unwrap() = relative_path::map::T::new()
    }
}

/// Whether one candidate can join one cluster, and what comes with it. Two
/// rules, cheapest first; the expensive one runs only on what the cheap one
/// turns down.
mod absorb {
    use super::*;

    pub enum Absorption {
        Absorbs(relative_path::set::T),
        BlockedBy(dep::T),
        Blocked,
        NoRoom,
    }

    /// Room left, or [None] when unbounded. Closure absorption is
    /// all-or-nothing, so checking the cap afterwards would not bound
    /// anything.
    pub fn fits(room: Option<isize>, n: isize) -> bool {
        match room {
            None => true,
            Some(room) => n <= room,
        }
    }

    pub struct Batch<'a> {
        pub ctx: &'a provider_context::T,
        pub workers: Option<usize>,
        pub deps_mode: &'a typing_deps::mode::T,
        pub naming_table: &'a naming_table::T,
        pub claimed: &'a relative_path::set::T,
        pub max_cluster_size: Option<isize>,
        pub max_dependents: isize,
        pub check_memory: &'a (dyn Fn() -> Result<(), BelowFloor> + Sync),
    }

    // Where the subset rule stands: every dependent already inside, one named
    // dependent outside, or too many dependents to have looked at all.
    enum Blocker {
        Inside,
        Witness(dep::T),
        NoWitness,
    }

    fn subset_rule(
        b: &Batch<'_>,
        cluster_deps: &dep_set::T,
        candidate: &RelativePath,
        own: &[dep::T],
        own_set: &dep_set::T,
    ) -> Blocker {
        match dependents::outside(b.deps_mode, candidate, own, own_set) {
            dependents::T::TooMany => Blocker::NoWitness,
            dependents::T::Outside(outside) => {
                match dependents::first_outside(cluster_deps, &outside) {
                    None => Blocker::Inside,
                    Some(dependent) => Blocker::Witness(dependent),
                }
            }
        }
    }

    // [refused] is what the subset rule already concluded: both rules are
    // monotone, so a candidate the closure rule also turns down stays blocked
    // by the dependent the subset rule named.
    fn closure_rule(
        b: &Batch<'_>,
        held: &relative_path::set::T,
        room: Option<isize>,
        refused: Absorption,
        candidate: &RelativePath,
    ) -> Absorption {
        match server_isolation_inbound::get(b.ctx, b.naming_table, b.max_dependents, candidate) {
            Some(closure) if closure.clone().intersection(b.claimed.clone()).is_empty() => {
                // Only files not already held count against the cap. A
                // candidate is on the frontier because a held file references
                // it, so that file depends on it and lies in its closure:
                // measuring the whole closure would refuse ones that fit.
                let joining = match room {
                    None => 0,
                    Some(_) => closure.clone().relative_complement(held.clone()).len() as isize,
                };
                if fits(room, joining) {
                    stats::record_absorbed_by_closure();
                    Absorption::Absorbs(closure)
                } else {
                    Absorption::NoRoom
                }
            }
            Some(_) | None => refused,
        }
    }

    pub fn absorbable(
        b: &Batch<'_>,
        held: &relative_path::set::T,
        room: Option<isize>,
        cluster_deps: &dep_set::T,
        candidate: &RelativePath,
    ) -> Absorption {
        match naming_table::get_file_info(b.naming_table, candidate) {
            None => Absorption::Blocked,
            _ if !fits(room, 1) => Absorption::NoRoom,
            Some(file_info) => {
                let own = typing_deps::deps_of_file_info(&file_info);
                let own_set = dep_set::of_list(&own);
                match subset_rule(b, cluster_deps, candidate, &own, &own_set) {
                    Blocker::Inside => {
                        stats::record_absorbed_by_subset();
                        Absorption::Absorbs(relative_path::set::T::unit(candidate.clone()))
                    }
                    Blocker::Witness(dependent) => {
                        closure_rule(b, held, room, Absorption::BlockedBy(dependent), candidate)
                    }
                    Blocker::NoWitness => {
                        closure_rule(b, held, room, Absorption::Blocked, candidate)
                    }
                }
            }
        }
    }
}

use absorb::Absorption;
use absorb::Batch;
use absorb::absorbable;

// Every file [files] references, added to [init]: a cluster accumulates onto
// what it already reached, a new one starts from nothing.
fn reached_from(
    b: &Batch<'_>,
    init: relative_path::set::T,
    files: &relative_path::set::T,
) -> relative_path::set::T {
    files.iter().fold(init, |acc, path| {
        acc.union(server_isolation_outbound::get(b.ctx, path))
    })
}

fn deps_of_files(naming_table: &naming_table::T, files: &relative_path::set::T) -> dep_set::T {
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

/// A grown cluster. [truncated] means the cap refused it a candidate, so it
/// stopped short of closing: a consumer treating it as finished will find files
/// outside it referencing in.
///
/// A cluster the rounds are finished with: what it holds, and whether the cap
/// stopped it short of closing. This is what a batch hands back.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Grown {
    pub seed: relative_path::T,
    pub files: relative_path::set::T,
    pub truncated: bool,
}

// The same cluster while the rounds are still running. It carries four things
// [grown] does not, because each round needs them and recomputing any of them
// per round would cost more than holding it.
#[derive(Clone)]
struct Growing {
    seed: RelativePath,
    cluster: relative_path::set::T,
    /// Dep hashes the cluster's files define, so absorption tests set
    /// membership rather than a naming-heap lookup.
    cluster_deps: dep_set::T,
    /// Candidate -> the dependent that kept it out. The frontier is rebuilt
    /// each round, so a refused candidate is offered again.
    blocked: relative_path::map::T<dep::T>,
    /// Everything the cluster references, extended with new members' edges
    /// rather than rebuilt, which would be quadratic in cluster size.
    reached: relative_path::set::T,
    /// Whether the cap refused this cluster a candidate it would have taken.
    truncated: bool,
}

fn index(b: &Batch<'_>, paths: &relative_path::set::T) -> Result<(), BelowFloor> {
    stats::timed(stats::add_index_seconds, || {
        let paths: Vec<RelativePath> = paths.iter().cloned().collect();
        server_isolation_outbound::ensure_indexed(b.ctx, b.workers, b.check_memory, &paths)
    })
}

// Everything the cluster reaches and does not hold, less the candidates whose
// blocker has not moved.
fn testable_frontier(g: &Growing) -> (relative_path::set::T, relative_path::set::T) {
    let frontier = g.reached.clone().relative_complement(g.cluster.clone());
    let to_test: relative_path::set::T = frontier
        .iter()
        .filter(|candidate| match g.blocked.get(*candidate) {
            None => true,
            Some(witness) => dep_set::mem(&g.cluster_deps, *witness),
        })
        .cloned()
        .collect();
    stats::add_candidates_skipped(frontier.len() as isize - to_test.len() as isize);
    (frontier, to_test)
}

// One candidate against one cluster, threading what the round holds so far.
fn offer(
    b: &Batch<'_>,
    cluster_deps: &dep_set::T,
    candidate: &RelativePath,
    (held, blocked, truncated): (relative_path::set::T, relative_path::map::T<dep::T>, bool),
) -> (relative_path::set::T, relative_path::map::T<dep::T>, bool) {
    if b.claimed.contains(candidate) {
        (held, blocked, truncated)
    } else if held.contains(candidate) {
        // Arrived earlier this round in another closure.
        (held, blocked, truncated)
    } else {
        stats::record_candidate_tested();
        // Shrinks as the round absorbs, so a round cannot take several
        // candidates that each fit alone.
        let room = b.max_cluster_size.map(|cap| cap - held.len() as isize);
        match absorbable(b, &held, room, cluster_deps, candidate) {
            Absorption::Absorbs(files) => (held.union(files), blocked, truncated),
            Absorption::BlockedBy(witness) => {
                (held, blocked.update(candidate.clone(), witness), truncated)
            }
            Absorption::Blocked => (held, blocked, truncated),
            Absorption::NoRoom => (held, blocked, true),
        }
    }
}

// The cluster with its blockers updated, and the files it gained — disjoint
// from what it already held, so callers may size the two by adding them.
fn absorb_round(
    b: &Batch<'_>,
    g: Growing,
    to_test: &relative_path::set::T,
) -> (Growing, relative_path::set::T) {
    let (held, blocked, truncated) = to_test.iter().fold(
        (g.cluster.clone(), g.blocked.clone(), false),
        |acc, candidate| offer(b, &g.cluster_deps, candidate, acc),
    );
    let absorbed = held.relative_complement(g.cluster.clone());
    let truncated = g.truncated || truncated;
    (
        Growing {
            blocked,
            truncated,
            ..g
        },
        absorbed,
    )
}

/// `(growing, grown) Either.t`
enum Advanced {
    First(Growing),
    Second(Grown),
}

// Retire the cluster, or carry it into the next round with what it gained.
fn advance(b: &Batch<'_>, g: Growing, absorbed: relative_path::set::T) -> Advanced {
    let retire = |g: &Growing, files| {
        Advanced::Second(Grown {
            seed: g.seed.clone(),
            files,
            truncated: g.truncated,
        })
    };
    if absorbed.is_empty() {
        retire(&g, g.cluster.clone())
    } else {
        let cluster = g.cluster.clone().union(absorbed.clone());
        let at_cap = match b.max_cluster_size {
            Some(cap) => cluster.len() as isize >= cap,
            None => false,
        };
        if at_cap {
            // Absorption already did the bounding; this only retires.
            retire(&g, cluster)
        } else {
            let cluster_deps =
                dep_set::union(&g.cluster_deps, &deps_of_files(b.naming_table, &absorbed));
            let reached = reached_from(b, g.reached.clone(), &absorbed);
            Advanced::First(Growing {
                cluster,
                cluster_deps,
                reached,
                ..g
            })
        }
    }
}

fn log_round(round: isize, clusters: isize, frontier_size: isize, entering: &stats::T) {
    let now = stats::get();
    crate::hh_logger::log(&format!(
        "[isolation] round {}: {} clusters, {} frontier files | index {:.1}s absorb {:.1}s | tested {} skipped {} closed {} | deps {} | heap {:.1}GiB rss {:.1}GiB",
        round,
        clusters,
        frontier_size,
        now.index_seconds - entering.index_seconds,
        now.absorb_seconds - entering.absorb_seconds,
        now.candidates_tested - entering.candidates_tested,
        now.candidates_skipped - entering.candidates_skipped,
        now.absorbed_by_closure - entering.absorbed_by_closure,
        dependents::cached_count(),
        memory::heap_gib(),
        memory::rss_gib()
    ))
}

// One absorption round over the whole batch, returning the clusters that are
// still growing and those that finished.
fn run_round(
    b: &Batch<'_>,
    round: isize,
    active: Vec<Growing>,
) -> Result<(Vec<Growing>, Vec<Grown>), BelowFloor> {
    // A round's own figures are the difference against this.
    let entering = stats::get();
    let with_frontier: Vec<(Growing, (relative_path::set::T, relative_path::set::T))> = active
        .into_iter()
        .map(|g| {
            let f = testable_frontier(&g);
            (g, f)
        })
        .collect();
    let frontier_size = with_frontier
        .iter()
        .fold(relative_path::set::T::new(), |acc, (_, (frontier, _))| {
            acc.union(frontier.clone())
        })
        .len() as isize;
    let clusters = with_frontier.len() as isize;
    // Absorption first, then index what it took. [absorbable] never reads an
    // outbound edge; edges are only needed to extend [reached] for files that
    // joined, so indexing the frontier would parse everything a cluster can
    // see to use the edges of the few that join.
    let absorption: Vec<(Growing, relative_path::set::T)> =
        stats::timed(stats::add_absorb_seconds, || {
            with_frontier
                .into_iter()
                .map(|(g, (_, to_test))| absorb_round(b, g, &to_test))
                .collect()
        });
    index(
        b,
        &absorption
            .iter()
            .fold(relative_path::set::T::new(), |acc, (_, a)| {
                acc.union(a.clone())
            }),
    )?;
    // `List.partition_map absorption ~f:(fun (g, absorbed) -> advance b g
    // absorbed)`
    let mut still_active = vec![];
    let mut done_now = vec![];
    for (g, absorbed) in absorption {
        match advance(b, g, absorbed) {
            Advanced::First(g) => still_active.push(g),
            Advanced::Second(g) => done_now.push(g),
        }
    }
    // Accepted closures are spent, and cheap to recompute; refusals are kept.
    server_isolation_inbound::release_closures();
    log_round(round, clusters, frontier_size, &entering);
    // The duplication this removes is within a round: most of a batch reaches
    // the same widely-used files at the same time.
    dependents::release();
    // (`Gc.compact ()`: the dependency sets are freed when they are dropped.)
    Ok((still_active, done_now))
}

fn open_cluster(b: &Batch<'_>, seed: RelativePath, cluster: relative_path::set::T) -> Growing {
    let cluster_deps = deps_of_files(b.naming_table, &cluster);
    let reached = reached_from(b, relative_path::set::T::new(), &cluster);
    Growing {
        seed,
        cluster,
        cluster_deps,
        blocked: relative_path::map::T::new(),
        truncated: false,
        reached,
    }
}

// A cluster starts as the seed's closure, not the seed alone. Growth only
// looks outbound, so it can never reach a file that references the seed
// without the seed referencing back, and the cluster would ship with that file
// pointing into it. A seed whose closure does not fit, or reaches a file
// another cluster holds, is dropped for the same reasons a candidate is.
fn seed_clusters(
    b: &Batch<'_>,
    seeds: &[RelativePath],
) -> Vec<(RelativePath, relative_path::set::T)> {
    let holds_nothing_claimed = |closure: &relative_path::set::T| {
        closure.clone().intersection(b.claimed.clone()).is_empty()
    };
    seeds
        .iter()
        .filter_map(|seed| {
            let closure =
                server_isolation_inbound::get(b.ctx, b.naming_table, b.max_dependents, seed);
            match closure {
                Some(closure) if holds_nothing_claimed(&closure) => Some((seed.clone(), closure)),
                _ => None,
            }
        })
        .collect()
}

/// [grow_batch ctx workers deps_mode naming_table ~claimed ~max_cluster_size
/// ~max_dependents seeds] grows each of [seeds], returning it with the set it
/// grew into.
///
/// [claimed] is every file already reported by an earlier batch; growth will
/// not take one. It is not extended as this batch grows, so two clusters in
/// one batch can both take the same file and the caller has to settle which
/// keeps it.
///
/// [max_dependents] bounds how far the closure rule reaches for one
/// candidate. It must be at least 1, since a seed is grown from its own
/// closure, and no larger than [max_cluster_size], or a cluster would open
/// already over the cap.
///
/// [check_memory] is called before every round, and may raise to stop the
/// batch where it is: a round is what takes the memory, and a batch can run
/// for hundreds of them.
pub fn grow_batch(
    ctx: &provider_context::T,
    workers: Option<usize>,
    deps_mode: &typing_deps::mode::T,
    naming_table: &naming_table::T,
    claimed: &relative_path::set::T,
    max_cluster_size: Option<isize>,
    max_dependents: isize,
    check_memory: &(dyn Fn() -> Result<(), BelowFloor> + Sync),
    seeds: &[relative_path::T],
) -> Result<Vec<Grown>, BelowFloor> {
    // `batch ctx workers deps_mode naming_table ~claimed ~max_cluster_size
    // ~max_dependents ~check_memory`: threaded through every step of the
    // batch, so it is assembled once.
    let b = Batch {
        ctx,
        workers,
        deps_mode,
        naming_table,
        claimed,
        max_cluster_size,
        max_dependents,
        check_memory,
    };
    let start = seed_clusters(&b, seeds);
    let seeded_files = start
        .iter()
        .fold(relative_path::set::T::new(), |acc, (_, cluster)| {
            acc.union(cluster.clone())
        });
    let clusters: Vec<Growing> = start
        .into_iter()
        .map(|(seed, cluster)| open_cluster(&b, seed, cluster))
        .collect();
    // Every closure must be indexed, since [reached] comes from the outbound
    // edges of every member. A file is in its own closure, so indexing the
    // seeds first would only have parsed the refused ones.
    index(&b, &seeded_files)?;
    // `rounds 1 clusters []`
    let mut round = 1;
    let mut active = clusters;
    let mut finished: Vec<Grown> = vec![];
    while !active.is_empty() {
        check_memory()?;
        let (still_active, mut done_now) = run_round(&b, round, active)?;
        // `done_now @ finished`
        done_now.append(&mut finished);
        finished = done_now;
        round += 1;
        active = still_active;
    }
    Ok(finished)
}

/// What this batch spent and decided.
///
/// Accumulates across a run; the caller resets between queries.
pub fn stats() -> stats::T {
    stats::get()
}

pub fn reset_stats() {
    stats::reset()
}

/// Drop what growth filled this round. The accepted closures are cheap to
/// recompute; the refusals are kept, since each cost a full walk and the files
/// that earn them recur everywhere.
///
/// Drop what a batch filled. Growth releases per round as it goes; a caller
/// finished with a batch should release too, since entries are keyed by path
/// and outlive a query.
pub fn release_caches() {
    server_isolation_inbound::release_closures();
    dependents::release()
}
