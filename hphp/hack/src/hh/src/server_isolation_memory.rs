// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_isolation_memory.ml`. See `hh/PORTING.md`.
//!
//! What a run reports about its own memory. An isolation run is bounded by
//! memory rather than by time, so every progress line carries these.
//!
//! `exception Below_floor` is the error of [`check`].

use serde::Deserialize;
use serde::Serialize;

const BYTES_PER_GIB: f64 = 1024. * 1024. * 1024.;

fn gib(bytes: isize) -> f64 {
    bytes as f64 / BYTES_PER_GIB
}

/// Resident set size in GiB. [0.] when the platform does not report one, which
/// a caller cannot tell from a genuine zero.
pub fn rss_gib() -> f64 {
    match crate::memory_stats::get_vm_rss() {
        Some(bytes) => gib(bytes),
        None => 0.,
    }
}

/// The shared heap in GiB.
pub fn heap_gib() -> f64 {
    gib(crate::shared_mem::sm_telemetry::heap_size() as isize)
}

/// Raised by [check] with the sentence that says why the run stopped.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BelowFloor(pub String);

/// The two limits a run is held to, and the memory the machine could give when
/// it began. Small and plain, so it can be sent to the workers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Guard {
    min_free_percent: isize,
    max_used_percent: isize,
    available_at_start: Option<isize>,
}

/// [guard ~min_free_percent ~max_used_percent ~available_at_start] holds the
/// memory available as the run began, in bytes, which the second limit is
/// measured from. [None] where the host does not report it.
pub fn guard(
    min_free_percent: isize,
    max_used_percent: isize,
    available_at_start: Option<isize>,
) -> Guard {
    Guard {
        min_free_percent,
        max_used_percent,
        available_at_start,
    }
}

/// [reason guard ~available ~total] is the sentence that says why a machine
/// with [available] of [total] bytes is past either limit, or [None].
pub fn reason(guard: &Guard, available: isize, total: isize) -> Option<String> {
    let Guard {
        min_free_percent,
        max_used_percent,
        available_at_start,
    } = *guard;
    let floor = total / 100 * min_free_percent;
    if min_free_percent > 0 && available < floor {
        Some(format!(
            "stopped because {:.1} GiB of this machine's memory is available, under the floor of {}% ({:.1} GiB). Clusters written before this are complete. To fit, lower --isolation-batch-size or --isolation-max-cluster-size; --isolation-min-free-memory sets the floor.",
            gib(available),
            min_free_percent,
            gib(floor)
        ))
    } else {
        match available_at_start {
            Some(start) if max_used_percent > 0 => {
                let budget = total / 100 * max_used_percent;
                if start - available > budget {
                    Some(format!(
                        "stopped because the memory available on this machine has fallen by {:.1} GiB since the run started, over its limit of {}% of the machine's memory ({:.1} GiB). Clusters written before this are complete. To fit, lower --isolation-batch-size or --isolation-max-cluster-size; --isolation-max-memory sets the limit.",
                        gib(start - available),
                        max_used_percent,
                        gib(budget)
                    ))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

/// [check guard] raises [Below_floor] when the memory the machine could still
/// give, whoever is using the rest, is under [min_free_percent] of its total,
/// or has fallen by more than [max_used_percent] of its total since [guard]
/// was made. The machine, not this process, since the workers are processes of
/// their own and the whole pool is what exhausts memory. A limit of 0 is off,
/// and nothing is checked where the host does not report its memory.
pub fn check(guard: &Guard) -> Result<(), BelowFloor> {
    match crate::memory_stats::get_mem_available_and_total() {
        Some((available, total)) => match reason(guard, available, total) {
            Some(message) => Err(BelowFloor(message)),
            None => Ok(()),
        },
        None => Ok(()),
    }
}
