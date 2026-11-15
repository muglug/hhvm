// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `hh_server.ml`: its toplevel (`Monitor_start.start ()`).
//! Only check mode is ported (`hh::monitor_start`).

#![allow(unexpected_cfgs)]

// The OCaml allocates on its own GC heap. Here mimalloc replaces the system
// allocator, because the checker allocates from many threads at once, which
// the system allocator handles poorly (on macOS in particular).
#[cfg(not(hh_heap_stats))]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

// Built with `RUSTFLAGS="--cfg hh_heap_stats"`: the live bytes are counted
// (`hh::rt::heap_stats`, logged as `HEAP_STATS` after each recheck).
#[cfg(hh_heap_stats)]
#[global_allocator]
static GLOBAL: hh::rt::heap_stats::Counting<mimalloc::MiMalloc> =
    hh::rt::heap_stats::Counting(mimalloc::MiMalloc);

fn main() {
    #[cfg(hh_heap_stats)]
    {
        GLOBAL.enable();
        // (Sampling of the live allocations by stack: `rt::heap_stats`.)
        if let Some(every) = std::env::var_os("HH_HEAP_SAMPLE") {
            hh::rt::heap_stats::sampler::enable(every.to_string_lossy().parse().unwrap());
        }
    }
    // A worker process runs its loop on the main thread, which forks.
    hh::worker::run_if_worker();
    // Run on a thread with a large stack, as `hh check` does (rayon's threads
    // get as large a stack: `hh::check::build_thread_pool`).
    let _ = hh::check::run_on_large_stack("hh_server", || hh::monitor_start::start());
    // (`start` exits; a panic that reaches here is an uncaught exception.)
    std::process::exit(221)
}
