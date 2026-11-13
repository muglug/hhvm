// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `hh_server`: the toplevel of `hh_server.ml` (`Monitor_start.start ()`).
//! Only check mode is ported (`hh::monitor_start`).

// The checker allocates from many threads at once, which the system allocator
// handles poorly (on macOS in particular).
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    // Run on a thread with a large stack, as `hh check` does (rayon's threads
    // get as large a stack: `hh::check::build_thread_pool`).
    let _ = hh::check::run_on_large_stack("hh_server", || hh::monitor_start::start());
    // (`start` exits; a panic that reaches here is an uncaught exception.)
    std::process::exit(221)
}
