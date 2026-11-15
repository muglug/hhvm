// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Fact_id` of the `glean_schema` library (`write_symbol_info/glean/fact_id.ml`).

use std::cell::Cell;

use crate::yojson::safe::T as Json;

pub type T = isize;

thread_local! {
    /// The `ref 1` of `next`. The OCaml counter is one per process: the
    /// indexer runs a batch of files on one thread here where the OCaml
    /// runs it in a worker process, and the thread starts the batch with
    /// the counter the OCaml's process would have (`set_next`).
    static NEXT: Cell<T> = const { Cell::new(1) };
}

pub fn next() -> T {
    NEXT.with(|x| {
        let r = x.get();
        x.set(r + 1);
        r
    })
}

/// The value the next call of `next` returns on this thread (Rust-only: see
/// `NEXT`).
pub fn get_next() -> T {
    NEXT.with(|x| x.get())
}

/// Sets the value the next call of `next` returns on this thread (Rust-only:
/// see `NEXT`).
pub fn set_next(v: T) {
    NEXT.with(|x| x.set(v))
}

pub fn to_json_number(i: T) -> Json {
    Json::Int(i)
}

/// `Fact_id.Map`.
pub type Map<V> = std::collections::BTreeMap<T, V>;
