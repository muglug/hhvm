// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/db_path_provider.ml`.
//!
//! Owned by **SS1** (plan §7.3).
//!
//! The naming_db_path says where the naming-table sqlite file is found.
//!
//! The OCaml keeps it per backend: in shared memory (`Shared_db_settings`,
//! for the `Shared_memory`/`Analysis` backends), in the Rust backend
//! (`Rust_provider_backend.Naming.set_db_path`), or in the
//! `naming_db_path_ref` of a `Local_memory` backend (the IDE). Here: in the
//! stores of the `Ctx` (`Shared_memory`), or in its `Local_memory` backend
//! (L0).

use crate::ctx::Ctx;
use crate::naming_sqlite;

/// the naming_db_path says where the naming-table sqlite file is found.
///
/// The `Shared_memory` backend keeps it in `Shared_db_settings` (one heap
/// for the process) behind a cache of absences: here in the stores of the
/// `Ctx` (shared by its generations and clones, one per daemon), whose `None`
/// is the absence. The `Local_memory` backend keeps it in its
/// `naming_db_path_ref`.
pub fn get_naming_db_path(backend: &Ctx) -> Option<naming_sqlite::DbPath> {
    match backend.local_memory() {
        Some(local_memory) => local_memory.naming_db_path_ref.lock().unwrap().clone(),
        None => backend.decl_stores.shared_db_path.read().unwrap().clone(),
    }
}

/// naming_db_path is set at initialization once we know the path.
pub fn set_naming_db_path(backend: &Ctx, naming_db_path: Option<naming_sqlite::DbPath>) {
    match backend.local_memory() {
        Some(local_memory) => *local_memory.naming_db_path_ref.lock().unwrap() = naming_db_path,
        None => {
            // (The reverse naming table, if built, falls back to it.)
            if let Some(table) = backend.reverse_naming_table_opt() {
                table.set_db_path(naming_db_path.clone());
            }
            *backend.decl_stores.shared_db_path.write().unwrap() = naming_db_path
        }
    }
}
