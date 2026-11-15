// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: the MEM census of the Rust daemon, the same table
//! as the instrumentation of the OCaml (the patch that adds `mem_census` to
//! `server_rpc.ml`): with `HH_MEM_CENSUS_OUT=FILE` in the server's
//! environment, each `STATS` request (`hh_client --stats`) appends to FILE
//! the shared heap heap by heap (entries, stored bytes, bytes before
//! compression, slot bytes), the hash table, this process's local caches,
//! the hash-consing table and the dependency graph's edges.

use std::fmt::Write;

use crate::ctx::Ctx;
use crate::server_env::Env;

/// The census (see the module documentation), if asked for.
pub fn mem_census(env: &Env) {
    let Some(out) = std::env::var_os("HH_MEM_CENSUS_OUT") else {
        return;
    };
    let t0 = std::time::Instant::now();
    let mut names = crate::file_info::empty_names();
    let mut paths = vec![];
    crate::naming_table::fold(None, &env.naming_table, (), |path, fi, ()| {
        paths.push(path.clone());
        let n = crate::file_info::simplify(fi);
        names.funs.extend(n.funs);
        names.classes.extend(n.classes);
        names.types.extend(n.types);
        names.consts.extend(n.consts);
        names.modules.extend(n.modules);
    });
    let mut s = String::new();
    writeln!(s, "=== MEM census (pid {})", std::process::id()).unwrap();
    writeln!(
        s,
        "names: {} classes, {} funs, {} typedefs, {} consts, {} modules, {} files",
        names.classes.len(),
        names.funs.len(),
        names.types.len(),
        names.consts.len(),
        names.modules.len(),
        paths.len()
    )
    .unwrap();
    writeln!(
        s,
        "{:<26} {:>9} {:>9} {:>12} {:>12} {:>12}",
        "heap", "keys", "entries", "stored", "marshalled", "slot"
    )
    .unwrap();
    let (tot_stored, tot_slot) = env.ctx.mem_census_rows(&names, &paths, &mut s);
    let (used, filled) = crate::hh_shared::hash_used_slots();
    writeln!(
        s,
        "shared heap: used {} wasted {}; attributed slot bytes {} (stored {}); hash table slots {} used {} filled {} ({} bytes)",
        crate::hh_shared::used_heap_size(),
        crate::hh_shared::wasted_heap_size(),
        tot_slot,
        tot_stored,
        crate::hh_shared::hash_slots(),
        used,
        filled,
        crate::hh_shared::hash_slots() * 16
    )
    .unwrap();
    for (desc, n) in crate::shared_mem::local_cache_counts() {
        writeln!(s, "local cache (this thread) {:<30} {:>7} entries", desc, n).unwrap();
    }
    {
        use ty::reason::Reason;
        let (len, cap) = crate::ctx::R::decl_ty_conser().len_and_capacity();
        writeln!(s, "hash-consed decl types: {} entries, capacity {}", len, cap).unwrap();
    }
    writeln!(
        s,
        "deps mode {:?}; delta edges {:?}",
        env.deps_mode,
        crate::typing_deps::telemetry::depgraph_delta_num_edges(&env.deps_mode)
    )
    .unwrap();
    writeln!(
        s,
        "master phys_footprint {} live_bytes {:?}",
        crate::rt::heap_stats::phys_footprint(),
        crate::rt::heap_stats::live_bytes()
    )
    .unwrap();
    writeln!(s, "census took {:.1} s", t0.elapsed().as_secs_f64()).unwrap();
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(out) {
        let _ = std::io::Write::write_all(&mut f, s.as_bytes());
    }
}

/// One row of the census: a heap and its keys.
pub(crate) fn row(
    s: &mut String,
    desc: &str,
    keys: usize,
    census: impl Iterator<Item = Option<(u64, u64, u64)>>,
) -> (u64, u64) {
    let (mut n, mut stored, mut orig, mut slot) = (0u64, 0u64, 0u64, 0u64);
    for c in census.flatten() {
        n += 1;
        stored += c.0;
        orig += c.1;
        slot += c.2;
    }
    writeln!(s, "{:<26} {:>9} {:>9} {:>12} {:>12} {:>12}", desc, keys, n, stored, orig, slot).unwrap();
    (stored, slot)
}

impl Ctx {
    /// The rows of the census for the heaps of this context.
    pub(crate) fn mem_census_rows(
        &self,
        names: &crate::file_info::Names,
        paths: &[crate::relative_path::RelativePath],
        s: &mut String,
    ) -> (u64, u64) {
        self.mem_census_rows_(names, paths, s)
    }
}
