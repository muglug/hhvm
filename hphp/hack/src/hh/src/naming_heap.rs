// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/naming_heap.ml`: the reverse naming table (name -> file).
//! It is the daemon's table of the `Ctx` (`crate::ctx::reverse_naming`, plan
//! D4): positions by the hash of the name, canonical names of types and
//! functions by lowercase name, with the write-once `add` of shared memory. During the world-thread phases of
//! a recheck (indexing, naming, redecl) naming lookups go through here, never
//! through the decl stores (which are being updated).
//!
//! The `db_path` arguments of the OCaml are the database of the table
//! (`Ctx::reverse_naming_table`, set by `Db_path_provider.set_naming_db_path`):
//! with one, a lookup that misses falls back to it and caches the answer
//! (`get_and_cache`), and a remove blocks the name (`BlockedEntries`). The
//! local-changes stacks (`push_local_changes`, `pop_local_changes`) are those
//! of the installed context's table (L0).
//!
//! Owned by **N1** (plan §3.1), then L0.

use crate::ctx::Ctx;

type RPSet = crate::relative_path::set::T;
type DepSet = crate::typing_deps::dep_set::T;

/// `Naming_heap.Types`
pub mod types {
    use oxidized::naming_types::KindOfType;

    use crate::ctx::Ctx;
    use crate::file_info;
    use crate::typing_deps::dep;

    /// `hash name`: `Typing_deps.Dep.make (Typing_deps.Dep.Type name)`
    pub fn hash(name: &str) -> dep::T {
        dep::make(&dep::Variant::Type(name.to_string()))
    }

    /// `canon_hash name`: the hash of the lowercase name.
    pub fn canon_hash(name: &str) -> dep::T {
        hash(&name.to_ascii_lowercase())
    }

    pub fn add(ctx: &Ctx, id: &str, (pos, kind): (&file_info::Pos, KindOfType)) {
        ctx.naming_types_add(id, pos, kind)
    }

    pub fn get_pos(ctx: &Ctx, name: &str) -> Option<(file_info::Pos, KindOfType)> {
        ctx.naming_types_get_pos(name)
    }

    pub fn remove_batch(ctx: &Ctx, types: &[String]) {
        ctx.naming_types_remove_batch(types)
    }

    pub fn get_canon_name(ctx: &Ctx, name: &str) -> Option<String> {
        ctx.get_type_canon_name(name).map(|name| name.as_str().to_string())
    }

    /// `get_kind`
    pub fn get_kind(ctx: &Ctx, name: &str) -> Option<KindOfType> {
        get_pos(ctx, name).map(|(_pos, kind)| kind)
    }
}

/// `Naming_heap.Funs`
pub mod funs {
    use crate::ctx::Ctx;
    use crate::file_info;
    use crate::typing_deps::dep;

    /// `hash name`: `Typing_deps.Dep.make (Typing_deps.Dep.Fun name)`
    pub fn hash(name: &str) -> dep::T {
        dep::make(&dep::Variant::Fun(name.to_string()))
    }

    /// `canon_hash name`: the hash of the lowercase name.
    pub fn canon_hash(name: &str) -> dep::T {
        hash(&name.to_ascii_lowercase())
    }

    pub fn add(ctx: &Ctx, id: &str, pos: &file_info::Pos) {
        ctx.naming_funs_add(id, pos)
    }

    pub fn get_pos(ctx: &Ctx, name: &str) -> Option<file_info::Pos> {
        ctx.naming_funs_get_pos(name)
    }

    pub fn remove_batch(ctx: &Ctx, funs: &[String]) {
        ctx.naming_funs_remove_batch(funs)
    }

    pub fn get_canon_name(ctx: &Ctx, name: &str) -> Option<String> {
        ctx.get_fun_canon_name(name).map(|name| name.as_str().to_string())
    }
}

/// `Naming_heap.Consts`
pub mod consts {
    use crate::ctx::Ctx;
    use crate::file_info;
    use crate::typing_deps::dep;

    /// `hash name`: `Typing_deps.Dep.make (Typing_deps.Dep.GConst name)`
    pub fn hash(name: &str) -> dep::T {
        dep::make(&dep::Variant::GConst(name.to_string()))
    }

    /// `canon_hash`: constants are case-sensitive.
    pub fn canon_hash(name: &str) -> dep::T {
        hash(name)
    }

    pub fn add(ctx: &Ctx, id: &str, pos: &file_info::Pos) {
        ctx.naming_consts_add(id, pos)
    }

    pub fn get_pos(ctx: &Ctx, name: &str) -> Option<file_info::Pos> {
        ctx.naming_consts_get_pos(name)
    }

    pub fn remove_batch(ctx: &Ctx, consts: &[String]) {
        ctx.naming_consts_remove_batch(consts)
    }

    pub fn get_canon_name(ctx: &Ctx, name: &str) -> Option<String> {
        match get_pos(ctx, name) {
            Some(_) => Some(name.to_string()),
            None => None,
        }
    }
}

/// `Naming_heap.Modules`
pub mod modules {
    use crate::ctx::Ctx;
    use crate::file_info;
    use crate::typing_deps::dep;

    /// `hash name`: `Typing_deps.Dep.make (Typing_deps.Dep.Module name)`
    pub fn hash(name: &str) -> dep::T {
        dep::make(&dep::Variant::Module(name.to_string()))
    }

    /// `canon_hash`: modules are case-sensitive.
    pub fn canon_hash(name: &str) -> dep::T {
        hash(name)
    }

    pub fn add(ctx: &Ctx, id: &str, pos: &file_info::Pos) {
        ctx.naming_modules_add(id, pos)
    }

    pub fn get_pos(ctx: &Ctx, name: &str) -> Option<file_info::Pos> {
        ctx.naming_modules_get_pos(name)
    }

    pub fn remove_batch(ctx: &Ctx, modules: &[String]) {
        ctx.naming_modules_remove_batch(modules)
    }

    pub fn get_canon_name(ctx: &Ctx, name: &str) -> Option<String> {
        match get_pos(ctx, name) {
            Some(_) => Some(name.to_string()),
            None => None,
        }
    }
}

/// `get_filenames_by_hash` (`naming_heap.ml:466`): the files of the types,
/// funs and consts whose hashes are given (not modules, as the OCaml).
pub fn get_filenames_by_hash(ctx: &Ctx, hashes: &DepSet) -> RPSet {
    ctx.naming_get_filenames_by_hash(hashes)
}

/// `push_local_changes`: a frame of local changes on every heap of the
/// reverse naming table of the installed context (the OCaml's heaps are the
/// process's; see `crate::ctx::push_naming_local_changes`).
pub fn push_local_changes() {
    crate::ctx::push_naming_local_changes()
}

/// `pop_local_changes`
pub fn pop_local_changes() {
    crate::ctx::pop_naming_local_changes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hashes_are_the_dep_hashes() {
        use crate::typing_deps::dep;
        assert_eq!(types::hash("\\C"), dep::make(&dep::Variant::Type("\\C".into())));
        assert_eq!(types::canon_hash("\\C"), types::hash("\\c"));
        assert_eq!(
            crate::typing_deps::dep::to_int64(funs::hash("\\f")) as u64,
            crate::ctx::reverse_naming::hash(typing_deps_hash::DepType::KFun, "\\f")
        );
        assert_eq!(
            crate::typing_deps::dep::to_int64(consts::hash("\\K")) as u64,
            crate::ctx::reverse_naming::hash(typing_deps_hash::DepType::KGConst, "\\K")
        );
        let _ = |ctx: &Ctx| get_filenames_by_hash(ctx, &DepSet::new());
    }
}
