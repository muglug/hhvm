// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/old_shallow_classes_provider.ml`. See `hh/PORTING.md`.
//!
//! The "old" shallow classes: those that `Decl_redecl_service` set aside
//! ("oldified") before declaring the changed files again, so that
//! `Shallow_decl_compare` can compare them with the new ones.
//!
//! # Backends
//!
//! Each function matches on `Provider_context.get_backend ctx`. The OCaml
//! daemon and `hh_single_type_check` run the `Shared_memory` backend
//! (`rust_provider_backend` is turned off at startup because
//! `shm_use_sharded_hashtbl` is false): that branch is the one ported, on
//! `Shallow_classes_heap.Classes`, the heap of shallow classes, which is the
//! store of shallow classes of the `Ctx`. Its old entries are the side map
//! of old decls of the `Ctx` (plan D3): `Shallow_classes_heap.Classes`
//! `get_old_batch`, `oldify_batch`, `remove_old_batch` are
//! `Ctx::get_old_defs`, `Ctx::oldify_defs`, `Ctx::remove_old_defs` on the
//! class names only (with the semantics of `Shared_mem`'s batch functions:
//! oldify moves a live entry to the old ones, or deletes the old entry of a
//! name that has no live one).
//!
//! Fetching old decls remotely (`Remote_old_decl_client`) is Meta-only
//! (design of the server layer, 1.1) and has no Rust module either.

use std::sync::Arc;

use ty::decl::ShallowClass;

use crate::ctx::R;
use crate::file_info;
use crate::provider_context;
use crate::s_map;
use crate::s_set;

/// `Shallow_decl_defs.shallow_class`, as the decl stores hold it.
type ShallowClassDecl = Arc<ShallowClass<R>>;

fn fetch_remote_old_decl_flag(ctx: &provider_context::T) -> bool {
    provider_context::get_tcopt(ctx).tco_fetch_remote_old_decls
}

fn only_fetch_remote_old_decl_during_init(ctx: &provider_context::T) -> bool {
    provider_context::get_tcopt(ctx).tco_only_fetch_remote_old_decl_during_init
}

fn fetch_remote_old_decls(ctx: &provider_context::T, during_init: bool) -> bool {
    fetch_remote_old_decl_flag(ctx) && (!only_fetch_remote_old_decl_during_init(ctx) || during_init)
}

/// `Remote_old_decl_client.fetch_old_decls ~ctx names`
fn remote_old_decl_client_fetch_old_decls(
    _ctx: &provider_context::T,
    _names: &[String],
) -> s_map::T<Option<ShallowClassDecl>> {
    todo!(
        "Old_shallow_classes_provider.fetch_missing_old_classes_remotely: \
         Remote_old_decl_client.fetch_old_decls (decl/remote_old_decl_client.ml, \
         Meta-only) has no Rust module"
    )
}

fn fetch_missing_old_classes_remotely(
    ctx: &provider_context::T,
    during_init: bool,
    old_classes: s_map::T<Option<ShallowClassDecl>>,
) -> s_map::T<Option<ShallowClassDecl>> {
    if fetch_remote_old_decls(ctx, during_init) {
        // `S_map.filter (fun _key -> Option.is_none) old_classes |> S_map.keys`
        let missing: s_map::T<Option<ShallowClassDecl>> = old_classes
            .iter()
            .filter(|(_, decl)| decl.is_none())
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let missing_old_classes = s_map::keys(&missing);
        let remote_old_classes = remote_old_decl_client_fetch_old_decls(ctx, &missing_old_classes);
        s_map::union(
            Some(&|_key: &String,
                   decl1: &Option<ShallowClassDecl>,
                   decl2: &Option<ShallowClassDecl>| {
                // `Option.first_some decl1 decl2`
                Some(decl1.clone().or_else(|| decl2.clone()))
            }),
            &old_classes,
            &remote_old_classes,
        )
    } else {
        old_classes
    }
}

/// `Classes_heap.get_old_batch names` (`Shallow_classes_heap.Classes`).
fn shallow_classes_heap_get_old_batch(
    ctx: &provider_context::T,
    names: &s_set::T,
) -> s_map::T<Option<ShallowClassDecl>> {
    ctx.get_old_defs(&classes_only(names))
        .classes
        .into_iter()
        .collect()
}

fn classes_only(names: &s_set::T) -> file_info::Names {
    file_info::Names {
        classes: names.iter().cloned().collect(),
        ..file_info::empty_names()
    }
}

pub fn get_old_batch(
    ctx: &provider_context::T,
    during_init: bool,
    names: &s_set::T,
) -> s_map::T<Option<ShallowClassDecl>> {
    // `Provider_backend.Shared_memory` (see the module documentation).
    let old_classes = shallow_classes_heap_get_old_batch(ctx, names);
    fetch_missing_old_classes_remotely(ctx, during_init, old_classes)
}

pub fn oldify_batch(ctx: &provider_context::T, names: &s_set::T) {
    // `Provider_backend.Rust_provider_backend _ | Provider_backend.Shared_memory`:
    // `Shallow_classes_heap.Classes.oldify_batch names`.
    ctx.oldify_defs(&classes_only(names))
}

pub fn remove_old_batch(ctx: &provider_context::T, names: &s_set::T) {
    // `Provider_backend.Rust_provider_backend _ | Provider_backend.Shared_memory`:
    // `Shallow_classes_heap.Classes.remove_old_batch names`.
    ctx.remove_old_defs(&classes_only(names))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;
    use crate::ctx::Ctx;

    fn ctx(fetch: bool, only_during_init: bool) -> provider_context::T {
        let tco = TypecheckerOptions {
            tco_fetch_remote_old_decls: fetch,
            tco_only_fetch_remote_old_decl_during_init: only_during_init,
            ..TypecheckerOptions::default()
        };
        Arc::new(Ctx::new(Path::new("/"), tco).unwrap())
    }

    #[test]
    fn when_old_decls_are_fetched_remotely() {
        assert!(!fetch_remote_old_decls(&ctx(false, false), false));
        assert!(!fetch_remote_old_decls(&ctx(false, true), true));
        assert!(fetch_remote_old_decls(&ctx(true, false), false));
        assert!(fetch_remote_old_decls(&ctx(true, false), true));
        assert!(!fetch_remote_old_decls(&ctx(true, true), false));
        assert!(fetch_remote_old_decls(&ctx(true, true), true));
        // Without remote fetching, the old classes are what the store gave.
        let old_classes: s_map::T<Option<ShallowClassDecl>> =
            [("\\C".to_string(), None)].into_iter().collect();
        let classes = fetch_missing_old_classes_remotely(&ctx(true, true), false, old_classes);
        assert_eq!(s_map::ordered_keys(&classes), vec!["\\C".to_string()]);
        assert!(classes.get("\\C").unwrap().is_none());
    }
}
