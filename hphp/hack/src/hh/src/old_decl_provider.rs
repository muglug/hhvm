// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/old_decl_provider.ml`. See `hh/PORTING.md`.
//!
//! The "old" decls: those that `Decl_redecl_service` set aside ("oldified")
//! before declaring the changed files again, so that `Shallow_decl_compare`
//! and `Decl_compare` can compare them with the new ones.
//!
//! # Backends
//!
//! Each function matches on `Provider_context.get_backend ctx`. The
//! `Shared_memory` and `Rust_provider_backend` backends are the same stores
//! here: `Shallow_classes_heap.Classes`, the heap of shallow classes, is the
//! store of shallow classes of the `Ctx`, and `Decl_heap.Funs`, `Typedefs`,
//! `GConsts` and `Modules` are `crate::decl_heap`. The old entries are the
//! side map of old decls of the `Ctx`: `Shallow_classes_heap.Classes`
//! `get_old_batch`, `oldify_batch`, `remove_old_batch` are
//! `Ctx::get_old_defs`, `Ctx::oldify_defs`, `Ctx::remove_old_defs` on the
//! class names only (with the semantics of `Shared_mem`'s batch functions:
//! oldify moves a live entry to the old ones, or deletes the old entry of a
//! name that has no live one).
//!
//! Fetching old decls remotely is `crate::remote_old_decl_client` (as the
//! open-source build has it: its FFI fails).

use std::sync::Arc;

use ty::decl::ShallowClass;
use ty::decl::shallow::NamedDecl;

use crate::ctx::R;
use crate::decl_heap;
use crate::decl_provider::FunDecl;
use crate::decl_provider::GconstDecl;
use crate::decl_provider::ModuleDecl;
use crate::decl_provider::TypedefDecl;
use crate::file_info;
use crate::provider_backend;
use crate::provider_context;
use crate::remote_old_decl_client;
use crate::s_map;
use crate::s_set;
use crate::typing_deps::dep;

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
        let missing_old_classes: Vec<dep::Variant> = s_map::keys(&missing)
            .into_iter()
            .map(dep::Variant::Type)
            .collect();
        let add_remote_class =
            |mut acc: s_map::T<Option<ShallowClassDecl>>, decl: NamedDecl<R>| match decl {
                NamedDecl::Class(name, cls) => {
                    acc.insert(name.as_str().to_string(), Some(Arc::new(cls)));
                    acc
                }
                NamedDecl::Fun(..)
                | NamedDecl::Typedef(..)
                | NamedDecl::Const(..)
                | NamedDecl::Module(..) => acc,
            };
        let remote_old_classes = remote_old_decl_client::fetch_old_decls(ctx, &missing_old_classes)
            .into_iter()
            .fold(s_map::T::new(), add_remote_class);
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

pub fn get_old_classes_batch(
    ctx: &provider_context::T,
    during_init: bool,
    names: &s_set::T,
) -> s_map::T<Option<ShallowClassDecl>> {
    match ctx.get_backend() {
        // TODO(sf, 2022-10-20): Reduce duplication between the following two cases.
        provider_backend::T::RustProviderBackend | provider_backend::T::SharedMemory => {
            let old_classes = shallow_classes_heap_get_old_batch(ctx, names);
            fetch_missing_old_classes_remotely(ctx, during_init, old_classes)
        }
        provider_backend::T::LocalMemory(_) => {
            panic!("get_old_classes_batch not implemented for Local_memory")
        }
    }
}

/// We only load a decl remotely if the hash we are expecting to have (per
/// [VersionedNames]) matches the hash of the decl in the saved state. That's
/// how we know that the old decl is indeed equivalent to the saved state
/// version. This rules out the case where we didn't find an old decl in the
/// heap because it was evicted, but the decl had changed w.r.t. the saved state
/// prior to being evicted.
fn can_use_saved_state_decl(
    ctx: &provider_context::T,
    dep: &dep::Variant,
    expected_hash: Option<file_info::decl_hash::T>,
) -> bool {
    match (expected_hash, remote_old_decl_client::utils::db_path_of_ctx(ctx)) {
        (Some(expected_hash), Some(db_path)) => {
            match remote_old_decl_client::utils::dep_to_decl_hash_opt(dep, &db_path) {
                None => false,
                Some(saved_hash) => file_info::decl_hash::equal(
                    &expected_hash,
                    &file_info::decl_hash::from_naming_table(
                        crate::rt::ocaml_stdlib::int64_of_string(&saved_hash),
                    ),
                ),
            }
        }
        (None, _) => {
            // We have no reference hash. Conservatively reject fetching an old version
            // for the decl.
            false
        }
        _ => false,
    }
}

/// `fun_decl option S_map.t * typedef_decl option S_map.t * const_decl option
/// S_map.t * module_decl option S_map.t`
type OldNonClasses = (
    s_map::T<Option<FunDecl>>,
    s_map::T<Option<TypedefDecl>>,
    s_map::T<Option<GconstDecl>>,
    s_map::T<Option<ModuleDecl>>,
);

fn fetch_missing_old_non_classes_remotely(
    ctx: &provider_context::T,
    during_init: bool,
    old_names: &file_info::old_names::T,
    old_decls: OldNonClasses,
) -> OldNonClasses {
    if provider_context::get_tcopt(ctx).tco_remote_old_decl_fetching_include_non_class
        && fetch_remote_old_decls(ctx, during_init)
    {
        let (old_funs, old_types, old_consts, old_modules) = &old_decls;
        // `S_map.fold add_missing old_decls deps`: `deps` is a list that is
        // consed to; here the missing deps are pushed, and reversed at the end.
        fn add_missing_deps<A>(
            ctx: &provider_context::T,
            make_dep: impl Fn(String) -> dep::Variant,
            old_hashes: &s_map::T<Option<file_info::decl_hash::T>>,
            old_decls: &s_map::T<Option<A>>,
            deps: &mut Vec<dep::Variant>,
        ) {
            for (name, decl) in old_decls.iter() {
                let expected_hash = old_hashes.get(name).copied().flatten();
                let dep = make_dep(name.clone());
                if decl.is_none() && can_use_saved_state_decl(ctx, &dep, expected_hash) {
                    deps.push(dep)
                }
            }
        }
        let missing_deps = {
            let mut deps = vec![];
            add_missing_deps(ctx, dep::Variant::Fun, &old_names.funs, old_funs, &mut deps);
            add_missing_deps(ctx, dep::Variant::Type, &old_names.types, old_types, &mut deps);
            add_missing_deps(ctx, dep::Variant::GConst, &old_names.consts, old_consts, &mut deps);
            add_missing_deps(ctx, dep::Variant::Module, &old_names.modules, old_modules, &mut deps);
            deps.reverse();
            deps
        };
        let add_remote_old_decl =
            |(mut funs, mut types, mut consts, mut modules): OldNonClasses, decl: NamedDecl<R>| {
                match decl {
                    NamedDecl::Fun(name, decl) => {
                        funs.insert(name.as_str().to_string(), Some(Arc::new(decl)));
                    }
                    NamedDecl::Typedef(name, decl) => {
                        types.insert(name.as_str().to_string(), Some(Arc::new(decl)));
                    }
                    NamedDecl::Const(name, decl) => {
                        consts.insert(name.as_str().to_string(), Some(Arc::new(decl)));
                    }
                    NamedDecl::Module(name, decl) => {
                        modules.insert(name.as_str().to_string(), Some(Arc::new(decl)));
                    }
                    NamedDecl::Class(..) => {}
                }
                (funs, types, consts, modules)
            };
        let remote_old_decls = remote_old_decl_client::fetch_old_decls(ctx, &missing_deps);
        remote_old_decls
            .into_iter()
            .fold(old_decls, add_remote_old_decl)
    } else {
        old_decls
    }
}

/// Remote fallback, when enabled, requires the expected old hash to match
/// the saved-state hash.
pub fn get_old_non_classes_batch(
    ctx: &provider_context::T,
    during_init: bool,
    old_names: &file_info::old_names::T,
    funs: &s_set::T,
    types: &s_set::T,
    consts: &s_set::T,
    modules: &s_set::T,
) -> OldNonClasses {
    let old_decls = {
        // `match Provider_backend.get () with Provider_backend.Rust_provider_backend
        // be -> Rust_provider_backend.Decl.get_old_defs be non_class_defs | _ ->`:
        // the same stores (see the module documentation).
        let names = |names: &s_set::T| names.iter().cloned().collect();
        // The components of the tuple are evaluated from right to left.
        let old_modules = decl_heap::modules::get_old_batch(ctx, &names(modules));
        let old_consts = decl_heap::gconsts::get_old_batch(ctx, &names(consts));
        let old_types = decl_heap::typedefs::get_old_batch(ctx, &names(types));
        let old_funs = decl_heap::funs::get_old_batch(ctx, &names(funs));
        (old_funs, old_types, old_consts, old_modules)
    };
    fetch_missing_old_non_classes_remotely(ctx, during_init, old_names, old_decls)
}

pub fn oldify_classes_batch(ctx: &provider_context::T, names: &s_set::T) {
    match ctx.get_backend() {
        provider_backend::T::RustProviderBackend | provider_backend::T::SharedMemory => {
            // `Shallow_classes_heap.Classes.oldify_batch names`
            ctx.oldify_defs(&classes_only(names))
        }
        provider_backend::T::LocalMemory(_) => {
            panic!("oldify_classes_batch not implemented for Local_memory")
        }
    }
}

pub fn remove_old_classes_batch(ctx: &provider_context::T, names: &s_set::T) {
    match ctx.get_backend() {
        provider_backend::T::RustProviderBackend | provider_backend::T::SharedMemory => {
            // `Shallow_classes_heap.Classes.remove_old_batch names`
            ctx.remove_old_defs(&classes_only(names))
        }
        provider_backend::T::LocalMemory(_) => {
            panic!("remove_old_classes_batch not implemented for Local_memory")
        }
    }
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
