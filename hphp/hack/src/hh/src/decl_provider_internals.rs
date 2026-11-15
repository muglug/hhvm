// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/decl_provider_internals.ml`, for the decl stores of
//! a `Ctx` (the `Shared_memory` branch of each function: the store, then,
//! in the daemon, the lazy parse of the file the name is bound to, which
//! `crate::ctx::LazyStore` does).

use std::sync::Arc;

use pos::ConstName;
use pos::FunName;
use pos::ModuleName;
use pos::TypeName;
use ty::decl::ShallowClass;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_entry;
use crate::decl_provider::*;
use crate::decl_provider::store_result;

pub fn get_fun_without_pessimise(ctx: &Arc<Ctx>, fun_name: &str) -> decl_entry::T<FunDecl> {
    decl_entry::of_option_or_does_not_exist(store_result(
        "get_fun",
        fun_name,
        ctx.shallow_decls.get_fun(FunName(crate::ctx::symbol(fun_name))),
    ))
}

pub fn get_typedef_without_pessimise(
    ctx: &Arc<Ctx>,
    typedef_name: &str,
) -> decl_entry::T<TypedefDecl> {
    // The OCaml (`Shared_memory`) reads the typedef heap of `Decl_store`
    // through the cache local to the worker that shared-memory heaps
    // have: here through the cache of the thread (`cache::typedef`). It
    // reads that heap alone: not the classes first (as
    // `FoldedDeclProvider::get_typedef` does, whose miss of a class
    // asks the naming table, which reads the entries of a context with
    // entries). The stores of a `Ctx` hold the winner of a type name
    // only, so the answers are the same.
    decl_entry::of_option_or_does_not_exist(crate::decl_provider::cache::typedef(ctx, typedef_name, || {
        store_result(
            "get_typedef",
            typedef_name,
            ctx.shallow_decls.get_typedef(TypeName(crate::ctx::symbol(typedef_name))),
        )
    }))
}

pub fn get_gconst(ctx: &Arc<Ctx>, gconst_name: &str) -> Option<GconstDecl> {
    store_result(
        "get_gconst",
        gconst_name,
        ctx.shallow_decls.get_const(ConstName(crate::ctx::symbol(gconst_name))),
    )
}

pub fn get_module(ctx: &Arc<Ctx>, module_name: &str) -> Option<ModuleDecl> {
    store_result(
        "get_module",
        module_name,
        ctx.shallow_decls.get_module(ModuleName(crate::ctx::symbol(module_name))),
    )
}

pub fn get_shallow_class(ctx: &Arc<Ctx>, name: &str) -> Option<Arc<ShallowClass<R>>> {
    store_result(
        "get_shallow_class",
        name,
        ctx.shallow_decls.get_class(TypeName(crate::ctx::symbol(name))),
    )
}
