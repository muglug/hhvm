// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_heap.ml`: the heaps of shared memory of the decls, over
//! the stores of the `Ctx` (see `crate::decl_redecl_service` and
//! `crate::decl_compare`).

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::ctx::Ctx;
use crate::decl_provider::FunDecl;
use crate::decl_provider::GconstDecl;
use crate::decl_provider::ModuleDecl;
use crate::decl_provider::TypedefDecl;
use crate::file_info;
use crate::s_map;
use crate::typing_defs::FunElt;
use crate::typing_defs_core::DeclTy;

/// The names of `kind`, as a `File_info.names` for the `Ctx` primitives.
pub(crate) fn names_of(
    set: impl Fn(&mut file_info::Names) -> &mut BTreeSet<String>,
    names: &BTreeSet<String>,
) -> file_info::Names {
    let mut n = file_info::empty_names();
    *set(&mut n) = names.clone();
    n
}

macro_rules! shallow_heap {
    ($m:ident, $field:ident, $old_field:ident, $ty:ty, $heap:literal, $get:ident, $name:ident) => {
        pub mod $m {
            use super::*;

            /// `get name`
            pub fn get(ctx: &Arc<Ctx>, name: &str) -> Option<$ty> {
                crate::decl_provider::store_result(
                    concat!($heap, ".get"),
                    name,
                    ctx.shallow_decls.$get(pos::$name::new(name)),
                )
            }

            fn names(names: &BTreeSet<String>) -> file_info::Names {
                names_of(|n| &mut n.$field, names)
            }

            pub fn oldify_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
                ctx.oldify_defs(&names(keys))
            }

            pub fn remove_old_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
                ctx.remove_old_defs(&names(keys))
            }

            pub fn remove_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
                ctx.remove_defs(&names(keys))
            }

            pub fn get_old_batch(
                ctx: &Arc<Ctx>,
                keys: &BTreeSet<String>,
            ) -> s_map::T<Option<$ty>> {
                ctx.get_old_defs(&names(keys))
                    .$old_field
                    .into_iter()
                    .collect()
            }
        }
    };
}

shallow_heap!(funs, funs, funs, FunDecl, "Funs", get_fun, FunName);
shallow_heap!(typedefs, types, typedefs, TypedefDecl, "Typedefs", get_typedef, TypeName);
shallow_heap!(gconsts, consts, consts, GconstDecl, "GConsts", get_const, ConstName);
shallow_heap!(modules, modules, modules, ModuleDecl, "Modules", get_module, ModuleName);

/// `Decl_heap.Classes`, the folded classes.
pub mod classes {
    use super::*;

    /// `Decl_heap.Classes.oldify_batch`: the folded classes leave the
    /// store (an old folded class is never read here).
    pub fn oldify_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
        ctx.remove_folded_classes(&keys.iter().cloned().collect())
    }

    /// `Decl_heap.Classes.remove_old_batch`: nothing is kept.
    pub fn remove_old_batch(_ctx: &Arc<Ctx>, _keys: &BTreeSet<String>) {}

    /// `Decl_heap.Classes.remove_batch`
    pub fn remove_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
        ctx.remove_folded_classes(&keys.iter().cloned().collect())
    }

    /// `Decl_heap.Classes.get c`: the folded class of `c` if it is in
    /// the folded store, without folding it.
    pub fn get(ctx: &Arc<Ctx>, c: &str) -> Option<Arc<ty::decl::FoldedClass<crate::ctx::R>>> {
        ctx.get_folded_class_if_present(c)
    }
}

/// The member heaps of `Decl_heap` that `Class_elt_diff` reads (see
/// `crate::decl_compare`): `Shared_mem.Heap` with keys `string * string`
/// (`Decl_heap.ClassEltKey`), and `Decl_heap.Constructors`, keyed by the
/// class name.
/// The part of `Shared_mem.Heap with type key = string * string` that
/// `Class_elt_diff.diff_elts` uses.
pub trait EltHeap {
    type Value;

    fn get_old(key: &(String, String)) -> Option<Self::Value>;

    fn get(key: &(String, String)) -> Option<Self::Value>;
}

pub enum Props {}

pub enum StaticProps {}

pub enum Methods {}

pub enum StaticMethods {}

macro_rules! elt_heap {
    ($heap:ident, $value:ty, $name:literal) => {
        impl EltHeap for $heap {
            type Value = $value;

            fn get_old(key: &(String, String)) -> Option<$value> {
                let _ = key;
                todo!(concat!(
                    "Decl_heap.",
                    $name,
                    ".get_old: the shared-memory member heaps of Decl_heap (and their old versions) have no Rust counterpart: the decl stores of a Ctx have no member heaps, and nothing is oldified"
                ))
            }

            fn get(key: &(String, String)) -> Option<$value> {
                let _ = key;
                todo!(concat!(
                    "Decl_heap.",
                    $name,
                    ".get: the shared-memory member heaps of Decl_heap have no Rust counterpart: the decl stores of a Ctx have no member heaps"
                ))
            }
        }
    };
}

elt_heap!(Props, DeclTy, "Props");
elt_heap!(StaticProps, DeclTy, "StaticProps");
elt_heap!(Methods, FunElt, "Methods");
elt_heap!(StaticMethods, FunElt, "StaticMethods");

/// `Decl_heap.Constructors`
pub mod constructors {
    use super::*;

    pub fn get_old(cid: &str) -> Option<FunElt> {
        let _ = cid;
        todo!(
            "Decl_heap.Constructors.get_old: the shared-memory member heaps of Decl_heap (and their old versions) have no Rust counterpart: the decl stores of a Ctx have no member heaps, and nothing is oldified"
        )
    }

    pub fn get(cid: &str) -> Option<FunElt> {
        let _ = cid;
        todo!(
            "Decl_heap.Constructors.get: the shared-memory member heaps of Decl_heap have no Rust counterpart: the decl stores of a Ctx have no member heaps"
        )
    }
}
