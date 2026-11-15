// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_store.ml`. See `hh/PORTING.md`.
//!
//! Abstracts over the particular shared memory implementation used for decl
//! information.
//!
//! # The stores
//!
//! A [`DeclStore`] is a record of functions, as in OCaml, and [`get`] gives
//! the one in use, which [`set`] replaces. It is process wide, as the OCaml
//! `ref` is in a process: the OCaml sets it once, when the provider backend
//! is chosen, before workers start.
//!
//! - [`SHARED_MEMORY_STORE`], the initial store as in OCaml, is made of the
//!   process-wide shared-memory heaps of `Decl_heap`. Here those heaps are
//!   the stores of a `crate::ctx::Ctx`, which no process-wide value holds,
//!   so each of its functions is a `todo!`, as are [`push_local_changes`]
//!   and [`pop_local_changes`].
//! - [`shared_memory_store_of_ctx`] is the store in use: the
//!   `Shared_memory` heaps of the OCaml over the stores of a `Ctx` (for its
//!   shape, `Rust_provider_backend.Decl.decl_store` of
//!   `providers/rust_provider_backend.ml`). The classes, functions,
//!   typedefs, constants and modules are those of the `Ctx` (a class is
//!   folded when it is first asked for, as
//!   `Decl_folded_class.class_decl_if_missing` folds it). Its member heaps
//!   are empty and adding to them does nothing: they are a cache of the
//!   members, which `crate::decl_class` reads from the shallow
//!   decls instead (see `crate::decl_redecl_service`). What uses a `Ctx`
//!   should `set` it.
//!
//! # Types
//!
//! `Decl_defs.decl_class_type` is the folded class as the decl stores keep
//! it, `Arc<ty::decl::FoldedClass<R>>` (as `crate::decl_env::DeclClassType`);
//! a `fun_elt`, `typedef_type`, `const_decl` or `module_def_type` of the
//! decl store is in an `Arc`, as `Ctx` keeps it (`crate::decl_provider`'s
//! `FunDecl`, `TypedefDecl`, `GconstDecl`, `ModuleDecl`); a member is a plain
//! `crate::typing_defs::FunElt` or `DeclTy`.
//!
//! The GADT `('k, 'v) kind` is the trait [`Kind`], whose implementations are
//! its constructors ([`Constructor`], [`Method`], [`StaticMethod`],
//! [`Property`], [`StaticProperty`]); `get kind` and `add kind` (which the
//! `.mli` does not export) are its methods.

use std::sync::Arc;
use std::sync::LazyLock;
use std::sync::RwLock;

use oxidized::s_map::SMap;
use pos::ConstName;
use pos::FunName;
use pos::ModuleName;
use pos::TypeName;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_provider::FunDecl;
use crate::decl_provider::GconstDecl;
use crate::decl_provider::ModuleDecl;
use crate::decl_provider::TypedefDecl;
use crate::typing_defs::FunElt;
use crate::typing_defs_core::DeclTy;

/// `Decl_defs.decl_class_type`, as the decl stores keep it.
pub type DeclClassType = Arc<ty::decl::FoldedClass<R>>;

/// `class_members`
#[derive(Clone, Debug)]
pub struct ClassMembers {
    pub properties: SMap<DeclTy>,
    pub static_properties: SMap<DeclTy>,
    pub methods: SMap<FunElt>,
    pub static_methods: SMap<FunElt>,
    pub constructor: Option<FunElt>,
}

/// `class_entries`
pub type ClassEntries = (DeclClassType, Option<ClassMembers>);

/// `module ClassEltKey = Decl_heap.ClassEltKey`
pub mod class_elt_key {
    use std::cmp::Ordering;

    /// `ClassEltKey.t`: the class that declares the member, and its name.
    pub type T = (String, String);

    pub fn compare((cls1, elt1): &T, (cls2, elt2): &T) -> Ordering {
        let r = cls1.cmp(cls2);
        if r != Ordering::Equal {
            r
        } else {
            elt1.cmp(elt2)
        }
    }

    pub fn to_string((cls, elt): &T) -> String {
        format!("{}::{}", cls, elt)
    }
}

/// `decl_store`
#[derive(Clone)]
pub struct DeclStore {
    pub add_class: Arc<dyn Fn(&str, DeclClassType) + Send + Sync>,
    pub get_class: Arc<dyn Fn(&str) -> Option<DeclClassType> + Send + Sync>,
    pub add_prop: Arc<dyn Fn(&class_elt_key::T, DeclTy) + Send + Sync>,
    pub get_prop: Arc<dyn Fn(&class_elt_key::T) -> Option<DeclTy> + Send + Sync>,
    pub add_static_prop: Arc<dyn Fn(&class_elt_key::T, DeclTy) + Send + Sync>,
    pub get_static_prop: Arc<dyn Fn(&class_elt_key::T) -> Option<DeclTy> + Send + Sync>,
    pub add_method: Arc<dyn Fn(&class_elt_key::T, FunElt) + Send + Sync>,
    pub get_method: Arc<dyn Fn(&class_elt_key::T) -> Option<FunElt> + Send + Sync>,
    pub add_static_method: Arc<dyn Fn(&class_elt_key::T, FunElt) + Send + Sync>,
    pub get_static_method: Arc<dyn Fn(&class_elt_key::T) -> Option<FunElt> + Send + Sync>,
    pub add_constructor: Arc<dyn Fn(&str, FunElt) + Send + Sync>,
    pub get_constructor: Arc<dyn Fn(&str) -> Option<FunElt> + Send + Sync>,
    pub add_fun: Arc<dyn Fn(&str, FunDecl) + Send + Sync>,
    pub get_fun: Arc<dyn Fn(&str) -> Option<FunDecl> + Send + Sync>,
    pub add_typedef: Arc<dyn Fn(&str, TypedefDecl) + Send + Sync>,
    pub get_typedef: Arc<dyn Fn(&str) -> Option<TypedefDecl> + Send + Sync>,
    pub add_gconst: Arc<dyn Fn(&str, GconstDecl) + Send + Sync>,
    pub get_gconst: Arc<dyn Fn(&str) -> Option<GconstDecl> + Send + Sync>,
    pub add_module: Arc<dyn Fn(&str, ModuleDecl) + Send + Sync>,
    pub get_module: Arc<dyn Fn(&str) -> Option<ModuleDecl> + Send + Sync>,
    pub push_local_changes: Arc<dyn Fn() + Send + Sync>,
    pub pop_local_changes: Arc<dyn Fn() + Send + Sync>,
}

impl std::fmt::Debug for DeclStore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("<decl_store>")
    }
}

/// `('k, 'v) kind`
pub trait Kind {
    type K;
    type V;

    /// `get kind`
    fn get(&self, key: &Self::K) -> Option<Self::V>;

    /// `add kind`
    fn add(&self, key: Self::K, v: Self::V);
}

/// `Constructor : (string, Typing_defs.fun_elt) kind`
#[derive(Clone, Copy, Debug)]
pub struct Constructor;

/// `Method : (ClassEltKey.t, Typing_defs.fun_elt) kind`
#[derive(Clone, Copy, Debug)]
pub struct Method;

/// `Static_method : (ClassEltKey.t, Typing_defs.fun_elt) kind`
#[derive(Clone, Copy, Debug)]
pub struct StaticMethod;

/// `Property : (ClassEltKey.t, Typing_defs.decl_ty) kind`
#[derive(Clone, Copy, Debug)]
pub struct Property;

/// `Static_property : (ClassEltKey.t, Typing_defs.decl_ty) kind`
#[derive(Clone, Copy, Debug)]
pub struct StaticProperty;

impl Kind for Constructor {
    type K = String;
    type V = FunElt;

    fn get(&self, key: &String) -> Option<FunElt> {
        let f = STORE.read().unwrap().get_constructor.clone();
        f(key)
    }

    fn add(&self, key: String, v: FunElt) {
        let f = STORE.read().unwrap().add_constructor.clone();
        f(&key, v)
    }
}

impl Kind for Method {
    type K = class_elt_key::T;
    type V = FunElt;

    fn get(&self, key: &class_elt_key::T) -> Option<FunElt> {
        let f = STORE.read().unwrap().get_method.clone();
        f(key)
    }

    fn add(&self, key: class_elt_key::T, v: FunElt) {
        let f = STORE.read().unwrap().add_method.clone();
        f(&key, v)
    }
}

impl Kind for StaticMethod {
    type K = class_elt_key::T;
    type V = FunElt;

    fn get(&self, key: &class_elt_key::T) -> Option<FunElt> {
        let f = STORE.read().unwrap().get_static_method.clone();
        f(key)
    }

    fn add(&self, key: class_elt_key::T, v: FunElt) {
        let f = STORE.read().unwrap().add_static_method.clone();
        f(&key, v)
    }
}

impl Kind for Property {
    type K = class_elt_key::T;
    type V = DeclTy;

    fn get(&self, key: &class_elt_key::T) -> Option<DeclTy> {
        let f = STORE.read().unwrap().get_prop.clone();
        f(key)
    }

    fn add(&self, key: class_elt_key::T, v: DeclTy) {
        let f = STORE.read().unwrap().add_prop.clone();
        f(&key, v)
    }
}

impl Kind for StaticProperty {
    type K = class_elt_key::T;
    type V = DeclTy;

    fn get(&self, key: &class_elt_key::T) -> Option<DeclTy> {
        let f = STORE.read().unwrap().get_static_prop.clone();
        f(key)
    }

    fn add(&self, key: class_elt_key::T, v: DeclTy) {
        let f = STORE.read().unwrap().add_static_prop.clone();
        f(&key, v)
    }
}

pub fn push_local_changes() {
    todo!(
        "Decl_store.push_local_changes: Decl_heap.{{Funs, Constructors, Props, StaticProps, \
         Methods, StaticMethods, Classes, Typedefs, GConsts, Modules}}.LocalChanges.push_stack: \
         the shared-memory decl heaps have no Rust counterpart"
    )
}

pub fn pop_local_changes() {
    todo!(
        "Decl_store.pop_local_changes: Decl_heap.{{Funs, Constructors, Props, StaticProps, \
         Methods, StaticMethods, Classes, Typedefs, GConsts, Modules}}.LocalChanges.pop_stack: \
         the shared-memory decl heaps have no Rust counterpart"
    )
}

/// `shared_memory_store`: the heaps of `Decl_heap`, which have no Rust
/// counterpart.
pub static SHARED_MEMORY_STORE: LazyLock<DeclStore> = LazyLock::new(|| DeclStore {
    add_prop: Arc::new(|_: &class_elt_key::T, _: DeclTy| {
        todo!("Decl_heap.Props.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_prop: Arc::new(|_: &class_elt_key::T| {
        todo!("Decl_heap.Props.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    add_static_prop: Arc::new(|_: &class_elt_key::T, _: DeclTy| {
        todo!("Decl_heap.StaticProps.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_static_prop: Arc::new(|_: &class_elt_key::T| {
        todo!("Decl_heap.StaticProps.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    add_method: Arc::new(|_: &class_elt_key::T, _: FunElt| {
        todo!("Decl_heap.Methods.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_method: Arc::new(|_: &class_elt_key::T| {
        todo!("Decl_heap.Methods.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    add_static_method: Arc::new(|_: &class_elt_key::T, _: FunElt| {
        todo!("Decl_heap.StaticMethods.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_static_method: Arc::new(|_: &class_elt_key::T| {
        todo!("Decl_heap.StaticMethods.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    add_constructor: Arc::new(|_: &str, _: FunElt| {
        todo!("Decl_heap.Constructors.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_constructor: Arc::new(|_: &str| {
        todo!("Decl_heap.Constructors.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    add_class: Arc::new(|_: &str, _: DeclClassType| {
        todo!("Decl_heap.Classes.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_class: Arc::new(|_: &str| {
        todo!("Decl_heap.Classes.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    add_fun: Arc::new(|_: &str, _: FunDecl| {
        todo!("Decl_heap.Funs.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_fun: Arc::new(|_: &str| {
        todo!("Decl_heap.Funs.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    add_typedef: Arc::new(|_: &str, _: TypedefDecl| {
        todo!("Decl_heap.Typedefs.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_typedef: Arc::new(|_: &str| {
        todo!("Decl_heap.Typedefs.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    add_gconst: Arc::new(|_: &str, _: GconstDecl| {
        todo!("Decl_heap.GConsts.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_gconst: Arc::new(|_: &str| {
        todo!("Decl_heap.GConsts.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    add_module: Arc::new(|_: &str, _: ModuleDecl| {
        todo!("Decl_heap.Modules.add: the shared-memory decl heaps have no Rust counterpart")
    }),
    get_module: Arc::new(|_: &str| {
        todo!("Decl_heap.Modules.get: the shared-memory decl heaps have no Rust counterpart")
    }),
    push_local_changes: Arc::new(push_local_changes),
    pop_local_changes: Arc::new(pop_local_changes),
});

/// `let store = ref shared_memory_store`
static STORE: LazyLock<RwLock<DeclStore>> =
    LazyLock::new(|| RwLock::new(SHARED_MEMORY_STORE.clone()));

/// `lookup_or kind key f`, without `~bypass` (the OCaml shadows it).
fn lookup_or_<Kd: Kind>(kind: Kd, key: Kd::K, f: impl FnOnce(&Kd::K) -> Kd::V) -> Kd::V
where
    Kd::V: Clone,
{
    match kind.get(&key) {
        Some(x) => x,
        None => {
            let x = f(&key);
            kind.add(key, x.clone());
            x
        }
    }
}

pub fn lookup_or<Kd: Kind>(
    bypass: bool,
    kind: Kd,
    key: Kd::K,
    f: impl FnOnce(&Kd::K) -> Kd::V,
) -> Kd::V
where
    Kd::V: Clone,
{
    if bypass {
        f(&key)
    } else {
        lookup_or_(kind, key, f)
    }
}

pub fn set(s: DeclStore) {
    *STORE.write().unwrap() = s;
}

pub fn get() -> DeclStore {
    STORE.read().unwrap().clone()
}

/// The decl store over the stores of `ctx`, which stand for the
/// `Shared_memory` heaps (see the module documentation). The stores of a
/// `Ctx` do not fail; this panics if they do.
pub fn shared_memory_store_of_ctx(ctx: Arc<Ctx>) -> DeclStore {
    fn store_result<A, E: std::fmt::Display>(what: &str, name: &str, result: Result<A, E>) -> A {
        // (As a read of shared memory does: see `decl_provider::store_result`.)
        crate::worker_cancel::raise_if_stop_requested();
        match result {
            Ok(x) => x,
            Err(err) => panic!("the decl stores of the context: {} {}: {}", what, name, err),
        }
    }
    ctx.set_installed();
    // Rely on lazy member lookup.
    let ctx_class = Arc::clone(&ctx);
    let ctx_fun = Arc::clone(&ctx);
    let ctx_typedef = Arc::clone(&ctx);
    let ctx_gconst = Arc::clone(&ctx);
    let ctx_module = ctx;
    DeclStore {
        add_prop: Arc::new(|_: &class_elt_key::T, _: DeclTy| ()),
        get_prop: Arc::new(|_: &class_elt_key::T| None),
        add_static_prop: Arc::new(|_: &class_elt_key::T, _: DeclTy| ()),
        get_static_prop: Arc::new(|_: &class_elt_key::T| None),
        add_method: Arc::new(|_: &class_elt_key::T, _: FunElt| ()),
        get_method: Arc::new(|_: &class_elt_key::T| None),
        add_static_method: Arc::new(|_: &class_elt_key::T, _: FunElt| ()),
        get_static_method: Arc::new(|_: &class_elt_key::T| None),
        add_constructor: Arc::new(|_: &str, _: FunElt| ()),
        get_constructor: Arc::new(|_: &str| None),
        add_class: Arc::new(|_: &str, _: DeclClassType| ()),
        get_class: Arc::new(move |name: &str| {
            store_result(
                "get_folded_class",
                name,
                ctx_class.folded_decls.get_class(TypeName::new(name)),
            )
        }),
        add_fun: Arc::new(|_: &str, _: FunDecl| ()),
        get_fun: Arc::new(move |name: &str| {
            store_result(
                "get_fun",
                name,
                ctx_fun.shallow_decls.get_fun(FunName::new(name)),
            )
        }),
        add_typedef: Arc::new(|_: &str, _: TypedefDecl| ()),
        get_typedef: Arc::new(move |name: &str| {
            store_result(
                "get_typedef",
                name,
                ctx_typedef.folded_decls.get_typedef(TypeName::new(name)),
            )
        }),
        add_gconst: Arc::new(|_: &str, _: GconstDecl| ()),
        get_gconst: Arc::new(move |name: &str| {
            store_result(
                "get_gconst",
                name,
                ctx_gconst.shallow_decls.get_const(ConstName::new(name)),
            )
        }),
        add_module: Arc::new(|_: &str, _: ModuleDecl| ()),
        get_module: Arc::new(move |name: &str| {
            store_result(
                "get_module",
                name,
                ctx_module.shallow_decls.get_module(ModuleName::new(name)),
            )
        }),
        // (The stacks of the decl heaps of the process: those of the stores
        // of `ctx`, recorded as the installed ones.)
        pop_local_changes: Arc::new(crate::ctx::pop_decl_local_changes),
        push_local_changes: Arc::new(crate::ctx::push_decl_local_changes),
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use ty::reason::Reason;

    use super::*;

    #[test]
    fn class_elt_keys() {
        let k1 = ("\\A".to_string(), "b".to_string());
        let k2 = ("\\A".to_string(), "c".to_string());
        assert_eq!(class_elt_key::compare(&k1, &k2), Ordering::Less);
        assert_eq!(class_elt_key::compare(&k2, &k2), Ordering::Equal);
        assert_eq!(class_elt_key::to_string(&k1), "\\A::b");
    }

    #[test]
    fn lookup_or_bypass_does_not_touch_the_store() {
        // The initial store is the shared-memory one, whose functions are
        // `todo!`: bypassing it must not call them.
        let key = ("\\A".to_string(), "b".to_string());
        let mut called = false;
        let ty = lookup_or(true, Property, key, |_| {
            called = true;
            ty::decl::Ty::<R>::mixed(R::none())
        });
        assert!(called);
        let _ = ty;
    }
}
