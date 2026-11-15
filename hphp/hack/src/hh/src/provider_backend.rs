// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/provider_backend.ml`: the backend of a context.
//!
//! A `Ctx` has one of three backends ([`T`]):
//!
//! - `Shared_memory`, the backend of `hh_server` and `hh_single_type_check`:
//!   the decl stores and the reverse naming table of the `Ctx`
//!   (`crate::ctx`), which stand for the shared-memory heaps;
//! - `Rust_provider_backend`, the backend of an `hh_server` whose local
//!   config has `rust_provider_backend` (which takes
//!   `shm_use_sharded_hashtbl=true` and `populate_member_heaps=false`, see
//!   `Server_local_config.load`). The OCaml's is a second set of stores, in
//!   Rust (a stub in open source); the stores of this crate are in Rust
//!   whatever the backend, so this one has those of `Shared_memory`, and
//!   differs only where the OCaml asks which backend it has;
//! - `Local_memory`, the backend of the IDE daemon (`clientIdeDaemon`): the
//!   bounded caches of [`LocalMemory`] and the reverse naming table delta
//!   over a SQLite naming table. A `Ctx` made by `Ctx::new_local_memory` has
//!   it.
//!
//! `Pessimised_shared_memory` and `Analysis` (tools of Meta's) are not
//! ported: no command of `hh_server`, `hh_client` or `hh single` uses them.
//! Nor is `Fixme_store`/`Fixmes` of `Local_memory`: the fixme tables of this
//! crate are per thread (`crate::fixme_provider`), which
//! is what one IDE thread needs.
//!
//! # `Decl_cache`
//!
//! The OCaml's `Decl_cache` holds the declarations of functions, typedefs,
//! constants and modules, and the `Typing_class_types.class_t` of the classes
//! `Decl_provider.get_class` returned (`Class_decl`). A `class_t` here holds
//! values that are not `Send` (it is made per thread): it is kept by the
//! per-thread class cache of `crate::decl_provider` (bounded too), which the
//! functions that drop a folded class here clear
//! (`crate::rt::decl_epoch::invalidate_local_caches`). So [`DeclCache`] has
//! no `Class_decl` entries, and its capacity counts the others only.

use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use pos::ConstName;
use pos::FunName;
use pos::ModuleName;
use pos::TypeName;
use ty::decl::ConstDecl;
use ty::decl::FoldedClass;
use ty::decl::FunDecl;
use ty::decl::ShallowClass;
use ty::decl::TypedefDecl;
use ty::decl::shallow::ModuleDecl;

use crate::ctx::R;
use crate::file_info;
use crate::hh_logger;
use crate::lfu_cache;
use crate::lfu_cache::PhysEqual;
use crate::naming_sqlite;
use crate::relative_path::RelativePath;
use crate::telemetry;
use crate::typing_deps;

/// `Decl_cache_entry`: the keys of [`DeclCache`] (a function named `foo`
/// and a class named `foo` are different keys).
pub mod decl_cache_entry {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum Key {
        FunDecl(FunName),
        TypedefDecl(TypeName),
        GconstDecl(ConstName),
        ModuleDecl(ModuleName),
    }

    pub fn key_to_log_string(key: &Key) -> String {
        match key {
            Key::FunDecl(s) => format!("[FunDecl]{}", s.as_str()),
            Key::TypedefDecl(s) => format!("[TypedefDecl]{}", s.as_str()),
            Key::GconstDecl(s) => format!("[GconstDecl]{}", s.as_str()),
            Key::ModuleDecl(s) => format!("[ModuleDecl]{}", s.as_str()),
        }
    }

    /// The values (`'a value` of the GADT): the decls of the stores.
    #[derive(Clone, Debug)]
    pub enum Value {
        Fun(Arc<FunDecl<R>>),
        Typedef(Arc<TypedefDecl<R>>),
        Gconst(Arc<ConstDecl<R>>),
        Module(Arc<ModuleDecl<R>>),
    }

    impl PhysEqual for Value {
        fn phys_equal(&self, other: &Self) -> bool {
            match (self, other) {
                (Value::Fun(a), Value::Fun(b)) => Arc::ptr_eq(a, b),
                (Value::Typedef(a), Value::Typedef(b)) => Arc::ptr_eq(a, b),
                (Value::Gconst(a), Value::Gconst(b)) => Arc::ptr_eq(a, b),
                (Value::Module(a), Value::Module(b)) => Arc::ptr_eq(a, b),
                _ => false,
            }
        }
    }
}

/// `Decl_cache`
pub type DeclCache = lfu_cache::Cache<decl_cache_entry::Key, decl_cache_entry::Value>;

/// `Shallow_decl_cache` (keys `Shallow_class_decl name`)
pub type ShallowDeclCache = lfu_cache::Cache<TypeName, Arc<ShallowClass<R>>>;

/// `Folded_class_cache` (keys `Folded_class_decl name`)
pub type FoldedClassCache = lfu_cache::Cache<TypeName, Arc<FoldedClass<R>>>;

/// `Reverse_naming_table_delta`
pub mod reverse_naming_table_delta {
    use super::*;

    /// `pos`
    pub type Pos = (file_info::NameType, RelativePath);

    /// `pos_or_deleted`: `Pos (winner, others)` (the others are the other
    /// files that declare the name: duplicates), or `Deleted`.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum PosOrDeleted {
        Pos(Pos, Vec<Pos>),
        Deleted,
    }

    /// `pos_or_deleted S_map.t ref`
    pub type Map = Mutex<std::collections::BTreeMap<String, PosOrDeleted>>;

    /// `t`
    #[derive(Debug, Default)]
    pub struct T {
        pub consts: Map,
        pub funs: Map,
        pub types: Map,
        pub modules: Map,
        pub funs_canon_key: Map,
        pub types_canon_key: Map,
    }

    pub fn make() -> T {
        T::default()
    }

    pub fn get_telemetry(key: &str, t: &T, telemetry: telemetry::T) -> telemetry::T {
        let consts = t.consts.lock().unwrap().len();
        let funs = t.funs.lock().unwrap().len();
        let types = t.types.lock().unwrap().len();
        let modules = t.modules.lock().unwrap().len();
        if consts + funs + types + modules == 0 {
            telemetry
        } else {
            let sub_telemetry = telemetry::create();
            let sub_telemetry = telemetry::int_("consts", consts as isize, sub_telemetry);
            let sub_telemetry = telemetry::int_("funs", funs as isize, sub_telemetry);
            let sub_telemetry = telemetry::int_("types", types as isize, sub_telemetry);
            let sub_telemetry = telemetry::int_("modules", modules as isize, sub_telemetry);
            telemetry::object_(key, sub_telemetry, telemetry)
        }
    }
}

/// `local_memory`
pub struct LocalMemory {
    pub shallow_decl_cache: Mutex<ShallowDeclCache>,
    pub folded_class_cache: Mutex<FoldedClassCache>,
    pub decl_cache: Mutex<DeclCache>,
    pub decls_reflect_this_file: Mutex<Option<(RelativePath, file_info::T, file_info::PfhHash)>>,
    pub reverse_naming_table_delta: reverse_naming_table_delta::T,
    pub naming_db_path_ref: Mutex<Option<naming_sqlite::DbPath>>,
    pub dep_table: Mutex<hash::HashMap<typing_deps::dep::T, String>>,
    /// `Provider_context.get_deps_mode` of the contexts of this backend
    /// (`Direct_decl_utils.add_extends_dep_edges` records the extends edges
    /// of the classes it caches in it; the caches have no context of their
    /// own when a lookup of theirs misses).
    pub deps_mode: typing_deps::mode::T,
}

impl std::fmt::Debug for LocalMemory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Provider_backend.Local_memory")
    }
}

/// `t`
#[derive(Clone, Debug)]
pub enum T {
    SharedMemory,
    LocalMemory(Arc<LocalMemory>),
    RustProviderBackend,
}

pub fn t_to_string(t: &T) -> &'static str {
    match t {
        T::SharedMemory => "Shared_memory",
        T::LocalMemory(_) => "Local_memory",
        T::RustProviderBackend => "Rust_provider_backend",
    }
}

/// `backend_ref`, as far as `set_rust_backend` changes it: whether the
/// backend of the process is `Rust_provider_backend` rather than
/// `Shared_memory` (`Ctx::get_backend`).
static BACKEND_REF_IS_RUST_PROVIDER_BACKEND: AtomicBool = AtomicBool::new(false);

/// `set_rust_backend backend` (there is no `Rust_provider_backend.t` to
/// set: see the module doc).
pub fn set_rust_backend() {
    BACKEND_REF_IS_RUST_PROVIDER_BACKEND.store(true, Ordering::Relaxed);
}

/// Whether `set_rust_backend` was called.
pub fn is_rust_backend() -> bool {
    BACKEND_REF_IS_RUST_PROVIDER_BACKEND.load(Ordering::Relaxed)
}

pub fn get_local_memory_telemetry(local_memory: &LocalMemory) -> telemetry::T {
    let telemetry = telemetry::create();
    let telemetry = local_memory
        .shallow_decl_cache
        .lock()
        .unwrap()
        .get_telemetry("shallow_decl_cache", telemetry);
    let telemetry = local_memory
        .decl_cache
        .lock()
        .unwrap()
        .get_telemetry("decl_cache", telemetry);
    local_memory
        .folded_class_cache
        .lock()
        .unwrap()
        .get_telemetry("folded_class_cache", telemetry)
}

/// `set_local_memory_backend_internal` (the record; `Ctx::new_local_memory`
/// makes the context that has it).
pub fn make_local_memory(
    max_num_decls: usize,
    max_num_folded_class_decls: usize,
    max_num_shallow_class_decls: usize,
    deps_mode: typing_deps::mode::T,
) -> LocalMemory {
    LocalMemory {
        decl_cache: Mutex::new(DeclCache::make(max_num_decls)),
        folded_class_cache: Mutex::new(FoldedClassCache::make(max_num_folded_class_decls)),
        shallow_decl_cache: Mutex::new(ShallowDeclCache::make(max_num_shallow_class_decls)),
        decls_reflect_this_file: Mutex::new(None),
        reverse_naming_table_delta: reverse_naming_table_delta::make(),
        naming_db_path_ref: Mutex::new(None),
        dep_table: Mutex::new(hash::HashMap::with_capacity_and_hasher(5000, Default::default())),
        deps_mode,
    }
}

/// `set_local_memory_backend ~max_num_decls ~max_num_folded_class_decls
/// ~max_num_shallow_class_decls`: the log line, then the record.
pub fn set_local_memory_backend(
    max_num_decls: usize,
    max_num_folded_class_decls: usize,
    max_num_shallow_class_decls: usize,
    deps_mode: typing_deps::mode::T,
) -> LocalMemory {
    hh_logger::log(&format!(
        "Provider_backend.Local_memory cache sizes: max_num_decls={} max_num_folded_class_decls={} max_num_shallow_class_decls={}",
        max_num_decls, max_num_folded_class_decls, max_num_shallow_class_decls
    ));
    make_local_memory(
        max_num_decls,
        max_num_folded_class_decls,
        max_num_shallow_class_decls,
        deps_mode,
    )
}

/// `supports_eviction`
pub fn supports_eviction(t: &T) -> bool {
    match t {
        T::LocalMemory(_) | T::RustProviderBackend | T::SharedMemory => true,
    }
}
