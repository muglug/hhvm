// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_provider.ml`. See `hh/PORTING.md`.
//!
//! Provides decls from the configured backend, e.g. shared memory, local memory, service, etc.
//!
//! The OCaml chooses between five backends (`Provider_context.get_backend`).
//! A `Ctx` has one: the hackrs decl stores (`Ctx::shallow_decls`,
//! `Ctx::folded_decls`), which is what the OCaml calls
//! `Rust_provider_backend`. Only that branch of each function is ported.
//!
//! Two OCaml modules this one is built from have no file in this crate. What
//! is needed of them is ported here, each in a module named after it, ready
//! to be moved to a file of its own:
//!
//! - [`decl_provider_internals`] (`providers/decl_provider_internals.ml`);
//! - [`decl_enforceability_shallow`] (`decl/decl_enforceability_shallow.ml`).
//!
//! None of the functions here records a dependency: as in the OCaml, that is
//! done by the functions of `Typing_env` that wrap them.

use std::sync::Arc;
use std::sync::LazyLock;

use naming_special_names_rust as sn;
use oxidized::ast_defs;
use oxidized::file_info::NameType;
use oxidized::naming_types::KindOfType;
use oxidized::pos::Pos;
use pos::FunName;
use pos::TypeName;
use ty::decl::ConstDecl;
use ty::decl::FoldedClass;
use ty::decl::ShallowClass;
use ty::decl::ty::FunElt;
use ty::decl::ty::ModuleDefType;
use ty::decl::ty::TypedefType;
use ty::reason::Reason;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_entry;
use crate::decl_utils;
use crate::folded_class;
// module Class = Folded_class
use crate::folded_class as class;
use crate::folded_class::ClassElt;
use crate::folded_class::decl_counters;
use crate::folded_class::decl_counters::DeclKind;
use crate::folded_class::decl_counters::TracingInfo;
use crate::folded_class::typing_class_types;

pub type FunKey = String;

pub type TypeKey = String;

pub type GconstKey = String;

pub type ModuleKey = String;

/// `Typing_defs.fun_elt`, as the decl stores hold it.
pub type FunDecl = Arc<FunElt<R>>;

pub type ClassDecl = folded_class::T;

/// `Typing_defs.typedef_type`, as the decl stores hold it.
pub type TypedefDecl = Arc<TypedefType<R>>;

/// `Typing_defs.const_decl`, as the decl stores hold it.
pub type GconstDecl = Arc<ConstDecl<R>>;

/// `Typing_defs.module_def_type`, as the decl stores hold it.
pub type ModuleDecl = Arc<ModuleDefType<R>>;

/// `Naming_provider.get_fun_path`. A `Ctx` has no naming table of its own:
/// its decl stores, which hold every declaration, are the table (see
/// `Ctx::get_fun_canon_name`).
///
/// The daemon's `Ctx` has a reverse naming table (`Ctx::build_dep_hash_index`),
/// and its stores may also hold decls of names bound elsewhere (the
/// OCaml's `cache_decls` keeps the decl of a name with no naming entry,
/// e.g. `class FOO` that lost to `class foo`): these four answer from the
/// naming table then (`crate::naming_provider`), as the OCaml does.
fn naming_provider_get_fun_path(ctx: &Arc<Ctx>, name: &str) -> Option<pos::RelativePath> {
    if ctx.has_reverse_naming_table() {
        return crate::naming_provider::get_fun_path(ctx, name).map(|p| pos::RelativePath::from(&p));
    }
    decl_entry::to_option(decl_provider_internals::get_fun_without_pessimise(
        ctx, name,
    ))
    .map(|decl| decl.pos.file())
}

/// `Naming_provider.get_type_kind`: when a class and a typedef have the same
/// name, the name is that of the class (as for hackrs's
/// `EagerShallowDeclProvider::get_type_kind`, which is what class folding and
/// `FoldedDeclProvider::get_typedef` go by).
fn naming_provider_get_type_kind(ctx: &Arc<Ctx>, name: &str) -> Option<KindOfType> {
    if ctx.has_reverse_naming_table() {
        return crate::naming_provider::get_type_kind(ctx, name);
    }
    let name = TypeName(crate::ctx::symbol(name));
    if store_result(
        "get_class",
        name.as_str(),
        ctx.shallow_decls.get_class(name),
    )
    .is_some()
    {
        Some(KindOfType::TClass)
    } else if store_result(
        "get_typedef",
        name.as_str(),
        ctx.shallow_decls.get_typedef(name),
    )
    .is_some()
    {
        Some(KindOfType::TTypedef)
    } else {
        None
    }
}

/// `Naming_provider.get_typedef_path`
fn naming_provider_get_typedef_path(ctx: &Arc<Ctx>, name: &str) -> Option<pos::RelativePath> {
    if ctx.has_reverse_naming_table() {
        return crate::naming_provider::get_typedef_path(ctx, name).map(|p| pos::RelativePath::from(&p));
    }
    match naming_provider_get_type_kind(ctx, name) {
        Some(KindOfType::TTypedef) => decl_entry::to_option(
            decl_provider_internals::get_typedef_without_pessimise(ctx, name),
        )
        .map(|decl| decl.pos.file()),
        Some(KindOfType::TClass) | None => None,
    }
}

/// `Naming_provider.get_class_path`
fn naming_provider_get_class_path(ctx: &Arc<Ctx>, name: &str) -> Option<pos::RelativePath> {
    if ctx.has_reverse_naming_table() {
        return crate::naming_provider::get_class_path(ctx, name).map(|p| pos::RelativePath::from(&p));
    }
    match naming_provider_get_type_kind(ctx, name) {
        Some(KindOfType::TClass) => {
            decl_provider_internals::get_shallow_class(ctx, name).map(|decl| decl.name.pos().file())
        }
        Some(KindOfType::TTypedef) | None => None,
    }
}

/// What a decl store answered. The stores of a `Ctx` do not fail; the
/// functions of `Rust_provider_backend.Decl` raise when theirs do.
///
/// A store of a `Ctx` stands for a heap of `Decl_heap` in shared memory,
/// whose reads raise `Worker_should_exit` in a worker that the master has
/// asked to stop (`raise_if_should_exit` of `hh_shared.c`).
fn store_result<A, E: std::fmt::Display>(what: &str, name: &str, result: Result<A, E>) -> A {
    crate::worker_cancel::raise_if_stop_requested();
    match result {
        Ok(x) => x,
        Err(err) => panic!("Rust_provider_backend.Decl.{} {}: {}", what, name, err),
    }
}

/// `Rust_provider_backend.Decl.get_folded_class`
fn rust_provider_backend_get_folded_class(
    ctx: &Arc<Ctx>,
    name: &str,
) -> Option<Arc<FoldedClass<R>>> {
    store_result(
        "get_folded_class",
        name,
        ctx.folded_decls.get_class(TypeName(crate::ctx::symbol(name))),
    )
}

pub mod decl_provider_internals {
    //! Port of `decl_provider_internals.ml`, for the decl stores of a `Ctx`
    //! (the branch `Provider_backend.Rust_provider_backend` of each function).

    use pos::ConstName;
    use pos::ModuleName;

    use super::*;

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
        decl_entry::of_option_or_does_not_exist(super::cache::typedef(ctx, typedef_name, || {
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
}

pub mod decl_enforceability_shallow {
    //! Port of `decl_enforceability_shallow.ml`.

    use oxidized::typechecker_options::TypecheckerOptions;
    use pos::BPos;
    use ty::decl::Ty;

    use super::*;
    use crate::decl_enforceability;
    use crate::decl_enforceability::ClassOrTypedefResult;
    use crate::decl_enforceability::FunKind;

    fn is_typedef(ctx: &Arc<Ctx>, x: &str) -> bool {
        match naming_provider_get_type_kind(ctx, x) {
            Some(KindOfType::TTypedef) => true,
            _ => false,
        }
    }

    pub struct Provider;

    impl decl_enforceability::Provider for Provider {
        type T = Arc<Ctx>;

        type ClassT = Arc<ShallowClass<R>>;

        fn get_tcopt(ctx: &Arc<Ctx>) -> &Arc<TypecheckerOptions> {
            // Provider_context.get_tcopt
            &ctx.tco
        }

        fn get_class(ctx: &Arc<Ctx>, name: &str) -> Option<Arc<ShallowClass<R>>> {
            decl_provider_internals::get_shallow_class(ctx, name)
        }

        fn get_class_or_typedef(
            ctx: &Arc<Ctx>,
            x: &str,
        ) -> Option<ClassOrTypedefResult<Arc<ShallowClass<R>>>> {
            if is_typedef(ctx, x) {
                match decl_entry::to_option(decl_provider_internals::get_typedef_without_pessimise(
                    ctx, x,
                )) {
                    None => None,
                    Some(td) => Some(ClassOrTypedefResult::TypedefResult(td)),
                }
            } else {
                match Self::get_class(ctx, x) {
                    None => None,
                    Some(cd) => Some(ClassOrTypedefResult::ClassResult(cd)),
                }
            }
        }
    }

    // module ShallowContextAccess = Decl_enforceability.ShallowContextAccess (Provider)
    type ShallowContextAccess = decl_enforceability::ShallowContextAccess<Provider>;

    // include Decl_enforceability.Pessimize (ShallowContextAccess)

    /// If the return type is not enforceable, turn it into a like type (~ty) otherwise
    /// return the original function type. Also add supportdyn<mixed> to the type parameters.
    pub fn pessimise_fun_type(
        fun_kind: FunKind,
        this_class: Option<&Arc<ShallowClass<R>>>,
        no_auto_likes: bool,
        cannot_override: bool,
        ctx: &Arc<Ctx>,
        p: &BPos,
        ty: &Ty<R>,
    ) -> Ty<R> {
        decl_enforceability::pessimize::pessimise_fun_type::<ShallowContextAccess>(
            fun_kind,
            this_class,
            no_auto_likes,
            cannot_override,
            ctx,
            p,
            ty,
        )
    }
}

/// This cache caches the result of full class computations
/// (the class merged with all its inherited members.)
///
/// `Shared_mem.FreqCache (String_key) (Typing_class_types.class_t)`, of
/// capacity 1000: a cache local to a worker, which is a thread here.
mod cache {
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Weak;

    use super::*;

    const CAPACITY: usize = 1000;

    const FRONT: usize = 512;

    /// An entry of the class cache: its frequency, its value and its key.
    struct Entry {
        freq: std::cell::Cell<usize>,
        value: typing_class_types::ClassT,
        key: Rc<str>,
    }

    fn front_slot(x: &str) -> (usize, usize) {
        let p = x.as_ptr() as usize;
        (p, (p >> 3 ^ p >> 12) & (FRONT - 1))
    }

    struct Cache {
        /// The OCaml has one provider context in a process, and clears the
        /// caches local to a worker when the declarations change
        /// (`Shared_mem.invalidate_local_caches`). A thread can be given
        /// several `Ctx`, whose classes must not be taken for one another:
        /// the cache is that of the `Ctx` it was last used with.
        ///
        /// A `Ctx` is identified by its decl store: the contexts that
        /// `Provider_context.map_tcopt` derives from one another share it,
        /// and so share the cache, as they do in OCaml.
        ctx: Weak<shallow_decl_provider::ShallowDeclStore<R>>,
        cache: hash::HashMap<Rc<str>, Rc<Entry>>,
        /// Not in the OCaml: a direct-mapped table in front of `cache`, by
        /// the address of the name looked up (class names are interned
        /// symbols in declarations, and strings that live as long as their
        /// type in inferred types: the same address is looked up again and
        /// again). An entry is used only if its name is the one looked up, so
        /// a reused address finds nothing wrong; it saves hashing the name.
        front: Vec<Option<(usize, Rc<Entry>)>>,
        /// The handle on the last `Ctx` given to `get_class`, which every
        /// `Folded_class.t` it returns keeps (see [`ctx_handle`]).
        ctx_handle: Option<Rc<Arc<Ctx>>>,
        /// See [`pessimised_typedef`]: by the address of the typedef of the
        /// store, which the entry keeps alive (so the address is not reused).
        pessimised_typedefs: hash::HashMap<usize, (TypedefDecl, TypedefDecl)>,
        /// See [`typedef`].
        typedefs: hash::HashMap<String, TypedefDecl>,
        /// See [`fun_decl`]: the options the entries were made with.
        funs_tco: Option<Arc<oxidized::typechecker_options::TypecheckerOptions>>,
        funs: hash::HashMap<String, FunDecl>,
        /// See [`disposable_class`].
        disposable: hash::HashMap<String, bool>,
        /// Changed whenever what the cache holds for a class is dropped (see
        /// [`generation`]).
        generation: u64,
    }

    thread_local! {
        static CACHE: RefCell<Cache> = RefCell::new(Cache {
            ctx: Weak::new(),
            cache: hash::HashMap::with_capacity_and_hasher(2 * CAPACITY, Default::default()),
            front: vec![None; FRONT],
            ctx_handle: None,
            pessimised_typedefs: hash::HashMap::default(),
            typedefs: hash::HashMap::default(),
            funs_tco: None,
            funs: hash::HashMap::default(),
            disposable: hash::HashMap::default(),
            generation: 0,
        });
    }

    /// `get_fun` (the lookup in the store, then `maybe_pessimise_fun_decl`)
    /// for a function the store has. The OCaml pessimises the declaration
    /// again at each lookup; what it builds depends only on the declaration
    /// (immutable in the store, which never changes what it has found), on
    /// the declarations of the store that the enforcement of its hints reads,
    /// and on the options. So the result is kept per thread, for the store
    /// (see [`use_with`]) and the options it was built with. Each thread has a
    /// copy of its own, so that handing one out does not write a reference
    /// count that all the threads share.
    pub fn fun_decl(
        ctx: &Arc<Ctx>,
        name: &str,
        compute: impl FnOnce() -> decl_entry::T<FunDecl>,
    ) -> decl_entry::T<FunDecl> {
        use_with(ctx);
        if let Some(fun_decl) = CACHE.with_borrow_mut(|c| {
            match &c.funs_tco {
                Some(tco) if Arc::ptr_eq(tco, &ctx.tco) => {}
                _ => {
                    c.funs.clear();
                    c.funs_tco = Some(Arc::clone(&ctx.tco));
                }
            }
            c.funs.get(name).cloned()
        }) {
            return decl_entry::T::Found(fun_decl);
        }
        match compute() {
            decl_entry::T::Found(fun_decl) => {
                // (A declaration pessimised here is already a copy of this
                // thread's.)
                let fun_decl = if Arc::strong_count(&fun_decl) == 1 {
                    fun_decl
                } else {
                    Arc::new(FunElt::clone(&fun_decl))
                };
                CACHE.with_borrow_mut(|c| {
                    if c.funs.len() >= 8 * CAPACITY {
                        c.funs.clear()
                    }
                    c.funs.insert(name.to_string(), Arc::clone(&fun_decl))
                });
                decl_entry::T::Found(fun_decl)
            }
            entry => entry,
        }
    }

    /// The typedefs found in the store of the `Ctx` the cache is that of
    /// (see [`use_with`]; a store never changes what it has found). Each
    /// thread has a copy of its own of each typedef, so that handing one out
    /// does not write the reference count of the typedef of the store, which
    /// all the threads share.
    pub fn typedef(
        ctx: &Arc<Ctx>,
        name: &str,
        lookup: impl FnOnce() -> Option<TypedefDecl>,
    ) -> Option<TypedefDecl> {
        if let Some(typedef_decl) = CACHE.with_borrow_mut(|c| {
            use_with_in(c, ctx);
            c.typedefs.get(name).cloned()
        }) {
            return Some(typedef_decl);
        }
        let typedef_decl = lookup()?;
        let typedef_decl = Arc::new(TypedefType::clone(&typedef_decl));
        CACHE.with_borrow_mut(|c| {
            if c.typedefs.len() >= 8 * CAPACITY {
                c.typedefs.clear()
            }
            c.typedefs.insert(name.to_string(), Arc::clone(&typedef_decl))
        });
        Some(typedef_decl)
    }

    /// `maybe_pessimise_typedef_decl` builds, at every lookup of a typedef,
    /// the same copy of it with another `as` constraint (`{ td with
    /// td_as_constraint = .. }`, a copy of a few pointers in OCaml, and a
    /// deep copy here, whose new decl type goes through the hash-consing
    /// table that all the threads lock). The copy depends on nothing but
    /// the typedef, which is immutable: it is made once per thread for each
    /// typedef (the entry keeps the typedef alive, so that its address
    /// cannot be reused by another).
    pub fn pessimised_typedef(
        typedef_decl: &TypedefDecl,
        pessimise: impl FnOnce() -> TypedefDecl,
    ) -> TypedefDecl {
        let key = Arc::as_ptr(typedef_decl) as usize;
        if let Some(pessimised) = CACHE.with_borrow(|c| {
            c.pessimised_typedefs
                .get(&key)
                .map(|(_, pessimised)| Arc::clone(pessimised))
        }) {
            return pessimised;
        }
        let pessimised = pessimise();
        CACHE.with_borrow_mut(|c| {
            if c.pessimised_typedefs.len() >= 4 * CAPACITY {
                c.pessimised_typedefs.clear()
            }
            c.pessimised_typedefs
                .insert(key, (Arc::clone(typedef_decl), Arc::clone(&pessimised)))
        });
        pessimised
    }

    /// Not in the OCaml: whether the class `name` of the store of `ctx` is
    /// disposable (`Typing_disposable.is_disposable_class`), which the OCaml
    /// computes again at each class of each type it looks at (the return type
    /// of every call). The answer depends only on the folded declarations of
    /// the class and of the classes it requires (all of the store of `ctx`,
    /// which never changes what it has found): it is kept for the store, as
    /// the classes are. `compute` gives `None` when the class does not exist
    /// (not kept).
    pub fn disposable_class(
        ctx: &Arc<Ctx>,
        name: &str,
        compute: impl FnOnce() -> Option<bool>,
    ) -> Option<bool> {
        if let Some(b) = CACHE.with_borrow_mut(|c| {
            use_with_in(c, ctx);
            c.disposable.get(name).copied()
        }) {
            return Some(b);
        }
        let b = compute()?;
        CACHE.with_borrow_mut(|c| {
            if c.disposable.len() >= 16 * CAPACITY {
                c.disposable.clear()
            }
            c.disposable.insert(name.to_string(), b)
        });
        Some(b)
    }

    /// A number that changes whenever the cache drops what it knew of the
    /// classes of a store (another store, a class removed): what is computed
    /// from the classes of the store of `ctx` alone, and kept elsewhere, is
    /// valid as long as the number has not changed.
    pub fn generation(ctx: &Arc<Ctx>) -> u64 {
        CACHE.with_borrow_mut(|c| {
            use_with_in(c, ctx);
            c.generation
        })
    }

    /// A handle on `ctx` that the thread shares: copying it into each class
    /// that `get_class` returns writes no reference count that other threads
    /// write too (`Arc::clone` of the context does, and all the threads
    /// look classes up all the time).
    pub fn ctx_handle(ctx: &Arc<Ctx>) -> Rc<Arc<Ctx>> {
        CACHE.with_borrow_mut(|c| match &c.ctx_handle {
            Some(handle) if Arc::ptr_eq(handle, ctx) => Rc::clone(handle),
            _ => {
                let handle = Rc::new(Arc::clone(ctx));
                c.ctx_handle = Some(Rc::clone(&handle));
                handle
            }
        })
    }

    /// Clear the cache if it was last used with another `Ctx`.
    pub fn use_with(ctx: &Arc<Ctx>) {
        CACHE.with_borrow_mut(|c| use_with_in(c, ctx))
    }

    /// [`use_with`], in a borrow of the cache that the caller has.
    fn use_with_in(c: &mut Cache, ctx: &Arc<Ctx>) {
        if !std::ptr::eq(c.ctx.as_ptr(), Arc::as_ptr(&ctx.shallow_decls)) {
            clear(c);
            c.ctx = Arc::downgrade(&ctx.shallow_decls);
        }
    }

    /// Drop everything the cache holds (what it knows of the classes too:
    /// the generation changes).
    fn clear(c: &mut Cache) {
        c.cache.clear();
        c.front.iter_mut().for_each(|e| *e = None);
        c.pessimised_typedefs.clear();
        c.typedefs.clear();
        c.funs.clear();
        c.disposable.clear();
        c.generation += 1;
    }

    /// `Shared_mem.invalidate_local_caches` for this thread (see
    /// `crate::rt::decl_epoch`): the declarations of the store may have
    /// changed in place, so nothing found before is kept, and the cache is
    /// that of no `Ctx` (nor holds one) until it is used again.
    pub fn forget_thread_memos() {
        CACHE.with_borrow_mut(|c| {
            clear(c);
            c.ctx = Weak::new();
            c.ctx_handle = None;
            c.funs_tco = None;
        })
    }

    /// The collection function is called when we reach twice original
    /// capacity in size. When the collection is triggered, we only keep
    /// the most frequently used objects.
    /// So before collection: size = 2 * capacity
    /// After collection: size = capacity (with the most frequently
    /// used objects)
    fn collect(c: &mut Cache) {
        let cache = &mut c.cache;
        if cache.len() < 2 * CAPACITY {
        } else {
            c.front.iter_mut().for_each(|e| *e = None);
            let mut l: Vec<(Rc<str>, usize, Rc<Entry>)> = cache
                .drain()
                .map(|(key, e)| (key, e.freq.get(), e))
                .collect();
            l.sort_by(|(_, x, _), (_, y, _)| y.cmp(x));
            for (k, _freq, e) in l.into_iter().take(CAPACITY) {
                e.freq.set(0);
                cache.insert(k, e);
            }
        }
    }

    pub fn add(x: &str, y: typing_class_types::ClassT) {
        CACHE.with_borrow_mut(|c| {
            collect(c);
            match c.cache.get_mut(x) {
                Some(e) => {
                    e.freq.set(e.freq.get() + 1);
                    if Rc::ptr_eq(&e.value.0, &y.0) && Rc::ptr_eq(&e.value.1, &y.1) {
                    } else {
                        let key = Rc::clone(&e.key);
                        let freq = e.freq.get();
                        *e = Rc::new(Entry {
                            freq: std::cell::Cell::new(freq),
                            value: y,
                            key,
                        });
                        c.front.iter_mut().for_each(|e| *e = None);
                    }
                }
                None => {
                    let key: Rc<str> = Rc::from(x);
                    c.cache.insert(
                        Rc::clone(&key),
                        Rc::new(Entry {
                            freq: std::cell::Cell::new(0),
                            value: y,
                            key,
                        }),
                    );
                }
            }
        })
    }

    /// `use_with ctx`, then `get x` and, if found, `ctx_handle ctx`: what
    /// `get_class` does on a hit, in one access to the thread's cache.
    pub fn get_for(
        ctx: &Arc<Ctx>,
        x: &str,
    ) -> Option<(typing_class_types::ClassT, Rc<Arc<Ctx>>)> {
        CACHE.with_borrow_mut(|c| {
            if !std::ptr::eq(c.ctx.as_ptr(), Arc::as_ptr(&ctx.shallow_decls)) {
                return None;
            }
            let handle = match &c.ctx_handle {
                Some(handle) if Arc::ptr_eq(handle, ctx) => Rc::clone(handle),
                _ => return None,
            };
            let (p, slot) = front_slot(x);
            if let Some((p1, e)) = &c.front[slot] {
                if *p1 == p && &*e.key == x {
                    e.freq.set(e.freq.get() + 1);
                    return Some((e.value.clone(), handle));
                }
            }
            match c.cache.get(x) {
                None => None,
                Some(e) => {
                    e.freq.set(e.freq.get() + 1);
                    let value = e.value.clone();
                    c.front[slot] = Some((p, Rc::clone(e)));
                    Some((value, handle))
                }
            }
        })
    }

    pub fn get(x: &str) -> Option<typing_class_types::ClassT> {
        CACHE.with_borrow_mut(|c| match c.cache.get(x) {
            None => None,
            Some(e) => {
                e.freq.set(e.freq.get() + 1);
                Some(e.value.clone())
            }
        })
    }

    pub fn remove(x: &str) {
        CACHE.with_borrow_mut(|c| {
            c.cache.remove(x);
            c.front.iter_mut().for_each(|e| *e = None);
            // (Whether another class is disposable may depend on this one.)
            c.disposable.clear();
            c.generation += 1;
        })
    }
}

/// See [`cache::forget_thread_memos`] (called by `crate::rt::decl_epoch`).
pub fn forget_thread_memos() {
    cache::forget_thread_memos()
}

/// See [`cache::generation`].
pub fn class_cache_generation(ctx: &Arc<Ctx>) -> u64 {
    cache::generation(ctx)
}

/// See [`cache::disposable_class`].
pub fn disposable_class_memo(
    ctx: &Arc<Ctx>,
    name: &str,
    compute: impl FnOnce() -> Option<bool>,
) -> Option<bool> {
    cache::disposable_class(ctx, name, compute)
}

/// `Decl_defs.raise_decl_not_found`: `exception Decl_not_found of string` is
/// a panic.
///
/// `Relative_path.to_absolute` reads the roots of the paths from global
/// state: they are in the `Ctx`.
fn raise_decl_not_found(ctx: &Arc<Ctx>, path: Option<pos::RelativePath>, name: &str) -> ! {
    // `Hack_event_logger.decl_consistency_bug` and `Hh_logger.log` only log.
    let err_str = format!(
        "{} not found in {}",
        name,
        match path {
            None => "_".to_string(),
            Some(path) => path.to_absolute(&ctx.path_ctx).display().to_string(),
        }
    );
    panic!("Decl_defs.Decl_not_found({:?})", err_str)
}

/// The OCaml also returns `Decl_store.class_members option`, the types of
/// the members of the class for the member heaps, which do not exist here
/// (see `folded_class::decl_class`).
fn declare_folded_class(ctx: &Arc<Ctx>, name: &str) -> Arc<FoldedClass<R>> {
    let f = || {
        match crate::diagnostics_state::run_in_decl_mode(|| {
            // `Decl_folded_class.class_decl_if_missing`: hackrs's
            // `LazyFoldedDeclProvider` folds the class if its store does not
            // have it.
            rust_provider_backend_get_folded_class(ctx, name)
        }) {
            None => raise_decl_not_found(ctx, None, name),
            Some(decl_and_members) => decl_and_members,
        }
    };
    // `Provider_backend.Local_memory` prefetches the decls the fold needs.
    f()
}

pub fn lookup_or_populate_class_cache(
    class_name: &str,
    populate: impl FnOnce(&str) -> Option<typing_class_types::ClassT>,
) -> Option<typing_class_types::ClassT> {
    match cache::get(class_name) {
        Some(result) => Some(result),
        None => match populate(class_name) {
            None => None,
            Some(v) => {
                cache::add(class_name, v.clone());
                Some(v)
            }
        },
    }
}

/// Direct use of `get_class` will not register a dependency. You probably
/// want to use `Typing_env.get_class` instead
pub fn get_class(
    tracing_info: Option<&TracingInfo>,
    ctx: &Arc<Ctx>,
    class_name: &str,
) -> decl_entry::T<ClassDecl> {
    decl_counters::count_decl(tracing_info, DeclKind::Class, class_name, |counter| {
        // There are several possibilities:
        // LOCAL BACKEND - the class_t is cached in the local backend.
        // SHAREDMEM BACKEND - the class_t is cached in the worker-local 'Cache' heap.
        //   Note that in the case of eager, the class_t is really just a fairly simple
        //   derivation of the decl_class_type that lives in shmem.
        // DECL BACKEND - the class_t is cached in the worker-local 'Cache' heap
        // The usual case, a class in the cache, first (the same as the
        // general case below, with one access to the cache).
        if let Some((v, handle)) = cache::get_for(ctx, class_name) {
            return decl_entry::T::Found(folded_class::T(counter, folded_class::make(v), Some(handle)));
        }
        cache::use_with(ctx);
        let entry = match lookup_or_populate_class_cache(class_name, |class_name| {
            rust_provider_backend_get_folded_class(ctx, class_name)
                .map(typing_class_types::make_class_t)
        }) {
            None => decl_entry::T::DoesNotExist,
            Some(v) => decl_entry::T::Found((counter, v, Some(cache::ctx_handle(ctx)))),
        };
        decl_entry::map(entry, |(counter, v, ctx)| {
            folded_class::T(counter, folded_class::make(v), ctx)
        })
    })
}

/// `remove_classes_from_decl_heap names ~old_members ~new_members`: the
/// member heaps (`Decl_class_elements`) have no counterpart (their entries are
/// recomputed from the shallow decls on a miss, as the members of a folded
/// class of the `Ctx` always are), and an old folded class is never kept
/// (see `decl_redecl_service::decl_heap`): what is left is
/// `Decl_heap.Classes.remove_batch names`, the folded classes.
fn remove_classes_from_decl_heap<DeclClassElements>(
    ctx: &Arc<Ctx>,
    names: &im::OrdSet<String>,
    old_members: &im::OrdMap<String, DeclClassElements>,
    new_members: &im::OrdMap<String, DeclClassElements>,
) {
    // `Decl_class_elements.remove_old_all old_members`,
    // `Decl_class_elements.remove_all new_members`: nothing to drop.
    let _ = (old_members, new_members);
    // `Decl_heap.Classes.remove_old_batch names`: nothing is kept.
    // `Decl_heap.Classes.remove_batch names`
    ctx.remove_folded_classes(names)
}

/// `remove_classes ctx names ~old_members ~new_members`, the branch of the
/// `Shared_memory` backend (the OCaml daemon's: `rust_provider_backend` is
/// turned off at startup since `shm_use_sharded_hashtbl` is false): the
/// classes leave the class cache (of this thread, see [`cache`]), then their
/// folded classes and member-heap entries are dropped. Their shallow decls
/// stay.
///
/// `Decl_class_elements.t`, which has no module in this crate, is a type
/// parameter (`decl_redecl_service::Elems` holds nothing).
pub fn remove_classes<DeclClassElements, F1, F2>(
    ctx: &Arc<Ctx>,
    names: &im::OrdSet<String>,
    old_members: &LazyLock<im::OrdMap<String, DeclClassElements>, F1>,
    new_members: &LazyLock<im::OrdMap<String, DeclClassElements>, F2>,
) where
    F1: FnOnce() -> im::OrdMap<String, DeclClassElements>,
    F2: FnOnce() -> im::OrdMap<String, DeclClassElements>,
{
    // `match Provider_context.get_backend ctx with ... | Provider_backend.Shared_memory ->`
    // `S_set.iter Cache.remove names`
    cache::use_with(ctx);
    for name in names {
        cache::remove(name)
    }
    // The labelled arguments are evaluated from right to left: `new_members`
    // is forced first.
    let new_members = LazyLock::force(new_members);
    let old_members = LazyLock::force(old_members);
    remove_classes_from_decl_heap(ctx, names, old_members, new_members)
}

/// `Provider_context.implicit_sdt_for_fun`
fn implicit_sdt_for_fun(ctx: &Arc<Ctx>, fe: &FunElt<R>) -> bool {
    ctx.tco.po.everything_sdt && !fe.no_auto_dynamic
}

/// `Provider_context.no_auto_likes_for_fun`
fn no_auto_likes_for_fun(fe: &FunElt<R>) -> bool {
    fe.no_auto_likes
}

fn maybe_pessimise_fun_decl(ctx: &Arc<Ctx>, fun_decl: FunDecl) -> FunDecl {
    if implicit_sdt_for_fun(ctx, &fun_decl) {
        let no_auto_likes = no_auto_likes_for_fun(&fun_decl);
        Arc::new(FunElt {
            ty: decl_enforceability_shallow::pessimise_fun_type(
                crate::decl_enforceability::FunKind::Function,
                None,
                no_auto_likes,
                true,
                ctx,
                &fun_decl.pos,
                &fun_decl.ty,
            ),
            ..(*fun_decl).clone()
        })
    } else {
        fun_decl
    }
}

fn maybe_pessimise_typedef_decl(ctx: &Arc<Ctx>, typedef_decl: TypedefDecl) -> TypedefDecl {
    if ctx.tco.po.everything_sdt
        && !decl_utils::attributes_mem(
            sn::user_attributes::NO_AUTO_DYNAMIC,
            &typedef_decl.attributes,
        )
    {
        // TODO: deal with super constraint
        match &typedef_decl.as_constraint {
            Some(_) => typedef_decl,
            None => {
                cache::pessimised_typedef(&typedef_decl, || {
                    let pos = &typedef_decl.pos;
                    Arc::new(TypedefType {
                        as_constraint: Some(crate::decl_enforceability::supportdyn_mixed(
                            pos,
                            &R::witness_from_decl(pos.clone()),
                        )),
                        ..(*typedef_decl).clone()
                    })
                })
            }
        }
    } else {
        typedef_decl
    }
}

/// Direct use of `get_fun` will not register a dependency. You probably want
/// to use `Typing_env.get_fun` instead
pub fn get_fun(
    tracing_info: Option<&TracingInfo>,
    ctx: &Arc<Ctx>,
    name: &str,
) -> decl_entry::T<FunDecl> {
    decl_counters::count_decl(tracing_info, DeclKind::Fun, name, |_counter| {
        cache::fun_decl(ctx, name, || {
            decl_entry::map(
                decl_provider_internals::get_fun_without_pessimise(ctx, name),
                |fun_decl| maybe_pessimise_fun_decl(ctx, fun_decl),
            )
        })
    })
}

/// Return the shallow declaration of the class with the given name if it is
/// present in the cache. Otherwise, compute it, store it in the cache, and
/// return it.
pub fn get_shallow_class(ctx: &Arc<Ctx>, name: &str) -> Option<Arc<ShallowClass<R>>> {
    decl_provider_internals::get_shallow_class(ctx, name)
}

/// Direct use of `get_typedef` will not register a dependency. You probably
/// want to use `Typing_env.get_typedef` instead
pub fn get_typedef(
    tracing_info: Option<&TracingInfo>,
    ctx: &Arc<Ctx>,
    name: &str,
) -> decl_entry::T<TypedefDecl> {
    decl_counters::count_decl(tracing_info, DeclKind::Typedef, name, |_counter| {
        decl_entry::map(
            decl_provider_internals::get_typedef_without_pessimise(ctx, name),
            |typedef_decl| maybe_pessimise_typedef_decl(ctx, typedef_decl),
        )
    })
}

/// Direct use of `get_gconst` will not register a dependency. You probably
/// want to use `Typing_env.get_gconst` instead
pub fn get_gconst(
    tracing_info: Option<&TracingInfo>,
    ctx: &Arc<Ctx>,
    name: &str,
) -> Option<GconstDecl> {
    decl_counters::count_decl(tracing_info, DeclKind::GConst, name, |_counter| {
        decl_provider_internals::get_gconst(ctx, name)
    })
}

/// Direct use of `get_module` will not register a dependency. You probably
/// want to use `Typing_env.get_module` instead
pub fn get_module(
    tracing_info: Option<&TracingInfo>,
    ctx: &Arc<Ctx>,
    name: &str,
) -> Option<ModuleDecl> {
    decl_counters::count_decl(tracing_info, DeclKind::Module_decl, name, |_counter| {
        decl_provider_internals::get_module(ctx, name)
    })
}

/// This assumes that [class_name] defines and overrides [method_name]
/// and returns the method from an ancestor or trait of [class_name] that would
/// have been inherited by [class_name] had it not overridden it.
pub fn get_overridden_method(
    ctx: &Arc<Ctx>,
    class_name: &str,
    method_name: &str,
    is_static: bool,
) -> decl_entry::T<ClassElt> {
    decl_entry::bind(get_class(None, ctx, class_name), |cls| {
        let get_class = |ctx: &Arc<Ctx>, x: &str| decl_entry::to_option(get_class(None, ctx, x));
        decl_entry::of_option_or_does_not_exist(class::overridden_method(
            &cls,
            method_name,
            is_static,
            get_class,
        ))
    })
}

/// This is a subtle function! If there is a winner defined for [name_type / name]
/// with that exact same capitalization, then it will return its position, otherwise
/// it will return None.
///
/// Example: [type t=int; type T=string;] where "t=int" is the winner.
/// * [get_pos_from_decl_of_winner Typedef "t"] --> Some
/// * [get_pos_from_decl_of_winner Typedef "T"] --> None
/// * [get_pos_from_decl_of_winner Class "T"] --> None
///
/// Example: [type tc=int; class tc {}] where "class tc" is the winner.
/// * [get_pos_from_decl_of_winner Class "tc"] --> Some
/// * [get_pos_from_decl_of_winner Typedef "tc"] --> None
/// * [get_pos_from_decl_of_winner Class "TC"] --> None
///
/// Why such a subtle function? We're trying to thread the needle between what's
/// efficient to obtain from the decl-provider without needing a costly
/// step of "obtain the canonical capitalization of this symbol", vs what's the
/// minimum correctness needed to support the function [is_this_def_the_winner].
///
/// Several branches of this function must first query Naming_provider
/// before it's safe to go on and query Decl_provider.
///
/// Internal helper used by [is_this_def_the_winner].
/// Exposed solely for testing in hh_single_decl; must not be used elsewhere
#[allow(non_snake_case)]
pub fn get_pos_from_decl_of_winner_FOR_TESTS_ONLY(
    ctx: &Arc<Ctx>,
    name_type: NameType,
    name: &str,
) -> Option<Pos> {
    // The positions of hackrs decls are `BPos`: each branch gives the `Pos`.
    let pos_opt: Option<Pos> = match name_type {
        NameType::Fun => {
            if naming_provider_get_fun_path(ctx, name).is_some() {
                decl_entry::to_option(get_fun(None, ctx, name)).map(|fe| Pos::from(fe.pos.clone()))
            } else {
                None
            }
        }
        NameType::Typedef => {
            if naming_provider_get_typedef_path(ctx, name).is_some() {
                decl_entry::to_option(get_typedef(None, ctx, name))
                    .map(|td| Pos::from(td.pos.clone()))
            } else {
                None
            }
        }
        NameType::Class => {
            if naming_provider_get_class_path(ctx, name).is_some() {
                decl_entry::to_option(get_class(None, ctx, name)).map(|cls| class::pos(&cls))
            } else {
                None
            }
        }
        NameType::Const => get_gconst(None, ctx, name).map(|cd| Pos::from(cd.pos.clone())),
        NameType::Module => get_module(None, ctx, name).map(|mdt| Pos::from(mdt.pos.clone())),
    };
    // `Pos_or_decl.unsafe_to_raw_pos` is the identity: `PosOrDecl` is `Pos`.
    pos_opt
}

/// Return type for [is_this_def_the_winner]
#[allow(non_camel_case_types)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Winner {
    /// yes it is the winner
    Winner,
    /// a different definition is the winner
    Loser_to(Pos),
    /// there is no winning definition for [name_type / name]
    Not_found,
}

/// `Pos.overlaps`, which `oxidized::pos::Pos` does not have.
fn pos_overlaps(pos1: &Pos, pos2: &Pos) -> bool {
    let (start1, end1) = pos1.info_raw();
    let (start2, end2) = pos2.info_raw();
    pos1.filename() == pos2.filename() && end1 > start2 && start1 < end2
}

/// [is_this_def_the_winner ctx name_kind (pos, name)] judges whether the
/// the definition at [name / name_kind / pos] is deemed the "winner" in the naming table.
/// Normally when a symbol is defined only once, then it is the winner. But if a name is
/// defined multiple times (maybe differing in case), then only one of those definitions
/// is the winner, be they in the same file or different. Examples:
/// * [type tc=int; class tc {}] - these conflict, and only one may be deemed the winner
/// * [type t=int; type T=string;] - these conflict, and only one may be deemed the winner
///
/// Most other functions e.g. [Decl_provider.get_typedef] are not sensitive to winners,
/// and will happily return information about losers if so requested!
///
/// This function returns [Winner] if the supplied definition is the winner,
/// or [Loser_to winner_pos] it it isn't the winner, or [Not_found] if there's no winner
/// for any capitalization of [name] in category [name_type] (nor, in the case of Class/Typedef,
/// in the other category].
pub fn is_this_def_the_winner(ctx: &Arc<Ctx>, name_type: NameType, id: &ast_defs::Id) -> Winner {
    let ast_defs::Id(pos, name) = id;
    match (
        get_pos_from_decl_of_winner_FOR_TESTS_ONLY(ctx, name_type, name),
        name_type,
    ) {
        (Some(winner_pos), _) if pos_overlaps(pos, &winner_pos) => {
            // There is a winner decl for [name_type name], the exact same name_type and capitalization
            // as we provided, and its position overlaps. Therefore [name_type / name / pos] is the winner!
            // The winner for [name_type / name] has the exact same capitalization and name_type,
            // We use "overlaps" to allow flexibility for whether the
            // pos associated with the AST refers to the pos of the identifier token or the pos of the whole
            // thing, and likewise the pos associated the decl.
            Winner::Winner
        }
        (Some(winner_pos), _) => {
            // There is a winner decl for [name_type name], the exact same name_type and capitalization
            // as we provided, but it is at a different position. Therefore we are the loser.
            Winner::Loser_to(winner_pos)
        }
        (None, NameType::Const | NameType::Module) => {
            // There is no winner decl for [name_type name]. These name-types are case-sensitive,
            // so we don't need to look further.
            Winner::Not_found
        }
        (None, NameType::Fun) => {
            // If there wasn't a winner decl for [Fun name], then maybe there is for a different
            // capitalization of [Name]? Note: this codepath results in either [Not_found] or [Loser_to],
            // neither of which occur in a program that typechecks clean, so it's okay if they're a little slow.
            // It technically has one path which returns [Winner] but we believe and assert that it will never arise.
            match ctx.get_fun_canon_name(name) {
                None => Winner::Not_found,
                Some(cname) => {
                    match get_pos_from_decl_of_winner_FOR_TESTS_ONLY(ctx, name_type, cname.as_str())
                    {
                        None => Winner::Not_found,
                        Some(winner_pos) if pos_overlaps(pos, &winner_pos) => {
                            // `Hack_event_logger.invariant_violation_bug` only logs:
                            // "caller provided wrong capitalization of fun name (unnecessarily slow path; should avoid)"
                            Winner::Winner
                        }
                        Some(winner_pos) => Winner::Loser_to(winner_pos),
                    }
                }
            }
        }
        (None, NameType::Class | NameType::Typedef) => {
            // If there wasn't a winner decl for [name_type name], then maybe there is a winning
            // decl for a different capitalization of [name]? or for the other [name_type]?
            // Note: this codepath results in either [Not_found] or [Loser_to], niether of which
            // occur in a program that typechecks clean, so it's okay if they're a little slow.
            // It technically has one path which returns [Winner] but we believe and assert that it will never arise.
            match ctx.get_type_canon_name(name) {
                None => Winner::Not_found,
                Some(cname) => {
                    // `Option.first_some` is given both.
                    let winner_pos_class = get_pos_from_decl_of_winner_FOR_TESTS_ONLY(
                        ctx,
                        NameType::Class,
                        cname.as_str(),
                    );
                    let winner_pos_typedef = get_pos_from_decl_of_winner_FOR_TESTS_ONLY(
                        ctx,
                        NameType::Typedef,
                        cname.as_str(),
                    );
                    let winner_pos_opt = winner_pos_class.or(winner_pos_typedef);
                    match winner_pos_opt {
                        None => Winner::Not_found,
                        Some(winner_pos) if pos_overlaps(pos, &winner_pos) => {
                            // `Hack_event_logger.decl_consistency_bug` only logs:
                            // "caller provided wrong capitalization of type name (unnecessarily slow path; should avoid)"
                            Winner::Winner
                        }
                        Some(winner_pos) => Winner::Loser_to(winner_pos),
                    }
                }
            }
        }
    }
}

pub fn local_changes_push_sharedmem_stack() {
    todo!(
        "Shallow_classes_heap.Classes.LocalChanges.push_stack, Decl_store.push_local_changes: the decl stores of Ctx have no stack of local changes"
    )
}

pub fn local_changes_pop_sharedmem_stack() {
    todo!(
        "Shallow_classes_heap.Classes.LocalChanges.pop_stack, Decl_store.pop_local_changes: the decl stores of Ctx have no stack of local changes"
    )
}

#[allow(non_snake_case)]
pub fn declare_folded_class_in_file_FOR_TESTS_ONLY(
    ctx: &Arc<Ctx>,
    cid: &str,
) -> Arc<FoldedClass<R>> {
    declare_folded_class(ctx, cid)
}

#[cfg(test)]
pub(crate) mod testing {
    use std::path::Path;

    use oxidized::typechecker_options::TypecheckerOptions;
    use pos::Prefix;
    use pos::RelativePath;

    use super::*;
    use crate::check;

    /// A `Ctx` over the hhi files and one file given in memory, declared as
    /// `hh single` declares them.
    pub fn ctx_of(src: &str, tco: TypecheckerOptions) -> Arc<Ctx> {
        let ctx = Ctx::new(Path::new("/"), tco).unwrap();
        let path = RelativePath::new(Prefix::Root, "test.php");
        ctx.files.set(path, src);
        let mut decl_paths = ctx.hhi_paths.clone();
        decl_paths.push(path);
        check::declare_files(&ctx, &decl_paths, &mut check::Stats::default());
        Arc::new(ctx)
    }

    /// The class `name`, which must exist.
    pub fn class(ctx: &Arc<Ctx>, name: &str) -> ClassDecl {
        match get_class(None, ctx, name) {
            decl_entry::T::Found(cls) => cls,
            entry => panic!("{}: {:?}", name, entry),
        }
    }
}

#[cfg(test)]
mod tests {
    use oxidized::typechecker_options::TypecheckerOptions;
    use ty::decl::ty::TypedefTypeAssignment;

    use super::testing::*;
    use super::*;

    const SRC: &str = r#"<?hh
new module some.mod {}

class C {
  public function m(): int { return 1; }
}

type Alias<T> = dict<string, T>;

newtype Opaque as arraykey = int;

<<__NoAutoDynamic>>
type NoAuto = int;

const int GCONST = 3;

function top<T>(T $x, int $y): int { return $y; }

<<__NoAutoDynamic>>
function top_no_auto<T>(T $x, int $y): int { return $y; }
"#;

    fn ctx() -> Arc<Ctx> {
        ctx_of(SRC, TypecheckerOptions::default())
    }

    fn ctx_sdt() -> Arc<Ctx> {
        let mut tco = TypecheckerOptions::default();
        tco.po.everything_sdt = true;
        ctx_of(SRC, tco)
    }

    #[test]
    fn classes() {
        let ctx = ctx();
        let cls = class(&ctx, "\\C");
        assert_eq!(class::name(&cls), "\\C");
        // The class holds the context it was found in.
        assert!(cls.2.as_ref().is_some_and(|c| Arc::ptr_eq(c, &ctx)));
        assert!(cls.0.is_none());
        // From the hhi files.
        let exception = class(&ctx, "\\Exception");
        assert!(class::has_ancestor(&exception, "\\Throwable"));
        assert!(matches!(
            get_class(None, &ctx, "\\Nope"),
            decl_entry::T::DoesNotExist
        ));
        // Names are case sensitive, and fully qualified.
        assert!(matches!(
            get_class(None, &ctx, "\\c"),
            decl_entry::T::DoesNotExist
        ));
        assert!(matches!(
            get_class(None, &ctx, "C"),
            decl_entry::T::DoesNotExist
        ));
        // A typedef is not a class, nor a class a typedef.
        assert!(matches!(
            get_class(None, &ctx, "\\Alias"),
            decl_entry::T::DoesNotExist
        ));
        assert!(matches!(
            get_typedef(None, &ctx, "\\C"),
            decl_entry::T::DoesNotExist
        ));

        let shallow = get_shallow_class(&ctx, "\\C").unwrap();
        assert_eq!(shallow.name.id_ref().as_str(), "\\C");
        assert_eq!(shallow.methods.len(), 1);
        assert!(get_shallow_class(&ctx, "\\Alias").is_none());

        let folded = declare_folded_class_in_file_FOR_TESTS_ONLY(&ctx, "\\C");
        assert!(Arc::ptr_eq(&folded, &cls.1.0));
    }

    #[test]
    fn the_class_cache_is_that_of_one_context() {
        let ctx1 = ctx();
        let cls1 = class(&ctx1, "\\C");
        let cls2 = class(&ctx1, "\\C");
        // The same folded class, with the same member tables.
        assert!(Arc::ptr_eq(&cls1.1.0, &cls2.1.0));
        assert!(std::rc::Rc::ptr_eq(&cls1.1.1, &cls2.1.1));

        // Another context, with another `C`, on the same thread.
        let ctx2 = ctx_of(
            "<?hh\nclass C { public function other(): void {} }\n",
            TypecheckerOptions::default(),
        );
        let other = class(&ctx2, "\\C");
        assert!(class::has_method(&other, "other") && !class::has_method(&other, "m"));
        assert!(matches!(
            get_typedef(None, &ctx2, "\\Alias"),
            decl_entry::T::DoesNotExist
        ));
        let cls3 = class(&ctx1, "\\C");
        assert!(class::has_method(&cls3, "m") && !class::has_method(&cls3, "other"));
    }

    #[test]
    fn lookup_or_populate() {
        let ctx = ctx();
        cache::use_with(&ctx);
        let mut populated = 0;
        let mut populate = |name: &str| {
            populated += 1;
            rust_provider_backend_get_folded_class(&ctx, name).map(typing_class_types::make_class_t)
        };
        let cls1 = lookup_or_populate_class_cache("\\C", &mut populate).unwrap();
        let cls2 = lookup_or_populate_class_cache("\\C", &mut populate).unwrap();
        assert!(std::rc::Rc::ptr_eq(&cls1.1, &cls2.1));
        // What does not exist is not cached.
        assert!(lookup_or_populate_class_cache("\\Nope", &mut populate).is_none());
        assert!(lookup_or_populate_class_cache("\\Nope", &mut populate).is_none());
        assert_eq!(populated, 3);
    }

    #[test]
    fn functions() {
        let ctx = ctx();
        let top = decl_entry::to_option(get_fun(None, &ctx, "\\top")).unwrap();
        assert_eq!(top.ty.to_string(), "(function<T>(T $x, int $y): int)");
        assert!(!top.no_auto_dynamic && !top.support_dynamic_type);
        assert!(matches!(
            get_fun(None, &ctx, "\\nope"),
            decl_entry::T::DoesNotExist
        ));
        assert!(matches!(
            get_fun(None, &ctx, "\\C"),
            decl_entry::T::DoesNotExist
        ));
        // From the hhi files.
        assert!(matches!(
            get_fun(None, &ctx, "\\HH\\Lib\\Vec\\map"),
            decl_entry::T::Found(_)
        ));

        // With `everything_sdt` the type parameters are made to support
        // dynamic, unless the function opts out.
        let ctx = ctx_sdt();
        let top = decl_entry::to_option(get_fun(None, &ctx, "\\top")).unwrap();
        assert_eq!(
            top.ty.to_string(),
            "(function<T as HH\\supportdyn<mixed>>(T $x, int $y): int)"
        );
        let top_no_auto = decl_entry::to_option(get_fun(None, &ctx, "\\top_no_auto")).unwrap();
        assert!(top_no_auto.no_auto_dynamic);
        assert_eq!(
            top_no_auto.ty.to_string(),
            "(function<T>(T $x, int $y): int)"
        );
    }

    #[test]
    fn typedefs() {
        let ctx = ctx();
        let alias = decl_entry::to_option(get_typedef(None, &ctx, "\\Alias")).unwrap();
        assert_eq!(alias.tparams.len(), 1);
        assert_eq!(alias.tparams[0].name.id_ref().as_str(), "T");
        match &alias.type_assignment {
            TypedefTypeAssignment::SimpleTypeDef(vis, ty) => {
                assert_eq!(*vis, oxidized::aast::TypedefVisibility::Transparent);
                assert_eq!(ty.to_string(), "HH\\dict<string, T>");
            }
            TypedefTypeAssignment::CaseType(..) => panic!(),
        }
        assert!(alias.as_constraint.is_none());
        let opaque = decl_entry::to_option(get_typedef(None, &ctx, "\\Opaque")).unwrap();
        assert_eq!(
            opaque.as_constraint.as_ref().unwrap().to_string(),
            "arraykey"
        );
        assert!(matches!(
            get_typedef(None, &ctx, "\\Nope"),
            decl_entry::T::DoesNotExist
        ));

        // With `everything_sdt` a typedef without a bound is given
        // `supportdyn<mixed>`, unless it opts out.
        let ctx = ctx_sdt();
        let as_constraint = |name: &str| {
            let td = decl_entry::to_option(get_typedef(None, &ctx, name)).unwrap();
            td.as_constraint.as_ref().map(|ty| ty.to_string())
        };
        assert_eq!(
            as_constraint("\\Alias").as_deref(),
            Some("HH\\supportdyn<mixed>")
        );
        assert_eq!(as_constraint("\\Opaque").as_deref(), Some("arraykey"));
        assert_eq!(as_constraint("\\NoAuto"), None);
    }

    #[test]
    fn constants_and_modules() {
        let ctx = ctx();
        let gconst = get_gconst(None, &ctx, "\\GCONST").unwrap();
        assert_eq!(gconst.ty.to_string(), "int");
        assert!(get_gconst(None, &ctx, "\\Nope").is_none());
        assert!(get_gconst(None, &ctx, "GCONST").is_none());
        assert!(get_module(None, &ctx, "some.mod").is_some());
        assert!(get_module(None, &ctx, "some.other").is_none());
    }

    #[test]
    fn winners() {
        let ctx = ctx();
        let id = |pos: &Pos, name: &str| ast_defs::Id(pos.clone(), name.to_string());
        let class_pos = class::pos(&class(&ctx, "\\C"));
        let fun_pos = Pos::from(
            decl_entry::to_option(get_fun(None, &ctx, "\\top"))
                .unwrap()
                .pos
                .clone(),
        );
        let const_pos = Pos::from(get_gconst(None, &ctx, "\\GCONST").unwrap().pos.clone());
        assert_ne!(class_pos, fun_pos);

        assert_eq!(
            get_pos_from_decl_of_winner_FOR_TESTS_ONLY(&ctx, NameType::Class, "\\C"),
            Some(class_pos.clone())
        );
        // The name of a class is not that of a typedef, whatever the case.
        assert_eq!(
            get_pos_from_decl_of_winner_FOR_TESTS_ONLY(&ctx, NameType::Typedef, "\\C"),
            None
        );
        assert_eq!(
            get_pos_from_decl_of_winner_FOR_TESTS_ONLY(&ctx, NameType::Class, "\\c"),
            None
        );
        assert_eq!(
            get_pos_from_decl_of_winner_FOR_TESTS_ONLY(&ctx, NameType::Class, "\\Alias"),
            None
        );
        assert!(
            get_pos_from_decl_of_winner_FOR_TESTS_ONLY(&ctx, NameType::Typedef, "\\Alias")
                .is_some()
        );
        assert_eq!(
            get_pos_from_decl_of_winner_FOR_TESTS_ONLY(&ctx, NameType::Fun, "\\top"),
            Some(fun_pos.clone())
        );
        assert!(
            get_pos_from_decl_of_winner_FOR_TESTS_ONLY(&ctx, NameType::Module, "some.mod")
                .is_some()
        );

        let winner = |name_type, pos: &Pos, name: &str| {
            is_this_def_the_winner(&ctx, name_type, &id(pos, name))
        };
        assert_eq!(winner(NameType::Class, &class_pos, "\\C"), Winner::Winner);
        assert_eq!(winner(NameType::Fun, &fun_pos, "\\top"), Winner::Winner);
        assert_eq!(
            winner(NameType::Const, &const_pos, "\\GCONST"),
            Winner::Winner
        );
        // Another definition of the name, somewhere else.
        assert_eq!(
            winner(NameType::Class, &fun_pos, "\\C"),
            Winner::Loser_to(class_pos.clone())
        );
        assert_eq!(
            winner(NameType::Const, &fun_pos, "\\GCONST"),
            Winner::Loser_to(const_pos.clone())
        );
        // A name that only differs by case from the winner's, or that is the
        // name of the winner of the other kind.
        assert_eq!(
            winner(NameType::Class, &fun_pos, "\\c"),
            Winner::Loser_to(class_pos.clone())
        );
        assert_eq!(
            winner(NameType::Typedef, &fun_pos, "\\C"),
            Winner::Loser_to(class_pos.clone())
        );
        assert_eq!(
            winner(NameType::Fun, &class_pos, "\\TOP"),
            Winner::Loser_to(fun_pos.clone())
        );
        // Constants are case sensitive.
        assert_eq!(
            winner(NameType::Const, &const_pos, "\\gconst"),
            Winner::Not_found
        );
        assert_eq!(
            winner(NameType::Class, &class_pos, "\\Nope"),
            Winner::Not_found
        );
        assert_eq!(winner(NameType::Fun, &fun_pos, "\\nope"), Winner::Not_found);
    }

    #[test]
    fn overridden_methods() {
        let ctx = ctx_of(
            r#"<?hh
class Base<T> {
  public function m(T $x): int { return 1; }
  public function only_base(): T { throw new Exception(); }
  public function q(): int { return 1; }
  public static function s(): void {}
  private function p(): void {}
}

trait Tr {
  public function m(string $x): int { return 2; }
  abstract public function q(): int;
}

class Child extends Base<string> {
  use Tr;
  public function m(string $x): int { return 3; }
  public function only_base(): string { return ''; }
  public function q(): int { return 2; }
  public static function s(): void {}
  private function p(): void {}
  public function own(): void {}
}
"#,
            TypecheckerOptions::default(),
        );
        let overridden = |class_name: &str, method_name: &str, is_static: bool| {
            decl_entry::to_option(get_overridden_method(
                &ctx,
                class_name,
                method_name,
                is_static,
            ))
            .map(|ce| (ce.ce_type.to_string(), ce.ce_origin.clone()))
        };
        let method = |ty: &str, origin: &str| Some((ty.to_string(), origin.to_string()));
        // The method of the trait is the one the class would have had.
        assert_eq!(
            overridden("\\Child", "m", false),
            method("(function(string $x): int)", "\\Tr")
        );
        // Unless it is abstract, and the parent class has a concrete one.
        assert_eq!(
            overridden("\\Child", "q", false),
            method("(function(): int)", "\\Base")
        );
        // The method is that of the parent class, as the parent class has it:
        // the type arguments of `extends Base<string>` are not applied.
        assert_eq!(
            overridden("\\Child", "only_base", false),
            method("(function(): T)", "\\Base")
        );
        assert_eq!(
            overridden("\\Child", "s", true),
            method("(function(): void)", "\\Base")
        );
        assert_eq!(overridden("\\Child", "s", false), None);
        // A private method overrides nothing, nor does a method the parents
        // do not have.
        assert_eq!(overridden("\\Child", "p", false), None);
        assert_eq!(overridden("\\Child", "own", false), None);
        assert_eq!(overridden("\\Base", "m", false), None);
        assert!(matches!(
            get_overridden_method(&ctx, "\\Nope", "m", false),
            decl_entry::T::DoesNotExist
        ));
    }

    #[test]
    fn overlaps() {
        let file = Arc::new(relative_path::RelativePath::make(
            relative_path::Prefix::Root,
            "a.php".into(),
        ));
        let pos = |file: &Arc<relative_path::RelativePath>, start: usize, end: usize| {
            Pos::from_lnum_bol_offset(Arc::clone(file), (1, 0, start), (1, 0, end))
        };
        assert!(pos_overlaps(&pos(&file, 0, 10), &pos(&file, 5, 15)));
        assert!(pos_overlaps(&pos(&file, 5, 15), &pos(&file, 0, 10)));
        assert!(pos_overlaps(&pos(&file, 0, 10), &pos(&file, 2, 3)));
        assert!(!pos_overlaps(&pos(&file, 0, 5), &pos(&file, 5, 10)));
        assert!(!pos_overlaps(&pos(&file, 6, 10), &pos(&file, 0, 5)));
        let other = Arc::new(relative_path::RelativePath::make(
            relative_path::Prefix::Root,
            "b.php".into(),
        ));
        assert!(!pos_overlaps(&pos(&file, 0, 10), &pos(&other, 0, 10)));
    }
}
