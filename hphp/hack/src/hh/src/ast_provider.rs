// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `ast_provider.ml`. See `hh/PORTING.md`.
//!
//! The ASTs are those of the parser before naming (`Nast.program` as the
//! lowerer makes it): files are parsed by `crate::full_fidelity_ast`, as
//! OCaml parses them (diagnostics, `HH_FIXME`s and lints are reported the
//! same way). `crate::parse` names the AST it makes, which the callers of
//! this module do themselves (`Naming.class_ ctx ast`).
//!
//! The backend of a `Ctx` is `Rust_provider_backend` (see
//! `crate::provider_context`): of each function that matches on the backend,
//! that branch is ported. The OCaml caches the ASTs in two places:
//!
//! - `ParserHeap`, a heap in shared memory with a cache local to each worker
//!   (`Shared_mem.HeapWithLocalCache`), and its stacks of local changes;
//! - `LocalParserCache`, a cache local to each worker (`Shared_mem.FreqCache`).
//!
//! Here a worker is a thread, and both are kept for each thread, with the
//! same behaviour (see [`shared_mem`]). They are those of the files of the
//! `Ctx` they were last used with (the contexts that `map_tcopt` and friends
//! make share the files of the one they come from): a thread given another
//! `Ctx` starts afresh, as `crate::decl_provider` does for its classes.
//!
//! `PositionedSyntaxTree.t` has no type in this crate (see
//! `crate::provider_context`), so `compute_cst` is not here.

use std::cell::RefCell;
use std::sync::Arc;
use std::sync::Weak;

use oxidized::file_info;
use oxidized::nast;
use oxidized::parser_options::ParserOptions;
use relative_path::RelativePath;

use crate::ctx::Files;
use crate::diagnostics_state as diagnostics;
use crate::full_fidelity_source_text;
use crate::parser_return;
use crate::provider_context;
use crate::provider_context::Entry;
use crate::provider_context::T as Ctx;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParseType {
    Decl,
    Full,
}

/// The parts of `Shared_mem` that the caches of this module are made of,
/// for one thread (`crate::file_provider` makes its `FileHeap` of [`Heap`]).
pub(crate) mod shared_mem {
    use std::collections::HashMap;

    use relative_path::RelativePath;

    /// `Shared_mem.FreqCache (Relative_path.S) (Value) (Capacity)`
    pub struct FreqCache<V> {
        capacity: usize,
        cache: HashMap<RelativePath, (usize, V)>,
    }

    impl<V: Clone> FreqCache<V> {
        pub fn new(capacity: usize) -> Self {
            Self {
                capacity,
                cache: HashMap::with_capacity(2 * capacity),
            }
        }

        pub fn clear(&mut self) {
            self.cache.clear()
        }

        /// The collection function is called when we reach twice original
        /// capacity in size. When the collection is triggered, we only keep
        /// the most frequently used objects.
        /// So before collection: size = 2 * capacity
        /// After collection: size = capacity (with the most frequently
        /// used objects)
        fn collect(&mut self) {
            if self.cache.len() < 2 * self.capacity {
            } else {
                let mut l: Vec<(RelativePath, usize, V)> = self
                    .cache
                    .drain()
                    .map(|(key, (freq, v))| (key, freq, v))
                    .collect();
                l.sort_by(|(_, x, _), (_, y, _)| y.cmp(x));
                for (k, _freq, v) in l.into_iter().take(self.capacity) {
                    self.cache.insert(k, (0, v));
                }
            }
        }

        pub fn add(&mut self, x: RelativePath, y: V) {
            self.collect();
            match self.cache.get_mut(&x) {
                Some((freq, y_)) => {
                    *freq += 1;
                    // `if phys_equal y' y then () else ...`: replacing a value
                    // by itself changes nothing.
                    *y_ = y
                }
                None => {
                    self.cache.insert(x, (0, y));
                }
            }
        }

        pub fn get(&mut self, x: &RelativePath) -> Option<V> {
            match self.cache.get_mut(x) {
                None => None,
                Some((freq, value)) => {
                    *freq += 1;
                    Some(value.clone())
                }
            }
        }

        pub fn remove(&mut self, x: &RelativePath) {
            self.cache.remove(x);
        }
    }

    /// `action` of `BackendWithLocalChanges.LocalChanges`
    enum Action<V> {
        /// The value does not exist in the current stack. When committed this
        /// action will invoke remove on the previous stack.
        Remove,
        /// The value is added to a previously empty slot. When committed this
        /// action will invoke add on the previous stack.
        Add(V),
        /// The value is replacing a value already associated with a key in the
        /// previous stack. When committed this action will invoke remove then
        /// add on the previous stack.
        Replace(V),
    }

    /// `BackendWithLocalChanges.LocalChanges.t`
    struct LocalChanges<V> {
        current: HashMap<RelativePath, Action<V>>,
        prev: Option<Box<LocalChanges<V>>>,
    }

    /// `Shared_mem.Heap (ImmediateBackend (Evictable)) (Relative_path.S)
    /// (Value)`: the heap itself (in which an `add` of a key that is there
    /// already changes nothing, and nothing is evicted here), and its stack
    /// of local changes.
    pub struct Heap<V> {
        backend: HashMap<RelativePath, V>,
        stack: Option<Box<LocalChanges<V>>>,
    }

    impl<V: Clone> Heap<V> {
        pub fn new() -> Self {
            Self {
                backend: HashMap::new(),
                stack: None,
            }
        }

        fn local_mem(
            backend: &HashMap<RelativePath, V>,
            stack_opt: Option<&LocalChanges<V>>,
            key: &RelativePath,
        ) -> bool {
            match stack_opt {
                None => backend.contains_key(key),
                Some(stack) => match stack.current.get(key) {
                    Some(Action::Remove) => false,
                    Some(_) => true,
                    None => Self::local_mem(backend, stack.prev.as_deref(), key),
                },
            }
        }

        fn local_get(
            backend: &HashMap<RelativePath, V>,
            stack_opt: Option<&LocalChanges<V>>,
            key: &RelativePath,
        ) -> Option<V> {
            match stack_opt {
                None => backend.get(key).cloned(),
                Some(stack) => match stack.current.get(key) {
                    Some(Action::Remove) => None,
                    Some(Action::Replace(value) | Action::Add(value)) => Some(value.clone()),
                    None => Self::local_get(backend, stack.prev.as_deref(), key),
                },
            }
        }

        // For remove/add it is best to think of them in terms of a state machine.
        // A key can be in the following states:
        //
        //  Remove:
        //    Local changeset removes a key from the previous stack
        //  Replace:
        //    Local changeset replaces value of a key in previous stack
        //  Add:
        //    Local changeset associates a value with a key. The key is not
        //    present in the previous stacks
        //  Empty:
        //    No local changes and key is not present in previous stack
        //  Filled:
        //    No local changes and key has an associated value in previous stack
        //  *Error*:
        //    This means an exception will occur

        /// Transitions table:
        ///   Remove  -> *Error*
        ///   Replace -> Remove
        ///   Add     -> Empty
        ///   Empty   -> *Error*
        ///   Filled  -> Remove
        fn local_remove(&mut self, key: &RelativePath) {
            match &mut self.stack {
                // `Backend.remove`: the key is there.
                None => {
                    self.backend.remove(key);
                }
                Some(stack) => match stack.current.get(key) {
                    Some(Action::Remove) => panic!("Trying to remove a non-existent value"),
                    Some(Action::Replace(_)) => {
                        stack.current.insert(key.clone(), Action::Remove);
                    }
                    Some(Action::Add(_)) => {
                        stack.current.remove(key);
                    }
                    None => {
                        if Self::local_mem(&self.backend, stack.prev.as_deref(), key) {
                            stack.current.insert(key.clone(), Action::Remove);
                        } else {
                            panic!("Trying to remove a non-existent value")
                        }
                    }
                },
            }
        }

        /// Transitions table:
        ///   Remove  -> Replace
        ///   Replace -> Replace
        ///   Add     -> Add
        ///   Empty   -> Add
        ///   Filled  -> Replace
        fn local_add(&mut self, key: RelativePath, value: V) {
            match &mut self.stack {
                // `Backend.add` (`hh_add`) does nothing when the key is there.
                None => {
                    self.backend.entry(key).or_insert(value);
                }
                Some(stack) => match stack.current.get(&key) {
                    Some(Action::Remove | Action::Replace(_)) => {
                        stack.current.insert(key, Action::Replace(value));
                    }
                    Some(Action::Add(_)) => {
                        stack.current.insert(key, Action::Add(value));
                    }
                    None => {
                        if Self::local_mem(&self.backend, stack.prev.as_deref(), &key) {
                            stack.current.insert(key, Action::Replace(value));
                        } else {
                            stack.current.insert(key, Action::Add(value));
                        }
                    }
                },
            }
        }

        pub fn add(&mut self, x: RelativePath, y: V) {
            self.local_add(x, y)
        }

        pub fn get(&self, x: &RelativePath) -> Option<V> {
            Self::local_get(&self.backend, self.stack.as_deref(), x)
        }

        pub fn mem(&self, x: &RelativePath) -> bool {
            Self::local_mem(&self.backend, self.stack.as_deref(), x)
        }

        pub fn remove(&mut self, x: &RelativePath) {
            if self.mem(x) {
                self.local_remove(x)
            } else {
            }
        }

        /// Not in the OCaml: remove every key, from the heap and from each
        /// change set of the stack, which keeps its depth (what removing
        /// every key from the shared heap does for a worker whose own stack
        /// is pushed: see `crate::rt::decl_epoch`).
        pub fn clear_keeping_stacks(&mut self) {
            self.backend = HashMap::new();
            let mut stack = self.stack.as_deref_mut();
            while let Some(changes) = stack {
                changes.current = HashMap::new();
                stack = changes.prev.as_deref_mut();
            }
        }

        pub fn push_stack(&mut self) {
            let prev = self.stack.take();
            self.stack = Some(Box::new(LocalChanges {
                current: HashMap::with_capacity(128),
                prev,
            }));
        }

        /// Not in the OCaml: how many stacks of local changes are pushed.
        pub fn stack_depth(&self) -> usize {
            let mut depth = 0;
            let mut stack = self.stack.as_deref();
            while let Some(changes) = stack {
                depth += 1;
                stack = changes.prev.as_deref();
            }
            depth
        }

        pub fn pop_stack(&mut self) {
            match self.stack.take() {
                None => panic!("There are no active local change stacks. Nothing to pop!"),
                Some(stack) => {
                    let LocalChanges { prev, .. } = *stack;
                    self.stack = prev
                }
            }
        }
    }

    /// `Shared_mem.HeapWithLocalCache (Backend) (Relative_path.S) (Value)
    /// (Capacity)`
    pub struct HeapWithLocalCache<V> {
        direct: Heap<V>,
        pub cache: FreqCache<V>,
    }

    impl<V: Clone> HeapWithLocalCache<V> {
        pub fn new(capacity: usize) -> Self {
            Self {
                direct: Heap::new(),
                cache: FreqCache::new(capacity),
            }
        }

        pub fn add(&mut self, x: RelativePath, y: V) {
            self.direct.add(x.clone(), y.clone());
            self.cache.add(x, y)
        }

        pub fn write_around(&mut self, x: RelativePath, y: V) {
            // Note that we do not need to do any cache invalidation here because
            // Direct.add is a no-op if the key already exists.
            self.direct.add(x, y)
        }

        pub fn get(&mut self, x: &RelativePath) -> Option<V> {
            match self.cache.get(x) {
                None => match self.direct.get(x) {
                    None => None,
                    Some(v) => {
                        self.cache.add(x.clone(), v.clone());
                        Some(v)
                    }
                },
                Some(v) => Some(v),
            }
        }

        pub fn mem(&mut self, x: &RelativePath) -> bool {
            match self.get(x) {
                None => false,
                Some(_) => true,
            }
        }

        pub fn remove_batch(&mut self, xs: &[RelativePath]) {
            for x in xs {
                self.direct.remove(x)
            }
            for x in xs {
                self.cache.remove(x)
            }
        }

        /// Not in the OCaml: see [`Heap::clear_keeping_stacks`].
        pub fn clear_keeping_stacks(&mut self) {
            self.direct.clear_keeping_stacks();
            self.cache.clear()
        }

        pub fn push_stack(&mut self) {
            self.direct.push_stack();
            self.cache.clear()
        }

        pub fn stack_depth(&self) -> usize {
            self.direct.stack_depth()
        }

        pub fn pop_stack(&mut self) {
            self.direct.pop_stack();
            self.cache.clear()
        }
    }
}

/// Whether full ASTs are kept in `LocalParserCache` (each thread's cache of
/// 1000 to 2000 ASTs, each stored as a copy). A batch check reads the AST of
/// each file once, so it switches the cache off: it only costs it memory and
/// a copy of every AST. The cache never changes what is computed.
static LOCAL_PARSER_CACHE_ENABLED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(true);

pub fn set_local_parser_cache_enabled(enabled: bool) {
    LOCAL_PARSER_CACHE_ENABLED.store(enabled, std::sync::atomic::Ordering::Relaxed)
}

/// The caches of a thread.
struct Caches {
    /// The files of the `Ctx` the caches were last used with (`None` before
    /// they are first used with one).
    files: Option<Weak<Files>>,
    /// `ParserHeap`: `Shared_mem.HeapWithLocalCache` of
    /// `Nast.program * parse_type` (description `"Ast_Parser"`), with a
    /// local cache of capacity 1000.
    parser_heap: shared_mem::HeapWithLocalCache<(nast::Program, ParseType)>,
    /// `LocalParserCache`: `Shared_mem.FreqCache` of `Nast.program`
    /// (description `"Ast_ParserLocal"`), of capacity 1000.
    local_parser_cache: shared_mem::FreqCache<nast::Program>,
}

thread_local! {
    static CACHES: RefCell<Caches> = RefCell::new(Caches {
        files: None,
        parser_heap: shared_mem::HeapWithLocalCache::new(1000),
        local_parser_cache: shared_mem::FreqCache::new(1000),
    });
}

/// Start the caches of this thread afresh if they were last used with the
/// files of another `Ctx`.
fn use_with(ctx: &Ctx) {
    CACHES.with_borrow_mut(|caches| {
        let same = match &caches.files {
            None => true,
            Some(files) => std::ptr::eq(files.as_ptr(), Arc::as_ptr(&ctx.files)),
        };
        if !same {
            // (The stacks of local changes pushed stay pushed, empty: the
            // typing service pops what it pushed around a thread's share.)
            let depth = caches.parser_heap.stack_depth();
            caches.parser_heap = shared_mem::HeapWithLocalCache::new(1000);
            for _ in 0..depth {
                caches.parser_heap.push_stack();
            }
            caches.local_parser_cache = shared_mem::FreqCache::new(1000);
        }
        caches.files = Some(Arc::downgrade(&ctx.files));
    })
}

/// `Nast.deregister_ignored_attributes`, when the file is an hhi file and
/// the PHP standard library is deregistered.
fn deregister_if_hhi(popt: &ParserOptions, path: &RelativePath, ast: nast::Program) -> nast::Program {
    if crate::relative_path::is_hhi(crate::relative_path::prefix(path)) && popt.deregister_php_stdlib
    {
        crate::nast::deregister_ignored_attributes(ast)
    } else {
        ast
    }
}

fn parse(
    popt: &ParserOptions,
    full: bool,
    source_text: &full_fidelity_source_text::T,
) -> (diagnostics::T, parser_return::T) {
    let path = full_fidelity_source_text::file_path(source_text).clone();
    let parser_env = crate::full_fidelity_ast::make_env(
        None,
        None,
        None,
        None,
        Some(!full),
        None,
        Some(popt.clone()),
        None,
        path.clone(),
    );
    let (err, result) = diagnostics::do_with_context(None, path.clone(), || {
        crate::full_fidelity_ast::from_source_text_with_legacy(&parser_env, source_text)
    });
    let parser_return::T {
        file_mode,
        comments,
        ast,
        content,
    } = result;
    let ast = deregister_if_hhi(popt, &path, ast);
    (
        err,
        parser_return::T {
            file_mode,
            comments,
            ast,
            content,
        },
    )
}

/// `Ide_parser_cache.get_ast_if_active popt file_name contents`.
///
/// `Ide_parser_cache` is not ported: its state starts `Disabled`, and only
/// `Ide_parser_cache.enable` (which `ServerMain` calls when it serves an
/// IDE) lets it become active; nothing here does, so it has no AST to give.
fn ide_parser_cache_get_ast_if_active(
    _popt: &ParserOptions,
    _file_name: &RelativePath,
    _contents: &[u8],
) -> Option<parser_return::T> {
    None
}

/// `Full_fidelity_parser.parse_mode` (the Rust parser's `parse_mode`, as
/// `rust_parser_ffi.rs` called it)
fn full_fidelity_parser_parse_mode(source: &full_fidelity_source_text::T) -> Option<file_info::Mode> {
    let (_, mode) = mode_parser::parse_mode(&full_fidelity_source_text::source_text(source));
    mode.map(Into::into)
}

/// Look up ast in LocalParserCache.
/// If not found, look up in Ide_parser_cache.
/// If not found, actually parse the file.
fn get_from_local_cache(full: bool, ctx: &Ctx, file_name: &RelativePath) -> (diagnostics::T, nast::Program) {
    let with_no_err = |ast: nast::Program| (diagnostics::empty, ast);
    let fn_ = crate::relative_path::to_absolute(file_name);
    use_with(ctx);
    match CACHES.with_borrow_mut(|caches| caches.local_parser_cache.get(file_name)) {
        Some(ast) => with_no_err(ast),
        None => {
            let popt = provider_context::get_popt(ctx);
            let parse = |contents: bstr::BString| {
                let contents = if crate::find_utils::file_filter(&fn_) {
                    contents
                } else {
                    bstr::BString::from("")
                };
                match ide_parser_cache_get_ast_if_active(popt, file_name, &contents) {
                    Some(ast) => with_no_err(ast.ast),
                    None => {
                        let source = full_fidelity_source_text::make(file_name, &contents);
                        match full_fidelity_parser_parse_mode(&source) {
                            None => with_no_err(nast::Program(vec![])),
                            Some(_) => {
                                // It's up to Parsing_service to add parsing errors.
                                let (err, result) =
                                    diagnostics::do_with_context(None, file_name.clone(), || {
                                        crate::full_fidelity_ast::defensive_program(
                                            Some(!full),
                                            None,
                                            None,
                                            None,
                                            popt.clone(),
                                            file_name,
                                            &contents,
                                        )
                                    });
                                (err, result.ast)
                            }
                        }
                    }
                }
            };
            // `File_provider.get_contents file_name`: the backend is that of
            // the context.
            let (err, ast) = match crate::file_provider::rust_provider_backend::file::get_contents(
                ctx, file_name,
            ) {
                None => with_no_err(nast::Program(vec![])),
                Some(contents) => parse(contents),
            };
            let ast = deregister_if_hhi(popt, file_name, ast);
            if full
                && diagnostics::has_no_errors(None, &err)
                && LOCAL_PARSER_CACHE_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
            {
                CACHES.with_borrow_mut(|caches| {
                    caches.local_parser_cache.add(file_name.clone(), ast.clone())
                });
            }
            (err, ast)
        }
    }
}

/// Compute the [Full_fidelity_source_text.t] for this [Provider_context.entry].
/// This is cached in the entry itself, but not in the AST provider's cache.
pub fn compute_source_text(entry: &Entry) -> full_fidelity_source_text::T {
    // (No lock is held while the contents are read: reading them may raise.)
    let cached = entry.source_text.lock().unwrap().clone();
    match cached {
        Some(source_text) => source_text,
        None => {
            let contents = provider_context::read_file_contents_exn(entry);
            let source_text = full_fidelity_source_text::make(&entry.path, &contents);
            *entry.source_text.lock().unwrap() = Some(source_text.clone());
            source_text
        }
    }
}

/// Note that some callers may not actually need the AST errors. This could be
/// improved with a method similar to the TAST-and-errors generation, where the TAST
/// errors are not generated unless necessary.
///
/// Compute the full [Parser_return.t] object.
/// This is cached in the entry itself, but not in the AST provider's cache.
pub fn compute_parser_return_and_ast_errors(
    popt: &ParserOptions,
    entry: &Entry,
) -> (parser_return::T, diagnostics::T) {
    let cached = (
        entry.ast_diagnostics.lock().unwrap().clone(),
        entry.parser_return.lock().unwrap().clone(),
    );
    match cached {
        (Some(ast_errors), Some(parser_return)) => (parser_return, ast_errors),
        _ => {
            let source_text = compute_source_text(entry);
            let (ast_errors, parser_return) = parse(popt, true, &source_text);
            *entry.ast_diagnostics.lock().unwrap() = Some(ast_errors.clone());
            *entry.parser_return.lock().unwrap() = Some(parser_return.clone());
            (parser_return, ast_errors)
        }
    }
}

fn compute_ast_with_error(popt: &ParserOptions, entry: &Entry) -> (diagnostics::T, nast::Program) {
    let (parser_return::T { ast, .. }, ast_errors) =
        compute_parser_return_and_ast_errors(popt, entry);
    (ast_errors, ast)
}

/// Compute the AST for the given [Provider_context.entry].
/// This is cached in the entry itself, but not in the AST provider's cache.
pub fn compute_ast(popt: &ParserOptions, entry: &Entry) -> nast::Program {
    compute_ast_with_error(popt, entry).1
}

/// Compute the comments for the given [Provider_context.entry].
/// This is cached in the entry itself, but not in the AST provider's cache.
pub fn compute_comments(popt: &ParserOptions, entry: &Entry) -> parser_return::Comments {
    let (parser_return::T { comments, .. }, _ast_errors) =
        compute_parser_return_and_ast_errors(popt, entry);
    comments
}

/// Compute the [File_info.t] associated with the given entry, doing a parse
/// if necessary.
/// This is cached in the entry itself, but not in the AST provider's cache.
pub fn compute_file_info(popt: &ParserOptions, entry: &Entry) -> file_info::Ids {
    let ast = compute_ast(popt, entry);
    crate::nast::get_def_names(&ast)
}

/// `full` determines whether this is producing the full AST or just the decl information.
///
/// (`parse_from_disk_no_caching`, which the OCaml defines here, is used by
/// the branches of the other backends only.)
pub fn get_ast_with_error(full: bool, ctx: &Ctx, path: &RelativePath) -> (diagnostics::T, nast::Program) {
    crate::counters::count(crate::counters::category::T::Ast_provider_get, || {
        // If there's a ctx, and this file is in the ctx, then use ctx.
        // Otherwise, the way we fetch/cache ASTs depends on the provider.
        let entry_opt = ctx.entries.get(path).cloned();
        match entry_opt {
            Some(entry) => {
                // See documentation on `entry` for its invariants.
                // The compute_ast function will use the cached (full) AST if present,
                // and otherwise will compute a full AST and cache it and return it.
                // It's okay for get_ast to return a full AST even if only asked for
                // a partial one. Our principle is that an ctx entry always indicates that
                // the file is open in the IDE, and so will benefit from a full AST at
                // some time, so we might as well get it now.
                compute_ast_with_error(provider_context::get_popt(ctx), &entry)
            }
            None if ctx.local_memory().is_some() => {
                // `Provider_backend.Local_memory _` (added by L0):
                // We never cache ASTs for this provider. There'd be no use.
                // The only valuable caching is to cache decls.
                // (`parse_from_disk_no_caching ~apply_file_filter:false`;
                // `Sys_utils.cat` raises when the file cannot be read.)
                let contents = match ::file_provider::FileProvider::get(&*ctx.files, pos::RelativePath::from(path)) {
                    Ok(contents) => contents,
                    Err(e) => panic!(
                        "Sys_error {:?}",
                        format!("{}: {}", crate::relative_path::to_absolute(path), e)
                    ),
                };
                let source_text = full_fidelity_source_text::make(path, &contents);
                let (err, parser_return::T { ast, .. }) =
                    parse(provider_context::get_popt(ctx), full, &source_text);
                (err, ast)
            }
            None => {
                // `Provider_backend.Rust_provider_backend _`
                //
                // Note that we might be looking up the shared ParserHeap directly,
                // or maybe into a local-change-stack due to quarantine.
                // The following code makes sure to only cache `Decl`/non-full ASTs
                // in the ParserHeap, for memory consumption reasons (I assume).
                // As of today, we only ever store `Full` ASTs in the ParserHeap for testing,
                // via `provide_ast_hint`.
                use_with(ctx);
                match (
                    CACHES.with_borrow_mut(|caches| caches.parser_heap.get(path)),
                    full,
                ) {
                    (Some((ast, ParseType::Decl)), false) | (Some((ast, ParseType::Full)), _) => {
                        // It's in the parser-heap! hurrah!
                        (diagnostics::empty, ast)
                    }
                    (None, true) | (Some((_, ParseType::Decl)), true) => {
                        // If we need full, and parser-heap can't provide it, then we
                        // don't want to write a full decl into the parser heap.
                        get_from_local_cache(full, ctx, path)
                    }
                    (None, false) => {
                        // This is the case where we will write into the parser heap.
                        let (err, ast) = get_from_local_cache(full, ctx, path);
                        if diagnostics::has_no_errors(None, &err) {
                            CACHES.with_borrow_mut(|caches| {
                                caches
                                    .parser_heap
                                    .add(path.clone(), (ast.clone(), ParseType::Decl))
                            });
                        }
                        (err, ast)
                    }
                }
            }
        }
    })
}

/// `full` determines whether this is producing the full AST or just the decl information.
pub fn get_ast(full: bool, ctx: &Ctx, path: &RelativePath) -> nast::Program {
    get_ast_with_error(full, ctx, path).1
}

fn get_def<A>(
    full: bool,
    ctx: &Ctx,
    file_name: &RelativePath,
    node_getter: impl Fn(nast::Def) -> Option<(A, String)>,
    name_matcher: impl Fn(&str) -> bool,
) -> Option<A> {
    let defs = get_ast(full, ctx, file_name);
    fn get<A>(
        acc: Option<A>,
        defs: Vec<nast::Def>,
        node_getter: &impl Fn(nast::Def) -> Option<(A, String)>,
        name_matcher: &impl Fn(&str) -> bool,
    ) -> Option<A> {
        let mut acc = acc;
        for def in defs {
            acc = match def {
                nast::Def::Namespace(namespace) => {
                    let (_, defs) = *namespace;
                    get(acc, defs, node_getter, name_matcher)
                }
                def => match node_getter(def) {
                    Some((node, name)) if name_matcher(&name) => Some(node),
                    _ => acc,
                },
            }
        }
        acc
    }
    get(None, defs.0, &node_getter, &name_matcher)
}

fn find_class_impl(def: nast::Def) -> Option<(nast::Class_, String)> {
    match def {
        nast::Def::Class(c) => {
            let name = c.name.1.clone();
            Some((*c, name))
        }
        _ => None,
    }
}

fn find_fun_impl(def: nast::Def) -> Option<(nast::FunDef, String)> {
    match def {
        nast::Def::Fun(f) => {
            let name = f.name.1.clone();
            Some((*f, name))
        }
        _ => None,
    }
}

fn find_typedef_impl(def: nast::Def) -> Option<(nast::Typedef, String)> {
    match def {
        nast::Def::Typedef(t) => {
            let name = t.name.1.clone();
            Some((*t, name))
        }
        _ => None,
    }
}

fn find_const_impl(def: nast::Def) -> Option<(nast::Gconst, String)> {
    match def {
        nast::Def::Constant(cst) => {
            let name = cst.name.1.clone();
            Some((*cst, name))
        }
        _ => None,
    }
}

fn find_module_impl(def: nast::Def) -> Option<(nast::ModuleDef, String)> {
    match def {
        nast::Def::Module(md) => {
            let name = md.name.1.clone();
            Some((*md, name))
        }
        _ => None,
    }
}

/// `Stdlib.String.lowercase_ascii`, both sides.
fn iequal(name: &str) -> impl Fn(&str) -> bool {
    let name = name.to_ascii_lowercase();
    move |s| name == s.to_ascii_lowercase()
}

/// Case-sensitive.
/// `full` determines whether this is producing the full AST or just the decl information.
pub fn find_class_in_file(
    full: bool,
    ctx: &Ctx,
    file_name: &RelativePath,
    name: &str,
) -> Option<nast::Class_> {
    get_def(full, ctx, file_name, find_class_impl, |s| name == s)
}

/// Case-insensitive
pub fn find_iclass_in_file(ctx: &Ctx, file_name: &RelativePath, iname: &str) -> Option<nast::Class_> {
    get_def(false, ctx, file_name, find_class_impl, iequal(iname))
}

/// Case-sensitive.
/// `full` determines whether this is producing the full AST or just the decl information.
pub fn find_fun_in_file(
    full: bool,
    ctx: &Ctx,
    file_name: &RelativePath,
    name: &str,
) -> Option<nast::FunDef> {
    get_def(full, ctx, file_name, find_fun_impl, |s| name == s)
}

/// Case-insensitive
pub fn find_ifun_in_file(ctx: &Ctx, file_name: &RelativePath, iname: &str) -> Option<nast::FunDef> {
    get_def(false, ctx, file_name, find_fun_impl, iequal(iname))
}

/// Case-sensitive.
/// `full` determines whether this is producing the full AST or just the decl information.
pub fn find_typedef_in_file(
    full: bool,
    ctx: &Ctx,
    file_name: &RelativePath,
    name: &str,
) -> Option<nast::Typedef> {
    get_def(full, ctx, file_name, find_typedef_impl, |s| name == s)
}

/// Case-insensitive
pub fn find_itypedef_in_file(
    ctx: &Ctx,
    file_name: &RelativePath,
    iname: &str,
) -> Option<nast::Typedef> {
    get_def(false, ctx, file_name, find_typedef_impl, iequal(iname))
}

/// Case-sensitive.
/// `full` determines whether this is producing the full AST or just the decl information.
pub fn find_gconst_in_file(
    full: bool,
    ctx: &Ctx,
    file_name: &RelativePath,
    name: &str,
) -> Option<nast::Gconst> {
    get_def(full, ctx, file_name, find_const_impl, |s| name == s)
}

/// Case-sensitive.
/// `full` determines whether this is producing the full AST or just the decl information.
pub fn find_module_in_file(
    full: bool,
    ctx: &Ctx,
    file_name: &RelativePath,
    name: &str,
) -> Option<nast::ModuleDef> {
    get_def(full, ctx, file_name, find_module_impl, |s| name == s)
}

pub fn local_changes_push_sharedmem_stack() {
    CACHES.with_borrow_mut(|caches| caches.parser_heap.push_stack())
}

pub fn local_changes_pop_sharedmem_stack() {
    CACHES.with_borrow_mut(|caches| caches.parser_heap.pop_stack())
}

pub fn provide_ast_hint(path: &RelativePath, program: nast::Program, parse_type: ParseType) {
    // `match Provider_backend.get () with`: the backend is
    // `Rust_provider_backend _` (not `Analysis`, which fails with
    // "Should not write into parser heap", nor `Local_memory`, which does
    // nothing).
    CACHES.with_borrow_mut(|caches| {
        caches
            .parser_heap
            .write_around(path.clone(), (program, parse_type))
    })
}

pub fn remove_batch(paths: &crate::relative_path::set::T) {
    let paths: Vec<RelativePath> = paths.iter().cloned().collect();
    CACHES.with_borrow_mut(|caches| caches.parser_heap.remove_batch(&paths))
}

pub fn has_for_test(path: &RelativePath) -> bool {
    CACHES.with_borrow_mut(|caches| caches.parser_heap.mem(path))
}

pub fn clear_parser_cache() {
    CACHES.with_borrow_mut(|caches| caches.parser_heap.cache.clear())
}

/// Not in the OCaml: `Shared_mem.invalidate_local_caches` for the caches of
/// this module on this thread (the local cache of `ParserHeap` and
/// `LocalParserCache`), see `crate::rt::decl_epoch`.
pub fn forget_thread_local_caches() {
    CACHES.with_borrow_mut(|caches| {
        caches.parser_heap.cache.clear();
        caches.local_parser_cache.clear()
    })
}

/// Not in the OCaml: the `ParserHeap` of this thread stands for the one in
/// shared memory, from which `Ast_provider.remove_batch` removes the changed
/// files for every worker; here every file is removed from it, on this
/// thread, when the files may have changed (see `crate::rt::decl_epoch`).
/// Its stack of local changes keeps its depth.
pub fn forget_thread_heaps() {
    CACHES.with_borrow_mut(|caches| caches.parser_heap.clear_keeping_stacks())
}

pub fn clear_local_cache() {
    CACHES.with_borrow_mut(|caches| caches.local_parser_cache.clear())
}

#[cfg(test)]
mod tests {
    use relative_path::Prefix;

    use super::*;

    fn path(name: &str) -> RelativePath {
        RelativePath::make(Prefix::Root, name.into())
    }

    #[test]
    fn heap_local_changes() {
        let mut heap = shared_mem::Heap::<isize>::new();
        heap.add(path("a"), 1);
        // `hh_add` does not replace.
        heap.add(path("a"), 2);
        assert_eq!(heap.get(&path("a")), Some(1));
        heap.push_stack();
        heap.add(path("a"), 3);
        heap.add(path("b"), 4);
        assert_eq!(heap.get(&path("a")), Some(3));
        assert_eq!(heap.get(&path("b")), Some(4));
        heap.remove(&path("a"));
        assert!(!heap.mem(&path("a")));
        heap.pop_stack();
        assert_eq!(heap.get(&path("a")), Some(1));
        assert!(!heap.mem(&path("b")));
        assert!(std::panic::catch_unwind(move || heap.pop_stack()).is_err());
    }

    #[test]
    fn freq_cache_keeps_the_most_used() {
        let mut cache = shared_mem::FreqCache::<isize>::new(2);
        cache.add(path("a"), 1);
        cache.add(path("b"), 2);
        cache.add(path("c"), 3);
        assert_eq!(cache.get(&path("a")), Some(1));
        assert_eq!(cache.get(&path("a")), Some(1));
        assert_eq!(cache.get(&path("c")), Some(3));
        cache.add(path("d"), 4);
        cache.add(path("e"), 5);
        // The collection kept `a` and `c`, then `e` came in.
        assert_eq!(cache.get(&path("b")), None);
        assert_eq!(cache.get(&path("a")), Some(1));
        assert_eq!(cache.get(&path("c")), Some(3));
        assert_eq!(cache.get(&path("e")), Some(5));
    }

    #[test]
    fn hints_and_removal() {
        let p = path("hint.php");
        assert!(!has_for_test(&p));
        provide_ast_hint(&p, nast::Program(vec![]), ParseType::Full);
        assert!(has_for_test(&p));
        remove_batch(&std::iter::once(p.clone()).collect());
        assert!(!has_for_test(&p));
        local_changes_push_sharedmem_stack();
        local_changes_pop_sharedmem_stack();
        assert!(std::panic::catch_unwind(local_changes_pop_sharedmem_stack).is_err());
    }

    #[test]
    fn case_insensitive() {
        let f = iequal("\\Foo");
        assert!(f("\\FOO"));
        assert!(!f("\\Fo"));
    }
}
