// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Everything a check needs that is not specific to one file: options, file
//! contents and declarations.

use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use aast_parser::rust_aast_parser_types::Env as ParserEnv;
use anyhow::Result;
use bstr::BString;
use datastore::NonEvictingStore;
use datastore::Store;
use decl_parser::DeclParser;
use decl_parser::DeclParserOptions;
use file_provider::FileProvider;
use folded_decl_provider::FoldedDeclProvider;
use folded_decl_provider::LazyFoldedDeclProvider;
use hash::DashMap;
use oxidized::decl_fold_options::DeclFoldOptions;
use oxidized::typechecker_options::TypecheckerOptions;
use pos::ConstName;
use pos::FunName;
use pos::ModuleName;
use pos::Prefix;
use pos::RelativePath;
use pos::RelativePathCtx;
use pos::TypeName;
use shallow_decl_provider::EagerShallowDeclProvider;
use shallow_decl_provider::ShallowDeclStore;
use ty::decl::ConstDecl;
use ty::decl::FoldedClass;
use ty::decl::FunDecl;
use ty::decl::ShallowClass;
use ty::decl::TypedefDecl;
use ty::decl::shallow::ModuleDecl;
use ty::decl::shallow::NamedDecl;
use ty::reason::BReason;

/// The reason type used throughout: decl types carry their positions.
pub type R = BReason;

/// File contents: an in-memory overlay (for the parts of a multifile, and for
/// files that were already read) over the disk.
#[derive(Debug)]
pub struct Files {
    path_ctx: Arc<RelativePathCtx>,
    overlay: DashMap<RelativePath, BString>,
}

impl Files {
    pub fn new(path_ctx: Arc<RelativePathCtx>) -> Self {
        Self {
            path_ctx,
            overlay: DashMap::default(),
        }
    }

    pub fn set(&self, path: RelativePath, contents: impl Into<BString>) {
        self.overlay.insert(path, contents.into());
    }

    pub fn absolute(&self, path: RelativePath) -> PathBuf {
        path.to_absolute(&self.path_ctx)
    }

    /// The length of what [`FileProvider::get`] gives, without reading the
    /// file (for the statistics of a check).
    pub fn len(&self, path: RelativePath) -> Result<usize> {
        if let Some(contents) = self.overlay.get(&path) {
            return Ok(contents.len());
        }
        Ok(std::fs::metadata(path.to_absolute(&self.path_ctx))?.len() as usize)
    }

    /// Give this thread the contents of `path` that another thread read
    /// ahead (with [`FileProvider::get`]): the next `get` of `path` on this
    /// thread takes them instead of reading the file again. `None` forgets
    /// what was given and not taken.
    pub fn set_read_ahead(&self, read_ahead: Option<(RelativePath, BString)>) {
        READ_AHEAD.set(read_ahead);
    }
}

thread_local! {
    /// See [`Files::set_read_ahead`].
    static READ_AHEAD: std::cell::Cell<Option<(RelativePath, BString)>> =
        const { std::cell::Cell::new(None) };
}

impl FileProvider for Files {
    fn get(&self, path: RelativePath) -> Result<BString> {
        if let Some((read_path, contents)) = READ_AHEAD.take() {
            if read_path == path {
                return Ok(contents);
            }
            READ_AHEAD.set(Some((read_path, contents)));
        }
        if let Some(contents) = self.overlay.get(&path) {
            return Ok(contents.clone());
        }
        Ok(std::fs::read(path.to_absolute(&self.path_ctx))?.into())
    }
}

/// `Symbol.new s`: the interned symbol of `s`, through a table of the
/// thread in front of the global table of `intern`, which every thread
/// locks (if only to read) and which the typing of names looks up all the
/// time (to find a class, a member, an ancestor...). An interned string
/// keeps its symbol for ever, so the table of a thread cannot go stale; the
/// first use of a string in the process interns it in the global table as
/// before. The keys are the strings of the symbols themselves (`'static`).
pub fn symbol(s: &str) -> pos::Symbol {
    thread_local! {
        static SYMBOLS: std::cell::RefCell<hash::HashMap<&'static str, pos::Symbol>> =
            Default::default();
    }
    SYMBOLS.with_borrow_mut(|symbols| match symbols.get(s) {
        Some(symbol) => *symbol,
        None => {
            let symbol = pos::Symbol::new(s);
            symbols.insert(symbol.as_str(), symbol);
            symbol
        }
    })
}

/// Where a declaration is, which decides which of two declarations of one
/// name the name is bound to: `Naming_global.ndecl_file_and_get_conflict_files`
/// is called on the files in the order of `Relative_path.Map` (by prefix,
/// then by suffix), and `make_env_and_check_not_already_bound` binds the
/// names of a file in lexical order, the classes before the typedefs (they
/// share a namespace). The first declaration of a name wins.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DeclOrder {
    file: RelativePath,
    /// 0, or 1 for a typedef.
    rank: u8,
    /// The index of the decl in the decls of the file, in lexical order.
    index: u32,
}

/// The declaration a name is bound to (see [`DeclOrder`]).
#[derive(Clone, Copy, Debug)]
pub struct Bound<K> {
    /// The name as declared.
    pub name: K,
    order: DeclOrder,
    /// For a type: whether it is a typedef (else a class).
    is_typedef: bool,
}

/// The names of a kind of symbol, by their lowercase form (`String.lowercase`
/// of Core: ASCII only): what
/// `Naming_provider.get_type_canon_name` and `get_fun_canon_name` look names
/// up in, to suggest the declared spelling of a name that only differs by
/// case. Only the winning declaration of a name is bound
/// ([`Ctx::declare_file`]).
pub type CanonNames<K> = Arc<DashMap<String, Bound<K>>>;

/// The decl stores of a `Ctx` (those of its `shallow_decls`), and the
/// declarations the names of the case-sensitive namespaces are bound to.
#[derive(Default)]
pub(crate) struct DeclStores {
    classes: Arc<NonEvictingStore<TypeName, Arc<ShallowClass<R>>>>,
    typedefs: Arc<NonEvictingStore<TypeName, Arc<TypedefDecl<R>>>>,
    funs: Arc<NonEvictingStore<FunName, Arc<FunDecl<R>>>>,
    consts: Arc<NonEvictingStore<ConstName, Arc<ConstDecl<R>>>>,
    modules: Arc<NonEvictingStore<ModuleName, Arc<ModuleDecl<R>>>>,
    const_names: DashMap<ConstName, DeclOrder>,
    module_names: DashMap<ModuleName, DeclOrder>,
    /// The store of the folded classes of `Ctx::folded_decls` (for
    /// [`Ctx::remove_folded_classes`] and friends).
    folded_classes: Arc<NonEvictingStore<TypeName, Arc<FoldedClass<R>>>>,
    /// The old declarations of the daemon (plan D3): what the OCaml's Rust
    /// backend keeps under `old$name` keys in the same stores.
    #[cfg(feature = "port")]
    old: std::sync::Mutex<OldDecls>,
    /// The daemon's reverse naming table (plan D4), built by
    /// [`Ctx::build_dep_hash_index`] after the init; the batch checker has
    /// none.
    #[cfg(feature = "port")]
    reverse: std::sync::OnceLock<reverse_naming::ReverseNamingTable>,
    /// Set with `reverse` (the daemon): a lookup that misses in a store
    /// parses the file the reverse naming table binds the name to
    /// ([`LazyStore`]).
    #[cfg(feature = "port")]
    lazy: std::sync::OnceLock<LazyParse>,
    /// The `Local_memory` backend (the IDE daemon's, L0), when the `Ctx` was
    /// made by [`Ctx::new_local_memory`]: its stores (`shallow_decls`,
    /// `folded_decls`) are then the bounded caches of the backend, and its
    /// naming table the backend's delta over SQLite; the stores above are
    /// unused.
    #[cfg(feature = "port")]
    local: Option<Arc<local_memory::LmParse>>,
    /// `Shared_db_settings` (`Db_path_provider`, the `Shared_memory`
    /// backend): the path of the SQLite naming table the reverse naming
    /// table falls back to (a saved-state init, L0).
    #[cfg(feature = "port")]
    pub(crate) shared_db_path: std::sync::RwLock<Option<crate::naming_sqlite::DbPath>>,
    /// The stacks of local changes of the decl heaps
    /// (`Decl_provider.local_changes_push_sharedmem_stack`: the shallow
    /// classes and `Decl_store`'s heaps), pushed and popped around a
    /// quarantine (L0).
    #[cfg(feature = "port")]
    local_decls: LocalDecls,
}

/// See [`DeclStores::local_decls`].
#[cfg(feature = "port")]
#[derive(Default)]
struct LocalDecls {
    classes: reverse_naming::Frames<TypeName, Arc<ShallowClass<R>>>,
    typedefs: reverse_naming::Frames<TypeName, Arc<TypedefDecl<R>>>,
    funs: reverse_naming::Frames<FunName, Arc<FunDecl<R>>>,
    consts: reverse_naming::Frames<ConstName, Arc<ConstDecl<R>>>,
    modules: reverse_naming::Frames<ModuleName, Arc<ModuleDecl<R>>>,
    folded: reverse_naming::Frames<TypeName, Arc<FoldedClass<R>>>,
}

/// The `ShallowDeclStore` of the stores: over the stores themselves without
/// the feature `port`; with it, over [`LazyStore`]s, which find what the
/// daemon removed again (and are the stores themselves until the daemon
/// builds its reverse naming table).
fn shallow_decl_store(stores: &Arc<DeclStores>) -> Arc<ShallowDeclStore<R>> {
    #[cfg(not(feature = "port"))]
    return Arc::new(ShallowDeclStore::with_no_member_stores(
        stores.classes.clone(),
        stores.typedefs.clone(),
        stores.funs.clone(),
        stores.consts.clone(),
        stores.modules.clone(),
    ));
    #[cfg(feature = "port")]
    {
        use oxidized::naming_types::KindOfType;
        fn type_path(
            table: &reverse_naming::ReverseNamingTable,
            name: TypeName,
            kind: KindOfType,
        ) -> Option<RelativePath> {
            match table.get_type_pos(name.as_str()) {
                Some((pos, k)) if k == kind => Some(pos.path()),
                Some(_) | None => None,
            }
        }
        Arc::new(ShallowDeclStore::with_no_member_stores(
            Arc::new(LazyStore {
                stores: Arc::clone(stores),
                store: |stores| &stores.classes,
                frames: |stores| &stores.local_decls.classes,
                path_of: |table, name| type_path(table, name, KindOfType::TClass),
                extract: |decl, key| match decl {
                    NamedDecl::Class(name, decl) if *name == key => Some(Arc::new(decl.clone())),
                    _ => None,
                },
            }),
            Arc::new(LazyStore {
                stores: Arc::clone(stores),
                store: |stores| &stores.typedefs,
                frames: |stores| &stores.local_decls.typedefs,
                path_of: |table, name| type_path(table, name, KindOfType::TTypedef),
                extract: |decl, key| match decl {
                    NamedDecl::Typedef(name, decl) if *name == key => Some(Arc::new(decl.clone())),
                    _ => None,
                },
            }),
            Arc::new(LazyStore {
                stores: Arc::clone(stores),
                store: |stores| &stores.funs,
                frames: |stores| &stores.local_decls.funs,
                path_of: |table, name| table.get_fun_pos(name.as_str()).map(|pos| pos.path()),
                extract: |decl, key| match decl {
                    NamedDecl::Fun(name, decl) if *name == key => Some(Arc::new(decl.clone())),
                    _ => None,
                },
            }),
            Arc::new(LazyStore {
                stores: Arc::clone(stores),
                store: |stores| &stores.consts,
                frames: |stores| &stores.local_decls.consts,
                path_of: |table, name| table.get_const_pos(name.as_str()).map(|pos| pos.path()),
                extract: |decl, key| match decl {
                    NamedDecl::Const(name, decl) if *name == key => Some(Arc::new(decl.clone())),
                    _ => None,
                },
            }),
            Arc::new(LazyStore {
                stores: Arc::clone(stores),
                store: |stores| &stores.modules,
                frames: |stores| &stores.local_decls.modules,
                path_of: |table, name| table.get_module_pos(name.as_str()).map(|pos| pos.path()),
                extract: |decl, key| match decl {
                    NamedDecl::Module(name, decl) if *name == key => Some(Arc::new(decl.clone())),
                    _ => None,
                },
            }),
        ))
    }
}

/// What a [`LazyStore`] parses with.
#[cfg(feature = "port")]
struct LazyParse {
    parser: DeclParser<R>,
    files: Arc<Files>,
}

/// A store of the decls of one kind that, in the daemon, behaves as the
/// OCaml's decl lookups of the `Shared_memory` backend (which the OCaml
/// daemon runs: `Decl_provider_internals.get_fun_without_pessimise`,
/// `get_shallow_class`, ...): a name the store does not have is looked up in
/// the reverse naming table (`Naming_provider.get_class_path`,
/// `get_typedef_path`, `get_fun_path`, ...: of its own kind), and the file it
/// is bound to is parsed with its decls cached
/// (`find_in_direct_decl_parse ~cache_results:true`:
/// `direct_decl_parse_and_cache`, i.e. [`Ctx::add_shallow_decls`]); the
/// answer is the decl found in the parse, not in the store. This is how
/// removed decls come back (`test_lazy_decl_idempotence`). Before the daemon
/// builds its reverse naming table (and always in the batch checker), a miss
/// is a miss. A file that no longer exists reads as `""` (`File_provider`).
#[cfg(feature = "port")]
struct LazyStore<K: std::hash::Hash + Eq, V> {
    stores: Arc<DeclStores>,
    store: fn(&DeclStores) -> &NonEvictingStore<K, V>,
    /// The local changes of the store (see [`DeclStores::local_decls`]).
    frames: fn(&DeclStores) -> &reverse_naming::Frames<K, V>,
    path_of: fn(&reverse_naming::ReverseNamingTable, K) -> Option<RelativePath>,
    /// `Shallow_decl_defs.to_*_decl_opt` of a decl named `K`.
    extract: fn(&NamedDecl<R>, K) -> Option<V>,
}

#[cfg(feature = "port")]
impl<K, V> std::fmt::Debug for LazyStore<K, V>
where
    K: std::hash::Hash + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LazyStore").finish()
    }
}

#[cfg(feature = "port")]
impl<K, V> Store<K, V> for LazyStore<K, V>
where
    K: Copy + Send + Sync + std::hash::Hash + Eq,
    V: Clone + Send + Sync,
{
    fn get(&self, key: K) -> Result<Option<V>> {
        let store = (self.store)(&self.stores);
        let frames = (self.frames)(&self.stores);
        // With local changes: what they say, a removed key being a miss.
        let local = if frames.active() { frames.get(&key) } else { None };
        match local {
            Some(Some(v)) => return Ok(Some(v)),
            Some(None) => {}
            None => {
                if let res @ Some(_) = store.get(key)? {
                    return Ok(res);
                }
            }
        }
        if let Some(lazy) = self.stores.lazy.get() {
            if let Some(table) = self.stores.reverse.get() {
                if let Some(path) = (self.path_of)(table, key) {
                    let text = match lazy.files.get(path) {
                        Ok(text) => text,
                        Err(err) => match err.downcast_ref::<std::io::Error>() {
                            Some(err) if err.kind() == std::io::ErrorKind::NotFound => BString::from(""),
                            _ => return Err(err),
                        },
                    };
                    let decls = lazy.parser.parse_with_text(path, &text)?;
                    // `find_in_direct_decl_parse`: the first decl of the
                    // name and kind in `pfh_decls`, which is in reverse
                    // lexical order (so the last one of the file), whatever
                    // the cache keeps.
                    let found = decls.iter().rev().find_map(|decl| (self.extract)(decl, key));
                    add_shallow_decls_to(&self.stores, path, decls);
                    return Ok(found);
                }
            }
        }
        Ok(None)
    }

    fn insert(&self, key: K, val: V) -> Result<()> {
        let frames = (self.frames)(&self.stores);
        if frames.active() {
            frames.set(key, Some(val));
            return Ok(());
        }
        (self.store)(&self.stores).insert(key, val)
    }

    fn contains_key(&self, key: K) -> Result<bool> {
        Ok(self.get(key)?.is_some())
    }

    fn remove_batch(&self, keys: &mut dyn Iterator<Item = K>) -> Result<()> {
        let frames = (self.frames)(&self.stores);
        if frames.active() {
            for key in keys {
                frames.set(key, None);
            }
            return Ok(());
        }
        (self.store)(&self.stores).remove_batch(keys)
    }
}

/// The store of the folded classes, with its local changes (see
/// [`DeclStores::local_decls`]).
#[cfg(feature = "port")]
struct FoldedStore {
    stores: Arc<DeclStores>,
}

#[cfg(feature = "port")]
impl std::fmt::Debug for FoldedStore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("FoldedStore")
    }
}

#[cfg(feature = "port")]
impl Store<TypeName, Arc<FoldedClass<R>>> for FoldedStore {
    fn get(&self, key: TypeName) -> Result<Option<Arc<FoldedClass<R>>>> {
        let frames = &self.stores.local_decls.folded;
        if frames.active() {
            match frames.get(&key) {
                Some(found) => return Ok(found),
                None => {}
            }
        }
        self.stores.folded_classes.get(key)
    }

    fn insert(&self, key: TypeName, val: Arc<FoldedClass<R>>) -> Result<()> {
        let frames = &self.stores.local_decls.folded;
        if frames.active() {
            frames.set(key, Some(val));
            return Ok(());
        }
        self.stores.folded_classes.insert(key, val)
    }

    fn remove_batch(&self, keys: &mut dyn Iterator<Item = TypeName>) -> Result<()> {
        let frames = &self.stores.local_decls.folded;
        if frames.active() {
            for key in keys {
                frames.set(key, None);
            }
            return Ok(());
        }
        self.stores.folded_classes.remove_batch(keys)
    }
}

/// The folded-class store of a `Ctx` over `stores`.
fn folded_store(stores: &Arc<DeclStores>) -> Arc<dyn Store<TypeName, Arc<FoldedClass<R>>>> {
    #[cfg(not(feature = "port"))]
    return stores.folded_classes.clone();
    #[cfg(feature = "port")]
    Arc::new(FoldedStore {
        stores: Arc::clone(stores),
    })
}

/// Binds `name` (up to case) to the declaration at `order` unless it is
/// bound to one that comes first; `insert` puts the declaration in its store,
/// `remove` takes out the one it replaces under another spelling or kind.
/// The entry stays locked while the stores change, so that the stores agree
/// with `names` whatever the order of the calls.
fn bind<K>(
    names: &CanonNames<K>,
    name: K,
    order: DeclOrder,
    is_typedef: bool,
    remove: impl FnOnce(Bound<K>),
    insert: impl FnOnce() -> Result<()>,
) where
    K: Copy + Eq + AsRef<str>,
{
    let bound = Bound {
        name,
        order,
        is_typedef,
    };
    let mut insert = Some(insert);
    let mut remove = Some(remove);
    names
        .entry(name.as_ref().to_ascii_lowercase())
        .and_modify(|previous| {
            if order < previous.order {
                if previous.name != name || previous.is_typedef != is_typedef {
                    (remove.take().unwrap())(*previous);
                }
                let _ = (insert.take().unwrap())();
                *previous = bound;
            }
        })
        .or_insert_with(|| {
            let _ = (insert.take().unwrap())();
            bound
        });
}

/// [`bind`] for a case-sensitive namespace (constants, modules), whose
/// store is keyed by the name: a replaced declaration is overwritten.
fn bind_exact<K>(
    names: &DashMap<K, DeclOrder>,
    name: K,
    order: DeclOrder,
    insert: impl FnOnce() -> Result<()>,
) where
    K: Copy + Eq + std::hash::Hash,
{
    let mut insert = Some(insert);
    names
        .entry(name)
        .and_modify(|previous| {
            if order < *previous {
                let _ = (insert.take().unwrap())();
                *previous = order;
            }
        })
        .or_insert_with(|| {
            let _ = (insert.take().unwrap())();
            order
        });
}

/// `magic_builtins` of `hh_single_type_check.ml`: "All of the stuff that
/// hh_single_type_check relies on is sadly not contained in the hhi library,
/// so we include a very small number of magic builtins".
///
/// These belong to `hh single` only (`hh_server` does not declare them): see
/// [`Ctx::add_magic_builtins`].
const MAGIC_BUILTINS: (&str, &str) = (
    "hh_single_type_check_magic.hhi",
    "<?hh
namespace {
<<__NoAutoDynamic, __SupportDynamicType>> function hh_show<T>(<<__AcceptDisposable>> readonly T $val)[]:T {}
<<__NoAutoDynamic, __SupportDynamicType>> function hh_expect<T>(<<__AcceptDisposable>> readonly T $val)[]:T {}
<<__NoAutoDynamic, __SupportDynamicType>> function hh_expect_equivalent<T>(<<__AcceptDisposable>> readonly T $val)[]:T {}
<<__NoAutoDynamic>> function hh_show_env()[]:void {}
<<__NoAutoDynamic>> function hh_log_level(string $key, int $level)[]:void {}
<<__NoAutoDynamic>> function hh_force_solve()[]:void {}<<__NoAutoDynamic>> function hh_time(string $command, string $tag = '_'):void {}
<<__NoAutoDynamic>> function hh_sleep(int $seconds)[]:void {}
}
",
);

/// A clone shares the stores and the files: `Provider_context.map_tcopt` and
/// friends copy the context with one field changed, as OCaml copies its
/// record.
#[derive(Clone)]
pub struct Ctx {
    pub tco: Arc<TypecheckerOptions>,
    pub parser_env: ParserEnv,
    pub path_ctx: Arc<RelativePathCtx>,
    pub files: Arc<Files>,
    pub decl_parser: DeclParser<R>,
    pub shallow_decls: Arc<ShallowDeclStore<R>>,
    /// The stores of `shallow_decls`, which [`Ctx::declare_file`] fills.
    pub(crate) decl_stores: Arc<DeclStores>,
    pub folded_decls: Arc<dyn FoldedDeclProvider<R>>,
    /// The hhi files. They are not on disk: their contents are in `files`.
    pub hhi_paths: Vec<RelativePath>,
    /// The declared classes and typedefs, by lowercase name.
    pub type_canon_names: CanonNames<TypeName>,
    /// The declared functions, by lowercase name.
    pub fun_canon_names: CanonNames<FunName>,
    /// `Provider_context.get_deps_mode`: how the dependencies found by
    /// typing are recorded.
    #[cfg(feature = "port")]
    pub deps_mode: crate::typing_deps::mode::T,
    /// `Provider_context.get_entries`: the files that the context has data
    /// of its own for (open in an editor, say).
    #[cfg(feature = "port")]
    pub entries: crate::provider_context::Entries,
}

impl Ctx {
    /// Declares the magic builtins of `hh_single_type_check` (`hh_show`,
    /// `hh_expect`, ...) with the hhi files. Only `hh single` does.
    pub fn add_magic_builtins(&mut self) {
        let (name, contents) = MAGIC_BUILTINS;
        let path = RelativePath::new(Prefix::Hhi, name);
        self.files.set(path, contents);
        self.hhi_paths.push(path);
    }

    /// `root` is the directory paths are relative to.
    pub fn new(root: &Path, tco: TypecheckerOptions) -> Result<Self> {
        let path_ctx = Arc::new(RelativePathCtx {
            root: root.to_path_buf(),
            hhi: PathBuf::from("/hhi"),
            dummy: PathBuf::new(),
            tmp: PathBuf::new(),
        });
        let files = Arc::new(Files::new(Arc::clone(&path_ctx)));
        let mut hhi_paths = Vec::with_capacity(hhi::HHI_CONTENTS.len());
        for (name, contents) in hhi::HHI_CONTENTS {
            let path = RelativePath::new(Prefix::Hhi, name);
            files.set(path, *contents);
            hhi_paths.push(path);
        }
        let file_provider: Arc<dyn FileProvider> = files.clone();

        let decl_parser = DeclParser::<R>::new(
            file_provider,
            DeclParserOptions::from_parser_options(&tco.po),
        );

        let type_canon_names = CanonNames::<TypeName>::default();
        let fun_canon_names = CanonNames::<FunName>::default();
        let decl_stores = Arc::new(DeclStores::default());
        let shallow_decls = shallow_decl_store(&decl_stores);
        let folded_decls: Arc<dyn FoldedDeclProvider<R>> = Arc::new(LazyFoldedDeclProvider::new(
            Arc::new(DeclFoldOptions::from_global_options(&tco)),
            folded_store(&decl_stores),
            Arc::new(EagerShallowDeclProvider::new(Arc::clone(&shallow_decls))),
        ));

        let parser_env = ParserEnv {
            elaborate_namespaces: true,
            // `HH_FIXME` comments suppress errors.
            scour_comments: true,
            parser_options: tco.po.clone(),
            ..Default::default()
        };

        Ok(Self {
            tco: Arc::new(tco),
            parser_env,
            path_ctx,
            files,
            decl_parser,
            shallow_decls,
            decl_stores,
            folded_decls,
            hhi_paths,
            type_canon_names,
            fun_canon_names,
            // As `hh_single_type_check` makes its context.
            #[cfg(feature = "port")]
            deps_mode: crate::typing_deps::mode::T::InMemoryMode(None),
            #[cfg(feature = "port")]
            entries: Default::default(),
        })
    }

    /// Puts the decls of the file `path` (as the decl parser gives them, in
    /// lexical order) into the decl stores, each only if its name is not
    /// already bound to a declaration that comes first (see [`DeclOrder`]):
    /// the losers are left out, as `Naming_global.make_env_and_check_not_already_bound`
    /// leaves them out of the naming table, and a winner that comes after
    /// a loser (when the files are declared in parallel) takes its place.
    /// Whatever the order the files are declared in, the stores end up with
    /// the decls the OCaml binds the names to. (The "Name already bound"
    /// errors are reported by typing, `Typing_toplevel.check_if_this_def_is_the_winner`.)
    pub fn declare_file(&self, path: RelativePath, decls: Vec<NamedDecl<R>>) {
        let stores = &*self.decl_stores;
        for (index, decl) in decls.into_iter().enumerate() {
            let order = |rank| DeclOrder {
                file: path,
                rank,
                index: index as u32,
            };
            match decl {
                NamedDecl::Class(name, decl) => {
                    self.bind_type(name, order(0), false, || {
                        stores.classes.insert(name, Arc::new(decl))
                    })
                }
                NamedDecl::Typedef(name, decl) => {
                    self.bind_type(name, order(1), true, || {
                        stores.typedefs.insert(name, Arc::new(decl))
                    })
                }
                NamedDecl::Fun(name, decl) => {
                    let remove = |loser: Bound<FunName>| {
                        let _ = stores.funs.remove_batch(&mut std::iter::once(loser.name));
                    };
                    bind(&self.fun_canon_names, name, order(0), false, remove, || {
                        stores.funs.insert(name, Arc::new(decl))
                    })
                }
                NamedDecl::Const(name, decl) => {
                    bind_exact(&stores.const_names, name, order(0), || {
                        stores.consts.insert(name, Arc::new(decl))
                    })
                }
                NamedDecl::Module(name, decl) => {
                    bind_exact(&stores.module_names, name, order(0), || {
                        stores.modules.insert(name, Arc::new(decl))
                    })
                }
            }
        }
    }

    /// Classes and typedefs share their namespace.
    fn bind_type(
        &self,
        name: TypeName,
        order: DeclOrder,
        is_typedef: bool,
        insert: impl FnOnce() -> Result<()>,
    ) {
        let stores = &*self.decl_stores;
        let remove = |loser: Bound<TypeName>| {
            let mut keys = std::iter::once(loser.name);
            let _ = if loser.is_typedef {
                stores.typedefs.remove_batch(&mut keys)
            } else {
                stores.classes.remove_batch(&mut keys)
            };
        };
        bind(&self.type_canon_names, name, order, is_typedef, remove, insert)
    }

    /// `Naming_provider.get_type_canon_name`: the class or typedef whose name
    /// is `name` up to case.
    pub fn get_type_canon_name(&self, name: &str) -> Option<TypeName> {
        let lower = name.to_ascii_lowercase();
        #[cfg(feature = "port")]
        if let Some(table) = self.decl_stores.reverse.get() {
            if table.type_canon.active() {
                if let Some(found) = table.type_canon.get(&lower) {
                    return found.map(|bound| bound.name);
                }
            }
        }
        self.type_canon_names.get(&lower).map(|entry| entry.value().name)
    }

    /// `Naming_provider.get_fun_canon_name`: the function whose name is
    /// `name` up to case.
    pub fn get_fun_canon_name(&self, name: &str) -> Option<FunName> {
        let lower = name.to_ascii_lowercase();
        #[cfg(feature = "port")]
        if let Some(table) = self.decl_stores.reverse.get() {
            if table.fun_canon.active() {
                if let Some(found) = table.fun_canon.get(&lower) {
                    return found.map(|bound| bound.name);
                }
            }
        }
        self.fun_canon_names.get(&lower).map(|entry| entry.value().name)
    }

    /// The path of a file under the root.
    pub fn relative_path(&self, path: &Path) -> RelativePath {
        match path.strip_prefix(&self.path_ctx.root) {
            Ok(suffix) => RelativePath::new(Prefix::Root, suffix),
            Err(_) => RelativePath::new(Prefix::Dummy, path),
        }
    }
}

/// The lazy contexts (L0, plan §7.3/§7.4): made from a naming table in
/// SQLite instead of parsing every file.
#[cfg(feature = "port")]
impl Ctx {
    /// `Provider_backend.set_local_memory_backend ~max_num_decls
    /// ~max_num_folded_class_decls ~max_num_shallow_class_decls` (which logs
    /// the sizes), then `Provider_context.empty_for_tool` with that backend:
    /// the context of the IDE daemon (`ClientIdeDaemon.initialize1` gives
    /// 5000, 5000 and 20000). Its decls are parsed on demand into the bounded
    /// caches of the backend (`crate::provider_backend::LocalMemory`); its
    /// reverse naming table is the backend's delta over the SQLite naming
    /// table that `naming_table::load_from_sqlite` gives it
    /// (`Db_path_provider.set_naming_db_path`: `naming_db_path_ref`).
    pub fn new_local_memory(
        root: &Path,
        tco: TypecheckerOptions,
        max_num_decls: usize,
        max_num_folded_class_decls: usize,
        max_num_shallow_class_decls: usize,
    ) -> Result<Self> {
        let mut ctx = Ctx::new(root, tco)?;
        let lm = crate::provider_backend::set_local_memory_backend(
            max_num_decls,
            max_num_folded_class_decls,
            max_num_shallow_class_decls,
            ctx.deps_mode.clone(),
        );
        ctx.install_local_memory(lm);
        Ok(ctx)
    }

    /// `Provider_backend.set_local_memory_backend_with_defaults_for_test`
    /// (5000, 5000, 20000, without the log line).
    pub fn new_local_memory_with_defaults_for_test(root: &Path, tco: TypecheckerOptions) -> Result<Self> {
        let mut ctx = Ctx::new(root, tco)?;
        let lm = crate::provider_backend::make_local_memory(5000, 5000, 20000, ctx.deps_mode.clone());
        ctx.install_local_memory(lm);
        Ok(ctx)
    }

    /// The stores of `self` become those of the `Local_memory` backend `lm`.
    /// (The parser options of the decl parser and of the context are those
    /// of `self` at this point: `empty_for_tool` makes the context with them.)
    pub fn install_local_memory(&mut self, lm: crate::provider_backend::LocalMemory) {
        let base = Arc::new(local_memory::LmParse {
            lm: Arc::new(lm),
            parser: self.decl_parser.clone(),
            files: Arc::clone(&self.files),
            popt: self.parser_env.parser_options.clone(),
            entries: Default::default(),
        });
        self.decl_stores = Arc::new(DeclStores {
            local: Some(Arc::clone(&base)),
            ..Default::default()
        });
        let (shallow_decls, folded_decls) = local_memory::stores(&self.tco, base);
        self.shallow_decls = shallow_decls;
        self.folded_decls = folded_decls;
        self.type_canon_names = Default::default();
        self.fun_canon_names = Default::default();
    }

    /// The `Shared_memory` backend of `hh_server` after a saved-state load
    /// (plan §7.4): nothing declared, an empty reverse naming table (as
    /// `Ctx::build_dep_hash_index` makes it after an init that declared
    /// nothing) whose lookups fall back to the SQLite naming table `naming`
    /// (`Naming_heap.get_and_cache`), and decls parsed on demand from the
    /// file a name is bound to ([`LazyStore`]). `naming_table::load_from_sqlite`
    /// on this context then applies the database's local changes.
    pub fn new_lazy(root: &Path, tco: TypecheckerOptions, naming: Arc<crate::naming_sqlite::DbPath>) -> Result<Self> {
        let ctx = Ctx::new(root, tco)?;
        ctx.build_dep_hash_index();
        crate::db_path_provider::set_naming_db_path(&ctx, Some(crate::naming_sqlite::DbPath::clone(&naming)));
        Ok(ctx)
    }

    /// `Provider_context.get_backend`
    pub fn get_backend(&self) -> crate::provider_backend::T {
        match &self.decl_stores.local {
            Some(base) => crate::provider_backend::T::LocalMemory(Arc::clone(&base.lm)),
            None => crate::provider_backend::T::SharedMemory,
        }
    }

    /// The `Local_memory` backend of the context, if it has that one.
    #[inline]
    pub fn local_memory(&self) -> Option<&Arc<crate::provider_backend::LocalMemory>> {
        match &self.decl_stores.local {
            Some(base) => Some(&base.lm),
            None => None,
        }
    }
}

/// `ctx` with `entries`, for a context of the `Local_memory` backend
/// (`Provider_context.add_or_overwrite_entry` and friends): the same caches
/// (the OCaml's are the backend's, whatever the context), read through
/// stores whose misses ask the naming table with these entries and parse the
/// contents of an entry for a name it declares (`Naming_provider` and
/// `Direct_decl_utils.get_file_contents` look at the entries first), as the
/// OCaml's lookups with this context do.
#[cfg(feature = "port")]
pub fn local_memory_with_entries(ctx: &Ctx, entries: crate::provider_context::Entries) -> Ctx {
    let base = match &ctx.decl_stores.local {
        Some(base) => base,
        None => panic!("Ctx: local_memory_with_entries of a context without the Local_memory backend"),
    };
    let lm_parse = Arc::new(local_memory::LmParse {
        entries: entries.clone(),
        ..local_memory::LmParse::clone(base)
    });
    let (shallow_decls, folded_decls) = local_memory::stores(&ctx.tco, lm_parse);
    Ctx {
        entries,
        shallow_decls,
        folded_decls,
        ..ctx.clone()
    }
}

/// The stores of a context of the `Local_memory` backend (L0): the bounded
/// caches of `crate::provider_backend::LocalMemory`, filled on a miss as the
/// OCaml's `Local_memory` branches of `Decl_provider_internals` and
/// `Direct_decl_utils.cache_decls` do.
#[cfg(feature = "port")]
pub(crate) mod local_memory {
    use std::hash::Hash;

    use ty::decl::shallow::NamedDecl;

    use super::*;
    use crate::lfu_cache;
    use crate::naming_provider::local_memory as naming;
    use crate::provider_backend::LocalMemory;
    use crate::provider_backend::decl_cache_entry::Key;
    use crate::provider_backend::decl_cache_entry::Value;
    use crate::typing_deps::dep;

    /// What the stores of a context parse with, and the naming table (with
    /// the entries of the context) their misses ask.
    #[derive(Clone)]
    pub(crate) struct LmParse {
        pub(crate) lm: Arc<LocalMemory>,
        pub(crate) parser: DeclParser<R>,
        pub(crate) files: Arc<Files>,
        pub(crate) popt: oxidized::parser_options::ParserOptions,
        pub(crate) entries: crate::provider_context::Entries,
    }

    impl LmParse {
        fn view(&self) -> naming::View<'_> {
            naming::View {
                local_memory: &self.lm,
                entries: &self.entries,
                popt: &self.popt,
            }
        }

        /// `Direct_decl_utils.direct_decl_parse_and_cache ctx file`
        /// (`Local_memory`), inside `find_in_direct_decl_parse
        /// ~cache_results:true`: the decls of `file` (in lexical order),
        /// from the contents of its entry if it has one, else of the file
        /// on disk (`File_provider.get_contents`: `None` when the file
        /// cannot be read, and then `Decl_not_found` for `name`); those that
        /// win their names are cached (`cache_decls`).
        fn direct_decl_parse_and_cache(&self, file: &crate::relative_path::RelativePath, name: &str) -> Vec<NamedDecl<R>> {
            let parsed = crate::counters::count(crate::counters::category::T::Direct_decl_parse, || {
                let path = pos::RelativePath::from(file);
                // `get_file_contents ~ignore_file_content_caches:false`
                let contents = match self.entries.get(file) {
                    Some(entry) => Some(BString::from(crate::full_fidelity_source_text::text(
                        &crate::ast_provider::compute_source_text(entry),
                    ))),
                    None => FileProvider::get(&*self.files, path).ok(),
                };
                contents.and_then(|contents| self.parser.parse_with_text(path, &contents).ok())
            });
            match parsed {
                None => crate::decl_defs::raise_decl_not_found(Some(file), name),
                Some(decls) => {
                    self.cache_decls(file, &decls);
                    decls
                }
            }
        }

        /// `Direct_decl_utils.cache_decls ctx file decls` (`Local_memory`):
        /// the first decl of each name (`dedup_decls`) whose name is not
        /// bound to another file (`remove_naming_conflict_losers`), added to
        /// the caches where they have no entry for it (`find_or_add`); a
        /// class added also gets its `Extends` edges
        /// (`add_extends_dep_edges`).
        fn cache_decls(&self, file: &crate::relative_path::RelativePath, decls: &[NamedDecl<R>]) {
            let v = self.view();
            let mut seen_types = std::collections::HashSet::new();
            let mut seen_funs = std::collections::HashSet::new();
            let mut seen_consts = std::collections::HashSet::new();
            let mut seen_modules = std::collections::HashSet::new();
            let wins = |path: Option<crate::relative_path::RelativePath>| match path {
                Some(nfile) => nfile == *file,
                None => true,
            };
            let path_of = |pos: Option<crate::file_info::Pos>| pos.map(|pos| crate::file_info::get_pos_filename(&pos));
            for decl in decls {
                let keep = match decl {
                    NamedDecl::Class(name, _) | NamedDecl::Typedef(name, _) => {
                        seen_types.insert(*name)
                            && wins(path_of(naming::get_type_pos_and_kind(&v, name.as_str()).map(|(pos, _)| pos)))
                    }
                    NamedDecl::Fun(name, _) => {
                        seen_funs.insert(*name) && wins(path_of(naming::get_fun_pos(&v, name.as_str())))
                    }
                    NamedDecl::Const(name, _) => {
                        seen_consts.insert(*name) && wins(path_of(naming::get_const_pos(&v, name.as_str())))
                    }
                    NamedDecl::Module(name, _) => {
                        seen_modules.insert(*name) && wins(path_of(naming::get_module_pos(&v, name.as_str())))
                    }
                };
                if !keep {
                    continue;
                }
                let lm = &self.lm;
                match decl {
                    NamedDecl::Class(name, d) => {
                        lfu_cache::find_or_add(&lm.shallow_decl_cache, *name, || {
                            self.add_extends_dep_edges(*name, d);
                            Some(Arc::new(d.clone()))
                        });
                    }
                    NamedDecl::Fun(name, d) => {
                        lfu_cache::find_or_add(&lm.decl_cache, Key::FunDecl(*name), || {
                            Some(Value::Fun(Arc::new(d.clone())))
                        });
                    }
                    NamedDecl::Typedef(name, d) => {
                        lfu_cache::find_or_add(&lm.decl_cache, Key::TypedefDecl(*name), || {
                            Some(Value::Typedef(Arc::new(d.clone())))
                        });
                    }
                    NamedDecl::Const(name, d) => {
                        lfu_cache::find_or_add(&lm.decl_cache, Key::GconstDecl(*name), || {
                            Some(Value::Gconst(Arc::new(d.clone())))
                        });
                    }
                    NamedDecl::Module(name, d) => {
                        lfu_cache::find_or_add(&lm.decl_cache, Key::ModuleDecl(*name), || {
                            Some(Value::Module(Arc::new(d.clone())))
                        });
                    }
                }
            }
        }

        /// `add_extends_dep_edges ctx class_ dep_table`: `Extends` dep
        /// edges from each parent of the class to the class itself, and the
        /// class name of its dep hash in `dep_table`.
        fn add_extends_dep_edges(&self, cls_name: TypeName, cls: &ShallowClass<R>) {
            let parents = crate::decl_utils::parentish_names(cls);
            let cls_name = cls_name.as_str().to_string();
            self.lm
                .dep_table
                .lock()
                .unwrap()
                .insert(dep::make(&dep::Variant::Type(cls_name.clone())), cls_name.clone());
            for parent in parents.iter() {
                crate::typing_deps::add_idep(
                    &self.lm.deps_mode,
                    &dep::Variant::Type(cls_name.clone()),
                    &dep::Variant::Extends(parent.clone()),
                );
            }
        }
    }

    /// One kind of decls and the cache that holds it.
    trait Kind {
        type K: Copy + Eq + Hash + Send + Sync + AsRef<str>;
        type V: Clone + Send + Sync;
        /// `find_or_add` of the cache.
        fn find_or_add(lm: &LocalMemory, key: Self::K, default: &mut dyn FnMut() -> Option<Self::V>) -> Option<Self::V>;
        fn add(lm: &LocalMemory, key: Self::K, v: Self::V);
        fn remove(lm: &LocalMemory, key: Self::K);
        /// `Naming_provider.get_class_path` and friends.
        fn path_of(v: &naming::View<'_>, key: Self::K) -> Option<crate::relative_path::RelativePath>;
        /// `Shallow_decl_defs.to_*_decl_opt` of a decl named `key`.
        fn extract(decl: &NamedDecl<R>, key: Self::K) -> Option<Self::V>;
    }

    fn decl_find_or_add<V>(
        lm: &LocalMemory,
        key: Key,
        default: &mut dyn FnMut() -> Option<V>,
        wrap: fn(V) -> Value,
        unwrap: fn(Value) -> Option<V>,
    ) -> Option<V> {
        lfu_cache::find_or_add(&lm.decl_cache, key, || default().map(wrap)).and_then(unwrap)
    }

    struct ClassK;
    impl Kind for ClassK {
        type K = TypeName;
        type V = Arc<ShallowClass<R>>;
        fn find_or_add(lm: &LocalMemory, key: TypeName, default: &mut dyn FnMut() -> Option<Self::V>) -> Option<Self::V> {
            lfu_cache::find_or_add(&lm.shallow_decl_cache, key, default)
        }
        fn add(lm: &LocalMemory, key: TypeName, v: Self::V) {
            lm.shallow_decl_cache.lock().unwrap().add(key, v)
        }
        fn remove(lm: &LocalMemory, key: TypeName) {
            lm.shallow_decl_cache.lock().unwrap().remove(&key)
        }
        fn path_of(v: &naming::View<'_>, key: TypeName) -> Option<crate::relative_path::RelativePath> {
            match naming::get_type_pos_and_kind(v, key.as_str()) {
                Some((pos, oxidized::naming_types::KindOfType::TClass)) => Some(crate::file_info::get_pos_filename(&pos)),
                Some(_) | None => None,
            }
        }
        fn extract(decl: &NamedDecl<R>, key: TypeName) -> Option<Self::V> {
            match decl {
                NamedDecl::Class(name, d) if *name == key => Some(Arc::new(d.clone())),
                _ => None,
            }
        }
    }

    struct TypedefK;
    impl Kind for TypedefK {
        type K = TypeName;
        type V = Arc<TypedefDecl<R>>;
        fn find_or_add(lm: &LocalMemory, key: TypeName, default: &mut dyn FnMut() -> Option<Self::V>) -> Option<Self::V> {
            decl_find_or_add(lm, Key::TypedefDecl(key), default, Value::Typedef, |v| match v {
                Value::Typedef(d) => Some(d),
                _ => None,
            })
        }
        fn add(lm: &LocalMemory, key: TypeName, v: Self::V) {
            lm.decl_cache.lock().unwrap().add(Key::TypedefDecl(key), Value::Typedef(v))
        }
        fn remove(lm: &LocalMemory, key: TypeName) {
            lm.decl_cache.lock().unwrap().remove(&Key::TypedefDecl(key))
        }
        fn path_of(v: &naming::View<'_>, key: TypeName) -> Option<crate::relative_path::RelativePath> {
            match naming::get_type_pos_and_kind(v, key.as_str()) {
                Some((pos, oxidized::naming_types::KindOfType::TTypedef)) => {
                    Some(crate::file_info::get_pos_filename(&pos))
                }
                Some(_) | None => None,
            }
        }
        fn extract(decl: &NamedDecl<R>, key: TypeName) -> Option<Self::V> {
            match decl {
                NamedDecl::Typedef(name, d) if *name == key => Some(Arc::new(d.clone())),
                _ => None,
            }
        }
    }

    struct FunK;
    impl Kind for FunK {
        type K = FunName;
        type V = Arc<FunDecl<R>>;
        fn find_or_add(lm: &LocalMemory, key: FunName, default: &mut dyn FnMut() -> Option<Self::V>) -> Option<Self::V> {
            decl_find_or_add(lm, Key::FunDecl(key), default, Value::Fun, |v| match v {
                Value::Fun(d) => Some(d),
                _ => None,
            })
        }
        fn add(lm: &LocalMemory, key: FunName, v: Self::V) {
            lm.decl_cache.lock().unwrap().add(Key::FunDecl(key), Value::Fun(v))
        }
        fn remove(lm: &LocalMemory, key: FunName) {
            lm.decl_cache.lock().unwrap().remove(&Key::FunDecl(key))
        }
        fn path_of(v: &naming::View<'_>, key: FunName) -> Option<crate::relative_path::RelativePath> {
            naming::get_fun_pos(v, key.as_str()).map(|pos| crate::file_info::get_pos_filename(&pos))
        }
        fn extract(decl: &NamedDecl<R>, key: FunName) -> Option<Self::V> {
            match decl {
                NamedDecl::Fun(name, d) if *name == key => Some(Arc::new(d.clone())),
                _ => None,
            }
        }
    }

    struct ConstK;
    impl Kind for ConstK {
        type K = ConstName;
        type V = Arc<ConstDecl<R>>;
        fn find_or_add(lm: &LocalMemory, key: ConstName, default: &mut dyn FnMut() -> Option<Self::V>) -> Option<Self::V> {
            decl_find_or_add(lm, Key::GconstDecl(key), default, Value::Gconst, |v| match v {
                Value::Gconst(d) => Some(d),
                _ => None,
            })
        }
        fn add(lm: &LocalMemory, key: ConstName, v: Self::V) {
            lm.decl_cache.lock().unwrap().add(Key::GconstDecl(key), Value::Gconst(v))
        }
        fn remove(lm: &LocalMemory, key: ConstName) {
            lm.decl_cache.lock().unwrap().remove(&Key::GconstDecl(key))
        }
        fn path_of(v: &naming::View<'_>, key: ConstName) -> Option<crate::relative_path::RelativePath> {
            naming::get_const_pos(v, key.as_str()).map(|pos| crate::file_info::get_pos_filename(&pos))
        }
        fn extract(decl: &NamedDecl<R>, key: ConstName) -> Option<Self::V> {
            match decl {
                NamedDecl::Const(name, d) if *name == key => Some(Arc::new(d.clone())),
                _ => None,
            }
        }
    }

    struct ModuleK;
    impl Kind for ModuleK {
        type K = ModuleName;
        type V = Arc<ModuleDecl<R>>;
        fn find_or_add(lm: &LocalMemory, key: ModuleName, default: &mut dyn FnMut() -> Option<Self::V>) -> Option<Self::V> {
            decl_find_or_add(lm, Key::ModuleDecl(key), default, Value::Module, |v| match v {
                Value::Module(d) => Some(d),
                _ => None,
            })
        }
        fn add(lm: &LocalMemory, key: ModuleName, v: Self::V) {
            lm.decl_cache.lock().unwrap().add(Key::ModuleDecl(key), Value::Module(v))
        }
        fn remove(lm: &LocalMemory, key: ModuleName) {
            lm.decl_cache.lock().unwrap().remove(&Key::ModuleDecl(key))
        }
        fn path_of(v: &naming::View<'_>, key: ModuleName) -> Option<crate::relative_path::RelativePath> {
            naming::get_module_pos(v, key.as_str()).map(|pos| crate::file_info::get_pos_filename(&pos))
        }
        fn extract(decl: &NamedDecl<R>, key: ModuleName) -> Option<Self::V> {
            match decl {
                NamedDecl::Module(name, d) if *name == key => Some(Arc::new(d.clone())),
                _ => None,
            }
        }
    }

    /// The store of one kind: `Decl_provider_internals.get_*` of the
    /// `Local_memory` backend (`Provider_backend.Decl_cache.find_or_add
    /// ~default:(fun () -> match Naming_provider.get_*_path ctx name with
    /// Some filename -> find_in_direct_decl_parse ~cache_results:true ...)`).
    struct LmStore<Kd> {
        p: Arc<LmParse>,
        _kind: std::marker::PhantomData<fn() -> Kd>,
    }

    impl<Kd> std::fmt::Debug for LmStore<Kd> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("Local_memory store")
        }
    }

    impl<Kd: Kind> Store<Kd::K, Kd::V> for LmStore<Kd> {
        fn get(&self, key: Kd::K) -> Result<Option<Kd::V>> {
            let p = &self.p;
            Ok(Kd::find_or_add(&p.lm, key, &mut || {
                let filename = Kd::path_of(&p.view(), key)?;
                // `find_in_direct_decl_parse`: the first decl of the name and
                // kind in `pfh_decls`, which is in reverse lexical order (so
                // the last one of the file).
                let decls = p.direct_decl_parse_and_cache(&filename, key.as_ref());
                decls.iter().rev().find_map(|decl| Kd::extract(decl, key))
            }))
        }

        fn insert(&self, key: Kd::K, val: Kd::V) -> Result<()> {
            Kd::add(&self.p.lm, key, val);
            Ok(())
        }

        fn contains_key(&self, key: Kd::K) -> Result<bool> {
            Ok(self.get(key)?.is_some())
        }

        fn remove_batch(&self, keys: &mut dyn Iterator<Item = Kd::K>) -> Result<()> {
            for key in keys {
                Kd::remove(&self.p.lm, key)
            }
            Ok(())
        }
    }

    /// `make_decl_store_from_local_memory`'s classes: the folded-class
    /// cache (`get_class` is `find_or_add ~default:(fun _ -> None)`, a use;
    /// `add_class` is `add`).
    struct LmFolded {
        lm: Arc<LocalMemory>,
    }

    impl std::fmt::Debug for LmFolded {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("Local_memory folded_class_cache")
        }
    }

    impl Store<TypeName, Arc<FoldedClass<R>>> for LmFolded {
        fn get(&self, key: TypeName) -> Result<Option<Arc<FoldedClass<R>>>> {
            Ok(self.lm.folded_class_cache.lock().unwrap().find_and_count(&key))
        }

        fn insert(&self, key: TypeName, val: Arc<FoldedClass<R>>) -> Result<()> {
            self.lm.folded_class_cache.lock().unwrap().add(key, val);
            Ok(())
        }

        fn remove_batch(&self, keys: &mut dyn Iterator<Item = TypeName>) -> Result<()> {
            let mut cache = self.lm.folded_class_cache.lock().unwrap();
            for key in keys {
                cache.remove(&key)
            }
            Ok(())
        }
    }

    /// The `ShallowDeclStore` and the folded-decl provider of a context of
    /// the backend of `p` (with the entries of `p`).
    pub(crate) fn stores(
        tco: &TypecheckerOptions,
        p: Arc<LmParse>,
    ) -> (Arc<ShallowDeclStore<R>>, Arc<dyn FoldedDeclProvider<R>>) {
        fn store<Kd: Kind>(p: &Arc<LmParse>) -> Arc<LmStore<Kd>> {
            Arc::new(LmStore {
                p: Arc::clone(p),
                _kind: std::marker::PhantomData,
            })
        }
        let shallow_decls = Arc::new(ShallowDeclStore::with_no_member_stores(
            store::<ClassK>(&p),
            store::<TypedefK>(&p),
            store::<FunK>(&p),
            store::<ConstK>(&p),
            store::<ModuleK>(&p),
        ));
        let folded_decls: Arc<dyn FoldedDeclProvider<R>> = Arc::new(LazyFoldedDeclProvider::new(
            Arc::new(DeclFoldOptions::from_global_options(tco)),
            Arc::new(LmFolded {
                lm: Arc::clone(&p.lm),
            }),
            Arc::new(EagerShallowDeclProvider::new(Arc::clone(&shallow_decls))),
        ));
        (shallow_decls, folded_decls)
    }
}

/// The old declarations of names that were oldified (plan D3): `None` for a
/// name that has no old declaration (`get_old_defs` of the OCaml's Rust
/// backend: `store.get(old$name)`). R1 converts them to the value types of
/// `decl_compare`.
///
/// Owned by **N1** (plan §3.1). Interface by W0 (plan §3.2).
#[cfg(feature = "port")]
#[derive(Clone, Debug, Default)]
pub struct OldDefs {
    pub classes: std::collections::BTreeMap<String, Option<Arc<ShallowClass<R>>>>,
    pub funs: std::collections::BTreeMap<String, Option<Arc<FunDecl<R>>>>,
    pub typedefs: std::collections::BTreeMap<String, Option<Arc<TypedefDecl<R>>>>,
    pub consts: std::collections::BTreeMap<String, Option<Arc<ConstDecl<R>>>>,
    pub modules: std::collections::BTreeMap<String, Option<Arc<ModuleDecl<R>>>>,
}

/// The old entries of the decl heaps (`Shared_mem` `oldify`: the
/// `old_`-prefixed keys of the same heaps), kept beside the stores (plan D3).
#[cfg(feature = "port")]
#[derive(Default)]
struct OldDecls {
    classes: hash::HashMap<TypeName, Arc<ShallowClass<R>>>,
    funs: hash::HashMap<FunName, Arc<FunDecl<R>>>,
    typedefs: hash::HashMap<TypeName, Arc<TypedefDecl<R>>>,
    consts: hash::HashMap<ConstName, Arc<ConstDecl<R>>>,
    modules: hash::HashMap<ModuleName, Arc<ModuleDecl<R>>>,
}

/// `ShallowStoreWithChanges::oldify` for one store: a name with a live
/// declaration has it moved to its old entry (replacing the old one); a
/// name without one loses its old entry.
#[cfg(feature = "port")]
fn oldify<K, V>(
    store: &NonEvictingStore<K, V>,
    old: &mut hash::HashMap<K, V>,
    names: impl Iterator<Item = K>,
) where
    K: Copy + Send + Sync + std::hash::Hash + Eq,
    V: Clone + Send + Sync,
{
    let mut moves = vec![];
    let mut deletes = vec![];
    for name in names {
        match store.get(name).unwrap() {
            Some(decl) => moves.push((name, decl)),
            None => {
                if old.contains_key(&name) {
                    deletes.push(name)
                }
            }
        }
    }
    store
        .remove_batch(&mut moves.iter().map(|(name, _)| *name))
        .unwrap();
    for (name, decl) in moves {
        old.insert(name, decl);
    }
    for name in deletes {
        old.remove(&name);
    }
}

/// `ShallowStoreWithChanges::get_old` for one store.
#[cfg(feature = "port")]
fn get_old<K, V>(
    old: &hash::HashMap<K, V>,
    names: &std::collections::BTreeSet<String>,
    key: impl Fn(&str) -> K,
) -> std::collections::BTreeMap<String, Option<V>>
where
    K: std::hash::Hash + Eq,
    V: Clone,
{
    names
        .iter()
        .map(|name| (name.clone(), old.get(&key(name)).cloned()))
        .collect()
}

/// The reverse naming table of the daemon (plan D4): `Naming_heap` of the
/// OCaml daemon (which runs the `Shared_memory` provider backend):
/// - the positions of the names of each namespace (`TypePosHeap`,
///   `FunPosHeap`, `ConstPosHeap`, `ModulePosHeap`), keyed by the dep hash of
///   the name (`get_filenames_by_hash` is a lookup of these maps);
/// - the canonical names of types and functions (`TypeCanonHeap`,
///   `FunCanonHeap`, by lowercase name): these are the canon maps of the
///   `Ctx` ([`Ctx::type_canon_names`], [`Ctx::fun_canon_names`]), which the
///   init fills (`Ctx::declare_file`);
/// - when the table has a SQLite naming table (a saved-state init, L0:
///   `Db_path_provider.set_naming_db_path`), a lookup that misses asks it and
///   caches the answer (`get_and_cache`), unless a remove blocked the name
///   (`BlockedEntries`, never unblocked, as in the OCaml);
/// - the stacks of local changes of all these heaps
///   (`Naming_heap.push_local_changes`, `pop_local_changes`): while one is
///   pushed, writes go to its top frame, which a pop drops.
///
/// The two are updated separately, as in the OCaml: removing a name removes
/// its lowercase entry from the canon map whatever spelling that entry has,
/// and the position of its own spelling only; adding a name changes neither
/// where it has an entry (`Shared_mem` `add`).
///
/// All lookups go through the methods of [`ReverseNamingTable`] (and the
/// `naming_*` methods of `Ctx`).
#[cfg(feature = "port")]
pub mod reverse_naming {
    use std::collections::HashMap;
    use std::hash::Hash;
    use std::sync::RwLock;
    use std::sync::atomic::AtomicBool;
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    use oxidized::file_info::NameType;
    use oxidized::naming_types::KindOfType;
    use oxidized::naming_types::NameKind;
    use pos::ConstName;
    use pos::FunName;
    use pos::ModuleName;
    use pos::RelativePath;
    use pos::TypeName;
    use typing_deps_hash::DepType;

    use super::DashMap;
    use crate::naming_sqlite;

    /// A `File_info.pos` with hackrs's compact positions and paths.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Pos {
        Full(pos::BPos),
        File(NameType, RelativePath),
    }

    impl Pos {
        pub fn path(&self) -> RelativePath {
            match self {
                Self::Full(pos) => pos.file(),
                Self::File(_, path) => *path,
            }
        }

        pub fn of_file_info(pos: &oxidized::file_info::Pos) -> Self {
            match pos {
                oxidized::file_info::Pos::Full(pos) => Self::Full(pos.into()),
                oxidized::file_info::Pos::File(name_type, path) => {
                    Self::File(*name_type, (&**path).into())
                }
            }
        }

        pub fn to_file_info(&self) -> oxidized::file_info::Pos {
            match self {
                Self::Full(pos) => oxidized::file_info::Pos::Full(pos.clone().into()),
                Self::File(name_type, path) => {
                    oxidized::file_info::Pos::File(*name_type, std::sync::Arc::new((*path).into()))
                }
            }
        }
    }

    /// `ToplevelSymbolHash::new name_type name` (= `Typing_deps.Dep.make` of
    /// the name's dependency).
    pub fn hash(dep_type: DepType, name: &str) -> u64 {
        typing_deps_hash::hash1(dep_type, name.as_bytes())
    }

    /// The dep hash as `Typing_deps.Dep.t`.
    fn dep_of_hash(hash: u64) -> crate::typing_deps::dep::T {
        crate::typing_deps::dep::T::from(depgraph_dep::Dep::new(hash))
    }

    /// An exception of `Naming_sqlite` that the OCaml lets through.
    fn raise<A>(result: naming_sqlite::Result<A>) -> A {
        match result {
            Ok(a) => a,
            Err(e) => std::panic::panic_any(e),
        }
    }

    /// The stack of local changes of a heap (`Shared_mem.LocalChanges`):
    /// frames (newest last) of the writes made while it is pushed; `None` is
    /// a removed key. The base heap is not touched while a frame is pushed.
    pub(crate) struct Frames<K, V> {
        depth: AtomicUsize,
        frames: RwLock<Vec<HashMap<K, Option<V>>>>,
    }

    impl<K, V> Default for Frames<K, V> {
        fn default() -> Self {
            Self {
                depth: AtomicUsize::new(0),
                frames: RwLock::new(vec![]),
            }
        }
    }

    impl<K: Eq + Hash, V: Clone> Frames<K, V> {
        /// Whether a frame is pushed (one load when none is).
        #[inline]
        pub(crate) fn active(&self) -> bool {
            self.depth.load(Ordering::Relaxed) > 0
        }

        /// What the frames say of `key`: `None` if nothing.
        pub(crate) fn get(&self, key: &K) -> Option<Option<V>> {
            let frames = self.frames.read().unwrap();
            frames.iter().rev().find_map(|frame| frame.get(key).cloned())
        }

        pub(crate) fn set(&self, key: K, value: Option<V>) {
            let mut frames = self.frames.write().unwrap();
            frames.last_mut().unwrap().insert(key, value);
        }

        pub(crate) fn push(&self) {
            self.frames.write().unwrap().push(HashMap::new());
            self.depth.fetch_add(1, Ordering::Relaxed);
        }

        pub(crate) fn depth(&self) -> usize {
            self.depth.load(Ordering::Relaxed)
        }

        pub(crate) fn pop(&self) {
            let mut frames = self.frames.write().unwrap();
            if frames.pop().is_none() {
                panic!("There are no active local change stacks. Nothing to pop!")
            }
            self.depth.fetch_sub(1, Ordering::Relaxed);
        }
    }

    /// A heap of `Naming_heap`: the shared map and its local changes.
    pub(crate) struct Heap<K, V> {
        base: DashMap<K, V>,
        local: Frames<K, V>,
    }

    impl<K: Eq + Hash, V> Default for Heap<K, V> {
        fn default() -> Self {
            Self {
                base: Default::default(),
                local: Default::default(),
            }
        }
    }

    impl<K: Copy + Eq + Hash, V: Clone> Heap<K, V> {
        pub(crate) fn get(&self, key: K) -> Option<V> {
            if self.local.active() {
                if let Some(found) = self.local.get(&key) {
                    return found;
                }
            }
            self.base.get(&key).map(|entry| entry.value().clone())
        }

        /// `add`: no-op when the key has a value; with local changes, the
        /// value replaces the one there (`LocalChanges.add` may overwrite).
        pub(crate) fn add(&self, key: K, value: V) {
            if self.local.active() {
                self.local.set(key, Some(value));
            } else {
                self.base.entry(key).or_insert(value);
            }
        }

        /// `remove` (when the key has a value: `Shared_mem` `remove` checks
        /// `mem` first).
        pub(crate) fn remove(&self, key: K) {
            if self.local.active() {
                if self.get(key).is_some() {
                    self.local.set(key, None);
                }
            } else {
                self.base.remove(&key);
            }
        }

        pub(crate) fn push(&self) {
            self.local.push()
        }

        pub(crate) fn pop(&self) {
            self.local.pop()
        }
    }

    /// The positions (`TypePosHeap`, `FunPosHeap`, `ConstPosHeap`,
    /// `ModulePosHeap` of `Naming_heap`, keyed by the dep hash of the name),
    /// their `BlockedEntries`, the SQLite naming table they fall back to, and
    /// the local changes of the canon heaps (whose base maps are the canon
    /// maps of the `Ctx`). As in shared memory, an `add_*` of a name that
    /// has a position is a no-op (`Shared_mem` `add` does not overwrite).
    /// Each entry keeps the name it was added under (the OCaml keeps only the
    /// hash) for `Ctx::check_naming_invariant`.
    #[derive(Default)]
    pub struct ReverseNamingTable {
        types: Heap<u64, (TypeName, Pos, KindOfType)>,
        funs: Heap<u64, (FunName, Pos)>,
        consts: Heap<u64, (ConstName, Pos)>,
        modules: Heap<u64, (ModuleName, Pos)>,
        types_blocked: Heap<u64, ()>,
        funs_blocked: Heap<u64, ()>,
        consts_blocked: Heap<u64, ()>,
        modules_blocked: Heap<u64, ()>,
        pub(crate) type_canon: Frames<String, super::Bound<TypeName>>,
        pub(crate) fun_canon: Frames<String, super::Bound<FunName>>,
        /// `db_path_opt` (`Db_path_provider.get_naming_db_path`).
        db: RwLock<Option<naming_sqlite::DbPath>>,
        has_db: AtomicBool,
    }

    impl ReverseNamingTable {
        /// The SQLite naming table lookups fall back to.
        pub fn set_db_path(&self, db_path: Option<naming_sqlite::DbPath>) {
            self.has_db.store(db_path.is_some(), Ordering::Relaxed);
            *self.db.write().unwrap() = db_path;
        }

        /// `db_path_opt`, read only on a miss.
        fn db_path(&self) -> Option<naming_sqlite::DbPath> {
            if self.has_db.load(Ordering::Relaxed) {
                self.db.read().unwrap().clone()
            } else {
                None
            }
        }

        pub fn has_db_path(&self) -> bool {
            self.has_db.load(Ordering::Relaxed)
        }

        /// `Naming_heap.push_local_changes`
        pub fn push_local_changes(&self) {
            self.types.push();
            self.type_canon.push();
            self.types_blocked.push();
            self.funs.push();
            self.fun_canon.push();
            self.funs_blocked.push();
            self.consts.push();
            self.consts_blocked.push();
            self.modules.push();
            self.modules_blocked.push();
        }

        /// `Naming_heap.pop_local_changes`
        pub fn pop_local_changes(&self) {
            self.types.pop();
            self.type_canon.pop();
            self.types_blocked.pop();
            self.funs.pop();
            self.fun_canon.pop();
            self.funs_blocked.pop();
            self.consts.pop();
            self.consts_blocked.pop();
            self.modules.pop();
            self.modules_blocked.pop();
        }

        /// The depth of the local changes (for tests).
        pub fn local_changes_depth(&self) -> usize {
            self.types.local.depth.load(Ordering::Relaxed)
        }

        pub fn add_type(&self, name: TypeName, pos: Pos, kind: KindOfType) {
            self.types.add(hash(DepType::KType, name.as_str()), (name, pos, kind));
        }

        /// `Naming_heap.Types.get_pos db_path_opt id`
        pub fn get_type_pos(&self, name: &str) -> Option<(Pos, KindOfType)> {
            let key = hash(DepType::KType, name);
            if let Some(entry) = self.types.get(key) {
                return Some((entry.1, entry.2));
            }
            // `get_and_cache`: the fallback (when there is a database),
            // unless the key is blocked.
            let db_path = self.db_path()?;
            if self.types_blocked.get(key).is_some() {
                return None;
            }
            match raise(naming_sqlite::get_path_by_64bit_dep(&db_path, dep_of_hash(key))) {
                None => None,
                Some((file, NameKind::TypeKind(type_kind))) => {
                    let name_type = NameType::from(type_kind);
                    let pos = Pos::File(name_type, (&file).into());
                    self.types
                        .add(key, (TypeName(super::symbol(name)), pos.clone(), type_kind));
                    Some((pos, type_kind))
                }
                Some((_, _)) => panic!("passed in Type dephash, but got non-type out"),
            }
        }

        /// `TypePosHeap.remove_batch` (the positions; see
        /// `Ctx::naming_types_remove_batch`).
        pub fn remove_type(&self, name: &str) {
            self.types.remove(hash(DepType::KType, name));
        }

        pub fn add_fun(&self, name: FunName, pos: Pos) {
            self.funs.add(hash(DepType::KFun, name.as_str()), (name, pos));
        }

        /// `Naming_heap.Funs.get_pos db_path_opt id`
        pub fn get_fun_pos(&self, name: &str) -> Option<Pos> {
            let key = hash(DepType::KFun, name);
            if let Some(entry) = self.funs.get(key) {
                return Some(entry.1);
            }
            let db_path = self.db_path()?;
            if self.funs_blocked.get(key).is_some() {
                return None;
            }
            let path = raise(naming_sqlite::get_path_by_64bit_dep(&db_path, dep_of_hash(key)))?.0;
            let pos = Pos::File(NameType::Fun, (&path).into());
            self.funs.add(key, (FunName(super::symbol(name)), pos.clone()));
            Some(pos)
        }

        pub fn remove_fun(&self, name: &str) {
            self.funs.remove(hash(DepType::KFun, name));
        }

        pub fn add_const(&self, name: ConstName, pos: Pos) {
            self.consts.add(hash(DepType::KGConst, name.as_str()), (name, pos));
        }

        /// `Naming_heap.Consts.get_pos db_path_opt id`
        pub fn get_const_pos(&self, name: &str) -> Option<Pos> {
            let key = hash(DepType::KGConst, name);
            if let Some(entry) = self.consts.get(key) {
                return Some(entry.1);
            }
            let db_path = self.db_path()?;
            if self.consts_blocked.get(key).is_some() {
                return None;
            }
            let path = raise(naming_sqlite::get_path_by_64bit_dep(&db_path, dep_of_hash(key)))?.0;
            let pos = Pos::File(NameType::Const, (&path).into());
            self.consts.add(key, (ConstName(super::symbol(name)), pos.clone()));
            Some(pos)
        }

        pub fn remove_const(&self, name: &str) {
            self.consts.remove(hash(DepType::KGConst, name));
        }

        pub fn add_module(&self, name: ModuleName, pos: Pos) {
            self.modules.add(hash(DepType::KModule, name.as_str()), (name, pos));
        }

        /// `Naming_heap.Modules.get_pos db_path_opt id`
        pub fn get_module_pos(&self, name: &str) -> Option<Pos> {
            let key = hash(DepType::KModule, name);
            if let Some(entry) = self.modules.get(key) {
                return Some(entry.1);
            }
            let db_path = self.db_path()?;
            if self.modules_blocked.get(key).is_some() {
                return None;
            }
            let path = raise(naming_sqlite::get_path_by_64bit_dep(&db_path, dep_of_hash(key)))?.0;
            let pos = Pos::File(NameType::Module, (&path).into());
            self.modules.add(key, (ModuleName(super::symbol(name)), pos.clone()));
            Some(pos)
        }

        pub fn remove_module(&self, name: &str) {
            self.modules.remove(hash(DepType::KModule, name));
        }

        /// The `BlockedEntries` part of `remove_batch` (when there is a
        /// database): the hashes, then (types and funs) the canon hashes.
        pub(crate) fn block(&self, dep_type: DepType, names: &[String], canon: bool) {
            if !self.has_db_path() {
                return;
            }
            let heap = match dep_type {
                DepType::KType => &self.types_blocked,
                DepType::KFun => &self.funs_blocked,
                DepType::KGConst => &self.consts_blocked,
                _ => &self.modules_blocked,
            };
            for name in names {
                heap.add(hash(dep_type, name), ());
            }
            if canon {
                for name in names {
                    heap.add(hash(dep_type, &name.to_ascii_lowercase()), ());
                }
            }
        }

        /// Whether the canon hash of `name` (a type, or a fun) is blocked,
        /// for the fallback of the canon heaps.
        pub(crate) fn is_canon_blocked(&self, dep_type: DepType, name: &str) -> bool {
            let heap = match dep_type {
                DepType::KType => &self.types_blocked,
                _ => &self.funs_blocked,
            };
            heap.get(hash(dep_type, &name.to_ascii_lowercase())).is_some()
        }

        /// The database, for the fallbacks of the canon heaps.
        pub(crate) fn db_path_for_fallback(&self) -> Option<naming_sqlite::DbPath> {
            self.db_path()
        }

        /// `Naming_heap.get_filename_by_hash`: types, then funs, then
        /// consts (not modules, as the OCaml); then the database, unless
        /// the heap of the kind it answers blocks the hash.
        pub fn get_filename_by_hash(&self, hash: u64) -> Option<RelativePath> {
            let pos = if let Some(entry) = self.types.get(hash) {
                Some(entry.1)
            } else if let Some(entry) = self.funs.get(hash) {
                Some(entry.1)
            } else {
                self.consts.get(hash).map(|entry| entry.1)
            };
            match (pos, self.db_path()) {
                (Some(pos), _) => Some(pos.path()),
                (None, None) => None,
                (None, Some(db_path)) => {
                    match raise(naming_sqlite::get_path_by_64bit_dep(&db_path, dep_of_hash(hash))) {
                        None => None,
                        Some((file, name_kind)) => {
                            let is_blocked = match name_kind {
                                NameKind::TypeKind(_) => self.types_blocked.get(hash),
                                NameKind::FunKind => self.funs_blocked.get(hash),
                                NameKind::ConstKind => self.consts_blocked.get(hash),
                                NameKind::ModuleKind => self.modules_blocked.get(hash),
                            };
                            match is_blocked {
                                Some(()) => None,
                                None => Some((&file).into()),
                            }
                        }
                    }
                }
            }
        }

        /// Whether the shared heap (not its local changes) has a position
        /// for the type `name` (for tests).
        pub fn base_has_type(&self, name: &str) -> bool {
            self.types.base.contains_key(&hash(DepType::KType, name))
        }

        /// Every position of the shared heaps, for `Ctx::check_naming_invariant`.
        pub(super) fn for_each(
            &self,
            mut types: impl FnMut(TypeName, &Pos, KindOfType),
            mut funs: impl FnMut(FunName, &Pos),
            mut consts: impl FnMut(ConstName, &Pos),
            mut modules: impl FnMut(ModuleName, &Pos),
        ) {
            for entry in self.types.base.iter() {
                types(entry.0, &entry.1, entry.2)
            }
            for entry in self.funs.base.iter() {
                funs(entry.0, &entry.1)
            }
            for entry in self.consts.base.iter() {
                consts(entry.0, &entry.1)
            }
            for entry in self.modules.base.iter() {
                modules(entry.0, &entry.1)
            }
        }
    }
}

/// The mutations of the daemon (plan D3, D4, D5.1): removal, oldify, the
/// reverse naming table and its index by dep hash, incremental decls. Owned
/// by **N1** (plan §3.1). Nothing on the batch path calls them.
#[cfg(feature = "port")]
impl Ctx {
    /// Same stores, new `ShallowDeclStore` and folded-provider wrappers (new
    /// identities), so that every cache keyed by their identity resets by
    /// itself (D5.1). The caller re-`install`s it into `decl_store`.
    pub fn next_generation(&self) -> Arc<Ctx> {
        if let Some(base) = &self.decl_stores.local {
            let (shallow_decls, folded_decls) = local_memory::stores(&self.tco, Arc::clone(base));
            return Arc::new(Ctx {
                shallow_decls,
                folded_decls,
                ..self.clone()
            });
        }
        let shallow_decls = shallow_decl_store(&self.decl_stores);
        let folded_decls: Arc<dyn FoldedDeclProvider<R>> = Arc::new(LazyFoldedDeclProvider::new(
            Arc::new(DeclFoldOptions::from_global_options(&self.tco)),
            folded_store(&self.decl_stores),
            Arc::new(EagerShallowDeclProvider::new(Arc::clone(&shallow_decls))),
        ));
        Arc::new(Ctx {
            shallow_decls,
            folded_decls,
            ..self.clone()
        })
    }

    /// `failed_naming` after the init (plan D4): what
    /// `Naming_global.ndecl_file_and_get_conflict_files` gives when the
    /// files of `nt` are named one after the other in the order of
    /// `Relative_path.Map`, from the names the init bound
    /// ([`Ctx::declare_file`], whose winners are those of that sequential
    /// naming). A file F that has a name not bound to it (a name declared
    /// by an earlier file, or twice in F) fails, and so does the file each
    /// name of F is bound to (`add_files_to_rename`: when F is named, the
    /// winner of each of its names is already the final one).
    ///
    /// Call it after the init and before any recheck changes the names.
    pub fn take_init_conflict_files(
        &self,
        nt: &crate::naming_table::T,
    ) -> crate::relative_path::set::T {
        let stores = &*self.decl_stores;
        let type_file = |name: &str| {
            self.type_canon_names
                .get(&name.to_ascii_lowercase())
                .map(|entry| entry.order.file)
        };
        let fun_file = |name: &str| {
            self.fun_canon_names
                .get(&name.to_ascii_lowercase())
                .map(|entry| entry.order.file)
        };
        let const_file = |name: &str| {
            stores
                .const_names
                .get(&ConstName(symbol(name)))
                .map(|entry| entry.file)
        };
        let module_file = |name: &str| {
            stores
                .module_names
                .get(&ModuleName(symbol(name)))
                .map(|entry| entry.file)
        };
        crate::naming_table::fold(nt, crate::relative_path::set::T::new(), |path, info, mut failed| {
            let file: RelativePath = path.into();
            let ids = &info.ids;
            // Whether some name of the file is not bound to it: one of its
            // names is bound to another file, or the file declares it twice
            // (up to case for types and functions).
            let lost = |ids: &[&Vec<crate::file_info::Id>],
                        key: &dyn Fn(&str) -> String,
                        winner: &dyn Fn(&str) -> Option<RelativePath>| {
                let mut seen = std::collections::HashSet::new();
                ids.iter().flat_map(|ids| ids.iter()).any(|id| {
                    !seen.insert(key(&id.name)) || winner(&id.name) != Some(file)
                })
            };
            let lower = |name: &str| name.to_ascii_lowercase();
            let exact = |name: &str| name.to_string();
            let is_okay = !lost(&[&ids.funs], &lower, &fun_file)
                && !lost(&[&ids.classes, &ids.typedefs], &lower, &type_file)
                && !lost(&[&ids.consts], &exact, &const_file)
                && !lost(&[&ids.modules], &exact, &module_file);
            if !is_okay {
                failed.insert(path.clone());
                let mut add = |ids: &Vec<crate::file_info::Id>, winner: &dyn Fn(&str) -> Option<RelativePath>| {
                    for id in ids {
                        if let Some(file) = winner(&id.name) {
                            failed.insert(file.into());
                        }
                    }
                };
                add(&ids.funs, &fun_file);
                add(&ids.classes, &type_file);
                add(&ids.typedefs, &type_file);
                add(&ids.consts, &const_file);
                add(&ids.modules, &module_file);
            }
            failed
        })
    }

    /// Builds the daemon's reverse naming table ([`reverse_naming`]) from the
    /// names the init bound: each name at the position of the declaration it
    /// is bound to (a `Full` position, as the OCaml's init adds the
    /// positions of the decls, `Direct_decl_parser.decls_to_fileinfo`). The
    /// table is also the index by dep hash (`get_filenames_by_hash`).
    pub fn build_dep_hash_index(&self) {
        use rayon::prelude::*;
        use reverse_naming::Pos;
        let stores = &*self.decl_stores;
        let table = reverse_naming::ReverseNamingTable::default();
        let types: Vec<Bound<TypeName>> = self.type_canon_names.iter().map(|e| *e.value()).collect();
        types.par_iter().for_each(|bound| {
            let (pos, kind, name_type) = if bound.is_typedef {
                let decl = stores.typedefs.get(bound.name).unwrap();
                (decl.map(|decl| decl.pos.clone()), KindOfTypeAlias::TTypedef, NameTypeAlias::Typedef)
            } else {
                let decl = stores.classes.get(bound.name).unwrap();
                (decl.map(|decl| decl.name.pos().clone()), KindOfTypeAlias::TClass, NameTypeAlias::Class)
            };
            let pos = match pos {
                Some(pos) => Pos::Full(pos),
                None => Pos::File(name_type, bound.order.file),
            };
            table.add_type(bound.name, pos, kind)
        });
        let funs: Vec<Bound<FunName>> = self.fun_canon_names.iter().map(|e| *e.value()).collect();
        funs.par_iter().for_each(|bound| {
            let pos = match stores.funs.get(bound.name).unwrap() {
                Some(decl) => Pos::Full(decl.pos.clone()),
                None => Pos::File(NameTypeAlias::Fun, bound.order.file),
            };
            table.add_fun(bound.name, pos)
        });
        let consts: Vec<(ConstName, DeclOrder)> =
            stores.const_names.iter().map(|e| (*e.key(), *e.value())).collect();
        consts.par_iter().for_each(|(name, order)| {
            let pos = match stores.consts.get(*name).unwrap() {
                Some(decl) => Pos::Full(decl.pos.clone()),
                None => Pos::File(NameTypeAlias::Const, order.file),
            };
            table.add_const(*name, pos)
        });
        let modules: Vec<(ModuleName, DeclOrder)> =
            stores.module_names.iter().map(|e| (*e.key(), *e.value())).collect();
        modules.par_iter().for_each(|(name, order)| {
            let pos = match stores.modules.get(*name).unwrap() {
                Some(decl) => Pos::Full(decl.pos.clone()),
                None => Pos::File(NameTypeAlias::Module, order.file),
            };
            table.add_module(*name, pos)
        });
        // The SQLite naming table it falls back to, if one was given.
        table.set_db_path(stores.shared_db_path.read().unwrap().clone());
        if stores.reverse.set(table).is_err() {
            panic!("Ctx.build_dep_hash_index: the reverse naming table is already built")
        }
        // From now on, the stores find removed decls again (`LazyStore`).
        let _ = stores.lazy.set(LazyParse {
            parser: self.decl_parser.clone(),
            files: Arc::clone(&self.files),
        });
    }

    /// Whether [`Ctx::build_dep_hash_index`] was called (the daemon).
    pub fn has_reverse_naming_table(&self) -> bool {
        self.decl_stores.reverse.get().is_some()
    }

    /// The daemon's reverse naming table, if it was built: the naming
    /// lookups of `naming_provider` answer from it when there is one.
    #[inline]
    pub fn reverse_naming_table_opt(&self) -> Option<&reverse_naming::ReverseNamingTable> {
        self.decl_stores.reverse.get()
    }

    /// The daemon's reverse naming table.
    pub fn reverse_naming_table(&self) -> &reverse_naming::ReverseNamingTable {
        match self.decl_stores.reverse.get() {
            Some(table) => table,
            None => panic!(
                "Ctx: no reverse naming table (the daemon builds it with Ctx::build_dep_hash_index after the init)"
            ),
        }
    }

    /// `Naming_heap.Types.add`: the position of `name`, and `name` as the
    /// canonical name of its lowercase form; each only if there is none
    /// yet (`Shared_mem` `add` does not overwrite).
    pub fn naming_types_add(&self, name: &str, pos: &crate::file_info::Pos, kind: KindOfTypeAlias) {
        let pos = reverse_naming::Pos::of_file_info(pos);
        let name = TypeName(symbol(name));
        let is_typedef = kind == KindOfTypeAlias::TTypedef;
        let order = DeclOrder {
            file: pos.path(),
            rank: is_typedef as u8,
            index: 0,
        };
        let table = self.reverse_naming_table();
        table.add_type(name, pos, kind);
        let bound = Bound {
            name,
            order,
            is_typedef,
        };
        let lower = name.as_str().to_ascii_lowercase();
        if table.type_canon.active() {
            table.type_canon.set(lower, Some(bound));
        } else {
            self.type_canon_names.entry(lower).or_insert(bound);
        }
    }

    /// `Naming_heap.Types.remove_batch`: the canonical names of the
    /// lowercase forms (`canon_hash`), whatever their spelling, then the
    /// positions.
    pub fn naming_types_remove_batch(&self, names: &[String]) {
        let table = self.reverse_naming_table();
        for name in names {
            let lower = name.to_ascii_lowercase();
            if table.type_canon.active() {
                if self.get_type_canon_name(&lower).is_some() {
                    table.type_canon.set(lower, None);
                }
            } else {
                self.type_canon_names.remove(&lower);
            }
        }
        for name in names {
            table.remove_type(name);
        }
        table.block(typing_deps_hash::DepType::KType, names, true);
    }

    /// `Naming_heap.Types.get_pos` (no SQLite fallback).
    pub fn naming_types_get_pos(&self, name: &str) -> Option<(crate::file_info::Pos, KindOfTypeAlias)> {
        self.reverse_naming_table()
            .get_type_pos(name)
            .map(|(pos, kind)| (pos.to_file_info(), kind))
    }

    /// `Naming_heap.Funs.add`
    pub fn naming_funs_add(&self, name: &str, pos: &crate::file_info::Pos) {
        let pos = reverse_naming::Pos::of_file_info(pos);
        let name = FunName(symbol(name));
        let order = DeclOrder {
            file: pos.path(),
            rank: 0,
            index: 0,
        };
        let table = self.reverse_naming_table();
        let bound = Bound {
            name,
            order,
            is_typedef: false,
        };
        let lower = name.as_str().to_ascii_lowercase();
        if table.fun_canon.active() {
            table.fun_canon.set(lower, Some(bound));
        } else {
            self.fun_canon_names.entry(lower).or_insert(bound);
        }
        table.add_fun(name, pos);
    }

    /// `Naming_heap.Funs.remove_batch`
    pub fn naming_funs_remove_batch(&self, names: &[String]) {
        let table = self.reverse_naming_table();
        for name in names {
            let lower = name.to_ascii_lowercase();
            if table.fun_canon.active() {
                if self.get_fun_canon_name(&lower).is_some() {
                    table.fun_canon.set(lower, None);
                }
            } else {
                self.fun_canon_names.remove(&lower);
            }
        }
        for name in names {
            table.remove_fun(name);
        }
        table.block(typing_deps_hash::DepType::KFun, names, true);
    }

    /// The fallback of `Naming_heap.Types.get_canon_name` to the SQLite
    /// naming table (`get_and_cache` of `TypeCanonHeap`): the file and kind
    /// of the type `name` (up to case), unless its canon hash is blocked;
    /// the caller parses the file for the canonical name and caches it
    /// ([`Ctx::naming_types_cache_canon_name`]). `None` without a database.
    pub fn naming_types_canon_fallback(&self, name: &str) -> Option<(crate::relative_path::RelativePath, KindOfTypeAlias)> {
        let table = self.decl_stores.reverse.get()?;
        let db_path = table.db_path_for_fallback()?;
        if table.is_canon_blocked(typing_deps_hash::DepType::KType, name) {
            return None;
        }
        match crate::naming_sqlite::get_itype_path_by_name(&db_path, name) {
            Ok(found) => found,
            Err(e) => std::panic::panic_any(e),
        }
    }

    /// `TypeCanonHeap.add (canon_hash id) canonical_name`
    pub fn naming_types_cache_canon_name(&self, id: &str, canonical_name: &str, path: &crate::relative_path::RelativePath, kind: KindOfTypeAlias) {
        let table = self.reverse_naming_table();
        let is_typedef = kind == KindOfTypeAlias::TTypedef;
        let bound = Bound {
            name: TypeName(symbol(canonical_name)),
            order: DeclOrder {
                file: path.into(),
                rank: is_typedef as u8,
                index: 0,
            },
            is_typedef,
        };
        let lower = id.to_ascii_lowercase();
        if table.type_canon.active() {
            table.type_canon.set(lower, Some(bound));
        } else {
            self.type_canon_names.entry(lower).or_insert(bound);
        }
    }

    /// The fallback of `Naming_heap.Funs.get_canon_name` (see
    /// [`Ctx::naming_types_canon_fallback`]).
    pub fn naming_funs_canon_fallback(&self, name: &str) -> Option<crate::relative_path::RelativePath> {
        let table = self.decl_stores.reverse.get()?;
        let db_path = table.db_path_for_fallback()?;
        if table.is_canon_blocked(typing_deps_hash::DepType::KFun, name) {
            return None;
        }
        match crate::naming_sqlite::get_ifun_path_by_name(&db_path, name) {
            Ok(found) => found,
            Err(e) => std::panic::panic_any(e),
        }
    }

    /// `FunCanonHeap.add (canon_hash name) canonical_name`
    pub fn naming_funs_cache_canon_name(&self, id: &str, canonical_name: &str, path: &crate::relative_path::RelativePath) {
        let table = self.reverse_naming_table();
        let bound = Bound {
            name: FunName(symbol(canonical_name)),
            order: DeclOrder {
                file: path.into(),
                rank: 0,
                index: 0,
            },
            is_typedef: false,
        };
        let lower = id.to_ascii_lowercase();
        if table.fun_canon.active() {
            table.fun_canon.set(lower, Some(bound));
        } else {
            self.fun_canon_names.entry(lower).or_insert(bound);
        }
    }

    /// `Naming_heap.Funs.get_pos` (no SQLite fallback).
    pub fn naming_funs_get_pos(&self, name: &str) -> Option<crate::file_info::Pos> {
        self.reverse_naming_table()
            .get_fun_pos(name)
            .map(|pos| pos.to_file_info())
    }

    /// `Naming_heap.Consts.add`
    pub fn naming_consts_add(&self, name: &str, pos: &crate::file_info::Pos) {
        self.reverse_naming_table()
            .add_const(ConstName(symbol(name)), reverse_naming::Pos::of_file_info(pos));
    }

    /// `Naming_heap.Consts.remove_batch`
    pub fn naming_consts_remove_batch(&self, names: &[String]) {
        let table = self.reverse_naming_table();
        for name in names {
            table.remove_const(name);
        }
        table.block(typing_deps_hash::DepType::KGConst, names, false);
    }

    /// `Naming_heap.Consts.get_pos` (no SQLite fallback).
    pub fn naming_consts_get_pos(&self, name: &str) -> Option<crate::file_info::Pos> {
        self.reverse_naming_table()
            .get_const_pos(name)
            .map(|pos| pos.to_file_info())
    }

    /// `Naming_heap.Modules.add`
    pub fn naming_modules_add(&self, name: &str, pos: &crate::file_info::Pos) {
        self.reverse_naming_table()
            .add_module(ModuleName(symbol(name)), reverse_naming::Pos::of_file_info(pos));
    }

    /// `Naming_heap.Modules.remove_batch`
    pub fn naming_modules_remove_batch(&self, names: &[String]) {
        let table = self.reverse_naming_table();
        for name in names {
            table.remove_module(name);
        }
        table.block(typing_deps_hash::DepType::KModule, names, false);
    }

    /// `Naming_heap.Modules.get_pos` (no SQLite fallback).
    pub fn naming_modules_get_pos(&self, name: &str) -> Option<crate::file_info::Pos> {
        self.reverse_naming_table()
            .get_module_pos(name)
            .map(|pos| pos.to_file_info())
    }

    /// `Naming_heap.get_filenames_by_hash` (without a SQLite database).
    pub fn naming_get_filenames_by_hash(
        &self,
        deps: &crate::typing_deps::dep_set::T,
    ) -> crate::relative_path::set::T {
        let table = self.reverse_naming_table();
        deps.iter()
            .filter_map(|dep| {
                table
                    .get_filename_by_hash(crate::typing_deps::dep::to_int64(*dep) as u64)
                    .map(crate::relative_path::RelativePath::from)
            })
            .collect()
    }

    /// `Decl_redecl_service.oldify_defs` (`Shared_memory` branch, the heaps'
    /// `oldify_batch`; the folded classes' old versions are never read): drops the folded
    /// classes of `names.classes`, and sets the live declarations of the
    /// names aside as their old ones (a name without a live declaration loses
    /// its old one).
    pub fn oldify_defs(&self, names: &crate::file_info::Names) {
        let stores = &*self.decl_stores;
        self.remove_folded_classes_of(names.classes.iter());
        let mut old = stores.old.lock().unwrap();
        let old = &mut *old;
        oldify(&stores.classes, &mut old.classes, names.classes.iter().map(|n| TypeName(symbol(n))));
        oldify(&stores.funs, &mut old.funs, names.funs.iter().map(|n| FunName(symbol(n))));
        oldify(&stores.typedefs, &mut old.typedefs, names.types.iter().map(|n| TypeName(symbol(n))));
        oldify(&stores.consts, &mut old.consts, names.consts.iter().map(|n| ConstName(symbol(n))));
        oldify(&stores.modules, &mut old.modules, names.modules.iter().map(|n| ModuleName(symbol(n))));
    }

    /// The heaps' `get_old_batch` (`Old_shallow_classes_provider.get_old_batch`, ...).
    pub fn get_old_defs(&self, names: &crate::file_info::Names) -> OldDefs {
        let old = self.decl_stores.old.lock().unwrap();
        OldDefs {
            classes: get_old(&old.classes, &names.classes, |n| TypeName(symbol(n))),
            funs: get_old(&old.funs, &names.funs, |n| FunName(symbol(n))),
            typedefs: get_old(&old.typedefs, &names.types, |n| TypeName(symbol(n))),
            consts: get_old(&old.consts, &names.consts, |n| ConstName(symbol(n))),
            modules: get_old(&old.modules, &names.modules, |n| ModuleName(symbol(n))),
        }
    }

    /// `Decl_redecl_service.remove_old_defs` (`Shared_memory` branch): drops the folded
    /// classes of `names.classes` and the old declarations of the names.
    pub fn remove_old_defs(&self, names: &crate::file_info::Names) {
        self.remove_folded_classes_of(names.classes.iter());
        let mut old = self.decl_stores.old.lock().unwrap();
        for n in &names.classes {
            old.classes.remove(&TypeName(symbol(n)));
        }
        for n in &names.funs {
            old.funs.remove(&FunName(symbol(n)));
        }
        for n in &names.types {
            old.typedefs.remove(&TypeName(symbol(n)));
        }
        for n in &names.consts {
            old.consts.remove(&ConstName(symbol(n)));
        }
        for n in &names.modules {
            old.modules.remove(&ModuleName(symbol(n)));
        }
    }

    /// `Decl_redecl_service.remove_defs` (`Shared_memory` branch): drops the folded
    /// classes of `names.classes` and the live declarations of the names.
    pub fn remove_defs(&self, names: &crate::file_info::Names) {
        let stores = &*self.decl_stores;
        self.remove_folded_classes_of(names.classes.iter());
        stores
            .classes
            .remove_batch(&mut names.classes.iter().map(|n| TypeName(symbol(n))))
            .unwrap();
        stores
            .funs
            .remove_batch(&mut names.funs.iter().map(|n| FunName(symbol(n))))
            .unwrap();
        stores
            .typedefs
            .remove_batch(&mut names.types.iter().map(|n| TypeName(symbol(n))))
            .unwrap();
        stores
            .consts
            .remove_batch(&mut names.consts.iter().map(|n| ConstName(symbol(n))))
            .unwrap();
        stores
            .modules
            .remove_batch(&mut names.modules.iter().map(|n| ModuleName(symbol(n))))
            .unwrap();
    }

    /// `Decl_heap.Classes.remove_batch` (`Decl_provider.remove_classes`).
    pub fn remove_folded_classes(&self, names: &crate::s_set::T) {
        self.remove_folded_classes_of(names.iter())
    }

    fn remove_folded_classes_of<'a>(&self, names: impl Iterator<Item = &'a String>) {
        self.decl_stores
            .folded_classes
            .remove_batch(&mut names.map(|n| TypeName(symbol(n))))
            .unwrap();
    }

    /// `Direct_decl_utils.cache_decls` (the `Shared_memory` branch, which
    /// the OCaml daemon runs): the decls of `path` (in lexical order)
    /// without the later ones of a name already seen (`dedup_decls`: classes
    /// and typedefs share their names), nor those of names bound to another
    /// file in the reverse naming table (`remove_naming_conflict_losers`: a
    /// name that is not bound keeps its decl), added to the stores where they
    /// have no decl for the name yet (`Shared_mem` `add` does not overwrite).
    pub fn add_shallow_decls(&self, path: RelativePath, decls: Vec<NamedDecl<R>>) {
        add_shallow_decls_to(&self.decl_stores, path, decls)
    }

    /// `Decl_heap.Classes.get`: the folded class of `name` if it was folded
    /// (and not removed since), without folding it.
    pub fn get_folded_class_if_present(&self, name: &str) -> Option<Arc<FoldedClass<R>>> {
        self.decl_stores
            .folded_classes
            .get(TypeName(symbol(name)))
            .unwrap()
    }

    /// Every name of the reverse naming table has the decl of its file in
    /// the stores, and no decl of the other kind of type
    /// (`HH_INCR_VERIFY=1`; plan D4). The stores may also have decls of names
    /// that are not bound (`remove_naming_conflict_losers` keeps them, as
    /// the OCaml does).
    pub fn check_naming_invariant(&self) -> Result<(), String> {
        let stores = &*self.decl_stores;
        let errors: std::cell::RefCell<Vec<String>> = Default::default();
        let file = |pos: &pos::BPos| pos.file();
        self.reverse_naming_table().for_each(
            |name, pos, kind| {
                let class = stores.classes.get(name).unwrap();
                let typedef = stores.typedefs.get(name).unwrap();
                let (decl_file, other) = match kind {
                    KindOfTypeAlias::TClass => (class.map(|d| file(d.name.pos())), typedef.is_some()),
                    KindOfTypeAlias::TTypedef => (typedef.map(|d| file(&d.pos)), class.is_some()),
                };
                if decl_file != Some(pos.path()) || other {
                    errors.borrow_mut().push(format!(
                        "type {} bound to {:?} ({:?}): decl in {:?}{}",
                        name,
                        pos.path(),
                        kind,
                        decl_file,
                        if other { ", and a decl of the other kind" } else { "" }
                    ))
                }
            },
            |name, pos| {
                let decl_file = stores.funs.get(name).unwrap().map(|d| file(&d.pos));
                if decl_file != Some(pos.path()) {
                    errors.borrow_mut().push(format!("fun {} bound to {:?}: decl in {:?}", name, pos.path(), decl_file))
                }
            },
            |name, pos| {
                let decl_file = stores.consts.get(name).unwrap().map(|d| file(&d.pos));
                if decl_file != Some(pos.path()) {
                    errors.borrow_mut().push(format!("const {} bound to {:?}: decl in {:?}", name, pos.path(), decl_file))
                }
            },
            |name, pos| {
                let decl_file = stores.modules.get(name).unwrap().map(|d| file(&d.pos));
                if decl_file != Some(pos.path()) {
                    errors.borrow_mut().push(format!("module {} bound to {:?}: decl in {:?}", name, pos.path(), decl_file))
                }
            },
        );
        let mut errors = errors.into_inner();
        if errors.is_empty() {
            Ok(())
        } else {
            let count = errors.len();
            errors.sort();
            errors.truncate(20);
            Err(format!(
                "naming invariant: {} violation(s):\n{}",
                count,
                errors.join("\n")
            ))
        }
    }
}

/// The stores of the context installed as the providers' (`decl_store`,
/// `hh_single_type_check::install`): the heaps of the process that the
/// OCaml's `Naming_heap.push_local_changes` and the decl heaps' stacks act
/// on, which take no context.
#[cfg(feature = "port")]
static INSTALLED: std::sync::RwLock<Option<std::sync::Weak<DeclStores>>> = std::sync::RwLock::new(None);

/// What each push of local changes pushed (popped in the same order).
#[cfg(feature = "port")]
static PUSHED_DECLS: std::sync::Mutex<Vec<Option<Arc<DeclStores>>>> = std::sync::Mutex::new(vec![]);
#[cfg(feature = "port")]
static PUSHED_NAMING: std::sync::Mutex<Vec<Option<Arc<DeclStores>>>> = std::sync::Mutex::new(vec![]);

#[cfg(feature = "port")]
impl Ctx {
    /// Records the stores of `self` as the heaps of the process (see
    /// [`push_decl_local_changes`]). Called when the context is installed
    /// as the providers' (`decl_store::rust_provider_backend_decl_store`).
    pub fn set_installed(&self) {
        *INSTALLED.write().unwrap() = Some(Arc::downgrade(&self.decl_stores));
    }
}

#[cfg(feature = "port")]
fn installed() -> Option<Arc<DeclStores>> {
    INSTALLED.read().unwrap().as_ref().and_then(|w| w.upgrade())
}

#[cfg(feature = "port")]
impl LocalDecls {
    fn push(&self) {
        self.classes.push();
        self.typedefs.push();
        self.funs.push();
        self.consts.push();
        self.modules.push();
        self.folded.push();
    }

    fn pop(&self) {
        self.classes.pop();
        self.typedefs.pop();
        self.funs.pop();
        self.consts.pop();
        self.modules.pop();
        self.folded.pop();
    }
}

/// `Shallow_classes_heap.Classes.LocalChanges.push_stack` and
/// `Decl_store.push_local_changes` (`Decl_heap.*.LocalChanges.push_stack`):
/// a frame of local changes on the decl stores of the installed context
/// (a context of the `Local_memory` backend has none: its
/// `push_local_changes` is a no-op, as the OCaml's).
#[cfg(feature = "port")]
pub fn push_decl_local_changes() {
    let stores = installed().filter(|stores| stores.local.is_none());
    if let Some(stores) = &stores {
        stores.local_decls.push();
    }
    PUSHED_DECLS.lock().unwrap().push(stores);
}

/// See [`push_decl_local_changes`].
#[cfg(feature = "port")]
pub fn pop_decl_local_changes() {
    match PUSHED_DECLS.lock().unwrap().pop() {
        None => panic!("There are no active local change stacks. Nothing to pop!"),
        Some(stores) => {
            if let Some(stores) = stores {
                stores.local_decls.pop()
            }
        }
    }
}

/// `Naming_heap.push_local_changes`: a frame of local changes on the
/// reverse naming table of the installed context, if it has one (a context
/// without one, `hh single`'s, has its names in its decl stores).
#[cfg(feature = "port")]
pub fn push_naming_local_changes() {
    let stores = installed().filter(|stores| stores.reverse.get().is_some());
    if let Some(stores) = &stores {
        stores.reverse.get().unwrap().push_local_changes();
    }
    PUSHED_NAMING.lock().unwrap().push(stores);
}

/// `Naming_heap.pop_local_changes`
#[cfg(feature = "port")]
pub fn pop_naming_local_changes() {
    match PUSHED_NAMING.lock().unwrap().pop() {
        None => panic!("There are no active local change stacks. Nothing to pop!"),
        Some(stores) => {
            if let Some(stores) = stores {
                stores.reverse.get().unwrap().pop_local_changes()
            }
        }
    }
}

#[cfg(feature = "port")]
impl Ctx {
    /// Whether the decl store of classes itself (not its local changes) has
    /// a decl of `name` (for tests).
    pub fn base_has_class_decl(&self, name: &str) -> bool {
        self.decl_stores.classes.get(TypeName(symbol(name))).unwrap().is_some()
    }

    /// The depth of the local changes of the decl stores (for tests).
    pub fn decl_local_changes_depth(&self) -> usize {
        let frames = &self.decl_stores.local_decls.funs;
        if frames.active() { frames_depth(frames) } else { 0 }
    }
}

#[cfg(feature = "port")]
fn frames_depth<K: Eq + std::hash::Hash, V: Clone>(frames: &reverse_naming::Frames<K, V>) -> usize {
    frames.depth()
}

/// [`Ctx::add_shallow_decls`], also used by [`LazyStore`].
#[cfg(feature = "port")]
fn add_shallow_decls_to(stores: &DeclStores, path: RelativePath, decls: Vec<NamedDecl<R>>) {
    // Without a reverse naming table yet (a full init that caches the
    // decls it parses, before naming), no name is bound: every decl is
    // kept, as the OCaml's empty naming heap does.
    let table = stores.reverse.get();
    // `dedup_decls`: if any decls in the list have the same name, retain
    // only the first declaration of each symbol in the sequence (classes and
    // typedefs share their names).
    let mut seen_types = std::collections::HashSet::new();
    let mut seen_funs = std::collections::HashSet::new();
    let mut seen_consts = std::collections::HashSet::new();
    let mut seen_modules = std::collections::HashSet::new();
    for decl in decls {
        let first = match &decl {
            NamedDecl::Class(name, _) | NamedDecl::Typedef(name, _) => seen_types.insert(name.as_symbol()),
            NamedDecl::Fun(name, _) => seen_funs.insert(name.as_symbol()),
            NamedDecl::Const(name, _) => seen_consts.insert(name.as_symbol()),
            NamedDecl::Module(name, _) => seen_modules.insert(name.as_symbol()),
        };
        if !first {
            continue;
        }
        // `remove_naming_conflict_losers`: if a symbol was also declared in
        // another file, and that file was determined to be the winner in the
        // naming table, remove its decl from the list.
        let path_opt = table.and_then(|table| match &decl {
            NamedDecl::Class(name, _) | NamedDecl::Typedef(name, _) => {
                table.get_type_pos(name.as_str()).map(|(pos, _)| pos.path())
            }
            NamedDecl::Fun(name, _) => table.get_fun_pos(name.as_str()).map(|pos| pos.path()),
            NamedDecl::Const(name, _) => table.get_const_pos(name.as_str()).map(|pos| pos.path()),
            NamedDecl::Module(name, _) => table.get_module_pos(name.as_str()).map(|pos| pos.path()),
        });
        if path_opt.is_none_or(|p| p == path) {
            // `Shallow_classes_heap.Classes.add`, `Decl_store.add_*`: a
            // name that already has a decl keeps it.
            let local = &stores.local_decls;
            match decl {
                NamedDecl::Class(name, decl) => add_once(&stores.classes, &local.classes, name, decl),
                NamedDecl::Fun(name, decl) => add_once(&stores.funs, &local.funs, name, decl),
                NamedDecl::Typedef(name, decl) => add_once(&stores.typedefs, &local.typedefs, name, decl),
                NamedDecl::Const(name, decl) => add_once(&stores.consts, &local.consts, name, decl),
                NamedDecl::Module(name, decl) => add_once(&stores.modules, &local.modules, name, decl),
            }
        }
    }
}

/// `Shared_mem` `add`: no-op when the key has a value (with local changes:
/// the value goes to their top frame; `LocalChanges.add` may overwrite, but
/// a decl is only added here where there is none).
#[cfg(feature = "port")]
fn add_once<K, V>(store: &NonEvictingStore<K, Arc<V>>, frames: &reverse_naming::Frames<K, Arc<V>>, name: K, decl: V)
where
    K: Copy + Send + Sync + std::hash::Hash + Eq,
    V: Send + Sync,
{
    if frames.active() {
        let present = match frames.get(&name) {
            Some(found) => found.is_some(),
            None => store.get(name).unwrap().is_some(),
        };
        if !present {
            frames.set(name, Some(Arc::new(decl)));
        }
        return;
    }
    if store.get(name).unwrap().is_none() {
        store.insert(name, Arc::new(decl)).unwrap()
    }
}


#[cfg(feature = "port")]
use oxidized::file_info::NameType as NameTypeAlias;
#[cfg(feature = "port")]
use oxidized::naming_types::KindOfType as KindOfTypeAlias;

#[cfg(all(test, feature = "port"))]
mod tests {
    use oxidized::file_info::NameType;
    use oxidized::naming_types::KindOfType;

    use super::*;

    /// A context that declares `files` (path under the root, contents) as
    /// the init does, with their forward naming table.
    fn ctx_of(files: &[(&str, &str)]) -> (Arc<Ctx>, crate::naming_table::T) {
        let ctx = Ctx::new(Path::new("/nonexistent"), TypecheckerOptions::default()).unwrap();
        let mut paths = vec![];
        for (name, contents) in files {
            let path = RelativePath::new(Prefix::Root, name);
            ctx.files.set(path, *contents);
            paths.push(path);
        }
        let mut infos = crate::relative_path::map::T::new();
        for path in &paths {
            let decls = ctx.decl_parser.parse(*path).unwrap();
            infos.insert(
                (*path).into(),
                crate::direct_decl_service::file_info_of_decls(*path, &decls, None),
            );
        }
        // In reverse order: the winners do not depend on it.
        for path in paths.iter().rev() {
            let decls = ctx.decl_parser.parse(*path).unwrap();
            ctx.declare_file(*path, decls);
        }
        (Arc::new(ctx), crate::naming_table::create(infos))
    }

    fn rp(name: &str) -> crate::relative_path::T {
        crate::relative_path::from_root(name)
    }

    fn names(classes: &[&str], funs: &[&str]) -> crate::file_info::Names {
        let mut names = crate::file_info::empty_names();
        names.classes = classes.iter().map(|s| s.to_string()).collect();
        names.funs = funs.iter().map(|s| s.to_string()).collect();
        names
    }

    fn set(paths: &[&str]) -> crate::relative_path::set::T {
        paths.iter().map(|p| rp(p)).collect()
    }

    #[test]
    fn generation_identity() {
        let (ctx, _) = ctx_of(&[("a.php", "<?hh\nclass C {}\n")]);
        let next = ctx.next_generation();
        assert!(!Arc::ptr_eq(&ctx.shallow_decls, &next.shallow_decls));
        assert!(!Arc::ptr_eq(&ctx.folded_decls, &next.folded_decls));
        assert!(Arc::ptr_eq(&ctx.decl_stores, &next.decl_stores));
        assert!(Arc::ptr_eq(&ctx.type_canon_names, &next.type_canon_names));
        let c = TypeName::new("\\C");
        assert!(next.shallow_decls.get_class(c).unwrap().is_some());
        assert!(next.folded_decls.get_class(c).unwrap().is_some());
    }

    #[test]
    fn oldify_round_trip() {
        let (ctx, _) = ctx_of(&[("a.php", "<?hh\nclass C {}\nfunction f(): void {}\n")]);
        ctx.build_dep_hash_index();
        let c = TypeName::new("\\C");
        let folded = ctx.folded_decls.get_class(c).unwrap().unwrap();
        let live = ctx.shallow_decls.get_class(c).unwrap().unwrap();
        let ns = names(&["\\C", "\\Gone"], &["\\f"]);
        ctx.oldify_defs(&ns);
        // Moved aside: no live decl, no folded class (in the stores
        // themselves: a lookup would parse a.php again).
        assert!(ctx.decl_stores.classes.get(c).unwrap().is_none());
        assert!(ctx.decl_stores.funs.get(FunName::new("\\f")).unwrap().is_none());
        assert!(ctx.decl_stores.folded_classes.get(c).unwrap().is_none());
        let old = ctx.get_old_defs(&ns);
        assert!(Arc::ptr_eq(old.classes["\\C"].as_ref().unwrap(), &live));
        assert!(old.classes["\\Gone"].is_none());
        assert!(old.funs["\\f"].is_some());
        // The new version of the file.
        let path = RelativePath::new(Prefix::Root, "a.php");
        ctx.files.set(path, "<?hh\nclass C { public function m(): void {} }\n");
        ctx.add_shallow_decls(path, ctx.decl_parser.parse(path).unwrap());
        let new = ctx.shallow_decls.get_class(c).unwrap().unwrap();
        assert_eq!(new.methods.len(), 1);
        let refolded = ctx.folded_decls.get_class(c).unwrap().unwrap();
        assert!(!Arc::ptr_eq(&folded, &refolded));
        // The old one is still there until removed.
        assert!(Arc::ptr_eq(ctx.get_old_defs(&ns).classes["\\C"].as_ref().unwrap(), &live));
        // Oldifying a name without a live decl drops its old one.
        ctx.oldify_defs(&names(&[], &["\\f"]));
        assert!(ctx.get_old_defs(&ns).funs["\\f"].is_none());
        ctx.remove_old_defs(&ns);
        assert!(ctx.get_old_defs(&ns).classes["\\C"].is_none());
        assert!(ctx.decl_stores.classes.get(c).unwrap().is_some());
        ctx.remove_defs(&ns);
        assert!(ctx.decl_stores.classes.get(c).unwrap().is_none());
        assert!(ctx.decl_stores.folded_classes.get(c).unwrap().is_none());
        assert!(ctx.get_folded_class_if_present("\\C").is_none());
    }

    /// `test_lazy_decl_idempotence`: in the daemon, a decl removed from the
    /// store is found again by parsing the file the name is bound to; in the
    /// batch checker (no reverse naming table), a miss is a miss.
    #[test]
    fn removed_decls_come_back() {
        let src = "<?hh\nclass Foo {}\nclass Bar extends Foo {}\nfunction f(): void {}\n";
        let (batch, _) = ctx_of(&[("a.php", src)]);
        let (ctx, _) = ctx_of(&[("a.php", src)]);
        ctx.build_dep_hash_index();
        let (foo, bar) = (TypeName::new("\\Foo"), TypeName::new("\\Bar"));
        let folded = ctx.folded_decls.get_class(bar).unwrap().unwrap();
        assert!(Arc::ptr_eq(&ctx.get_folded_class_if_present("\\Bar").unwrap(), &folded));
        assert!(ctx.get_folded_class_if_present("\\Foo").is_some());
        for ctx in [&batch, &ctx] {
            ctx.remove_defs(&names(&["\\Foo", "\\Bar"], &["\\f"]));
        }
        assert!(batch.shallow_decls.get_class(foo).unwrap().is_none());
        assert!(batch.folded_decls.get_class(bar).unwrap().is_none());
        assert!(ctx.decl_stores.classes.get(foo).unwrap().is_none());
        assert!(ctx.get_folded_class_if_present("\\Bar").is_none());
        // Typing finds them again.
        assert!(ctx.folded_decls.get_class(bar).unwrap().is_some());
        assert!(ctx.decl_stores.classes.get(foo).unwrap().is_some());
        assert!(ctx.shallow_decls.get_fun(FunName::new("\\f")).unwrap().is_some());
        // The answer of a miss is the last decl of the name in the file (the
        // parse's `pfh_decls` are in reverse order); the store keeps the
        // first.
        let b = RelativePath::new(Prefix::Root, "a.php");
        ctx.files.set(b, "<?hh\nfunction f(): int { return 1; }\nfunction f(): string { return \"\"; }\n");
        ctx.remove_defs(&names(&[], &["\\f"]));
        let f = FunName::new("\\f");
        let first = ctx.shallow_decls.get_fun(f).unwrap().unwrap();
        let stored = ctx.decl_stores.funs.get(f).unwrap().unwrap();
        assert!(!Arc::ptr_eq(&first, &stored));
        assert_ne!(format!("{:?}", first.ty), format!("{:?}", stored.ty));
        // A name bound to a deleted file, or not bound, is not found.
        let a = RelativePath::new(Prefix::Root, "a.php");
        ctx.files.set(a, "<?hh\n");
        ctx.remove_defs(&names(&["\\Foo"], &[]));
        assert!(ctx.shallow_decls.get_class(foo).unwrap().is_none());
        assert!(ctx.shallow_decls.get_class(TypeName::new("\\Nope")).unwrap().is_none());
        // `Foo` is still bound to a.php, which no longer declares it.
        assert!(ctx.check_naming_invariant().is_err());
    }

    #[test]
    fn reverse_table_and_dep_hashes() {
        let (ctx, _) = ctx_of(&[
            ("a.php", "<?hh\nclass C {}\nfunction f(): void {}\nconst int K = 1;\nnew module m {}\n"),
            ("b.php", "<?hh\ntype T = int;\n"),
        ]);
        ctx.build_dep_hash_index();
        assert!(ctx.check_naming_invariant().is_ok());
        let (pos, kind) = ctx.naming_types_get_pos("\\C").unwrap();
        assert_eq!(kind, KindOfType::TClass);
        assert!(matches!(pos, crate::file_info::Pos::Full(_)));
        assert_eq!(crate::file_info::get_pos_filename(&pos), rp("a.php"));
        assert_eq!(ctx.naming_types_get_pos("\\T").unwrap().1, KindOfType::TTypedef);
        // Exact spelling for positions.
        assert!(ctx.naming_types_get_pos("\\c").is_none());
        use crate::typing_deps::dep;
        let deps = |vs: &[dep::Variant]| vs.iter().map(dep::make).collect::<crate::typing_deps::dep_set::T>();
        assert_eq!(
            ctx.naming_get_filenames_by_hash(&deps(&[dep::Variant::Fun("\\f".into())])),
            set(&["a.php"])
        );
        assert_eq!(
            ctx.naming_get_filenames_by_hash(&deps(&[
                dep::Variant::Type("\\T".into()),
                dep::Variant::GConst("\\K".into()),
                dep::Variant::Type("\\Nope".into()),
            ])),
            set(&["a.php", "b.php"])
        );
        // Not modules (`get_filename_by_hash`).
        assert!(ctx.naming_get_filenames_by_hash(&deps(&[dep::Variant::Module("m".into())])).is_empty());
        // Removal by another spelling: the canon entry goes, the position of
        // `\C` stays (as in the OCaml).
        ctx.naming_types_remove_batch(&["\\c".to_string()]);
        assert!(ctx.get_type_canon_name("\\C").is_none());
        assert!(ctx.naming_types_get_pos("\\C").is_some());
        ctx.naming_types_remove_batch(&["\\C".to_string()]);
        assert!(ctx.naming_types_get_pos("\\C").is_none());
        // Re-adding, as a recheck does.
        let file_pos = crate::file_info::Pos::File(NameType::Class, Arc::new(rp("b.php")));
        ctx.naming_types_add("\\C", &file_pos, KindOfType::TClass);
        assert_eq!(ctx.get_type_canon_name("\\c").unwrap().as_str(), "\\C");
        assert_eq!(ctx.naming_types_get_pos("\\C").unwrap().0, file_pos);
        // The decl is still that of a.php: the invariant does not hold
        // until the redecl of b.php.
        assert!(ctx.check_naming_invariant().is_err());
        ctx.naming_consts_remove_batch(&["\\K".to_string()]);
        assert!(ctx.naming_consts_get_pos("\\K").is_none());
        ctx.naming_funs_remove_batch(&["\\F".to_string()]);
        assert!(ctx.get_fun_canon_name("\\f").is_none());
        assert!(ctx.naming_funs_get_pos("\\f").is_some());
        ctx.naming_modules_remove_batch(&["m".to_string()]);
        assert!(ctx.naming_modules_get_pos("m").is_none());
    }

    #[test]
    fn add_shallow_decls_keeps_the_winners() {
        let (ctx, _) = ctx_of(&[
            ("a.php", "<?hh\nclass C {}\n"),
            ("b.php", "<?hh\nclass C { public function m(): void {} }\nclass D {}\ntype D = int;\n"),
        ]);
        ctx.build_dep_hash_index();
        let b = RelativePath::new(Prefix::Root, "b.php");
        ctx.add_shallow_decls(b, ctx.decl_parser.parse(b).unwrap());
        // `C` is bound to a.php: b.php's decl is a loser.
        let c = ctx.shallow_decls.get_class(TypeName::new("\\C")).unwrap().unwrap();
        assert_eq!(c.methods.len(), 0);
        // A typedef after a class of the same name is dropped.
        assert!(ctx.decl_stores.typedefs.get(TypeName::new("\\D")).unwrap().is_none());
        // And a class after a typedef (`dedup_decls`).
        ctx.files.set(b, "<?hh\ntype G = int;\nclass G {}\nclass D { public function m(): void {} }\n");
        ctx.add_shallow_decls(b, ctx.decl_parser.parse(b).unwrap());
        assert!(ctx.decl_stores.classes.get(TypeName::new("\\G")).unwrap().is_none());
        assert!(ctx.decl_stores.typedefs.get(TypeName::new("\\G")).unwrap().is_some());
        // A name that has a decl keeps it (`Shared_mem` `add`).
        let d = ctx.decl_stores.classes.get(TypeName::new("\\D")).unwrap().unwrap();
        assert_eq!(d.methods.len(), 0);
        // A name that is not bound keeps its decl.
        ctx.files.set(b, "<?hh\nclass E {}\n");
        ctx.add_shallow_decls(b, ctx.decl_parser.parse(b).unwrap());
        assert!(ctx.shallow_decls.get_class(TypeName::new("\\E")).unwrap().is_some());
    }

    /// `failed_naming` of the init: what the OCaml's sequential naming
    /// (`Naming_global.ndecl_file_and_get_conflict_files` over the files in
    /// order) gives on synthetic duplicates.
    #[test]
    fn init_conflict_files() {
        let (ctx, nt) = ctx_of(&[
            // No conflict.
            ("0.php", "<?hh\nclass Alone {}\n"),
            // `A` is also declared by c.php (wins: a < c); `Mine` is a's only.
            ("a.php", "<?hh\nclass A {}\nfunction mine(): void {}\n"),
            // b.php declares `Shared` twice (up to case): b fails alone.
            ("b.php", "<?hh\nfunction shared(): void {}\nfunction SHARED(): void {}\n"),
            // c.php loses `A` to a.php, and declares `K` which d.php loses.
            ("c.php", "<?hh\nclass A {}\nconst int K = 1;\n"),
            // d.php loses `K` to c.php, and `t` (case-insensitively) to e.php? No:
            // d < e, so d wins `t`; e loses it.
            ("d.php", "<?hh\nconst int K = 2;\ntype t = int;\n"),
            ("e.php", "<?hh\nclass T {}\nfunction mine2(): void {}\n"),
            // A module declared twice.
            ("f.php", "<?hh\nnew module m {}\n"),
            ("g.php", "<?hh\nnew module m {}\n"),
        ]);
        assert_eq!(
            ctx.take_init_conflict_files(&nt),
            // c: {c, a (A)}; b: {b}; d: {d, c (K), d (t)}; e: {e, d (T), e (mine2)};
            // g: {g, f}.
            set(&["a.php", "b.php", "c.php", "d.php", "e.php", "f.php", "g.php"])
        );
        let (ctx, nt) = ctx_of(&[
            ("a.php", "<?hh\nclass A {}\n"),
            ("b.php", "<?hh\nclass B {}\n"),
            // Loses both: a and b fail with it.
            ("c.php", "<?hh\nclass A {}\nclass B {}\n"),
            ("d.php", "<?hh\nclass D {}\n"),
        ]);
        assert_eq!(ctx.take_init_conflict_files(&nt), set(&["a.php", "b.php", "c.php"]));
    }
}
