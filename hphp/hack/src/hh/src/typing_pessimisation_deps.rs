// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_pessimisation_deps.ml`. See `hh/PORTING.md`.
//!
//! - As in `crate::typing_deps`, the state that every OCaml worker process
//!   has a private copy of is thread-local here: the cache of dependencies
//!   (`Backend.cache` and its size) and the database it is flushed to
//!   (`SQLitePersistence.db_stmt_cache`), a file named after the
//!   `typing_deps::worker_id` of the thread. A thread calls [`finalize`] at
//!   the end of its batch, as an OCaml worker does.
//! - `Typing_deps.Dep.dependency Typing_deps.Dep.variant` and
//!   `Typing_deps.Dep.dependent Typing_deps.Dep.variant` are both
//!   `typing_deps::dep::Variant`.
//! - The `Hashtbl.t` and `Hash_set.t` of the cache are `IndexMap` and
//!   `IndexSet`, which iterate in the order their entries were added; the
//!   OCaml iterates in the order of its hash tables. So the database gets
//!   the same rows as from the OCaml, written in another order.
//! - `Sqlite3` (the OCaml binding) is `rusqlite`; see `crate::sqlite_utils`.

#![allow(non_upper_case_globals)]

use indexmap::IndexMap;
use indexmap::IndexSet;

use crate::typing_deps::dep;
use crate::typing_deps_mode;

/// A [dependent_member] augments a [coarse_dependent]. It denotes a
/// child/member of the toplevel definition represented by
/// [coarse_dependent]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DependentMember {
    Constructor,
    Method(String),
    SMethod(String),
}

/// A dependency is something (e.g., a method) that some other piece of code
/// depends on (e.g., due to calling it)
pub type Dependency = dep::Variant;

/// A dependent (= something with dependencies) as used by the original,
/// "coarse" dependency graph mechanism
pub type CoarseDependent = dep::Variant;

/// [Typing_deps.Dep.dependency Typing_deps.Dep.variant] contains additionally
/// constructors that we don't need here.
/// Also, the fact that we use it for dependents rather than dependencies may
/// be confusing. But this type is not part of the module's interface
type FineDependent = dep::Variant;

/// For debugging: When enabled, should record exactly the same dependencies
/// as the original/coarse grained dependency tracking implemented in
/// [Typing_deps]
const record_coarse_only: bool = false;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct CacheSetEntry {
    dependency: Dependency,
    is_override: bool,
}

type Cache = IndexMap<FineDependent, IndexSet<CacheSetEntry>>;

pub mod sqlite_persistence {
    use std::cell::RefCell;

    use indexmap::IndexSet;
    use rusqlite::Connection;
    use rusqlite::OpenFlags;
    use rusqlite::Statement;
    use rusqlite::types::Value;

    use super::Cache;
    use super::CacheSetEntry;
    use crate::path;
    use crate::sqlite_utils as su;
    use crate::typing_deps;
    use crate::typing_deps::dep;
    use crate::typing_deps_mode;

    thread_local! {
        /// Contains the database connection once opened and a "statement
        /// cache", which stores compiled versions of SQL queries for later
        /// re-use
        static db_stmt_cache: RefCell<Option<su::statement_cache::T>> =
            const { RefCell::new(None) };
    }

    /// A glob pattern for the file names used by the per-worker output
    /// files. A star is used in place of the worker id
    pub const worker_file_name_glob: &str = "finedeps-*.sqlite3";

    fn target_folder_from_mode(mode: &typing_deps_mode::T) -> &str {
        match mode {
            typing_deps_mode::T::SaveToDiskMode { new_edges_dir, .. } => new_edges_dir,
            _ => panic!("Can only record fine dependencies in SaveToDiskMode"),
        }
    }

    fn worker_file_path(mode: &typing_deps_mode::T) -> String {
        let folder = target_folder_from_mode(mode);
        let worker_id = typing_deps::worker_id
            .with(|worker_id| worker_id.get())
            .unwrap_or(0);
        // String.substr_replace_first worker_file_name_glob ~pattern:"*"
        //   ~with_:(Int.to_string worker_id)
        let file_name = worker_file_name_glob.replacen('*', &worker_id.to_string(), 1);
        path::to_string(&path::concat(&path::make(folder), &file_name))
    }

    /// `S.exec db sql |> SU.check_rc db`
    fn exec_and_check(db: &Connection, sql: &str) {
        su::check_rc(db, db.execute_batch(sql))
    }

    /// `S.bind_values stmt data`: binds the values to the parameters 1, 2,
    /// ... of the statement, up to the first that fails.
    fn bind_values(stmt: &mut Statement<'_>, data: Vec<Value>) -> rusqlite::Result<()> {
        for (i, value) in data.into_iter().enumerate() {
            stmt.raw_bind_parameter(i + 1, value)?;
        }
        Ok(())
    }

    fn bind_and_exec(
        stmt_cache: &su::statement_cache::T,
        stmt: &mut Statement<'_>,
        data: Vec<Value>,
    ) {
        su::check_rc(&stmt_cache.db, bind_values(stmt, data));
        // `S.step stmt`: the statements insert, so stepping gives `DONE`.
        su::check_rc(&stmt_cache.db, stmt.raw_execute());
    }

    /// The message of the `Sqlite3.Error` that `S.db_open` raises: `error
    /// opening database: <errmsg>`. (For `CANTOPEN`, `rusqlite` appends `:
    /// <path>` to the message of SQLite; the binding does not.)
    fn db_open_errmsg(path: &str, error: &rusqlite::Error) -> String {
        match error {
            rusqlite::Error::SqliteFailure(
                rusqlite::ffi::Error {
                    code: rusqlite::ErrorCode::CannotOpen,
                    ..
                },
                Some(msg),
            ) => match msg
                .strip_suffix(path)
                .and_then(|msg| msg.strip_suffix(": "))
            {
                Some(msg) => msg.to_string(),
                None => msg.clone(),
            },
            rusqlite::Error::SqliteFailure(_, Some(msg)) => msg.clone(),
            _ => error.to_string(),
        }
    }

    fn open_db(path: &str) -> Connection {
        // `S.db_open path`, which raises `Sqlite3.Error` when the database
        // cannot be opened. The binding opens it read-write, creating it,
        // with a file name (`~uri:false`): `rusqlite`'s default flags without
        // `SQLITE_OPEN_URI`.
        let flags = OpenFlags::SQLITE_OPEN_READ_WRITE
            | OpenFlags::SQLITE_OPEN_CREATE
            | OpenFlags::SQLITE_OPEN_NO_MUTEX;
        let db = match Connection::open_with_flags(path, flags) {
            Ok(db) => db,
            Err(error) => panic!("error opening database: {}", db_open_errmsg(path, &error)),
        };
        // `rusqlite` gives every connection a busy timeout of 5 seconds; the
        // OCaml binding sets none, so that a locked database is reported
        // (`BUSY`) at once.
        db.busy_timeout(std::time::Duration::ZERO)
            .expect("sqlite3_busy_timeout");
        exec_and_check(&db, "PRAGMA synchronous = OFF;");
        exec_and_check(&db, "PRAGMA journal_mode = MEMORY;");
        db
    }

    pub(super) fn close_db() {
        // (The names of the thread-local refs, which are those of the OCaml,
        // cannot be bound by the closures: they would be patterns.)
        db_stmt_cache.with(|slot| {
            // `Option.iter !db_stmt_cache ~f:(fun stmt_cache -> ...;
            // db_stmt_cache := None)`
            let stmt_cache = slot.borrow_mut().take();
            if let Some(stmt_cache) = stmt_cache {
                su::statement_cache::close(&stmt_cache);
                // `S.db_close stmt_cache.SU.StatementCache.db |> ignore`
                let _ = stmt_cache.db.close();
            }
        })
    }

    fn create_tables(db: &Connection) {
        let create_nodes_table = "CREATE TABLE IF NOT EXISTS nodes(
           root TEXT NOT NULL,
           kind INTEGER NOT NULL,
           member TEXT,
           hash INTEGER NOT NULL
       );";

        let create_dependencies_table = "CREATE TABLE IF NOT EXISTS dependencies(
           dependent_hash INTEGER NOT NULL,
           is_override INTEGER NOT NULL,
           dependency_hash INTEGER NOT NULL
       );";

        exec_and_check(db, create_nodes_table);
        exec_and_check(db, create_dependencies_table)
    }

    /// `get_stmt_cache mode`, given what to do with the statement cache (it
    /// is thread-local): it opens the database of the worker the first time.
    fn get_stmt_cache<R>(
        mode: &typing_deps_mode::T,
        f: impl FnOnce(&su::statement_cache::T) -> R,
    ) -> R {
        let path = worker_file_path(mode);
        db_stmt_cache.with(|slot| {
            if slot.borrow().is_none() {
                let new_db = open_db(&path);
                create_tables(&new_db);

                let new_stmt_cache = su::statement_cache::make(new_db);

                *slot.borrow_mut() = Some(new_stmt_cache);
            }
            f(slot.borrow().as_ref().unwrap())
        })
    }

    fn write_node(
        stmt_cache: &su::statement_cache::T,
        data: (String, Option<String>, isize),
        hash: isize,
    ) {
        let (root, member_opt, kind_id) = data;
        let sql = "INSERT INTO nodes(root, kind, member, hash) VALUES (?, ?, ?, ?)";

        let mut stmt = su::statement_cache::make_stmt(stmt_cache, sql);
        let data = {
            use su::data_shorthands::*;
            vec![text(root), int(kind_id), opt_text(member_opt), int(hash)]
        };
        bind_and_exec(stmt_cache, &mut stmt, data)
    }

    fn write_dependency_edge(
        stmt_cache: &su::statement_cache::T,
        is_override: bool,
        dependent_hash: isize,
        dependency_hash: isize,
    ) {
        let sql = "INSERT INTO dependencies(dependent_hash, is_override, dependency_hash) VALUES (?, ?, ?)";

        let mut stmt = su::statement_cache::make_stmt(stmt_cache, sql);
        let data = {
            use su::data_shorthands::*;
            vec![int(dependent_hash), bool(is_override), int(dependency_hash)]
        };
        bind_and_exec(stmt_cache, &mut stmt, data)
    }

    pub(super) fn persist_cache(cache: &Cache, mode: &typing_deps_mode::T) {
        get_stmt_cache(mode, |db| {
            let mut all_nodes: IndexSet<dep::Variant> = IndexSet::new();
            let data_of_dep = |dep: &dep::Variant| {
                (
                    dep::extract_root_name(Some(false), dep),
                    dep::extract_member_name(dep),
                    dep::dep_kind_to_enum(dep::dep_kind_of_variant(dep)),
                )
            };

            let hash_of_dep = |dep: &dep::Variant| dep::to_int(dep::make(dep));

            let handle_dependency =
                |is_override: bool, dependent_hash: isize, dependency: &dep::Variant| {
                    let dependency_hash = hash_of_dep(dependency);
                    write_dependency_edge(db, is_override, dependent_hash, dependency_hash)
                };
            let mut handle_dependent =
                |fine_dependent: &dep::Variant, dependency_entries: &IndexSet<CacheSetEntry>| {
                    let dependent_hash = hash_of_dep(fine_dependent);
                    all_nodes.insert(fine_dependent.clone());
                    for CacheSetEntry {
                        dependency,
                        is_override,
                    } in dependency_entries
                    {
                        all_nodes.insert(dependency.clone());
                        handle_dependency(*is_override, dependent_hash, dependency)
                    }
                };
            for (key, data) in cache {
                handle_dependent(key, data)
            }
            for dep in &all_nodes {
                write_node(db, data_of_dep(dep), hash_of_dep(dep))
            }
        })
    }
}

mod backend {
    use std::cell::Cell;
    use std::cell::RefCell;

    use indexmap::IndexMap;
    use indexmap::IndexSet;

    use super::Cache;
    use super::CacheSetEntry;
    use super::Dependency;
    use super::FineDependent;
    use super::sqlite_persistence;
    use crate::typing_deps_mode;

    thread_local! {
        static cache: RefCell<Option<Cache>> = const { RefCell::new(None) };

        static cache_used_size: Cell<isize> = const { Cell::new(0) };
    }

    /// Let's (conservatively) assume each entry is 100 bytes, and we want to
    /// allow 10MB of cache (per worker)
    const cache_max_size: isize = 10_000_000 / 100;

    fn make_cache() -> Cache {
        IndexMap::new()
    }

    fn make_set() -> IndexSet<CacheSetEntry> {
        IndexSet::new()
    }

    /// `get_cache ()`, given what to do with the cache (it is thread-local):
    /// it is made the first time.
    ///
    /// (The thread-local refs have the names of the OCaml, so the closures
    /// call the cache `table`: a binding named `cache` would be a pattern.)
    fn get_cache<R>(f: impl FnOnce(&mut Cache) -> R) -> R {
        cache.with(|slot| f(slot.borrow_mut().get_or_insert_with(make_cache)))
    }

    fn incr_cache_used_size() {
        cache_used_size.with(|size| size.set(size.get() + 1))
    }

    fn cache_is_full() -> bool {
        cache_used_size.with(|size| size.get()) >= cache_max_size
    }

    pub(super) fn flush_cache(mode: &typing_deps_mode::T) {
        get_cache(|table| {
            sqlite_persistence::persist_cache(table, mode);
            table.clear()
        });
        cache_used_size.with(|size| size.set(0))
    }

    pub(super) fn add_dependency_edge(
        is_override: bool,
        mode: &typing_deps_mode::T,
        fine_dependent: FineDependent,
        dependency: Dependency,
    ) {
        get_cache(|table| {
            let inc_and_make = || {
                incr_cache_used_size();
                make_set()
            };
            let set = table.entry(fine_dependent).or_insert_with(inc_and_make);
            let entry = CacheSetEntry {
                dependency,
                is_override,
            };
            // `Result.is_ok @@ Hash_set.strict_add set entry`
            if set.insert(entry) {
                incr_cache_used_size()
            }
        });
        if cache_is_full() {
            flush_cache(mode)
        }
    }

    pub(super) fn add_node(mode: &typing_deps_mode::T, node: FineDependent) {
        get_cache(|table| {
            let inc_and_make = || {
                incr_cache_used_size();
                make_set()
            };
            table.entry(node).or_insert_with(inc_and_make);
        });
        if cache_is_full() {
            flush_cache(mode)
        }
    }

    pub(super) fn finalize(mode: &typing_deps_mode::T) {
        flush_cache(mode);
        sqlite_persistence::close_db()
    }
}

fn should_ignore_node(node: &FineDependent) -> bool {
    use dep::DepKind::*;
    let root = dep::extract_root_name(Some(false), node);
    let kind = dep::dep_kind_of_variant(node);
    // This is a sufficient, but not a necessary condition for being an hhi
    // definition. However, the alternative would be to lookup the path for
    // every defininition here.
    let is_hh_def = root.strip_prefix("HH\\").is_some();

    // Checks that this is the function call created by
    // [Naming.invalid_expr_], which doesn't provide a nicer way for checking
    // this. Note the missing toplevel \
    let is_invalid_expr_sentinel_fun = match kind {
        KFun => root == "invalid_expr",
        _ => false,
    };
    let has_useful_kind = match kind {
        KFun | KMethod | KSMethod => {
            // Dependencies that we currently utilize
            true
        }
        KGConst | KConst | KConstructor | KProp | KSProp => {
            // Dependencies that we may utilize at some point, but aren't at
            // the moment
            false
        }
        KType | KExtends | KNotSubtype | KAllMembers | KGConstName | KModule | KDeclares
        | KFile => {
            // Dependencies that we will most likely never utilize
            false
        }
    };
    is_hh_def || !has_useful_kind || is_invalid_expr_sentinel_fun
}

fn should_ignore_edge(fine_dependent: &FineDependent, dependency: &Dependency) -> bool {
    fine_dependent == dependency
        || should_ignore_node(fine_dependent)
        || should_ignore_node(dependency)
}

fn add_fine_dep(
    mode: &typing_deps_mode::T,
    fine_dependent: FineDependent,
    dependency: &Dependency,
) {
    if !should_ignore_edge(&fine_dependent, dependency) {
        backend::add_dependency_edge(false, mode, fine_dependent, dependency.clone())
    }
}

pub fn add_coarse_dep(
    mode: &typing_deps_mode::T,
    coarse_dep: &CoarseDependent,
    dependency: &Dependency,
) {
    add_fine_dep(mode, dep::dependency_of_variant(coarse_dep), dependency)
}

fn dependency_variant_of_member(class_name: &str, member: &DependentMember) -> Dependency {
    match member {
        DependentMember::Constructor => dep::Variant::Constructor(class_name.to_string()),
        DependentMember::Method(m) => dep::Variant::Method(class_name.to_string(), m.clone()),
        DependentMember::SMethod(m) => dep::Variant::SMethod(class_name.to_string(), m.clone()),
    }
}

fn fine_dependent_of_coarse_and_member(
    coarse: &CoarseDependent,
    member: Option<&DependentMember>,
) -> FineDependent {
    let member = if record_coarse_only { None } else { member };
    match (coarse, member) {
        (root, None) => dep::dependency_of_variant(root),
        (dep::Variant::Type(t), Some(member)) => dependency_variant_of_member(t, member),
        (_, Some(_)) => {
            panic!("Only types/classes can have members for the purposes of dependency tracking!")
        }
    }
}

pub fn try_add_fine_dep(
    mode: &typing_deps_mode::T,
    coarse: Option<&CoarseDependent>,
    member: Option<&DependentMember>,
    dependency: &Dependency,
) {
    let member = if record_coarse_only { None } else { member };
    match (coarse, member) {
        (None, None) => {}
        (None, Some(_)) => panic!("Cannot have member dependent without root"),
        (Some(root), member_opt) => {
            let dependent = fine_dependent_of_coarse_and_member(root, member_opt);
            add_fine_dep(mode, dependent, dependency)
        }
    }
}

pub fn add_override_dep(
    mode: &typing_deps_mode::T,
    child_name: &str,
    parent_name: &str,
    member: &DependentMember,
) {
    let dependent = dependency_variant_of_member(parent_name, member);
    let dependency = dependency_variant_of_member(child_name, member);

    if !should_ignore_edge(&dependent, &dependency) {
        backend::add_dependency_edge(true, mode, dependent, dependency)
    }
}

/// Informs the pessimisation dependency graph about the existence of a node.
/// This allows ensuring that certain nodes are added to the the graph even if
/// they may not have any incoming or outgoing edges.
pub fn add_node(
    mode: &typing_deps_mode::T,
    coarse: &CoarseDependent,
    member: Option<&DependentMember>,
) {
    let node = fine_dependent_of_coarse_and_member(coarse, member);
    if !should_ignore_node(&node) {
        backend::add_node(mode, node)
    }
}

/// Persists all currently cached dependencies to disk
pub fn finalize(mode: &typing_deps_mode::T) {
    backend::finalize(mode)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typing_deps;
    use crate::typing_deps::dep::Variant::*;
    use crate::typing_deps_mode::T;

    fn s(x: &str) -> String {
        x.to_string()
    }

    #[test]
    fn ignored_nodes_and_edges() {
        assert!(!should_ignore_node(&Fun(s("\\f"))));
        assert!(!should_ignore_node(&Method(s("\\C"), s("m"))));
        assert!(!should_ignore_node(&SMethod(s("\\C"), s("m"))));
        // Kinds that are not used (yet).
        assert!(should_ignore_node(&Type(s("\\C"))));
        assert!(should_ignore_node(&Prop(s("\\C"), s("p"))));
        assert!(should_ignore_node(&Constructor(s("\\C"))));
        assert!(should_ignore_node(&Declares));
        // `HH\` is looked for at the start of the name as it is.
        assert!(should_ignore_node(&Fun(s("HH\\f"))));
        assert!(!should_ignore_node(&Fun(s("\\HH\\f"))));
        // The function of `Naming.invalid_expr_`.
        assert!(should_ignore_node(&Fun(s("invalid_expr"))));
        assert!(!should_ignore_node(&Method(s("invalid_expr"), s("m"))));
        // An edge from a node to itself.
        assert!(should_ignore_edge(&Fun(s("\\f")), &Fun(s("\\f"))));
        assert!(!should_ignore_edge(&Fun(s("\\f")), &Fun(s("\\g"))));
        assert!(should_ignore_edge(&Fun(s("\\f")), &Type(s("\\C"))));
    }

    #[test]
    fn fine_dependents() {
        let c = Type(s("\\C"));
        assert_eq!(
            fine_dependent_of_coarse_and_member(&c, Some(&DependentMember::Method(s("m")))),
            Method(s("\\C"), s("m"))
        );
        assert_eq!(
            fine_dependent_of_coarse_and_member(&c, Some(&DependentMember::SMethod(s("m")))),
            SMethod(s("\\C"), s("m"))
        );
        assert_eq!(
            fine_dependent_of_coarse_and_member(&c, Some(&DependentMember::Constructor)),
            Constructor(s("\\C"))
        );
        assert_eq!(
            fine_dependent_of_coarse_and_member(&Fun(s("\\f")), None),
            Fun(s("\\f"))
        );
        assert!(
            std::panic::catch_unwind(|| fine_dependent_of_coarse_and_member(
                &Fun(s("\\f")),
                Some(&DependentMember::Constructor)
            ))
            .is_err()
        );
        let no_root = std::panic::catch_unwind(|| {
            try_add_fine_dep(
                &T::InMemoryMode(None),
                None,
                Some(&DependentMember::Constructor),
                &Fun(s("\\g")),
            )
        });
        assert_eq!(
            no_root.unwrap_err().downcast_ref::<&str>(),
            Some(&"Cannot have member dependent without root")
        );
        // Without a root there is nothing to record.
        try_add_fine_dep(&T::InMemoryMode(None), None, None, &Fun(s("\\g")));
    }

    #[test]
    fn finalize_needs_save_to_disk_mode() {
        let result = std::panic::catch_unwind(|| finalize(&T::InMemoryMode(None)));
        assert_eq!(
            result.unwrap_err().downcast_ref::<&str>(),
            Some(&"Can only record fine dependencies in SaveToDiskMode")
        );
    }

    #[test]
    fn a_database_that_cannot_be_opened_is_reported_as_by_the_binding() {
        let mode = T::SaveToDiskMode {
            graph: None,
            new_edges_dir: s("/nonexistent/hh_typing_pessimisation_deps_test"),
            human_readable_dep_map_dir: None,
        };
        let result = std::panic::catch_unwind(|| finalize(&mode));
        assert_eq!(
            result
                .unwrap_err()
                .downcast_ref::<String>()
                .map(String::as_str),
            Some("error opening database: unable to open database file")
        );
    }

    #[test]
    fn finalize_writes_the_database_of_the_worker() {
        let dir = std::env::temp_dir().join(format!(
            "hh_typing_pessimisation_deps_test_{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let mode = T::SaveToDiskMode {
            graph: None,
            new_edges_dir: dir.to_str().unwrap().to_string(),
            human_readable_dep_map_dir: None,
        };
        typing_deps::worker_id.with(|worker_id| worker_id.set(Some(7)));
        let method_m = DependentMember::Method(s("m"));
        try_add_fine_dep(&mode, Some(&Fun(s("\\f"))), None, &Fun(s("\\g")));
        try_add_fine_dep(
            &mode,
            Some(&Type(s("\\C"))),
            Some(&method_m),
            &Fun(s("\\g")),
        );
        // The same edge again, and edges that are ignored.
        try_add_fine_dep(&mode, Some(&Fun(s("\\f"))), None, &Fun(s("\\g")));
        try_add_fine_dep(&mode, Some(&Fun(s("\\f"))), None, &Type(s("\\C")));
        try_add_fine_dep(&mode, Some(&Fun(s("\\f"))), None, &Fun(s("\\f")));
        add_override_dep(&mode, "\\D", "\\C", &method_m);
        add_node(&mode, &Fun(s("\\h")), None);
        add_node(&mode, &Type(s("\\C")), None);
        finalize(&mode);
        typing_deps::worker_id.with(|worker_id| worker_id.set(None));

        let hash = |v: &dep::Variant| dep::to_int(dep::make(v)) as i64;
        let db = rusqlite::Connection::open(dir.join("finedeps-7.sqlite3")).unwrap();
        let mut nodes: Vec<(String, i64, Option<String>, i64)> = {
            let mut stmt = db
                .prepare("SELECT root, kind, member, hash FROM nodes")
                .unwrap();
            stmt.query_map([], |row| {
                Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?))
            })
            .unwrap()
            .map(Result::unwrap)
            .collect()
        };
        nodes.sort();
        let fun = dep::dep_kind_to_enum(dep::DepKind::KFun) as i64;
        let method = dep::dep_kind_to_enum(dep::DepKind::KMethod) as i64;
        let mut expected_nodes = vec![
            (s("\\f"), fun, None, hash(&Fun(s("\\f")))),
            (s("\\g"), fun, None, hash(&Fun(s("\\g")))),
            (
                s("\\C"),
                method,
                Some(s("m")),
                hash(&Method(s("\\C"), s("m"))),
            ),
            (
                s("\\D"),
                method,
                Some(s("m")),
                hash(&Method(s("\\D"), s("m"))),
            ),
            (s("\\h"), fun, None, hash(&Fun(s("\\h")))),
        ];
        expected_nodes.sort();
        assert_eq!(nodes, expected_nodes);

        let mut edges: Vec<(i64, i64, i64)> = {
            let mut stmt = db
                .prepare("SELECT dependent_hash, is_override, dependency_hash FROM dependencies")
                .unwrap();
            stmt.query_map([], |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)))
                .unwrap()
                .map(Result::unwrap)
                .collect()
        };
        edges.sort();
        let mut expected_edges = vec![
            (hash(&Fun(s("\\f"))), 0, hash(&Fun(s("\\g")))),
            (hash(&Method(s("\\C"), s("m"))), 0, hash(&Fun(s("\\g")))),
            (
                hash(&Method(s("\\C"), s("m"))),
                1,
                hash(&Method(s("\\D"), s("m"))),
            ),
        ];
        expected_edges.sort();
        assert_eq!(edges, expected_edges);
        drop(db);
        let _ = std::fs::remove_dir_all(&dir);
    }
}
