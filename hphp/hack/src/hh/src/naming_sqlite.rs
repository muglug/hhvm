// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/naming_sqlite.ml`.
//!
//! Owned by **SS1** (plan §7.3).
//!
//! The naming-table database: a forward table (`NAMING_FILE_INFO`, the file
//! infos by path), a reverse table (`NAMING_SYMBOLS`, the file of a symbol by
//! its 64-bit dependency hash, with a case-insensitive `CANON_HASH`), a
//! checksum, and the local-changes blob. The schema is the one the crate
//! `names` (`hh_naming_table_builder`) also writes; this module issues the
//! OCaml's own SQL, in the OCaml's order, so that a database it writes has
//! the same table contents as one the OCaml writes from the same file infos
//! (`names` writes its own variant: `NAMING_SYMBOLS_OVERFLOW` for
//! duplicates, `FILE_DIGEST` `""` instead of `NULL`).
//!
//! # Differences from the OCaml that nothing outside the process sees
//!
//! - The cached connection (`db_cache`) is per thread: OCaml workers are
//!   processes, each with its own cache; here the workers are threads and a
//!   SQLite connection is not `Sync`. [`free_db_cache`] drops the cache of
//!   every thread (each thread drops its connection the next time it uses
//!   the cache).
//! - `StatementCache` is rusqlite's prepared-statement cache.
//!
//! # Exceptions
//!
//! The OCaml raises `Failure` (from `check_rc`, `failwith`), `Sqlite3.Error`
//! (opening a database, preparing a statement), `Invalid_argument` (a column
//! of an unexpected type, a relative-path prefix that is not set) and the
//! exceptions of `FileUtil.cp`. Here they are the [`Error`] of a `Result`,
//! whose `Debug` is `Printexc.to_string` of the OCaml exception
//! (`Failure("SQLite operation failed: CONSTRAINT (...)")`).
//!
//! # `NAMING_LOCAL_CHANGES`
//!
//! The `LOCAL_CHANGES` column is an OCaml `Marshal` blob of a
//! `File_info.saved forward_naming_table_delta Relative_path.Map.t`. The
//! OCaml only ever writes the empty map (`LocalChanges.prime`), whose
//! encoding is the constant [`EMPTY_LOCAL_CHANGES_BLOB`]; reading it gives
//! no deltas. A non-empty blob is decoded with the Marshal codec of
//! `rt::ocaml_marshal` ([`local_changes::file_deltas_of_blob`],
//! [`blob_format_of_ocaml`]).

use std::cell::RefCell;
use std::fmt::Debug;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;

use oxidized::naming_types::KindOfType;
use oxidized::naming_types::NameKind;
use rusqlite::Connection;
use rusqlite::types::ValueRef;

use crate::exception;
use crate::file_info;
use crate::file_info::NameType;
use crate::format;
use crate::format::Formatter;
use crate::hh_logger;
use crate::relative_path;
use crate::relative_path::Prefix;
use crate::relative_path::RelativePath;
use crate::rt::ocaml_marshal;
use crate::rt::ocaml_printf::sprintf_S;
use crate::typing_deps::dep;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// `type db_path = Db_path of string`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DbPath(pub String);

/// `[@@deriving eq]`
pub fn equal_db_path(a: &DbPath, b: &DbPath) -> bool {
    a == b
}

/// `[@@deriving show]`
pub fn pp_db_path(fmt: &mut Formatter, DbPath(s): &DbPath) {
    pp_constr1(fmt, "Naming_sqlite.Db_path", |fmt| {
        format::pp_print_string(fmt, &sprintf_S(s))
    })
}

/// `[@@deriving show]`
pub fn show_db_path(p: &DbPath) -> String {
    format::asprintf(|fmt| pp_db_path(fmt, p))
}

/// The OCaml exceptions this module raises or lets through (see the module
/// documentation). `Debug` is `Printexc.to_string`.
#[derive(Clone, PartialEq, Eq)]
pub enum Error {
    /// `Failure msg`
    Failure(String),
    /// `Invalid_argument msg`
    InvalidArgument(String),
    /// `Sqlite3.Error msg`
    Sqlite3Error(String),
    /// `Sys_error msg` (and the errors of `FileUtil.cp`)
    SysError(String),
}

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Failure(s) => write!(f, "Failure({})", sprintf_S(s)),
            Error::InvalidArgument(s) => write!(f, "Invalid_argument({})", sprintf_S(s)),
            Error::Sqlite3Error(s) => write!(f, "Sqlite3.Error({})", sprintf_S(s)),
            Error::SysError(s) => write!(f, "Sys_error({})", sprintf_S(s)),
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

pub struct InsertionError {
    pub canon_hash: i64,
    pub hash: i64,
    pub name_kind: NameKind,
    pub name: String,
    pub origin_exception: exception::T,
}

impl Debug for InsertionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&show_insertion_error(self))
    }
}

/// `[@@deriving show]`, with the field printer of `origin_exception`
/// (`Exception.get_ctor_string`).
pub fn pp_insertion_error(fmt: &mut Formatter, e: &InsertionError) {
    pp_record(
        fmt,
        &[
            ("Naming_sqlite.canon_hash", &|fmt| pp_int64(fmt, e.canon_hash)),
            ("hash", &|fmt| pp_int64(fmt, e.hash)),
            ("name_kind", &|fmt| pp_name_kind(fmt, &e.name_kind)),
            ("name", &|fmt| format::pp_print_string(fmt, &sprintf_S(&e.name))),
            ("origin_exception", &|fmt| {
                format::pp_print_string(fmt, &exception::get_ctor_string(&e.origin_exception))
            }),
        ],
    )
}

pub fn show_insertion_error(e: &InsertionError) -> String {
    format::asprintf(|fmt| pp_insertion_error(fmt, e))
}

#[derive(Debug)]
pub struct SaveResult {
    pub files_added: isize,
    pub symbols_added: isize,
    pub errors: Vec<InsertionError>,
    pub checksum: i64,
}

/// `[@@deriving show]`
pub fn pp_save_result(fmt: &mut Formatter, r: &SaveResult) {
    pp_record(
        fmt,
        &[
            ("Naming_sqlite.files_added", &|fmt| {
                format::pp_print_string(fmt, &r.files_added.to_string())
            }),
            ("symbols_added", &|fmt| {
                format::pp_print_string(fmt, &r.symbols_added.to_string())
            }),
            ("errors", &|fmt| pp_list(fmt, &r.errors, pp_insertion_error)),
            ("checksum", &|fmt| pp_int64(fmt, r.checksum)),
        ],
    )
}

/// `[@@deriving show]`
pub fn show_save_result(r: &SaveResult) -> String {
    format::asprintf(|fmt| pp_save_result(fmt, r))
}

pub fn empty_save_result(checksum: i64) -> SaveResult {
    SaveResult {
        files_added: 0,
        symbols_added: 0,
        errors: vec![],
        checksum,
    }
}

fn insert_safe(
    name: &str,
    name_kind: &NameKind,
    hash: i64,
    canon_hash: i64,
    f: impl FnOnce() -> Result<()>,
) -> std::result::Result<(), InsertionError> {
    match f() {
        Ok(()) => Ok(()),
        Err(e) => {
            let origin_exception = exception::wrap(e);
            Err(InsertionError {
                canon_hash,
                hash,
                name_kind: name_kind.clone(),
                name: name.to_string(),
                origin_exception,
            })
        }
    }
}

/// `'a forward_naming_table_delta`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForwardNamingTableDelta<A> {
    Modified(A),
    Deleted,
}

/// `file_deltas`
pub type FileDeltas = relative_path::map::T<ForwardNamingTableDelta<file_info::T>>;

/// `local_changes`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalChanges {
    pub file_deltas: FileDeltas,
    pub base_content_version: String,
}

/// `symbol_and_decl_hash`
struct SymbolAndDeclHash {
    /// the HASH column of NAMING_SYMBOLS
    symbol: i64,
    /// the DECL_HASH column of NAMING_SYMBOLS
    decl_hash: file_info::decl_hash::T,
}

/// `external checksum_addremove` (`checksum_addremove_ffi` in
/// `rust_decl_ffi.rs`, the same as `hh24_types::Checksum::addremove`).
pub fn checksum_addremove(
    checksum: i64,
    symbol: i64,
    decl_hash: file_info::decl_hash::T,
    path: &RelativePath,
) -> i64 {
    let checksum = checksum as u64;
    let checksum = checksum ^ hh_hash::hash(&(symbol, decl_hash, path));
    checksum as i64
}

fn make_relative_path(prefix_int: i64, suffix: &str) -> Result<RelativePath> {
    let prefix: Prefix = match relative_path::prefix_of_enum(prefix_int as isize) {
        Some(prefix) => prefix,
        None => panic!("Option.value_exn None"),
    };
    let prefix_path = relative_path::path_of_prefix(prefix)
        .map_err(|relative_path::InvalidArgument(msg)| Error::InvalidArgument(msg))?;
    let full_suffix = crate::rt::ocaml_filename::concat(&prefix_path, suffix);
    Ok(relative_path::create(prefix, &full_suffix))
}

/// The canonical name (and assorted *Canon heaps) store the canonical name for a
/// symbol, keyed off of the lowercase version of its name. We use the canon
/// heaps to check for symbols which are redefined using different
/// capitalizations so we can throw proper Hack errors for them.
pub fn to_canon_name_key(s: &str) -> String {
    s.to_ascii_lowercase()
}

// ---------------------------------------------------------------------------
// `Sqlite_utils` and the result codes of `Sqlite3`
// ---------------------------------------------------------------------------

/// `Sqlite3.Rc.to_string` of a result code.
fn rc_to_string(code: i32) -> &'static str {
    match code & 0xff {
        0 => "OK",
        1 => "ERROR",
        2 => "INTERNAL",
        3 => "PERM",
        4 => "ABORT",
        5 => "BUSY",
        6 => "LOCKED",
        7 => "NOMEM",
        8 => "READONLY",
        9 => "INTERRUPT",
        10 => "IOERR",
        11 => "CORRUPT",
        12 => "NOTFOUND",
        13 => "FULL",
        14 => "CANTOPEN",
        15 => "PROTOCOL",
        16 => "EMPTY",
        17 => "SCHEMA",
        18 => "TOOBIG",
        19 => "CONSTRAINT",
        20 => "MISMATCH",
        21 => "MISUSE",
        22 => "NOFLS",
        23 => "AUTH",
        24 => "FORMAT",
        25 => "RANGE",
        26 => "NOTADB",
        27 => "NOTICE",
        28 => "WARNING",
        100 => "ROW",
        101 => "DONE",
        _ => "UNKNOWN",
    }
}

/// The result code and `Sqlite3.errmsg db` of a failed operation.
fn rc_and_errmsg(e: &rusqlite::Error) -> (&'static str, String) {
    match e {
        rusqlite::Error::SqliteFailure(err, msg) => (
            rc_to_string(err.extended_code),
            msg.clone().unwrap_or_else(|| err.to_string()),
        ),
        // `step` gave a row where none was expected.
        rusqlite::Error::ExecuteReturnedResults => ("ROW", "another row available".to_string()),
        e => ("ERROR", e.to_string()),
    }
}

/// `Sqlite_utils.check_rc db rc`, for an operation that failed.
fn check_rc(e: rusqlite::Error) -> Error {
    let (rc, msg) = rc_and_errmsg(&e);
    Error::Failure(format!("SQLite operation failed: {} ({})", rc, msg))
}

/// `Sqlite3.prepare` (and `Sqlite3.db_open`) raise `Sqlite3.Error`.
fn sqlite3_error(e: rusqlite::Error) -> Error {
    let (_, msg) = rc_and_errmsg(&e);
    Error::Sqlite3Error(msg)
}

/// `Sqlite3.exec db sql |> check_rc db`
fn exec(db: &Connection, sql: &str) -> Result<()> {
    db.execute_batch(sql).map_err(check_rc)
}

/// `StatementCache.make_stmt`
fn make_stmt<'a>(db: &'a Connection, sql: &str) -> Result<rusqlite::CachedStatement<'a>> {
    db.prepare_cached(sql).map_err(sqlite3_error)
}

/// `Sqlite3.bind stmt i data |> check_rc db`
fn bind(stmt: &mut rusqlite::Statement<'_>, i: usize, data: impl rusqlite::ToSql) -> Result<()> {
    stmt.raw_bind_parameter(i, data).map_err(check_rc)
}

/// `Sqlite3.step stmt |> check_rc db` (of a statement that gives no row).
fn step_done(stmt: &mut rusqlite::Statement<'_>) -> Result<()> {
    stmt.raw_execute().map(|_| ()).map_err(check_rc)
}

/// `Sqlite3.Data.to_string_debug`
fn to_string_debug(v: ValueRef<'_>) -> String {
    match v {
        ValueRef::Null => "NULL".to_string(),
        ValueRef::Integer(i) => format!("INT <{}>", i),
        ValueRef::Real(f) => format!("FLOAT <{}>", f),
        ValueRef::Text(s) => format!("TEXT <{}>", sprintf_S(&String::from_utf8_lossy(s))),
        ValueRef::Blob(b) => format!("BLOB <{}>", b.len()),
    }
}

fn column<'a>(row: &'a rusqlite::Row<'_>, idx: usize) -> Result<ValueRef<'a>> {
    row.get_ref(idx).map_err(check_rc)
}

fn to_str_exn(value: ValueRef<'_>) -> Result<String> {
    match value {
        ValueRef::Text(s) => Ok(String::from_utf8_lossy(s).into_owned()),
        _ => Err(Error::InvalidArgument(format!(
            "Expected a string, but was {}",
            to_string_debug(value)
        ))),
    }
}

fn to_blob_exn(value: ValueRef<'_>) -> Result<Vec<u8>> {
    match value {
        ValueRef::Blob(b) => Ok(b.to_vec()),
        _ => Err(Error::InvalidArgument(format!(
            "Expected a blob, but was {}",
            to_string_debug(value)
        ))),
    }
}

/// Convert a sqlite data value to an Int64, or raise an exception
fn to_int64_exn(value: ValueRef<'_>) -> Result<i64> {
    match value {
        ValueRef::Integer(i) => Ok(i),
        _ => Err(Error::InvalidArgument(format!(
            "Expected an int, but was {}",
            to_string_debug(value)
        ))),
    }
}

fn column_str(row: &rusqlite::Row<'_>, idx: usize) -> Result<String> {
    to_str_exn(column(row, idx)?)
}

fn column_blob(row: &rusqlite::Row<'_>, idx: usize) -> Result<Vec<u8>> {
    to_blob_exn(column(row, idx)?)
}

fn column_int64(row: &rusqlite::Row<'_>, idx: usize) -> Result<i64> {
    to_int64_exn(column(row, idx)?)
}

fn column_str_option(row: &rusqlite::Row<'_>, idx: usize) -> Result<Option<String>> {
    match column(row, idx)? {
        ValueRef::Null => Ok(None),
        v => to_str_exn(v).map(Some),
    }
}

fn column_int64_option(row: &rusqlite::Row<'_>, idx: usize) -> Result<Option<i64>> {
    match column(row, idx)? {
        ValueRef::Null => Ok(None),
        v => to_int64_exn(v).map(Some),
    }
}

/// `fold_sqlite stmt ~f ~init`: the rows of a query whose parameters are
/// bound.
fn fold_sqlite<A>(
    stmt: &mut rusqlite::Statement<'_>,
    init: A,
    mut f: impl FnMut(&rusqlite::Row<'_>, A) -> Result<A>,
) -> Result<A> {
    let mut rows = stmt.raw_query();
    let mut acc = init;
    loop {
        match rows.next() {
            Ok(None) => return Ok(acc),
            Ok(Some(row)) => acc = f(row, acc)?,
            Err(e) => {
                return Err(Error::Failure(format!(
                    "SQLite operation failed: {}",
                    rc_and_errmsg(&e).0
                )));
            }
        }
    }
}

/// `Sqlite3.step stmt` of a query expected to give one row: the row, or
/// `failwith (Printf.sprintf "Failure retrieving row: %s" rc)`. (`get`
/// treats `DONE` itself where the OCaml matches it.)
fn step_row<A>(
    stmt: &mut rusqlite::Statement<'_>,
    on_done: impl FnOnce() -> Result<A>,
    on_row: impl FnOnce(&rusqlite::Row<'_>) -> Result<A>,
) -> Result<A> {
    let mut rows = stmt.raw_query();
    match rows.next() {
        Ok(None) => on_done(),
        Ok(Some(row)) => on_row(row),
        Err(e) => Err(Error::Failure(format!(
            "Failure retrieving row: {}",
            rc_and_errmsg(&e).0
        ))),
    }
}

// ---------------------------------------------------------------------------
// It's kind of weird to just dump this into the SQLite database, but removing
// entries one at a time during a normal incremental update leads to too many
// table scans, and I don't want to put this in a separate file because then
// the naming table and dep table in a given SQLite database might not agree
// with each other, and that just feels weird.
// ---------------------------------------------------------------------------

/// `Marshal.to_string (Relative_path.Map.empty : blob_format) [Marshal.No_sharing]`
pub const EMPTY_LOCAL_CHANGES_BLOB: &[u8] = &[
    0x84, 0x95, 0xa6, 0xbe, // magic (small header)
    0x00, 0x00, 0x00, 0x01, // data length
    0x00, 0x00, 0x00, 0x00, // number of objects
    0x00, 0x00, 0x00, 0x00, // size in words (32-bit)
    0x00, 0x00, 0x00, 0x00, // size in words (64-bit)
    0x40, // the immediate 0: `Empty`
];

pub mod local_changes {
    use super::*;

    pub const TABLE_NAME: &str = "NAMING_LOCAL_CHANGES";

    pub fn create_table_sqlite() -> String {
        format!(
            "
          CREATE TABLE IF NOT EXISTS {}(
            ID INTEGER PRIMARY KEY,
            LOCAL_CHANGES BLOB NOT NULL,
            BASE_CONTENT_VERSION TEXT
          );
        ",
            TABLE_NAME
        )
    }

    pub fn insert_sqlite() -> String {
        format!(
            "
          INSERT INTO {} (ID, LOCAL_CHANGES, BASE_CONTENT_VERSION) VALUES (0, ?, ?);
        ",
            TABLE_NAME
        )
    }

    pub fn get_sqlite() -> String {
        format!(
            "
          SELECT LOCAL_CHANGES, BASE_CONTENT_VERSION FROM {};
        ",
            TABLE_NAME
        )
    }

    pub fn prime(db: &Connection, base_content_version: &str) -> Result<()> {
        let mut insert_stmt = make_stmt(db, &insert_sqlite())?;
        let empty = EMPTY_LOCAL_CHANGES_BLOB;
        bind(&mut insert_stmt, 1, empty)?;
        bind(&mut insert_stmt, 2, base_content_version)?;
        step_done(&mut insert_stmt)
    }

    /// `Marshal.from_string local_changes_blob 0`, then `File_info.from_saved`
    /// on each `Modified`. A blob that is not a marshalled `blob_format` is
    /// a `Failure` (the OCaml's `Marshal` raises `Failure "input_value: ..."`
    /// on a malformed blob, and reads a well-formed one of another type as
    /// garbage).
    pub fn file_deltas_of_blob(local_changes_blob: &[u8]) -> Result<FileDeltas> {
        if local_changes_blob == EMPTY_LOCAL_CHANGES_BLOB {
            return Ok(FileDeltas::new());
        }
        let v = ocaml_marshal::from_bytes(local_changes_blob, 0)
            .map_err(|ocaml_marshal::MarshalError(msg)| Error::Failure(msg))?;
        let local_changes_saved = blob_format_of_ocaml(&v)
            .map_err(|ocaml_marshal::ConvError(msg)| Error::Failure(format!("input_value: {}", msg)))?;
        Ok(local_changes_saved
            .into_iter()
            .map(|(path, delta)| {
                let delta = match delta {
                    ForwardNamingTableDelta::Modified(saved) => {
                        ForwardNamingTableDelta::Modified(file_info::from_saved(path.clone(), &saved))
                    }
                    ForwardNamingTableDelta::Deleted => ForwardNamingTableDelta::Deleted,
                };
                (path, delta)
            })
            .collect())
    }

    pub fn get(db: &Connection) -> Result<LocalChanges> {
        let mut get_stmt = make_stmt(db, &get_sqlite())?;
        // We don't include DONE in this match because we always expect
        // exactly one row.
        let mut rows = get_stmt.raw_query();
        match rows.next() {
            Ok(Some(row)) => {
                let local_changes_blob = column_blob(row, 0)?;
                let file_deltas = file_deltas_of_blob(&local_changes_blob)?;
                let base_content_version = column_str(row, 1)?;
                // (`Hack_event_logger.naming_sqlite_local_changes_nonempty "get"`
                // when there are deltas: a no-op in OSS.)
                Ok(LocalChanges {
                    base_content_version,
                    file_deltas,
                })
            }
            Ok(None) => Err(Error::Failure("Failure retrieving row: DONE".to_string())),
            Err(e) => Err(Error::Failure(format!(
                "Failure retrieving row: {}",
                rc_and_errmsg(&e).0
            ))),
        }
    }
}

/// `blob_format` (`File_info.saved forward_naming_table_delta
/// Relative_path.Map.t`) as OCaml values: what `NAMING_LOCAL_CHANGES` holds.
/// `Relative_path.t` is `prefix * string` (the prefix a constant
/// constructor, `Root` = 0), `Relative_path.Map` and `S_set` the stdlib's
/// `Map.Make`/`Set.Make` (by `Relative_path.compare` and `String.compare`),
/// `File_info.saved` the record `{ s_names: { sn_funs; sn_classes; sn_types;
/// sn_consts; sn_modules }; s_position_free_decl_hash: Int64.t option;
/// s_mode: mode option }` (`Mhhi` = 0, `Mstrict` = 1), `Modified saved` a
/// block of tag 0 and `Deleted` the integer 0. (L0.)
pub type BlobFormat = Vec<(RelativePath, ForwardNamingTableDelta<file_info::Saved>)>;

fn relative_path_of_ocaml(v: &ocaml_marshal::Value) -> std::result::Result<RelativePath, ocaml_marshal::ConvError> {
    let f = v.fields(0, 2)?;
    let prefix = relative_path::prefix_of_enum(f[0].as_int()? as isize)
        .ok_or_else(|| ocaml_marshal::ConvError(format!("not a Relative_path.prefix: {:?}", f[0])))?;
    let suffix = String::from_utf8(f[1].as_bytes()?.to_vec())
        .map_err(|e| ocaml_marshal::ConvError(e.to_string()))?;
    Ok(RelativePath::make(prefix, std::path::PathBuf::from(suffix)))
}

fn s_set_of_ocaml(v: &ocaml_marshal::Value) -> std::result::Result<std::collections::BTreeSet<String>, ocaml_marshal::ConvError> {
    ocaml_marshal::ocaml_set::elements_of_ocaml(v)?
        .into_iter()
        .map(|s| {
            String::from_utf8(s.as_bytes()?.to_vec()).map_err(|e| ocaml_marshal::ConvError(e.to_string()))
        })
        .collect()
}

fn saved_of_ocaml(v: &ocaml_marshal::Value) -> std::result::Result<file_info::Saved, ocaml_marshal::ConvError> {
    let f = v.fields(0, 3)?;
    let n = f[0].fields(0, 5)?;
    let names = file_info::SavedNames {
        funs: s_set_of_ocaml(&n[0])?,
        classes: s_set_of_ocaml(&n[1])?,
        types: s_set_of_ocaml(&n[2])?,
        consts: s_set_of_ocaml(&n[3])?,
        modules: s_set_of_ocaml(&n[4])?,
    };
    let position_free_decl_hash = match &f[1] {
        ocaml_marshal::Value::Int(0) => None,
        some => Some(some.fields(0, 1)?[0].as_int64()?),
    };
    let mode = match &f[2] {
        ocaml_marshal::Value::Int(0) => None,
        some => Some(match some.fields(0, 1)?[0].as_int()? {
            0 => file_info::Mode::Mhhi,
            1 => file_info::Mode::Mstrict,
            n => return Err(ocaml_marshal::ConvError(format!("not a File_info.mode: {}", n))),
        }),
    };
    Ok(file_info::Saved::of_fields(names, position_free_decl_hash, mode))
}

/// The bindings of a marshalled `blob_format`, in key order.
pub fn blob_format_of_ocaml(v: &ocaml_marshal::Value) -> std::result::Result<BlobFormat, ocaml_marshal::ConvError> {
    ocaml_marshal::ocaml_map::bindings_of_ocaml(v)?
        .into_iter()
        .map(|(k, d)| {
            let path = relative_path_of_ocaml(k)?;
            let delta = match d {
                ocaml_marshal::Value::Int(0) => ForwardNamingTableDelta::Deleted,
                modified => ForwardNamingTableDelta::Modified(saved_of_ocaml(&modified.fields(0, 1)?[0])?),
            };
            Ok((path, delta))
        })
        .collect()
}

/// The OCaml value of a `blob_format` whose bindings are added to the empty
/// map in this order (`Relative_path.Map.add`), as the OCaml would build it.
/// The OCaml only ever writes the empty map; this is for tests and tools.
pub fn blob_format_to_ocaml(bindings: &BlobFormat) -> ocaml_marshal::Value {
    use ocaml_marshal::Value;
    let s_set = |s: &std::collections::BTreeSet<String>| {
        let set = ocaml_marshal::ocaml_set::of_iter(s.iter().cloned(), &|a: &String, b: &String| a.cmp(b));
        ocaml_marshal::ocaml_set::to_ocaml(&set, &mut |x| Value::string(x.as_bytes()))
    };
    let map = ocaml_marshal::ocaml_map::of_iter(bindings.iter().cloned(), &|a: &RelativePath, b: &RelativePath| {
        relative_path::compare(a, b)
    });
    ocaml_marshal::ocaml_map::to_ocaml(
        &map,
        &mut |path| {
            Value::block(
                0,
                vec![
                    Value::int(relative_path::prefix_to_enum(relative_path::prefix(path)) as i64),
                    Value::string(relative_path::suffix(path).into_bytes()),
                ],
            )
        },
        &mut |delta| match delta {
            ForwardNamingTableDelta::Deleted => Value::int(0),
            ForwardNamingTableDelta::Modified(saved) => {
                let (names, hash, mode) = saved.fields();
                Value::block(
                    0,
                    vec![Value::block(
                        0,
                        vec![
                            Value::block(
                                0,
                                vec![
                                    s_set(&names.funs),
                                    s_set(&names.classes),
                                    s_set(&names.types),
                                    s_set(&names.consts),
                                    s_set(&names.modules),
                                ],
                            ),
                            match hash {
                                None => Value::int(0),
                                Some(h) => Value::some(Value::int64(h)),
                            },
                            match mode {
                                None => Value::int(0),
                                Some(file_info::Mode::Mhhi) => Value::some(Value::int(0)),
                                Some(file_info::Mode::Mstrict) => Value::some(Value::int(1)),
                            },
                        ],
                    )],
                )
            }
        },
    )
}

pub mod checksum_table {
    use super::*;

    pub const CREATE_TABLE_SQLITE: &str =
        "CREATE TABLE IF NOT EXISTS CHECKSUM (ID INTEGER PRIMARY KEY, CHECKSUM_VALUE INTEGER NOT NULL);";

    pub fn set(db: &Connection, checksum: i64) -> Result<()> {
        let mut stmt = make_stmt(db, "REPLACE INTO CHECKSUM (ID, CHECKSUM_VALUE) VALUES (0, ?);")?;
        bind(&mut stmt, 1, checksum)?;
        step_done(&mut stmt)?;
        Ok(())
    }

    pub fn get(db: &Connection) -> Result<i64> {
        let mut stmt = make_stmt(db, "SELECT CHECKSUM_VALUE FROM CHECKSUM;")?;
        let mut rows = stmt.raw_query();
        match rows.next() {
            Ok(Some(row)) => column_int64(row, 0),
            Ok(None) => Err(Error::Failure("DONE".to_string())),
            Err(e) => Err(Error::Failure(rc_and_errmsg(&e).0.to_string())),
        }
    }
}

// These are just done as modules to keep the SQLite for related tables close together.
pub mod file_info_table {
    use super::*;

    pub const TABLE_NAME: &str = "NAMING_FILE_INFO";

    pub fn create_table_sqlite() -> String {
        format!(
            "
      CREATE TABLE IF NOT EXISTS {}(
        FILE_INFO_ID INTEGER PRIMARY KEY AUTOINCREMENT,
        FILE_DIGEST TEXT,
        PATH_PREFIX_TYPE INTEGER NOT NULL,
        PATH_SUFFIX TEXT NOT NULL,
        TYPE_CHECKER_MODE INTEGER,
        DECL_HASH INTEGER,
        CLASSES TEXT,
        CONSTS TEXT,
        FUNS TEXT,
        TYPEDEFS TEXT,
        MODULES TEXT
      );
      ",
            TABLE_NAME
        )
    }

    pub fn create_index_sqlite() -> String {
        format!(
            "
      CREATE UNIQUE INDEX IF NOT EXISTS FILE_INFO_PATH_IDX ON {} (PATH_SUFFIX, PATH_PREFIX_TYPE);
      ",
            TABLE_NAME
        )
    }

    fn insert_sqlite() -> String {
        format!(
            "
        INSERT INTO {}(
          PATH_PREFIX_TYPE,
          PATH_SUFFIX,
          TYPE_CHECKER_MODE,
          DECL_HASH,
          CLASSES,
          CONSTS,
          FUNS,
          TYPEDEFS,
          MODULES
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?);
      ",
            TABLE_NAME
        )
    }

    fn delete_sqlite() -> String {
        format!(
            "
        DELETE FROM {} WHERE PATH_PREFIX_TYPE = ? AND PATH_SUFFIX = ?
      ",
            TABLE_NAME
        )
    }

    fn get_file_info_id_sqlite() -> String {
        format!(
            "
        SELECT
          FILE_INFO_ID
        FROM
          {}
        WHERE
          PATH_PREFIX_TYPE = ?
          AND PATH_SUFFIX = ?
      ",
            TABLE_NAME
        )
    }

    fn get_sqlite() -> String {
        format!(
            "
        SELECT
          TYPE_CHECKER_MODE, DECL_HASH, CLASSES, CONSTS, FUNS, TYPEDEFS, MODULES
        FROM {}
        WHERE PATH_PREFIX_TYPE = ? AND PATH_SUFFIX = ?;
      ",
            TABLE_NAME
        )
    }

    fn iter_sqlite() -> String {
        format!(
            "
        SELECT
          PATH_PREFIX_TYPE,
          PATH_SUFFIX,
          TYPE_CHECKER_MODE,
          DECL_HASH,
          CLASSES,
          CONSTS,
          FUNS,
          TYPEDEFS,
          MODULES
        FROM {}
        ORDER BY PATH_PREFIX_TYPE, PATH_SUFFIX;
      ",
            TABLE_NAME
        )
    }

    fn prefix_type(relative_path: &RelativePath) -> i64 {
        relative_path::prefix_to_enum(relative_path::prefix(relative_path)) as i64
    }

    pub fn delete(db: &Connection, relative_path: &RelativePath) -> Result<()> {
        let prefix_type = prefix_type(relative_path);
        let suffix = relative_path::suffix(relative_path);
        let mut delete_stmt = make_stmt(db, &delete_sqlite())?;
        bind(&mut delete_stmt, 1, prefix_type)?;
        bind(&mut delete_stmt, 2, suffix)?;
        step_done(&mut delete_stmt)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn insert(
        db: &Connection,
        relative_path: &RelativePath,
        type_checker_mode: Option<file_info::Mode>,
        file_decls_hash: Option<i64>,
        classes: &[file_info::Id],
        consts: &[file_info::Id],
        funs: &[file_info::Id],
        typedefs: &[file_info::Id],
        modules: &[file_info::Id],
    ) -> Result<()> {
        let prefix_type = prefix_type(relative_path);
        let suffix = relative_path::suffix(relative_path);
        let type_checker_mode: Option<i64> =
            type_checker_mode.map(|m| file_info::mode_to_enum(m) as i64);
        let names_to_data_type = |ids: &[file_info::Id]| -> Option<String> {
            let names = ids
                .iter()
                .map(|id| id.name.as_str())
                .collect::<Vec<_>>()
                .join("|");
            if names.is_empty() { None } else { Some(names) }
        };
        let mut insert_stmt = make_stmt(db, &insert_sqlite())?;
        bind(&mut insert_stmt, 1, prefix_type)?;

        bind(&mut insert_stmt, 2, suffix)?;

        bind(&mut insert_stmt, 3, type_checker_mode)?;

        bind(&mut insert_stmt, 4, file_decls_hash)?;
        bind(&mut insert_stmt, 5, names_to_data_type(classes))?;
        bind(&mut insert_stmt, 6, names_to_data_type(consts))?;
        bind(&mut insert_stmt, 7, names_to_data_type(funs))?;
        bind(&mut insert_stmt, 8, names_to_data_type(typedefs))?;
        bind(&mut insert_stmt, 9, names_to_data_type(modules))?;
        step_done(&mut insert_stmt)
    }

    pub(super) fn read_row(
        row: &rusqlite::Row<'_>,
        path: &RelativePath,
        base_index: usize,
    ) -> Result<file_info::T> {
        let file_mode = column_int64_option(row, base_index)?
            .and_then(|i| file_info::mode_of_enum(i as isize));
        let position_free_decl_hash = Some(column_int64(row, base_index + 1)?);
        let path = std::sync::Arc::new(path.clone());
        let to_ids = |value: ValueRef<'_>, name_type: NameType| -> Result<Vec<file_info::Id>> {
            match value {
                ValueRef::Text(s) => Ok(String::from_utf8_lossy(s)
                    .split('|')
                    .map(|name| {
                        let pos = file_info::Pos::File(name_type, std::sync::Arc::clone(&path));
                        file_info::Id {
                            pos,
                            name: name.to_string(),
                            decl_hash: None,
                        }
                    })
                    .collect()),
                ValueRef::Null => Ok(vec![]),
                _ => Err(Error::Failure(
                    "Unexpected column type when retrieving names".to_string(),
                )),
            }
        };
        let classes = to_ids(column(row, base_index + 2)?, NameType::Class)?;
        let consts = to_ids(column(row, base_index + 3)?, NameType::Const)?;
        let funs = to_ids(column(row, base_index + 4)?, NameType::Fun)?;
        let typedefs = to_ids(column(row, base_index + 5)?, NameType::Typedef)?;
        let modules = to_ids(column(row, base_index + 6)?, NameType::Module)?;
        Ok(file_info::FileInfo {
            position_free_decl_hash: file_info::HashType(position_free_decl_hash),
            file_mode,
            ids: file_info::Ids {
                funs,
                classes,
                typedefs,
                consts,
                modules,
            },
            comments: None,
        })
    }

    pub fn get_file_info(db: &Connection, path: &RelativePath) -> Result<Option<file_info::T>> {
        let mut get_stmt = make_stmt(db, &get_sqlite())?;
        let prefix_type = prefix_type(path);
        let suffix = relative_path::suffix(path);
        bind(&mut get_stmt, 1, prefix_type)?;
        bind(&mut get_stmt, 2, suffix)?;
        step_row(
            &mut get_stmt,
            || Ok(None),
            |row| Ok(Some(read_row(row, path, 0)?)),
        )
    }

    pub fn get_file_info_id(db: &Connection, path: &RelativePath) -> Result<Option<i64>> {
        let mut get_stmt = make_stmt(db, &get_file_info_id_sqlite())?;
        let prefix_type = prefix_type(path);
        let suffix = relative_path::suffix(path);
        bind(&mut get_stmt, 1, prefix_type)?;
        bind(&mut get_stmt, 2, suffix)?;
        step_row(&mut get_stmt, || Ok(None), |row| Ok(Some(column_int64(row, 0)?)))
    }

    pub fn fold<A>(
        db: &Connection,
        init: A,
        mut f: impl FnMut(RelativePath, file_info::T, A) -> A,
    ) -> Result<A> {
        let mut iter_stmt = make_stmt(db, &iter_sqlite())?;
        fold_sqlite(&mut iter_stmt, init, |row, acc| {
            let prefix_int = column_int64(row, 0)?;
            let suffix = column_str(row, 1)?;
            let path = make_relative_path(prefix_int, &suffix)?;
            let fi = read_row(row, &path, 2)?;
            Ok(f(path, fi, acc))
        })
    }
}

pub mod symbol_table {
    use super::*;

    pub const TABLE_NAME: &str = "NAMING_SYMBOLS";

    pub fn create_table_sqlite() -> String {
        // CANON_HASH is the hash of the lowercase form of the name (even for consts which don't need it)
        // FLAGS comes from Naming_types.name_kind
        format!(
            "
      CREATE TABLE IF NOT EXISTS {}(
        HASH INTEGER PRIMARY KEY NOT NULL,
        CANON_HASH INTEGER NOT NULL,
        DECL_HASH INTEGER NOT NULL,
        FLAGS INTEGER NOT NULL,
        FILE_INFO_ID INTEGER NOT NULL
      );
    ",
            TABLE_NAME
        )
    }

    pub fn create_index_sqlite() -> String {
        format!(
            "
    CREATE INDEX IF NOT EXISTS TYPES_CANON ON {} (CANON_HASH);
    ",
            TABLE_NAME
        )
    }

    pub fn create_temporary_index_sqlite() -> String {
        format!(
            "
    CREATE INDEX IF NOT EXISTS SYMBOLS_FILE_INFO_ID ON {} (FILE_INFO_ID);
    ",
            TABLE_NAME
        )
    }

    pub const DROP_TEMPORARY_INDEX_SQLITE: &str = "
    DROP INDEX SYMBOLS_FILE_INFO_ID;
    ";

    fn insert_sqlite() -> String {
        format!(
            "
      INSERT INTO {}(
        HASH,
        CANON_HASH,
        DECL_HASH,
        FLAGS,
        FILE_INFO_ID)
      VALUES (?, ?, ?, ?, ?);
    ",
            TABLE_NAME
        )
    }

    fn delete_sqlite() -> String {
        format!(
            "
      DELETE FROM {} WHERE FILE_INFO_ID = ?
      ",
            TABLE_NAME
        )
    }

    fn base() -> String {
        "
        SELECT
          NAMING_FILE_INFO.PATH_PREFIX_TYPE,
          NAMING_FILE_INFO.PATH_SUFFIX,
          NAMING_FILE_INFO.FILE_DIGEST,
          {table_name}.FLAGS,
          {table_name}.DECL_HASH
        FROM {table_name}
        LEFT JOIN NAMING_FILE_INFO ON
          {table_name}.FILE_INFO_ID = NAMING_FILE_INFO.FILE_INFO_ID
        WHERE {table_name}.{hash} = ?"
            .replace("{table_name}", TABLE_NAME)
    }

    /// The query of a symbol by `HASH`.
    pub fn get_sqlite() -> String {
        base().replace("{hash}", "HASH")
    }

    /// The query of a symbol by `CANON_HASH`.
    pub fn get_sqlite_case_insensitive() -> String {
        base().replace("{hash}", "CANON_HASH")
    }

    pub fn delete(db: &Connection, file_info_id: i64) -> Result<()> {
        let mut delete_stmt = make_stmt(db, &delete_sqlite())?;
        bind(&mut delete_stmt, 1, file_info_id)?;
        step_done(&mut delete_stmt)
    }

    /// Note: name parameter is used solely for debugging; it's only the hash and canon_hash that get inserted.
    pub fn insert(
        db: &Connection,
        name: &str,
        hash: i64,
        canon_hash: i64,
        name_kind: &NameKind,
        file_info_id: i64,
        decl_hash: file_info::decl_hash::T,
    ) -> std::result::Result<(), InsertionError> {
        insert_safe(name, name_kind, hash, canon_hash, || {
            let flags = name_kind_to_enum(name_kind) as i64;
            let mut insert_stmt = make_stmt(db, &insert_sqlite())?;
            bind(&mut insert_stmt, 1, hash)?;
            bind(&mut insert_stmt, 2, canon_hash)?;
            bind(&mut insert_stmt, 3, file_info::decl_hash::to_int64(decl_hash))?;
            bind(&mut insert_stmt, 4, flags)?;
            bind(&mut insert_stmt, 5, file_info_id)?;
            step_done(&mut insert_stmt)
        })
    }

    /// `(path, name_kind, decl_hash, file_hash)` of a symbol.
    pub type Row = (RelativePath, NameKind, String, String);

    pub fn get(db: &Connection, dep: dep::T, stmt: &str) -> Result<Option<Row>> {
        let hash = dep::to_int64(dep);
        let mut get_stmt = make_stmt(db, stmt)?;
        bind(&mut get_stmt, 1, hash)?;
        step_row(
            &mut get_stmt,
            || Ok(None),
            |row| {
                let prefix_type = column_int64(row, 0)?;
                let suffix = column_str(row, 1)?;
                let file_hash_opt = column_str_option(row, 2)?;
                let file_hash = file_hash_opt.unwrap_or_default();
                let flag = column_int64(row, 3)?;
                let decl_hash = column_int64(row, 4)?.to_string();
                let name_kind = match name_kind_of_enum(flag as isize) {
                    Some(name_kind) => name_kind,
                    None => panic!("Option.value_exn None"),
                };
                Ok(Some((
                    make_relative_path(prefix_type, &suffix)?,
                    name_kind,
                    decl_hash,
                    file_hash,
                )))
            },
        )
    }

    pub(super) fn get_symbols_and_decl_hashes_for_file_id(
        db: &Connection,
        file_info_id: i64,
    ) -> Result<Vec<SymbolAndDeclHash>> {
        let sqlite = format!(
            "SELECT HASH, DECL_HASH FROM {} WHERE FILE_INFO_ID = ?",
            TABLE_NAME
        );
        let mut stmt = make_stmt(db, &sqlite)?;
        bind(&mut stmt, 1, file_info_id)?;
        let mut acc = fold_sqlite(&mut stmt, vec![], |row, mut acc| {
            let symbol = column_int64(row, 0)?;
            let decl_hash = file_info::decl_hash::from_naming_table(column_int64(row, 1)?);
            acc.push(SymbolAndDeclHash { symbol, decl_hash });
            Ok(acc)
        })?;
        // `{ symbol; decl_hash } :: acc`
        acc.reverse();
        Ok(acc)
    }
}

// ---------------------------------------------------------------------------
// `Naming_types.name_kind`
// ---------------------------------------------------------------------------

/// `Naming_types.name_kind_to_enum`: these values are stored in the naming
/// table database (the numbers of `File_info.name_type`).
pub fn name_kind_to_enum(name_kind: &NameKind) -> isize {
    let name_type = match name_kind {
        NameKind::TypeKind(KindOfType::TClass) => NameType::Class,
        NameKind::TypeKind(KindOfType::TTypedef) => NameType::Typedef,
        NameKind::FunKind => NameType::Fun,
        NameKind::ConstKind => NameType::Const,
        NameKind::ModuleKind => NameType::Module,
    };
    file_info::name_type_to_enum(name_type)
}

/// `Naming_types.name_kind_of_enum`
pub fn name_kind_of_enum(i: isize) -> Option<NameKind> {
    file_info::name_type_of_enum(i).map(|name_type| match name_type {
        NameType::Class => NameKind::TypeKind(KindOfType::TClass),
        NameType::Typedef => NameKind::TypeKind(KindOfType::TTypedef),
        NameType::Fun => NameKind::FunKind,
        NameType::Const => NameKind::ConstKind,
        NameType::Module => NameKind::ModuleKind,
    })
}

/// `Naming_types.pp_name_kind` (`[@@deriving show]`)
fn pp_name_kind(fmt: &mut Formatter, k: &NameKind) {
    match k {
        NameKind::TypeKind(t) => pp_constr1(fmt, "Naming_types.Type_kind", |fmt| {
            format::pp_print_string(
                fmt,
                match t {
                    KindOfType::TClass => "Naming_types.TClass",
                    KindOfType::TTypedef => "Naming_types.TTypedef",
                },
            )
        }),
        NameKind::FunKind => format::pp_print_string(fmt, "Naming_types.Fun_kind"),
        NameKind::ConstKind => format::pp_print_string(fmt, "Naming_types.Const_kind"),
        NameKind::ModuleKind => format::pp_print_string(fmt, "Naming_types.Module_kind"),
    }
}

// ---------------------------------------------------------------------------
// The printers of `[@@deriving show]`
// ---------------------------------------------------------------------------

/// `Format.fprintf fmt "%LdL"`
fn pp_int64(fmt: &mut Formatter, n: i64) {
    format::pp_print_string(fmt, &format!("{}L", n))
}

/// `"@[<2>["`, the elements separated by `";@ "`, `"@,]@]"`.
fn pp_list<A>(fmt: &mut Formatter, l: &[A], pp: impl Fn(&mut Formatter, &A)) {
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "[");
    let mut sep = false;
    for x in l {
        if sep {
            format::pp_print_string(fmt, ";");
            format::pp_print_space(fmt);
        }
        pp(fmt, x);
        sep = true;
    }
    format::pp_print_cut(fmt);
    format::pp_print_string(fmt, "]");
    format::pp_close_box(fmt);
}

/// `"@[<2>{ "`, the fields separated by `";@ "`, `"@ }@]"`; a field is
/// `"@[%s =@ "`, its value, `"@]"`.
fn pp_record(fmt: &mut Formatter, fields: &[(&str, &dyn Fn(&mut Formatter))]) {
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "{ ");
    for (i, (name, pp_value)) in fields.iter().enumerate() {
        if i > 0 {
            format::pp_print_string(fmt, ";");
            format::pp_print_space(fmt);
        }
        format::pp_open_box(fmt, 0);
        format::pp_print_string(fmt, name);
        format::pp_print_string(fmt, " =");
        format::pp_print_space(fmt);
        pp_value(fmt);
        format::pp_close_box(fmt);
    }
    format::pp_print_space(fmt);
    format::pp_print_string(fmt, "}");
    format::pp_close_box(fmt);
}

/// `"(@[<2>Name@ "`, the argument, `"@])"`.
fn pp_constr1(fmt: &mut Formatter, name: &str, pp_arg: impl FnOnce(&mut Formatter)) {
    format::pp_print_string(fmt, "(");
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, name);
    format::pp_print_space(fmt);
    pp_arg(fmt);
    format::pp_close_box(fmt);
    format::pp_print_string(fmt, ")");
}

// ---------------------------------------------------------------------------
// The cached connection
// ---------------------------------------------------------------------------

/// Bumped by [`free_db_cache`]: a thread whose cache is older drops it.
static DB_CACHE_GENERATION: AtomicU64 = AtomicU64::new(0);

thread_local! {
    /// `db_cache`: `Not_yet_cached` is `None`; `Cached (Some ...)` is the
    /// path and its connection, with the generation it was opened in.
    static DB_CACHE: RefCell<Option<(DbPath, Connection, u64)>> = const { RefCell::new(None) };
}

pub fn open_db(DbPath(path): &DbPath) -> Result<Connection> {
    let db = Connection::open(path).map_err(sqlite3_error)?;
    exec(&db, "PRAGMA synchronous = OFF;")?;
    exec(&db, "PRAGMA journal_mode = MEMORY;")?;
    Ok(db)
}

/// `get_db_and_stmt_cache`: runs `f` on the cached connection of `path`,
/// opening it first if the cache holds another path (or none).
fn with_db<A>(path: &DbPath, f: impl FnOnce(&Connection) -> Result<A>) -> Result<A> {
    DB_CACHE.with(|cache| {
        let generation = DB_CACHE_GENERATION.load(Ordering::SeqCst);
        let mut cache = cache.borrow_mut();
        let cached = matches!(
            &*cache,
            Some((existing_path, _, g)) if equal_db_path(path, existing_path) && *g == generation
        );
        if !cached {
            *cache = None;
            let db = open_db(path)?;
            *cache = Some((path.clone(), db, generation));
        }
        let (_, db, _) = cache.as_ref().unwrap();
        f(db)
    })
}

pub fn validate_can_open_db(db_path: &DbPath) -> Result<()> {
    // sqlite is entirely happy opening a non-existent file;
    // all it does is touches the file (giving it zero size) and
    // reports that the file doesn't contain any tables. Here
    // we catch the zero-size case as well as the file-not-found
    // case, so we're robust against accidental sqlite touching
    // prior to this function.
    let DbPath(path) = db_path;
    let exists = match std::fs::metadata(path) {
        Ok(stat) => stat.len() > 0,
        Err(e) => {
            hh_logger::log(&format!(
                "opening naming-table sqlite: {}",
                unix_error_to_string(&e, "stat", path)
            ));
            false
        }
    };
    if !exists {
        return Err(Error::Failure(
            "naming-table sqlite absent or empty".to_string(),
        ));
    }
    with_db(db_path, |_| Ok(()))
}

/// `Exn.to_string` (Core) of the `Unix.Unix_error` that `Unix.stat` raises:
/// `("Unix.Unix_error(Unix.ENOENT, \"stat\", \"/path\")")`.
fn unix_error_to_string(e: &std::io::Error, fn_: &str, arg: &str) -> String {
    format!(
        "({})",
        sexp_atom(&crate::rt::ocaml_unix::unix_error_to_string(e, fn_, arg))
    )
}

/// An atom of `Sexp.to_string_hum`: quoted when it has to be.
fn sexp_atom(s: &str) -> String {
    let needs_quotes = s.is_empty()
        || s
            .bytes()
            .any(|c| matches!(c, b' ' | b'"' | b'(' | b')' | b';' | b'\\') || !(b'!'..=b'~').contains(&c));
    if needs_quotes {
        sprintf_S(s)
    } else {
        s.to_string()
    }
}

pub fn free_db_cache() {
    DB_CACHE_GENERATION.fetch_add(1, Ordering::SeqCst);
    DB_CACHE.with(|cache| *cache.borrow_mut() = None);
}

// ---------------------------------------------------------------------------
// Saving
// ---------------------------------------------------------------------------

fn save_file_info(
    db: &Connection,
    relative_path: &RelativePath,
    checksum: i64,
    file_info: &file_info::T,
) -> Result<SaveResult> {
    let file_info::FileInfo {
        file_mode,
        position_free_decl_hash,
        comments: _,
        ids:
            file_info::Ids {
                classes,
                funs,
                typedefs,
                modules,
                consts,
            },
    } = file_info;
    file_info_table::insert(
        db,
        relative_path,
        *file_mode,
        position_free_decl_hash.0,
        classes,
        consts,
        funs,
        typedefs,
        modules,
    )?;
    // `SELECT last_insert_rowid()`
    let file_info_id = db.last_insert_rowid();
    let insert = |name_kind: NameKind,
                  dep_ctor: &dyn Fn(String) -> dep::Variant,
                  (symbols_inserted, mut errors, checksum): (isize, Vec<InsertionError>, i64),
                  file_info: &file_info::Id|
     -> (isize, Vec<InsertionError>, i64) {
        let file_info::Id {
            pos: _,
            name,
            decl_hash,
        } = file_info;
        let hash = dep::to_int64(dep::make(&dep_ctor(name.clone())));
        let canon_hash = dep::to_int64(dep::make(&dep_ctor(to_canon_name_key(name))));
        match decl_hash {
            None => {
                let origin_exception =
                    exception::wrap(Error::Failure("Missing declaration hash".to_string()));
                let error = InsertionError {
                    canon_hash,
                    hash,
                    name_kind,
                    name: name.clone(),
                    origin_exception,
                };
                // `error :: errors`
                errors.push(error);
                (symbols_inserted, errors, checksum)
            }
            Some(decl_hash) => {
                let checksum = checksum_addremove(checksum, hash, *decl_hash, relative_path);
                match symbol_table::insert(
                    db,
                    name,
                    hash,
                    canon_hash,
                    &name_kind,
                    file_info_id,
                    *decl_hash,
                ) {
                    Ok(()) => (symbols_inserted + 1, errors, checksum),
                    Err(error) => {
                        errors.push(error);
                        (symbols_inserted, errors, checksum)
                    }
                }
            }
        }
    };
    let mut results = (0, vec![], checksum);
    for id in funs {
        results = insert(NameKind::FunKind, &dep::Variant::Fun, results, id);
    }
    for id in classes {
        results = insert(
            NameKind::TypeKind(KindOfType::TClass),
            &dep::Variant::Type,
            results,
            id,
        );
    }
    for id in typedefs {
        results = insert(
            NameKind::TypeKind(KindOfType::TTypedef),
            &dep::Variant::Type,
            results,
            id,
        );
    }
    for id in consts {
        results = insert(NameKind::ConstKind, &dep::Variant::GConst, results, id);
    }
    for id in modules {
        results = insert(NameKind::ModuleKind, &dep::Variant::Module, results, id);
    }
    let (symbols_added, mut errors, checksum) = results;
    // The OCaml conses each error onto the list.
    errors.reverse();
    Ok(SaveResult {
        files_added: 1,
        symbols_added,
        errors,
        checksum,
    })
}

/// The accumulation of the per-file results in `save_file_infos` and
/// `copy_and_update`: `errors = List.rev_append acc.errors per_file.errors`.
fn add_per_file(acc: SaveResult, per_file: SaveResult) -> SaveResult {
    let mut errors = acc.errors;
    errors.reverse();
    errors.extend(per_file.errors);
    SaveResult {
        files_added: acc.files_added + per_file.files_added,
        symbols_added: acc.symbols_added + per_file.symbols_added,
        errors,
        checksum: per_file.checksum,
    }
}

pub fn save_file_infos(
    db_name: &str,
    file_info_map: &relative_path::map::T<file_info::T>,
    base_content_version: &str,
) -> Result<SaveResult> {
    let db = Connection::open(db_name).map_err(sqlite3_error)?;
    exec(&db, "BEGIN TRANSACTION;")?;
    let body = || -> Result<SaveResult> {
        exec(&db, &local_changes::create_table_sqlite())?;
        exec(&db, &file_info_table::create_table_sqlite())?;
        exec(&db, &symbol_table::create_table_sqlite())?;
        exec(&db, checksum_table::CREATE_TABLE_SQLITE)?;

        // Incremental updates only update the single row in this table, so we need
        // to write in some dummy data to start.
        local_changes::prime(&db, base_content_version)?;
        let mut save_result = empty_save_result(0);
        for (path, file_info) in file_info_map.iter() {
            let per_file = save_file_info(&db, path, save_result.checksum, file_info)?;
            // (`Hack_event_logger.calling_ocaml_naming_table ()`: a no-op in OSS.)
            save_result = add_per_file(save_result, per_file);
        }
        checksum_table::set(&db, save_result.checksum)?;
        exec(&db, &file_info_table::create_index_sqlite())?;
        exec(&db, &symbol_table::create_index_sqlite())?;
        exec(&db, "END TRANSACTION;")?;
        Ok(save_result)
    };
    match body() {
        Ok(save_result) => {
            // `StatementCache.close stmt_cache`
            db.flush_prepared_statement_cache();
            if db.close().is_err() {
                return Err(Error::Failure(format!(
                    "Could not close database at {}",
                    db_name
                )));
            }
            Ok(save_result)
        }
        Err(e) => {
            exec(&db, "END TRANSACTION;")?;
            Err(e)
        }
    }
}

/// `FileUtil.cp ~force:(FileUtil.Ask (fun _ -> false)) [existing_path] new_path`:
/// copies, unless the destination exists (the answer to "overwrite?" is no).
fn file_util_cp_no_overwrite(existing_path: &str, new_path: &str) -> Result<()> {
    let dest = std::path::Path::new(new_path);
    let dest = if dest.is_dir() {
        dest.join(
            std::path::Path::new(existing_path)
                .file_name()
                .unwrap_or_default(),
        )
    } else {
        dest.to_path_buf()
    };
    if dest.exists() {
        return Ok(());
    }
    std::fs::copy(existing_path, &dest)
        .map(|_| ())
        .map_err(|e| Error::SysError(format!("{}: {}", existing_path, e)))
}

pub fn copy_and_update(
    existing_db: &DbPath,
    new_db: &DbPath,
    local_changes: &LocalChanges,
) -> Result<SaveResult> {
    let (DbPath(existing_path), DbPath(new_path)) = (existing_db, new_db);
    file_util_cp_no_overwrite(existing_path, new_path)?;
    let new_db = open_db(new_db)?;
    exec(&new_db, "BEGIN TRANSACTION;")?;
    exec(&new_db, &symbol_table::create_temporary_index_sqlite())?;

    // Our update plan is to use two phases: (1) go through every single file that has been
    // changed in any way and delete the old entries, (2) go through every file and add the
    // updated entries if any. First step is to gather from the database the FILE_INFO_ID
    // of every old file...
    let mut old_files: Vec<(RelativePath, i64)> = vec![];
    for (path, _delta) in local_changes.file_deltas.iter() {
        if let Some(file_info_id) = file_info_table::get_file_info_id(&new_db, path)? {
            old_files.push((path.clone(), file_info_id));
        }
    }

    // Checksum: phase 1 is to remove from the checksum every item which used to be
    // there in the old entries. We've read the forward-naming-table to read which symbols
    // used to be there, and now we read the reverse-naming-table to read what decl-hashes they used to have.
    // This has to be done before any of those old symbols have yet been removed!
    let mut checksum = checksum_table::get(&new_db)?;
    for (path, file_info_id) in &old_files {
        let symbols_and_decl_hashes =
            symbol_table::get_symbols_and_decl_hashes_for_file_id(&new_db, *file_info_id)?;
        for SymbolAndDeclHash { symbol, decl_hash } in symbols_and_decl_hashes {
            checksum = checksum_addremove(checksum, symbol, decl_hash, path);
        }
    }

    // Symbols: phase 1 is to remove from forward and reverse naming table every symbol
    // which used to be there. Our strategy here is to read the forward-naming-table to learn
    // the FILE_INFO_ID, and then bulk delete all entries from the reverse-naming-table which
    // have this same FILE_INFO_ID. (The reverse table isn't indexed by FILE_INFO_ID, which is
    // why we had to create a temporary index for it. It would have been more efficient to
    // get ToplevelSymbolHash from the forward naming table and remove by that, since the reverse
    // naming table is already indexed by ToplevelSymbolHash.
    for (path, file_info_id) in &old_files {
        symbol_table::delete(&new_db, *file_info_id)?;
        file_info_table::delete(&new_db, path)?;
    }

    // Symbols: phase 2 is to add forward and reverse entries for every item in file_deltas.
    // Note: if we tried to combine phases 1 and 2, then in the case of symbol X being moved from
    // b.php to a.php, we might have done local-change b.php first and tried to add X->b.php,
    // even before X->a.php had been deleted. That would have lead to a duplicate primary key violation.
    // By doing it in two phases we avoid that problem. (Of course if someone adds a duplicate entry
    // then that truly will result in a duplicate primary key violation.)
    //
    // Checksum: phase 2 is to add to the checksum every symbol in file_deltas. This would give
    // incorrect answers in case of duplicate symbol definitions (since the checksum is only meant
    // to include the winner) but symbols phase 2 would already have already raised a sqlite
    // duplicate violation if there were any duplicate symbol definitions.
    let mut result = empty_save_result(checksum);
    for (path, file_info) in local_changes.file_deltas.iter() {
        match file_info {
            ForwardNamingTableDelta::Deleted => {}
            ForwardNamingTableDelta::Modified(file_info) => {
                let per_file = save_file_info(&new_db, path, result.checksum, file_info)?;
                result = add_per_file(result, per_file);
            }
        }
    }
    checksum_table::set(&new_db, result.checksum)?;
    exec(&new_db, "END TRANSACTION;")?;
    new_db.flush_prepared_statement_cache();
    exec(&new_db, symbol_table::DROP_TEMPORARY_INDEX_SQLITE)?;
    // This reclaims space after deleting the index
    exec(&new_db, "VACUUM;")?;
    Ok(result)
}

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

pub fn get_local_changes(db_path: &DbPath) -> Result<LocalChanges> {
    with_db(db_path, local_changes::get)
}

/// `fold ?warn_on_naming_costly_iter ~db_path ~init ~f ~file_deltas`: the
/// files of the database with `file_deltas` applied, in increasing order of
/// path.
pub fn fold<A>(
    warn_on_naming_costly_iter: Option<bool>,
    db_path: &DbPath,
    init: A,
    mut f: impl FnMut(&RelativePath, &file_info::T, A) -> A,
    file_deltas: &FileDeltas,
) -> Result<A> {
    let warn_on_naming_costly_iter = warn_on_naming_costly_iter.unwrap_or(true);
    // We depend on [Relative_path.Map.bindings] returning results in increasing
    // order here.
    let sorted_changes: Vec<(&RelativePath, &ForwardNamingTableDelta<file_info::T>)> =
        file_deltas.iter().collect();
    // This function looks kind of funky, but it's not too terrible when
    // explained. We essentially have two major inputs:
    //   1. a path and file info that we got from SQLite. In order for this
    //      function to work properly, we require that consecutive invocations
    //      of this function within the same [fold] call have paths that are
    //      strictly increasing.
    //   2. the list of local changes. This list is also required to be in
    //      increasing sorted order.
    // In order to make sure that we a) return results in sorted order, and
    // b) properly handle files that have been added (and therefore will never
    // show up in the [path] and [fi] args), we essentially walk both lists in
    // sorted order (walking the SQLite list through successive invocations and
    // walking the local changes list through recursion), at each step folding
    // over whichever entry has the lowest sort order. If both paths are
    // identical, we use the one from our local changes. In this way we get O(n)
    // iteration while handling additions, modifications, and deletions
    // properly (again, given our input sorting restraints).
    let consume_sorted_changes = |path: RelativePath,
                                  fi: file_info::T,
                                  (mut next, mut acc): (usize, A)|
     -> (usize, A) {
        loop {
            match sorted_changes.get(next) {
                Some((hd_path, hd_delta)) if relative_path::compare(hd_path, &path).is_lt() => {
                    next += 1;
                    match hd_delta {
                        ForwardNamingTableDelta::Modified(local_fi) => {
                            acc = f(hd_path, local_fi, acc);
                        }
                        ForwardNamingTableDelta::Deleted => {}
                    }
                }
                Some((hd_path, hd_delta)) if relative_path::equal(hd_path, &path) => {
                    return match hd_delta {
                        ForwardNamingTableDelta::Modified(fi) => (next + 1, f(&path, fi, acc)),
                        ForwardNamingTableDelta::Deleted => (next + 1, acc),
                    };
                }
                _ => return (next, f(&path, &fi, acc)),
            }
        }
    };
    let (remaining_changes, mut acc) = with_db(db_path, |db| {
        file_info_table::fold(db, (0, init), consume_sorted_changes)
    })?;
    for (path, delta) in &sorted_changes[remaining_changes..] {
        match delta {
            ForwardNamingTableDelta::Modified(fi) => acc = f(path, fi, acc),
            // This probably shouldn't happen?
            ForwardNamingTableDelta::Deleted => {}
        }
    }
    if warn_on_naming_costly_iter {
        hh_logger::log(&format!(
            "NAMING_COSTLY_ITER\n{}",
            exception::clean_stack(&exception::get_current_callstack_string(99))
        ));
        // (`Hack_event_logger.naming_costly_iter ~start_t`: a no-op in OSS.)
    }
    Ok(acc)
}

pub fn get_file_info(db_path: &DbPath, path: &RelativePath) -> Result<Option<file_info::T>> {
    with_db(db_path, |db| file_info_table::get_file_info(db, path))
}

/// Same as `get_db_and_stmt_cache` but with logging for when opening the
/// database fails.
fn sqlite_exn_wrapped_with_db<A>(
    db_path: &DbPath,
    name: &str,
    f: impl FnOnce(&Connection) -> Result<A>,
) -> Result<A> {
    let mut opened = false;
    let r = with_db(db_path, |db| {
        opened = true;
        f(db)
    });
    match r {
        Err(Error::Sqlite3Error(msg)) if !opened => {
            hh_logger::info(
                None,
                None,
                &format!(
                    "Sqlite_db_open_bug: couldn't open the DB at `{}` while getting the position of `{}`",
                    show_db_path(db_path),
                    name
                ),
            );
            Err(Error::Sqlite3Error(msg))
        }
        r => r,
    }
}

fn get_type_wrapper(result: Option<symbol_table::Row>) -> Result<Option<(RelativePath, KindOfType)>> {
    match result {
        None => Ok(None),
        Some((filename, NameKind::TypeKind(kind_of_type), _, _)) => Ok(Some((filename, kind_of_type))),
        Some(_) => Err(Error::Failure("wrong symbol kind".to_string())),
    }
}

fn get_fun_wrapper(result: Option<symbol_table::Row>) -> Result<Option<RelativePath>> {
    match result {
        None => Ok(None),
        Some((filename, NameKind::FunKind, _, _)) => Ok(Some(filename)),
        Some(_) => Err(Error::Failure("wrong symbol kind".to_string())),
    }
}

fn get_const_wrapper(result: Option<symbol_table::Row>) -> Result<Option<RelativePath>> {
    match result {
        None => Ok(None),
        Some((filename, NameKind::ConstKind, _, _)) => Ok(Some(filename)),
        Some(_) => Err(Error::Failure("wrong symbol kind".to_string())),
    }
}

fn get_module_wrapper(result: Option<symbol_table::Row>) -> Result<Option<RelativePath>> {
    match result {
        None => Ok(None),
        Some((filename, NameKind::ModuleKind, _, _)) => Ok(Some(filename)),
        Some(_) => Err(Error::Failure("wrong symbol kind".to_string())),
    }
}

fn get_decl_hash_wrapper(result: Option<symbol_table::Row>) -> Option<String> {
    result.map(|(_, _, decl_hash, _)| decl_hash)
}

fn get_file_hash_wrapper(result: Option<symbol_table::Row>) -> Option<(RelativePath, String)> {
    result.map(|(path, _, _, file_hash)| (path, file_hash))
}

pub fn get_type_path_by_name(
    db_path: &DbPath,
    name: &str,
) -> Result<Option<(RelativePath, KindOfType)>> {
    let row = sqlite_exn_wrapped_with_db(db_path, name, |db| {
        symbol_table::get(
            db,
            dep::make(&dep::Variant::Type(name.to_string())),
            &symbol_table::get_sqlite(),
        )
    })?;
    get_type_wrapper(row)
}

pub fn get_itype_path_by_name(
    db_path: &DbPath,
    name: &str,
) -> Result<Option<(RelativePath, KindOfType)>> {
    let row = sqlite_exn_wrapped_with_db(db_path, name, |db| {
        symbol_table::get(
            db,
            dep::make(&dep::Variant::Type(name.to_ascii_lowercase())),
            &symbol_table::get_sqlite_case_insensitive(),
        )
    })?;
    get_type_wrapper(row)
}

pub fn get_fun_path_by_name(db_path: &DbPath, name: &str) -> Result<Option<RelativePath>> {
    let row = with_db(db_path, |db| {
        symbol_table::get(
            db,
            dep::make(&dep::Variant::Fun(name.to_string())),
            &symbol_table::get_sqlite(),
        )
    })?;
    get_fun_wrapper(row)
}

pub fn get_ifun_path_by_name(db_path: &DbPath, name: &str) -> Result<Option<RelativePath>> {
    let row = with_db(db_path, |db| {
        symbol_table::get(
            db,
            dep::make(&dep::Variant::Fun(name.to_ascii_lowercase())),
            &symbol_table::get_sqlite_case_insensitive(),
        )
    })?;
    get_fun_wrapper(row)
}

pub fn get_const_path_by_name(db_path: &DbPath, name: &str) -> Result<Option<RelativePath>> {
    let row = with_db(db_path, |db| {
        symbol_table::get(
            db,
            dep::make(&dep::Variant::GConst(name.to_string())),
            &symbol_table::get_sqlite(),
        )
    })?;
    get_const_wrapper(row)
}

pub fn get_module_path_by_name(db_path: &DbPath, name: &str) -> Result<Option<RelativePath>> {
    let row = with_db(db_path, |db| {
        symbol_table::get(
            db,
            dep::make(&dep::Variant::Module(name.to_string())),
            &symbol_table::get_sqlite(),
        )
    })?;
    get_module_wrapper(row)
}

pub fn get_path_by_64bit_dep(
    db_path: &DbPath,
    dep: dep::T,
) -> Result<Option<(RelativePath, NameKind)>> {
    let row = with_db(db_path, |db| {
        symbol_table::get(db, dep, &symbol_table::get_sqlite())
    })?;
    Ok(row.map(|(first, second, _, _)| (first, second)))
}

pub fn get_decl_hash_by_64bit_dep(db_path: &DbPath, dep: dep::T) -> Result<Option<String>> {
    let row = with_db(db_path, |db| {
        symbol_table::get(db, dep, &symbol_table::get_sqlite())
    })?;
    Ok(get_decl_hash_wrapper(row))
}

pub fn get_file_hash_by_64bit_dep(
    db_path: &DbPath,
    dep: dep::T,
) -> Result<Option<(RelativePath, String)>> {
    let row = with_db(db_path, |db| {
        symbol_table::get(db, dep, &symbol_table::get_sqlite())
    })?;
    Ok(get_file_hash_wrapper(row))
}

#[cfg(test)]
mod tests;
