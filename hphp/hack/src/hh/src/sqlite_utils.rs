// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/sqlite/sqlite_utils.ml`: the functions that the ported
//! modules need so far (`check_rc`, `StatementCache`, `Data_shorthands`; add
//! the others as they are needed). See `hh/PORTING.md`.
//!
//! The OCaml binding `Sqlite3` is `rusqlite` here:
//!
//! | OCaml | Rust |
//! |---|---|
//! | `Sqlite3.db` | `rusqlite::Connection` |
//! | `Sqlite3.stmt` | `rusqlite::Statement` (`CachedStatement`) |
//! | `Sqlite3.Data.t` | `rusqlite::types::Value` |
//! | the `Sqlite3.Rc.t` an operation returns | its `rusqlite::Result` |
//!
//! `rusqlite` reports `OK` and `DONE` as `Ok`, and every other result code
//! as an `Err`: that is the test of `check_rc`.

use rusqlite::Connection;

/// `Sqlite3.Rc.to_string` of the (primary) result code `rc`.
fn rc_to_string(rc: i32) -> String {
    let s = match rc {
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
        // (sic: the binding's spelling of `NOFLS`)
        22 => "NOLFS",
        23 => "AUTH",
        24 => "FORMAT",
        25 => "RANGE",
        26 => "NOTADB",
        100 => "ROW",
        101 => "DONE",
        n => return format!("UNKNOWN {}", n),
    };
    s.to_string()
}

/// The result code and the message (`Sqlite3.errmsg`) of an error that
/// SQLite reported: the message `rusqlite` read from the connection when the
/// call failed. `rusqlite` enables the extended result codes: their low byte
/// is the primary code, which is what the OCaml binding sees. (A query that
/// does not compile is a `SqlInputError`, which also has the offset of the
/// faulty token.) `None` for the errors that `rusqlite` reports without
/// calling SQLite.
fn sqlite_error(error: &rusqlite::Error) -> Option<(i32, String)> {
    match error {
        rusqlite::Error::SqliteFailure(error, msg) => Some((
            error.extended_code & 0xff,
            match msg {
                Some(msg) => msg.clone(),
                None => error.to_string(),
            },
        )),
        rusqlite::Error::SqlInputError { error, msg, .. } => {
            Some((error.extended_code & 0xff, msg.clone()))
        }
        _ => None,
    }
}

/// Check a sqlite result, and crash if it is invalid
///
/// (`Sqlite3.errmsg db` is the message that `rusqlite` read from `db` when
/// the operation failed, kept in the error.)
pub fn check_rc<T>(_db: &Connection, rc: rusqlite::Result<T>) -> T {
    match rc {
        Ok(x) => x,
        Err(error) => match sqlite_error(&error) {
            Some((rc, errmsg)) => {
                panic!("SQLite operation failed: {} ({})", rc_to_string(rc), errmsg)
            }
            // Not an error of SQLite: it has no result code.
            None => panic!("SQLite operation failed: {}", error),
        },
    }
}

/// The message of the `Sqlite3.Error` that the binding raises (`Sqlite3.<loc>:
/// <errmsg>` for a call that SQLite failed).
fn sqlite3_error_message(loc: &str, error: &rusqlite::Error) -> String {
    match sqlite_error(error) {
        Some((_rc, errmsg)) => format!("Sqlite3.{}: {}", loc, errmsg),
        None => format!("Sqlite3.{}: {}", loc, error),
    }
}

pub mod statement_cache {
    use rusqlite::CachedStatement;
    use rusqlite::Connection;

    /// `StatementCache.t`. The table of the prepared statements by query
    /// (`statements`) is the cache that `rusqlite` keeps in the connection
    /// (`Connection::prepare_cached`).
    pub struct T {
        pub db: Connection,
    }

    /// `make ~db`
    pub fn make(db: Connection) -> T {
        T { db }
    }

    /// Prepared statements must be finalized before we can close the
    /// database connection, or else an exception is thrown. Call this
    /// function before attempting `Sqlite3.close_db`.
    ///
    /// (`rusqlite` finalizes the statements it drops from its cache, and
    /// ignores what `sqlite3_finalize` returns: it returns the error of the
    /// last step of the statement, which `check_rc` has already reported.)
    pub fn close(t: &T) {
        t.db.flush_prepared_statement_cache()
    }

    /// The statement of `query`, prepared the first time.
    ///
    /// Clear any previous bindings for prepared statement parameters.
    /// (`Sqlite3.reset stmt |> check_rc t.db`: a statement that comes out of
    /// the cache of `rusqlite` has been reset, and its bindings cleared.)
    ///
    /// `Sqlite3.prepare` raises `Sqlite3.Error` when the query does not
    /// compile.
    pub fn make_stmt<'a>(t: &'a T, query: &str) -> CachedStatement<'a> {
        match t.db.prepare_cached(query) {
            Ok(stmt) => stmt,
            Err(error) => panic!("{}", super::sqlite3_error_message("prepare", &error)),
        }
    }
}

pub mod data_shorthands {
    use rusqlite::types::Value;

    /// `Sqlite3.Data.opt_text`
    pub fn opt_text(s: Option<String>) -> Value {
        match s {
            None => Value::Null,
            Some(s) => Value::Text(s),
        }
    }

    /// `Sqlite3.Data.opt_int`
    pub fn opt_int(i: Option<isize>) -> Value {
        match i {
            None => Value::Null,
            Some(i) => Value::Integer(i as i64),
        }
    }

    /// `Sqlite3.Data.opt_bool`
    pub fn opt_bool(b: Option<bool>) -> Value {
        match b {
            None => Value::Null,
            Some(b) => Value::Integer(if b { 1 } else { 0 }),
        }
    }

    pub fn text(s: String) -> Value {
        opt_text(Some(s))
    }

    pub fn int(i: isize) -> Value {
        opt_int(Some(i))
    }

    pub fn bool(b: bool) -> Value {
        opt_bool(Some(b))
    }
}

#[cfg(test)]
mod tests {
    use rusqlite::types::Value;

    use super::*;

    #[test]
    fn shorthands() {
        assert_eq!(
            data_shorthands::text("a".to_string()),
            Value::Text("a".to_string())
        );
        assert_eq!(data_shorthands::opt_text(None), Value::Null);
        assert_eq!(data_shorthands::int(-3), Value::Integer(-3));
        assert_eq!(data_shorthands::opt_int(None), Value::Null);
        assert_eq!(data_shorthands::bool(true), Value::Integer(1));
        assert_eq!(data_shorthands::bool(false), Value::Integer(0));
        assert_eq!(data_shorthands::opt_bool(None), Value::Null);
    }

    #[test]
    fn statements_are_cached_and_checked() {
        let db = Connection::open_in_memory().unwrap();
        check_rc(&db, db.execute_batch("CREATE TABLE t(x INTEGER);"));
        let cache = statement_cache::make(db);
        for i in 0..3 {
            let mut stmt = statement_cache::make_stmt(&cache, "INSERT INTO t(x) VALUES (?)");
            check_rc(
                &cache.db,
                stmt.raw_bind_parameter(1, data_shorthands::int(i)),
            );
            check_rc(&cache.db, stmt.raw_execute());
        }
        let n: i64 = cache
            .db
            .query_row("SELECT COUNT(*) FROM t", [], |row| row.get(0))
            .unwrap();
        assert_eq!(n, 3);
        statement_cache::close(&cache);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_rc(
                &cache.db,
                cache.db.execute_batch("INSERT INTO nope VALUES (1);"),
            )
        }));
        let message = match result {
            Err(payload) => payload.downcast::<String>().map(|s| *s).unwrap_or_default(),
            Ok(()) => panic!("the insert should fail"),
        };
        assert_eq!(
            message,
            "SQLite operation failed: ERROR (no such table: nope)"
        );
    }
}
