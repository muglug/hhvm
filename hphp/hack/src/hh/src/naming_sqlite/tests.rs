// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Tests of `naming_sqlite`.
//!
//! The unit tests write and read databases in a temporary directory. The
//! `#[ignore]`d tests check databases written by the OCaml `hh_server
//! --check --save-naming FILE` (the oracle); run them with
//! `HH_SS1_OCAML_DB=<db> cargo test ... naming_sqlite -- --ignored`:
//! they read every row of the OCaml's database through this module, compare
//! every lookup with what the rows say, recompute the OCaml's checksum,
//! rewrite the same file infos with `save_file_infos` and compare the table
//! contents with the OCaml's, and read our database with the crate `names`
//! (`hh_naming_table_builder`'s reader).

use std::collections::BTreeMap;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Once;

use super::*;

fn setup_prefixes() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        // Keep what another test set; only fill in the missing ones.
        for (prefix, dir) in [
            (Prefix::Root, "/tmp/hh-ss1-test-root"),
            (Prefix::Hhi, "/tmp/hh-ss1-test-hhi"),
            (Prefix::Tmp, "/tmp/hh-ss1-test-tmp"),
        ] {
            if relative_path::path_of_prefix(prefix).is_err() {
                relative_path::set_path_prefix(prefix, Path::new(dir));
            }
        }
    });
}

fn tmp_db(name: &str) -> String {
    let dir = std::env::temp_dir().join(format!("hh_naming_sqlite_tests_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let p = dir.join(name);
    let _ = std::fs::remove_file(&p);
    p.display().to_string()
}

fn rp(prefix: Prefix, s: &str) -> RelativePath {
    RelativePath::make(prefix, PathBuf::from(s))
}

fn id(path: &RelativePath, name_type: NameType, name: &str, decl_hash: Option<i64>) -> file_info::Id {
    file_info::Id {
        pos: file_info::Pos::File(name_type, Arc::new(path.clone())),
        name: name.to_string(),
        decl_hash,
    }
}

#[derive(Default)]
struct Names<'a> {
    funs: &'a [(&'a str, i64)],
    classes: &'a [(&'a str, i64)],
    typedefs: &'a [(&'a str, i64)],
    consts: &'a [(&'a str, i64)],
    modules: &'a [(&'a str, i64)],
}

fn fi(path: &RelativePath, decl_hash: Option<i64>, names: Names<'_>) -> file_info::T {
    let ids = |l: &[(&str, i64)], t| l.iter().map(|(n, h)| id(path, t, n, Some(*h))).collect();
    file_info::FileInfo {
        position_free_decl_hash: file_info::HashType(decl_hash),
        file_mode: Some(file_info::Mode::Mstrict),
        ids: file_info::Ids {
            funs: ids(names.funs, NameType::Fun),
            classes: ids(names.classes, NameType::Class),
            typedefs: ids(names.typedefs, NameType::Typedef),
            consts: ids(names.consts, NameType::Const),
            modules: ids(names.modules, NameType::Module),
        },
        comments: None,
    }
}

/// The file infos as read back: `decl_hash` of the ids is `None`, and the
/// `comments` are `None`.
fn as_read_back(f: &file_info::T) -> file_info::T {
    let mut f = f.clone();
    for ids in [
        &mut f.ids.funs,
        &mut f.ids.classes,
        &mut f.ids.typedefs,
        &mut f.ids.consts,
        &mut f.ids.modules,
    ] {
        for id in ids.iter_mut() {
            id.decl_hash = None;
        }
    }
    f.comments = None;
    f
}

fn sample() -> relative_path::map::T<file_info::T> {
    let a = rp(Prefix::Root, "a.php");
    let b = rp(Prefix::Root, "b/c.php");
    let c = rp(Prefix::Root, "b-c.php");
    let h = rp(Prefix::Hhi, "builtins.hhi");
    let mut m = relative_path::map::T::new();
    m.insert(
        a.clone(),
        fi(
            &a,
            Some(11),
            Names {
                funs: &[("\\foo", 1), ("\\Bar", 2)],
                classes: &[("\\C", 3)],
                typedefs: &[("\\T", 4)],
                consts: &[("\\K", 5)],
                modules: &[("m.n", 6)],
            },
        ),
    );
    m.insert(
        b.clone(),
        fi(&b, Some(-12), Names { classes: &[("\\D", 7), ("\\E", 8)], ..Default::default() }),
    );
    m.insert(c.clone(), fi(&c, Some(13), Names::default()));
    m.insert(h.clone(), fi(&h, Some(14), Names { funs: &[("\\hh_builtin", 9)], ..Default::default() }));
    m
}

#[test]
fn empty_local_changes_blob_is_the_ocamls() {
    // `select hex(LOCAL_CHANGES) from NAMING_LOCAL_CHANGES` of a database
    // written by the OCaml (and the constant of the crate `names`).
    let hex: String = EMPTY_LOCAL_CHANGES_BLOB.iter().map(|b| format!("{:02X}", b)).collect();
    assert_eq!(hex, "8495A6BE0000000100000000000000000000000040");
}

#[test]
fn show_of_save_result_is_the_ocamls() {
    // As the OCaml printed it for a root with two duplicate classes.
    let e = |canon_hash, hash, name: &str| InsertionError {
        canon_hash,
        hash,
        name_kind: NameKind::TypeKind(KindOfType::TClass),
        name: name.to_string(),
        origin_exception: exception::wrap(Error::Failure(
            "SQLite operation failed: CONSTRAINT (UNIQUE constraint failed: NAMING_SYMBOLS.HASH)"
                .to_string(),
        )),
    };
    let r = SaveResult {
        files_added: 363,
        symbols_added: 6108,
        errors: vec![
            e(4998368293914373073, 8173476405246828177, "\\Dup"),
            e(8005251849090039537, 7434303420316301745, "\\Partial"),
        ],
        checksum: 695051280555917078,
    };
    let expected = r#"{ Naming_sqlite.files_added = 363; symbols_added = 6108;
  errors =
  [{ Naming_sqlite.canon_hash = 4998368293914373073L;
     hash = 8173476405246828177L;
     name_kind = (Naming_types.Type_kind Naming_types.TClass);
     name = "\\Dup";
     origin_exception =
     Failure("SQLite operation failed: CONSTRAINT (UNIQUE constraint failed: NAMING_SYMBOLS.HASH)")
     };
    { Naming_sqlite.canon_hash = 8005251849090039537L;
      hash = 7434303420316301745L;
      name_kind = (Naming_types.Type_kind Naming_types.TClass);
      name = "\\Partial";
      origin_exception =
      Failure("SQLite operation failed: CONSTRAINT (UNIQUE constraint failed: NAMING_SYMBOLS.HASH)")
      }
    ];
  checksum = 695051280555917078L }"#;
    assert_eq!(show_save_result(&r), expected);
    let r = SaveResult {
        files_added: 363,
        symbols_added: 6110,
        errors: vec![],
        checksum: -8002516197239558260,
    };
    assert_eq!(
        show_save_result(&r),
        "{ Naming_sqlite.files_added = 363; symbols_added = 6110; errors = [];\n  checksum = -8002516197239558260L }"
    );
    assert_eq!(show_db_path(&DbPath("/a b".into())), "(Naming_sqlite.Db_path \"/a b\")");
}

#[test]
fn save_then_read() {
    setup_prefixes();
    let path = tmp_db("save_then_read.sql");
    let m = sample();
    let r = save_file_infos(&path, &m, "1-abc").unwrap();
    assert_eq!((r.files_added, r.symbols_added, r.errors.len()), (4, 9, 0));
    let db = DbPath(path.clone());
    validate_can_open_db(&db).unwrap();
    // Forward table.
    for (p, f) in m.iter() {
        assert_eq!(get_file_info(&db, p).unwrap(), Some(as_read_back(f)));
    }
    assert_eq!(get_file_info(&db, &rp(Prefix::Root, "nope.php")).unwrap(), None);
    // Fold: every file, in order.
    let got = fold(Some(false), &db, vec![], |p, f, mut acc| {
        acc.push((p.clone(), f.clone()));
        acc
    }, &FileDeltas::new())
    .unwrap();
    let exp: Vec<_> = m.iter().map(|(p, f)| (p.clone(), as_read_back(f))).collect();
    assert_eq!(got, exp);
    // Reverse tables.
    let a = rp(Prefix::Root, "a.php");
    assert_eq!(get_fun_path_by_name(&db, "\\foo").unwrap(), Some(a.clone()));
    assert_eq!(get_fun_path_by_name(&db, "\\FOO").unwrap(), None);
    assert_eq!(get_ifun_path_by_name(&db, "\\FOO").unwrap(), Some(a.clone()));
    assert_eq!(get_ifun_path_by_name(&db, "\\bar").unwrap(), Some(a.clone()));
    assert_eq!(get_type_path_by_name(&db, "\\C").unwrap(), Some((a.clone(), KindOfType::TClass)));
    assert_eq!(get_type_path_by_name(&db, "\\T").unwrap(), Some((a.clone(), KindOfType::TTypedef)));
    assert_eq!(get_itype_path_by_name(&db, "\\t").unwrap(), Some((a.clone(), KindOfType::TTypedef)));
    assert_eq!(get_const_path_by_name(&db, "\\K").unwrap(), Some(a.clone()));
    assert_eq!(get_module_path_by_name(&db, "m.n").unwrap(), Some(a.clone()));
    assert_eq!(
        get_type_path_by_name(&db, "\\E").unwrap(),
        Some((rp(Prefix::Root, "b/c.php"), KindOfType::TClass))
    );
    assert_eq!(
        get_fun_path_by_name(&db, "\\hh_builtin").unwrap(),
        Some(rp(Prefix::Hhi, "builtins.hhi"))
    );
    // A symbol of another kind: "wrong symbol kind" (`\K` is a const, and
    // types and funs hash differently, so look a fun up as a fun by dep).
    let dep_k = dep::make(&dep::Variant::GConst("\\K".into()));
    assert_eq!(
        get_path_by_64bit_dep(&db, dep_k).unwrap(),
        Some((a.clone(), NameKind::ConstKind))
    );
    assert_eq!(get_decl_hash_by_64bit_dep(&db, dep_k).unwrap(), Some("5".to_string()));
    assert_eq!(get_file_hash_by_64bit_dep(&db, dep_k).unwrap(), Some((a.clone(), String::new())));
    assert_eq!(
        get_path_by_64bit_dep(&db, dep::make(&dep::Variant::Fun("\\nope".into()))).unwrap(),
        None
    );
    // Local changes.
    let lc = get_local_changes(&db).unwrap();
    assert_eq!(lc.base_content_version, "1-abc");
    assert!(lc.file_deltas.is_empty());
    // Checksum: the XOR of every symbol.
    let mut checksum = 0;
    for (p, f) in m.iter() {
        for (ids, ctor) in [
            (&f.ids.funs, dep::Variant::Fun as fn(String) -> dep::Variant),
            (&f.ids.classes, dep::Variant::Type),
            (&f.ids.typedefs, dep::Variant::Type),
            (&f.ids.consts, dep::Variant::GConst),
            (&f.ids.modules, dep::Variant::Module),
        ] {
            for id in ids {
                let h = dep::to_int64(dep::make(&ctor(id.name.clone())));
                checksum = checksum_addremove(checksum, h, id.decl_hash.unwrap(), p);
            }
        }
    }
    assert_eq!(r.checksum, checksum);
    free_db_cache();
}

#[test]
fn errors_of_duplicates_and_missing_decl_hashes() {
    setup_prefixes();
    let path = tmp_db("dups.sql");
    let a = rp(Prefix::Root, "a.php");
    let b = rp(Prefix::Root, "b.php");
    let mut m = relative_path::map::T::new();
    m.insert(a.clone(), fi(&a, Some(1), Names { classes: &[("\\X", 1), ("\\Y", 2)], ..Default::default() }));
    let mut fb = fi(&b, Some(2), Names { classes: &[("\\X", 3), ("\\Y", 4)], funs: &[("\\f", 5)], ..Default::default() });
    fb.ids.funs[0].decl_hash = None;
    m.insert(b.clone(), fb);
    let r = save_file_infos(&path, &m, "v").unwrap();
    assert_eq!((r.files_added, r.symbols_added), (2, 2));
    // b.php: the fun first (missing hash), then X, then Y; the OCaml conses
    // them, so the list is Y, X, f.
    let names: Vec<_> = r.errors.iter().map(|e| e.name.as_str()).collect();
    assert_eq!(names, vec!["\\Y", "\\X", "\\f"]);
    assert_eq!(
        exception::get_ctor_string(&r.errors[0].origin_exception),
        "Failure(\"SQLite operation failed: CONSTRAINT (UNIQUE constraint failed: NAMING_SYMBOLS.HASH)\")"
    );
    assert_eq!(
        exception::get_ctor_string(&r.errors[2].origin_exception),
        "Failure(\"Missing declaration hash\")"
    );
    // The winner is the first file.
    let db = DbPath(path);
    assert_eq!(get_type_path_by_name(&db, "\\X").unwrap(), Some((a, KindOfType::TClass)));
    free_db_cache();
}

#[test]
fn validate() {
    let missing = tmp_db("missing.sql");
    assert_eq!(
        validate_can_open_db(&DbPath(missing.clone())),
        Err(Error::Failure("naming-table sqlite absent or empty".into()))
    );
    std::fs::write(&missing, "").unwrap();
    assert_eq!(
        validate_can_open_db(&DbPath(missing)),
        Err(Error::Failure("naming-table sqlite absent or empty".into()))
    );
    assert_eq!(
        unix_error_to_string(
            &std::io::Error::from_raw_os_error(libc::ENOENT),
            "stat",
            "/x/y.sql"
        ),
        r#"("Unix.Unix_error(Unix.ENOENT, \"stat\", \"/x/y.sql\")")"#
    );
}

#[test]
fn copy_and_update_then_fold_with_deltas() {
    setup_prefixes();
    let base = tmp_db("base.sql");
    let new = tmp_db("new.sql");
    let m = sample();
    save_file_infos(&base, &m, "base-version").unwrap();
    let a = rp(Prefix::Root, "a.php");
    let b = rp(Prefix::Root, "b/c.php");
    let z = rp(Prefix::Root, "z.php");
    let a0 = rp(Prefix::Root, "0.php");
    let mut deltas = FileDeltas::new();
    // `\D` moves from b/c.php to z.php; a.php loses `\Bar`; 0.php is new.
    deltas.insert(b.clone(), ForwardNamingTableDelta::Deleted);
    deltas.insert(
        z.clone(),
        ForwardNamingTableDelta::Modified(fi(&z, Some(20), Names { classes: &[("\\D", 70)], ..Default::default() })),
    );
    deltas.insert(
        a.clone(),
        ForwardNamingTableDelta::Modified(fi(
            &a,
            Some(21),
            Names {
                funs: &[("\\foo", 1)],
                classes: &[("\\C", 3)],
                typedefs: &[("\\T", 4)],
                consts: &[("\\K", 5)],
                modules: &[("m.n", 6)],
            },
        )),
    );
    deltas.insert(
        a0.clone(),
        ForwardNamingTableDelta::Modified(fi(&a0, Some(22), Names { funs: &[("\\zero", 9)], ..Default::default() })),
    );
    let lc = LocalChanges {
        file_deltas: deltas.clone(),
        base_content_version: "base-version".into(),
    };

    // Fold over the base with the deltas = the final map.
    let mut fin = m.clone();
    for (p, d) in deltas.iter() {
        match d {
            ForwardNamingTableDelta::Deleted => {
                fin.remove(p);
            }
            ForwardNamingTableDelta::Modified(f) => {
                fin.insert(p.clone(), f.clone());
            }
        }
    }
    let base_db = DbPath(base.clone());
    let got = fold(Some(false), &base_db, vec![], |p, f, mut acc| {
        acc.push((p.clone(), as_read_back(f)));
        acc
    }, &deltas)
    .unwrap();
    let exp: Vec<_> = fin.iter().map(|(p, f)| (p.clone(), as_read_back(f))).collect();
    assert_eq!(got, exp);

    let r = copy_and_update(&base_db, &DbPath(new.clone()), &lc).unwrap();
    assert_eq!((r.files_added, r.symbols_added, r.errors.len()), (3, 7, 0));
    // The checksum is the one of a database saved from the final map.
    let fresh = tmp_db("fresh.sql");
    let r_fresh = save_file_infos(&fresh, &fin, "x").unwrap();
    assert_eq!(r.checksum, r_fresh.checksum);
    let new_db = DbPath(new);
    assert_eq!(checksum_from(&new_db), r_fresh.checksum);
    assert_eq!(get_type_path_by_name(&new_db, "\\D").unwrap(), Some((z.clone(), KindOfType::TClass)));
    assert_eq!(get_fun_path_by_name(&new_db, "\\Bar").unwrap(), None);
    assert_eq!(get_fun_path_by_name(&new_db, "\\zero").unwrap(), Some(a0.clone()));
    assert_eq!(get_file_info(&new_db, &b).unwrap(), None);
    let got = fold(Some(false), &new_db, vec![], |p, f, mut acc| {
        acc.push((p.clone(), f.clone()));
        acc
    }, &FileDeltas::new())
    .unwrap();
    assert_eq!(got, exp);
    // The base is untouched.
    assert_eq!(get_type_path_by_name(&base_db, "\\D").unwrap(), Some((b, KindOfType::TClass)));
    free_db_cache();
}

/// A database built by the crate `names` (what `hh_naming_table_builder`
/// writes, e.g. the IDE's `<esc>.client_ide_naming_table`) reads as the
/// OCaml reads it.
#[test]
fn read_a_names_crate_database() {
    setup_prefixes();
    let path = tmp_db("names_crate.sql");
    let m = sample();
    let summaries: Vec<(RelativePath, names::FileSummary)> = m
        .iter()
        .map(|(p, f)| {
            let mut decls = vec![];
            for (ids, t) in [
                (&f.ids.funs, NameType::Fun),
                (&f.ids.classes, NameType::Class),
                (&f.ids.typedefs, NameType::Typedef),
                (&f.ids.consts, NameType::Const),
                (&f.ids.modules, NameType::Module),
            ] {
                for id in ids {
                    decls.push(names::DeclSummary {
                        name_type: t,
                        symbol: id.name.clone(),
                        hash: hh24_types::DeclHash::from_u64(id.decl_hash.unwrap() as u64),
                    });
                }
            }
            let summary = names::FileSummary {
                mode: f.file_mode,
                file_decls_hash: hh24_types::FileDeclsHash::from_u64(
                    f.position_free_decl_hash.0.unwrap() as u64,
                ),
                decls,
                file_digest: None,
            };
            (p.clone(), summary)
        })
        .collect();
    let built = names::Names::build_from_iterator(&path, summaries).unwrap();
    let db = DbPath(path.clone());
    validate_can_open_db(&db).unwrap();
    // Same checksum as ours for the same symbols.
    let ours = save_file_infos(&tmp_db("names_crate_ours.sql"), &m, "v").unwrap();
    assert_eq!(built.checksum.as_u64() as i64, ours.checksum);
    assert_eq!(checksum_from(&db), ours.checksum);
    for (p, f) in m.iter() {
        assert_eq!(get_file_info(&db, p).unwrap(), Some(as_read_back(f)));
    }
    let a = rp(Prefix::Root, "a.php");
    assert_eq!(get_ifun_path_by_name(&db, "\\BAR").unwrap(), Some(a.clone()));
    assert_eq!(get_type_path_by_name(&db, "\\T").unwrap(), Some((a.clone(), KindOfType::TTypedef)));
    // FILE_DIGEST is "" there (NULL in the OCaml's): the file hash is "" either way.
    let dep_c = dep::make(&dep::Variant::Type("\\C".into()));
    assert_eq!(get_file_hash_by_64bit_dep(&db, dep_c).unwrap(), Some((a, String::new())));
    let lc = get_local_changes(&db).unwrap();
    assert!(lc.file_deltas.is_empty());
    free_db_cache();
}

fn checksum_from(db: &DbPath) -> i64 {
    with_db(db, checksum_table::get).unwrap()
}

// ---------------------------------------------------------------------------
// Against a database written by the OCaml (`#[ignore]`: needs
// `HH_SS1_OCAML_DB`).
// ---------------------------------------------------------------------------

/// The rows of `NAMING_SYMBOLS` joined with the paths, straight from SQLite.
fn symbol_rows(path: &str) -> Vec<(i64, i64, i64, i64, i64, i64, String)> {
    let conn = Connection::open(path).unwrap();
    let mut stmt = conn
        .prepare(
            "SELECT NAMING_SYMBOLS.HASH, CANON_HASH, NAMING_SYMBOLS.DECL_HASH, FLAGS, \
             NAMING_SYMBOLS.FILE_INFO_ID, PATH_PREFIX_TYPE, PATH_SUFFIX FROM NAMING_SYMBOLS \
             LEFT JOIN NAMING_FILE_INFO ON NAMING_SYMBOLS.FILE_INFO_ID = NAMING_FILE_INFO.FILE_INFO_ID \
             ORDER BY NAMING_SYMBOLS.HASH",
        )
        .unwrap();
    stmt.query_map([], |r| {
        Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?, r.get(4)?, r.get(5)?, r.get(6)?))
    })
    .unwrap()
    .map(|r| r.unwrap())
    .collect()
}

/// `sqlite3 DB .dump`-like contents of the tables, in a stable order.
fn table_contents(path: &str) -> Vec<String> {
    let conn = Connection::open(path).unwrap();
    let mut out = vec![];
    for (table, order) in [
        ("NAMING_FILE_INFO", "FILE_INFO_ID"),
        ("NAMING_SYMBOLS", "HASH"),
        ("CHECKSUM", "ID"),
        ("NAMING_LOCAL_CHANGES", "ID"),
        ("sqlite_sequence", "name"),
    ] {
        let mut stmt = conn.prepare(&format!("SELECT * FROM {} ORDER BY {}", table, order)).unwrap();
        let n = stmt.column_count();
        let rows = stmt
            .query_map([], |r| {
                let mut cols = vec![];
                for i in 0..n {
                    cols.push(match r.get_ref(i)? {
                        ValueRef::Null => "NULL".to_string(),
                        ValueRef::Integer(i) => i.to_string(),
                        ValueRef::Real(f) => f.to_string(),
                        ValueRef::Text(t) => format!("'{}'", String::from_utf8_lossy(t)),
                        ValueRef::Blob(b) => format!("X'{}'", b.iter().map(|b| format!("{:02X}", b)).collect::<String>()),
                    });
                }
                Ok(cols.join("|"))
            })
            .unwrap();
        for row in rows {
            out.push(format!("{}: {}", table, row.unwrap()));
        }
    }
    let mut stmt = conn
        .prepare("SELECT type, name, tbl_name, sql FROM sqlite_master ORDER BY name")
        .unwrap();
    for row in stmt
        .query_map([], |r| {
            Ok(format!(
                "schema: {}|{}|{}|{}",
                r.get::<_, String>(0)?,
                r.get::<_, String>(1)?,
                r.get::<_, String>(2)?,
                r.get::<_, Option<String>>(3)?.unwrap_or_default()
            ))
        })
        .unwrap()
    {
        out.push(row.unwrap());
    }
    out
}

#[test]
#[ignore]
fn ocaml_database_read_compared_and_rewritten() {
    let Some(ocaml_db) = std::env::var_os("HH_SS1_OCAML_DB") else {
        eprintln!("skipped: HH_SS1_OCAML_DB is not set");
        return;
    };
    let ocaml_db = ocaml_db.to_string_lossy().into_owned();
    setup_prefixes();
    let db = DbPath(ocaml_db.clone());
    validate_can_open_db(&db).unwrap();
    let start = std::time::Instant::now();

    // 1. Every row of the reverse table, through get_path_by_64bit_dep and
    //    friends, against the row itself.
    let rows = symbol_rows(&ocaml_db);
    let mut checksum = 0i64;
    let mut decl_hash_of: BTreeMap<i64, i64> = BTreeMap::new();
    for (hash, _canon, decl_hash, flags, _id, prefix, suffix) in &rows {
        let dep = dep::T::from(depgraph_dep::Dep::new(*hash as u64));
        let p = rp(relative_path::prefix_of_enum(*prefix as isize).unwrap(), suffix);
        let kind = name_kind_of_enum(*flags as isize).unwrap();
        assert_eq!(get_path_by_64bit_dep(&db, dep).unwrap(), Some((p.clone(), kind)));
        assert_eq!(get_decl_hash_by_64bit_dep(&db, dep).unwrap(), Some(decl_hash.to_string()));
        assert_eq!(get_file_hash_by_64bit_dep(&db, dep).unwrap(), Some((p.clone(), String::new())));
        checksum = checksum_addremove(checksum, *hash, *decl_hash, &p);
        decl_hash_of.insert(*hash, *decl_hash);
    }
    // 2. The OCaml's checksum (its FFI) is ours.
    assert_eq!(checksum_from(&db), checksum, "checksum");

    // 3. Every file of the forward table: its names, looked up by name and
    //    case-insensitively, are in this file (the OCaml's DB has no
    //    duplicates: it deletes the file when there are).
    let files = fold(Some(false), &db, vec![], |p, f, mut acc| {
        acc.push((p.clone(), f.clone()));
        acc
    }, &FileDeltas::new())
    .unwrap();
    let mut n_symbols = 0;
    let mut map = relative_path::map::T::new();
    for (p, f) in &files {
        assert_eq!(get_file_info(&db, p).unwrap().as_ref(), Some(f));
        let mut f2 = f.clone();
        let fill = |ids: &mut Vec<file_info::Id>, ctor: fn(String) -> dep::Variant| {
            for id in ids.iter_mut() {
                let h = dep::to_int64(dep::make(&ctor(id.name.clone())));
                id.decl_hash = decl_hash_of.get(&h).copied();
            }
        };
        fill(&mut f2.ids.funs, dep::Variant::Fun);
        fill(&mut f2.ids.classes, dep::Variant::Type);
        fill(&mut f2.ids.typedefs, dep::Variant::Type);
        fill(&mut f2.ids.consts, dep::Variant::GConst);
        fill(&mut f2.ids.modules, dep::Variant::Module);
        map.insert(p.clone(), f2);
        for id in &f.ids.funs {
            assert_eq!(get_fun_path_by_name(&db, &id.name).unwrap().as_ref(), Some(p), "{}", id.name);
            let ip = get_ifun_path_by_name(&db, &id.name.to_ascii_uppercase()).unwrap().unwrap();
            let names = get_file_info(&db, &ip).unwrap().unwrap().ids.funs;
            assert!(names.iter().any(|n| n.name.eq_ignore_ascii_case(&id.name)), "{}", id.name);
            n_symbols += 1;
        }
        for (ids, k) in [(&f.ids.classes, KindOfType::TClass), (&f.ids.typedefs, KindOfType::TTypedef)] {
            for id in ids {
                assert_eq!(get_type_path_by_name(&db, &id.name).unwrap(), Some((p.clone(), k)), "{}", id.name);
                let (ip, _) = get_itype_path_by_name(&db, &id.name.to_ascii_uppercase()).unwrap().unwrap();
                let fi = get_file_info(&db, &ip).unwrap().unwrap();
                assert!(
                    fi.ids.classes.iter().chain(fi.ids.typedefs.iter()).any(|n| n.name.eq_ignore_ascii_case(&id.name)),
                    "{}",
                    id.name
                );
                n_symbols += 1;
            }
        }
        for id in &f.ids.consts {
            assert_eq!(get_const_path_by_name(&db, &id.name).unwrap().as_ref(), Some(p), "{}", id.name);
            n_symbols += 1;
        }
        for id in &f.ids.modules {
            assert_eq!(get_module_path_by_name(&db, &id.name).unwrap().as_ref(), Some(p), "{}", id.name);
            n_symbols += 1;
        }
    }
    assert_eq!(n_symbols, rows.len());
    let lc = get_local_changes(&db).unwrap();
    assert!(lc.file_deltas.is_empty());
    eprintln!(
        "read {} files, {} symbols of the OCaml's database in {:?}",
        files.len(),
        rows.len(),
        start.elapsed()
    );

    // 4. Rewrite the same file infos: the tables are the OCaml's.
    let ours = std::env::var("HH_SS1_OUR_DB").unwrap_or_else(|_| tmp_db("rewritten.sql"));
    let _ = std::fs::remove_file(&ours);
    let start = std::time::Instant::now();
    let r = save_file_infos(&ours, &map, &lc.base_content_version).unwrap();
    eprintln!("wrote {} in {:?}", ours, start.elapsed());
    assert_eq!(r.errors.len(), 0);
    assert_eq!(r.checksum, checksum);
    let (theirs, mine) = (table_contents(&ocaml_db), table_contents(&ours));
    assert_eq!(theirs.len(), mine.len());
    for (a, b) in theirs.iter().zip(mine.iter()) {
        assert_eq!(a, b);
    }

    // 5. The crate `names` reads ours.
    let names = names::Names::from_file_readonly(&ours).unwrap();
    assert_eq!(names.get_checksum().unwrap().as_u64() as i64, checksum);
    for (hash, _canon, decl_hash, _flags, _id, prefix, suffix) in rows.iter().step_by(7) {
        let h = hh24_types::ToplevelSymbolHash::from_u64(*hash as u64);
        let (p, _) = names.get_filename(h).unwrap().unwrap();
        assert_eq!(p, rp(relative_path::prefix_of_enum(*prefix as isize).unwrap(), suffix));
        assert_eq!(names.get_decl_hash(h).unwrap().unwrap().as_u64() as i64, *decl_hash);
    }
    free_db_cache();
}

/// A non-empty `NAMING_LOCAL_CHANGES` blob written by OCaml 5.1.1 `Marshal`
/// (`fixtures/gen_local_changes.ml`, the layouts of this version's types),
/// with and without sharing: decoded, and encoded back to the OCaml's bytes.
#[test]
fn local_changes_blob_of_the_ocaml() {
    setup_prefixes();
    let ns: &[u8] = include_bytes!("fixtures/local_changes_ns.bin");
    let shared: &[u8] = include_bytes!("fixtures/local_changes.bin");
    let saved = |funs: &[&str], classes: &[&str], types: &[&str], consts: &[&str], modules: &[&str], hash, mode| {
        let set = |l: &[&str]| l.iter().map(|s| s.to_string()).collect();
        file_info::Saved::of_fields(
            file_info::SavedNames {
                funs: set(funs),
                classes: set(classes),
                types: set(types),
                consts: set(consts),
                modules: set(modules),
            },
            hash,
            mode,
        )
    };
    use ForwardNamingTableDelta::*;
    use file_info::Mode::*;
    // In the order the generator adds them.
    let bindings: BlobFormat = vec![
        (rp(Prefix::Root, "z.php"), Deleted),
        (
            rp(Prefix::Root, "a.php"),
            Modified(saved(&["\\f", "\\g"], &["\\A", "\\C"], &[], &[], &[], Some(1234567890123), Some(Mstrict))),
        ),
        (
            rp(Prefix::Root, "sub/b.php"),
            Modified(saved(&[], &[], &["\\T"], &["\\K"], &["m"], Some(-5), Some(Mhhi))),
        ),
        (rp(Prefix::Hhi, "x.hhi"), Modified(saved(&[], &[], &[], &[], &[], None, None))),
        (rp(Prefix::Root, "c.php"), Deleted),
        (rp(Prefix::Root, "b.php"), Modified(saved(&[], &["\\B"], &[], &[], &[], Some(i64::MAX), Some(Mstrict)))),
    ];
    let mut sorted = bindings.clone();
    sorted.sort_by(|(a, _), (b, _)| relative_path::compare(a, b));
    for blob in [ns, shared] {
        let v = ocaml_marshal::from_bytes(blob, 0).unwrap();
        assert_eq!(blob_format_of_ocaml(&v).unwrap(), sorted);
        let deltas = local_changes::file_deltas_of_blob(blob).unwrap();
        assert_eq!(deltas.len(), 6);
        match deltas.get(&rp(Prefix::Root, "a.php")).unwrap() {
            Modified(fi) => {
                assert_eq!(fi.position_free_decl_hash, file_info::HashType(Some(1234567890123)));
                assert_eq!(fi.file_mode, Some(Mstrict));
                let names: Vec<&str> = fi.ids.classes.iter().map(|id| id.name.as_str()).collect();
                assert_eq!(names, ["\\A", "\\C"]);
                assert!(matches!(&fi.ids.funs[0].pos, file_info::Pos::File(NameType::Fun, p) if **p == rp(Prefix::Root, "a.php")));
            }
            Deleted => panic!(),
        }
        assert_eq!(deltas.get(&rp(Prefix::Root, "z.php")), Some(&Deleted));
    }
    // Built as the OCaml builds it, the value marshals to the OCaml's bytes
    // (the sets are built in increasing order, as the generator does: the
    // shape of an AVL tree depends on the order of the additions).
    let ours = ocaml_marshal::to_bytes(&blob_format_to_ocaml(&bindings), &[ocaml_marshal::ExternFlag::NoSharing]).unwrap();
    assert_eq!(ours, ns);
    // A malformed blob is a Failure.
    assert!(matches!(local_changes::file_deltas_of_blob(&ns[..30]), Err(Error::Failure(_))));
}
