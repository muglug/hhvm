// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: tests of the lazy contexts. A context of the
//! `Local_memory` backend (the IDE daemon's) over the SQLite naming table of
//! a scratch tree gives the TASTs and diagnostics that the eager context
//! (`hh single`'s: every file declared) gives; the naming delta after
//! edits, additions, deletions, moves and duplicates; the cases of
//! `test/integration_ml/ide` that exercise the delta (replayed with the
//! functions the IDE daemon calls: `Naming_provider.update`,
//! `Provider_utils.invalidate_upon_file_changes`, then
//! `Tast_provider.compute_tast_and_errors_quarantined` on the opened file).

use std::path::Path;
use std::sync::Arc;
use std::sync::Mutex;

use bstr::BString;
use pos::Prefix;

use crate::ctx::Ctx;
use crate::diagnostics;
use crate::file_info;
use crate::naming_provider;
use crate::naming_table;
use crate::provider_context;
use crate::relative_path;
use crate::tast_provider;

static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

/// One test at a time (the providers' context is installed globally), on a
/// large stack.
fn run(f: impl FnOnce() + Send + 'static) {
    let _guard = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
    if let Err(e) = crate::check::run_on_large_stack("lazy_ctx test", f) {
        std::panic::resume_unwind(e)
    }
}

const ROOT: &str = "/hh_lazy_ctx_test_root";

fn path(name: &str) -> pos::RelativePath {
    pos::RelativePath::new(Prefix::Root, name)
}

fn ox(name: &str) -> relative_path::RelativePath {
    path(name).into()
}

fn tco() -> oxidized::global_options::GlobalOptions {
    crate::hh_single_type_check::make_tcopt(&Default::default())
        .unwrap()
        .tcopt
}

/// The eager context of `files` (`hh single`'s: the hhi files, the magic
/// builtins and `files`, all declared), installed.
fn eager(files: &[(&str, &str)]) -> provider_context::T {
    let root = Path::new(ROOT);
    crate::hh_single_type_check::set_path_prefixes(root);
    let mut ctx = Ctx::new(root, tco()).unwrap();
    ctx.add_magic_builtins();
    let mut paths = ctx.hhi_paths.clone();
    for (name, text) in files {
        ctx.files.set(path(name), *text);
        paths.push(path(name));
    }
    let mut stats = Default::default();
    crate::check::declare_files(&ctx, &paths, &mut stats);
    let ctx = Arc::new(ctx);
    crate::hh_single_type_check::install(&ctx);
    ctx
}

/// The file info of `file` as `Direct_decl_parser.decls_to_fileinfo` gives
/// it (with the hashes a saved naming table needs), `None` if the file has
/// no contents.
fn file_info_of(ctx: &provider_context::T, file: &relative_path::RelativePath) -> Option<file_info::T> {
    let parsed = crate::direct_decl_service::direct_decl_parse(ctx, file)?;
    Some(crate::direct_decl_service::decls_to_fileinfo(file, &parsed))
}

/// The naming table of the files of `ctx` (with the hhi files), saved to a
/// fresh database: what `hh_server --save-naming` writes.
fn naming_db(ctx: &provider_context::T, names: &[&str], db_name: &str) -> String {
    let dir = std::env::temp_dir().join(format!("hh_lazy_ctx_tests_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let db = dir.join(db_name).display().to_string();
    let _ = std::fs::remove_file(&db);
    let mut infos = relative_path::map::T::new();
    for p in ctx.hhi_paths.iter().copied().chain(names.iter().map(|n| path(n))) {
        let p: relative_path::RelativePath = p.into();
        if let Some(fi) = file_info_of(ctx, &p) {
            infos.insert(p, fi);
        }
    }
    let r = naming_table::save(&naming_table::create(infos), &db).unwrap();
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    crate::naming_sqlite::free_db_cache();
    db
}

/// A context of the `Local_memory` backend over `db`, with `files` on
/// "disk", as the IDE daemon makes it (`initialize1`, then
/// `Naming_table.load_from_sqlite`), installed; and its forward table.
fn lazy(files: &[(&str, &str)], db: &str) -> (provider_context::T, naming_table::T) {
    let root = Path::new(ROOT);
    crate::hh_single_type_check::set_path_prefixes(root);
    let mut ctx = Ctx::new_local_memory_with_defaults_for_test(root, tco()).unwrap();
    ctx.add_magic_builtins();
    for (name, text) in files {
        ctx.files.set(path(name), *text);
    }
    let ctx = Arc::new(ctx);
    let nt = naming_table::load_from_sqlite(&ctx, db).unwrap();
    crate::hh_single_type_check::install(&ctx);
    (ctx, nt)
}

fn sorted(errors: diagnostics::T) -> Vec<String> {
    diagnostics::get_sorted_diagnostic_list(None, errors)
        .iter()
        .map(|d| format!("{:?}", d))
        .collect()
}

/// The diagnostics and the TAST of `name` (with `text` as its contents) in
/// `ctx`: what the IDE daemon computes for an open file.
fn check(ctx: &provider_context::T, name: &str, text: &str) -> (Vec<String>, String) {
    crate::hh_single_type_check::install(ctx);
    let (ctx, entry) = provider_context::add_or_overwrite_entry_contents(ctx, ox(name), BString::from(text));
    let r = tast_provider::compute_tast_and_errors_quarantined(&ctx, &entry, &tast_provider::ErrorFilter::default());
    let mut defs: Vec<String> = r
        .tast
        .under_normal_assumptions
        .0
        .iter()
        .map(|d| format!("{:?}", d))
        .collect();
    defs.sort();
    (sorted(r.diagnostics), defs.join("\n"))
}

const TREE: &[(&str, &str)] = &[
    (
        "a.php",
        "<?hh
interface I { public function i(): int; }
trait T { public function t(): string { return 't'; } }
abstract class A implements I {
  const int K = 1;
  public function __construct(protected int $x) {}
  public function m(): int { return $this->x; }
  abstract public function n(): string;
}
",
    ),
    (
        "b.php",
        "<?hh
final class B extends A {
  use T;
  public function i(): int { return 2; }
  public function n(): string { return $this->t(); }
  public static function make(): B { return new B(3); }
}
function fb(): B { return B::make(); }
",
    ),
    (
        "c.php",
        "<?hh
type Pair = shape('a' => int, 'b' => string);
newtype Opaque = int;
const string GREETING = 'hello';
enum Color: int { RED = 1; GREEN = 2; }
function make_opaque(int $i): Opaque { return $i; }
",
    ),
    (
        "d.php",
        "<?hh
new module m.n {}
",
    ),
    (
        "e.php",
        "<?hh
module m.n;
function use_all(Pair $p, Color $c): string {
  $b = fb();
  $x = $b->m() + $b->i() + B::K;
  $o = make_opaque($x);
  $v = Vector { $x, $p['a'] };
  return GREETING.$p['b'].$b->n();
}
function errors(): int {
  $b = new B(1);
  undefined_fun();
  $z = new NoSuchClass();
  return fb()->n();
}
",
    ),
    (
        "sub/f.php",
        "<?hh
class F extends B {}
",
    ),
];

/// For every file of a scratch tree: the TAST and the diagnostics on a lazy
/// context over the tree's naming database are those of the eager context.
#[test]
fn lazy_context_checks_as_the_eager_one() {
    run(|| {
        let names: Vec<&str> = TREE.iter().map(|(n, _)| *n).collect();
        let eager_ctx = eager(TREE);
        let db = naming_db(&eager_ctx, &names, "tree.sql");
        let expected: Vec<(Vec<String>, String)> = TREE.iter().map(|(n, t)| check(&eager_ctx, n, t)).collect();
        // Not vacuous: e.php has errors.
        assert!(!expected[4].0.is_empty());
        let (lazy_ctx, nt) = lazy(TREE, &db);
        assert_eq!(naming_table::get_files(&nt).len(), eager_ctx.hhi_paths.len() + TREE.len());
        assert!(lazy_ctx.local_memory().is_some());
        for ((name, text), expected) in TREE.iter().zip(expected.iter()) {
            let got = check(&lazy_ctx, name, text);
            assert_eq!(&got.0, &expected.0, "diagnostics of {}", name);
            assert_eq!(&got.1, &expected.1, "TAST of {}", name);
        }
        // Again (from the caches this time).
        for ((name, text), expected) in TREE.iter().zip(expected.iter()) {
            assert_eq!(&check(&lazy_ctx, name, text), expected, "{} again", name);
        }
        // The caches are bounded and hold only what was asked for.
        let lm = lazy_ctx.local_memory().unwrap();
        let shallow = lm.shallow_decl_cache.lock().unwrap().length();
        assert!(shallow > 5 && shallow < 400, "{}", shallow);
        let t = crate::provider_backend::get_local_memory_telemetry(lm);
        let t = crate::telemetry::to_string(None, &t);
        assert!(t.contains("\"shallow_decl_cache\"") && t.contains("\"capacity\":20000"), "{}", t);
    })
}

/// The naming lookups of a lazy context: positions are `File` positions of
/// the database, entries are looked at first, canonical names.
#[test]
fn lazy_naming_lookups() {
    run(|| {
        let names: Vec<&str> = TREE.iter().map(|(n, _)| *n).collect();
        let eager_ctx = eager(TREE);
        let db = naming_db(&eager_ctx, &names, "lookups.sql");
        let (ctx, _nt) = lazy(TREE, &db);
        use oxidized::naming_types::KindOfType;
        assert_eq!(naming_provider::get_class_path(&ctx, "\\B"), Some(ox("b.php")));
        assert_eq!(naming_provider::get_typedef_path(&ctx, "\\Pair"), Some(ox("c.php")));
        assert_eq!(naming_provider::get_type_kind(&ctx, "\\Opaque"), Some(KindOfType::TTypedef));
        assert_eq!(naming_provider::get_fun_path(&ctx, "\\fb"), Some(ox("b.php")));
        assert_eq!(naming_provider::get_const_path(&ctx, "\\GREETING"), Some(ox("c.php")));
        assert_eq!(naming_provider::get_module_path(&ctx, "m.n"), Some(ox("d.php")));
        assert!(matches!(
            naming_provider::get_fun_pos(&ctx, "\\fb"),
            Some(file_info::Pos::File(file_info::NameType::Fun, _))
        ));
        assert_eq!(naming_provider::get_fun_path(&ctx, "\\FB"), None);
        assert_eq!(naming_provider::get_fun_canon_name(&ctx, "\\FB").as_deref(), Some("\\fb"));
        assert_eq!(naming_provider::get_type_canon_name(&ctx, "\\pAIR").as_deref(), Some("\\Pair"));
        assert_eq!(naming_provider::get_type_canon_name(&ctx, "\\nope"), None);
        // The hhi files are in the table too.
        assert!(naming_provider::get_class_path(&ctx, "\\HH\\Vector").is_some());
        // An entry that declares a new function, and one that drops `fb`.
        let (ctx2, _) = provider_context::add_or_overwrite_entry_contents(
            &ctx,
            ox("b.php"),
            BString::from("<?hh\nfunction fresh(): void {}\n"),
        );
        assert_eq!(naming_provider::get_fun_path(&ctx2, "\\fresh"), Some(ox("b.php")));
        assert_eq!(naming_provider::get_fun_path(&ctx2, "\\fb"), None);
        assert_eq!(naming_provider::get_fun_path(&ctx, "\\fresh"), None);
        // The delta caches what SQLite answered.
        let lm = ctx.local_memory().unwrap();
        assert!(lm.reverse_naming_table_delta.funs.lock().unwrap().contains_key("\\fb"));
        // `get_files` is not available with this backend (the OCaml fails).
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            naming_provider::get_files(&ctx, &Default::default())
        }));
        assert!(r.is_err());
    })
}

/// What `Client_ide_incremental.update_naming_tables_and_si` does to the
/// naming tables for changed files (the new contents are on "disk"), then
/// `Provider_utils.invalidate_upon_file_changes`.
fn update_files(
    ctx: &provider_context::T,
    nt: naming_table::T,
    changes: &[(&str, Option<&str>)],
) -> naming_table::T {
    let mut changed_ids = vec![];
    for (name, text) in changes {
        match text {
            Some(text) => ctx.files.set(path(name), *text),
            None => ctx.files.set(path(name), ""),
        }
        let p = ox(name);
        let new_info = match text {
            Some(_) => file_info_of(ctx, &p),
            None => None,
        };
        let old_file_info = naming_table::get_file_info(&nt, &p);
        changed_ids.push(file_info::Change {
            path: p.clone(),
            new_ids: new_info.as_ref().map(|fi| fi.ids.clone()),
            new_pfh_hash: None,
            old_ids: old_file_info.map(|fi| fi.ids),
        });
        let _ = new_info;
    }
    for change in &changed_ids {
        naming_provider::update(ctx, &change.path, change.old_ids.as_ref(), change.new_ids.as_ref());
    }
    let mut nt = nt;
    for change in &changed_ids {
        if change.old_ids.is_some() {
            nt = naming_table::remove(&nt, &change.path);
        }
    }
    let mut updates = relative_path::map::T::new();
    for (name, text) in changes {
        if text.is_some() {
            if let Some(fi) = file_info_of(ctx, &ox(name)) {
                updates.insert(ox(name), fi);
            }
        }
    }
    let nt = naming_table::update_many(&nt, &updates);
    let lm = ctx.local_memory().unwrap();
    crate::provider_utils::invalidate_upon_file_changes(ctx, lm, &changed_ids, &Default::default());
    nt
}

/// The tree with `changes` applied.
fn edited(changes: &[(&str, Option<&str>)]) -> Vec<(String, String)> {
    let mut files: Vec<(String, String)> = TREE.iter().map(|(n, t)| (n.to_string(), t.to_string())).collect();
    for (name, text) in changes {
        files.retain(|(n, _)| n != name);
        if let Some(text) = text {
            files.push((name.to_string(), text.to_string()));
        }
    }
    files.sort();
    files
}

/// Every lookup and every check of the lazy context after the changes equal
/// those of an eager context of the edited tree.
fn assert_like_eager(ctx: &provider_context::T, files: &[(String, String)], names: &[&str]) {
    let as_refs: Vec<(&str, &str)> = files.iter().map(|(n, t)| (n.as_str(), t.as_str())).collect();
    let eager_ctx = eager(&as_refs);
    for name in names {
        let class = |ctx: &provider_context::T| naming_provider::get_type_path_and_kind(ctx, name);
        assert_eq!(class(ctx), class(&eager_ctx), "type {}", name);
        let fun = |ctx: &provider_context::T| naming_provider::get_fun_path(ctx, name);
        assert_eq!(fun(ctx), fun(&eager_ctx), "fun {}", name);
        let cst = |ctx: &provider_context::T| naming_provider::get_const_path(ctx, name);
        assert_eq!(cst(ctx), cst(&eager_ctx), "const {}", name);
        let canon = |ctx: &provider_context::T| naming_provider::get_fun_canon_name(ctx, &name.to_ascii_uppercase());
        assert_eq!(canon(ctx), canon(&eager_ctx), "canon fun {}", name);
        let tcanon = |ctx: &provider_context::T| naming_provider::get_type_canon_name(ctx, &name.to_ascii_uppercase());
        assert_eq!(tcanon(ctx), tcanon(&eager_ctx), "canon type {}", name);
    }
    for (name, text) in files {
        let expected = check(&eager_ctx, name, text);
        let got = check(ctx, name, text);
        assert_eq!(got.0, expected.0, "diagnostics of {}", name);
        assert_eq!(got.1, expected.1, "TAST of {}", name);
    }
}

/// A file edited, added, deleted; a symbol moved between files; a duplicate
/// introduced and removed: the lazy context answers as an eager context
/// rebuilt from scratch.
#[test]
fn naming_delta_follows_the_edits() {
    run(|| {
        let names: Vec<&str> = TREE.iter().map(|(n, _)| *n).collect();
        let db = naming_db(&eager(TREE), &names, "delta.sql");
        let (ctx, nt) = lazy(TREE, &db);
        let probe = ["\\A", "\\B", "\\F", "\\G", "\\fb", "\\moved", "\\GREETING", "\\NEWC", "\\Pair", "\\dup", "\\Dup"];
        // Warm the caches (and the delta) first.
        for (name, text) in TREE {
            check(&ctx, name, text);
        }
        // 1. b.php edited: `fb` returns an int now, a new function `moved`.
        let b2 = "<?hh
final class B extends A {
  use T;
  public function i(): int { return 2; }
  public function n(): string { return $this->t(); }
  public static function make(): B { return new B(3); }
}
function fb(): int { return 1; }
function moved(): void {}
";
        let changes = [("b.php", Some(b2))];
        let nt = update_files(&ctx, nt, &changes);
        let mut files = edited(&changes);
        assert_like_eager(&ctx, &files, &probe);
        // 2. a file added (g.php), with a new class and constant.
        let g = "<?hh\nclass G extends F {}\nconst int NEWC = 3;\nfunction use_g(): G { return new G(1); }\n";
        let changes = [("g.php", Some(g))];
        let nt = update_files(&ctx, nt, &changes);
        files = edited_from(&files, &changes);
        assert_like_eager(&ctx, &files, &probe);
        // 3. `moved` moves from b.php to c.php.
        let c2 = format!("{}function moved(): int {{ return 2; }}\n", TREE[2].1);
        let changes = [("b.php", Some(b2.replace("function moved(): void {}\n", "").leak() as &str)), ("c.php", Some(c2.leak() as &str))];
        let nt = update_files(&ctx, nt, &changes);
        files = edited_from(&files, &changes);
        assert_like_eager(&ctx, &files, &probe);
        // 4. A duplicate introduced in a later file (the first one keeps
        // the name, as an eager context binds it), then removed.
        let h = "<?hh\nfunction dup(): void {}\nclass Dup {}\n";
        let z = "<?hh\nfunction dup(): int { return 1; }\nclass Dup { public function m(): void {} }\n";
        let changes = [("h.php", Some(h))];
        let nt = update_files(&ctx, nt, &changes);
        files = edited_from(&files, &changes);
        let changes = [("z.php", Some(z))];
        let nt = update_files(&ctx, nt, &changes);
        files = edited_from(&files, &changes);
        assert_eq!(naming_provider::get_fun_path(&ctx, "\\dup"), Some(ox("h.php")));
        assert_like_eager(&ctx, &files, &probe);
        let changes = [("z.php", None)];
        let nt = update_files(&ctx, nt, &changes);
        files = edited_from(&files, &changes);
        assert_like_eager(&ctx, &files, &probe);
        // 5. A file deleted (sub/f.php: G loses its parent).
        let changes = [("sub/f.php", None)];
        let nt = update_files(&ctx, nt, &changes);
        files = edited_from(&files, &changes);
        assert_like_eager(&ctx, &files, &probe);
        assert!(!naming_table::has_file(&nt, &ox("sub/f.php")));
        assert!(naming_table::has_file(&nt, &ox("g.php")));
    })
}

fn edited_from(files: &[(String, String)], changes: &[(&str, Option<&str>)]) -> Vec<(String, String)> {
    let mut files = files.to_vec();
    for (name, text) in changes {
        files.retain(|(n, _)| n != name);
        if let Some(text) = text {
            files.push((name.to_string(), text.to_string()));
        }
    }
    files.sort();
    files
}

/// The OCaml's delta keeps the winner of a name when a duplicate is added
/// in an earlier file (`Naming_provider.add`: the SQLite winner first, the
/// new file in the others), and its invariant failures.
#[test]
fn naming_delta_duplicates_and_invariants() {
    run(|| {
        let names: Vec<&str> = TREE.iter().map(|(n, _)| *n).collect();
        let db = naming_db(&eager(TREE), &names, "dups.sql");
        let (ctx, nt) = lazy(TREE, &db);
        use crate::provider_backend::reverse_naming_table_delta::PosOrDeleted;
        // `0.php` (before b.php) declares `fb` too: b.php keeps it.
        let changes = [("0.php", Some("<?hh\nfunction fb(): void {}\n"))];
        let nt = update_files(&ctx, nt, &changes);
        assert_eq!(naming_provider::get_fun_path(&ctx, "\\fb"), Some(ox("b.php")));
        let lm = ctx.local_memory().unwrap();
        assert_eq!(
            lm.reverse_naming_table_delta.funs.lock().unwrap().get("\\fb"),
            Some(&PosOrDeleted::Pos(
                (file_info::NameType::Fun, ox("b.php")),
                vec![(file_info::NameType::Fun, ox("0.php"))]
            ))
        );
        // b.php loses it: 0.php has it.
        let b2 = TREE[1].1.replace("function fb(): B { return B::make(); }\n", "");
        let changes = [("b.php", Some(b2.leak() as &str))];
        let nt = update_files(&ctx, nt, &changes);
        assert_eq!(naming_provider::get_fun_path(&ctx, "\\fb"), Some(ox("0.php")));
        // 0.php deleted: gone.
        let changes = [("0.php", None)];
        let _nt = update_files(&ctx, nt, &changes);
        assert_eq!(naming_provider::get_fun_path(&ctx, "\\fb"), None);
        assert_eq!(
            lm.reverse_naming_table_delta.funs.lock().unwrap().get("\\fb"),
            Some(&PosOrDeleted::Deleted)
        );
        // Removing it again: the OCaml's failure.
        let ids = file_info::Ids {
            funs: vec![file_info::Id {
                pos: file_info::Pos::File(file_info::NameType::Fun, Arc::new(ox("0.php"))),
                name: "\\fb".to_string(),
                decl_hash: None,
            }],
            ..crate::file_info::empty_ids()
        };
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            naming_provider::update(&ctx, &ox("0.php"), Some(&ids), None)
        }));
        let msg = crate::exception::get_ctor_string(&crate::exception::wrap(r.unwrap_err()));
        assert!(msg.contains("removing symbol that's already removed"), "{}", msg);
        // A name whose delta says another file: the invariant failure.
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let ids = file_info::Ids {
                classes: vec![file_info::Id {
                    pos: file_info::Pos::File(file_info::NameType::Class, Arc::new(ox("x.php"))),
                    name: "\\B".to_string(),
                    decl_hash: None,
                }],
                ..crate::file_info::empty_ids()
            };
            // (Read once so that the delta has it from SQLite.)
            let _ = naming_provider::get_class_path(&ctx, "\\B");
            naming_provider::update(&ctx, &ox("x.php"), Some(&ids), None)
        }));
        let msg = crate::exception::get_ctor_string(&crate::exception::wrap(r.unwrap_err()));
        assert!(
            msg.contains("Naming_provider invariant failed: symbol \\B was in") && msg.contains("but we're trying to remove"),
            "{}",
            msg
        );
    })
}

/// `test/integration_ml/ide/test_remove_function.ml`,
/// `test_remove_parent.ml`, `test_added_parent_ide.ml`: the naming delta and
/// the invalidation of the IDE daemon after a change on disk.
#[test]
fn integration_ml_ide_naming_cases() {
    run(|| {
        let codes = |errors: &[String]| -> Vec<String> {
            errors
                .iter()
                .map(|e| {
                    let i = e.find("code: ").unwrap();
                    e[i + 6..].split(|c: char| !c.is_ascii_digit()).next().unwrap().to_string()
                })
                .collect()
        };
        // test_remove_function
        let foo = "<?hh // strict\n\nfunction foo() : void {}\n";
        let bar = "<?hh // strict\n\nfunction test(): void {\n  foo();\n}\n";
        let tree = [("bar.php", bar), ("foo.php", foo)];
        let db = naming_db(&eager(&tree), &["bar.php", "foo.php"], "remove_function.sql");
        let (ctx, nt) = lazy(&tree, &db);
        assert_eq!(check(&ctx, "bar.php", bar).0, Vec::<String>::new());
        let _nt = update_files(&ctx, nt, &[("foo.php", Some(""))]);
        // Unbound name: `foo` (a global function) (Naming[2049]);
        // Unbound name (typing): `foo` (Typing[4107])
        assert_eq!(codes(&check(&ctx, "bar.php", bar).0), ["2049", "4107"]);

        // test_remove_parent
        let foo_parent = "<?hh // strict\n\nclass FooParent {\n  public function lol() : void {}\n}\n";
        let foo = "<?hh // strict\n\nclass Foo extends FooParent {\n  public function test() : void {\n    $this->lol();\n  }\n}\n";
        let tree = [("foo.php", foo), ("foo_parent.php", foo_parent)];
        let db = naming_db(&eager(&tree), &["foo.php", "foo_parent.php"], "remove_parent.sql");
        let (ctx, nt) = lazy(&tree, &db);
        assert_eq!(check(&ctx, "foo.php", foo).0, Vec::<String>::new());
        let nt = update_files(&ctx, nt, &[("foo_parent.php", Some(""))]);
        // Unbound name: `FooParent` (Naming[2049]); No instance method `lol` (Typing[4053])
        assert_eq!(codes(&check(&ctx, "foo.php", foo).0), ["2049", "4053"]);
        let _nt = update_files(&ctx, nt, &[("foo_parent.php", Some(foo_parent))]);
        assert_eq!(check(&ctx, "foo.php", foo).0, Vec::<String>::new());

        // test_added_parent_ide
        let foo = "<?hh // strict\n\nclass Foo {\n  /* HH_FIXME[4110] */\n  public function f() : string {\n  }\n}\n";
        let foo_child = "<?hh // strict\n\n/* HH_FIXME[2049] */\n/* HH_FIXME[4123] */\nclass FooChild extends Foo {}\n";
        let bar = "<?hh // strict\n\nfunction take_int(int $x) : void {}\n\nfunction test(FooChild $foo_child) : void {\n  take_int($foo_child->f());\n}\n";
        let tree = [("bar.php", bar), ("foo.php", ""), ("foo_child.php", foo_child)];
        let db = naming_db(&eager(&tree), &["bar.php", "foo.php", "foo_child.php"], "added_parent.sql");
        let (ctx, nt) = lazy(&tree, &db);
        // No instance method `f` in `FooChild` (Typing[4053])
        assert_eq!(codes(&check(&ctx, "bar.php", bar).0), ["4053"]);
        let _nt = update_files(&ctx, nt, &[("foo.php", Some(foo))]);
        // (Opening foo_child.php invalidates FooChild: the quarantine.)
        let _ = check(&ctx, "foo_child.php", foo_child);
        // Invalid argument (Typing[4110])
        assert_eq!(codes(&check(&ctx, "bar.php", bar).0), ["4110"]);
    })
}

/// The footprint of a lazy context over Slack's naming table after typing a
/// few hundred files through `Tast_provider`, next to the eager context's
/// (`HH_LAZY_CTX_TEST_WEBAPP=<root> HH_LAZY_CTX_TEST_DB=<db> cargo test ... lazy_ctx_tests::footprint
/// -- --ignored --nocapture`). The root must be a read-only export.
#[test]
#[ignore]
fn footprint() {
    let (Some(root), Some(db)) = (std::env::var_os("HH_LAZY_CTX_TEST_WEBAPP"), std::env::var_os("HH_LAZY_CTX_TEST_DB")) else {
        eprintln!("skipped: HH_LAZY_CTX_TEST_WEBAPP or HH_LAZY_CTX_TEST_DB is not set");
        return;
    };
    let n: usize = std::env::var("HH_LAZY_CTX_TEST_FILES").ok().and_then(|s| s.parse().ok()).unwrap_or(300);
    let root = std::path::PathBuf::from(root);
    let db = db.to_string_lossy().into_owned();
    let r = crate::check::run_on_large_stack("footprint", move || {
        let rss = || -> u64 {
            let out = std::process::Command::new("ps")
                .args(["-o", "rss=", "-p", &std::process::id().to_string()])
                .output()
                .unwrap();
            String::from_utf8_lossy(&out.stdout).trim().parse::<u64>().unwrap_or(0) * 1024
        };
        let eager_mode = std::env::var_os("HH_LAZY_CTX_TEST_EAGER").is_some();
        let (tco, _ignored) = crate::check::check_options(&root, &[]).unwrap();
        let before = rss();
        let start = std::time::Instant::now();
        let (ctx, files): (provider_context::T, Vec<relative_path::RelativePath>) = if eager_mode {
            // The eager context: every file of the root declared.
            let r = crate::check::discover_files(root.canonicalize().unwrap(), std::time::Instant::now(), tco, &_ignored).unwrap();
            crate::hh_single_type_check::set_path_prefixes(&r.root);
            let mut stats = Default::default();
            crate::check::declare_files(&r.ctx, &r.paths, &mut stats);
            let files: Vec<relative_path::RelativePath> =
                r.paths[r.hhi_count..].iter().map(|p| relative_path::RelativePath::from(*p)).collect();
            (Arc::new(r.ctx), files)
        } else {
            crate::hh_single_type_check::set_path_prefixes(&root.canonicalize().unwrap());
            let ctx = Arc::new(Ctx::new_local_memory(&root.canonicalize().unwrap(), tco, 5000, 5000, 20000).unwrap());
            let nt = naming_table::load_from_sqlite(&ctx, &db).unwrap();
            let files = naming_table::get_files(&nt)
                .into_iter()
                .filter(|p| p.prefix() == relative_path::Prefix::Root)
                .collect();
            (ctx, files)
        };
        crate::hh_single_type_check::install(&ctx);
        eprintln!(
            "{} context made in {:?}; rss +{} MB",
            if eager_mode { "eager" } else { "lazy" },
            start.elapsed(),
            (rss() - before) >> 20
        );
        let mut files: Vec<relative_path::RelativePath> = files
            .into_iter()
            .filter(|p| {
                let p = p.path().to_string_lossy();
                p.ends_with(".php") || p.ends_with(".hack")
            })
            .collect();
        files.sort_by(|a, b| relative_path::compare(a, b));
        let files: Vec<relative_path::RelativePath> = files.into_iter().step_by(97).take(n).collect();
        let start = std::time::Instant::now();
        let mut errors = 0;
        for (i, p) in files.iter().enumerate() {
            let (c, entry) = provider_context::add_entry_if_missing(&ctx, p.clone());
            let r = tast_provider::compute_tast_and_errors_quarantined(&c, &entry, &tast_provider::ErrorFilter::default());
            errors += diagnostics::get_sorted_diagnostic_list(None, r.diagnostics).len();
            if i % 50 == 49 {
                match ctx.local_memory() {
                    Some(lm) => eprintln!(
                        "{} files in {:?}: rss +{} MB; shallow {} folded {} decls {}",
                        i + 1,
                        start.elapsed(),
                        (rss() - before) >> 20,
                        lm.shallow_decl_cache.lock().unwrap().length(),
                        lm.folded_class_cache.lock().unwrap().length(),
                        lm.decl_cache.lock().unwrap().length(),
                    ),
                    None => eprintln!("{} files in {:?}: rss +{} MB", i + 1, start.elapsed(), (rss() - before) >> 20),
                }
            }
        }
        eprintln!("{} files, {} diagnostics, {:?}; rss +{} MB", files.len(), errors, start.elapsed(), (rss() - before) >> 20);
    });
    if let Err(e) = r {
        std::panic::resume_unwind(e)
    }
}

/// The `Shared_memory` lazy context (`Ctx::new_lazy`: `hh_server` after a
/// saved-state load) over the tree's database: the same checks as the
/// eager context; lookups fall back to SQLite and cache; a remove blocks.
#[test]
fn shared_memory_lazy_context() {
    run(|| {
        let names: Vec<&str> = TREE.iter().map(|(n, _)| *n).collect();
        let eager_ctx = eager(TREE);
        let db = naming_db(&eager_ctx, &names, "shared.sql");
        let expected: Vec<(Vec<String>, String)> = TREE.iter().map(|(n, t)| check(&eager_ctx, n, t)).collect();
        let root = Path::new(ROOT);
        let mut ctx = Ctx::new_lazy(root, tco(), Arc::new(crate::naming_sqlite::DbPath(db.clone()))).unwrap();
        ctx.add_magic_builtins();
        for (name, text) in TREE {
            ctx.files.set(path(name), *text);
        }
        let ctx = Arc::new(ctx);
        let nt = naming_table::load_from_sqlite(&ctx, &db).unwrap();
        crate::hh_single_type_check::install(&ctx);
        assert!(ctx.local_memory().is_none() && ctx.has_reverse_naming_table());
        let table = ctx.reverse_naming_table();
        assert!(!table.base_has_type("\\B"));
        assert!(!ctx.base_has_class_decl("\\B"));
        for ((name, text), expected) in TREE.iter().zip(expected.iter()) {
            let got = check(&ctx, name, text);
            assert_eq!(&got.0, &expected.0, "diagnostics of {}", name);
            assert_eq!(&got.1, &expected.1, "TAST of {}", name);
        }
        // (Those checks were quarantined: nothing they cached is left.)
        assert!(!table.base_has_type("\\B"));
        assert!(!ctx.base_has_class_decl("\\B"));
        // Found in SQLite, cached in the heap; decls parsed on demand.
        assert!(crate::decl_entry::to_option(crate::decl_provider::get_class(None, &ctx, "\\F")).is_some());
        assert!(table.base_has_type("\\B"));
        assert!(ctx.base_has_class_decl("\\B"));
        assert!(matches!(
            naming_provider::get_type_pos(&ctx, "\\B"),
            Some(file_info::Pos::File(file_info::NameType::Class, _))
        ));
        assert_eq!(naming_provider::get_type_canon_name(&ctx, "\\pair").as_deref(), Some("\\Pair"));
        assert_eq!(naming_provider::get_fun_canon_name(&ctx, "\\FB").as_deref(), Some("\\fb"));
        // get_files: by the heap, then SQLite.
        use crate::typing_deps::dep;
        let deps: crate::typing_deps::dep_set::T =
            [dep::make(&dep::Variant::Fun("\\make_opaque".into())), dep::make(&dep::Variant::Type("\\F".into()))]
                .into_iter()
                .collect();
        assert_eq!(naming_provider::get_files(&ctx, &deps), [ox("c.php"), ox("sub/f.php")].into_iter().collect());
        // A remove blocks the database's answer (`BlockedEntries`), the
        // canonical name too; adding again finds it.
        naming_provider::remove_fun_batch(&ctx, &["\\make_opaque".to_string()]);
        assert_eq!(naming_provider::get_fun_path(&ctx, "\\make_opaque"), None);
        assert_eq!(naming_provider::get_fun_canon_name(&ctx, "\\MAKE_OPAQUE"), None);
        assert_eq!(naming_provider::get_files(&ctx, &deps), [ox("sub/f.php")].into_iter().collect());
        let pos = file_info::Pos::File(file_info::NameType::Fun, Arc::new(ox("c.php")));
        naming_provider::add_fun(&ctx, "\\make_opaque", &pos);
        assert_eq!(naming_provider::get_fun_path(&ctx, "\\make_opaque"), Some(ox("c.php")));
        let _ = nt;
    })
}

/// A quarantine on the `Shared_memory` lazy context: what the lookups cache
/// meanwhile (the SQLite answers in the naming heap, the decls parsed from
/// the disk) goes to the local changes, which the end of the quarantine
/// drops (`Naming_heap.pop_local_changes`, the decl heaps' stacks).
#[test]
fn shared_memory_quarantine_drops_the_caches() {
    run(|| {
        let names: Vec<&str> = TREE.iter().map(|(n, _)| *n).collect();
        let db = naming_db(&eager(TREE), &names, "quarantine.sql");
        let root = Path::new(ROOT);
        let mut ctx = Ctx::new_lazy(root, tco(), Arc::new(crate::naming_sqlite::DbPath(db.clone()))).unwrap();
        ctx.add_magic_builtins();
        for (name, text) in TREE {
            ctx.files.set(path(name), *text);
        }
        let ctx = Arc::new(ctx);
        let _nt = naming_table::load_from_sqlite(&ctx, &db).unwrap();
        crate::hh_single_type_check::install(&ctx);
        let table = ctx.reverse_naming_table();
        let (ectx, entry) =
            provider_context::add_or_overwrite_entry_contents(&ctx, ox("e.php"), BString::from(TREE[4].1));
        let errors = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ectx, || {
            assert_eq!(table.local_changes_depth(), 1);
            assert_eq!(ctx.decl_local_changes_depth(), 1);
            let r = tast_provider::compute_tast_and_errors_unquarantined(&ectx, &entry, &tast_provider::ErrorFilter::default());
            // Looked up meanwhile: in the local changes, not in the heaps.
            assert!(naming_provider::get_class_path(&ctx, "\\B").is_some());
            assert!(!table.base_has_type("\\B"));
            assert!(!ctx.base_has_class_decl("\\B"));
            sorted(r.diagnostics)
        });
        assert!(!errors.is_empty());
        assert_eq!(table.local_changes_depth(), 0);
        assert_eq!(ctx.decl_local_changes_depth(), 0);
        assert!(!table.base_has_type("\\B"));
        assert!(!ctx.base_has_class_decl("\\B"));
        // Outside, the same lookups cache in the heaps.
        let (ectx, entry) =
            provider_context::add_or_overwrite_entry_contents(&ctx, ox("e.php"), BString::from(TREE[4].1));
        let r = tast_provider::compute_tast_and_errors_unquarantined(&ectx, &entry, &tast_provider::ErrorFilter::default());
        assert_eq!(sorted(r.diagnostics), errors);
        assert!(table.base_has_type("\\B"));
        assert!(ctx.base_has_class_decl("\\B"));
    })
}
