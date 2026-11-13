// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Plan §3.1 (MEMO): on one thread, check A, change the declarations of B
//! (a second `Ctx` over the same files, the stand-in for N1's
//! `Ctx::next_generation` until it lands) and bump the epoch, check A again:
//! the result must be that of a fresh thread (whose per-thread state is that
//! of a fresh process). Each case changes something that one of the
//! per-thread memos or caches would give stale; the cases marked `stale`
//! also check that, without the epoch, the thread would give the old answer
//! (so that the case does exercise a memo).
//!
//! And: with dependency edges recorded, the edges recorded with the memos
//! on are those recorded with every memo off (`HH_NO_MEMOS`).

use std::sync::Arc;
use std::sync::Mutex;

use pos::Prefix;
use pos::RelativePath;

use super::*;
use crate::ctx::Ctx;
use crate::hh_single_type_check as hstc;

/// The tests change process-wide state (the installed decl store, the
/// dependency callbacks, `trace`, `HH_NO_MEMOS`): one at a time.
static LOCK: Mutex<()> = Mutex::new(());

fn options(config: &[&str]) -> oxidized::global_options::GlobalOptions {
    let flags = hstc::Flags {
        config_overrides: config.iter().map(|s| s.to_string()).collect(),
        ..Default::default()
    };
    hstc::make_tcopt(&flags).unwrap().tcopt
}

fn path(name: &str) -> RelativePath {
    RelativePath::new(Prefix::Dummy, name)
}

/// A `Ctx` declaring the hhi files and `files`, whose contents are put in
/// `files_of` (the files of another `Ctx`, shared, as the generations of
/// one `Ctx` share them) if given.
fn make_ctx(config: &[&str], files: &[(&str, &str)], files_of: Option<&Ctx>) -> Arc<Ctx> {
    hstc::set_path_prefixes(std::path::Path::new("/"));
    let mut ctx = Ctx::new(std::path::Path::new("/"), options(config)).unwrap();
    if let Some(other) = files_of {
        ctx.files = Arc::clone(&other.files);
    }
    let mut paths = ctx.hhi_paths.clone();
    for (name, text) in files {
        ctx.files.set(path(name), *text);
        paths.push(path(name));
    }
    crate::check::declare_files(&ctx, &paths, &mut crate::check::Stats::default());
    let ctx = Arc::new(ctx);
    hstc::install(&ctx);
    ctx
}

/// What `check.rs` does for a file, printed as `hh single` prints it.
fn check(ctx: &Arc<Ctx>, name: &str) -> String {
    let fn_: relative_path::RelativePath = path(name).into();
    let (file_errors, ast) = crate::ast_provider::get_ast_with_error(true, ctx, &fn_);
    let errors = if crate::diagnostics_state::has_errors(None, &file_errors) {
        file_errors
    } else {
        crate::typing_check_job::calc_errors(ctx, Some(false), &fn_, ast)
    };
    let errors = crate::diagnostics_state::drop_fixmed_errors_in_files(errors);
    let mut out = vec![];
    hstc::write_error_list(
        crate::diagnostics_state::format_or_default(None),
        errors,
        &mut out,
        None,
    );
    String::from_utf8(out).unwrap()
}

fn on_new_thread<A: Send>(f: impl FnOnce() -> A + Send) -> A {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn_scoped(s, f)
            .unwrap()
            .join()
            .unwrap()
    })
}

struct Case {
    name: &'static str,
    config: &'static [&'static str],
    /// The files before and after the change (the checked file is `a.php`).
    before: Vec<(&'static str, &'static str)>,
    after: Vec<(&'static str, &'static str)>,
    /// Without the epoch, the thread gives the old answer.
    stale: bool,
}

/// Check `a.php`, change, check it again on the same thread (with the
/// epoch bumped if `bump`); and the check of the files after the change on
/// a fresh thread.
fn run(case: &Case, bump: bool) -> (String, String, String) {
    on_new_thread(|| {
        sync_thread();
        let ctx1 = make_ctx(case.config, &case.before, None);
        let first = check(&ctx1, "a.php");
        let ctx2 = make_ctx(case.config, &case.after, Some(&ctx1));
        if bump {
            super::bump();
        }
        sync_thread();
        let again = check(&ctx2, "a.php");
        let fresh = on_new_thread(|| {
            let ctx = make_ctx(case.config, &case.after, None);
            check(&ctx, "a.php")
        });
        (first, again, fresh)
    })
}

const SDT: &[&str] = &["everything_sdt=true"];

fn shape_alias(field_a: &str) -> String {
    let mut fields = vec![format!("'a' => {}", field_a)];
    for i in 0..30 {
        fields.push(format!("'f{}' => vec<int>", i));
    }
    format!("<?hh\ntype T = shape({});\n", fields.join(", "))
}

fn cases() -> Vec<Case> {
    let leak = |s: String| -> &'static str { Box::leak(s.into_boxed_str()) };
    let alias_before = leak(shape_alias("int"));
    let alias_after = leak(shape_alias("string"));
    vec![
        Case {
            name: "class member type",
            config: &[],
            before: vec![
                ("b.php", "<?hh\nclass C { public function m(): int { return 1; } }\n"),
                ("a.php", "<?hh\nfunction f(C $c): string { return $c->m(); }\n"),
            ],
            after: vec![
                ("b.php", "<?hh\nclass C { public function m(): string { return 's'; } }\n"),
                ("a.php", "<?hh\nfunction f(C $c): string { return $c->m(); }\n"),
            ],
            stale: false,
        },
        Case {
            // `C <: I` is answered by the subtype memos (closed types).
            name: "class ancestors (subtype ask/tell memo)",
            config: &[],
            before: vec![
                ("b.php", "<?hh\ninterface I {}\nclass C implements I {}\n"),
                (
                    "a.php",
                    "<?hh\nfunction f(C $c): I { return $c; }\nfunction g(C $c): I { return $c; }\n",
                ),
            ],
            after: vec![
                ("b.php", "<?hh\ninterface I {}\nclass C {}\n"),
                (
                    "a.php",
                    "<?hh\nfunction f(C $c): I { return $c; }\nfunction g(C $c): I { return $c; }\n",
                ),
            ],
            stale: true,
        },
        Case {
            // A big closed shape alias is kept by the alias cache's
            // `extra` tier, for the file being checked.
            name: "typedef (alias cache)",
            config: &[],
            before: vec![
                ("b.php", alias_before),
                ("a.php", "<?hh\nfunction f(T $x): int { return $x['a']; }\n"),
            ],
            after: vec![
                ("b.php", alias_after),
                ("a.php", "<?hh\nfunction f(T $x): int { return $x['a']; }\n"),
            ],
            stale: true,
        },
        Case {
            name: "function signature",
            config: &[],
            before: vec![
                ("b.php", "<?hh\nfunction g(): int { return 1; }\n"),
                ("a.php", "<?hh\nfunction f(): int { return g(); }\n"),
            ],
            after: vec![
                ("b.php", "<?hh\nfunction g(): string { return 's'; }\n"),
                ("a.php", "<?hh\nfunction f(): int { return g(); }\n"),
            ],
            stale: false,
        },
        Case {
            name: "class becomes disposable",
            config: &[],
            before: vec![
                ("b.php", "<?hh\nclass D {}\n"),
                ("a.php", "<?hh\nfunction f(): D { return new D(); }\nfunction g(): void { $d = f(); }\n"),
            ],
            after: vec![
                (
                    "b.php",
                    "<?hh\nclass D implements IDisposable { public function __dispose(): void {} }\n",
                ),
                ("a.php", "<?hh\nfunction f(): D { return new D(); }\nfunction g(): void { $d = f(); }\n"),
            ],
            stale: false,
        },
        Case {
            name: "constant",
            config: &[],
            before: vec![
                ("b.php", "<?hh\nconst int X = 1;\n"),
                ("a.php", "<?hh\nfunction f(): int { return X; }\n"),
            ],
            after: vec![
                ("b.php", "<?hh\nconst string X = 's';\n"),
                ("a.php", "<?hh\nfunction f(): int { return X; }\n"),
            ],
            stale: false,
        },
        Case {
            // `C <: dynamic` (the subtype memos and `dynamic_memo`).
            name: "class stops supporting dynamic",
            config: SDT,
            before: vec![
                ("b.php", "<?hh\nclass C {}\n"),
                (
                    "a.php",
                    "<?hh\nfunction f(C $c): dynamic { return $c; }\nfunction g(vec<C> $c): dynamic { return $c; }\n",
                ),
            ],
            after: vec![
                ("b.php", "<?hh\n<<__NoAutoDynamic>>\nclass C {}\n"),
                (
                    "a.php",
                    "<?hh\nfunction f(C $c): dynamic { return $c; }\nfunction g(vec<C> $c): dynamic { return $c; }\n",
                ),
            ],
            stale: false,
        },
        Case {
            // The checked file itself changes (its AST and fixmes, kept per
            // thread).
            name: "checked file changes",
            config: SDT,
            before: vec![("a.php", "<?hh\nfunction f(): int { return 's'; }\n")],
            after: vec![("a.php", "<?hh\nfunction f(): int { return 1; }\n")],
            stale: true,
        },
        Case {
            name: "fixme added",
            config: &[],
            before: vec![("a.php", "<?hh\nfunction f(): int {\n  return 's';\n}\n")],
            after: vec![(
                "a.php",
                "<?hh\nfunction f(): int {\n  /* HH_FIXME[4110] */\n  return 's';\n}\n",
            )],
            stale: false,
        },
    ]
}

#[test]
fn recheck_on_the_same_thread_is_a_fresh_check() {
    let _lock = LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let mut failures = vec![];
    for case in cases() {
        let (first, again, fresh) = run(&case, true);
        if first == fresh {
            failures.push(format!("{}: the change changes nothing:\n{}", case.name, fresh));
        }
        if again != fresh {
            failures.push(format!(
                "{}: after the epoch:\n{}\nfresh:\n{}",
                case.name, again, fresh
            ));
        }
        if case.stale {
            let (_, stale, fresh) = run(&case, false);
            if stale == fresh {
                failures.push(format!(
                    "{}: without the epoch the result is not stale (the case exercises no memo)",
                    case.name
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// The dependency edges recorded by the check of `a.php` (with the other
/// files declared), on a fresh thread (as hashes).
fn edges_of(
    files: &[(&str, &str)],
    no_memos: bool,
) -> std::collections::BTreeSet<crate::typing_deps::DepEdge> {
    set_no_memos(no_memos);
    let edges = on_new_thread(|| {
        sync_thread();
        let ctx = make_ctx(SDT, files, None);
        let _ = crate::typing_deps::flush_ideps_batch(&ctx.deps_mode);
        // Twice: the second check of the file finds the memos full.
        check(&ctx, "a.php");
        check(&ctx, "a.php");
        crate::typing_deps::flush_ideps_batch(&ctx.deps_mode).unwrap()
    });
    set_no_memos(false);
    edges
}

#[test]
fn memo_hits_lose_no_dependency_edge() {
    let _lock = LOCK.lock().unwrap_or_else(|e| e.into_inner());
    // Definitions that ask the same closed subtyping questions (answered
    // from the ask/tell memos and `dynamic_memo` across definitions when no
    // edge is recorded), of classes reached only through subtyping.
    let b = "<?hh
interface I {}
interface J extends I {}
class P implements J {}
class C extends P {}
<<__SupportDynamicType>> class S {}
final class Req1<TGet as shape(...), TPost as shape(...)> {}
final class Req2<TGet as shape(...), TPost as shape(...)> {}
type g_t = shape(?'redir' => string, ?'redirect' => string);
type p_t = shape();
type T = shape('a' => C, 'b' => vec<int>, 'c' => vec<int>, 'd' => vec<int>, 'e' => vec<int>,
  'f' => vec<int>, 'g' => vec<int>, 'h' => vec<int>, 'i' => vec<int>, 'j' => vec<int>, 'k' => vec<int>);
";
    let a = "<?hh
function f1(C $c): I { return $c; }
function f2(C $c): I { return $c; }
class K1 { public function m(C $c): J { return $c; } }
class K2 { public function m(C $c): J { return $c; } }
function g1(S $s): dynamic { return $s; }
function g2(S $s): dynamic { return $s; }
function h1(T $t): C { return $t['a']; }
function h2(T $t): C { return $t['a']; }
function u1(vec<C> $v): vec<I> { return $v; }
function u2(vec<C> $v): vec<I> { return $v; }
// (Found on Slack's code: without the dependent in the memos' context,
// the edge `Type A2 -> Type HH\\supportdyn` is lost.)
type A1 = Req1<g_t, p_t>;
type A2 = Req2<g_t, p_t>;
";
    let files = [("b.php", b), ("a.php", a)];
    crate::typing_deps::trace.store(true, std::sync::atomic::Ordering::Relaxed);
    let with_memos = edges_of(&files, false);
    let without = edges_of(&files, true);
    crate::typing_deps::trace.store(false, std::sync::atomic::Ordering::Relaxed);
    assert!(!with_memos.is_empty());
    let missing: Vec<_> = without.difference(&with_memos).collect();
    let extra: Vec<_> = with_memos.difference(&without).collect();
    assert!(
        missing.is_empty() && extra.is_empty(),
        "edges missing with the memos: {:#?}\nextra: {:#?}",
        missing,
        extra
    );
}

/// An entry typed inside a quarantine (P0's `respect_but_quarantine_unsaved_changes`,
/// which calls [`invalidate_local_caches`] at both ends), then, on the same
/// thread, a file that depends on it typed outside the quarantine, with the
/// context of the entry and with the context without it: as on a fresh
/// thread.
#[test]
fn quarantine_leaves_nothing_behind() {
    let _lock = LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let disk: &[(&str, &str)] = &[
        ("b.php", "<?hh\ninterface I {}\nclass C {}\n"),
        (
            "d.php",
            "<?hh\nfunction f(Y $y): int { return $y->m(); }\nfunction g(C $c): I { return $c; }\n",
        ),
    ];
    let entry_contents = "<?hh\nclass Y { public function m(): string { return 's'; } }\n\
        function h(Y $y): int { return $y->m(); }\nfunction k(C $c): I { return $c; }\n";
    let with_entry = |ctx: &Arc<Ctx>| {
        crate::provider_context::add_or_overwrite_entry_contents(
            ctx,
            path("e.php").into(),
            entry_contents.into(),
        )
    };
    let after = |ctx: &Arc<Ctx>, ctx_e: &Arc<Ctx>| (check(ctx_e, "d.php"), check(ctx, "d.php"));
    let (inside, again) = on_new_thread(|| {
        sync_thread();
        let ctx = make_ctx(&[], disk, None);
        let (ctx_e, entry) = with_entry(&ctx);
        let inside = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx_e, || {
            let errors = crate::tast_provider::compute_tast_and_errors_quarantined(
                &ctx_e,
                &entry,
                &crate::tast_provider::ErrorFilter::default(),
            )
            .diagnostics;
            (crate::diagnostics_state::count(None, &errors), check(&ctx_e, "d.php"))
        });
        (inside, after(&ctx, &ctx_e))
    });
    let fresh = on_new_thread(|| {
        sync_thread();
        let ctx = make_ctx(&[], disk, None);
        let (ctx_e, _) = with_entry(&ctx);
        after(&ctx, &ctx_e)
    });
    assert!(inside.0 > 0, "the entry has an error");
    assert_eq!(again, fresh, "inside the quarantine: {:?}", inside);
}
