// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The daemon's memory over cycles of edits and reverts: the bytes
//! live after each cycle must come back to the level after the first one.
//!
//! The daemon runs in a child process (the harness of
//! `server_type_check::tests::child`, mode `daemon`, with `HH_TYPE_CHECK_TEST_HEAP=1`:
//! the lib test binary's allocator counts and the child prints the bytes
//! live after each step).

use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;

const LOG: &str = "final class Log {
  public static function devDebug(mixed $msg, dict<string, mixed> $ctx = dict[]): void {
    if ($msg is string) { echo $msg; }
  }
  public static function info(string $msg): void { echo $msg; }
}
";

const HTTP: &str = "enum HttpMethod: string {
  GET = 'GET';
  POST = 'POST';
}

const int HTTP_REDIRECT_LIMIT = 5;

final class HttpLib {
  public static int $timeout = 30;
}
";

fn class_file(i: usize) -> String {
    let b = i % 5;
    let dep = if i > 0 { format!("return C{}::make()->count();", i - 1) } else { "return 0;".to_string() };
    format!(
        "final class C{i} extends Base{b}<int> {{
  const int K = {i};
  public function name(): string {{ return 'C{i}'; }}
  public function run(HttpMethod $m, dict<string, vec<int>> $d): int {{
    Log::devDebug('run', dict['i' => {i}]);
    $n = 0;
    foreach ($d as $k => $v) {{ $n += \\count($v) + \\strlen($k); }}
    switch ($m) {{
      case HttpMethod::GET: $n += 1; break;
      case HttpMethod::POST: $n += 2; break;
    }}
    $s = $this->shape_of();
    $n += $s['n'] + HTTP_REDIRECT_LIMIT + HttpLib::$timeout;
    $f = (int $x): int ==> $x * {k};
    return $f($n);
  }}
  public static function make(): C{i} {{ return new C{i}(); }}
  public function other(): int {{ {dep} }}
}}

function f{i}(vec<C{i}> $xs): int {{
  $t = 0;
  foreach ($xs as $x) {{ $t += $x->run(HttpMethod::GET, dict['a' => vec[1, 2]]); }}
  Log::info('f{i}');
  return $t;
}}
",
        k = i % 13 + 1
    )
}

/// The generated tree: `(path, contents)`.
fn tree(n: usize) -> Vec<(String, String)> {
    let mut files = vec![
        ("src/logger/Log.hack".to_string(), LOG.to_string()),
        ("src/http/lib_http.hack".to_string(), HTTP.to_string()),
    ];
    for b in 0..5 {
        files.push((
            format!("src/base/Base{b}.hack"),
            format!(
                "abstract class Base{b}<T> {{
  protected vec<T> $items = vec[];
  public function add(T $x): this {{ $this->items[] = $x; return $this; }}
  public function count(): int {{ return \\count($this->items); }}
  abstract public function name(): string;
  public function shape_of(): shape('n' => int, 's' => string) {{
    return shape('n' => $this->count(), 's' => $this->name());
  }}
}}
"
            ),
        ));
    }
    for i in 0..n {
        files.push((format!("src/c/{}/C{i}.hack", i % 20), class_file(i)));
    }
    files
}

/// One cycle of the edits of a recorded webapp session, each
/// followed by its revert: `(path, Some(contents) | None)` per step.
fn cycle(files: &[(String, String)]) -> Vec<Vec<(String, Option<String>)>> {
    let log = "src/logger/Log.hack".to_string();
    let http = "src/http/lib_http.hack".to_string();
    let c5 = files.iter().find(|(p, _)| p.ends_with("/C5.hack")).unwrap().clone();
    let one = |p: &String, c: String| vec![(p.clone(), Some(c))];
    let mut steps = vec![];
    let mut edit = |p: &String, orig: &str, new: String| {
        steps.push(one(p, new));
        steps.push(one(p, orig.to_string()));
    };
    edit(&log, LOG, LOG.replace("echo $msg;", "echo $msg; echo 'x';"));
    edit(&log, LOG, LOG.replace("devDebug(mixed $msg", "devDebug(string $msg"));
    edit(&log, LOG, LOG.replace("final class Log {", "final class Log {\n  public static function extra(): void {}"));
    edit(&c5.0, &c5.1, c5.1.replace("$n = 0;", "$n = 0; $q = 1 + 'a';"));
    edit(&http, HTTP, HTTP.replace("POST = 'POST';", "POST = 'POST';\n  PUT = 'PUT';"));
    edit(&http, HTTP, HTTP.replace("const int HTTP_REDIRECT_LIMIT = 5;", "const string HTTP_REDIRECT_LIMIT = '5';"));
    edit(&http, HTTP, HTTP.replace("public static int $timeout", "public static string $timeout"));
    edit(&log, LOG, LOG.replace("final class Log {", "final class Log {{"));
    let new = "src/t2/T2New.hack".to_string();
    steps.push(one(&new, "function t2_new(): int { return C5::make()->run(HttpMethod::GET, dict[]); }\n".to_string()));
    steps.push(vec![(new, None)]);
    let dup = "src/t2/dup.hack".to_string();
    steps.push(one(&dup, "final class Log {}\n".to_string()));
    steps.push(vec![(dup, None)]);
    // Many files at once, then back.
    let bulk: Vec<_> = files.iter().filter(|(p, _)| p.starts_with("src/c/")).step_by(7).take(40).collect();
    steps.push(
        bulk.iter()
            .enumerate()
            .map(|(k, (p, c))| (p.clone(), Some(format!("{c}\nfunction t2_bulk_{k}(): int {{ return {k}; }}\n"))))
            .collect(),
    );
    steps.push(bulk.iter().map(|(p, c)| (p.clone(), Some(c.clone()))).collect());
    steps
}

fn scratch(test: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("hh-mem-{}-{}", test, std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// The bytes live after init and after each cycle of `cycles` (and the
/// steps per cycle), for a tree of `n` class files.
fn live_after_cycles(test: &str, n: usize, cycles: usize) -> (Vec<i64>, usize) {
    let dir = scratch(test);
    let root = dir.join("root");
    let files = tree(n);
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(root.join(".hhconfig"), "").unwrap();
    for (p, c) in &files {
        let path = root.join(p);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, c).unwrap();
    }
    let steps = cycle(&files);
    let edits = dir.join("edits");
    let mut k = 0;
    for _ in 0..cycles {
        for step in &steps {
            k += 1;
            let step_dir = edits.join(k.to_string());
            std::fs::create_dir_all(&step_dir).unwrap();
            let mut deleted = String::new();
            for (p, c) in step {
                match c {
                    Some(c) => {
                        let path = step_dir.join(p);
                        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
                        std::fs::write(path, c).unwrap();
                    }
                    None => {
                        deleted.push_str(p);
                        deleted.push('\n');
                    }
                }
            }
            if !deleted.is_empty() {
                std::fs::write(edits.join(format!("{k}.deleted")), deleted).unwrap();
            }
        }
    }
    let out = dir.join("out");
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["server_type_check::tests::child", "--exact", "--nocapture", "--test-threads=1"])
        .env("HH_TYPE_CHECK_TEST_MODE", "daemon")
        .env("HH_TYPE_CHECK_TEST_ROOT", &root)
        .env("HH_TYPE_CHECK_TEST_EDITS", &edits)
        .env("HH_TYPE_CHECK_TEST_OUT", &out)
        .env("HH_TYPE_CHECK_TEST_HEAP", "1")
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("1 passed"),
        "the child failed:\n{stdout}\n{}",
        &stderr[stderr.len().saturating_sub(20000)..]
    );
    let out = std::fs::read_to_string(&out).unwrap();
    let live: Vec<i64> = out
        .lines()
        .filter_map(|l| l.strip_prefix("=== heap "))
        .map(|n| n.parse().unwrap())
        .collect();
    assert_eq!(live.len(), 1 + cycles * steps.len(), "{out}");
    if let Some(dump) = std::env::var_os("HH_MEM_DUMP") {
        // The bytes live after each step, one per line.
        let lines: Vec<String> = live.iter().map(|l| l.to_string()).collect();
        std::fs::write(dump, lines.join("\n")).unwrap();
    }
    let _ = std::fs::remove_dir_all(&dir);
    let per_cycle = steps.len();
    (
        (0..=cycles).map(|c| live[c * per_cycle]).collect(),
        per_cycle,
    )
}

fn mb(b: i64) -> f64 {
    b as f64 / 1e6
}

/// After the first cycle of edits and reverts, the bytes live do not
/// grow from cycle to cycle (the OCaml's footprint is flat after its first
/// cycle). Tolerance: 1% of the level after the first cycle, at least
/// 0.75 MB. (Before the fixes of the daemon's memory growth: +2.1 MB after 10
/// cycles, growing by about 0.2 MB a cycle; after: +0.3 MB, flat from the third
/// cycle.)
#[test]
fn live_bytes_plateau_over_recheck_cycles() {
    let cycles = 10;
    let (live, steps) = live_after_cycles("plateau", 300, cycles);
    let shown: Vec<String> = live.iter().map(|b| format!("{:.2}", mb(*b))).collect();
    eprintln!("live MB after init and each cycle of {steps} steps: {}", shown.join(" "));
    let base = live[1];
    let tolerance = (base / 100).max(750_000);
    for (c, l) in live.iter().enumerate().skip(2) {
        assert!(
            l - base <= tolerance,
            "cycle {c}: {:.2} MB live, {:.2} MB more than after cycle 1 (tolerance {:.2} MB): {}",
            mb(*l),
            mb(l - base),
            mb(tolerance),
            shown.join(" ")
        );
    }
}

/// For investigation: `HH_MEM_N=files HH_MEM_CYCLES=k cargo test ...
/// heap_stats::tests::series -- --ignored --nocapture`.
#[test]
#[ignore]
fn series() {
    let n = std::env::var("HH_MEM_N").map_or(300, |v| v.parse().unwrap());
    let cycles = std::env::var("HH_MEM_CYCLES").map_or(6, |v| v.parse().unwrap());
    let (live, steps) = live_after_cycles("series", n, cycles);
    let shown: Vec<String> = live.iter().map(|b| format!("{:.2}", mb(*b))).collect();
    eprintln!("{n} files, {steps} steps per cycle; live MB after init and each cycle: {}", shown.join(" "));
}

/// For investigation on a real tree: `HH_MEM_DIR=<a directory of edits,
/// one subdirectory per step> HH_MEM_STEPS=<steps per cycle>
/// cargo test ... heap_stats::tests::series_dir -- --ignored --nocapture`
/// (`HH_MEM_DUMP=FILE`: the bytes live after each step).
#[test]
#[ignore]
fn series_dir() {
    let dir = PathBuf::from(std::env::var("HH_MEM_DIR").unwrap());
    let per_cycle: usize = std::env::var("HH_MEM_STEPS").unwrap().parse().unwrap();
    let out = dir.join("out");
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["server_type_check::tests::child", "--exact", "--nocapture", "--test-threads=1"])
        .env("HH_TYPE_CHECK_TEST_MODE", "daemon")
        .env("HH_TYPE_CHECK_TEST_ROOT", dir.join("root"))
        .env("HH_TYPE_CHECK_TEST_EDITS", dir.join("edits"))
        .env("HH_TYPE_CHECK_TEST_OUT", &out)
        .env("HH_TYPE_CHECK_TEST_HEAP", "1")
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("1 passed"),
        "the child failed:\n{stdout}\n{}",
        &stderr[stderr.len().saturating_sub(20000)..]
    );
    let out = std::fs::read_to_string(&out).unwrap();
    let live: Vec<i64> = out
        .lines()
        .filter_map(|l| l.strip_prefix("=== heap "))
        .map(|n| n.parse().unwrap())
        .collect();
    if let Some(dump) = std::env::var_os("HH_MEM_DUMP") {
        let lines: Vec<String> = live.iter().map(|l| l.to_string()).collect();
        std::fs::write(dump, lines.join("\n")).unwrap();
    }
    let shown: Vec<String> = live.iter().step_by(per_cycle).map(|b| format!("{:.2}", mb(*b))).collect();
    eprintln!("live MB after init and each cycle: {}", shown.join(" "));
}

/// The child of `server_type_check::tests`, mode `breakdown` (after init and
/// the full check of its root): the bytes live by owner, found by taking the
/// daemon's state apart piece by piece and counting what each piece freed. One
/// line per piece.
pub(crate) fn breakdown(after_init: Option<i64>, env: crate::server_env::Env) -> String {
    let env = env;
    use std::fmt::Write;
    let live = || super::live_bytes().unwrap();
    let mut out = String::new();
    let last = std::cell::Cell::new(live());
    let step = |out: &mut String, what: &str| {
        let now = live();
        writeln!(out, "{:>10.1} MB  {}", (last.get() - now) as f64 / 1e6, what).unwrap();
        last.set(now);
    };
    let (rss, _, commit, _) = super::process_info();
    writeln!(
        out,
        "live after init {:.1} MB, after the full check {:.1} MB (mimalloc commit {:.1} MB, rss {:.1} MB)",
        after_init.unwrap_or(0) as f64 / 1e6,
        last.get() as f64 / 1e6,
        commit as f64 / 1e6,
        rss as f64 / 1e6
    )
    .unwrap();
    crate::rt::decl_epoch::wait_for_hash_consed_gc();
    let mi = |out: &mut String, what: &str| {
        let (rss, _, commit, _) = super::process_info();
        writeln!(
            out,
            "  {what}: live {:.1} MB, mimalloc commit {:.1} MB, rss {:.1} MB, phys_footprint {:.1} MB",
            live() as f64 / 1e6,
            commit as f64 / 1e6,
            rss as f64 / 1e6,
            super::phys_footprint() as f64 / 1e6
        )
        .unwrap();
    };
    let sample = |out: &mut String, what: &str| {
        if let Some(dir) = std::env::var_os("HH_HEAP_SAMPLE_OUT") {
            let path = std::path::Path::new(&dir).join(format!("{what}.txt"));
            let bytes = super::sampler::report(&path);
            writeln!(out, "  (samples: {:.1} MB live in {})", bytes as f64 / 1e6, path.display()).unwrap();
        }
    };
    mi(&mut out, "after the check's release (and its hcons collection)");
    out.push_str(&super::mi_report(true));
    sample(&mut out, "after_check");
    let t = std::time::Instant::now();
    rayon::broadcast(|_| super::collect(true));
    super::collect(true);
    let collect_ms = t.elapsed().as_secs_f64() * 1e3;
    mi(&mut out, &format!("after mi_collect(true) on every thread ({collect_ms:.0} ms)"));
    out.push_str(&super::mi_report(false));
    {
        use ty::reason::Reason;
        let conser = crate::ctx::R::decl_ty_conser();
        let (len, cap) = conser.len_and_capacity();
        let before = live();
        let t = std::time::Instant::now();
        conser.shrink_to_fit();
        writeln!(
            out,
            "  hcons table: {len} entries, capacity {cap}; shrink_to_fit freed {:.1} MB in {:.0} ms (capacity now {})",
            (before - live()) as f64 / 1e6,
            t.elapsed().as_secs_f64() * 1e3,
            conser.len_and_capacity().1
        )
        .unwrap();
    }
    rayon::broadcast(|_| super::collect(true));
    super::collect(true);
    mi(&mut out, "after the hcons shrink and mi_collect");
    out.push_str(&super::mi_report(false));
    last.set(live());
    let edges = crate::typing_deps::telemetry::depgraph_delta_num_edges(&env.deps_mode);
    writeln!(out, "dependency edges in memory: {:?}", edges).unwrap();
    {
        use ty::reason::Reason;
        let t = std::time::Instant::now();
        crate::ctx::R::decl_ty_conser().gc();
        let what = format!(
            "hash-consed decl types: dead entries (`Conser::gc`, {:.0} ms)",
            t.elapsed().as_secs_f64() * 1e3
        );
        step(&mut out, &what);
    }
    // The per-thread caches and memos of every pool thread and this one,
    // one kind at a time (`decl_epoch::forget_thread_memos`).
    let each = |f: fn()| {
        rayon::broadcast(|_| f());
        f();
    };
    each(crate::decl_provider::forget_thread_memos);
    step(&mut out, "per-thread: decl_provider class/fun/typedef cache");
    each(crate::ast_provider::forget_thread_local_caches);
    step(&mut out, "per-thread: ast_provider local caches");
    each(crate::typing_phase::forget_thread_memos);
    step(&mut out, "per-thread: typing_phase alias cache + localize memo");
    each(crate::typing_data_type::forget_thread_memos);
    each(crate::tast_logger_util::generated_file_utils::forget_thread_memos);
    each(crate::tast_env::clear_merge_memo);
    step(&mut out, "per-thread: typing_data_type, tast_logger_util, tast_env merge memo");
    each(crate::naming_provider::forget_thread_memos);
    step(&mut out, "per-thread: naming_provider memos");
    each(crate::typing_subtype::subtype_ask::memo::forget_thread_memos);
    step(&mut out, "per-thread: subtype ask/tell memo");
    each(crate::typing_subtype::dynamic_memo::forget_thread_memos);
    each(crate::typing_disposable::forget_thread_memos);
    step(&mut out, "per-thread: dynamic_memo, typing_disposable");
    each(crate::ast_provider::forget_thread_heaps);
    step(&mut out, "per-thread: ast_provider parser heap (ASTs)");
    each(crate::file_provider::file_heap::forget_thread_heap);
    step(&mut out, "per-thread: file_provider file heap (contents)");
    each(crate::fixme_provider::forget_thread_tables);
    step(&mut out, "per-thread: fixme tables");
    crate::rt::decl_epoch::bump();
    rayon::broadcast(|_| crate::rt::decl_epoch::sync_thread());
    crate::rt::decl_epoch::sync_thread();
    step(&mut out, "per-thread: anything else forget_thread_memos drops");
    each(crate::ctx::forget_thread_symbols);
    step(&mut out, "per-thread: tables of interned symbols (ctx::symbol)");
    let mut env = env;
    env.diagnostics = Default::default();
    step(&mut out, "diagnostics (env.diagnostics)");
    let dest = std::env::temp_dir().join(format!("hh-mem-edges-{}", std::process::id()));
    crate::typing_deps::save_discovered_edges(&env.deps_mode, &dest.display().to_string(), true);
    let _ = std::fs::remove_file(&dest);
    step(&mut out, "dependency edges (the in-memory delta)");
    let names = crate::naming_table::fold(None, &env.naming_table, crate::file_info::empty_names(), |_, fi, mut acc| {
        let n = crate::file_info::simplify(fi);
        acc.funs.extend(n.funs);
        acc.classes.extend(n.classes);
        acc.types.extend(n.types);
        acc.consts.extend(n.consts);
        acc.modules.extend(n.modules);
        acc
    });
    step(&mut out, "(the names of every file, made for the next steps: freed later)");
    if std::env::var_os("HH_MEM_ENCODE").is_some() {
        // What the decls would take as bincode (the OCaml keeps its decls as
        // compressed marshalled blobs), and what encoding and decoding cost.
        let config = bincode::config::standard();
        let (mut n, mut bytes, mut enc, mut dec) = (0usize, 0usize, 0f64, 0f64);
        for name in &names.classes {
            if let Some(c) = env.ctx.get_folded_class_if_present(name) {
                let t = std::time::Instant::now();
                let v = bincode::serde::encode_to_vec(intern::WithIntern(&*c), config).unwrap();
                enc += t.elapsed().as_secs_f64();
                let t = std::time::Instant::now();
                let (intern::WithIntern(back), _): (intern::WithIntern<ty::decl::FoldedClass<crate::ctx::R>>, usize) =
                    bincode::serde::decode_from_slice(&v, config).unwrap();
                assert!(back == *c, "{name}: the decoded folded class differs");
                dec += t.elapsed().as_secs_f64();
                n += 1;
                bytes += v.len();
            }
        }
        {
            // What the member maps hold (and could hold without slack).
            let (mut elts, mut cap, mut consts, mut tconsts, mut ancestors, mut substs, mut with_sets) = (0, 0, 0, 0, 0, 0, 0);
            for name in &names.classes {
                if let Some(c) = env.ctx.get_folded_class_if_present(name) {
                    for m in [&c.props, &c.static_props] {
                        elts += m.len();
                        cap += m.capacity();
                        with_sets += m.values().filter(|e| e.sealed_allowlist.is_some() || e.overlapping_tparams.is_some()).count();
                    }
                    for m in [&c.methods, &c.static_methods] {
                        elts += m.len();
                        cap += m.capacity();
                        with_sets += m.values().filter(|e| e.sealed_allowlist.is_some() || e.overlapping_tparams.is_some()).count();
                    }
                    consts += c.consts.len();
                    tconsts += c.type_consts.len();
                    ancestors += c.ancestors.len();
                    substs += c.substs.len();
                }
            }
            writeln!(out, "  folded members: {elts} (capacity {cap}; {with_sets} with a sealed allowlist or overlapping tparams), consts {consts}, type consts {tconsts}, ancestors {ancestors}, substs {substs}").unwrap();
        }
        writeln!(out, "  folded classes as bincode: {n} classes, {:.1} MB; encode {:.1} us, decode {:.1} us per class", bytes as f64 / 1e6, enc / n.max(1) as f64 * 1e6, dec / n.max(1) as f64 * 1e6).unwrap();
        let (mut n, mut bytes, mut dec) = (0usize, 0usize, 0f64);
        for name in &names.classes {
            if let Ok(Some(c)) = env.ctx.shallow_decls.get_class(pos::TypeName(crate::ctx::symbol(name))) {
                let v = bincode::serde::encode_to_vec(intern::WithIntern(&*c), config).unwrap();
                let t = std::time::Instant::now();
                let (intern::WithIntern(back), _): (intern::WithIntern<ty::decl::ShallowClass<crate::ctx::R>>, usize) =
                    bincode::serde::decode_from_slice(&v, config).unwrap();
                assert!(back == *c, "{name}: the decoded shallow class differs");
                dec += t.elapsed().as_secs_f64();
                n += 1;
                bytes += v.len();
            }
        }
        writeln!(out, "  shallow classes as bincode: {n} classes, {:.1} MB; decode {:.1} us per class", bytes as f64 / 1e6, dec / n.max(1) as f64 * 1e6).unwrap();
        last.set(live());
    }
    env.ctx.remove_folded_classes(&names.classes.iter().cloned().collect());
    step(&mut out, "folded classes");
    env.ctx.remove_old_defs(&names);
    step(&mut out, "old decls");
    env.ctx.remove_defs(&names);
    step(&mut out, "shallow decls (live decls of every name)");
    crate::ast_provider::forget_thread_heaps();
    crate::file_provider::file_heap::forget_thread_heap();
    step(&mut out, "world thread's parser/file heaps");
    drop(names);
    step(&mut out, "(the names again)");
    let crate::server_env::Env { naming_table, failed_naming, needs_recheck, disk_needs_parsing, .. } = &mut env;
    *naming_table = crate::naming_table::create(Default::default());
    *failed_naming = Default::default();
    *needs_recheck = Default::default();
    *disk_needs_parsing = Default::default();
    step(&mut out, "forward naming table (env.naming_table) and the file sets");
    drop(env);
    step(&mut out, "the rest of env (its Ctx: reverse naming table, canon names, ...; unless installed elsewhere)");
    {
        use ty::reason::Reason;
        crate::ctx::R::decl_ty_conser().gc();
        step(&mut out, "hash-consed decl types that only the decls removed above used");
    }
    crate::decl_store::set(crate::decl_store::SHARED_MEMORY_STORE.clone());
    step(&mut out, "the installed context (decl_store): its stores, reverse naming table, canon names");
    {
        use ty::reason::Reason;
        crate::ctx::R::decl_ty_conser().gc();
        step(&mut out, "hash-consed decl types that only the installed context used");
    }
    writeln!(out, "{:>10.1} MB  left (globals: interners, installed context, hash-consed types, ...)", last.get() as f64 / 1e6).unwrap();
    sample(&mut out, "left");
    rayon::broadcast(|_| super::collect(true));
    super::collect(true);
    mi(&mut out, "at the end, after mi_collect");
    out.push_str(&super::mi_report(false));
    out
}

/// `HH_MEM_ROOT=<root> cargo test ... heap_stats::tests::breakdown_of_root
/// -- --ignored --nocapture`: the bytes live after init and the full check
/// of a root, by owner (see [`breakdown`]).
#[test]
#[ignore]
fn breakdown_of_root() {
    let root = PathBuf::from(std::env::var("HH_MEM_ROOT").unwrap());
    let dir = scratch("breakdown");
    let out = dir.join("out");
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["server_type_check::tests::child", "--exact", "--nocapture", "--test-threads=1"])
        .env("HH_TYPE_CHECK_TEST_MODE", "breakdown")
        .env("HH_TYPE_CHECK_TEST_ROOT", &root)
        .env("HH_TYPE_CHECK_TEST_OUT", &out)
        .env("HH_TYPE_CHECK_TEST_HEAP", "1")
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("1 passed"),
        "the child failed:\n{stdout}\n{}",
        &stderr[stderr.len().saturating_sub(20000)..]
    );
    eprintln!("{}", std::fs::read_to_string(&out).unwrap());
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
#[ignore]
fn decl_type_sizes() {
    use std::mem::size_of;
    type R = crate::ctx::R;
    eprintln!("FoldedElement {}", size_of::<ty::decl::folded::FoldedElement>());
    eprintln!("ClassConst {}", size_of::<ty::decl::folded::ClassConst<R>>());
    eprintln!("TypeConst {}", size_of::<ty::decl::folded::TypeConst<R>>());
    eprintln!("SubstContext {}", size_of::<ty::decl::folded::SubstContext<R>>());
    eprintln!("FoldedClass {}", size_of::<ty::decl::FoldedClass<R>>());
    eprintln!("Ty {}", size_of::<ty::decl::Ty<R>>());
    eprintln!("BPos {}", size_of::<pos::BPos>());
    eprintln!("IndexSet<TypeName> {}", size_of::<indexmap::IndexSet<pos::TypeName>>());
}
