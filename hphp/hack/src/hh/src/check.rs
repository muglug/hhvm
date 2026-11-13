// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The two phases of a check: declaring every file, then checking every file.

use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;

use file_provider::FileProvider;
use oxidized::diagnostics::Diagnostic;
use pos::RelativePath;
use rayon::prelude::*;

use crate::ctx::Ctx;
use crate::diagnostics;
use crate::parse;

#[derive(Debug, Default, Clone)]
pub struct Stats {
    pub files: usize,
    pub bytes: usize,
    pub decl_time: Duration,
    pub check_time: Duration,
    /// Naming errors that have no message yet (see `naming_errors`).
    pub unrendered_naming_errors: usize,
}

/// Phase 1: parse the declarations of every file into the decl store.
///
/// Reading a file is mostly opening it, which can cost as much as parsing it
/// (where file accesses are monitored) and does not get faster with more
/// threads (the opens of concurrent threads serialise in the kernel): a few
/// threads of their own read the files, in order, ahead of the threads of the
/// pool, which parse what they read (from a bounded queue).
pub fn declare_files(ctx: &Ctx, paths: &[RelativePath], stats: &mut Stats) {
    declare_files_(ctx, paths, stats, None)
}

fn declare_files_(
    ctx: &Ctx,
    paths: &[RelativePath],
    stats: &mut Stats,
    on_file: Option<&(dyn Fn(RelativePath, &[ty::decl::shallow::NamedDecl<crate::ctx::R>]) + Sync)>,
) {
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;
    const READERS: usize = 3;
    let start = Instant::now();
    let queue = FileQueue::new(256, READERS);
    let next = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..READERS {
            scope.spawn(|| {
                while let Some(&path) = paths.get(next.fetch_add(1, Ordering::Relaxed)) {
                    // (A file that cannot be read declares nothing.)
                    if let Ok(text) = ctx.files.get(path) {
                        queue.push((path, text));
                    }
                }
                queue.close();
            });
        }
        rayon::broadcast(|_| {
            while let Some((path, text)) = queue.pop() {
                if let Ok(decls) = ctx.decl_parser.parse_with_text(path, &text) {
                    if let Some(on_file) = on_file {
                        on_file(path, &decls);
                    }
                    // When a name is declared twice, the first declaration
                    // (in the order of the paths, not of the threads) wins.
                    ctx.declare_file(path, decls);
                }
            }
        });
    });
    stats.decl_time += start.elapsed();
}

/// [`declare_files`], also giving the decls of each file to `on_file` (the
/// daemon builds its forward naming table from them, plan D4: no second
/// parse). Owned by **TCS** (plan §3.1); interface by W0 (plan §3.2).
pub fn declare_files_with(
    ctx: &Ctx,
    paths: &[RelativePath],
    stats: &mut Stats,
    on_file: &(dyn Fn(RelativePath, &[ty::decl::shallow::NamedDecl<crate::ctx::R>]) + Sync),
) {
    declare_files_(ctx, paths, stats, Some(on_file))
}

/// The files read for `declare_files`: a bounded queue whose waits block
/// (the channels of `crossbeam` spin a long time first, which costs the
/// readers more than they do when the queue stays full).
struct FileQueue {
    state: std::sync::Mutex<(std::collections::VecDeque<(RelativePath, bstr::BString)>, usize)>,
    not_empty: std::sync::Condvar,
    not_full: std::sync::Condvar,
    capacity: usize,
}

impl FileQueue {
    /// A queue of `capacity` files, filled by `writers` threads.
    fn new(capacity: usize, writers: usize) -> Self {
        Self {
            state: std::sync::Mutex::new((std::collections::VecDeque::with_capacity(capacity), writers)),
            not_empty: std::sync::Condvar::new(),
            not_full: std::sync::Condvar::new(),
            capacity,
        }
    }

    fn push(&self, file: (RelativePath, bstr::BString)) {
        let mut state = self.state.lock().unwrap();
        while state.0.len() >= self.capacity {
            state = self.not_full.wait(state).unwrap();
        }
        state.0.push_back(file);
        drop(state);
        self.not_empty.notify_one();
    }

    /// A writer is done.
    fn close(&self) {
        let mut state = self.state.lock().unwrap();
        state.1 -= 1;
        drop(state);
        self.not_empty.notify_all();
    }

    /// The next file, or `None` once every writer is done and the queue empty.
    fn pop(&self) -> Option<(RelativePath, bstr::BString)> {
        let mut state = self.state.lock().unwrap();
        loop {
            if let Some(file) = state.0.pop_front() {
                drop(state);
                self.not_full.notify_one();
                return Some(file);
            }
            if state.1 == 0 {
                return None;
            }
            state = self.not_empty.wait(state).unwrap();
        }
    }
}

/// `Typing[4001]`, the code of internal errors.
const INTERNAL_ERROR: isize = 4001;

struct FileResult {
    diagnostics: Vec<Diagnostic>,
    bytes: usize,
    unrendered_naming_errors: usize,
}

fn check_file(ctx: &Ctx, path: RelativePath) -> FileResult {
    let text = match ctx.files.get(path) {
        Ok(text) => text,
        Err(_) => {
            return FileResult {
                diagnostics: vec![],
                bytes: 0,
                unrendered_naming_errors: 0,
            };
        }
    };
    let ox_path: Arc<relative_path::RelativePath> = Arc::new(path.into());
    // A bug in the checker must not take the whole run down with it.
    let checked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let named = parse::parse_and_name(ctx, &ox_path, &text);
        let mut diagnostics = named.diagnostics;
        let mut unrendered = 0;
        for error in named.naming_errors {
            match crate::naming_errors::to_diagnostic(error) {
                Some(d) => diagnostics.push(d),
                None => unrendered += 1,
            }
        }
        crate::nast_check::check_program_with_comments(
            ctx,
            &named.program,
            &named.comments,
            &mut diagnostics,
        );
        crate::typing_slice::check_program(ctx, &named.program, &named.comments, &mut diagnostics);
        // `HH_FIXME`s apply to the diagnostics of every phase.
        diagnostics.retain(|d| {
            !crate::diagnostics::is_fixmed(&named.comments.fixmes, &d.claim.0, d.code)
        });
        (diagnostics, unrendered)
    }));
    let (diagnostics, unrendered) = checked.unwrap_or_else(|panic| {
        let what = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap_or("unknown panic");
        let pos = oxidized::pos::Pos::from_lnum_bol_offset(ox_path.clone(), (1, 0, 0), (1, 0, 0));
        let internal_error = diagnostics::error(
            INTERNAL_ERROR,
            pos,
            format!("Internal error: the typechecker panicked: {}", what),
        );
        (vec![internal_error], 0)
    });
    FileResult {
        diagnostics,
        bytes: text.len(),
        unrendered_naming_errors: unrendered,
    }
}

/// Phase 2: parse, name and typecheck every file. The diagnostics are sorted.
pub fn check_files(ctx: &Ctx, paths: &[RelativePath], stats: &mut Stats) -> Vec<Diagnostic> {
    let start = Instant::now();
    let results: Vec<FileResult> = paths
        .par_iter()
        .map(|&path| check_file(ctx, path))
        .collect();
    let mut all = vec![];
    for result in results {
        stats.files += 1;
        stats.bytes += result.bytes;
        stats.unrendered_naming_errors += result.unrendered_naming_errors;
        all.extend(result.diagnostics);
    }
    diagnostics::sort_and_dedup(&mut all);
    stats.check_time += start.elapsed();
    all
}

/// The diagnostics of a file of `check_files_typed_by_file`: the
/// `Diagnostics.t` that `Typing_check_service.process_file` gives for it (by
/// the file each diagnostic is reported in, in the order they were reported),
/// without those that an `HH_FIXME` suppresses.
#[cfg(feature = "port")]
pub type FileDiagnostics = crate::diagnostics_state::T;

/// Phase 2 with the ported typechecker: `Typing_check_service.process_file`
/// for every file of `paths`, in parallel; the diagnostics of each file, in
/// the order of `paths`. A file with parse errors gets only those; any other
/// file is typechecked (`Typing_check_job.calc_errors_and_tast`). The
/// diagnostics that an `HH_FIXME` suppresses are dropped, as
/// `Diagnostics.get_diagnostic_list` does. The loop is the typing service's
/// (`typing_check_service::check_paths`); a panic while checking a file is
/// reported as an internal error of that file. The dependency edges
/// recorded, if any (`--save-64bit`), are flushed by each thread and
/// registered.
#[cfg(feature = "port")]
pub fn check_files_typed_by_file(
    ctx: &Arc<Ctx>,
    paths: &[RelativePath],
    stats: &mut Stats,
) -> Vec<FileDiagnostics> {
    use crate::typing_check_service as tcs;
    let start = Instant::now();
    let checked = tcs::check_paths(ctx, paths, false, tcs::OnPanic::InternalError, None, false);
    crate::typing_deps::register_discovered_dep_edges(&checked.dep_edges);
    let mut all = Vec::with_capacity(paths.len());
    for tcs::FileOutcome { diagnostics, bytes } in checked.outcomes.into_iter().flatten() {
        stats.files += 1;
        stats.bytes += bytes;
        all.push(diagnostics);
    }
    stats.check_time += start.elapsed();
    all
}

// ~~ The check of a root ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// What `hh check ROOT` and `hh_server --check ROOT` share: the options of the
// root, the files to check, and the two phases.

/// The stack of every thread that typechecks. The typechecker recurses as
/// deeply as the expressions it checks (OCaml's stack grows on demand); the
/// memory is only reserved, and touched as it is used.
pub const STACK_SIZE: usize = 1 << 30;

/// Runs `f` on a thread of its own with a stack of [`STACK_SIZE`] (the main
/// thread's cannot be made larger), and waits for it.
pub fn run_on_large_stack<T: Send + 'static>(
    name: &str,
    f: impl FnOnce() -> T + Send + 'static,
) -> std::thread::Result<T> {
    std::thread::Builder::new()
        .name(name.to_string())
        .stack_size(STACK_SIZE)
        .spawn(f)
        .expect("cannot start the main thread")
        .join()
}

/// Makes rayon's global pool, whose threads do the work of both phases:
/// `threads` threads (as many as there are logical CPUs if `None`), with
/// stacks of [`STACK_SIZE`].
pub fn build_thread_pool(threads: Option<usize>) -> anyhow::Result<()> {
    let mut pool = rayon::ThreadPoolBuilder::new().stack_size(STACK_SIZE);
    if let Some(threads) = threads {
        pool = pool.num_threads(threads);
    }
    pool.build_global()?;
    Ok(())
}

/// Without the port, the options that the `hh_config` crate computes: those
/// of `.hhconfig` if there is one under `root`, then `defaults`, then
/// `overrides` (`key=value`, as for `--config`).
#[cfg(not(feature = "port"))]
pub fn hh_config(
    root: Option<&std::path::Path>,
    defaults: &[&str],
    overrides: &[String],
) -> anyhow::Result<hh_config::HhConfig> {
    use config_file::ConfigFile;
    let mut config = match root {
        Some(root) if root.join(".hhconfig").exists() => {
            ConfigFile::from_file(root.join(".hhconfig"))?
        }
        _ => ConfigFile::default(),
    };
    config.apply_overrides(&ConfigFile::from_args(
        defaults
            .iter()
            .map(|kv| kv.as_bytes())
            .chain(overrides.iter().map(|kv| kv.as_bytes())),
    ));
    hh_config::HhConfig::from_configs(
        root.unwrap_or(std::path::Path::new("")),
        config,
        ConfigFile::default(),
        Default::default(),
    )
}

/// The options of the check of `root` and the patterns of its ignored paths:
/// those of `hh_server --check ROOT` (`Server_config.load`, as
/// `Monitor_start.monitor_daemon_main` calls it): `ROOT/.hhconfig` with the
/// `--config` overrides (`cli_config_overrides`, as `Server_args.config` has
/// them: the last one given first), applied by `Server_config.load_config` to
/// the default options with the fields that the local config (`hh.conf`, with
/// the same overrides) decides, then the packages of the root. The messages
/// of `Server_config.load` go to the log (stderr).
#[cfg(feature = "port")]
pub fn check_options(
    root: &std::path::Path,
    cli_config_overrides: &[(String, String)],
) -> anyhow::Result<(oxidized::typechecker_options::TypecheckerOptions, Vec<String>)> {
    use crate::server_config;
    // `Wwwroot.validate_www_directory`, which `Server_args.parse_options`
    // applies to the root (here the root is the directory given, it is not
    // looked for in its parents): `Config_file.parse_hhconfig` would exit
    // with `Hhconfig_deleted`.
    if !root.join(".hhconfig").exists() {
        anyhow::bail!(
            "could not find a .hhconfig file in {} or any of its parent directories. Do you have a .hhconfig in your code's root directory?",
            root.display()
        );
    }
    crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, root);
    server_config::warn_on_invalid_config_keys(cli_config_overrides);
    let (config, _local_config) = server_config::load(false, "", cli_config_overrides)
        .map_err(|e| anyhow::anyhow!("{:?}", e))?;
    Ok((
        server_config::typechecker_options(&config),
        server_config::ignored_path_patterns(&config).to_vec(),
    ))
}

/// The options of the check of `root` without the port: those that the
/// `hh_config` crate computes.
#[cfg(not(feature = "port"))]
pub fn check_options(
    root: &std::path::Path,
    cli_config_overrides: &[(String, String)],
) -> anyhow::Result<(oxidized::typechecker_options::TypecheckerOptions, Vec<String>)> {
    // (`hh_config` applies the overrides in order: the last one wins.)
    let overrides: Vec<String> = cli_config_overrides
        .iter()
        .rev()
        .map(|(k, v)| format!("{k}={v}"))
        .collect();
    let hh_config = hh_config(Some(root), &[], &overrides)?;
    Ok((hh_config.opts, hh_config.ignored_paths))
}

/// A root whose options are known and whose files have been found.
pub struct Root {
    /// The root (a canonical path).
    pub root: std::path::PathBuf,
    pub ctx: Ctx,
    /// The hhi files, then the files of the root, in the order they are
    /// checked.
    pub paths: Vec<RelativePath>,
    /// How many of `paths` are hhi files.
    pub hhi_count: usize,
    /// When the work on the root began.
    pub start: Instant,
    /// How long finding the options and the files took.
    pub discovery_time: Duration,
}

/// The options of `root` (see [`check_options`]) and the Hack files under it
/// that are not ignored.
pub fn discover_root(
    root: &std::path::Path,
    cli_config_overrides: &[(String, String)],
) -> anyhow::Result<Root> {
    let root = root.canonicalize()?;
    let start = Instant::now();
    // The cache of localized type aliases (`Typing_phase`) has the settings
    // of OCaml (30 types of 10,000 nodes or more per worker); it keeps more
    // types where that cannot change what is computed (see
    // `typing_phase::MakeTyCache`).
    let (tco, ignored_paths) = check_options(&root, cli_config_overrides)?;
    discover_files(root, start, tco, &ignored_paths)
}

/// The Hack files under `root` (a canonical path) that the patterns
/// `ignored_paths` do not ignore, to be checked with the options `tco`;
/// the work on the root began at `start`.
pub fn discover_files(
    root: std::path::PathBuf,
    start: Instant,
    tco: oxidized::typechecker_options::TypecheckerOptions,
    ignored_paths: &[String],
) -> anyhow::Result<Root> {
    let ignored = crate::files::ignored_path_regexes(ignored_paths)?;
    let ctx = Ctx::new(&root, tco)?;
    let mut paths = ctx.hhi_paths.clone();
    let hhi_count = paths.len();
    paths.extend(
        crate::files::find_hack_files(&root, &ignored)
            .iter()
            .map(|path| RelativePath::new(pos::Prefix::Root, path)),
    );
    Ok(Root {
        root,
        ctx,
        paths,
        hhi_count,
        start,
        discovery_time: start.elapsed(),
    })
}

/// `Server_main.get_deps_mode options`: where the dependency edges of a check
/// go, given `--save-64bit` and `--save-human-readable-64bit-dep-map`. Set it
/// as the `deps_mode` of the root's `ctx` before [`check_root`].
#[cfg(feature = "port")]
pub fn get_deps_mode(
    save_64bit: Option<&str>,
    save_human_readable_64bit_dep_map: Option<&str>,
) -> crate::typing_deps::mode::T {
    match save_64bit {
        Some(new_edges_dir) => crate::typing_deps::mode::T::SaveToDiskMode {
            graph: None,
            new_edges_dir: new_edges_dir.to_string(),
            human_readable_dep_map_dir: save_human_readable_64bit_dep_map.map(str::to_string),
        },
        None => crate::typing_deps::mode::T::InMemoryMode(None),
    }
}

/// What [`check_root`] found.
pub struct CheckedRoot {
    pub stats: Stats,
    /// The diagnostics of each file checked, in the order of the files.
    #[cfg(feature = "port")]
    pub diagnostics: Vec<FileDiagnostics>,
    #[cfg(not(feature = "port"))]
    pub diagnostics: Vec<Diagnostic>,
}

impl CheckedRoot {
    /// The diagnostics of all the files, sorted and without duplicates (what
    /// `hh check` prints).
    pub fn sorted_diagnostics(self) -> Vec<Diagnostic> {
        #[cfg(feature = "port")]
        return crate::diagnostics_state::sort(
            self.diagnostics
                .into_iter()
                .flat_map(|d| d.into_values().flatten())
                .collect(),
        );
        #[cfg(not(feature = "port"))]
        self.diagnostics
    }
}

/// Instructions retired and CPU cycles of this process so far (0 where the OS
/// does not say).
#[cfg(feature = "port")]
fn instructions_and_cycles() -> (u64, u64) {
    #[cfg(target_os = "macos")]
    unsafe {
        let mut info: libc::rusage_info_v4 = std::mem::zeroed();
        libc::proc_pid_rusage(
            libc::getpid(),
            libc::RUSAGE_INFO_V4,
            &mut info as *mut _ as *mut libc::rusage_info_t,
        );
        (info.ri_instructions, info.ri_cycles)
    }
    #[cfg(not(target_os = "macos"))]
    (0, 0)
}

/// The two phases on the files of `root`: every file is declared (the hhi
/// files and those of the root), then the files of the root are checked
/// (only those listed in the file `only`, one root-relative path per line,
/// if there is one), with rayon's global pool. The hhi files are named as
/// under `hhi_root` (`hh_server` extracts them there; `hh check` and
/// `hh single` name them `/hhi/...`).
pub fn check_root(
    root: Root,
    only: Option<&std::path::Path>,
    hhi_root: &std::path::Path,
) -> anyhow::Result<CheckedRoot> {
    let Root {
        root,
        ctx,
        mut paths,
        hhi_count,
        ..
    } = root;
    let mut stats = Stats::default();
    declare_files(&ctx, &paths, &mut stats);
    if let Some(only) = only {
        let wanted: std::collections::HashSet<std::path::PathBuf> =
            std::fs::read_to_string(only)?
                .lines()
                .filter(|l| !l.trim().is_empty())
                .map(|l| std::path::PathBuf::from(l.trim()))
                .collect();
        let rest: Vec<RelativePath> = paths[hhi_count..]
            .iter()
            .filter(|p| wanted.contains(p.path()))
            .copied()
            .collect();
        paths.truncate(hhi_count);
        paths.extend(rest);
    }
    // The hhi files are declared, but only the files of the root are checked.
    #[cfg(not(feature = "port"))]
    let diagnostics = {
        let _ = (&root, hhi_root);
        check_files(&ctx, &paths[hhi_count..], &mut stats)
    };
    #[cfg(feature = "port")]
    let diagnostics = {
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, &root);
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Hhi, hhi_root);
        crate::relative_path::set_path_prefix(
            crate::relative_path::Prefix::Tmp,
            std::path::Path::new("/tmp"),
        );
        // The workers of the OCaml's check mode trace the dependency edges
        // (they copy `Typing_deps.trace` before `Server_env_build.make_genv`
        // turns it off for the master); only `SaveToDiskMode` (`--save-64bit`)
        // makes that observable, so only then are they traced here.
        //
        // The OCaml also typechecks the hhi files (they are in its naming
        // table); that only shows in the edges (they report no error), so
        // they are checked only when the edges are saved.
        //
        // Not in the OCaml: `HH_RECORD_EDGES_TO=FILE` records the edges in
        // memory, as the daemon does (`InMemoryMode`, `trace` on), and saves
        // the delta to FILE at the end (`Typing_deps.save_discovered_edges`,
        // the format of `--save-64bit`): to test and measure the daemon's
        // recording with the batch check.
        let record_edges_to = std::env::var_os("HH_RECORD_EDGES_TO");
        let first_checked = if let crate::typing_deps::mode::T::SaveToDiskMode { .. } =
            &ctx.deps_mode
        {
            crate::typing_deps::trace.store(true, std::sync::atomic::Ordering::Relaxed);
            0
        } else if record_edges_to.is_some() {
            crate::typing_deps::trace.store(true, std::sync::atomic::Ordering::Relaxed);
            0
        } else {
            hhi_count
        };
        let ctx = Arc::new(ctx);
        crate::hh_single_type_check::install(&ctx);
        crate::ast_provider::set_local_parser_cache_enabled(false);
        // `HH_PERF_INSTR=1`: print the instructions retired by the check phase.
        let (instr0, cycles0) = instructions_and_cycles();
        let diagnostics = check_files_typed_by_file(&ctx, &paths[first_checked..], &mut stats);
        if let Some(file) = &record_edges_to {
            let file = file.to_string_lossy();
            let edges = crate::typing_deps::save_discovered_edges(&ctx.deps_mode, &file, false);
            eprintln!("recorded edges saved to {}: {} dependencies", file, edges);
        }
        if std::env::var_os("HH_PERF_INSTR").is_some() {
            let (instr1, cycles1) = instructions_and_cycles();
            eprintln!("check-instr: {:.2}G", (instr1 - instr0) as f64 / 1e9);
            // The cycles of all the threads in the check phase: at 8 threads
            // against 1, the difference is contention (cache lines bouncing
            // between cores), which the instructions do not show.
            eprintln!("check-cycles: {:.2}G", (cycles1 - cycles0) as f64 / 1e9);
        }
        diagnostics
    };
    Ok(CheckedRoot { stats, diagnostics })
}
