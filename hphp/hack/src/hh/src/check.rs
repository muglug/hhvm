// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: the driver of `hh check` (and of the daemon's full
//! init): declaring every file, then checking every file, on rayon threads.
//! It stands in for the parsing of `Server_init`'s full init and for
//! `Typing_check_service.go` over `Multi_worker`'s worker processes.

use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;

use file_provider::FileProvider;
use oxidized::diagnostics::Diagnostic;
use pos::RelativePath;
use rayon::prelude::*;

use crate::ctx::Ctx;
use crate::diagnostics_helpers;
use crate::parse;

#[derive(Debug, Default, Clone)]
pub struct Stats {
    pub files: usize,
    pub bytes: usize,
    pub decl_time: Duration,
    pub check_time: Duration,
}

/// Phase 1: parse the declarations of every file into the decl store.
///
/// The OCaml's parsing workers (`Direct_decl_service.go` over `Multi_worker`)
/// each open and parse the files of their bucket. Here a few threads of their
/// own read the files, in order, ahead of the threads of the pool, which
/// parse what they read (from a bounded queue), because reading a file is
/// mostly opening it, which can cost as much as parsing it (where file
/// accesses are monitored) and does not get faster with more threads (the
/// opens of concurrent threads serialise in the kernel).
pub fn declare_files(ctx: &Ctx, paths: &[RelativePath], stats: &mut Stats) {
    declare_files_(ctx, paths, stats, None)
}

fn declare_files_(
    ctx: &Ctx,
    paths: &[RelativePath],
    stats: &mut Stats,
    on_file: Option<&(dyn Fn(RelativePath, &oxidized::direct_decl_parser::ParsedFileWithHashes) + Sync)>,
) {
    #[cfg(feature = "server")]
    if on_file.is_none() && crate::multi_worker::has_workers() {
        if let Some(snapshot) = ctx.worker_snapshot() {
            let start = Instant::now();
            declare_files_on_workers(ctx, snapshot, paths, false);
            stats.decl_time += start.elapsed();
            return;
        }
    }
    declare_files_on_threads(ctx, paths, stats, on_file)
}

/// [`declare_files_with_infos`] (and [`declare_files`]) over the workers:
/// `Direct_decl_service.go ~decl_mode:Cached` (buckets of
/// `Multi_worker.next`: each clone parses its files, adds their decls to the
/// shared heap and sends back the kinds and names of the decls, with the file
/// infos if asked), then the master binds the names file after file
/// (`Ctx::bind_file_names`), and stores the winners of the names declared
/// more than once (`Ctx::store_winners_of_duplicates`): the stores end up as
/// [`declare_files_on_threads`] leaves them.
#[cfg(feature = "server")]
fn declare_files_on_workers(
    ctx: &Ctx,
    snapshot: crate::ctx::WorkerSnapshot,
    paths: &[RelativePath],
    want_infos: bool,
) -> Vec<(RelativePath, crate::file_info::T)> {
    use crate::ctx::DeclKind;
    let indexed: Vec<(usize, crate::relative_path::RelativePath)> =
        paths.iter().enumerate().map(|(i, p)| (i, crate::relative_path::RelativePath::from(*p))).collect();
    let num_workers = crate::multi_worker::num_workers();
    let mut per_file: Vec<Option<ParsedNames>> = Vec::with_capacity(paths.len());
    per_file.resize_with(paths.len(), || None);
    let next = crate::multi_worker::next(num_workers, None, indexed);
    let mut next = {
        let mut next = next;
        move || match next() {
            crate::multi_worker::Bucket::Job(paths) => crate::multi_worker::Bucket::Job(DeclareInput {
                ctx: snapshot.clone(),
                paths,
                want_infos,
            }),
            crate::multi_worker::Bucket::Wait => crate::multi_worker::Bucket::Wait,
            crate::multi_worker::Bucket::Done => crate::multi_worker::Bucket::Done,
        }
    };
    crate::multi_worker::with_workers(|workers| {
        crate::multi_worker::call(
            workers.expect("declare_files_on_workers: no workers"),
            "Direct_decl_service.parse",
            |_, out: Vec<(usize, ParsedNames)>, ()| {
                for (i, names) in out {
                    per_file[i] = Some(names);
                }
            },
            (),
            &mut next,
        )
    });
    // The names, in the order of the paths, and the duplicates.
    let mut seen: std::collections::HashMap<(u8, String), usize> = Default::default();
    for names in per_file.iter().flatten() {
        for (kind, name) in &names.decls {
            *seen.entry(kind.binding_key(name)).or_default() += 1;
        }
    }
    let mut occurrences: Vec<(DeclKind, String, RelativePath)> = vec![];
    let mut infos = vec![];
    for (path, names) in paths.iter().zip(per_file) {
        let Some(names) = names else { continue };
        ctx.bind_file_names(*path, &names.decls);
        for (kind, name) in &names.decls {
            if seen[&kind.binding_key(name)] > 1 {
                occurrences.push((*kind, name.clone(), *path));
            }
        }
        if let Some(info) = names.info {
            infos.push((*path, info));
        }
    }
    if !occurrences.is_empty() {
        ctx.store_winners_of_duplicates(&occurrences, &|path| {
            let text = ctx.files.get(path).unwrap_or_default();
            ctx.decl_parser.parse_with_text(path, &text).unwrap_or_default()
        });
    }
    infos
}

/// What a clone gives of a file it declared.
#[cfg(feature = "server")]
#[derive(serde::Serialize, serde::Deserialize)]
pub struct ParsedNames {
    /// The kinds and names of the decls, in their order.
    decls: Vec<(crate::ctx::DeclKind, String)>,
    /// `Direct_decl_parser.decls_to_fileinfo`, if asked for.
    info: Option<crate::file_info::T>,
}

/// The input of a declaration job.
#[cfg(feature = "server")]
#[derive(serde::Serialize, serde::Deserialize)]
pub struct DeclareInput {
    ctx: crate::ctx::WorkerSnapshot,
    paths: Vec<(usize, crate::relative_path::RelativePath)>,
    want_infos: bool,
}

/// `Direct_decl_service.parse` in a worker's clone: each file parsed, its
/// decls added to the shared heap (`Direct_decl_utils.cache_decls`), the
/// kinds and names (and file infos) sent back. A file that cannot be read
/// declares nothing.
#[cfg(feature = "server")]
pub fn declare_job(input: DeclareInput) -> Vec<(usize, ParsedNames)> {
    let ctx = Ctx::of_worker_snapshot(input.ctx).expect("Direct_decl_service.parse: the worker's context");
    let mut out = vec![];
    for (i, path) in input.paths {
        let path = RelativePath::from(&path);
        let Ok(text) = ctx.files.get(path) else { continue };
        let hashed_file = ctx.decl_parser.parse_impl(path, &text);
        let info = input
            .want_infos
            .then(|| crate::direct_decl_service::decls_to_fileinfo(&path.into(), &hashed_file));
        let decls: Vec<ty::decl::shallow::NamedDecl<crate::ctx::R>> = hashed_file
            .into_iter()
            .map(|(name, decl, _)| ty::decl::shallow::NamedDecl::from((name, decl)))
            .collect();
        let names = decls
            .iter()
            .map(|d| {
                let (k, n) = crate::ctx::DeclKind::of_decl(d);
                (k, n.to_string())
            })
            .collect();
        ctx.add_parsed_decls(decls);
        out.push((i, ParsedNames { decls: names, info }));
    }
    out
}

/// [`declare_files`], giving the file infos of the files declared
/// (`Direct_decl_parser.decls_to_fileinfo`), in the order of the paths.
#[cfg(feature = "port")]
pub fn declare_files_with_infos(
    ctx: &Ctx,
    paths: &[RelativePath],
    stats: &mut Stats,
) -> Vec<(RelativePath, crate::file_info::T)> {
    #[cfg(feature = "server")]
    if crate::multi_worker::has_workers() {
        if let Some(snapshot) = ctx.worker_snapshot() {
            let start = Instant::now();
            let infos = declare_files_on_workers(ctx, snapshot, paths, true);
            stats.decl_time += start.elapsed();
            return infos;
        }
    }
    let infos: std::sync::Mutex<Vec<(RelativePath, crate::file_info::T)>> = Default::default();
    let on_file = |path: RelativePath, hashed_file: &oxidized::direct_decl_parser::ParsedFileWithHashes| {
        let info = crate::direct_decl_service::decls_to_fileinfo(&path.into(), hashed_file);
        infos.lock().unwrap_or_else(|e| e.into_inner()).push((path, info));
    };
    declare_files_on_threads(ctx, paths, stats, Some(&on_file));
    infos.into_inner().unwrap_or_else(|e| e.into_inner())
}

/// [`declare_files`] on the threads of the pool (see its documentation).
fn declare_files_on_threads(
    ctx: &Ctx,
    paths: &[RelativePath],
    stats: &mut Stats,
    on_file: Option<&(dyn Fn(RelativePath, &oxidized::direct_decl_parser::ParsedFileWithHashes) + Sync)>,
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
                let decls = match on_file {
                    // The decls with their hashes, for the file infos of the
                    // daemon's naming table (as the OCaml's parse gives them).
                    Some(on_file) => {
                        let hashed_file = ctx.decl_parser.parse_impl(path, &text);
                        on_file(path, &hashed_file);
                        hashed_file
                            .into_iter()
                            .map(|(name, decl, _)| ty::decl::shallow::NamedDecl::from((name, decl)))
                            .collect()
                    }
                    None => match ctx.decl_parser.parse_with_text(path, &text) {
                        Ok(decls) => decls,
                        Err(_) => continue,
                    },
                };
                // When a name is declared twice, the first declaration
                // (in the order of the paths, not of the threads) wins.
                ctx.declare_file(path, decls);
            }
        });
    });
    stats.decl_time += start.elapsed();
}

/// [`declare_files`], also giving the decls of each file to `on_file` (the
/// daemon builds its forward naming table from them, so that the files are
/// parsed once).
pub fn declare_files_with(
    ctx: &Ctx,
    paths: &[RelativePath],
    stats: &mut Stats,
    on_file: &(dyn Fn(RelativePath, &oxidized::direct_decl_parser::ParsedFileWithHashes) + Sync),
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
}

fn check_file(ctx: &Ctx, path: RelativePath) -> FileResult {
    let text = match ctx.files.get(path) {
        Ok(text) => text,
        Err(_) => {
            return FileResult {
                diagnostics: vec![],
                bytes: 0,
            };
        }
    };
    let ox_path: Arc<relative_path::RelativePath> = Arc::new(path.into());
    // A bug in the checker must not take the whole run down with it.
    let checked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let named = parse::parse_and_name(ctx, &ox_path, &text);
        let mut diagnostics = named.diagnostics;
        for error in named.naming_errors {
            diagnostics.push(crate::naming_phase_error::to_user_diagnostic(error));
        }
        crate::nast_check::program_with_comments(
            ctx,
            &named.program,
            &named.comments,
            &mut diagnostics,
        );
        crate::typing_slice::check_program(ctx, &named.program, &named.comments, &mut diagnostics);
        // `HH_FIXME`s apply to the diagnostics of every phase.
        diagnostics.retain(|d| {
            !crate::diagnostics_helpers::is_fixmed(&named.comments.fixmes, &d.claim.0, d.code)
        });
        diagnostics
    }));
    let diagnostics = checked.unwrap_or_else(|panic| {
        let what = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap_or("unknown panic");
        let pos = oxidized::pos::Pos::from_lnum_bol_offset(ox_path.clone(), (1, 0, 0), (1, 0, 0));
        let internal_error = diagnostics_helpers::error(
            INTERNAL_ERROR,
            pos,
            format!("Internal error: the typechecker panicked: {}", what),
        );
        vec![internal_error]
    });
    FileResult {
        diagnostics,
        bytes: text.len(),
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
        all.extend(result.diagnostics);
    }
    diagnostics_helpers::sort_and_dedup(&mut all);
    stats.check_time += start.elapsed();
    all
}

/// The diagnostics of a file of `check_files_typed_by_file`: the
/// `Diagnostics.t` that `Typing_check_service.process_file` gives for it (by
/// the file each diagnostic is reported in, in the order they were reported),
/// without those that an `HH_FIXME` suppresses.
#[cfg(feature = "port")]
pub type FileDiagnostics = crate::diagnostics::T;

/// Phase 2 with the ported typechecker: `Typing_check_service.process_file`
/// for every file of `paths`, in parallel; the diagnostics of each file, in
/// the order of `paths`. A file with parse errors gets only those; any other
/// file is typechecked (`Typing_check_job.calc_errors_and_tast`). The
/// diagnostics that an `HH_FIXME` suppresses are dropped, as
/// `Diagnostics.get_diagnostic_list` does. The loop is the typing service's
/// (`typing_check_service::check_paths`); a panic while checking a file is
/// reported as an internal error of that file. The dependency edges
/// recorded, if any (`--save-64bit`), are flushed by each thread and
/// registered. `on_file_checked`, if given, is called on the calling thread
/// each time a file has been checked, with how many are, how many will be,
/// and a copy of the file's diagnostics.
///
/// The OCaml hands buckets of files to worker processes; here rayon threads
/// take the files one at a time. That is safe because the result is per file
/// and in the order of `paths`, whatever thread checked it.
#[cfg(feature = "port")]
pub fn check_files_typed_by_file(
    ctx: &Arc<Ctx>,
    paths: &[RelativePath],
    stats: &mut Stats,
    on_file_checked: Option<&mut dyn FnMut(usize, usize, FileDiagnostics)>,
) -> Vec<FileDiagnostics> {
    use crate::typing_check_service as tcs;
    let start = Instant::now();
    let total_count = paths.len();
    let checked = match on_file_checked {
        None => tcs::check_paths(ctx, paths, false, tcs::OnPanic::InternalError, None, false),
        Some(on_file_checked) => {
            // The calling thread is told of each file as it is finished.
            let mut done_count = 0;
            let mut during = |_stop: &dyn Fn(),
                              finished: &crossbeam_channel::Receiver<tcs::Finished>,
                              _wake: std::os::fd::RawFd| {
                while let Ok(Some((_, diagnostics))) = finished.recv() {
                    done_count += 1;
                    on_file_checked(done_count, total_count, diagnostics.unwrap_or_default());
                }
            };
            tcs::check_paths(
                ctx,
                paths,
                false,
                tcs::OnPanic::InternalError,
                Some(&mut during),
                true,
            )
        }
    };
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

/// `Shared_mem.init` and `ServerWorker.make` for a batch check of `root`
/// (`hh_server --check` as the OCaml; `hh check`, which shares its code): the
/// shared heap (sized by `config`), the decl stores of the contexts made from
/// now on on it, and `num_workers` worker processes, which get the path
/// prefixes set here (`Server_global_state`). `trace`: whether the workers
/// trace the dependency edges (see `check_declared_root`). Only with
/// `HH_RUST_WORKERS=1` (`multi_worker::workers_switched_on`): by default the
/// threads of the pool check, with the stores in this process (no shared
/// heap): the OCaml's `setup_server` makes the workers and the shared heap
/// they read; the threads read the stores directly (the fastest form, a peak
/// of 3.7-3.8 GB on Slack's code against the OCaml's 4.5 GB).
#[cfg(feature = "server")]
pub fn start_workers(
    root: &std::path::Path,
    hhi_root: &std::path::Path,
    num_workers: usize,
    trace: bool,
    config: &crate::shared_mem::Config,
) -> anyhow::Result<()> {
    if !crate::multi_worker::workers_switched_on() || crate::multi_worker::has_workers() {
        return Ok(());
    }
    crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, root);
    crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Hhi, hhi_root);
    crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Tmp, std::path::Path::new("/tmp"));
    let handle = match crate::hh_shared::get_handle() {
        Some(handle) => handle,
        None => crate::hh_shared::init(config, num_workers)?,
    };
    crate::ctx::use_shared_memory_stores(true);
    let workers = crate::server_worker::make(true, num_workers, &handle, trace)?;
    crate::multi_worker::set_workers(workers);
    Ok(())
}

/// The shared heap's configuration for the batch check of `root`
/// (`Server_config.sharedmem_config` of the root's `.hhconfig` and the
/// overrides).
#[cfg(feature = "server")]
pub fn sharedmem_config(
    root: &std::path::Path,
    cli_config_overrides: &[(String, String)],
) -> anyhow::Result<crate::shared_mem::Config> {
    crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, root);
    // (Silent: `check_options` loads it again, and says what it says once.)
    let (config, _local_config) = crate::server_config::load(true, "", cli_config_overrides)
        .map_err(|e| anyhow::anyhow!("{:?}", e))?;
    Ok(crate::server_config::sharedmem_config(&config))
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
    Ok((hh_config.common.opts, hh_config.common.ignored_paths))
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
        return crate::diagnostics::sort(
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
    // (With workers, the clones' too: every process counts.)
    #[cfg(feature = "server")]
    {
        let (i, c) = crate::worker_controller::clone_instructions_and_cycles();
        let (si, sc) = own_instructions_and_cycles();
        return (si + i, sc + c);
    }
    #[cfg(not(feature = "server"))]
    own_instructions_and_cycles()
}

/// Instructions retired and CPU cycles of this process so far.
#[cfg(feature = "port")]
fn own_instructions_and_cycles() -> (u64, u64) {
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
    check_declared_root(declare_root(root)?, only, hhi_root)
}

/// The files of a root once declared: the first phase of [`check_root`].
pub struct DeclaredRoot {
    root: std::path::PathBuf,
    ctx: Ctx,
    paths: Vec<RelativePath>,
    hhi_count: usize,
    stats: Stats,
}

impl DeclaredRoot {
    /// The hhi files, then the files of the root, in the order they are
    /// checked.
    pub fn paths(&self) -> &[RelativePath] {
        &self.paths
    }

    /// How many of [`DeclaredRoot::paths`] are hhi files.
    pub fn hhi_count(&self) -> usize {
        self.hhi_count
    }

    /// `Ctx::publish_canon_names` (nothing unless the stores are on the
    /// shared heap).
    #[cfg(feature = "port")]
    pub fn publish_canon_names(&self) {
        self.ctx.publish_canon_names()
    }
}

/// The first phase of [`check_root`]: every file is declared.
pub fn declare_root(root: Root) -> anyhow::Result<DeclaredRoot> {
    let Root {
        root,
        ctx,
        paths,
        hhi_count,
        ..
    } = root;
    let mut stats = Stats::default();
    declare_files(&ctx, &paths, &mut stats);
    Ok(DeclaredRoot {
        root,
        ctx,
        paths,
        hhi_count,
        stats,
    })
}

/// The second phase of [`check_root`]: the files of the root are checked
/// (those listed in `only`, if given). The hhi files are declared, but only
/// checked when the dependency edges are traced (see
/// [`check_declared_files`]).
pub fn check_declared_root(
    declared: DeclaredRoot,
    only: Option<&std::path::Path>,
    hhi_root: &std::path::Path,
) -> anyhow::Result<CheckedRoot> {
    let hhi_count = declared.hhi_count;
    let mut paths = declared.paths.clone();
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
    // `hh_server --check` typechecks the hhi files as the OCaml's full init
    // does (`server_main`); `hh check` checks only the files of the root,
    // because the hhi files report no diagnostic (only their dependency
    // edges show that they were checked): they are checked here only when
    // the edges are traced.
    #[cfg(feature = "port")]
    let first_checked = if traces_dep_edges(&declared.ctx) { 0 } else { hhi_count };
    #[cfg(not(feature = "port"))]
    let first_checked = hhi_count;
    Ok(check_declared_files(declared, &paths[first_checked..], hhi_root, None))
}

/// Whether the check of a root traces the dependency edges: the workers of
/// the OCaml's check mode trace them (they copy `Typing_deps.trace` before
/// `Server_env_build.make_genv` turns it off for the master); only
/// `SaveToDiskMode` (`--save-64bit`) makes that observable, so only then
/// are they traced here.
///
/// Not in the OCaml: `HH_RECORD_EDGES_TO=FILE` records the edges in memory,
/// as the daemon does (`InMemoryMode`, `trace` on), and saves the delta to
/// FILE at the end (`Typing_deps.save_discovered_edges`, the format of
/// `--save-64bit`): to test and measure the daemon's recording with the
/// batch check.
#[cfg(feature = "port")]
fn traces_dep_edges(ctx: &Ctx) -> bool {
    matches!(ctx.deps_mode, crate::typing_deps::mode::T::SaveToDiskMode { .. })
        || std::env::var_os("HH_RECORD_EDGES_TO").is_some()
}

/// The second phase of a check: `files` (of the declared root) are checked.
/// `on_file_checked`, if given, is called on the calling thread each time a
/// file has been checked (see [`check_files_typed_by_file`]).
pub fn check_declared_files(
    declared: DeclaredRoot,
    files: &[RelativePath],
    hhi_root: &std::path::Path,
    #[cfg(feature = "port")] on_file_checked: Option<&mut dyn FnMut(usize, usize, FileDiagnostics)>,
    #[cfg(not(feature = "port"))] on_file_checked: Option<&mut dyn FnMut(usize, usize, Vec<Diagnostic>)>,
) -> CheckedRoot {
    let DeclaredRoot {
        root,
        ctx,
        paths: _,
        hhi_count: _,
        mut stats,
    } = declared;
    #[cfg(not(feature = "port"))]
    let diagnostics = {
        let _ = (&root, hhi_root, on_file_checked);
        check_files(&ctx, files, &mut stats)
    };
    #[cfg(feature = "port")]
    let diagnostics = {
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, &root);
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Hhi, hhi_root);
        crate::relative_path::set_path_prefix(
            crate::relative_path::Prefix::Tmp,
            std::path::Path::new("/tmp"),
        );
        if traces_dep_edges(&ctx) {
            crate::typing_deps::TRACE.store(true, std::sync::atomic::Ordering::Relaxed);
        }
        let record_edges_to = std::env::var_os("HH_RECORD_EDGES_TO");
        // The canon names the workers read (nothing without workers).
        ctx.publish_canon_names();
        let ctx = Arc::new(ctx);
        crate::hh_single_type_check::install(&ctx);
        crate::ast_provider::set_local_parser_cache_enabled(false);
        // `HH_PERF_INSTR=1`: print the instructions retired by the check phase.
        let (instr0, cycles0) = instructions_and_cycles();
        let diagnostics = check_files_typed_by_file(&ctx, files, &mut stats, on_file_checked);
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
    CheckedRoot { stats, diagnostics }
}
