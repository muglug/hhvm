// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_isolation.ml` (the `FIND_ISOLATABLE_CLUSTERS`
//! command). See `hh/PORTING.md`.
//!
//! Read top to bottom: where a run starts ([`seeds`]) and where its clusters
//! go ([`sink`]); the [`Run`] record both modes thread through; then the two
//! modes, each seed's closure first and clusters grown around them second; and
//! last [`make_run`], [`result`], [`query`] and [`go`], which choose a mode
//! and assemble the answer.
//!
//! `exception Server_isolation_memory.Below_floor`, raised wherever a run
//! checks its memory and handled in [`go`], is the `Err` of `BelowFloor`
//! threaded through the functions in between.

use std::cell::Cell;
use std::collections::BTreeMap;

use crate::naming_table;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_isolation_growth as growth;
use crate::server_isolation_inbound;
use crate::server_isolation_memory as memory;
use crate::server_isolation_memory::BelowFloor;
use crate::server_isolation_outbound;
use crate::server_isolation_types;
use crate::server_isolation_types::Cluster;
use crate::server_isolation_types::Mode;
use crate::typing_deps;
use crate::typing_deps::dep_set;

/// Which files a run starts growing from. A whole-repository scan finds the
/// files nothing references; a seed list or an entry-point family names them
/// instead, and those may well have references in — the cluster grown around
/// such a seed is what the question is about.
pub mod seeds {
    use super::*;

    /// A file is a seed when nothing outside it depends on any symbol it
    /// defines, compared in hash space so no naming-table lookup is needed.
    /// Only top-level hashes are known, so a dependent recorded at member
    /// granularity inside the file also counts as outside: the test can
    /// withhold seed status from a file that deserves it, never grant it to
    /// one that does not.
    pub fn has_external_dependents(
        deps_mode: &typing_deps::mode::T,
        file_info: &crate::file_info::T,
    ) -> bool {
        let own = dep_set::of_list(&typing_deps::deps_of_file_info(file_info));
        let dependents = typing_deps::add_typing_deps(deps_mode, &own);
        !dep_set::is_empty(&dep_set::diff(&dependents, &own))
    }

    /// Paths the typechecker already excludes, per [package_exclude_patterns].
    ///
    /// A test is the perfect seed and a useless one — nothing depends on it,
    /// so it always passes the seed test — and on a whole-repository scan they
    /// are a large share of what is found. This filters where seeds are
    /// scanned for, not what may end up inside a cluster: a test still has to
    /// join the cluster holding the code it exercises, since strict isolation
    /// switches off the exemption these patterns otherwise grant.
    ///
    /// Returns the test rather than performing it, so the patterns compile
    /// once rather than once per file in the repository.
    pub fn excluded_path_filter(
        ctx: &provider_context::T,
    ) -> impl Fn(&RelativePath) -> bool + use<> {
        use crate::rt::ocaml_str;
        let patterns: Vec<ocaml_str::Regexp> = provider_context::get_tcopt(ctx)
            .tco_package_exclude_patterns
            .iter()
            .map(|s| match ocaml_str::regexp(s) {
                Ok(re) => re,
                Err(ocaml_str::Failure(msg)) => panic!("{}", msg),
            })
            .collect();
        move |path: &RelativePath| {
            let filename = relative_path::to_absolute(path);
            patterns
                .iter()
                .any(|pattern| ocaml_str::string_match(pattern, &filename, 0))
        }
    }

    pub fn scan(
        ctx: &provider_context::T,
        deps_mode: &typing_deps::mode::T,
        naming_table: &naming_table::T,
    ) -> Vec<RelativePath> {
        let is_excluded_path = excluded_path_filter(ctx);
        // One whole-repo naming table scan, unavoidable for a whole-repo
        // query. The [file_info] it yields is used in place; re-deriving it
        // per file would cost a SQLite SELECT each.
        let mut seeds = naming_table::fold(
            Some(false),
            naming_table,
            vec![],
            |path, file_info, mut seeds: Vec<RelativePath>| {
                if relative_path::is_root(relative_path::prefix(path))
                    && !is_excluded_path(path)
                    && !has_external_dependents(deps_mode, file_info)
                {
                    seeds.push(path.clone());
                }
                seeds
            },
        );
        seeds.sort_by(relative_path::compare);
        seeds
    }

    /// Every subclass of [base], less the base itself: it defines the family
    /// rather than belonging to it, and is the one member nothing can
    /// isolate.
    ///
    /// [add_extend_deps] walks inheritance recursively, so one call gives the
    /// whole family rather than direct children. The name is normalised to a
    /// leading backslash, which is how the graph spells a top-level class and
    /// not how a caller types one.
    pub fn from_framework(
        ctx: &provider_context::T,
        deps_mode: &typing_deps::mode::T,
        keep_excluded_paths: bool,
        base: &str,
    ) -> Vec<RelativePath> {
        let base = if base.starts_with('\\') {
            base.to_string()
        } else {
            format!("\\{}", base)
        };
        let root = dep_set::singleton(typing_deps::dep::make(&typing_deps::dep::Variant::Type(
            base.clone(),
        )));
        let family = typing_deps::add_extend_deps(deps_mode, &root);
        let is_excluded_path = excluded_path_filter(ctx);
        let base_files = crate::naming_provider::get_files(ctx, &root);
        let paths: Vec<RelativePath> = crate::naming_provider::get_files(ctx, &family)
            .into_iter()
            .filter(|path| {
                relative_path::is_root(relative_path::prefix(path))
                    && (keep_excluded_paths || !is_excluded_path(path))
                    && !base_files.contains(path)
            })
            .collect();
        crate::hh_logger::log(&format!(
            "[isolation] seed framework: {}, {} subclasses",
            base,
            paths.len()
        ));
        if paths.is_empty() {
            crate::hh_logger::log(&format!(
                "[isolation] seed framework: {} resolved to nothing — is the name right, and fully qualified?",
                base
            ));
        }
        paths
    }

    /// Order preserved, so a seed window over a list without repeats selects
    /// the same slice as before.
    pub fn dedupe(paths: &[RelativePath]) -> Vec<RelativePath> {
        let mut seen = relative_path::set::T::new();
        let mut acc = vec![];
        for path in paths {
            if !seen.contains(path) {
                acc.push(path.clone());
                seen.insert(path.clone());
            }
        }
        acc
    }

    /// [paths] less the repeats and less what the naming table does not know,
    /// both counted out loud under [seed_source].
    ///
    /// A path the naming table does not know is dropped rather than grown
    /// from: it would look like a file that references nothing, and report as
    /// an isolatable cluster of one. Silently wrong beats loudly wrong here. A
    /// repeat would be grown twice and the second cluster discarded for
    /// overlapping the first, which is indistinguishable in the counters from
    /// two distinct seeds colliding.
    pub fn known_paths(
        naming_table: &naming_table::T,
        seed_source: &str,
        paths: &[RelativePath],
    ) -> Vec<RelativePath> {
        let deduped = dedupe(paths);
        let repeated = paths.len() - deduped.len();
        if repeated > 0 {
            crate::hh_logger::log(&format!(
                "[isolation] {}: {} repeated paths ignored",
                seed_source, repeated
            ));
        }
        let (known, unknown): (Vec<RelativePath>, Vec<RelativePath>) = deduped
            .into_iter()
            .partition(|path| naming_table::get_file_info(naming_table, path).is_some());
        crate::hh_logger::log(&format!(
            "[isolation] {}: {} paths, {} unknown to the naming table",
            seed_source,
            known.len(),
            unknown.len()
        ));
        known
    }

    /// `String.strip` (Base): without the leading and trailing whitespace
    /// (`Char.is_whitespace`).
    fn strip(s: &str) -> &str {
        s.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r'))
    }

    /// The paths of the lines of [contents]: one per line, blank lines
    /// skipped (`In_channel.read_lines` then the filter of [from_list]).
    pub fn paths_of_lines(contents: &str) -> Vec<RelativePath> {
        // `In_channel.read_lines`: no empty last line after a final newline;
        // the `\r` it strips from a `\r\n` is whitespace to [strip] anyway.
        crate::rt::ocaml_string::split_lines(contents)
            .into_iter()
            .filter_map(|line| match strip(&line) {
                "" => None,
                suffix => Some(relative_path::from_root(suffix)),
            })
            .collect()
    }

    /// The repo-relative paths in [file], one per line, taken as given: no
    /// path is dropped for being a test or excluded.
    pub fn from_list(naming_table: &naming_table::T, file: &str) -> Vec<RelativePath> {
        let contents = match std::fs::read(file) {
            Ok(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
            Err(e) => panic!("{}", crate::sys_utils::SysError::of_io_error(file, &e)),
        };
        known_paths(
            naming_table,
            &format!("seed list {}", file),
            &paths_of_lines(&contents),
        )
    }

    pub fn absolute_dir(dir: &str) -> String {
        let root = match relative_path::path_of_prefix(relative_path::Prefix::Root) {
            Ok(root) => root,
            Err(relative_path::InvalidArgument(message)) => {
                panic!("Invalid_argument: {}", message)
            }
        };
        crate::rt::ocaml_filename::concat(&root, dir)
    }

    /// Every Hack file under [dir], which is repo-relative. [dir] is a
    /// directory: [query] refuses the run before reaching here otherwise.
    ///
    /// The same walk the typechecker indexes the repository with, so it finds
    /// the same files under [dir] that the naming table holds, and is then
    /// filtered against the table exactly as a hand-written seed list is.
    pub fn from_directory(
        ctx: &provider_context::T,
        naming_table: &naming_table::T,
        keep_excluded_paths: bool,
        dir: &str,
    ) -> Vec<RelativePath> {
        let is_excluded_path = excluded_path_filter(ctx);
        let mut paths: Vec<RelativePath> = crate::find::find(
            None,
            Some(&crate::find_utils::file_filter),
            Some(true),
            &[crate::path::make(&absolute_dir(dir))],
        )
        .iter()
        .map(|s| relative_path::create_detect_prefix(s))
        .filter(|path| {
            relative_path::is_root(relative_path::prefix(path))
                && (keep_excluded_paths || !is_excluded_path(path))
        })
        .collect();
        paths.sort_by(relative_path::compare);
        known_paths(naming_table, &format!("seed dir {}", dir), &paths)
    }

    /// [keep_excluded_paths] turns off the test filter, which is a
    /// seed-finding heuristic and not part of any question about a named set
    /// of files. A directory's own tests move with it, so dropping them would
    /// both shrink the package and report each of them as referencing in.
    pub fn select(
        ctx: &provider_context::T,
        deps_mode: &typing_deps::mode::T,
        naming_table: &naming_table::T,
        keep_excluded_paths: bool,
        seed_framework: Option<&str>,
        seed_list: Option<&str>,
        seed_dir: Option<&str>,
    ) -> Vec<RelativePath> {
        match (seed_framework, seed_list, seed_dir) {
            (Some(base), _, _) => from_framework(ctx, deps_mode, keep_excluded_paths, base),
            (None, Some(file), _) => from_list(naming_table, file),
            (None, None, Some(dir)) => from_directory(ctx, naming_table, keep_excluded_paths, dir),
            (None, None, None) => {
                let seeds = scan(ctx, deps_mode, naming_table);
                crate::hh_logger::log(&format!(
                    "[isolation] seed scan: found {} seeds",
                    seeds.len()
                ));
                seeds
            }
        }
    }

    pub fn window(
        all_seeds: &[RelativePath],
        seed_offset: isize,
        max_seeds: Option<isize>,
    ) -> Vec<RelativePath> {
        // `List.drop` and `List.take` (Base): a count past the end takes or
        // drops everything, a negative one nothing.
        let seeds =
            &all_seeds[std::cmp::min(std::cmp::max(seed_offset, 0) as usize, all_seeds.len())..];
        match max_seeds {
            None => seeds.to_vec(),
            Some(n) => seeds[..std::cmp::min(std::cmp::max(n, 0) as usize, seeds.len())].to_vec(),
        }
    }

    pub fn log_window(
        total_seeds: isize,
        seed_offset: isize,
        max_seeds: Option<isize>,
        available: isize,
    ) {
        if seed_offset > 0 || max_seeds.is_some() {
            crate::hh_logger::log(&format!(
                "[isolation] seed window: {} seeds from offset {} (of {})",
                total_seeds, seed_offset, available
            ));
        }
    }
}

/// Where a cluster goes as soon as it is known. In memory for a small run;
/// one JSON object per line for a large one, where carrying every cluster back
/// through the RPC would put them all in memory before the server could
/// reply.
pub mod sink {
    use std::cell::RefCell;
    use std::io::Write;
    use std::rc::Rc;

    use super::*;

    pub struct T {
        pub emit: Box<dyn Fn(&Cluster)>,
        pub close: Box<dyn Fn()>,
    }

    // The leading components two paths agree on.
    pub fn common_prefix(a: &[String], b: &[String]) -> Vec<String> {
        a.iter()
            .zip(b.iter())
            .take_while(|(x, y)| x == y)
            .map(|(x, _)| x.clone())
            .collect()
    }

    /// Longest directory prefix shared by every file, "" when there is none.
    pub fn common_directory(files: &[RelativePath]) -> String {
        let dirs: Vec<Vec<String>> = files
            .iter()
            .map(|path| {
                // [Filename.dirname] answers "." for a file at the root, which
                // would otherwise render as a "./" prefix.
                match crate::rt::ocaml_filename::dirname(&relative_path::suffix(path)).as_str() {
                    "." => vec![],
                    dir => dir.split('/').map(str::to_string).collect(),
                }
            })
            .collect();
        match dirs.split_first() {
            None => "".to_string(),
            Some((first, rest)) => {
                match rest
                    .iter()
                    .fold(first.clone(), |acc, dir| common_prefix(&acc, dir))
                    .as_slice()
                {
                    [] => "".to_string(),
                    shared => format!("{}/", shared.join("/")),
                }
            }
        }
    }

    /// For a run nobody asked the clusters from: counted in the summary, then
    /// dropped. Stateless, so there is one of it.
    pub fn discard() -> T {
        T {
            emit: Box::new(|_| ()),
            close: Box::new(|| ()),
        }
    }

    /// The line [to_file] writes for [cluster].
    pub fn cluster_line(grow: bool, cluster: &Cluster) -> String {
        use crate::yojson::safe;
        safe::to_string(&safe::T::Assoc(vec![
            (
                "files".to_string(),
                safe::T::List(
                    cluster
                        .files
                        .iter()
                        .map(|f| safe::T::String(f.clone()))
                        .collect(),
                ),
            ),
            (
                "size".to_string(),
                safe::T::Int(cluster.files.len() as isize),
            ),
            (
                "common_directory".to_string(),
                safe::T::String(cluster.common_directory.clone()),
            ),
            ("grown".to_string(), safe::T::Bool(grow)),
            ("truncated".to_string(), safe::T::Bool(cluster.truncated)),
        ]))
    }

    // [grown] is recorded on every line because both modes write sets of
    // files called clusters to the same place, and they mean different things:
    // the smallest isolatable set around a file, or that set grown as far as
    // the bounds allow. A file that says which can be read without knowing the
    // command that produced it.
    pub fn to_file(grow: bool, path: &str) -> T {
        let sys_error = |e: std::io::Error| -> ! {
            panic!("{}", crate::sys_utils::SysError::of_io_error(path, &e))
        };
        let out = match std::fs::File::create(path) {
            Ok(out) => out,
            Err(e) => sys_error(e),
        };
        let out = Rc::new(RefCell::new(Some(out)));
        let out_for_close = Rc::clone(&out);
        let path_for_emit = path.to_string();
        T {
            emit: Box::new(move |cluster| {
                let line = cluster_line(grow, cluster);
                let mut out = out.borrow_mut();
                let Some(out) = out.as_mut() else {
                    panic!("Sys_error(\"Bad file descriptor\")")
                };
                // Flushed per cluster, not left to [close_out]: a family-sized
                // run can be killed partway, and a buffer the process never
                // writes takes the last clusters with it. (Written unbuffered
                // here: one write per line.)
                let mut bytes = line.into_bytes();
                bytes.push(b'\n');
                if let Err(e) = out.write_all(&bytes).and_then(|()| out.flush()) {
                    panic!(
                        "{}",
                        crate::sys_utils::SysError::of_io_error(&path_for_emit, &e)
                    )
                }
            }),
            // The caller is reading the file, so returning them as well would
            // put back the memory this exists to avoid.
            close: Box::new(move || drop(out_for_close.borrow_mut().take())),
        }
    }
}

/// What a query threads through: the providers it reads, the bounds it runs
/// under, where its clusters go, and the two tallies only the caller of
/// growth can keep.
pub struct Run<'a> {
    ctx: provider_context::T,
    workers: Option<usize>,
    deps_mode: crate::typing_deps_mode::T,
    naming_table: &'a naming_table::T,
    sink: &'a sink::T,
    max_dependents: isize,
    max_cluster_size: Option<isize>,
    batch_size: isize,
    memory_guard: memory::Guard,
    /// Clusters dropped because an earlier cluster in the same batch already
    /// claimed one of their files. Counted here rather than in growth: growth
    /// reports each cluster it grew, and whether two of them overlap is only
    /// knowable once they are collected.
    overlapping_clusters: Cell<isize>,
    /// Starting files in no cluster: when measuring, because
    /// [closure_of_seed] found none for them; when growing, because no
    /// reported cluster took them.
    refused_seeds: Cell<isize>,
    /// Clusters the cap refused a candidate they would otherwise have taken.
    /// They stopped short of closing, so they are prefixes of packages rather
    /// than packages, and a consumer that treats one as finished will find
    /// files outside it referencing in. Counted so a run says how much of its
    /// output is in that state.
    truncated_clusters: Cell<isize>,
}

fn incr(c: &Cell<isize>) {
    c.set(c.get() + 1)
}

/// Stops the run, by raising, when the machine is running out of memory.
/// Called wherever a run could be using more of it than a moment ago,
/// including in the workers, which are sent this function: it holds the guard
/// and nothing else of the run.
fn check_memory(r: &Run<'_>) -> impl Fn() -> Result<(), BelowFloor> + Sync + use<> {
    let guard = r.memory_guard;
    move || memory::check(&guard)
}

pub fn median(sizes: &[isize]) -> isize {
    let mut sorted = sizes.to_vec();
    sorted.sort();
    match sorted.as_slice() {
        [] => 0,
        sorted => sorted[sorted.len() / 2],
    }
}

pub fn histogram(
    sizes: &[isize],
    bucket: impl Fn(isize) -> isize,
    label: impl Fn(isize, isize) -> String,
) -> String {
    let mut acc: BTreeMap<isize, isize> = BTreeMap::new();
    for n in sizes {
        *acc.entry(bucket(*n)).or_insert(0) += 1;
    }
    acc.into_iter()
        .map(|(b, count)| label(b, count))
        .collect::<Vec<_>>()
        .join(" ")
}

// Bucket boundaries for the size histogram: fine at the bottom, where most
// closures fall, and wide at the top, where they span orders of magnitude. A
// list of raw sizes carries the same information and shows none of its shape.
const CLOSURE_BUCKETS: [isize; 8] = [1, 2, 5, 10, 50, 100, 500, 2000];

// Anything past the last bucket shares one. [max_value] keys it so it sorts
// last, and is never printed — the label says what it actually means.
pub fn closure_bucket(n: isize) -> isize {
    CLOSURE_BUCKETS
        .iter()
        .copied()
        .find(|bucket| n <= *bucket)
        .unwrap_or(isize::MAX)
}

// [closure_buckets] holds upper bounds only, so a range starts one past the
// previous bound: 1, 2, 3-5, 6-10, and so on.
fn closure_ranges() -> Vec<(isize, isize)> {
    let mut lower = 1;
    CLOSURE_BUCKETS
        .iter()
        .map(|&upper| {
            let range = (lower, upper);
            lower = upper + 1;
            range
        })
        .collect()
}

pub fn closure_label(bucket: isize, count: isize) -> String {
    if bucket == isize::MAX {
        format!(
            "{}+:{}",
            CLOSURE_BUCKETS[CLOSURE_BUCKETS.len() - 1] + 1,
            count
        )
    } else {
        match closure_ranges()
            .into_iter()
            .find(|(_, upper)| *upper == bucket)
        {
            Some((lower, upper)) if lower == upper => format!("{}:{}", upper, count),
            Some((lower, upper)) => format!("{}-{}:{}", lower, upper, count),
            None => format!("{}:{}", bucket, count),
        }
    }
}

fn cluster_of_files(files: &[RelativePath], truncated: bool) -> Cluster {
    Cluster {
        files: files.iter().map(relative_path::suffix).collect(),
        common_directory: sink::common_directory(files),
        truncated,
    }
}

/// One seed's closure, emitted and released; [None] when the walk refused
/// it.
fn closure_of_seed(r: &Run<'_>, path: &RelativePath) -> Option<isize> {
    match server_isolation_inbound::get(&r.ctx, r.naming_table, r.max_dependents, path) {
        None => None,
        Some(closure) => {
            let files: Vec<RelativePath> = closure.iter().cloned().collect();
            // Nothing grew, so no cap refused anything.
            (r.sink.emit)(&cluster_of_files(&files, false));
            server_isolation_inbound::release_closures();
            Some(files.len() as isize)
        }
    }
}

/// Reported as the run goes so one that is killed still says where the
/// memory was going, which the single line at the end cannot.
fn log_closure_progress(done_count: isize, total_seeds: isize, fitted_count: isize) {
    crate::hh_logger::log(&format!(
        "[isolation] closure report: {}/{} seeds | {} isolatable | heap {:.1}GiB rss {:.1}GiB",
        done_count,
        total_seeds,
        fitted_count,
        memory::heap_gib(),
        memory::rss_gib()
    ))
}

fn log_closure_report(total_seeds: isize, closure_sizes: &[isize]) {
    crate::hh_logger::log(&format!(
        "[isolation] closure report: {} files | {} isolatable ({:.1}%) | median {} | largest {} | buckets {}",
        total_seeds,
        closure_sizes.len(),
        100.0 * closure_sizes.len() as f64 / std::cmp::max(1, total_seeds) as f64,
        median(closure_sizes),
        closure_sizes.iter().copied().fold(0, std::cmp::max),
        histogram(closure_sizes, closure_bucket, closure_label)
    ))
}

/// Measure each seed's isolatability: walk its closure, emit it, and return
/// the sizes. The closure is what "is this file isolatable, and what would it
/// cost" means. A refused seed counts as not isolatable, which is the
/// question's own definition — except where the walk's hash guard refuses a
/// closure that would have fitted in files, which is why these figures are a
/// lower bound.
///
/// Emitted and released one at a time; only the sizes are needed after.
/// Compacted periodically because the walk's dependency sets live behind a
/// Rust custom block, so the OCaml collector barely notices them. [compact]
/// rather than [full_major] to hand memory back to the operating system.
fn measure_seeds(
    r: &Run<'_>,
    seeds: &[RelativePath],
    total_seeds: isize,
) -> Result<Vec<isize>, BelowFloor> {
    // Large enough that walking the whole heap is not what the run spends its
    // time on.
    let seeds_between_compactions = 2000;
    // On a clock rather than per compaction: a run with fewer seeds than that
    // would otherwise report nothing until it finished.
    let seconds_between_reports = 60.0;
    let gettimeofday = crate::rt::ocaml_unix::gettimeofday;
    let done_count = Cell::new(0);
    let fitted_count = Cell::new(0);
    let last_report = Cell::new(gettimeofday());
    let report = || {
        last_report.set(gettimeofday());
        log_closure_progress(done_count.get(), total_seeds, fitted_count.get())
    };
    let report_if_due = || -> Result<(), BelowFloor> {
        if gettimeofday() - last_report.get() > seconds_between_reports {
            check_memory(r)()?;
            report();
        }
        Ok(())
    };
    let measure_one_seed = |seed: &RelativePath| -> Result<Option<isize>, BelowFloor> {
        let size = closure_of_seed(r, seed);
        incr(&done_count);
        if size.is_some() {
            incr(&fitted_count)
        } else {
            incr(&r.refused_seeds)
        }
        report_if_due()?;
        Ok(size)
    };
    let measure_then_compact = |seeds: &[RelativePath]| -> Result<Vec<isize>, BelowFloor> {
        let mut measured_sizes = vec![];
        for seed in seeds {
            if let Some(size) = measure_one_seed(seed)? {
                measured_sizes.push(size)
            }
        }
        // (`Gc.compact ()`: the dependency sets are freed when they are
        // dropped.)
        Ok(measured_sizes)
    };
    let mut measured_sizes = vec![];
    for chunk in seeds.chunks(seeds_between_compactions) {
        measured_sizes.extend(measure_then_compact(chunk)?);
    }
    report();
    log_closure_report(total_seeds, &measured_sizes);
    Ok(measured_sizes)
}

fn log_growth_progress(grown: isize, total_seeds: isize, since: f64) {
    let growth::stats::T {
        index_seconds,
        absorb_seconds,
        candidates_tested,
        absorbed_by_closure,
        ..
    } = growth::stats();
    crate::hh_logger::log(&format!(
        "[isolation] growth: {}/{} seeds | index {:.1}s ({} files) | absorb {:.1}s ({} candidates, {} by closure) | closures {} computed {} served {} refused | heap {:.1}GiB | rss {:.1}GiB | total {:.1}s",
        grown,
        total_seeds,
        index_seconds,
        server_isolation_outbound::files_indexed(),
        absorb_seconds,
        candidates_tested,
        absorbed_by_closure,
        server_isolation_inbound::closures_computed(),
        server_isolation_inbound::closures_served(),
        server_isolation_inbound::refusals_held(),
        memory::heap_gib(),
        memory::rss_gib(),
        crate::rt::ocaml_unix::gettimeofday() - since
    ))
}

/// Logged as well as returned, since a long run outlives its client.
fn log_growth_result(r: &Run<'_>, sizes: &[isize]) {
    let growth::stats::T {
        absorbed_by_subset,
        absorbed_by_closure,
        ..
    } = growth::stats();
    crate::hh_logger::log(&format!(
        "[isolation] result: {} clusters ({} truncated) | {} files | median {} | largest {} | subset {} closure {} | dropped {} | sizes {}",
        sizes.len(),
        r.truncated_clusters.get(),
        sizes.iter().sum::<isize>(),
        median(sizes),
        sizes.iter().copied().fold(0, std::cmp::max),
        absorbed_by_subset,
        absorbed_by_closure,
        r.overlapping_clusters.get(),
        histogram(sizes, |n| n, |b, count| format!("{}:{}", b, count))
    ))
}

/// The sizes of the clusters reported so far (in the order they were
/// reported), the seeds they account for, and every file they hold.
type Collected = (Vec<isize>, relative_path::set::T, relative_path::set::T);

/// One grown cluster against what the clusters before it took. Clusters in
/// one batch share a [claimed] snapshot, so two can take the same file.
/// Trimming the overlap out of one would leave it with an inbound edge from
/// the file it lost, so the later cluster is dropped whole.
fn collect_cluster(
    r: &Run<'_>,
    (mut clusters, visited, claimed): Collected,
    grown: growth::Grown,
) -> Collected {
    let growth::Grown {
        seed: _,
        files: cluster,
        truncated,
    } = grown;
    if !cluster.clone().intersection(claimed.clone()).is_empty() {
        // [visited] is left alone. A dropped cluster was never reported, so
        // its files are in no package, and marking them would retire seeds
        // that no output accounts for — a later batch tests against a larger
        // [claimed] and may grow one of them into a cluster that does not
        // overlap.
        incr(&r.overlapping_clusters);
        (clusters, visited, claimed)
    } else {
        let visited = visited.union(cluster.clone());
        let files: Vec<RelativePath> = cluster.iter().cloned().collect();
        let claimed = claimed.union(cluster);
        if truncated {
            incr(&r.truncated_clusters)
        }
        (r.sink.emit)(&cluster_of_files(&files, truncated));
        // `List.length files :: clusters`, reversed by [grow_seeds]: kept in
        // the order reported.
        clusters.push(files.len() as isize);
        (clusters, visited, claimed)
    }
}

/// One batch grown and collected, then everything the next batch will not ask
/// for again released.
fn grow_one_batch(
    r: &Run<'_>,
    max_dependents: isize,
    total_seeds: isize,
    since: f64,
    grown: &Cell<isize>,
    (clusters, visited, claimed): Collected,
    batch: &[RelativePath],
) -> Result<Collected, BelowFloor> {
    // A seed already absorbed by an earlier cluster is not its own cluster,
    // but it still counts towards progress: the denominator is every seed,
    // not just the ones that needed growing.
    grown.set(grown.get() + batch.len() as isize);
    let batch: Vec<RelativePath> = batch
        .iter()
        .filter(|seed| !visited.contains(*seed))
        .cloned()
        .collect();
    let grown_batch = growth::grow_batch(
        &r.ctx,
        r.workers,
        &r.deps_mode,
        r.naming_table,
        &claimed,
        r.max_cluster_size,
        max_dependents,
        &check_memory(r),
        &batch,
    )?;
    log_growth_progress(grown.get(), total_seeds, since);
    // This batch's clusters are at a fixed point, so nothing will ask for
    // their outbound edges again, and an accepted closure is cheap to
    // recompute if a later batch does. Refusals survive: they cost a full walk
    // and the files that earn them recur everywhere.
    server_isolation_outbound::release_cache();
    server_isolation_inbound::release_closures();
    growth::release_caches();
    Ok(grown_batch
        .into_iter()
        .fold((clusters, visited, claimed), |acc, g| {
            collect_cluster(r, acc, g)
        }))
}

/// Seeds are advanced in batches so each round's frontiers pool into one
/// parallel index call. Larger batches fill the worker pool better; they also
/// hold more clusters in memory at once, which is the trade-off
/// [--isolation-batch-size] sets.
fn grow_seeds(
    r: &Run<'_>,
    seeds: &[RelativePath],
    total_seeds: isize,
    since: f64,
) -> Result<Vec<isize>, BelowFloor> {
    // A closure larger than the whole cluster can never be absorbed, and the
    // walk is where growth spends its time. Clamped once per run, not per
    // candidate: the memo is keyed by path, so a varying bound would poison
    // it. Growth only — without [grow] the bound is the measurement.
    let max_dependents = match r.max_cluster_size {
        Some(cap) => std::cmp::min(r.max_dependents, cap),
        None => r.max_dependents,
    };
    crate::hh_logger::log(&format!(
        "[isolation] cluster growth: starting over {} seeds (closure bound {})",
        total_seeds, max_dependents
    ));
    // Caches are dropped between batches, so the batch sets how much memory a
    // run needs, not the length of the seed list.
    let batch_size = r.batch_size;
    if batch_size <= 0 {
        // `List.chunks_of` on a length that is not positive
        panic!("List.chunks_of: Expected length > 0, got {}", batch_size)
    }
    let grown = Cell::new(0);
    // [visited] stops a seed being grown twice; [claimed] is every file in a
    // cluster already reported.
    let mut acc: Collected = (
        vec![],
        relative_path::set::T::new(),
        relative_path::set::T::new(),
    );
    for batch in seeds.chunks(batch_size as usize) {
        acc = grow_one_batch(r, max_dependents, total_seeds, since, &grown, acc, batch)?;
    }
    let (sizes, visited, _claimed) = acc;
    // A seed no reported cluster took is one nothing could be grown around, or
    // whose cluster was dropped for overlapping an earlier one. Counted so the
    // summary accounts for every starting file, as the default mode's does.
    r.refused_seeds
        .set(seeds.iter().filter(|seed| !visited.contains(*seed)).count() as isize);
    let _t = crate::hh_logger::log_duration(None, None, "[isolation] cluster growth", since);
    log_growth_result(r, &sizes);
    Ok(sizes)
}

/// [movability_of_seeds r seeds] is whether [seeds], taken together, can move
/// as they stand, paired with the sizes of the clusters emitted: the whole
/// set as one cluster when movable, none when blocked.
fn movability_of_seeds(
    r: &Run<'_>,
    seeds: &[RelativePath],
) -> (server_isolation_types::Movability, Vec<isize>) {
    let candidate: relative_path::set::T = seeds.iter().cloned().collect();
    let since = crate::rt::ocaml_unix::gettimeofday();
    let blockers = server_isolation_inbound::referrers(&r.ctx, r.naming_table, &candidate);
    let _t = crate::hh_logger::log_duration(None, None, "[isolation] movability", since);
    if blockers.is_empty() {
        let files: Vec<RelativePath> = candidate.iter().cloned().collect();
        crate::hh_logger::log(&format!(
            "[isolation] movability: movable, {} files",
            files.len()
        ));
        (r.sink.emit)(&cluster_of_files(&files, false));
        (
            server_isolation_types::Movability::Movable,
            vec![files.len() as isize],
        )
    } else {
        let since = crate::rt::ocaml_unix::gettimeofday();
        let by_target =
            server_isolation_inbound::referrers_by_target(&r.ctx, r.naming_table, &candidate);
        let blockers: Vec<server_isolation_types::Blocker> = blockers
            .iter()
            .map(|referrer| {
                let references = by_target.get(referrer).cloned().unwrap_or_default();
                server_isolation_types::Blocker {
                    file: relative_path::suffix(referrer),
                    references: references.iter().map(relative_path::suffix).collect(),
                }
            })
            .collect();
        let _t =
            crate::hh_logger::log_duration(None, None, "[isolation] blockers by target", since);
        crate::hh_logger::log(&format!(
            "[isolation] movability: {} files reference in",
            blockers.len()
        ));
        (
            server_isolation_types::Movability::Blocked(blockers),
            vec![],
        )
    }
}

fn make_run<'a>(
    options: &server_isolation_types::Options,
    genv: &Genv,
    env: &'a Env,
    sink: &'a sink::T,
) -> Run<'a> {
    let server_isolation_types::Options {
        max_dependents,
        max_cluster_size,
        batch_size,
        min_free_memory_percent,
        max_memory_percent,
        ..
    } = *options;
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let deps_mode = provider_context::get_deps_mode(&ctx);
    Run {
        ctx,
        workers: crate::server_find_refs::workers(genv),
        deps_mode,
        naming_table: &env.naming_table,
        sink,
        max_dependents,
        max_cluster_size,
        batch_size,
        memory_guard: memory::guard(
            min_free_memory_percent,
            max_memory_percent,
            crate::memory_stats::get_mem_available(),
        ),
        overlapping_clusters: Cell::new(0),
        refused_seeds: Cell::new(0),
        truncated_clusters: Cell::new(0),
    }
}

/// What a run that did not happen reports: the reason, and nothing found.
fn refused(grow: bool, total_seeds: isize, message: String) -> server_isolation_types::Result {
    server_isolation_types::Result {
        refused: Some(message),
        movability: None,
        grown: grow,
        total_seeds,
        total_isolatable_files: 0,
        total_clusters: 0,
        total_truncated: 0,
        total_refused: 0,
        largest_cluster: 0,
    }
}

/// Each mode reports the sizes of the sets it found, and differs in nothing
/// else the caller sees, so the result is assembled here rather than at the
/// end of each branch.
fn result(
    r: &Run<'_>,
    grow: bool,
    movability: Option<server_isolation_types::Movability>,
    total_seeds: isize,
    sizes: &[isize],
) -> server_isolation_types::Result {
    server_isolation_types::Result {
        refused: None,
        movability,
        grown: grow,
        total_seeds,
        total_isolatable_files: sizes.iter().sum(),
        total_clusters: sizes.len() as isize,
        total_truncated: r.truncated_clusters.get(),
        total_refused: r.refused_seeds.get(),
        largest_cluster: sizes.iter().copied().fold(0, std::cmp::max),
    }
}

/// Refuse a run long enough that the caller should have meant it, and say how
/// to proceed. Reported rather than raised: the caller learns what to change
/// and the server stays up.
pub fn too_long_to_run(grow: bool, total_seeds: isize, allow_long_run: bool) -> Option<String> {
    // Seconds a seed costs, measured rather than derived. Rough on purpose:
    // here to tell an afternoon apart from a week, not to predict a runtime.
    let seconds_per_seed = if grow { 0.5 } else { 0.03 };
    // Past this the caller is told rather than left to find out. Two hours
    // still clears measuring a whole class hierarchy, and refuses growing one.
    let hours_before_asking = 2.0;
    let hours = total_seeds as f64 * seconds_per_seed / 3600.;
    if allow_long_run || hours <= hours_before_asking {
        None
    } else {
        // Big enough to read a rate off, small enough to come back while the
        // caller is still waiting. Growth costs about 17x what measuring does,
        // so the two differ.
        let sample = if grow { 400 } else { 5000 };
        let (verb, verb_all) = if grow {
            ("grows", "grow")
        } else {
            ("measures", "measure")
        };
        Some(format!(
            "{} seeds, which will take {}.\nSample it rather than covering it: --isolation-max-seeds {} {} {} seeds and stops, which is enough to see what fraction is isolatable. --isolation-seed-offset {} picks a different {}.\nOr pass --isolation-allow-long-run to {} all {}.",
            total_seeds,
            if hours >= 24. { "days" } else { "hours" },
            sample,
            verb,
            sample,
            sample * 3,
            sample,
            verb_all,
            total_seeds
        ))
    }
}

/// Refuse a seed source that cannot be read, before the run starts.
fn unreadable_seed_source(seed_list: Option<&str>, seed_dir: Option<&str>) -> Option<String> {
    // [Disk.file_exists] is true of a directory, which would read as a file
    // and raise the error this is here to prevent.
    let is_file = |path: &str| crate::disk::file_exists(path) && !crate::disk::is_directory(path);
    match (seed_list, seed_dir) {
        (Some(file), _) if !is_file(file) => Some(format!(
            "{} is not a file. --isolation-seed-list takes a file of repo-relative paths, one per line.",
            file
        )),
        (_, Some(dir)) if !crate::disk::is_directory(&seeds::absolute_dir(dir)) => Some(format!(
            "{} is not a directory. --isolation-seed-dir takes a path relative to the repository root.",
            dir
        )),
        _ => None,
    }
}

/// Refuse a named seed source that gave no files, which would otherwise
/// answer as an empty set that reads as a success: a framework with a
/// mistyped name, a directory with no Hack files, a list of paths the server
/// does not know.
pub fn empty_seed_source(
    seed_framework: Option<&str>,
    seed_list: Option<&str>,
    seed_dir: Option<&str>,
) -> Option<String> {
    match (seed_framework, seed_list, seed_dir) {
        (Some(base), _, _) => Some(format!(
            "{} has no subclasses to start from. --isolation-seed-framework takes a class name, fully qualified.",
            base
        )),
        (None, Some(file), _) => Some(format!(
            "none of the paths in {} is a Hack file the server knows.",
            file
        )),
        (None, None, Some(dir)) => Some(format!("{} has no Hack files to start from.", dir)),
        (None, None, None) => None,
    }
}

/// The query itself: which files to start from, then how far to take them.
/// Runs with the caches already clear and the sink already open.
fn query(
    r: &Run<'_>,
    options: &server_isolation_types::Options,
) -> Result<server_isolation_types::Result, BelowFloor> {
    let server_isolation_types::Options {
        mode,
        seed_framework,
        seed_list,
        seed_dir,
        max_seeds,
        seed_offset,
        allow_long_run,
        ..
    } = options;
    let seed_framework = seed_framework.as_deref();
    let seed_list = seed_list.as_deref();
    let seed_dir = seed_dir.as_deref();
    let grow = server_isolation_types::is_grow(mode);
    let ask_movability = server_isolation_types::is_check_movability(mode);
    // Accumulates across a run; a second query in the same server would
    // otherwise report the first one's totals.
    growth::reset_stats();
    let refuse = |total_seeds: isize, message: String| {
        crate::hh_logger::log(&format!("[isolation] refused: {}", message));
        refused(grow, total_seeds, message)
    };
    // Three reasons to refuse before doing any work, each checked as soon as
    // it can be known:
    // - the seed source cannot be read: before any seeds are selected;
    // - the seed source gave no seeds: once they are selected;
    // - the run would take too long: once the number of seeds is known.
    match unreadable_seed_source(seed_list, seed_dir) {
        Some(refusal) => Ok(refuse(0, refusal)),
        None => {
            let t_start = crate::rt::ocaml_unix::gettimeofday();
            let all_seeds = seeds::select(
                &r.ctx,
                &r.deps_mode,
                r.naming_table,
                ask_movability,
                seed_framework,
                seed_list,
                seed_dir,
            );
            let t = crate::hh_logger::log_duration(None, None, "[isolation] seed scan", t_start);
            let seeds = seeds::window(&all_seeds, *seed_offset, *max_seeds);
            let total_seeds = seeds.len() as isize;
            seeds::log_window(
                total_seeds,
                *seed_offset,
                *max_seeds,
                all_seeds.len() as isize,
            );
            // The estimate is per seed, because both cluster modes walk once
            // per seed. Movability walks once for the whole set however many
            // files it holds, so the guard does not describe it and would
            // refuse a large directory that answers in under a second.
            let refusal = if all_seeds.is_empty() {
                empty_seed_source(seed_framework, seed_list, seed_dir)
            } else if ask_movability {
                None
            } else {
                too_long_to_run(grow, total_seeds, *allow_long_run)
            };
            match refusal {
                Some(refusal) => Ok(refuse(total_seeds, refusal)),
                None => {
                    let (movability, sizes) = match mode {
                        Mode::CheckMovability | Mode::MoveTo(_) => {
                            let (verdict, sizes) = movability_of_seeds(r, &seeds);
                            (Some(verdict), sizes)
                        }
                        Mode::Grow => (None, grow_seeds(r, &seeds, total_seeds, t)?),
                        Mode::Measure => (None, measure_seeds(r, &seeds, total_seeds)?),
                    };
                    Ok(result(r, grow, movability, total_seeds, &sizes))
                }
            }
        }
    }
}

/// A move needs the server to learn of the renamed directory from its file
/// watcher, and Watchman does not report it on an Eden mount. The question is
/// refused up front there, since otherwise the client moves the directory,
/// waits for a change the server never sees, and undoes the move. It checks
/// the watcher in use and not [edenfs_file_watcher_enabled], because the
/// server falls back to Watchman when it cannot start the EdenFS one.
fn watcher_refusal(mode: &Mode, notifier: &crate::server_notifier::T) -> Option<String> {
    match mode {
        Mode::MoveTo(_) if crate::server_notifier::uses_watchman_on_eden_mount(notifier) => Some(
            "the server is watching this Eden checkout with Watchman, which does not report a moved directory to it. Stop it with `hh stop` and run this again with `--config edenfs_file_watcher_enabled=true`."
                .to_string(),
        ),
        Mode::MoveTo(_) | Mode::CheckMovability | Mode::Measure | Mode::Grow => None,
    }
}

pub fn go(
    options: &server_isolation_types::Options,
    genv: &Genv,
    env: &Env,
) -> server_isolation_types::Result {
    let server_isolation_types::Options {
        mode,
        clusters_destination,
        ..
    } = options;
    let sink = match clusters_destination {
        server_isolation_types::ClustersDestination::ToFile(path) => {
            sink::to_file(server_isolation_types::is_grow(mode), path)
        }
        server_isolation_types::ClustersDestination::Dropped => sink::discard(),
    };
    // Non-evictable shared heaps that outlive the query: cleared on the way in
    // so a run cannot reuse results from before an edit, and on the way out so
    // it leaves nothing resident.
    let reset_caches = || {
        server_isolation_outbound::reset();
        server_isolation_inbound::reset();
        growth::release_caches()
    };
    // Closed on the way out only — [reset_caches] also runs at the start, and
    // closing there would leave every cluster written to a closed channel.
    crate::utils::try_finally(
        || match watcher_refusal(mode, &genv.notifier) {
            Some(message) => {
                crate::hh_logger::log(&format!("[isolation] refused: {}", message));
                refused(server_isolation_types::is_grow(mode), 0, message)
            }
            None => {
                let r = make_run(options, genv, env, &sink);
                reset_caches();
                match query(&r, options) {
                    Ok(result) => result,
                    Err(BelowFloor(reason)) => {
                        let message = crate::rt::ocaml_string::capitalize(&reason);
                        crate::hh_logger::log(&format!("[isolation] refused: {}", message));
                        refused(server_isolation_types::is_grow(mode), 0, message)
                    }
                }
            }
        },
        || {
            // Nested, so that a sink failing to flush cannot skip the cache
            // reset: those heaps are non-evictable and would outlive the
            // query.
            crate::utils::try_finally(|| (sink.close)(), reset_caches)
        },
    )
}

#[cfg(test)]
mod tests {
    //! The pure parts of the module, and the cases of upstream's
    //! `test/unit/isolation_inbound_tests.ml` and
    //! `isolation_outbound_tests.ml`. Those run on a daemon after its init
    //! (the files of `Common_setup` declared, named and typechecked with the
    //! edges recorded), in a child process each
    //! (`fanout::testing::with_edges`: the graph, the path prefixes and the
    //! memos of the two modules are global to the process).
    //!
    //! The fixture records the graph by typechecking, where `Common_setup`
    //! leaves it empty: so the closure of `Bar.php` holds `Foo.php`, and
    //! `referrers` finds the edge without one being added by hand.

    use std::path::Path;
    use std::sync::Arc;

    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;
    use crate::ctx::Ctx;
    use crate::fanout::testing::with_edges;
    use crate::typing_deps_mode::T::InMemoryMode;

    #[test]
    fn median_is_the_upper_middle() {
        assert_eq!(median(&[]), 0);
        assert_eq!(median(&[3]), 3);
        assert_eq!(median(&[4, 1, 3, 2]), 3);
        assert_eq!(median(&[5, 1, 3]), 3);
    }

    #[test]
    fn closure_histogram_labels() {
        assert_eq!(closure_bucket(0), 1);
        assert_eq!(closure_bucket(3), 5);
        assert_eq!(closure_bucket(2000), 2000);
        assert_eq!(closure_bucket(2001), isize::MAX);
        assert_eq!(
            histogram(
                &[1, 1, 2, 3, 7, 60, 2001, 9999],
                closure_bucket,
                closure_label
            ),
            "1:2 2:1 3-5:1 6-10:1 51-100:1 2001+:2"
        );
        assert_eq!(
            histogram(&[3, 1, 3], |n| n, |b, count| format!("{}:{}", b, count)),
            "1:1 3:2"
        );
        assert_eq!(histogram(&[], closure_bucket, closure_label), "");
    }

    #[test]
    fn common_directory_of_files() {
        let p = |s: &str| relative_path::from_root(s);
        assert_eq!(sink::common_directory(&[]), "");
        assert_eq!(sink::common_directory(&[p("a/b/c.php")]), "a/b/");
        assert_eq!(
            sink::common_directory(&[p("a/b/c.php"), p("a/b/d/e.php"), p("a/bc/f.php")]),
            "a/"
        );
        assert_eq!(sink::common_directory(&[p("a/b.php"), p("c.php")]), "");
        assert_eq!(sink::common_directory(&[p("x/a.php"), p("y/b.php")]), "");
    }

    #[test]
    fn seed_lists_and_windows() {
        let p = |s: &str| relative_path::from_root(s);
        assert_eq!(
            seeds::paths_of_lines("a.php\n\n  b/c.php \r\n\t\nd.php"),
            vec![p("a.php"), p("b/c.php"), p("d.php")]
        );
        assert_eq!(
            seeds::dedupe(&[p("b"), p("a"), p("b"), p("c"), p("a")]),
            vec![p("b"), p("a"), p("c")]
        );
        let all = vec![p("a"), p("b"), p("c")];
        assert_eq!(seeds::window(&all, 0, None), all);
        assert_eq!(seeds::window(&all, 1, Some(1)), vec![p("b")]);
        assert_eq!(seeds::window(&all, 2, Some(5)), vec![p("c")]);
        assert_eq!(seeds::window(&all, 7, None), vec![]);
    }

    #[test]
    fn refusals() {
        assert_eq!(too_long_to_run(true, 14400, false), None);
        assert_eq!(too_long_to_run(true, 1_000_000, true), None);
        assert_eq!(
            too_long_to_run(true, 14401, false).unwrap(),
            "14401 seeds, which will take hours.\nSample it rather than covering it: --isolation-max-seeds 400 grows 400 seeds and stops, which is enough to see what fraction is isolatable. --isolation-seed-offset 1200 picks a different 400.\nOr pass --isolation-allow-long-run to grow all 14401."
        );
        assert_eq!(
            too_long_to_run(false, 3_000_000, false).unwrap(),
            "3000000 seeds, which will take days.\nSample it rather than covering it: --isolation-max-seeds 5000 measures 5000 seeds and stops, which is enough to see what fraction is isolatable. --isolation-seed-offset 15000 picks a different 5000.\nOr pass --isolation-allow-long-run to measure all 3000000."
        );
        assert_eq!(empty_seed_source(None, None, None), None);
        assert_eq!(
            empty_seed_source(None, None, Some("lib")).unwrap(),
            "lib has no Hack files to start from."
        );
        assert_eq!(
            empty_seed_source(Some("C"), Some("l"), None).unwrap(),
            "C has no subclasses to start from. --isolation-seed-framework takes a class name, fully qualified."
        );
    }

    #[test]
    fn sink_writes_one_line_per_cluster() {
        let path =
            std::env::temp_dir().join(format!("hh_isolation_sink_{}.jsonl", std::process::id()));
        let path = path.to_str().unwrap().to_string();
        let sink = sink::to_file(true, &path);
        (sink.emit)(&Cluster {
            files: vec!["a/b.php".into(), "a/c.php".into()],
            common_directory: "a/".into(),
            truncated: false,
        });
        (sink.emit)(&Cluster {
            files: vec!["d\"e.php".into()],
            common_directory: "".into(),
            truncated: true,
        });
        (sink.close)();
        assert_eq!(
            std::fs::read_to_string(&path).unwrap(),
            "{\"files\":[\"a/b.php\",\"a/c.php\"],\"size\":2,\"common_directory\":\"a/\",\"grown\":true,\"truncated\":false}\n\
             {\"files\":[\"d\\\"e.php\"],\"size\":1,\"common_directory\":\"\",\"grown\":true,\"truncated\":true}\n"
        );
        let _ = std::fs::remove_file(&path);
    }

    /// `test_memory_guard_stops_a_run_over_its_share`
    #[test]
    fn memory_guard_stops_a_run_over_its_share() {
        let gib = |n: isize| n * 1024 * 1024 * 1024;
        let total = gib(200);
        let reason = |max_used_percent, available_at_start, available| {
            memory::reason(
                &memory::guard(15, max_used_percent, available_at_start),
                gib(available),
                total,
            )
        };
        let from_150 = |available| reason(25, Some(gib(150)), available);
        // A quarter of 200 GiB is 50 GiB, and the floor is 30 GiB available.
        assert!(from_150(120).is_none());
        assert!(from_150(100).is_none());
        assert!(from_150(99).is_some());
        assert!(from_150(29).is_some());
        // 0 turns the share off, and the floor still holds.
        assert!(reason(0, Some(gib(150)), 60).is_none());
        assert!(reason(0, Some(gib(150)), 29).is_some());
        // A host that did not report its memory at the start has no share to
        // hold.
        assert!(reason(25, None, 60).is_none());
    }

    // ~~ The daemon fixture ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    /// `Common_setup.foo_contents`
    const FOO_CONTENTS: &str = r#"<?hh //strict
  new module foo {}
  class Foo {
    public function foo (Bar $b) : int {
      A::class;
      new B<D>();
      $x = Vector { 3 };
      return $b->toString();
    }
  }

  function f1(Foo $x) : void { }
  function f2(foo $x) : void { }
"#;

    /// `Common_setup.bar_contents`
    const BAR_CONTENTS: &str = r#"<?hh //strict
  module foo;
  class A {}
  class B<T> {}
  class D {}

  class Bar {
    public function toString() : string {
      return "bar";
    }
  }
"#;

    // AttrUser names MyAttr only in the attribute.
    const ATTRIBUTE_FILES: &[(&str, &str)] = &[
        ("AttrDef.php", "<?hh\nclass MyAttr {}\n"),
        ("AttrUser.php", "<?hh\n<<MyAttr>>\nclass AttrUser {}\n"),
    ];

    // MemberUser reaches MemberTarget only through a method call on a value
    // whose class it never names, and names MemberFactory directly.
    const MEMBER_FILES: &[(&str, &str)] = &[
        (
            "MemberTarget.php",
            "<?hh\nclass MemberTarget {\n  public function ping(): int { return 1; }\n}\n",
        ),
        (
            "MemberFactory.php",
            "<?hh\nfunction make_target(): MemberTarget { return new MemberTarget(); }\n",
        ),
        (
            "MemberUser.php",
            "<?hh\nfunction use_it(): int { return make_target()->ping(); }\n",
        ),
    ];

    /// A daemon after its init on Foo.php, Bar.php and [extra_files]: the
    /// files declared, the reverse naming table, every file typechecked with
    /// the edges registered, and the env with the forward naming table.
    fn daemon(extra_files: &[(&str, &str)]) -> (Genv, Env) {
        let mut files = vec![("Foo.php", FOO_CONTENTS), ("Bar.php", BAR_CONTENTS)];
        files.extend_from_slice(extra_files);
        // The files are read from the disk (entries of the context), as in
        // the daemon: they are written to a fresh root.
        let root = std::env::temp_dir().join(format!("hh_server_isolation_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).unwrap();
        for (name, contents) in &files {
            std::fs::write(root.join(name), contents).unwrap();
        }
        let root = root.canonicalize().unwrap();
        let ctx = Ctx::new(&root, TypecheckerOptions::default()).unwrap();
        let mut paths = ctx.hhi_paths.clone();
        let mut checked = vec![];
        for (name, contents) in &files {
            let path = ::pos::RelativePath::new(::pos::Prefix::Root, *name);
            ctx.files.set(path, *contents);
            paths.push(path);
            checked.push(path);
        }
        crate::check::declare_files(&ctx, &paths, &mut crate::check::Stats::default());
        ctx.build_reverse_naming_table();
        relative_path::set_path_prefix(relative_path::Prefix::Root, &root);
        relative_path::set_path_prefix(relative_path::Prefix::Hhi, Path::new("/hhi"));
        relative_path::set_path_prefix(relative_path::Prefix::Tmp, Path::new("/tmp"));
        let ctx = Arc::new(ctx);
        crate::hh_single_type_check::install(&ctx);
        crate::ast_provider::set_local_parser_cache_enabled(false);
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .stack_size(256 << 20)
            .build()
            .unwrap();
        pool.install(|| {
            typing_deps::TRACE.store(true, std::sync::atomic::Ordering::SeqCst);
            let _ = crate::check::check_files_typed_by_file(
                &ctx,
                &checked,
                &mut crate::check::Stats::default(),
                None,
            );
            typing_deps::flush_deps(&InMemoryMode(None));
            typing_deps::TRACE.store(false, std::sync::atomic::Ordering::SeqCst);
        });
        let mut files_info = relative_path::map::T::new();
        for p in &checked {
            let p: relative_path::T = (*p).into();
            let decls = crate::direct_decl_service::direct_decl_parse(&ctx, &p).unwrap();
            files_info.insert(
                p.clone(),
                crate::direct_decl_service::decls_to_fileinfo(&p, &decls),
            );
        }
        let genv = crate::server_env_build::default_genv();
        let mut env = crate::server_env_build::make_env(
            "test",
            InMemoryMode(None),
            None,
            &genv.config,
            Path::new("/"),
        );
        env.naming_table = crate::naming_table::create(files_info);
        env.ctx = ctx;
        (genv, env)
    }

    /// The daemon of [daemon], with the context the commands get.
    fn setup(extra_files: &[(&str, &str)]) -> (provider_context::T, Env) {
        let (_genv, env) = daemon(extra_files);
        let ctx = crate::provider_utils::ctx_from_server_env(&env);
        (ctx, env)
    }

    fn foo_path() -> RelativePath {
        relative_path::from_root("Foo.php")
    }

    fn bar_path() -> RelativePath {
        relative_path::from_root("Bar.php")
    }

    fn set_of(paths: &[RelativePath]) -> relative_path::set::T {
        paths.iter().cloned().collect()
    }

    /// Runs `body` alone in a child process (see the module doc).
    fn isolated(test: &str, body: impl FnOnce()) {
        with_edges(module_path!(), test, &[], body)
    }

    // ~~ isolation_inbound_tests.ml ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #[test]
    fn closure_of_an_unreferenced_file_is_just_itself() {
        isolated("closure_of_an_unreferenced_file_is_just_itself", || {
            server_isolation_inbound::reset();
            // (Foo.php is referenced here, by Bar.php's `module foo;`: the
            // unreferenced file is one of the member files.)
            let (ctx, env) = setup(MEMBER_FILES);
            let user_path = relative_path::from_root("MemberUser.php");
            // Pins that the file itself is in its own closure, which is what
            // makes the set safe to absorb whole.
            assert_eq!(
                server_isolation_inbound::get(&ctx, &env.naming_table, 100, &user_path),
                Some(set_of(&[user_path]))
            );
        })
    }

    /// Not in the OCaml (whose fixture has no graph): the closure of a file
    /// holds the file that references it.
    #[test]
    fn closure_of_a_referenced_file_holds_its_referrer() {
        isolated("closure_of_a_referenced_file_holds_its_referrer", || {
            server_isolation_inbound::reset();
            let (ctx, env) = setup(&[]);
            assert_eq!(
                server_isolation_inbound::get(&ctx, &env.naming_table, 100, &bar_path()),
                Some(set_of(&[bar_path(), foo_path()]))
            );
            // Two files do not fit under a bound of one.
            server_isolation_inbound::reset();
            assert_eq!(
                server_isolation_inbound::get(&ctx, &env.naming_table, 1, &bar_path()),
                None
            );
        })
    }

    #[test]
    fn second_request_is_memoised() {
        isolated("second_request_is_memoised", || {
            server_isolation_inbound::reset();
            let (ctx, env) = setup(&[]);
            let first = server_isolation_inbound::get(&ctx, &env.naming_table, 100, &bar_path());
            let after_one = server_isolation_inbound::closures_computed();
            let second = server_isolation_inbound::get(&ctx, &env.naming_table, 100, &bar_path());
            let after_two = server_isolation_inbound::closures_computed();
            // The count is the assertion. A closure is a global fact, so the
            // second request must be served rather than recomputed however
            // many clusters ask.
            assert_eq!(after_one, 1);
            assert_eq!(after_two, 1);
            assert_eq!(first, second);
            assert_eq!(server_isolation_inbound::closures_served(), 1);
        })
    }

    #[test]
    fn refusals_are_memoised_too() {
        isolated("refusals_are_memoised_too", || {
            server_isolation_inbound::reset();
            let (ctx, env) = setup(&[]);
            let first = server_isolation_inbound::get(&ctx, &env.naming_table, 0, &bar_path());
            let second = server_isolation_inbound::get(&ctx, &env.naming_table, 0, &bar_path());
            // A refusal costs as much as an answer, and widely-used files are
            // asked about repeatedly, so [None] has to be cached rather than
            // recomputed.
            assert_eq!(first, None);
            assert_eq!(second, None);
            assert_eq!(server_isolation_inbound::closures_computed(), 1);
            assert_eq!(server_isolation_inbound::refusals_held(), 1);
        })
    }

    #[test]
    fn reset_drops_the_memo() {
        isolated("reset_drops_the_memo", || {
            server_isolation_inbound::reset();
            let (ctx, env) = setup(&[]);
            let _ = server_isolation_inbound::get(&ctx, &env.naming_table, 100, &bar_path());
            server_isolation_inbound::reset();
            let cleared = server_isolation_inbound::closures_computed() == 0;
            let _ = server_isolation_inbound::get(&ctx, &env.naming_table, 100, &bar_path());
            // Recomputing is what shows the entry went: had it survived, this
            // request would have been served and the count would still be 0.
            assert!(cleared);
            assert_eq!(server_isolation_inbound::closures_computed(), 1);
        })
    }

    #[test]
    fn referrers_answers_for_the_whole_candidate_at_once() {
        isolated("referrers_answers_for_the_whole_candidate_at_once", || {
            server_isolation_inbound::reset();
            let (ctx, env) = setup(&[]);
            let candidate = set_of(&[foo_path(), bar_path()]);
            let _ = server_isolation_inbound::referrers(&ctx, &env.naming_table, &candidate);
            // [referrers] does not touch the per-file memo at all, so nothing
            // is recorded against it.
            assert_eq!(server_isolation_inbound::closures_computed(), 0);
        })
    }

    #[test]
    fn referrers_names_the_file_that_references_in() {
        isolated("referrers_names_the_file_that_references_in", || {
            server_isolation_inbound::reset();
            let (ctx, env) = setup(&[]);
            let candidate = set_of(&[bar_path()]);
            assert_eq!(
                server_isolation_inbound::referrers(&ctx, &env.naming_table, &candidate),
                set_of(&[foo_path()])
            );
        })
    }

    #[test]
    fn referrers_of_a_candidate_holding_both_ends_is_empty() {
        isolated(
            "referrers_of_a_candidate_holding_both_ends_is_empty",
            || {
                server_isolation_inbound::reset();
                let (ctx, env) = setup(&[]);
                let candidate = set_of(&[foo_path(), bar_path()]);
                // Empty is the move's green light, so it has to mean "nothing
                // references in" and not "nothing was looked at". The previous
                // case shares the graph and finds the edge, which is what rules
                // that out.
                assert!(
                    server_isolation_inbound::referrers(&ctx, &env.naming_table, &candidate)
                        .is_empty()
                );
            },
        )
    }

    // ~~ isolation_outbound_tests.ml ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #[test]
    fn edges_point_at_the_referenced_file() {
        isolated("edges_point_at_the_referenced_file", || {
            server_isolation_outbound::reset();
            let (ctx, _env) = setup(&[]);
            let edges = server_isolation_outbound::get(&ctx, &foo_path());
            assert!(edges.contains(&bar_path()));
            assert!(!edges.contains(&foo_path()));
        })
    }

    #[test]
    fn second_request_is_served_from_cache() {
        isolated("second_request_is_served_from_cache", || {
            server_isolation_outbound::reset();
            let (ctx, _env) = setup(&[]);
            let first = server_isolation_outbound::get(&ctx, &foo_path());
            let after_one = server_isolation_outbound::files_indexed();
            let second = server_isolation_outbound::get(&ctx, &foo_path());
            let after_two = server_isolation_outbound::files_indexed();
            // The count is what distinguishes a cache hit from a
            // recomputation that happens to agree.
            assert_eq!(after_one, 1);
            assert_eq!(after_two, 1);
            assert_eq!(first, second);
        })
    }

    #[test]
    fn reset_drops_the_cache() {
        isolated("reset_drops_the_cache", || {
            server_isolation_outbound::reset();
            let (ctx, _env) = setup(&[]);
            let _ = server_isolation_outbound::get(&ctx, &foo_path());
            server_isolation_outbound::reset();
            let cleared = server_isolation_outbound::files_indexed() == 0;
            // The count going back to 1 is what shows the heap entry was
            // dropped too: had it survived, this [get] would hit the cache and
            // never increment.
            let _ = server_isolation_outbound::get(&ctx, &foo_path());
            assert!(cleared);
            assert_eq!(server_isolation_outbound::files_indexed(), 1);
        })
    }

    #[test]
    fn attribute_only_reference_yields_an_edge() {
        isolated("attribute_only_reference_yields_an_edge", || {
            server_isolation_outbound::reset();
            let (ctx, _env) = setup(ATTRIBUTE_FILES);
            let user_path = relative_path::from_root("AttrUser.php");
            let def_path = relative_path::from_root("AttrDef.php");
            // This edge exists only if [Attribute] occurrences are followed.
            // Asserting the whole set, not just membership, so an
            // over-inclusive filter fails here too.
            assert_eq!(
                server_isolation_outbound::get(&ctx, &user_path),
                set_of(&[def_path])
            );
        })
    }

    #[test]
    fn member_only_reference_yields_no_edge() {
        isolated("member_only_reference_yields_no_edge", || {
            server_isolation_outbound::reset();
            let (ctx, _env) = setup(MEMBER_FILES);
            let user_path = relative_path::from_root("MemberUser.php");
            let factory_path = relative_path::from_root("MemberFactory.php");
            let target_path = relative_path::from_root("MemberTarget.php");
            let edges = server_isolation_outbound::get(&ctx, &user_path);
            // Deliberate: MemberTarget is a real dependency, but no package
            // rule can reject a method call.
            assert!(edges.contains(&factory_path));
            assert!(!edges.contains(&target_path));
        })
    }

    #[test]
    fn module_membership_yields_no_edge() {
        isolated("module_membership_yields_no_edge", || {
            server_isolation_outbound::reset();
            let (ctx, _env) = setup(&[]);
            // Bar.php reaches Foo.php only through `module foo;`, declared in
            // Foo.php.
            let edges = server_isolation_outbound::get(&ctx, &bar_path());
            assert!(!edges.contains(&foo_path()));
        })
    }

    #[test]
    fn ensure_indexed_warms_the_cache() {
        isolated("ensure_indexed_warms_the_cache", || {
            server_isolation_outbound::reset();
            let (ctx, _env) = setup(&[]);
            server_isolation_outbound::ensure_indexed(
                &ctx,
                None,
                &|| Ok(()),
                &[foo_path(), bar_path()],
            )
            .unwrap();
            let after_bulk = server_isolation_outbound::files_indexed();
            let edges = server_isolation_outbound::get(&ctx, &foo_path());
            // The count not moving is the assertion: [get] served what the
            // bulk call indexed rather than recomputing it.
            assert_eq!(after_bulk, 2);
            assert_eq!(server_isolation_outbound::files_indexed(), 2);
            assert!(edges.contains(&bar_path()));
        })
    }

    #[test]
    fn ensure_indexed_stops_when_memory_is_low() {
        isolated("ensure_indexed_stops_when_memory_is_low", || {
            server_isolation_outbound::reset();
            let (ctx, _env) = setup(&[]);
            for workers in [None, Some(4)] {
                server_isolation_outbound::reset();
                assert_eq!(
                    server_isolation_outbound::ensure_indexed(
                        &ctx,
                        workers,
                        &|| Err(BelowFloor("memory is low".into())),
                        &[foo_path(), bar_path()],
                    ),
                    Err(BelowFloor("memory is low".into()))
                );
            }
        })
    }

    #[test]
    fn release_cache_keeps_the_count() {
        isolated("release_cache_keeps_the_count", || {
            server_isolation_outbound::reset();
            let (ctx, _env) = setup(&[]);
            let _ = server_isolation_outbound::get(&ctx, &foo_path());
            server_isolation_outbound::release_cache();
            // This is the whole difference from [reset]: entries go, the tally
            // stays.
            let kept = server_isolation_outbound::files_indexed() == 1;
            let _ = server_isolation_outbound::get(&ctx, &foo_path());
            assert!(kept);
            assert_eq!(server_isolation_outbound::files_indexed(), 2);
        })
    }

    // ~~ The query ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    fn options(
        mode: Mode,
        clusters_destination: server_isolation_types::ClustersDestination,
    ) -> server_isolation_types::Options {
        server_isolation_types::Options {
            mode,
            clusters_destination,
            seed_framework: None,
            seed_list: None,
            seed_dir: None,
            max_dependents: 100,
            max_cluster_size: None,
            batch_size: 10,
            min_free_memory_percent: 0,
            max_memory_percent: 0,
            allow_long_run: false,
            max_seeds: None,
            seed_offset: 0,
        }
    }

    /// Not in the OCaml: the three modes over the fixture and the member
    /// files. MemberUser.php is the one file nothing references (the seed
    /// scan: Foo.php and Bar.php reference each other), and grows into the
    /// three member files; Bar.php alone is blocked by Foo.php, and the two
    /// move together.
    #[test]
    fn the_three_modes() {
        isolated("the_three_modes", || {
            let (genv, env) = daemon(MEMBER_FILES);
            let out =
                std::env::temp_dir().join(format!("hh_isolation_go_{}.jsonl", std::process::id()));
            let out = out.to_str().unwrap().to_string();
            let to_file = || server_isolation_types::ClustersDestination::ToFile(out.clone());

            let r = go(&options(Mode::Measure, to_file()), &genv, &env);
            assert_eq!(r.refused, None);
            assert!(!r.grown);
            assert_eq!(r.total_seeds, 1);
            assert_eq!(r.total_clusters, 1);
            assert_eq!(r.largest_cluster, 1);
            assert_eq!(
                std::fs::read_to_string(&out).unwrap(),
                "{\"files\":[\"MemberUser.php\"],\"size\":1,\"common_directory\":\"\",\"grown\":false,\"truncated\":false}\n"
            );

            let r = go(&options(Mode::Grow, to_file()), &genv, &env);
            assert_eq!(r.refused, None);
            assert!(r.grown);
            assert_eq!(r.total_seeds, 1);
            assert_eq!(r.total_clusters, 1);
            assert_eq!(r.largest_cluster, 3);
            assert_eq!(r.total_refused, 0);
            assert_eq!(
                std::fs::read_to_string(&out).unwrap(),
                "{\"files\":[\"MemberFactory.php\",\"MemberTarget.php\",\"MemberUser.php\"],\"size\":3,\"common_directory\":\"\",\"grown\":true,\"truncated\":false}\n"
            );

            let list =
                std::env::temp_dir().join(format!("hh_isolation_list_{}", std::process::id()));
            std::fs::write(&list, "Bar.php\nBar.php\nMissing.php\n").unwrap();
            let mut o = options(
                Mode::CheckMovability,
                server_isolation_types::ClustersDestination::Dropped,
            );
            o.seed_list = Some(list.to_str().unwrap().to_string());
            let r = go(&o, &genv, &env);
            assert_eq!(
                r.movability,
                Some(server_isolation_types::Movability::Blocked(vec![
                    server_isolation_types::Blocker {
                        file: "Foo.php".into(),
                        references: vec!["Bar.php".into()],
                    }
                ]))
            );
            assert_eq!(r.total_seeds, 1);
            std::fs::write(&list, "Bar.php\nFoo.php\n").unwrap();
            let r = go(&o, &genv, &env);
            assert_eq!(
                r.movability,
                Some(server_isolation_types::Movability::Movable)
            );
            assert_eq!(r.total_isolatable_files, 2);

            o.seed_list = Some("/nonexistent/list".into());
            let r = go(&o, &genv, &env);
            assert_eq!(
                r.refused.as_deref(),
                Some(
                    "/nonexistent/list is not a file. --isolation-seed-list takes a file of repo-relative paths, one per line."
                )
            );
            let mut o = options(
                Mode::Measure,
                server_isolation_types::ClustersDestination::Dropped,
            );
            o.seed_dir = Some(".".into());
            let r = go(&o, &genv, &env);
            assert_eq!(r.refused, None);
            assert_eq!(r.total_seeds, 5);
            let _ = std::fs::remove_file(&out);
            let _ = std::fs::remove_file(&list);
        })
    }
}
