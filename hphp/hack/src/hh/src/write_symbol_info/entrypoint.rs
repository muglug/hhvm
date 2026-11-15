// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Entrypoint` (`write_symbol_info/entrypoint.ml`): entry
//! point to the hack indexer.

// (`go` and what only it uses are for the server.)
#![cfg_attr(not(feature = "server"), allow(dead_code))]

use std::collections::BTreeSet;
use std::io::Write;

use super::add_fact;
use super::file_info;
use super::glean::src::index_failure_reason;
use super::index_batch;
use super::indexable;
use super::indexer_options;
use super::predicate::Failure;
use super::predicate::fact_acc;
use super::sym_hash;
use super::sym_hash::Md5;
use crate::hh_logger;
use crate::path;
use crate::provider_context;
use crate::relative_path;
use crate::rt::ocaml_unix::gettimeofday;
use crate::rt::quiet_panic;
use crate::worker_cancel::WorkerShouldExit;
use crate::yojson::safe as yojson;

pub mod job_return {
    use super::*;

    #[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
    pub struct T {
        pub elapsed: f64,
        pub hashes: BTreeSet<Md5>,
        pub reindexed: BTreeSet<String>,
        /// set of files referenced by the indexed files
        pub referenced: BTreeSet<String>,
        pub index_failures: isize,
    }

    pub fn neutral() -> T {
        T::default()
    }

    pub fn merge(t1: T, t2: T) -> T {
        let mut hashes = t1.hashes;
        hashes.extend(t2.hashes);
        let mut reindexed = t1.reindexed;
        reindexed.extend(t2.reindexed);
        let mut referenced = t1.referenced;
        referenced.extend(t2.referenced);
        T {
            elapsed: t1.elapsed + t2.elapsed,
            hashes,
            reindexed,
            referenced,
            index_failures: t1.index_failures + t2.index_failures,
        }
    }
}

/// Indexing failures should be non-existent or very rare as they
/// usually affect the hack typechecker as well
const MAX_INDEX_FAILURES: isize = 100;

fn log_elapsed(s: &str, elapsed: f64) {
    // `Unix.gmtime elapsed`: the minutes and seconds of the hour.
    let secs = if elapsed > 0. { elapsed as u64 } else { 0 };
    hh_logger::log(&format!("{} {}m{}s", s, (secs / 60) % 60, secs % 60))
}

fn write_file(referenced: &BTreeSet<String>, output_file: &str) -> std::io::Result<()> {
    let mut oc = std::fs::File::create(output_file)?;
    for str in referenced {
        oc.write_all(str.as_bytes())?;
        oc.write_all(b"\n")?;
    }
    Ok(())
}

/// `Printf.sprintf "%g"` (six significant digits).
fn sprintf_g(x: f64) -> String {
    let precision = 6;
    let e = format!("{:.*e}", precision - 1, x);
    let (mantissa, exponent) = e.split_once('e').unwrap();
    let exponent: i32 = exponent.parse().unwrap();
    let strip_zeros = |s: &str| -> String {
        if s.contains('.') {
            s.trim_end_matches('0').trim_end_matches('.').to_string()
        } else {
            s.to_string()
        }
    };
    if -4 <= exponent && exponent < precision as i32 {
        let decimals = (precision as i32 - 1 - exponent) as usize;
        strip_zeros(&format!("{:.*}", decimals, x))
    } else {
        format!(
            "{}e{}{:02}",
            strip_zeros(mantissa),
            if exponent < 0 { '-' } else { '+' },
            exponent.abs()
        )
    }
}

/// `Byte_units.to_string_hum (Byte_units.of_bytes_int n)`
fn byte_units_to_string_hum(n: usize) -> String {
    let kib = 1024usize;
    let mib = kib * kib;
    let gib = kib * mib;
    if n < kib {
        format!("{}B", n)
    } else if n < mib {
        format!("{}K", sprintf_g(n as f64 / kib as f64))
    } else if n < gib {
        format!("{}M", sprintf_g(n as f64 / mib as f64))
    } else {
        format!("{}G", sprintf_g(n as f64 / gib as f64))
    }
}

/// `` `Count n | `Path path `` of `write_facts_file`.
pub enum Files {
    Count(usize),
    Path(String),
}

/// `Filename_unix.open_temp_file ~in_dir prefix suffix`: a new file
/// `prefix.tmp.XXXXXX` `suffix` (six random hexadecimal digits), made with
/// `O_EXCL` and mode 0o600; up to 1000 other names are tried when the
/// creation fails.
fn open_temp_file(in_dir: &str, prefix: &str, suffix: &str) -> std::io::Result<(String, std::fs::File)> {
    use std::hash::BuildHasher;
    use std::hash::Hasher;
    use std::os::unix::fs::OpenOptionsExt;
    let mut counter = 0;
    loop {
        let rnd = {
            let mut h = std::collections::hash_map::RandomState::new().build_hasher();
            h.write_u128(std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_nanos()));
            h.write_u32(std::process::id());
            h.finish() & 0xFF_FFFF
        };
        let name = format!("{}.tmp.{:06x}{}", prefix, rnd, suffix);
        let name = path::to_string(&path::concat(&path::make_unsafe(in_dir), &name));
        match std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&name)
        {
            Ok(f) => return Ok((name, f)),
            Err(e) => {
                if counter >= 1000 {
                    return Err(e);
                }
                counter += 1
            }
        }
    }
}

fn write_facts_file(out_dir: &str, global: Option<bool>, files: Files, json_chunks: Vec<yojson::T>) -> Result<(), Failure> {
    let global = global.unwrap_or(false);
    let (_out_file, mut channel) = open_temp_file(out_dir, "glean_symbol_info_chunk_", ".json")
        .map_err(|e| Failure(format!("Sys_error: {}", e)))?;
    let json_string = yojson::to_string(&yojson::T::List(json_chunks));
    let json_length = json_string.len();
    channel
        .write_all(json_string.as_bytes())
        .map_err(|e| Failure(format!("Sys_error: {}", e)))?;
    drop(channel);
    hh_logger::log(&format!(
        "Wrote {} of {}JSON facts for {}",
        byte_units_to_string_hum(json_length),
        if global { "global " } else { "" },
        match files {
            Files::Count(n) => format!("{} files", n),
            Files::Path(path) => path,
        }
    ));
    Ok(())
}

// these facts aren't generated by the workers, but once for the whole
// indexing run. There are
// - symbol hash facts for incrementality (empty if gen_sym_hash isn't set)
// - the namespace aliases defined in .hhconfig

const BYTES_PER_HASH: usize = 16;

/// input hashes are stored in facts, we try to keep the max size
/// of such  fact to a reasonable size (800KB), ideally less than
/// Glean pagination limit
const MAX_FACT_BYTES: usize = 800 * 1024; // 800KB

const MAX_HASHES_PER_FACT: usize = MAX_FACT_BYTES / BYTES_PER_HASH;

fn gen_global_facts(
    ns: &[(String, String)],
    ownership: bool,
    shard_name: &str,
    all_hashes: &BTreeSet<Md5>,
) -> Vec<yojson::T> {
    let list_hashes: Vec<Md5> = all_hashes.iter().copied().collect();
    // Split hashes into chunks
    let hash_chunks: Vec<&[Md5]> = list_hashes.chunks(MAX_HASHES_PER_FACT).collect();
    let num_chunks = hash_chunks.len();
    // Generate facts for each chunk
    let mut res = vec![];
    for (i, chunk_hashes) in hash_chunks.into_iter().enumerate() {
        let mut fa = fact_acc::init(ownership);
        // Only include namespace aliases in the first shard
        if i == 0 {
            if ownership {
                fact_acc::set_ownership_unit(&mut fa, Some(".hhconfig".to_string()));
            }
            for (from, to_) in ns {
                add_fact::global_namespace_alias(from, to_, &mut fa);
            }
        }
        let chunk_shard_name = if num_chunks == 1 {
            shard_name.to_string()
        } else {
            format!("{}{:03}", shard_name, i)
        };
        add_fact::indexer_inputs_hash(&chunk_shard_name, chunk_hashes, &mut fa);
        res.extend(fact_acc::to_json(&fa))
    }
    res
}

fn emit_index_failure_facts(ownership: bool, out_dir: &str, index_failures: &[(String, String)]) -> Result<(), Failure> {
    if !index_failures.is_empty() {
        let mut fa = fact_acc::init(ownership);
        for (path, details) in index_failures {
            if ownership {
                fact_acc::set_ownership_unit(&mut fa, Some(path.clone()));
            }
            add_fact::index_failure(path, index_failure_reason::T::CompileError, details.clone(), &mut fa);
        }
        let json_chunks = fact_acc::to_json(&fa);
        write_facts_file(out_dir, None, Files::Count(index_failures.len()), json_chunks)?
    }
    Ok(())
}

/// `Exn.to_string` of what a `try ... with e ->` of this module catches: a
/// `Failure`, or a panic (an exception of the code below, whose payload is
/// its text). `Worker_should_exit` is re-raised (cancellation requests must
/// be).
pub fn exn_to_string_or_reraise(e: Box<dyn std::any::Any + Send>) -> String {
    if e.is::<WorkerShouldExit>() {
        std::panic::resume_unwind(e)
    }
    // A panic with a message is a `failwith` (`hh/PORTING.md`).
    if let Some(s) = e.downcast_ref::<&str>() {
        Failure(s.to_string()).exn_to_string()
    } else if let Some(s) = e.downcast_ref::<String>() {
        Failure(s.clone()).exn_to_string()
    } else if let Some(e) = e.downcast_ref::<crate::rt::ocaml_exn::Uncaught>() {
        e.to_string()
    } else if let Some(e) = e.downcast_ref::<crate::decl_defs::DeclNotFound>() {
        // An exception without a sexp converter: `Exn.to_string` gives the
        // list of the atom `Printexc.to_string e`.
        crate::rt::ocaml_exn::Uncaught::Printexc(e.to_string()).to_string()
    } else {
        "<exception>".to_string()
    }
}

fn write_json(
    ctx: &provider_context::T,
    ownership: bool,
    out_dir: &str,
    files_info: &[&file_info::T],
    start_time: f64,
) -> job_return::T {
    // Large file may lead to large json files which timeout when sent
    // to the server. Not an issue currently, but if it is, we can index
    // xrefs/decls separately, or split in batches according to files size
    for file_info::T { tast, path, .. } in files_info {
        if tast.len() > 2000 {
            hh_logger::log(&format!("Large file: {}", path))
        }
    }
    let res = quiet_panic::catch_reported(
        |p| !p.is::<WorkerShouldExit>(),
        || -> Result<(), Failure> {
            let json_chunks = index_batch::build_json(ctx, files_info, ownership)?;
            let files = {
                let file_count = files_info.len();
                if file_count == 1 {
                    Files::Path(files_info[0].path.clone())
                } else {
                    Files::Count(file_count)
                }
            };
            write_facts_file(out_dir, None, files, json_chunks)
        },
    );
    let failure = match res {
        Ok(Ok(())) => None,
        Ok(Err(e)) => Some(e.exn_to_string()),
        Err(e) => Some(exn_to_string_or_reraise(e)),
    };
    if let Some(e) = failure {
        eprint!("WARNING: symbol write failure: \n{}\n", e)
    }
    let elapsed = gettimeofday() - start_time;
    log_elapsed("Processed batch in", elapsed);
    let hashes = files_info.iter().filter_map(|file_info| file_info.sym_hash).collect();
    job_return::T {
        elapsed,
        hashes,
        reindexed: BTreeSet::new(),
        referenced: BTreeSet::new(),
        index_failures: 0,
    }
}

fn references_from_files_info(ctx: &provider_context::T, files_info: &[file_info::T]) -> BTreeSet<String> {
    let mut res = BTreeSet::new();
    for fi in files_info {
        res.extend(file_info::referenced(ctx, fi))
    }
    res
}

fn recheck_job(
    ctx: &provider_context::T,
    opts: &indexer_options::T,
    _: job_return::T,
    fa: &[indexable::T],
) -> job_return::T {
    let start_time = gettimeofday();

    // file hashes must be computed for incremental indexing, bases or increments
    let gen_sym_hash = opts.gen_sym_hash || opts.incremental.is_some();

    // in order to compute referenced files, we need to compute the path of referenced
    // symbols
    let gen_references = opts.referenced_file.is_some();
    let mut files_info = vec![];
    let mut index_failures = vec![];
    for indexable in fa {
        let res = quiet_panic::catch_reported(
            |p| !p.is::<WorkerShouldExit>(),
            || file_info::create(ctx, indexable, gen_sym_hash, &opts.root_path, &opts.hhi_path),
        );
        let failure = match res {
            Ok(Ok(Some(fi))) => {
                files_info.push(fi);
                None
            }
            Ok(Ok(None)) => None,
            Ok(Err(e)) => Some(e.exn_to_string()),
            Err(e) => Some(exn_to_string_or_reraise(e)),
        };
        if let Some(e) = failure {
            let path = relative_path::to_absolute_with_prefix(
                // (`Path.make_unsafe`)
                std::path::Path::new(&opts.root_path),
                std::path::Path::new(&opts.hhi_path),
                &indexable.path,
            );
            hh_logger::log(&format!("WARNING: indexing failure for {}: {}", path, e));
            // (`(path, Exn.to_string e) :: err_acc`)
            index_failures.insert(0, (path, e));
        }
    }
    let reindex = |f: &file_info::T| match (f.fanout, &opts.incremental, &f.sym_hash) {
        (true, Some(table), Some(hash)) if sym_hash::mem(table, hash) => false,
        _ => true,
    };
    // (`to_reindex` as references to `files_info`, which `referenced` reads
    // after.)
    let to_reindex: Vec<&file_info::T> = files_info.iter().filter(|f| reindex(f)).collect();
    let res = write_json(ctx, opts.ownership, &opts.out_dir, &to_reindex, start_time);
    if let Err(e) = emit_index_failure_facts(opts.ownership, &opts.out_dir, &index_failures) {
        // (The OCaml lets the exception out of the job.)
        panic!("{}", e.exn_to_string())
    }
    let fanout_reindexed = to_reindex
        .iter()
        .filter_map(|file_info::T { path, fanout, .. }| if *fanout { Some(path.clone()) } else { None })
        .collect();
    let referenced = if gen_references {
        references_from_files_info(ctx, &files_info)
    } else {
        BTreeSet::new()
    };
    job_return::T {
        reindexed: fanout_reindexed,
        referenced,
        index_failures: index_failures.len() as isize,
        ..res
    }
}

/// `Md5.to_hex`
pub fn md5_to_hex(h: &Md5) -> String {
    h.iter().map(|b| format!("{:02x}", b)).collect()
}

pub fn sym_hashes(ctx: &provider_context::T, files: &[relative_path::T]) -> Result<Vec<(String, Md5)>, Failure> {
    let f = |file: &relative_path::T| -> Result<(String, Md5), Failure> {
        let fi = file_info::create(ctx, &indexable::from_file(file.clone()), true, "www", "hhi")?;
        let sym_hash = match fi.and_then(|fi| fi.sym_hash) {
            None => return Err(Failure("Internal error".to_string())), // can't happen since gen_sym_hash = true
            Some(sh) => sh,
        };
        Ok((relative_path::to_absolute(file), sym_hash))
    };
    files.iter().map(f).collect()
}

/// simpler entry point, uses default options indexing options, doesn't
/// use worker. This is used by hh_single_type_check.
pub fn index_files(ctx: &provider_context::T, out_dir: &str, files: &[relative_path::T]) {
    let idx: Vec<indexable::T> = files.iter().cloned().map(indexable::from_file).collect();
    let opts = indexer_options::default(out_dir);
    let _ = recheck_job(ctx, &opts, job_return::neutral(), &idx);
}

/// The job of [`go`] on the workers (`recheck_job ctx opts`): each bucket in
/// a worker's clone, which writes its own facts files, its fact ids
/// starting where the master's were when [`go`] started (as an OCaml
/// worker's clone starts with the fact ids of the process it was forked
/// from).
#[cfg(feature = "server")]
pub struct RecheckJob;

#[cfg(feature = "server")]
impl crate::multi_worker::ServiceJob for RecheckJob {
    const NAME: &'static str = "Write_symbol_info.Entrypoint.recheck_job";
    /// The options and the first fact id.
    type Params = (indexer_options::T, isize);
    type Item = indexable::T;
    type Output = job_return::T;
    fn run(ctx: &provider_context::T, (opts, first_fact_id): &Self::Params, bucket: Vec<indexable::T>) -> Self::Output {
        super::glean::fact_id::set_next(*first_fact_id);
        recheck_job(ctx, opts, job_return::neutral(), &bucket)
    }
}

/// namespace_map is the aliases map, used to generate hack.GlobalNamespaceAlias
///
/// The OCaml runs each bucket of files in a worker process forked for the
/// job (`Worker`: "We fork a clone process for every incoming request"),
/// whose fact ids start where the server's were when its workers were made.
/// Here the buckets run on the threads of the pool (the OCaml's workers are
/// processes because its threads could not run in parallel; see
/// `multi_worker::workers_switched_on`), each starting with the fact ids the
/// master had at the start; with `HH_RUST_WORKERS=1` they run in the worker
/// processes' clones ([`RecheckJob`]), from the same fact ids. The files written are the same either way, only the order of
/// the "Wrote ..." lines of the buckets in the log depends on the
/// scheduling, as it does in the OCaml.
#[cfg(feature = "server")]
pub fn go(
    num_workers: Option<usize>,
    ctx: &provider_context::T,
    opts: &indexer_options::T,
    namespace_map: &[(String, String)],
    files: Vec<indexable::T>,
) -> Result<(), Failure> {
    use rayon::prelude::*;
    indexer_options::log(opts);
    let num_workers = num_workers.unwrap_or(1);
    let start_time = gettimeofday();
    let num_files = files.len();
    let mut next = crate::bucket::make_list(num_workers as isize, None, Some(115), files);
    let mut buckets = vec![];
    loop {
        let b = next();
        if b.is_empty() {
            break;
        }
        buckets.push(b)
    }
    use super::glean::fact_id;
    let first_fact_id = fact_id::get_next();
    let results: Vec<job_return::T> = crate::multi_worker::call_service_buckets::<RecheckJob, _>(
        ctx,
        (opts.clone(), first_fact_id),
        buckets,
        |r, mut acc: Vec<job_return::T>| {
            acc.push(r);
            acc
        },
        vec![],
        |buckets, _| {
            buckets
                .par_iter()
                .map(|b| {
                    // (The logger of the worker: `[worker-N]` before its lines.)
                    let saved_logger = hh_logger::thread_instance();
                    let logger = hh_logger::Instance::new(None);
                    hh_logger::set_thread_instance(Some(logger));
                    hh_logger::set_id(&format!("worker-{}", rayon::current_thread_index().map_or(0, |i| i + 1)));
                    let saved = fact_id::get_next();
                    fact_id::set_next(first_fact_id);
                    let r = recheck_job(ctx, opts, job_return::neutral(), b);
                    fact_id::set_next(saved);
                    hh_logger::set_thread_instance(saved_logger);
                    r
                })
                .collect()
        },
    );
    let jobs = results.into_iter().fold(job_return::neutral(), job_return::merge);
    // just a uid
    let shard_name = md5_to_hex(&file_info::md5_digest_string(format!("{}", start_time).as_bytes()));
    let global_facts = gen_global_facts(namespace_map, opts.ownership, &shard_name, &jobs.hashes);
    write_facts_file(&opts.out_dir, Some(true), Files::Count(num_files), global_facts)?;
    // TODO remove this log once the workflows use the reindexed_file option
    for r in &jobs.reindexed {
        hh_logger::log(&format!("Reindexed: {}", r))
    }
    if let Some(f) = &opts.referenced_file {
        write_file(&jobs.referenced, f).map_err(|e| Failure(format!("Sys_error: {}", e)))?
    }
    if let Some(f) = &opts.reindexed_file {
        write_file(&jobs.reindexed, f).map_err(|e| Failure(format!("Sys_error: {}", e)))?
    }
    let total_failures = jobs.index_failures;
    if total_failures > 0 {
        hh_logger::log(&format!("Total indexing failures: {}", total_failures))
    }
    if total_failures > MAX_INDEX_FAILURES {
        return Err(Failure(format!(
            "Too many indexing failures ({}). Threshold is {}. Aborting.",
            total_failures, MAX_INDEX_FAILURES
        )));
    }
    let cumulated_elapsed = jobs.elapsed;
    log_elapsed("Processed all batches (cumulated time) in ", cumulated_elapsed);
    let elapsed = gettimeofday() - start_time;
    log_elapsed("Processed all batches in ", elapsed);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_units() {
        assert_eq!(byte_units_to_string_hum(14304), "13.9688K");
        assert_eq!(byte_units_to_string_hum(2), "2B");
        assert_eq!(byte_units_to_string_hum(1024), "1K");
        assert_eq!(byte_units_to_string_hum(3 * 1024 * 1024 + 5), "3M");
    }
}
