// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/find_refs_service.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F6** (plan §7.3).
//!
//! - `Pos.Map.t` (the results of a file, by position) is a `BTreeMap` keyed
//!   by [`PosKey`], ordered by `Pos.compare`; `Pos.Map.union acc m` keeps the
//!   binding of `acc` (`Wrapped_map.union`'s default `combine`).
//! - `Multi_worker.call workers` is [`multi_worker_call`]: the buckets of
//!   `Multi_worker.next workers` (`Bucket.make`'s sizes), run in order on the
//!   calling thread for one worker (`workers = None` and the one-worker case
//!   give the same result in OCaml), on the rayon pool for more, their results
//!   merged in bucket order (one of the orders a run of the OCaml can give).
//! - `Timeout.with_timeout` around the TAST of one file (only with a
//!   `deadline`) is not ported: a Rust computation cannot be interrupted. No
//!   caller passes a deadline (`Server_find_refs.search` gives `None`), so
//!   nothing observable differs; the deadline itself is honoured between
//!   files, as in the OCaml.
//! - `Iter.Cancelled` is the `Err(Cancelled)` of the helpers.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::sync::Arc;

use oxidized::naming_types::KindOfType;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
use crate::decl_provider;
use crate::decl_utils;
use crate::file_info;
use crate::find_refs_wire_format;
use crate::folded_class as cls;
use crate::hh_logger;
use crate::identify_symbol_service;
use crate::naming_provider;
use crate::naming_table;
use crate::path;
use crate::pos;
use crate::provider_context;
use crate::relative_path;
use crate::rt::ocaml_unix;
use crate::s_set;
use crate::search_types::find_refs;
use crate::search_types::find_refs::Member;
use crate::string_utils;
use crate::symbol_occurrence;
use crate::symbol_occurrence::Kind as SO;
use crate::tast;
use crate::tast_provider;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;

type RPSet = relative_path::set::T;

/// The class containing the member can be specified in two ways:
/// - Class_set - as an explicit, pre-computed set of names, which are then
///   compared using string comparison
/// - Subclasses_of - the class's name, in which comparison will use the
///   subtyping relation
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemberClass {
    ClassSet(s_set::T),
    SubclassesOf(String),
}

/// `action_internal`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActionInternal {
    IClass(String),
    IExplicitClass(String),
    IMember(MemberClass, Member),
    IFunction(String),
    IGConst(String),
}

use ActionInternal::*;

/// A key of `Pos.Map`: ordered by `Pos.compare` (file, start offset, end
/// offset).
#[derive(Clone, Debug)]
pub struct PosKey(pub Pos);

impl PartialEq for PosKey {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for PosKey {}

impl PartialOrd for PosKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PosKey {
    fn cmp(&self, other: &Self) -> Ordering {
        pos::compare(&self.0, &other.0)
    }
}

/// `string Pos.Map.t`
type PosMap = BTreeMap<PosKey, String>;

fn singleton(p: &Pos, name: String) -> PosMap {
    let mut m = PosMap::new();
    m.insert(PosKey(p.clone()), name);
    m
}

fn process_fun_id(target_fun: &str, id: (&Pos, &str)) -> PosMap {
    if target_fun == id.1 {
        singleton(id.0, id.1.to_string())
    } else {
        PosMap::new()
    }
}

fn check_if_extends_class(
    ctx: &provider_context::T,
    target_class_name: &str,
    class_name: &str,
) -> bool {
    let class_ = decl_provider::get_class(None, ctx, class_name);
    match class_ {
        decl_entry::T::Found(cls)
            if cls::has_ancestor(&cls, target_class_name)
                || cls::requires_ancestor(&cls, target_class_name) =>
        {
            true
        }
        _ => false,
    }
}

fn is_target_class(ctx: &provider_context::T, target_classes: &MemberClass, class_name: &str) -> bool {
    match target_classes {
        MemberClass::ClassSet(s) => s.contains(class_name),
        MemberClass::SubclassesOf(s) => {
            s == class_name || check_if_extends_class(ctx, s, class_name)
        }
    }
}

fn process_member_id(
    ctx: &provider_context::T,
    target_classes: &MemberClass,
    target_member: &Member,
    class_name: &str,
    mid: (&Pos, &str),
    is_method: bool,
    is_const: bool,
) -> PosMap {
    let member_name = mid.1;
    let is_target = match target_member {
        Member::Method(target_name) => is_method && member_name == target_name,
        Member::Property(target_name) => {
            !is_method
                && !is_const
                && string_utils::lstrip(member_name, "$") == target_name.as_str()
        }
        Member::ClassConst(target_name) => is_const && member_name == target_name,
        Member::Typeconst(_) => false,
    };
    if is_target && is_target_class(ctx, target_classes, class_name) {
        singleton(mid.0, format!("{}::{}", class_name, mid.1))
    } else {
        PosMap::new()
    }
}

fn process_class_id(
    target_class: &str,
    (pos, class_name): (&Pos, &str),
    class_id_type: symbol_occurrence::ClassIdType,
    include_all_ci_types: bool,
) -> PosMap {
    if target_class == class_name {
        match (include_all_ci_types, class_id_type) {
            (false, symbol_occurrence::ClassIdType::Other) => PosMap::new(),
            _ => singleton(pos, class_name.to_string()),
        }
    } else {
        PosMap::new()
    }
}

fn process_taccess(
    ctx: &provider_context::T,
    target_classes: &MemberClass,
    target_typeconst: &str,
    (class_name, tconst_name, p): (&str, &str, &Pos),
) -> PosMap {
    if is_target_class(ctx, target_classes, class_name) && target_typeconst == tconst_name {
        singleton(p, format!("{}::{}", class_name, tconst_name))
    } else {
        PosMap::new()
    }
}

fn process_gconst_id(target_gconst: &str, id: (&Pos, &str)) -> PosMap {
    if target_gconst == id.1 {
        singleton(id.0, id.1.to_string())
    } else {
        PosMap::new()
    }
}

fn add_if_extends_class(
    ctx: &provider_context::T,
    target_class_name: &str,
    class_name: &str,
    mut acc: s_set::T,
) -> s_set::T {
    if check_if_extends_class(ctx, target_class_name, class_name) {
        acc.insert(class_name.to_string());
    }
    acc
}

pub fn find_child_classes_in_files(
    ctx: &provider_context::T,
    target_class_name: &str,
    naming_table: &naming_table::T,
    files: &RPSet,
) -> s_set::T {
    crate::rt::decl_epoch::invalidate_local_caches();
    files.iter().fold(s_set::T::new(), |acc, fn_| {
        match naming_table::get_file_info_exn(naming_table, fn_) {
            Ok(file_info::FileInfo {
                ids: file_info::Ids { classes, .. },
                ..
            }) => classes.iter().fold(acc, |acc, id| {
                add_if_extends_class(ctx, target_class_name, &id.name, acc)
            }),
            Err(naming_table::FileInfoNotFound) => acc,
        }
    })
}

pub fn get_origin_class_name(ctx: &provider_context::T, class_name: &str, member: &Member) -> String {
    let origin = match member {
        Member::Method(method_name) => match decl_provider::get_class(None, ctx, class_name) {
            decl_entry::T::Found(class_) => {
                let get_origin_class = |meth: Option<cls::ClassElt>| meth.map(|meth| meth.ce_origin);
                let origin = get_origin_class(cls::get_method(&class_, method_name));
                if origin.is_some() {
                    origin
                } else {
                    get_origin_class(cls::get_smethod(&class_, method_name))
                }
            }
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
        },
        Member::Property(_) | Member::ClassConst(_) | Member::Typeconst(_) => None,
    };
    origin.unwrap_or_else(|| class_name.to_string())
}

pub fn get_child_classes_files(ctx: &provider_context::T, class_name: &str) -> RPSet {
    match naming_provider::get_type_kind(ctx, class_name) {
        Some(KindOfType::TClass) => {
            let deps_mode = provider_context::get_deps_mode(ctx);
            // Find the files that contain classes that extend class_
            let cid_hash = dep::make(&dep::Variant::Type(class_name.to_string()));
            let extend_deps = crate::decl_compare::get_extend_deps(
                &deps_mode,
                cid_hash,
                &dep_set::singleton(cid_hash),
            );
            naming_provider::get_files(ctx, &extend_deps)
        }
        _ => RPSet::new(),
    }
}

/// `Relative_path.Set.union`
fn union(a: RPSet, b: RPSet) -> RPSet {
    a.union(b)
}

fn get_deps_set(ctx: &provider_context::T, classes: &s_set::T) -> RPSet {
    let deps_mode = provider_context::get_deps_mode(ctx);
    classes.iter().fold(RPSet::new(), |acc, class_name| {
        match naming_provider::get_type_path(ctx, class_name) {
            None => acc,
            Some(fn_) => {
                let dep = dep::Variant::Type(class_name.clone());
                let ideps = typing_deps::get_ideps(&deps_mode, &dep);
                let mut files = naming_provider::get_files(ctx, &ideps);
                files.insert(fn_);
                union(files, acc)
            }
        }
    })
}

/// If `max_deps` is provided and the number of descendants or their
/// dependents exceeds that value, we return Error. If no `max_deps` is
/// provided, we always return Ok.
pub fn get_files_for_descendants_and_dependents_of_members_in_descendants(
    ctx: &provider_context::T,
    class_name: &str,
    max_deps: Option<isize>,
    members: &[typing_deps::dep::member::T],
) -> Result<(RPSet, RPSet), ()> {
    let check = |dep_set: dep_set::T| -> Result<dep_set::T, ()> {
        match max_deps {
            Some(n) if dep_set::cardinal(&dep_set) > n => Err(()),
            _ => Ok(dep_set),
        }
    };
    let mode = provider_context::get_deps_mode(ctx);
    let class_dep = dep_set::singleton(dep::make(&dep::Variant::Type(class_name.to_string())));
    let class_and_descendants_dep = check(typing_deps::add_extend_deps(&mode, &class_dep))?;
    let dependents = dep_set::fold_result(
        &class_and_descendants_dep,
        dep_set::make(),
        |descendant_dep, result| {
            let result = members.iter().fold(result, |result, member| {
                let member_dep = dep::make_member_dep_from_type_dep(descendant_dep, member);
                let member_fanout = typing_deps::get_ideps_from_hash(&mode, member_dep);
                dep_set::union(&result, &member_fanout)
            });
            check(result)
        },
    )?;
    Ok((
        naming_provider::get_files(ctx, &class_and_descendants_dep),
        naming_provider::get_files(ctx, &dependents),
    ))
}

fn get_deps_set_function(ctx: &provider_context::T, f_name: &str) -> RPSet {
    match naming_provider::get_fun_path(ctx, f_name) {
        Some(fn_) => {
            let deps_mode = provider_context::get_deps_mode(ctx);
            let dep = dep::Variant::Fun(f_name.to_string());
            let ideps = typing_deps::get_ideps(&deps_mode, &dep);
            let mut files = naming_provider::get_files(ctx, &ideps);
            files.insert(fn_);
            files
        }
        None => RPSet::new(),
    }
}

fn get_deps_set_gconst(ctx: &provider_context::T, cst_name: &str) -> RPSet {
    match naming_provider::get_const_path(ctx, cst_name) {
        Some(fn_) => {
            let deps_mode = provider_context::get_deps_mode(ctx);
            let dep = dep::Variant::GConst(cst_name.to_string());
            let ideps = typing_deps::get_ideps(&deps_mode, &dep);
            let mut files = naming_provider::get_files(ctx, &ideps);
            files.insert(fn_);
            files
        }
        None => RPSet::new(),
    }
}

fn fold_one_tast(
    ctx: &provider_context::T,
    target: &ActionInternal,
    mut acc: PosMap,
    symbol: &symbol_occurrence::T<Pos>,
) -> PosMap {
    use symbol_occurrence::ReceiverClass::ClassName;
    let symbol_occurrence::T {
        type_, pos, name, ..
    } = symbol;
    let m = match (target, type_) {
        (IMember(classes, Member::Typeconst(tc)), SO::Typeconst(c_name, tc_name)) => {
            process_taccess(ctx, classes, tc, (c_name, tc_name, pos))
        }
        (IMember(classes, member), SO::Method(ClassName(c_name), m_name))
        | (IMember(classes, member), SO::ClassConst(ClassName(c_name), m_name))
        | (IMember(classes, member), SO::Property(ClassName(c_name), m_name))
        | (IMember(classes, member), SO::XhpLiteralAttr(c_name, m_name)) => {
            let mid = (pos, m_name.as_str());
            let is_method = matches!(type_, SO::Method(..));
            let is_const = matches!(type_, SO::ClassConst(..));
            process_member_id(ctx, classes, member, c_name, mid, is_method, is_const)
        }
        (IFunction(fun_name), SO::Function) => process_fun_id(fun_name, (pos, name)),
        (IClass(c), SO::Class(class_id_type)) => {
            let include_all_ci_types = true;
            process_class_id(c, (pos, name), *class_id_type, include_all_ci_types)
        }
        (IExplicitClass(c), SO::Class(class_id_type)) => {
            let include_all_ci_types = false;
            process_class_id(c, (pos, name), *class_id_type, include_all_ci_types)
        }
        (IGConst(cst_name), SO::GConst) => process_gconst_id(cst_name, (pos, name)),
        _ => PosMap::new(),
    };
    // `Pos.Map.union acc m`: the bindings of `acc` win.
    for (k, v) in m {
        acc.entry(k).or_insert(v);
    }
    acc
}

/// `Pos.Map.fold (fun p str acc -> { name = str; pos = p } :: acc) results []`:
/// the results in decreasing position order.
fn results_of_map(results: PosMap) -> Vec<find_refs::T> {
    results
        .into_iter()
        .rev()
        .map(|(PosKey(pos), name)| find_refs::Result { name, pos })
        .collect()
}

fn should_cancel(stream_file: Option<&path::T>, deadline: Option<f64>) -> bool {
    let streaming_file_gone = match stream_file {
        None => false,
        Some(stream_file) => !path::file_exists(stream_file),
    };
    let past_deadline = match deadline {
        None => false,
        Some(d) => ocaml_unix::gettimeofday() >= d,
    };
    streaming_file_gone || past_deadline
}

/// `Iter.Cancelled`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cancelled;

mod iter {
    use super::*;

    /// This datastructure is used for the [find_refs] function, which iterates
    /// over a list of files, finds references in them, and streams them.
    pub struct Acc {
        /// When did we last check for cancellation?
        pub last_cancellation_check: f64,
        /// Accumulates all results from [find_refs]
        pub results: Vec<Vec<find_refs::T>>,
        /// Accumulates only those results that should be streamed at the end of [find_refs]
        pub to_stream_at_end_of_batch: Vec<Vec<find_refs::Absolute>>,
        /// How many individual references have been streamed so far
        pub streamed_so_far: usize,
    }

    pub fn init() -> Acc {
        Acc {
            last_cancellation_check: ocaml_unix::gettimeofday(),
            results: vec![],
            to_stream_at_end_of_batch: vec![],
            streamed_so_far: 0,
        }
    }

    /// We'll check a few times a second whether we should cancel.
    pub fn raise_if_should_cancel(
        mut acc: Acc,
        t_now: f64,
        stream_file: Option<&path::T>,
        deadline: Option<f64>,
    ) -> Result<Acc, Cancelled> {
        if t_now > acc.last_cancellation_check + 0.2 {
            if should_cancel(stream_file, deadline) {
                return Err(Cancelled);
            }
            acc.last_cancellation_check = t_now;
        }
        Ok(acc)
    }

    /// Stream on a per-file basis for the first few results of a find-refs,
    /// but on a per-job basis for the rest. (Each job covers several hundred files).
    /// We do it this way because a find-refs might have 50k results, and it's too much
    /// for 30 processes to do 50k locks between them over the course of the find-refs.
    pub fn stream_file(
        per_file: &[find_refs::T],
        stream_fd: Option<&std::fs::File>,
        t_now: f64,
        t_start: f64,
        mut acc: Acc,
    ) -> Acc {
        match stream_fd {
            None => acc,
            Some(stream_fd) => {
                let max_results_to_stream_by_file = 20;
                let max_secs_to_stream_by_file = 10.0;
                let should_stream_now = acc.streamed_so_far < max_results_to_stream_by_file
                    && t_now < t_start + max_secs_to_stream_by_file;
                let abs_results: Vec<find_refs::Absolute> = per_file
                    .iter()
                    .map(|r| find_refs::Result {
                        name: r.name.clone(),
                        pos: pos::to_absolute(&r.pos),
                    })
                    .collect();
                if should_stream_now {
                    lock_and_append(stream_fd, &abs_results);
                    acc.streamed_so_far += abs_results.len();
                    acc
                } else {
                    acc.to_stream_at_end_of_batch.insert(0, abs_results);
                    acc
                }
            }
        }
    }

    /// This streams any results from the job that haven't already been done on
    /// a per-file basis earlier by [stream_file].
    pub fn stream_job(stream_fd: Option<&std::fs::File>, acc: &Acc) {
        match stream_fd {
            None => {}
            Some(stream_fd) => {
                let all: Vec<find_refs::Absolute> =
                    acc.to_stream_at_end_of_batch.iter().flatten().cloned().collect();
                lock_and_append(stream_fd, &all)
            }
        }
    }

    /// `Find_refs_wire_format.Ide_stream.lock_and_append`: a `Unix_error` is
    /// an exception that ends the job (the server's exception handler).
    fn lock_and_append(stream_fd: &std::fs::File, results: &[find_refs::Absolute]) {
        if let Err(e) = find_refs_wire_format::ide_stream::lock_and_append(stream_fd, results) {
            panic!("Unix.Unix_error: {}", e)
        }
    }
}

/// The TAST of `path`, or `None` when the file does not exist (any
/// exception, when the entry has no contents).
fn tast_of_file(ctx: &provider_context::T, path: &relative_path::T) -> Option<tast::Program> {
    let (_ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
    let compute = || {
        let tast_provider::ComputeTastResult { tast, .. } =
            tast_provider::compute_tast_unquarantined(ctx, &entry);
        Some(tast.under_normal_assumptions)
    };
    // (`Timeout.with_timeout` when there is a deadline: see the module doc.)
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(compute)) {
        Ok(r) => r,
        Err(_) if provider_context::get_file_contents_if_present(&entry).is_none() => None,
        Err(e) => std::panic::resume_unwind(e),
    }
}

/// Either returns results from this batch (concatenated with `job_acc`), or
/// `Err` if cancelled.
pub fn find_refs(
    ctx: &provider_context::T,
    target: &ActionInternal,
    job_acc: Result<Vec<find_refs::T>, ()>,
    files: &[relative_path::T],
    omit_declaration: bool,
    stream_file: Option<&path::T>,
    deadline: Option<f64>,
    t_start: f64,
) -> Result<Vec<find_refs::T>, ()> {
    // The helper function 'results_from_tast' takes a tast, looks at all
    // use-sites in the tast e.g. "foo(1)" is a use-site of symbol foo,
    // and returns a list of use-site-position along with the string name they used.
    let results_from_tast = |tast_opt: Option<tast::Program>| -> Vec<find_refs::T> {
        match tast_opt {
            None => vec![],
            Some(tast) => {
                let results_map = identify_symbol_service::all_symbols(ctx, &tast)
                    .iter()
                    .filter(|symbol| {
                        if omit_declaration {
                            symbol.is_declaration.is_none()
                        } else {
                            true
                        }
                    })
                    .fold(PosMap::new(), |acc, symbol| fold_one_tast(ctx, target, acc, symbol));
                results_of_map(results_map)
            }
        }
    };

    let run = || -> Result<Vec<find_refs::T>, Cancelled> {
        let stream_fd = match stream_file {
            None => None,
            Some(stream_file) => {
                let file = path::to_string(stream_file);
                match std::fs::OpenOptions::new().append(true).open(&file) {
                    Ok(fd) => Some(fd),
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Err(Cancelled),
                    Err(e) => panic!("Unix.Unix_error: {}", e),
                }
            }
        };
        // (`Utils.try_finally ~finally:(Unix.close)`: the file is closed
        // when `stream_fd` is dropped.)
        let mut acc = iter::init();
        for path in files {
            let t_now = ocaml_unix::gettimeofday();
            acc = iter::raise_if_should_cancel(acc, t_now, stream_file, deadline)?;
            let per_file = results_from_tast(tast_of_file(ctx, path));
            acc = iter::stream_file(&per_file, stream_fd.as_ref(), t_now, t_start, acc);
            acc.results.insert(0, per_file);
        }
        iter::stream_job(stream_fd.as_ref(), &acc);
        let job_acc = match job_acc {
            Ok(job_acc) => job_acc,
            Err(()) => return Err(Cancelled),
        };
        // `List.rev_append job_acc (List.concat acc.Iter.results)`
        let mut res: Vec<find_refs::T> = job_acc.into_iter().rev().collect();
        res.extend(acc.results.into_iter().flatten());
        Ok(res)
    };
    run().map_err(|Cancelled| ())
}

pub fn find_refs_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    target: &ActionInternal,
) -> Vec<find_refs::T> {
    let symbols = identify_symbol_service::all_symbols_ctx(ctx, entry);
    let results = symbols
        .iter()
        .filter(|symbol| symbol.is_declaration.is_none())
        .fold(PosMap::new(), |acc, symbol| fold_one_tast(ctx, target, acc, symbol));
    results_of_map(results)
}

/// `Hh_bucket.calculate_bucket_size`
fn calculate_bucket_size(num_jobs: usize, num_workers: usize, max_size: Option<usize>) -> usize {
    let max_size = max_size.unwrap_or(500);
    if num_jobs < num_workers * max_size {
        std::cmp::max(1, 1 + (num_jobs / num_workers))
    } else {
        max_size
    }
}

/// `Multi_worker.next workers jobs`: the buckets, in order (`Bucket.make`:
/// an empty list of jobs gives no bucket).
pub fn multi_worker_buckets<A: Clone>(num_workers: usize, jobs: &[A]) -> Vec<Vec<A>> {
    let num_workers = std::cmp::max(1, num_workers);
    let bucket_size = calculate_bucket_size(jobs.len(), num_workers, None);
    jobs.chunks(bucket_size).map(|c| c.to_vec()).collect()
}

/// `Multi_worker.call workers ~job ~neutral ~merge ~next` over the buckets of
/// `jobs` (see the module doc). `should_stop` is checked before each bucket
/// is handed out (`next` returning `Bucket.Done`). `num_workers = None` is
/// `workers = None`.
pub fn multi_worker_call<A, B, C>(
    num_workers: Option<usize>,
    jobs: &[A],
    job: impl Fn(C, Vec<A>) -> B + Sync,
    neutral: impl Fn() -> C + Sync,
    mut merge: impl FnMut(B, C) -> C,
    should_stop: impl Fn() -> bool + Sync,
) -> C
where
    A: Clone + Send + Sync,
    B: Send,
{
    let workers = num_workers.unwrap_or(1);
    let buckets = multi_worker_buckets(workers, jobs);
    if workers <= 1 {
        let mut acc = neutral();
        for bucket in buckets {
            if should_stop() {
                break;
            }
            let res = job(neutral(), bucket);
            acc = merge(res, acc);
        }
        acc
    } else {
        use rayon::prelude::*;
        let outputs: Vec<Option<B>> = buckets
            .into_par_iter()
            .map(|bucket| {
                if should_stop() {
                    None
                } else {
                    // (A pool thread forgets its memos if the decls moved:
                    // `decl_epoch`'s rule for work items.)
                    crate::rt::decl_epoch::sync_thread();
                    Some(job(neutral(), bucket))
                }
            })
            .collect();
        outputs
            .into_iter()
            .flatten()
            .fold(neutral(), |acc, res| merge(res, acc))
    }
}

fn parallel_find_refs(
    num_workers: Option<usize>,
    files: &[relative_path::T],
    target: &ActionInternal,
    ctx: &provider_context::T,
    omit_declaration: bool,
    stream_file: Option<&path::T>,
    deadline: Option<f64>,
    t_start: f64,
) -> Result<Vec<find_refs::T>, ()> {
    multi_worker_call(
        num_workers,
        files,
        |acc, files: Vec<relative_path::T>| {
            find_refs(
                ctx,
                target,
                acc,
                &files,
                omit_declaration,
                stream_file,
                deadline,
                t_start,
            )
        },
        || Ok(vec![]),
        |output, acc| match (output, acc) {
            (Ok(output), Ok(acc)) => {
                // `List.rev_append output acc`
                let mut res: Vec<find_refs::T> = output.into_iter().rev().collect();
                res.extend(acc);
                Ok(res)
            }
            _ => Err(()),
        },
        // We create the "next" function just once, now; it will dole
        // out chunks of [files] each time it's asked, below.
        || should_cancel(stream_file, deadline),
    )
}

fn get_definitions(ctx: &provider_context::T, action: &ActionInternal) -> Vec<find_refs::T> {
    let resolve = |p: &PosOrDecl| naming_provider::resolve_position(ctx, p);
    match action {
        IMember(MemberClass::ClassSet(classes), Member::Method(method_name)) => {
            classes.iter().fold(vec![], |acc, class_name| {
                match decl_provider::get_class(None, ctx, class_name) {
                    decl_entry::T::Found(class_) => {
                        let add_meth = |get: Option<cls::ClassElt>, mut acc: Vec<find_refs::T>| {
                            match get {
                                Some(meth) if meth.ce_origin == cls::name(&class_) => {
                                    let pos = resolve(&PosOrDecl::from(decl_utils::get_pos(
                                        &meth.ce_type,
                                    )));
                                    acc.insert(
                                        0,
                                        find_refs::Result {
                                            name: method_name.clone(),
                                            pos,
                                        },
                                    );
                                    acc
                                }
                                _ => acc,
                            }
                        };
                        let acc = add_meth(cls::get_method(&class_, method_name), acc);
                        add_meth(cls::get_smethod(&class_, method_name), acc)
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => acc,
                }
            })
        }
        IMember(MemberClass::ClassSet(classes), Member::ClassConst(class_const_name)) => {
            classes.iter().fold(vec![], |acc, class_name| {
                match decl_provider::get_class(None, ctx, class_name) {
                    decl_entry::T::Found(class_) => {
                        let mut acc = acc;
                        match cls::get_const(&class_, class_const_name) {
                            Some(class_const)
                                if class_const.origin.as_str() == cls::name(&class_) =>
                            {
                                let pos = resolve(&PosOrDecl::from(class_const.pos.clone()));
                                acc.insert(
                                    0,
                                    find_refs::Result {
                                        name: class_const_name.clone(),
                                        pos,
                                    },
                                );
                            }
                            _ => {}
                        }
                        acc
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => acc,
                }
            })
        }
        IExplicitClass(class_name) | IClass(class_name) => {
            match naming_provider::get_type_kind(ctx, class_name) {
                Some(KindOfType::TClass) => {
                    match decl_entry::to_option(decl_provider::get_class(None, ctx, class_name)) {
                        Some(class_) => vec![find_refs::Result {
                            name: class_name.clone(),
                            pos: resolve(&cls::pos(&class_)),
                        }],
                        None => vec![],
                    }
                }
                Some(KindOfType::TTypedef) => {
                    match decl_entry::to_option(decl_provider::get_typedef(None, ctx, class_name)) {
                        Some(type_) => vec![find_refs::Result {
                            name: class_name.clone(),
                            pos: resolve(&PosOrDecl::from(type_.pos.clone())),
                        }],
                        None => vec![],
                    }
                }
                None => vec![],
            }
        }
        IFunction(fun_name) => match decl_provider::get_fun(None, ctx, fun_name) {
            decl_entry::T::Found(fe) => vec![find_refs::Result {
                name: fun_name.clone(),
                pos: resolve(&PosOrDecl::from(fe.pos.clone())),
            }],
            _ => vec![],
        },
        IGConst(_)
        | IMember(MemberClass::SubclassesOf(_), _)
        | IMember(_, Member::Property(_) | Member::Typeconst(_)) => {
            // this code path is used only in ServerRename, we can update it at some
            // later time
            vec![]
        }
    }
}

/// `find_references ctx workers target include_defs files ~deadline
/// ~stream_file`; `num_workers = None` is `workers = None`.
pub fn find_references(
    ctx: &provider_context::T,
    num_workers: Option<usize>,
    target: &ActionInternal,
    include_defs: bool,
    files: &[relative_path::T],
    deadline: Option<f64>,
    stream_file: Option<&path::T>,
) -> Vec<find_refs::T> {
    let len = files.len();
    hh_logger::debug(None, None, &format!("find_references: {} files", len));
    let t_start = ocaml_unix::gettimeofday();
    // This "10" threshold is exercised in test/integration/findrefs_multiworker --
    // if you change the threshold here, then please update the test.
    let results = if len < 10 {
        find_refs(ctx, target, Ok(vec![]), files, true, stream_file, deadline, t_start)
    } else {
        parallel_find_refs(num_workers, files, target, ctx, true, stream_file, deadline, t_start)
    };
    match results {
        Err(()) => {
            hh_logger::log("find-references: cancelled");
            vec![]
        }
        Ok(results) => {
            let defs = if include_defs {
                get_definitions(ctx, target)
            } else {
                vec![]
            };
            hh_logger::log(&format!(
                "find-references: {} files -> {} results + {} defs({})",
                len,
                results.len(),
                defs.len(),
                include_defs
            ));
            // `List.rev_append defs results`
            let mut res: Vec<find_refs::T> = defs.into_iter().rev().collect();
            res.extend(results);
            res
        }
    }
}

pub fn find_references_single_file(
    ctx: &provider_context::T,
    target: &ActionInternal,
    file: &relative_path::T,
) -> Vec<find_refs::T> {
    let results = find_refs(
        ctx,
        target,
        Ok(vec![]),
        std::slice::from_ref(file),
        false,
        None,
        None,
        ocaml_unix::gettimeofday(),
    );
    match results {
        Ok(results) => results,
        Err(()) => vec![],
    }
}

pub fn get_dependent_files_function(
    ctx: &provider_context::T,
    _num_workers: Option<usize>,
    f_name: &str,
) -> RPSet {
    // This is performant enough to not need to go parallel for now
    get_deps_set_function(ctx, f_name)
}

pub fn get_dependent_files_gconst(
    ctx: &provider_context::T,
    _num_workers: Option<usize>,
    cst_name: &str,
) -> RPSet {
    // This is performant enough to not need to go parallel for now
    get_deps_set_gconst(ctx, cst_name)
}

pub fn get_dependent_files(
    ctx: &provider_context::T,
    _num_workers: Option<usize>,
    input_set: &s_set::T,
) -> RPSet {
    // This is performant enough to not need to go parallel for now
    get_deps_set(ctx, input_set)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn buckets_as_bucket_make() {
        let jobs: Vec<usize> = (0..12).collect();
        // One worker: one bucket of everything (fewer than 500 jobs).
        assert_eq!(multi_worker_buckets(1, &jobs), vec![jobs.clone()]);
        // 4 workers: 1 + 12 / 4 = 4 per bucket.
        assert_eq!(multi_worker_buckets(4, &jobs).len(), 3);
        assert!(multi_worker_buckets(4, &Vec::<usize>::new()).is_empty());
        let many: Vec<usize> = (0..1200).collect();
        assert_eq!(
            multi_worker_buckets(1, &many)
                .iter()
                .map(|b| b.len())
                .collect::<Vec<_>>(),
            vec![500, 500, 200]
        );
    }

    #[test]
    fn single_threaded_merge_order() {
        // `List.rev_append output acc` over buckets [0..4], [4..8], ...
        let jobs: Vec<usize> = (0..1001).collect();
        let r = multi_worker_call(
            None,
            &jobs,
            |_acc: Vec<usize>, b: Vec<usize>| vec![b[0]],
            Vec::new,
            |out, acc| {
                let mut r: Vec<usize> = out.into_iter().rev().collect();
                r.extend(acc);
                r
            },
            || false,
        );
        assert_eq!(r, vec![1000, 500, 0]);
    }
}
