// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_redecl_service.ml` (+ `.mli`). See `hh/PORTING.md`.
//!
//! On the fly defs-declaration are called when the user modified a file
//! and we are not at initilalization time anymore. Therefore, we have a bit
//! more work to do. We need to calculate what must be re-checked.
//!
//! Owned by **R1** (plan §3.1).
//!
//! # Workers
//!
//! The OCaml sends buckets of files (or classes) to its worker processes
//! (`Multi_worker.call`) when there are at least 10 of them, and passes the
//! defs through shared memory (`OnTheFlyStore`, `ClassSetStore`). Here the
//! buckets (of at most `bucket_size`) go to the rayon pool, and the data is
//! shared by reference; the merges are those of the OCaml (fanout unions,
//! sums, set unions), so the results do not depend on the order the buckets
//! finish in, and equal those of the sequential path. The progress messages
//! (`Server_progress.write_percentage`) are written as the buckets are
//! merged, as in the OCaml (only with the feature `server`: `Server_progress`
//! is a server module).
//!
//! # Backend
//!
//! The OCaml daemon runs the `Shared_memory` backend (`rust_provider_backend`
//! is turned off at startup because `shm_use_sharded_hashtbl` is false, and
//! `populate_member_heaps` is true): the branches ported are the `| _ ->`
//! ones, on the heaps of shared memory. The port has one in-process store,
//! the `Ctx`; [`decl_heap`] maps each heap operation the OCaml does here to
//! it:
//!
//! - `Decl_heap.Funs`, `Typedefs`, `GConsts`, `Modules` (the shallow decls of
//!   the non-classes) and `Shallow_classes_heap.Classes`
//!   (`Old_shallow_classes_provider`): the decl stores of the `Ctx`, whose old
//!   entries are its side map of old decls (plan D3): `oldify_batch`,
//!   `get_old_batch`, `remove_old_batch`, `remove_batch` are
//!   `Ctx::oldify_defs`, `get_old_defs`, `remove_old_defs`, `remove_defs` on
//!   the names of that kind (with `Shared_mem`'s batch semantics: oldify moves
//!   a live entry to the old ones, or deletes the old entry of a name without
//!   a live one).
//! - `Decl_heap.Classes` (the folded classes): the folded store of the `Ctx`.
//!   `remove_batch` and `oldify_batch` are `Ctx::remove_folded_classes`: an
//!   old folded class is only ever read by `Decl_class_elements.get_for_classes
//!   ~old:true`, i.e. to find the member-heap entries to drop, which do not
//!   exist here (next item); so `remove_old_batch` of folded classes has
//!   nothing to do. A folded class that is not there is folded again on
//!   demand, as `Decl_folded_class.class_decl_if_missing` does.
//! - `Decl_class_elements` (the member heaps `Decl_heap.Props`, `Methods`,
//!   ...): no counterpart. They are a cache of the members of each class,
//!   filled from the shallow decl of the member's origin on a miss
//!   (`Decl_store.lookup_or`); the members of a folded class of the `Ctx` are
//!   always read from the shallow decls of the store. Dropping (oldifying,
//!   removing) entries of that cache is therefore a no-op here, and
//!   [`get_elems`], whose only use is to name the entries to drop, gives empty
//!   maps (it logs and reports progress as the OCaml does), of a type,
//!   [`Elems`], that cannot hold anything.
//!
//! `Shared_mem.invalidate_local_caches` and `Shared_mem.GC.collect` have no
//! counterpart: what they act on (the caches of the shared-memory heaps of
//! this process, the shared heap) does not exist. The per-thread caches of
//! the typing core are reset by the context generation and the decl epoch
//! (plan D5) after the redeclaration; the redeclaration itself reads the
//! decl stores of the `Ctx` directly.
//!
//! # Declaring the files
//!
//! `Decl.make_env` parses a file, caches its decls
//! (`direct_decl_parse_and_cache`) and folds its classes. In the OCaml the
//! fold of a class whose parent is in another changed file that has not been
//! declared yet finds the parent anyway: a miss in the shallow class heap is
//! served by parsing the file the naming table binds the name to (lazy decl,
//! `Decl_provider_internals.get_shallow_class`). So that the same holds whatever the order
//! the files are declared in, [`redeclare_files`] first parses and caches
//! every file, then folds: the stores then have the new decls of all the
//! files before any fold, as they would after the lazy parses of the OCaml.
//! The parse runs on the pool; the caching (`Ctx::add_shallow_decls`, cheap)
//! runs on the calling thread in the order of the files.

use std::sync::Arc;
use std::sync::Mutex;

use rayon::prelude::*;

use crate::ctx::Ctx;
use crate::decl;
use crate::decl_compare;
use crate::decl_compare::versioned_file_info;
use crate::decl_compare::versioned_names;
use crate::decl_compare::versioned_s_set;
use crate::decl_provider;
use crate::decl_provider::FunDecl;
use crate::decl_provider::GconstDecl;
use crate::decl_provider::ModuleDecl;
use crate::decl_provider::TypedefDecl;
use crate::decl_utils;
use crate::exception;
use crate::fanout;
use crate::file_info;
use crate::hh_logger;
use crate::naming_provider;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::rt::ocaml_unix::gettimeofday;
use crate::s_map;
use crate::s_set;
use crate::shallow_class_fanout;
use crate::shallow_decl_compare;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;
use crate::typing_deps::visited_set;
use crate::typing_deps_mode;

type RPMap<A> = crate::relative_path::map::T<A>;
type RPSet = crate::relative_path::set::T;

/// `get_classes_in_file`
pub type GetClassesInFile<'a> = &'a (dyn Fn(&RelativePath) -> s_set::T + Sync);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RedoTypeDeclResult {
    pub fanout: fanout::T,
    /// The number of old decls we didn't have when calculating the redecl.
    pub old_decl_missing_count: isize,
}

/// `Decl_class_elements.t` (see the module documentation): nothing.
pub type DeclClassElements = std::convert::Infallible;

/// `Decl_class_elements.t S_map.t`: always empty.
pub type Elems = s_map::T<DeclClassElements>;

const LVL: hh_logger::level::T = hh_logger::level::T::Debug;

/// `Hh_logger.log ~lvl`
fn log_lvl(msg: &str) {
    hh_logger::log_with(Some(LVL), None, msg)
}

/// `Hh_logger.log_duration ~lvl`
fn log_duration_lvl(name: &str, t: f64) -> f64 {
    hh_logger::log_duration(Some(LVL), None, name, t)
}

/// `Server_progress.with_frame` (a server module: without the feature
/// `server`, just `f ()`).
fn server_progress_with_frame<A>(f: impl FnOnce() -> A) -> A {
    #[cfg(feature = "server")]
    {
        crate::server_progress::with_frame(None, f)
    }
    #[cfg(not(feature = "server"))]
    {
        f()
    }
}

/// `Server_progress.write_percentage ~operation ~done_count ~total_count
/// ~unit ~extra:None`
fn server_progress_write_percentage(
    operation: &str,
    done_count: isize,
    total_count: isize,
    unit: &str,
) {
    #[cfg(feature = "server")]
    crate::server_progress::write_percentage(operation, done_count, total_count, unit, None);
    #[cfg(not(feature = "server"))]
    let _ = (operation, done_count, total_count, unit);
}

/// The buckets of `Multi_worker.next ~max_size:bucket_size`.
fn buckets<T>(xs: &[T], bucket_size: isize) -> std::slice::Chunks<'_, T> {
    xs.chunks(bucket_size.max(1) as usize)
}

/// [`buckets`], on the pool.
fn par_buckets<T: Sync>(xs: &[T], bucket_size: isize) -> rayon::slice::Chunks<'_, T> {
    xs.par_chunks(bucket_size.max(1) as usize)
}

/// `try f () with exn -> Printf.printf "Error: %s\n" (Exception.get_ctor_string e);
/// Out_channel.flush stdout; Exception.reraise e`
fn print_error_and_reraise<A>(f: impl FnOnce() -> A) -> A {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(a) => a,
        Err(payload) => {
            use std::io::Write as _;
            let e = exception::wrap(payload);
            print!("Error: {}\n", exception::get_ctor_string(&e));
            let _ = std::io::stdout().flush();
            exception::reraise(e)
        }
    }
}

/// `compute_deps_neutral`
fn compute_deps_neutral() -> (fanout::T, isize) {
    (fanout::empty(), 0)
}

fn reconcile_parallel_redecl_fanout(
    during_init: bool,
    deps_mode: &typing_deps_mode::T,
    fanout: fanout::T,
) -> fanout::T {
    if during_init {
        fanout
    } else {
        // Dependency edges discovered during typechecking are registered in
        // the master process. Redecl workers can therefore compute fanout
        // from a stale process-local view of the dependency graph.
        let master_dependents = dep_set::diff(
            &typing_deps::add_typing_deps(deps_mode, &fanout.changed),
            &fanout.changed,
        );
        let to_recheck = dep_set::union(&fanout.to_recheck, &master_dependents);
        fanout::T {
            to_recheck,
            ..fanout
        }
    }
}

pub mod for_test {
    pub fn reconcile_parallel_redecl_fanout(
        during_init: bool,
        deps_mode: &crate::typing_deps_mode::T,
        fanout: crate::fanout::T,
    ) -> crate::fanout::T {
        super::reconcile_parallel_redecl_fanout(during_init, deps_mode, fanout)
    }
}

/// Given a set of functions, compare the old and the new decl and deduce
/// what must be rechecked accordingly.
fn compare_funs_and_get_fanout(
    ctx: &Arc<Ctx>,
    old_funs: &s_map::T<Option<FunDecl>>,
    fanout_acc: fanout::T,
    funs: &versioned_s_set::Diff,
) -> (fanout::T, isize) {
    let (fanout, old_funs_missing) = decl_compare::get_funs_deps(ctx, old_funs, funs);
    let fanout_acc = fanout::union(&fanout, &fanout_acc);
    (fanout_acc, old_funs_missing)
}

/// Given a set of typedefs, compare the old and the new decl and deduce
/// what must be rechecked accordingly.
fn compare_types_and_get_fanout(
    ctx: &Arc<Ctx>,
    old_types: &s_map::T<Option<TypedefDecl>>,
    fanout_acc: fanout::T,
    types: &versioned_s_set::Diff,
) -> (fanout::T, isize) {
    let (fanout, old_types_missing) = decl_compare::get_types_deps(ctx, old_types, types);
    let fanout_acc = fanout::union(&fanout, &fanout_acc);
    (fanout_acc, old_types_missing)
}

/// Given a set of global constants, compare the old and the new decl and
/// deduce what must be rechecked accordingly.
fn compare_gconsts_and_get_fanout(
    ctx: &Arc<Ctx>,
    old_gconsts: &s_map::T<Option<GconstDecl>>,
    fanout_acc: fanout::T,
    gconsts: &versioned_s_set::Diff,
) -> (fanout::T, isize) {
    let (fanout, old_gconsts_missing) = decl_compare::get_gconsts_deps(ctx, old_gconsts, gconsts);
    let fanout_acc = fanout::union(&fanout, &fanout_acc);
    (fanout_acc, old_gconsts_missing)
}

/// Given a set of modules, compare the old and the new decl and deduce what
/// must be rechecked accordingly.
fn compare_modules_and_get_fanout(
    ctx: &Arc<Ctx>,
    old_modules: &s_map::T<Option<ModuleDecl>>,
    fanout_acc: fanout::T,
    modules: &versioned_s_set::Diff,
) -> (fanout::T, isize) {
    let (fanout, old_modules_missing) = decl_compare::get_modules_deps(ctx, old_modules, modules);
    let fanout_acc = fanout::union(&fanout, &fanout_acc);
    (fanout_acc, old_modules_missing)
}

// Redeclares a list of files
// And then computes the files that must be redeclared/rechecked by looking
// at what changed in the signatures of the classes/functions.

/// Compute decls in files. Return errors raised during decling.
///
/// `List.iter filel ~f:(fun fn -> Decl.make_env ~sh:Shared_mem.Uses ctx fn)`,
/// with all the parses and caches before the folds (see the module
/// documentation). The parses run on the pool when `parallel`.
fn redeclare_files(
    ctx: &Arc<Ctx>,
    filel: &[RelativePath],
    parallel: bool,
) -> Vec<Vec<pos::TypeName>> {
    let parsed: Vec<_> = if parallel {
        filel
            .par_iter()
            .map(|fn_| decl::direct_decl_parse(ctx, fn_))
            .collect()
    } else {
        filel
            .iter()
            .map(|fn_| decl::direct_decl_parse(ctx, fn_))
            .collect()
    };
    filel
        .iter()
        .zip(parsed)
        .map(|(fn_, decls)| match decls {
            None => vec![],
            Some(decls) => {
                let classes = decl::classes_of_decls(&decls);
                decl::cache_decls(ctx, fn_, decls);
                classes
            }
        })
        .collect()
}

/// Invalidate local caches and compute decls in files. Return errors raised
/// during decling.
fn decl_files(ctx: &Arc<Ctx>, filel: &[RelativePath]) {
    // `Shared_mem.invalidate_local_caches ()`: see the module documentation.
    for classes in redeclare_files(ctx, filel, false) {
        decl::declare_folded_classes(ctx, &classes)
    }
}

fn compare_decls_and_get_fanout(
    ctx: &Arc<Ctx>,
    defs_per_file: &RPMap<versioned_names::T>,
    filel: &[RelativePath],
) -> (fanout::T, isize) {
    let mut all_defs = versioned_names::empty();
    for fn_ in filel {
        // `Relative_path.Map.find` raises `Not_found`.
        let names = match defs_per_file.get(fn_) {
            Some(names) => names,
            None => panic!("Not_found"),
        };
        all_defs = versioned_names::merge(&all_defs, names);
    }
    // Fetching everything at once is faster
    let (old_funs, old_types, old_consts, old_modules) = {
        let file_info::Names {
            classes: _,
            funs,
            types,
            consts,
            modules,
        } = &all_defs.old_names;
        // `match Provider_backend.get () with ... | _ ->`
        (
            decl_heap::funs::get_old_batch(ctx, funs),
            decl_heap::typedefs::get_old_batch(ctx, types),
            decl_heap::gconsts::get_old_batch(ctx, consts),
            decl_heap::modules::get_old_batch(ctx, modules),
        )
    };
    let versioned_file_info::diff::T {
        funs,
        types,
        gconsts,
        modules,
    } = versioned_file_info::diff_names(&all_defs);
    let acc = fanout::empty();
    let (acc, old_funs_missing) = compare_funs_and_get_fanout(ctx, &old_funs, acc, &funs);
    let (acc, old_types_missing) = compare_types_and_get_fanout(ctx, &old_types, acc, &types);
    let (acc, old_gconsts_missing) =
        compare_gconsts_and_get_fanout(ctx, &old_consts, acc, &gconsts);
    let (acc, old_modules_missing) =
        compare_modules_and_get_fanout(ctx, &old_modules, acc, &modules);
    let old_decl_missing_count =
        old_funs_missing + old_types_missing + old_gconsts_missing + old_modules_missing;
    (acc, old_decl_missing_count)
}

// Load the environment and then redeclare

/// Invalidate local caches and compute decls in files. Return the file
/// count.
///
/// The folds of a bucket (the parses and caches of all the buckets are done
/// before, by [`redeclare_files`]).
fn decl_files_job(ctx: &Arc<Ctx>, classes: &[Vec<pos::TypeName>]) -> (isize, ()) {
    print_error_and_reraise(|| {
        for classes in classes {
            decl::declare_folded_classes(ctx, classes)
        }
        (classes.len() as isize, ())
    })
}

fn load_defs_compare_and_get_fanout(
    ctx: &Arc<Ctx>,
    defs_per_file: &RPMap<versioned_names::T>,
    filel: &[RelativePath],
) -> ((fanout::T, isize), isize) {
    print_error_and_reraise(|| {
        // `OnTheFlyStore.load ()`: `defs_per_file`
        let (fanout, old_decl_missing_count) =
            compare_decls_and_get_fanout(ctx, defs_per_file, filel);
        ((fanout, filel.len() as isize), old_decl_missing_count)
    })
}

// Merges the results coming back from the different workers

fn merge_on_the_fly(
    files_initial_count: isize,
    files_declared_count: &mut isize,
    (count, ()): (isize, ()),
    (): (),
) {
    *files_declared_count += count;
    server_progress_write_percentage(
        "declaring",
        *files_declared_count,
        files_initial_count,
        "files",
    );
}

fn merge_compute_deps(
    files_initial_count: isize,
    files_computed_count: &mut isize,
    ((fanout1, computed_count), old_decl_missing_count1): ((fanout::T, isize), isize),
    (fanout2, old_decl_missing_count2): (fanout::T, isize),
) -> (fanout::T, isize) {
    *files_computed_count += computed_count;
    let fanout = fanout::union(&fanout1, &fanout2);
    server_progress_write_percentage(
        "computing dependencies of",
        *files_computed_count,
        files_initial_count,
        "files",
    );
    (fanout, old_decl_missing_count1 + old_decl_missing_count2)
}

// The parallel worker

/// Invalidate local decl caches and recompute decls in files in parallel.
/// Compare new and old decls and deduce the fanout.
/// Return errors raised during decling, fanout and missing old decl count.
fn parallel_redecl_compare_and_get_fanout(
    ctx: &Arc<Ctx>,
    bucket_size: isize,
    defs_per_file: &RPMap<versioned_names::T>,
    fnl: &[RelativePath],
) -> (fanout::T, isize) {
    server_progress_with_frame(|| {
        // `try ... with exn -> if Shared_mem.SMTelemetry.is_heap_overflow ()
        // then Exit.exit Exit_status.Redecl_heap_overflow else
        // Exception.reraise e`: there is no shared heap to overflow, so a
        // panic goes on.
        // `OnTheFlyStore.store defs_per_file`: shared by reference.
        let files_initial_count = fnl.len() as isize;
        let files_declared_count = Mutex::new(0isize);
        let t = gettimeofday();
        log_lvl(&format!(
            "Declaring on-the-fly {} files",
            files_initial_count
        ));
        server_progress_write_percentage(
            "declaring",
            *files_declared_count.lock().unwrap(),
            files_initial_count,
            "files",
        );
        let classes = redeclare_files(ctx, fnl, true);
        par_buckets(&classes, bucket_size).for_each(|bucket| {
            let result = decl_files_job(ctx, bucket);
            let mut count = files_declared_count.lock().unwrap();
            merge_on_the_fly(files_initial_count, &mut count, result, ())
        });
        let t = log_duration_lvl("Finished declaring on-the-fly", t);
        log_lvl(&format!(
            "Computing dependencies of {} files",
            files_initial_count
        ));
        let files_computed_count = Mutex::new(0isize);
        server_progress_write_percentage(
            "computing dependencies of",
            0,
            files_initial_count,
            "files",
        );
        let acc = Mutex::new(compute_deps_neutral());
        par_buckets(fnl, bucket_size).for_each(|bucket| {
            let result = load_defs_compare_and_get_fanout(ctx, defs_per_file, bucket);
            let mut count = files_computed_count.lock().unwrap();
            let mut acc = acc.lock().unwrap();
            let previous = std::mem::replace(&mut *acc, compute_deps_neutral());
            *acc = merge_compute_deps(files_initial_count, &mut count, result, previous);
        });
        let (fanout, old_decl_missing_count) = acc.into_inner().unwrap();
        let _t: f64 = log_duration_lvl("Finished computing dependencies", t);
        // `OnTheFlyStore.clear ()`
        (fanout, old_decl_missing_count)
    })
}

// Code invalidating the heap

/// The heaps of shared memory that this module acts on, over the `Ctx` (see
/// the module documentation).
pub(crate) mod decl_heap {
    use std::collections::BTreeSet;

    use super::*;

    /// The names of `kind`, as a `File_info.names` for the `Ctx` primitives.
    fn names_of(
        set: impl Fn(&mut file_info::Names) -> &mut BTreeSet<String>,
        names: &BTreeSet<String>,
    ) -> file_info::Names {
        let mut n = file_info::empty_names();
        *set(&mut n) = names.clone();
        n
    }

    macro_rules! shallow_heap {
        ($m:ident, $field:ident, $old_field:ident, $ty:ty) => {
            pub mod $m {
                use super::*;

                fn names(names: &BTreeSet<String>) -> file_info::Names {
                    names_of(|n| &mut n.$field, names)
                }

                pub fn oldify_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
                    ctx.oldify_defs(&names(keys))
                }

                pub fn remove_old_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
                    ctx.remove_old_defs(&names(keys))
                }

                pub fn remove_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
                    ctx.remove_defs(&names(keys))
                }

                pub fn get_old_batch(
                    ctx: &Arc<Ctx>,
                    keys: &BTreeSet<String>,
                ) -> s_map::T<Option<$ty>> {
                    ctx.get_old_defs(&names(keys))
                        .$old_field
                        .into_iter()
                        .collect()
                }
            }
        };
    }

    shallow_heap!(funs, funs, funs, FunDecl);
    shallow_heap!(typedefs, types, typedefs, TypedefDecl);
    shallow_heap!(gconsts, consts, consts, GconstDecl);
    shallow_heap!(modules, modules, modules, ModuleDecl);

    /// `Shallow_classes_heap.Classes.remove_batch`
    pub fn shallow_classes_remove_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
        ctx.remove_defs(&names_of(|n| &mut n.classes, keys))
    }

    /// `Decl_heap.Classes`, the folded classes.
    pub mod classes {
        use super::*;

        /// `Decl_heap.Classes.oldify_batch`: the folded classes leave the
        /// store (an old folded class is never read here).
        pub fn oldify_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
            ctx.remove_folded_classes(&keys.iter().cloned().collect())
        }

        /// `Decl_heap.Classes.remove_old_batch`: nothing is kept.
        pub fn remove_old_batch(_ctx: &Arc<Ctx>, _keys: &BTreeSet<String>) {}

        /// `Decl_heap.Classes.remove_batch`
        pub fn remove_batch(ctx: &Arc<Ctx>, keys: &BTreeSet<String>) {
            ctx.remove_folded_classes(&keys.iter().cloned().collect())
        }

        /// `Decl_heap.Classes.get c`: the folded class of `c` if it is in
        /// the folded store, without folding it.
        pub fn get(ctx: &Arc<Ctx>, c: &str) -> Option<Arc<ty::decl::FoldedClass<crate::ctx::R>>> {
            ctx.get_folded_class_if_present(c)
        }
    }

    /// `Decl_class_elements.oldify_all`, `remove_old_all`, `remove_all`: the
    /// member heaps have no counterpart (`elems` is always empty).
    pub fn decl_class_elements_noop(elems: &Elems) {
        let _ = elems;
    }
}

/// Oldify provided defs and elements (a.k.a. members).
/// This is equivalent to moving a the decls for those defs to some heap of
/// old decls, i.e. they will only be retrievable when querying old values.
/// For classes, it oldifies both shallow and folded classes
fn oldify_defs(ctx: &Arc<Ctx>, names: &file_info::Names, elems: &Elems, collect_garbage: bool) {
    let file_info::Names {
        funs,
        classes,
        types,
        consts,
        modules,
    } = names;
    // `match Provider_backend.get () with ... | _ ->`
    decl_heap::funs::oldify_batch(ctx, funs);
    decl_heap::decl_class_elements_noop(elems); // `Decl_class_elements.oldify_all elems`
    decl_heap::classes::oldify_batch(ctx, classes);
    crate::old_shallow_classes_provider::oldify_batch(ctx, &classes.iter().cloned().collect());
    decl_heap::typedefs::oldify_batch(ctx, types);
    decl_heap::gconsts::oldify_batch(ctx, consts);
    decl_heap::modules::oldify_batch(ctx, modules);
    // `if collect_garbage then Shared_mem.GC.collect `gentle`
    let _ = collect_garbage;
}

/// The first `remove_old_defs` of the OCaml (the one with the elements),
/// which the public [`remove_old_defs`] shadows.
fn remove_old_defs_with_elems(ctx: &Arc<Ctx>, names: &file_info::Names, elems: &Elems) {
    let file_info::Names {
        funs,
        classes,
        types,
        consts,
        modules,
    } = names;
    // `match Provider_backend.get () with ... | _ ->`
    decl_heap::funs::remove_old_batch(ctx, funs);
    decl_heap::decl_class_elements_noop(elems); // `Decl_class_elements.remove_old_all elems`
    decl_heap::classes::remove_old_batch(ctx, classes);
    crate::old_shallow_classes_provider::remove_old_batch(ctx, &classes.iter().cloned().collect());
    decl_heap::typedefs::remove_old_batch(ctx, types);
    decl_heap::gconsts::remove_old_batch(ctx, consts);
    decl_heap::modules::remove_old_batch(ctx, modules);
    // `Shared_mem.GC.collect `gentle`
}

/// Remove provided defs and elements from the heap of current decls.
/// For classes, it removes both shallow and folded classes.
///
/// (`elems`, always empty here, is dropped from the signature: plan §3.2.)
///
/// Test-only.
pub fn remove_defs(names: &file_info::Names, ctx: &Arc<Ctx>, collect_garbage: bool) {
    let file_info::Names {
        funs,
        classes,
        types,
        consts,
        modules,
    } = names;
    // `match Provider_backend.get () with ... | _ ->`
    decl_heap::funs::remove_batch(ctx, funs);
    // `Decl_class_elements.remove_all elems`: nothing.
    decl_heap::classes::remove_batch(ctx, classes);
    decl_heap::shallow_classes_remove_batch(ctx, classes);
    decl_heap::typedefs::remove_batch(ctx, types);
    decl_heap::gconsts::remove_batch(ctx, consts);
    decl_heap::modules::remove_batch(ctx, modules);
    // `if collect_garbage then Shared_mem.GC.collect `gentle`
    let _ = collect_garbage;
}

/// `is_descendant_of_any_of classes c` returns whether class `c` is a member
/// of or is a descendant of any of the `classes`.
fn is_descendant_of_any_of(ctx: &Arc<Ctx>, classes: &s_set::T, c: &str) -> bool {
    if classes.contains(c) {
        true
    } else {
        match decl_heap::classes::get(ctx, c) {
            None => false,
            // it might be a descendant class, but we are only doing this
            // check for the purpose of invalidating things from the heap
            // - if it's already not there, then we don't care.
            Some(c) => {
                fn intersection_nonempty<'a>(
                    s1: impl IntoIterator<Item = &'a pos::TypeName>,
                    s2: &s_set::T,
                ) -> bool {
                    s1.into_iter().any(|x| s2.contains(x.as_str()))
                }
                c.ancestors.keys().any(|c| classes.contains(c.as_str()))
                    || intersection_nonempty(&c.extends, classes)
                    || intersection_nonempty(&c.xhp_attr_deps, classes)
                    || intersection_nonempty(&c.req_ancestors_extends, classes)
            }
        }
    }
}

/// `add_classes_in_files get_classes files classes_acc` adds to
/// `classes_acc` the classes in `files`, obtained with `get_classes file` for
/// `file` in `files`
fn add_classes_in_files(
    get_classes: GetClassesInFile<'_>,
    files: &RPSet,
    classes_acc: s_set::T,
) -> s_set::T {
    let mut acc = classes_acc;
    for fn_ in files.iter() {
        acc = acc.union(get_classes(fn_));
    }
    acc
}

/// Return the files containing all descendants of provided classes
fn get_files_of_descendants(ctx: &Arc<Ctx>, class_names: &s_set::T) -> RPSet {
    let mode = provider_context::get_deps_mode(ctx);
    let mut acc = dep_set::make();
    for c in class_names.iter() {
        acc = typing_deps::get_extend_deps(
            &mode,
            &mut visited_set::make(),
            dep::make(&dep::Variant::Type(c.clone())),
            &acc,
        );
    }
    naming_provider::get_files(ctx, &acc)
}

/// `filter_descendant_classes classes ~maybe_descendant_classes` filters
/// `maybe_descendant_classes` to keep only those which are a descendant or a
/// class in `classes`, or a member of `classes`.
fn filter_descendant_classes(
    ctx: &Arc<Ctx>,
    classes: &s_set::T,
    maybe_descendant_classes: &[String],
) -> Vec<String> {
    maybe_descendant_classes
        .iter()
        .filter(|c| is_descendant_of_any_of(ctx, classes, c))
        .cloned()
        .collect()
}

fn load_and_filter_descendant_classes(
    ctx: &Arc<Ctx>,
    classes: &s_set::T,
    maybe_descendant_classes: &[String],
) -> (Vec<String>, isize) {
    // `ClassSetStore.load ()`: `classes`
    (
        filter_descendant_classes(ctx, classes, maybe_descendant_classes),
        maybe_descendant_classes.len() as isize,
    )
}

fn merge_descendant_classes(
    classes_initial_count: isize,
    classes_filtered_count: &mut isize,
    (descendant_classes, filtered): (Vec<String>, isize),
    acc: Vec<String>,
) -> Vec<String> {
    *classes_filtered_count += filtered;
    server_progress_write_percentage(
        "filtering",
        *classes_filtered_count,
        classes_initial_count,
        "classes",
    );
    let mut descendant_classes = descendant_classes;
    descendant_classes.extend(acc);
    descendant_classes
}

fn filter_descendant_classes_parallel(
    ctx: &Arc<Ctx>,
    bucket_size: isize,
    classes: &s_set::T,
    maybe_descendant_classes: &[String],
) -> Vec<String> {
    let classes_initial_count = maybe_descendant_classes.len() as isize;
    if classes_initial_count < 10 {
        filter_descendant_classes(ctx, classes, maybe_descendant_classes)
    } else {
        server_progress_with_frame(|| {
            // `ClassSetStore.store classes`: shared by reference.
            let classes_filtered_count = Mutex::new(0isize);
            let t = gettimeofday();
            log_lvl(&format!(
                "Filtering {} descendant classes",
                classes_initial_count
            ));
            server_progress_write_percentage("filtering", 0, classes_initial_count, "classes");
            let res = Mutex::new(vec![]);
            par_buckets(maybe_descendant_classes, bucket_size).for_each(|c| {
                let result = load_and_filter_descendant_classes(ctx, classes, c);
                let mut count = classes_filtered_count.lock().unwrap();
                let mut res = res.lock().unwrap();
                let acc = std::mem::take(&mut *res);
                *res = merge_descendant_classes(classes_initial_count, &mut count, result, acc);
            });
            let _t: f64 = log_duration_lvl("Finished filtering descendant classes", t);
            // `ClassSetStore.clear ()`
            res.into_inner().unwrap()
        })
    }
}

/// Exposed for tests only!
/// For a set of classes, return all the declared classes that share their
/// class elements (see Decl_class_elements).
/// Not for general use case since it doesn't use lazy decl and makes sense
/// only in a very particular use case of invalidate_type_decl.
pub fn get_descendant_classes(
    ctx: &Arc<Ctx>,
    bucket_size: isize,
    get_classes: GetClassesInFile<'_>,
    classes: &s_set::T,
) -> s_set::T {
    let files_of_descendants = get_files_of_descendants(ctx, classes);
    let maybe_descendant_classes: Vec<String> =
        add_classes_in_files(get_classes, &files_of_descendants, classes.clone())
            .into_iter()
            .collect();
    filter_descendant_classes_parallel(ctx, bucket_size, classes, &maybe_descendant_classes)
        .into_iter()
        .collect()
}

fn merge_elements(
    classes_initial_count: isize,
    classes_processed_count: &mut isize,
    (elements, count): (Elems, isize),
    acc: Elems,
) -> Elems {
    *classes_processed_count += count;
    let acc = elements.union(acc);
    server_progress_write_percentage(
        "getting members of",
        *classes_processed_count,
        classes_initial_count,
        "classes",
    );
    acc
}

/// `Decl_class_elements.get_for_classes ~old classes`: the member heaps it
/// reads have no counterpart (see the module documentation).
fn decl_class_elements_get_for_classes(old: bool, classes: &[String]) -> Elems {
    let _ = (old, classes);
    Elems::new()
}

/// Get the `Decl_class_elements.t`s (a.k.a. members) corresponding to the
/// classes contained in `defs`. Get them from the element heaps.
fn get_elems(bucket_size: isize, old: bool, defs: &file_info::Names) -> Elems {
    let classes: Vec<String> = defs.classes.iter().cloned().collect();
    // Getting the members of a class requires fetching the class from the
    // heap. Doing this for too many classes will cause a large amount of
    // allocations to be performed on the master process triggering the GC
    // and slowing down redeclaration. Using the workers prevents this from
    // occurring
    let classes_initial_count = classes.len() as isize;
    let t = gettimeofday();
    log_lvl(&format!(
        "Getting elements of {} classes",
        classes_initial_count
    ));
    let elements = if classes_initial_count < 10 {
        decl_class_elements_get_for_classes(old, &classes)
    } else {
        server_progress_with_frame(|| {
            let mut classes_processed_count = 0;
            server_progress_write_percentage(
                "getting members of",
                classes_processed_count,
                classes_initial_count,
                "classes",
            );
            // (Nothing to compute on the pool: the buckets are merged here.)
            let mut acc = Elems::new();
            for c in buckets(&classes, bucket_size) {
                let result = (
                    decl_class_elements_get_for_classes(old, c),
                    c.len() as isize,
                );
                acc = merge_elements(
                    classes_initial_count,
                    &mut classes_processed_count,
                    result,
                    acc,
                );
            }
            acc
        })
    };
    let _t: f64 = log_duration_lvl("Finished getting elements", t);
    elements
}

fn invalidate_folded_classes(
    ctx: &Arc<Ctx>,
    bucket_size: isize,
    get_classes_in_file: GetClassesInFile<'_>,
    changed_classes: &[shallow_class_fanout::ChangedClass],
) {
    let mut to_invalidate = s_set::T::new();
    for shallow_class_fanout::ChangedClass {
        descendant_deps, ..
    } in changed_classes
    {
        let names = shallow_class_fanout::class_names_from_deps(
            ctx,
            |fn_| get_classes_in_file(fn_),
            descendant_deps,
        );
        to_invalidate = names.union(to_invalidate);
    }
    hh_logger::log(&format!(
        "Invalidating {} folded classes",
        to_invalidate.len()
    ));
    let get_elems = |n_classes: &s_set::T, old: bool| {
        get_elems(
            bucket_size,
            old,
            &file_info::Names {
                classes: n_classes.iter().cloned().collect(),
                ..file_info::empty_names()
            },
        )
    };
    let (old_members, new_members) = (
        std::sync::LazyLock::new(|| get_elems(&to_invalidate, true)),
        std::sync::LazyLock::new(|| get_elems(&to_invalidate, false)),
    );
    decl_provider::remove_classes(ctx, &to_invalidate, &old_members, &new_members);
    // `Shared_mem.invalidate_local_caches ()`, `Shared_mem.GC.collect
    // `gentle`: see the module documentation.
}

// The main entry point

/// Oldify any defs in `defs` which aren't already in
/// `previously_oldified_defs`, then determines which symbols need to be
/// re-typechecked as a result of comparing the current versions of the
/// symbols to their old versions.
pub fn redo_type_decl(
    ctx: &Arc<Ctx>,
    during_init: bool,
    bucket_size: isize,
    get_classes: GetClassesInFile<'_>,
    previously_oldified_defs: &file_info::Names,
    defs: &RPMap<versioned_names::T>,
) -> RedoTypeDeclResult {
    hh_logger::log("Decl_redecl_service.redo_type_decl: oldifying defs");
    let mut all_defs = versioned_names::empty();
    for names in defs.values() {
        all_defs = versioned_names::merge(names, &all_defs);
    }
    let all_old_defs = &all_defs.old_names;
    // Some of the definitions are already in the old heap, left there by a
    // previous lazy check
    let (oldified_defs, current_defs) =
        decl_utils::split_defs(all_old_defs, previously_oldified_defs);
    // Oldify the remaining defs along with their elements
    let current_elems = get_elems(bucket_size, false, &current_defs);
    oldify_defs(ctx, &current_defs, &current_elems, true);

    // Fetch the already oldified elements too so we can remove them later
    let oldified_elems = get_elems(bucket_size, true, &oldified_defs);
    let all_elems = current_elems.union(oldified_elems);
    let fnl: Vec<RelativePath> = defs.keys().cloned().collect();

    hh_logger::log("Decl_redecl_service.redo_type_decl: computing fanout of non-classes");
    let (fanout_acc, old_decl_missing_count) =
        // If there aren't enough files, let's do this ourselves ... it's faster!
        if fnl.len() < 10 {
            decl_files(ctx, &fnl);
            compare_decls_and_get_fanout(ctx, defs, &fnl)
        } else {
            let (fanout, old_decl_missing_count) =
                parallel_redecl_compare_and_get_fanout(ctx, bucket_size, defs, &fnl);
            let fanout = reconcile_parallel_redecl_fanout(
                during_init,
                &provider_context::get_deps_mode(ctx),
                fanout,
            );
            (fanout, old_decl_missing_count)
        };
    hh_logger::log("Decl_redecl_service.redo_type_decl: computing fanout of classes");
    let fanout = {
        let changes = shallow_decl_compare::compute_changes(
            ctx,
            during_init,
            &versioned_s_set::diff(&versioned_s_set::get_classes(&all_defs)),
        );
        invalidate_folded_classes(ctx, bucket_size, get_classes, &changes);
        let fanout = shallow_class_fanout::fanout_of_changes(ctx, &changes);
        fanout::union(&fanout, &fanout_acc)
    };
    remove_old_defs_with_elems(ctx, all_old_defs, &all_elems);

    hh_logger::log("Finished recomputing type declarations:");
    hh_logger::log(&format!(
        "  changed defs count: {}",
        dep_set::cardinal(&fanout.changed)
    ));
    hh_logger::log(&format!(
        "  defs to recheck count: {}",
        dep_set::cardinal(&fanout.to_recheck)
    ));

    RedoTypeDeclResult {
        fanout,
        old_decl_missing_count,
    }
}

/// Mark all provided `defs` as old, as long as they were not previously
/// oldified. All definitions in `previously_oldified_defs` are then removed
/// from the decl heaps.
///
/// Typically, there are only any `previously_oldified_defs` during
/// two-phase redeclaration.
pub fn oldify_decls_and_remove_descendants(
    ctx: &Arc<Ctx>,
    collect_garbage: Option<bool>,
    get_classes: GetClassesInFile<'_>,
    bucket_size: isize,
    defs: &file_info::Names,
) {
    let collect_garbage = collect_garbage.unwrap_or(true);
    let elems = get_elems(bucket_size, false, defs);
    oldify_defs(ctx, defs, &elems, collect_garbage);

    // Oldifying/removing classes also affects their elements
    // (see Decl_class_elements), which might be shared with other classes. We
    // need to remove all of them too to avoid dangling references
    let all_classes: s_set::T = defs.classes.iter().cloned().collect();
    let descendant_classes = get_descendant_classes(ctx, bucket_size, get_classes, &all_classes);
    let descendant_classes = file_info::Names {
        classes: descendant_classes
            .relative_complement(all_classes)
            .into_iter()
            .collect(),
        ..file_info::empty_names()
    };
    // This path exists to invalidate folded/member state derived from
    // oldified classes. [remove_defs] also removes descendant shallow decls,
    // but that is likely over-broad: a descendant's shallow decl is a direct
    // function of its own file, not of the oldified parent. If we determine
    // there to be performance impact of this consider correcting it.
    remove_defs(&descendant_classes, ctx, collect_garbage)
}

/// Remove provided defs from the heap of old decls.
/// For classes, it removes both shallow and folded classes.
pub fn remove_old_defs(ctx: &Arc<Ctx>, bucket_size: isize, names: &file_info::Names) {
    let elems = get_elems(bucket_size, true, names);
    remove_old_defs_with_elems(ctx, names, &elems)
}

#[cfg(test)]
mod tests {
    //! The tests that need the dependency graph run in a child process
    //! ([`fanout::testing::with_edges`]): the graph and `Typing_deps.trace`
    //! are global to the process.
    //!
    //! The expected fanouts are those the OCaml daemon computes on the same
    //! files and edits (its log prints the hashes: "Fanout of \Foo (hash:
    //! 0x4cd17f7c3d7b6feb) is 3 deps: ...", "changed defs count: 1",
    //! "defs to recheck count: 3"), recorded by
    //! `/tmp/hh-incr/r1/scripts/oracle.py` from the specs of
    //! `test/integration_ml` (`test_remove_method.ml`, ...).

    use std::collections::BTreeMap;
    use std::path::Path;

    use oxidized::typechecker_options::TypecheckerOptions;
    use relative_path::Prefix;
    use ty::decl::shallow::NamedDecl;

    use super::*;
    use crate::fanout::testing::with_edges;
    use crate::typing_deps_mode::T::InMemoryMode;

    /// [`with_edges`], with the progress file of `Server_progress` disabled
    /// (in the child process: the setting is global).
    fn in_child(test: &str, edges: &[(dep::Variant, dep::Variant)], body: impl FnOnce()) {
        with_edges(module_path!(), test, edges, || {
            #[cfg(feature = "server")]
            crate::server_progress::disable();
            body()
        })
    }

    fn rp(name: &str) -> RelativePath {
        RelativePath::make(Prefix::Root, name.into())
    }

    fn hex(deps: &dep_set::T) -> Vec<String> {
        let mut v: Vec<String> = deps.iter().map(|d| dep::to_hex_string(*d)).collect();
        v.sort();
        v
    }

    fn hexes(deps: &[dep::Variant]) -> Vec<String> {
        let mut v: Vec<String> = deps
            .iter()
            .map(|d| dep::to_hex_string(dep::make(d)))
            .collect();
        v.sort();
        v.dedup();
        v
    }

    fn names_of_decls(decls: &[NamedDecl<crate::ctx::R>]) -> file_info::Names {
        let mut names = file_info::empty_names();
        for decl in decls {
            match decl {
                NamedDecl::Class(name, _) => names.classes.insert(name.as_str().to_string()),
                NamedDecl::Fun(name, _) => names.funs.insert(name.as_str().to_string()),
                NamedDecl::Typedef(name, _) => names.types.insert(name.as_str().to_string()),
                NamedDecl::Const(name, _) => names.consts.insert(name.as_str().to_string()),
                NamedDecl::Module(name, _) => names.modules.insert(name.as_str().to_string()),
            };
        }
        names
    }

    /// A repository in memory, as the daemon has it after its full init:
    /// declared, typechecked once with `Typing_deps.trace` on (the edges are
    /// in the graph of the process).
    struct Repo {
        ctx: Arc<Ctx>,
        contents: BTreeMap<String, String>,
    }

    impl Repo {
        fn new(tco: TypecheckerOptions, files: &[(&str, &str)]) -> Self {
            let ctx = Ctx::new(Path::new("/"), tco).unwrap();
            let mut paths = ctx.hhi_paths.clone();
            let mut checked = vec![];
            for (name, contents) in files {
                let path = pos::RelativePath::new(pos::Prefix::Root, *name);
                ctx.files.set(path, *contents);
                paths.push(path);
                checked.push(path);
            }
            crate::check::declare_files(&ctx, &paths, &mut crate::check::Stats::default());
            // The daemon's reverse naming table, after the init (N1).
            ctx.build_dep_hash_index();
            // As `check::check_root` does.
            crate::relative_path::set_path_prefix(
                crate::relative_path::Prefix::Root,
                Path::new("/"),
            );
            crate::relative_path::set_path_prefix(
                crate::relative_path::Prefix::Hhi,
                Path::new("/hhi"),
            );
            crate::relative_path::set_path_prefix(
                crate::relative_path::Prefix::Tmp,
                Path::new("/tmp"),
            );
            let ctx = Arc::new(ctx);
            crate::hh_single_type_check::install(&ctx);
            crate::ast_provider::set_local_parser_cache_enabled(false);
            // Typecheck on one thread, and register the edges of that thread.
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(1)
                .stack_size(256 << 20)
                .build()
                .unwrap();
            pool.install(|| {
                typing_deps::trace.store(true, std::sync::atomic::Ordering::SeqCst);
                let _ = crate::check::check_files_typed_by_file(
                    &ctx,
                    &checked,
                    &mut crate::check::Stats::default(),
                );
                typing_deps::flush_deps(&InMemoryMode(None));
                typing_deps::trace.store(false, std::sync::atomic::Ordering::SeqCst);
            });
            Repo {
                ctx,
                contents: files
                    .iter()
                    .map(|(n, c)| (n.to_string(), c.to_string()))
                    .collect(),
            }
        }

        fn parse(&self, name: &str, contents: &str) -> Vec<NamedDecl<crate::ctx::R>> {
            self.ctx
                .decl_parser
                .parse_with_text(
                    pos::RelativePath::new(pos::Prefix::Root, name),
                    contents.as_bytes(),
                )
                .unwrap()
        }

        /// What `Server_type_check.type_check_core` does to the decls for
        /// the edits (`None`: deleted; the file is then empty): naming
        /// (`Naming_global.remove_decls` of the old names, then
        /// `ndecl_file_skip_if_already_bound`), then `do_redecl`.
        fn edit(&mut self, edits: &[(&str, Option<&str>)]) -> RedoTypeDeclResult {
            let mut defs: RPMap<versioned_names::T> = RPMap::new();
            let mut parsed = vec![];
            for (name, contents) in edits {
                let old = self.contents.get(*name).cloned().unwrap_or_default();
                let new = contents.unwrap_or("").to_string();
                let old_decls = self.parse(name, &old);
                let new_decls = self.parse(name, &new);
                let path = pos::RelativePath::new(pos::Prefix::Root, *name);
                self.ctx.files.set(path, new.clone());
                self.contents.insert(name.to_string(), new);
                defs.insert(
                    rp(name),
                    versioned_names::T {
                        old_names: names_of_decls(&old_decls),
                        new_names: names_of_decls(&new_decls),
                    },
                );
                parsed.push((name.to_string(), path, new_decls));
            }
            for names in defs.values() {
                let v =
                    |s: &std::collections::BTreeSet<String>| s.iter().cloned().collect::<Vec<_>>();
                let n = &names.old_names;
                crate::naming_global::remove_decls(
                    &self.ctx,
                    &v(&n.funs),
                    &v(&n.classes),
                    &v(&n.types),
                    &v(&n.consts),
                    &v(&n.modules),
                );
            }
            for (name, path, decls) in &parsed {
                let info = crate::direct_decl_service::file_info_of_decls(*path, decls, None);
                crate::naming_global::ndecl_file_skip_if_already_bound(
                    &self.ctx,
                    &rp(name),
                    &info.ids,
                );
            }
            let classes: BTreeMap<RelativePath, s_set::T> = defs
                .iter()
                .map(|(path, names)| {
                    let mut c: s_set::T = names.old_names.classes.iter().cloned().collect();
                    c.extend(names.new_names.classes.iter().cloned());
                    (path.clone(), c)
                })
                .collect();
            let get_classes = |path: &RelativePath| classes.get(path).cloned().unwrap_or_default();
            redo_type_decl(
                &self.ctx,
                false,
                1,
                &get_classes,
                &file_info::empty_names(),
                &defs,
            )
        }
    }

    fn assert_fanout(
        result: &RedoTypeDeclResult,
        changed: &[dep::Variant],
        to_recheck: &[dep::Variant],
    ) {
        assert_eq!(hex(&result.fanout.changed), hexes(changed), "changed");
        assert_eq!(
            hex(&result.fanout.to_recheck),
            hexes(to_recheck),
            "to_recheck"
        );
    }

    const H: &str = "<?hh // strict\n\n";

    fn src(body: &str) -> String {
        format!("{H}{body}")
    }

    /// `decl_redecl_service_test.ml`, `test_reconciles_master_dependencies`
    /// and `test_does_not_reconcile_during_init`.
    #[test]
    fn reconcile_parallel_redecl_fanout_with_master_dependencies() {
        use dep::Variant::*;
        in_child(
            "reconcile_parallel_redecl_fanout_with_master_dependencies",
            &[(Fun("module_consumer".into()), Module("test.module".into()))],
            || {
                let deps_mode = InMemoryMode(None);
                let module_dep = dep::make(&Module("test.module".into()));
                let consumer_dep = dep::make(&Fun("module_consumer".into()));
                let sentinel_dep = dep::make(&Fun("existing_fanout".into()));
                let errors_sentinel_dep = dep::make(&Fun("existing_error_fanout".into()));
                let make_stale_worker_fanout = || fanout::T {
                    changed: dep_set::singleton(module_dep),
                    to_recheck: dep_set::singleton(sentinel_dep),
                    to_recheck_if_errors: dep_set::singleton(errors_sentinel_dep),
                };
                let result = for_test::reconcile_parallel_redecl_fanout(
                    false,
                    &deps_mode,
                    make_stale_worker_fanout(),
                );
                assert!(
                    dep_set::mem(&result.to_recheck, consumer_dep),
                    "master-only dependent should be added"
                );
                assert!(
                    !dep_set::mem(&result.to_recheck, module_dep),
                    "changed dependency should not be added to to_recheck"
                );
                assert!(
                    dep_set::mem(&result.to_recheck, sentinel_dep),
                    "existing worker fanout should be preserved"
                );
                assert_eq!(dep_set::cardinal(&result.to_recheck), 2);
                assert!(dep_set::mem(&result.changed, module_dep));
                assert_eq!(dep_set::cardinal(&result.changed), 1);
                assert!(dep_set::mem(
                    &result.to_recheck_if_errors,
                    errors_sentinel_dep
                ));
                assert_eq!(dep_set::cardinal(&result.to_recheck_if_errors), 1);

                let result = for_test::reconcile_parallel_redecl_fanout(
                    true,
                    &deps_mode,
                    make_stale_worker_fanout(),
                );
                assert!(
                    !dep_set::mem(&result.to_recheck, consumer_dep),
                    "guarded reconciliation should not add the master-only dependent"
                );
                assert!(dep_set::mem(&result.to_recheck, sentinel_dep));
                assert_eq!(dep_set::cardinal(&result.to_recheck), 1);
            },
        );
    }

    /// The elements are always empty, whatever the number of classes (the
    /// path with buckets is taken from 10 classes).
    #[test]
    fn elements_are_empty() {
        in_child("elements_are_empty", &[], elements_are_empty_body)
    }

    fn elements_are_empty_body() {
        let mut names = file_info::empty_names();
        assert!(get_elems(1, false, &names).is_empty());
        for i in 0..12 {
            names.classes.insert(format!("\\C{i}"));
        }
        assert!(get_elems(1, true, &names).is_empty());
        assert!(get_elems(5, false, &names).is_empty());
    }

    /// The edges that the redecl tests rely on, as the typecheck of
    /// [`Repo::new`] records them: those of the OCaml (its
    /// `--save-human-readable-64bit-dep-map` on the files of
    /// [`remove_method`]: `Fun test -> Type FooChild`, `Fun test ->
    /// Method(FooChild, f)`, `Type FooChild -> Extends Foo`, ...).
    #[test]
    fn edges_of_the_typecheck() {
        in_child("edges_of_the_typecheck", &[], || {
            use dep::Variant::*;
            let _repo = Repo::new(
                TypecheckerOptions::default(),
                &[
                    (
                        "foo.php",
                        &src("class Foo {\n  public function f() : void {}\n}\n"),
                    ),
                    ("foo_child.php", &src("class FooChild extends Foo {}\n")),
                    (
                        "bar.php",
                        &src(
                            "function test(FooChild $foo_child) : void {\n  $foo_child->f();\n}\n",
                        ),
                    ),
                ],
            );
            let mode = InMemoryMode(None);
            let ideps = |d: dep::Variant| hex(&typing_deps::get_ideps(&mode, &d));
            assert!(ideps(Type("\\FooChild".into())).contains(&hexes(&[Fun("\\test".into())])[0]));
            assert!(
                ideps(Method("\\FooChild".into(), "f".into()))
                    .contains(&hexes(&[Fun("\\test".into())])[0])
            );
            assert_eq!(
                hex(&typing_deps::add_extend_deps(
                    &mode,
                    &dep_set::singleton(dep::make(&Type("\\Foo".into())))
                )),
                hexes(&[Type("\\Foo".into()), Type("\\FooChild".into())])
            );
        });
    }

    /// `test_remove_method.ml`. The OCaml: `"\\Foo": "(Minor_change {
    /// methods = { \"f\" -> Removed } })"`, "Invalidating 2 folded classes",
    /// "Fanout of \Foo (hash: 0x4cd17f7c3d7b6feb) is 3 deps:
    /// 0x25894526565b5d5b, 0x2ea4df4486132a28, 0x4cd17f7c3d7b6feb" (`Type
    /// FooChild`, `Fun test`, `Type Foo`), "changed defs count: 1", "defs to
    /// recheck count: 3"; rechecks bar.php, foo.php, foo_child.php.
    #[test]
    fn remove_method() {
        in_child("remove_method", &[], || {
            use dep::Variant::*;
            let mut repo = Repo::new(
                TypecheckerOptions::default(),
                &[
                    (
                        "foo.php",
                        &src("class Foo {\n  public function f() : void {}\n}\n"),
                    ),
                    ("foo_child.php", &src("class FooChild extends Foo {}\n")),
                    (
                        "bar.php",
                        &src(
                            "function test(FooChild $foo_child) : void {\n  $foo_child->f();\n}\n",
                        ),
                    ),
                ],
            );
            let result = repo.edit(&[("foo.php", Some(&src("class Foo {}\n")))]);
            assert_eq!(
                dep::to_hex_string(dep::make(&Type("\\Foo".into()))),
                "0x4cd17f7c3d7b6feb"
            );
            assert_fanout(
                &result,
                &[Type("\\Foo".into())],
                &[
                    Type("\\Foo".into()),
                    Type("\\FooChild".into()),
                    Fun("\\test".into()),
                ],
            );
            assert_eq!(result.old_decl_missing_count, 0);
        });
    }

    /// `test_added_parent.ml`: foo.php was empty, then defines `Foo`. The
    /// OCaml: `"\\Foo": "(Major_change Added)"`, "Invalidating 2 folded
    /// classes", the same 3 deps as [`remove_method`].
    #[test]
    fn added_parent() {
        in_child("added_parent", &[], || {
            use dep::Variant::*;
            let mut repo = Repo::new(
                TypecheckerOptions::default(),
                &[
                    ("foo.php", ""),
                    (
                        "foo_child.php",
                        &src(
                            "/* HH_FIXME[2049] */\n/* HH_FIXME[4123] */\nclass FooChild extends Foo {}\n",
                        ),
                    ),
                    (
                        "bar.php",
                        &src(
                            "function take_int(int $x) : void {}\n\nfunction test(FooChild $foo_child) : void {\n  /* HH_FIXME[4053] */\n  take_int($foo_child->f());\n}\n",
                        ),
                    ),
                ],
            );
            let result = repo.edit(&[(
                "foo.php",
                Some(&src(
                    "class Foo {\n  /* HH_FIXME[4336] */\n  public function f() : string {\n  }\n}\n",
                )),
            )]);
            assert_fanout(
                &result,
                &[Type("\\Foo".into())],
                &[
                    Type("\\Foo".into()),
                    Type("\\FooChild".into()),
                    Fun("\\test".into()),
                ],
            );
        });
    }

    /// `test_remove_enum_variant.ml`. The OCaml: `"\\E": "(Minor_change {
    /// consts = { \"B\" -> Removed } })"`, "Invalidating 1 folded classes",
    /// "Fanout of \E (hash: 0x54148630eabf74b5) is 2 deps:
    /// 0x54148630eabf74b5, 0x23152a30cfd6b784" (`Type E`, `Fun f`).
    #[test]
    fn remove_enum_variant() {
        in_child("remove_enum_variant", &[], || {
            use dep::Variant::*;
            let mut repo = Repo::new(
                TypecheckerOptions::default(),
                &[
                    ("e.php", "<?hh\n\nenum E: int {\n  A = 1;\n  B = 2;\n}\n"),
                    (
                        "f.php",
                        "<?hh\n\nfunction f(E $e): int {\n  switch ($e) {\n    case E::A:\n      return 4;\n  }\n  return 42;\n}\n",
                    ),
                ],
            );
            let result = repo.edit(&[("e.php", Some("<?hh\n\nenum E: int {\n  A = 1;\n}\n"))]);
            assert_fanout(
                &result,
                &[Type("\\E".into())],
                &[Type("\\E".into()), Fun("\\f".into())],
            );
        });
    }

    /// `test_decl_decl.ml`: C.php was empty, then defines `C`, which the
    /// return type of `A::f` names. The OCaml: `"\\C": "(Major_change
    /// Added)"`, "Invalidating 1 folded classes", "Fanout of \C (hash:
    /// 0x54147a30eabf6051) is 2 deps: 0x54147a30eabf6051, 0x54147e30eabf671d"
    /// (`Type C`, `Type A`); rechecks A.php, C.php.
    #[test]
    fn decl_decl() {
        in_child("decl_decl", &[], || {
            use dep::Variant::*;
            let mut repo = Repo::new(
                TypecheckerOptions::default(),
                &[
                    (
                        "A.php",
                        &src(
                            "class A {\n  /* HH_FIXME[4336] */\n  /* HH_FIXME[4422] */\n  final public function f() : C {\n  }\n}\n",
                        ),
                    ),
                    ("B.php", &src("class B extends A {}\n")),
                    ("C.php", ""),
                ],
            );
            let result = repo.edit(&[("C.php", Some(&src("class C {}\n")))]);
            assert_fanout(
                &result,
                &[Type("\\C".into())],
                &[Type("\\C".into()), Type("\\A".into())],
            );
        });
    }

    /// Functions, typedefs, constants, modules (the comparisons of
    /// `compare_decls_and_get_fanout`). The OCaml: a changed return type of
    /// `f`, a changed typedef `T` and a whitespace-only change of `g`:
    /// "changed defs count: 2", "defs to recheck count: 1" (u.php); then a
    /// changed constant, a removed function and a removed module: "changed
    /// defs count: 3", "defs to recheck count: 1".
    #[test]
    fn non_classes() {
        in_child("non_classes", &[], || {
            use dep::Variant::*;
            let mut repo = Repo::new(
                TypecheckerOptions::default(),
                &[
                    ("f.php", &src("function f(): int { return 1; }\n")),
                    ("t.php", &src("type T = int;\n")),
                    ("c.php", &src("const int K = 1;\n")),
                    ("m.php", "<?hh\nnew module mm {}\n"),
                    (
                        "u.php",
                        &src("function u(T $t): int { return f() + K + $t; }\n"),
                    ),
                    ("g.php", &src("function g(): void {}\n")),
                ],
            );
            let result = repo.edit(&[
                (
                    "f.php",
                    Some(&src("function f(): string { return 'a'; }\n")),
                ),
                ("t.php", Some(&src("type T = string;\n"))),
                ("g.php", Some(&src("\n\nfunction g(): void {}\n"))),
            ]);
            assert_fanout(
                &result,
                &[Fun("\\f".into()), Type("\\T".into())],
                &[Fun("\\u".into())],
            );
            assert_eq!(result.old_decl_missing_count, 0);
            let result = repo.edit(&[
                ("c.php", Some(&src("const string K = 'a';\n"))),
                ("m.php", None),
                ("f.php", None),
            ]);
            assert_fanout(
                &result,
                &[GConst("\\K".into()), Fun("\\f".into()), Module("mm".into())],
                &[Fun("\\u".into())],
            );
        });
    }

    /// 13 changed files: the parallel path. The OCaml: 13 changed classes
    /// (a method of each changed its return type), "Invalidating 13 folded
    /// classes", "changed defs count: 25" (the classes and the 12
    /// functions `fn_i`), "defs to recheck count: 25" (the classes and the
    /// functions `use_i`).
    #[test]
    fn parallel() {
        in_child("parallel", &[], || {
            use dep::Variant::*;
            let mut files = vec![(
                "base.php".to_string(),
                src("class Base {\n  public function m(): int { return 1; }\n}\n"),
            )];
            let mut edit = vec![(
                "base.php".to_string(),
                src("class Base {\n  public function m(): string { return 'a'; }\n}\n"),
            )];
            let mut changed = vec![Type("\\Base".into())];
            let mut to_recheck = vec![Type("\\Base".into())];
            for i in 0..12 {
                files.push((
                    format!("c{i:02}.php"),
                    src(&format!(
                        "class C{i} extends Base {{\n  public function n{i}(): int {{ return 1; }}\n}}\nfunction fn{i}(): int {{ return 1; }}\n"
                    )),
                ));
                files.push((
                    format!("u{i:02}.php"),
                    src(&format!(
                        "function use{i}(C{i} $c): int {{ return $c->m() + $c->n{i}() + fn{i}(); }}\n"
                    )),
                ));
                edit.push((
                    format!("c{i:02}.php"),
                    src(&format!(
                        "class C{i} extends Base {{\n  public function n{i}(): string {{ return 'a'; }}\n}}\nfunction fn{i}(): string {{ return 'a'; }}\n"
                    )),
                ));
                changed.push(Type(format!("\\C{i}")));
                changed.push(Fun(format!("\\fn{i}")));
                to_recheck.push(Type(format!("\\C{i}")));
                to_recheck.push(Fun(format!("\\use{i}")));
            }
            let files: Vec<(&str, &str)> = files
                .iter()
                .map(|(n, c)| (n.as_str(), c.as_str()))
                .collect();
            let mut repo = Repo::new(TypecheckerOptions::default(), &files);
            let edit: Vec<(&str, Option<&str>)> = edit
                .iter()
                .map(|(n, c)| (n.as_str(), Some(c.as_str())))
                .collect();
            let result = repo.edit(&edit);
            assert_eq!(dep_set::cardinal(&result.fanout.changed), 25);
            assert_eq!(dep_set::cardinal(&result.fanout.to_recheck), 25);
            assert_fanout(&result, &changed, &to_recheck);
        });
    }

    /// `test_get_dependent_classes.ml`
    #[test]
    fn get_dependent_classes() {
        in_child("get_dependent_classes", &[], || {
            let files: Vec<(String, String)> = [
                ("C", "class C {}"),
                ("D", "class D extends C {}"),
                ("E", "class E extends D {}"),
                ("F", "trait F { require extends E; }"),
                ("G", "trait G { use F; }"),
                ("H", "trait H {}"),
                ("I", "class I { use H; }"),
                ("J", "interface J {}"),
                ("K", "interface K extends J {}"),
                ("L", "trait L { require implements K; }"),
                ("M", "class :M {}"),
                ("N", "class :N { attribute :M; }"),
                ("Unrelated", "class Unrelated {}"),
            ]
            .iter()
            .map(|(name, contents)| (format!("{name}.php"), format!("<?hh\n{contents}")))
            .collect();
            let files: Vec<(&str, &str)> = files
                .iter()
                .map(|(n, c)| (n.as_str(), c.as_str()))
                .collect();
            let repo = Repo::new(TypecheckerOptions::default(), &files);
            let classes: BTreeMap<RelativePath, s_set::T> = files
                .iter()
                .map(|(name, contents)| {
                    (
                        rp(name),
                        names_of_decls(&repo.parse(name, contents))
                            .classes
                            .into_iter()
                            .collect(),
                    )
                })
                .collect();
            let get_classes = |path: &RelativePath| classes.get(path).cloned().unwrap_or_default();
            let dependent_classes = get_descendant_classes(
                &repo.ctx,
                1,
                &get_classes,
                &["\\C", "\\H", "\\J", "\\:M"]
                    .iter()
                    .map(|s| s.to_string())
                    .collect(),
            );
            let mut expected = vec![
                "\\C", "\\D", "\\E", "\\F", "\\G", "\\H", "\\I", "\\J", "\\K", "\\L", "\\:M",
                "\\:N",
            ];
            expected.sort();
            assert_eq!(dependent_classes.into_iter().collect::<Vec<_>>(), expected);
        });
    }

    /// `test_lazy_decl_idempotence.ml`: the classes removed from the decl
    /// stores (`remove_defs`) are declared again when typing needs them, with
    /// the same errors.
    #[test]
    fn lazy_decl_idempotence() {
        in_child("lazy_decl_idempotence", &[], lazy_decl_idempotence_body)
    }

    fn lazy_decl_idempotence_body() {
        let foo = "<?hh //strict\n\nconst string GLOBAL_X = \"X\";\n\nclass Foo {\n  // this is an error (lack of typehint) revealed during declaration only\n  const X = GLOBAL_X;\n}\n";
        let bar = "<?hh //strict\nclass Bar {\n  public function test(Foo $x) : void {}\n}\n";
        let repo = Repo::new(
            TypecheckerOptions::default(),
            &[("foo.php", foo), ("bar.php", bar)],
        );
        let mut defs = file_info::empty_names();
        defs.classes.insert("\\Foo".to_string());
        defs.classes.insert("\\Bar".to_string());
        remove_defs(&defs, &repo.ctx, false);
        let check = |name: &str| {
            let path = pos::RelativePath::new(pos::Prefix::Root, name);
            let diags = crate::check::check_files_typed_by_file(
                &repo.ctx,
                &[path],
                &mut crate::check::Stats::default(),
            );
            diags
                .iter()
                .map(|d| {
                    format!(
                        "{:?}",
                        crate::diagnostics_state::get_diagnostic_list(None, d.clone())
                            .iter()
                            .map(|d| d.code)
                            .collect::<Vec<_>>()
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(check("bar.php"), vec!["[]".to_string()]);
        assert_eq!(check("bar.php"), vec!["[]".to_string()]);
        assert_eq!(check("foo.php"), vec!["[2035]".to_string()]);
        assert_eq!(check("foo.php"), vec!["[2035]".to_string()]);
    }
}
