// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_isolation_decls.ml`. See `hh/PORTING.md`.
//!
//! [`with_repackaged_decls`] runs `f` with the decls of `files` rebuilt
//! under the package configuration `ctx` carries, then puts the heaps back
//! as they were.
//!
//! A symbol's package is a field on its decl, written when the file was
//! parsed, so adding a package to a context changes nothing until those
//! decls go; removing them makes the next lookup recompute from the context
//! that asked.
//!
//! # Only for a server dedicated to this analysis
//!
//! The decl heaps belong to the whole process. While `f` runs, the
//! candidate's symbols are either absent or carry a package no repository
//! declares, so anything else in the server that reads them in that window
//! sees something the repository does not say. Do not run this on a server
//! that is also answering a developer's typechecks; give the analysis its
//! own server, and restart it afterwards rather than carrying the run's
//! residue into whatever that server does next.
//!
//! # What restoring does and does not cover
//!
//! Restoration covers the ordinary path and an exception out of `f`: a
//! local-changes stack per heap the backend uses, popped afterwards, and a
//! second deletion for any heap that stack does not cover. It does not
//! cover the process dying mid-run, which leaves the stacks pushed and the
//! decls missing — the reason to restart rather than trust the server.
//!
//! Raises unless `allow_repackaging` is set, which the caller takes from
//! `isolation_allow_decl_repackaging` in the server config. The warning
//! above is a convention until an operator opts in; this makes it one the
//! server enforces.
//!
//! Raises on a backend whose heaps it does not know, before removing
//! anything, rather than deleting decls it has no way to put back.
//!
//! The process-local caches above the heaps are invalidated before `f` runs
//! as well as after: they hold folded classes carrying the package they
//! were folded under, which no local-changes stack reaches.
//!
//! `Typing_deps.trace` is off throughout: edges found while typechecking
//! are appended to the dependency graph, which no local-changes stack
//! covers and no restart short of a fresh init will undo.

use std::cell::RefCell;
use std::panic::AssertUnwindSafe;
use std::sync::Arc;
use std::sync::atomic::Ordering;

use crate::decl_redecl_service;
use crate::exception;
use crate::file_info;
use crate::hh_logger;
use crate::naming_table;
use crate::provider_backend;
use crate::provider_context;
use crate::relative_path;
use crate::typing_deps;
use crate::utils;

/// `union_names`
fn union_names(a: file_info::Names, b: file_info::Names) -> file_info::Names {
    let file_info::Names {
        mut funs,
        mut classes,
        mut types,
        mut consts,
        mut modules,
    } = a;
    funs.extend(b.funs);
    classes.extend(b.classes);
    types.extend(b.types);
    consts.extend(b.consts);
    modules.extend(b.modules);
    file_info::Names {
        funs,
        classes,
        types,
        consts,
        modules,
    }
}

/// `names_defined_in`
fn names_defined_in(
    naming_table: &naming_table::T,
    files: &[relative_path::T],
) -> file_info::Names {
    files.iter().fold(
        file_info::empty_names(),
        |acc, file| match naming_table::get_file_info(naming_table, file) {
            None => acc,
            Some(file_info) => union_names(acc, file_info::simplify(&file_info)),
        },
    )
}

/// `remove_decls`. (`Decl_class_elements.get_for_classes ~old:false`, the
/// `~elems` of `Decl_redecl_service.remove_defs`, is not computed: the
/// member heaps have no counterpart, so `remove_defs` takes none.)
///
/// The decls are removed from the context's stores, which are those of the
/// server (`Provider_context.empty_for_tool ~backend:(get_backend ctx)` in
/// the caller: the same heaps).
fn remove_decls(ctx: &provider_context::T, names: &file_info::Names) {
    decl_redecl_service::remove_defs(names, ctx, false)
}

/// The decls of `files` parsed under the package configuration of `ctx`,
/// and cached as a lookup that parses them caches them
/// (`Direct_decl_utils.direct_decl_parse_and_cache`).
///
/// The OCaml leaves this to the next lookup, which parses with the
/// options of the context that asked. Here a store that misses parses with
/// the decl parser it was given when the server built its reverse naming
/// table (`Ctx::build_reverse_naming_table`), so a lookup through the
/// candidate's context would rebuild the decls under the server's own
/// package configuration, and the candidate would look isolatable whatever
/// referred into it. Parsing them here with the candidate's parser puts
/// what the OCaml's lookup would have computed in the stores, inside the
/// local changes pushed by [`push_decl_stacks`], which drop it again.
fn declare_under_candidate(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    files: &[relative_path::T],
) {
    for file in files {
        // Only the files whose decls `remove_decls` removed.
        if naming_table::get_file_info(naming_table, file).is_none() {
            continue;
        }
        let Some(text) = crate::file_provider::rust_provider_backend::file::get_contents(ctx, file)
        else {
            continue;
        };
        let path = pos::RelativePath::from(file);
        match ctx.decl_parser.parse_with_text(path, &text) {
            Ok(decls) => ctx.add_shallow_decls(path, decls),
            // (A file that does not parse is cached with no decls, as a
            // lookup that parses it would find none.)
            Err(_) => {}
        }
    }
}

type Pop = Box<dyn FnOnce()>;

/// `push p pop`: `p ()`, then records `pop`, so a push that raises is not
/// recorded.
fn push(pops: &RefCell<Vec<Pop>>, p: impl FnOnce(), pop: Pop) {
    p();
    pops.borrow_mut().push(pop);
}

/// `pop_all`: every pop runs even if one raises, and the caches are
/// invalidated either way: a heap left with a stack pushed, or a stale
/// local cache, outlives the query and belongs to no one. The first failure
/// is reraised once the rest have been unwound.
fn pop_all(pops: Vec<Pop>) {
    let mut failure: Option<exception::T> = None;
    // In reverse order of pushing (the OCaml's `::` list).
    for pop in pops.into_iter().rev() {
        if let Err(exn) = std::panic::catch_unwind(AssertUnwindSafe(pop)) {
            let exn = exception::wrap(exn);
            if failure.is_none() {
                failure = Some(exn);
            }
        }
    }
    crate::rt::decl_epoch::invalidate_local_caches();
    if let Some(exn) = failure {
        exception::reraise(exn)
    }
}

/// `push_decl_stacks backend`: push a local-changes stack on each heap the
/// backend uses, returning the pop that undoes exactly what was pushed.
///
/// Each pop is recorded as its push succeeds, so a push that raises partway
/// does not leave the server with stacks nobody unwinds.
///
/// Takes the context rather than its backend: the stacks of the decl
/// stores are those of the context's stores
/// (`Ctx::local_changes_push_decl_stores`), the daemon having no installed
/// decl store whose `push_local_changes` would reach them.
fn push_decl_stacks(ctx: &provider_context::T) -> impl FnOnce() + use<> {
    let pops: RefCell<Vec<Pop>> = RefCell::new(vec![]);
    // Which heaps a backend keeps in OCaml shared memory, mirroring
    // [Provider_utils.respect_but_quarantine_unsaved_changes]. Keep the two in
    // step: a heap left out here holds on to a decl built under the synthesized
    // package, and nothing reports it. That function cannot be called instead —
    // it ends by making the heaps read-only, and the rebuilt decls have to land.
    //
    // (`Rust_provider_backend.push_local_changes` is the pushes of
    // `Shared_memory`: the port's `Rust_provider_backend` has its stores.)
    let pushed = std::panic::catch_unwind(AssertUnwindSafe(|| match ctx.get_backend() {
        provider_backend::T::RustProviderBackend | provider_backend::T::SharedMemory => {
            push(
                &pops,
                crate::ast_provider::local_changes_push_sharedmem_stack,
                Box::new(crate::ast_provider::local_changes_pop_sharedmem_stack),
            );
            let decl_ctx = Arc::clone(ctx);
            push(
                &pops,
                || ctx.local_changes_push_decl_stores(),
                Box::new(move || decl_ctx.local_changes_pop_decl_stores()),
            );
            push(
                &pops,
                crate::file_provider::local_changes_push_sharedmem_stack,
                Box::new(crate::file_provider::local_changes_pop_sharedmem_stack),
            );
            push(
                &pops,
                crate::fixme_provider::local_changes_push_sharedmem_stack,
                Box::new(crate::fixme_provider::local_changes_pop_sharedmem_stack),
            );
            push(
                &pops,
                crate::naming_provider::local_changes_push_sharedmem_stack,
                Box::new(crate::naming_provider::local_changes_pop_sharedmem_stack),
            );
        }
        backend => {
            // No stacks pushed means nothing to restore, and the caller removes
            // decls regardless. Refuse rather than leave that to be discovered.
            panic!(
                "isolation: no local-changes stacks known for backend {}",
                provider_backend::t_to_string(&backend)
            )
        }
    }));
    let pops = pops.into_inner();
    if let Err(exn) = pushed {
        let exn = exception::wrap(exn);
        // A pop that fails in turn must not replace the push failure, which is the
        // one that says what went wrong.
        if let Err(pop_exn) = std::panic::catch_unwind(AssertUnwindSafe(|| pop_all(pops))) {
            hh_logger::log(&format!(
                "isolation: unwinding a failed decl-stack push also failed: {}",
                exception::to_string(&exception::wrap(pop_exn))
            ));
        }
        exception::reraise(exn)
    }
    move || pop_all(pops)
}

/// `with_repackaged_decls ctx naming_table files ~allow_repackaging ~f`
/// (see the module doc).
pub fn with_repackaged_decls<A>(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    files: &[relative_path::T],
    allow_repackaging: bool,
    f: impl FnOnce() -> A,
) -> A {
    if !allow_repackaging {
        panic!(
            "isolation: decl repackaging is off; set isolation_allow_decl_repackaging=true in hh.conf, on a server dedicated to this analysis"
        );
    }
    let names = names_defined_in(naming_table, files);
    let traced = typing_deps::TRACE.load(Ordering::SeqCst);
    let pop_decl_stacks = push_decl_stacks(ctx);
    typing_deps::TRACE.store(false, Ordering::SeqCst);
    utils::try_finally(
        || {
            remove_decls(ctx, &names);
            declare_under_candidate(ctx, naming_table, files);
            // Removing a decl from the shared heaps does not touch the process-local
            // caches above them: [Decl_provider.Cache] holds folded classes, and a
            // class folded before this point still carries the package it was folded
            // under. Left in place, the typecheck reads the old package from cache
            // and the candidate looks fine when it is not.
            crate::rt::decl_epoch::invalidate_local_caches();
            f()
        },
        || {
            // Nested, so the trace flag and the stacks are restored even if the
            // second deletion raises. Those two are process-wide and outlive the
            // query; a decl left behind only costs the next lookup a recompute.
            utils::try_finally(
                || remove_decls(ctx, &names),
                || {
                    typing_deps::TRACE.store(traced, Ordering::SeqCst);
                    pop_decl_stacks()
                },
            )
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(funs: &[&str], classes: &[&str]) -> file_info::Names {
        file_info::Names {
            funs: funs.iter().map(|s| s.to_string()).collect(),
            classes: classes.iter().map(|s| s.to_string()).collect(),
            ..file_info::empty_names()
        }
    }

    #[test]
    fn union_of_names() {
        let u = union_names(
            names(&["\\f", "\\g"], &["\\C"]),
            names(&["\\g", "\\h"], &[]),
        );
        let expected = names(&["\\f", "\\g", "\\h"], &["\\C"]);
        assert_eq!(u.funs, expected.funs);
        assert_eq!(u.classes, expected.classes);
        assert!(u.types.is_empty() && u.consts.is_empty() && u.modules.is_empty());
    }

    #[test]
    fn pop_all_runs_every_pop_and_reraises_the_first_failure() {
        let ran = std::rc::Rc::new(RefCell::new(vec![]));
        let pop = |i: usize, fail: bool| -> Pop {
            let ran = std::rc::Rc::clone(&ran);
            Box::new(move || {
                ran.borrow_mut().push(i);
                if fail {
                    std::panic::panic_any(format!("pop {}", i))
                }
            })
        };
        let pops = vec![pop(0, false), pop(1, true), pop(2, true)];
        let res = std::panic::catch_unwind(AssertUnwindSafe(|| pop_all(pops)));
        // Popped in reverse order of pushing, all of them.
        assert_eq!(*ran.borrow(), vec![2, 1, 0]);
        // The first failure is the one reraised.
        let payload = res.unwrap_err();
        assert_eq!(
            payload.downcast_ref::<String>().map(String::as_str),
            Some("pop 2")
        );
    }

    #[test]
    fn refuses_without_repackaging() {
        let ctx = Arc::new(
            crate::ctx::Ctx::new(
                std::path::Path::new("/nonexistent"),
                oxidized::typechecker_options::TypecheckerOptions::default(),
            )
            .unwrap(),
        );
        let ran = std::cell::Cell::new(false);
        let res = std::panic::catch_unwind(AssertUnwindSafe(|| {
            with_repackaged_decls(&ctx, &naming_table::empty(), &[], false, || ran.set(true))
        }));
        let payload = res.unwrap_err();
        assert_eq!(
            payload.downcast_ref::<&str>().copied(),
            Some(
                "isolation: decl repackaging is off; set isolation_allow_decl_repackaging=true in hh.conf, on a server dedicated to this analysis"
            )
        );
        assert!(!ran.get());
    }
}
