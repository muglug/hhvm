// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_check_job.ml`. See `hh/PORTING.md`.
//!
//! The type checking service receives a list of files and their symbols as input and
//! distributes the work to worker processes.
//!
//! In this file you will only find functions to process a single file at a time
//!
//! # Notes on the port
//!
//! - The definitions are taken by value (`~full_ast`): naming consumes them.
//! - `handle_exn_as_error` catches the panics of `f` (the exceptions of the
//!   OCaml) with `catch_unwind`, and raises the three it re-raises again with
//!   the same payload.
//! - `Nast_check.def ctx def` has no Rust function of that name:
//!   `crate::nast_check` runs its checks with `check_program`, which collects
//!   the diagnostics instead of adding them; [`nast_check_def`] runs it on the
//!   one definition and adds what it collects. `check_program` also runs
//!   `Nast_init_check` on a class, which the OCaml runs from `Typing_class`
//!   (see `typing_class.rs`).
//! - In the OCaml the NAST checks report with `Diagnostics.add_diagnostic`,
//!   which is what applies the `HH_FIXME`s (keeping the fixmed errors when
//!   `~drop_fixmed:false`, and recording the fixmes it applies). So the
//!   checks are run with `program_with_comments` and no comments, which
//!   drops nothing itself, and `diagnostics::add_diagnostic` applies
//!   the fixmes, as for every other error.

use std::panic::AssertUnwindSafe;
use std::sync::Arc;

use oxidized::aast;
use oxidized::file_info;
use oxidized::pos::Pos;
use oxidized::scoured_comments::ScouredComments;
use relative_path::RelativePath;

use crate::ctx::Ctx;
use crate::diagnostics;
use crate::exception;
use crate::file_provider::FileProviderStale;
use crate::naming;
use crate::nast;
use crate::s_map;
use crate::tast;
use crate::tast_check;
use crate::tast_with_dynamic;
use crate::typing_deps::DepgraphUnavailable;
use crate::typing_toplevel;
use crate::worker_cancel::WorkerShouldExit;

/// `Nast_check.def ctx def`: the checks of `crate::nast_check` on a program
/// of this one definition, whose diagnostics are added in the order they were
/// found. No comments are given, so that the checks drop nothing:
/// `add_diagnostic` applies the `HH_FIXME`s, as `Diagnostics.add_diagnostic`
/// does in the OCaml.
fn nast_check_def(ctx: &Arc<Ctx>, def: nast::Def) -> nast::Def {
    let program = nast::Program(vec![def]);
    let mut diagnostics = vec![];
    crate::nast_check::program_with_comments(
        ctx,
        &program,
        &ScouredComments::default(),
        &mut diagnostics,
    );
    for diagnostic in diagnostics {
        diagnostics::add_diagnostic(diagnostic)
    }
    let nast::Program(mut defs) = program;
    defs.pop().expect("the definition that was checked")
}

// ---------------------------------------------------------------------------
// The job that will be run on the workers
// ---------------------------------------------------------------------------

fn handle_exn_as_error<Res>(pos: &Pos, f: impl FnOnce() -> Option<Res>) -> Option<Res> {
    match std::panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(res) => res,
        Err(exn) => {
            if exn.is::<WorkerShouldExit>() {
                // Cancellation request must be re-raised
                let e = exception::wrap(exn);
                exception::reraise(e)
            } else if exn.is::<FileProviderStale>() {
                // File-provider-stale must be re-raised so the recheck loop
                // can restart a full init cycle.
                let e = exception::wrap(exn);
                exception::reraise(e)
            } else if exn.is::<DepgraphUnavailable>() {
                let e = exception::wrap(exn);
                exception::reraise(e)
            } else {
                let e = exception::wrap(exn);
                diagnostics::exception_occurred(pos.clone(), &e);
                None
            }
        }
    }
}

/// After running TAST checks on the normal TAST, run warning checks on
/// the dynamic TAST (if it exists) and use the intersection to determine
/// which type-dependent warnings are trusted.
///
/// `normal_keys` are the keys of the warnings that the warning checks added
/// when `Tast_check.def` ran on the normal TAST (see
/// `tast_check::def_recording_warning_keys`), when there is no dynamic TAST:
/// they are what running the checks again on that TAST would collect.
fn intersect_dynamic_warnings(
    ctx: &Arc<Ctx>,
    twd: &tast_with_dynamic::T<tast::Def>,
    normal_keys: Option<Vec<(isize, Pos)>>,
) {
    // Not in the OCaml: with no untrusted warning in the accumulator, marking
    // warnings trusted changes nothing, so the keys are not computed (the
    // warning checks on the dynamic TAST run in an isolated context, which
    // adds nothing).
    if !diagnostics::has_untrusted_warnings() {
        return;
    }
    // Determine which def to run warning checks on for trust verification.
    // If there's a dynamic TAST, use it. If not (all params enforceable),
    // re-run on the normal TAST so the keys are scoped to this definition
    // only — using mark_all_warnings_trusted would incorrectly promote
    // untrusted warnings from earlier definitions in the same file.
    let check_def = match &twd.under_dynamic_assumptions {
        Some(dyn_def) => dyn_def,
        None => &twd.under_normal_assumptions,
    };
    let keys = match (&twd.under_dynamic_assumptions, normal_keys) {
        (None, Some(keys)) => keys,
        _ => diagnostics::collect_warning_keys(|| tast_check::warning_def(ctx, check_def)),
    };
    diagnostics::mark_warnings_trusted(&keys)
}

/// `Tast_check.def ctx twd.under_normal_assumptions`; when there is no
/// dynamic TAST, also the keys for [`intersect_dynamic_warnings`].
///
/// The OCaml runs the warning checks a second time on the normal TAST to get
/// these keys (`intersect_dynamic_warnings`); recording them while
/// `Tast_check.def` runs gives the same keys without the second pass.
fn tast_check_def(
    ctx: &Arc<Ctx>,
    twd: &tast_with_dynamic::T<tast::Def>,
) -> Option<Vec<(isize, Pos)>> {
    match &twd.under_dynamic_assumptions {
        Some(_) => {
            tast_check::def(ctx, &twd.under_normal_assumptions);
            None
        }
        None => Some(tast_check::def_recording_warning_keys(
            ctx,
            &twd.under_normal_assumptions,
        )),
    }
}

fn set_tcopt_unstable_features(ctx: &Arc<Ctx>, fa: &nast::FileAttribute) -> Arc<Ctx> {
    typing_toplevel::set_tcopt_unstable_features(ctx, fa)
}

pub fn type_fun(ctx: &Arc<Ctx>, full_ast: nast::FunDef) -> Option<tast_with_dynamic::T<tast::Def>> {
    let pos = full_ast.fun.span.clone();
    handle_exn_as_error(&pos, || {
        let fun_ = naming::fun_def(ctx, full_ast);
        let ctx = fun_
            .file_attributes
            .iter()
            .fold(Arc::clone(ctx), |env, fa| {
                set_tcopt_unstable_features(&env, fa)
            });
        let aast::Def::Fun(fun_) = nast_check_def(&ctx, aast::Def::Fun(Box::new(fun_))) else {
            unreachable!()
        };
        let def_opt = typing_toplevel::fun_def(&ctx, &fun_)
            .map(|t| tast_with_dynamic::map(|f| aast::Def::Fun(Box::new(f)), t));
        // Only do TAST check on normal TAST
        let normal_keys = def_opt.as_ref().map(|fs| tast_check_def(&ctx, fs));
        // Intersect warning checks with dynamic TAST to determine trust
        if let Some(twd) = &def_opt {
            intersect_dynamic_warnings(&ctx, twd, normal_keys.flatten())
        }
        def_opt
    })
}

pub fn type_class(
    ctx: &Arc<Ctx>,
    full_ast: nast::Class_,
) -> Option<tast_with_dynamic::T<tast::Def>> {
    let pos = full_ast.span.clone();
    handle_exn_as_error(&pos, || {
        let class_ = naming::class_(ctx, full_ast);
        let ctx = class_
            .file_attributes
            .iter()
            .fold(Arc::clone(ctx), |env, fa| {
                set_tcopt_unstable_features(&env, fa)
            });
        let aast::Def::Class(class_) = nast_check_def(&ctx, aast::Def::Class(Box::new(class_)))
        else {
            unreachable!()
        };
        let def_opt = typing_toplevel::class_def(&ctx, &class_)
            .map(|t| tast_with_dynamic::map(|c| aast::Def::Class(Box::new(c)), t));
        // Only do TAST check on normal TAST
        let normal_keys = def_opt.as_ref().map(|c| tast_check_def(&ctx, c));
        // Intersect warning checks with dynamic TAST to determine trust
        if let Some(twd) = &def_opt {
            intersect_dynamic_warnings(&ctx, twd, normal_keys.flatten())
        }
        def_opt
    })
}

pub fn check_typedef(ctx: &Arc<Ctx>, full_ast: nast::Typedef) -> Option<tast::Def> {
    handle_exn_as_error(&Pos::NONE, || {
        let typedef = naming::typedef(ctx, full_ast);
        let ctx = typedef
            .file_attributes
            .iter()
            .fold(Arc::clone(ctx), |env, fa| {
                set_tcopt_unstable_features(&env, fa)
            });
        let aast::Def::Typedef(typedef) =
            nast_check_def(&ctx, aast::Def::Typedef(Box::new(typedef)))
        else {
            unreachable!()
        };
        let ret = typing_toplevel::typedef_def(&ctx, &typedef);
        let def = aast::Def::Typedef(Box::new(ret));
        tast_check::def(&ctx, &def);
        Some(def)
    })
}

pub fn check_const(ctx: &Arc<Ctx>, full_ast: nast::Gconst) -> Option<tast::Def> {
    let pos = full_ast.span.clone();
    handle_exn_as_error(&pos, || {
        let cst = naming::global_const(ctx, full_ast);
        let aast::Def::Constant(cst) = nast_check_def(ctx, aast::Def::Constant(Box::new(cst)))
        else {
            unreachable!()
        };
        let def = aast::Def::Constant(Box::new(typing_toplevel::gconst_def(ctx, &cst)));
        tast_check::def(ctx, &def);
        Some(def)
    })
}

pub fn check_module(ctx: &Arc<Ctx>, full_ast: nast::ModuleDef) -> Option<tast::Def> {
    let pos = full_ast.name.0.clone();
    handle_exn_as_error(&pos, || {
        let md = naming::module_(ctx, full_ast);
        let aast::Def::Module(md) = nast_check_def(ctx, aast::Def::Module(Box::new(md))) else {
            unreachable!()
        };
        let def = aast::Def::Module(Box::new(typing_toplevel::module_def(ctx, &md)));
        tast_check::def(ctx, &def);
        Some(def)
    })
}

/// [type_file ctx fn ~full_ast] works as follows:
/// 1. uses [fn] for the error context
/// 2. iterates over the defs in [full_ast]
/// 3. For each one runs them through [Naming], does [Nast_check],
///    typechecks and obtains tast with [Typing_toplevel], does [Tast_check]
///
/// It is unfortunate that this routine exists alongside [Typing_top_level.nast_to_tast]
/// which does almost exactly the same thing, except it doesn't do [Naming], and
/// there are minor differences in treatment of some toplevel nodes.
pub fn calc_errors_and_tast(
    ctx: &Arc<Ctx>,
    drop_fixmed: Option<bool>,
    fn_: &RelativePath,
    full_ast: nast::Program,
) -> (diagnostics::T, tast::ByNames) {
    calc_errors_and_tast_inner(ctx, drop_fixmed, fn_, full_ast, true)
}

/// Not in the OCaml (`calc_errors_and_tast` keeps every TAST to the end of the
/// file): [`calc_errors_and_tast`] for a caller that only wants the errors, as
/// a batch check does. The TAST of each definition is dropped once it is
/// checked (while it is still in the caches), which bounds the memory of a
/// file to one definition's TAST.
pub fn calc_errors(
    ctx: &Arc<Ctx>,
    drop_fixmed: Option<bool>,
    fn_: &RelativePath,
    full_ast: nast::Program,
) -> diagnostics::T {
    calc_errors_and_tast_inner(ctx, drop_fixmed, fn_, full_ast, false).0
}

/// The body of [`calc_errors_and_tast`]; the TASTs are kept when `keep_tasts`
/// (split so that [`calc_errors`] can drop each one once it is checked).
fn calc_errors_and_tast_inner(
    ctx: &Arc<Ctx>,
    drop_fixmed: Option<bool>,
    fn_: &RelativePath,
    full_ast: nast::Program,
    keep_tasts: bool,
) -> (diagnostics::T, tast::ByNames) {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    let nast::Defs {
        funs,
        classes,
        typedefs,
        constants,
        modules,
        stmts,
    } = nast::get_defs(full_ast);
    fn calc_tast<Def, Res>(
        ctx: &Arc<Ctx>,
        typecheck: impl Fn(&Arc<Ctx>, Def) -> Option<Res>,
        defs: Vec<(file_info::Id, Def)>,
        keep_tasts: bool,
    ) -> s_map::T<Res>
    where
        Res: Clone,
    {
        let mut acc = s_map::T::new();
        for (id, full_ast) in defs {
            if let Some(tast) = typecheck(ctx, full_ast) {
                if keep_tasts {
                    acc.insert(id.name, tast);
                }
            }
        }
        acc
    }
    diagnostics::do_with_context(Some(drop_fixmed), fn_.clone(), || {
        // Some of our tests depend upon the order of [calc_tast] being exactly as follows, i.e. funs
        // first, classes next, and so on. This is likely irrelevant to end user experience though,
        // since user gets sorted errors.
        let fun_tasts = calc_tast(ctx, type_fun, funs, keep_tasts);
        let class_tasts = calc_tast(ctx, type_class, classes, keep_tasts);
        let typedef_tasts = calc_tast(ctx, check_typedef, typedefs, keep_tasts);
        let gconst_tasts = calc_tast(ctx, check_const, constants, keep_tasts);
        let module_tasts = calc_tast(ctx, check_module, modules, keep_tasts);
        // For now we only want to elaborate/validate top-level statements to
        // generate errors but not typecheck
        let _: Option<nast::FunDef> = {
            let stmts = stmts.into_iter().map(|(_, stmt)| stmt).collect();
            naming::fun_def_of_stmts(ctx, stmts)
        };
        tast::ByNames {
            fun_tasts,
            class_tasts,
            typedef_tasts,
            gconst_tasts,
            module_tasts,
        }
    })
}

pub fn calc_errors_and_tast_for<Def, Res: Clone>(
    ctx: &Arc<Ctx>,
    drop_fixmed: Option<bool>,
    fn_: &RelativePath,
    typecheck: impl FnOnce(&Arc<Ctx>, Def) -> Option<Res>,
    full_ast: Def,
    id: &file_info::Id,
) -> (diagnostics::T, s_map::T<Res>) {
    let drop_fixmed = drop_fixmed.unwrap_or(true);
    diagnostics::do_with_context(Some(drop_fixmed), fn_.clone(), || {
        let mut acc = s_map::T::new();
        if let Some(tast) = typecheck(ctx, full_ast) {
            acc.insert(id.name.clone(), tast);
        }
        acc
    })
}
