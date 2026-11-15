// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the entry points of `naming/naming.ml`: the naming of one
//! definition, as `Typing_check_job` calls it, and of top-level statements.
//!
//! The naming passes themselves are the `elab` crate (`elab::elaborate_fun_def`
//! and friends follow `Naming.fun_def` and friends: namespaces, captures,
//! `await` validation, then the passes of `naming.ml`); these functions give
//! them the OCaml interface. `Naming.elab_elem` reports the errors found
//! through `Naming_phase_error.emit`, which adds them to `Diagnostics`; so do
//! these, through `crate::naming_phase_error` and `crate::diagnostics`.
//!
//! `elab` takes the experimental features that the file enables; only its
//! `lift_await` reads them, and that does not run for the typechecker
//! (`Naming_validate_await` does), so the set is empty here.
//!
//! `Naming.program` (whole-file naming, for `Tast_provider`) is
//! [`program`].

use std::sync::Arc;

use oxidized::aast;
use oxidized::ast_defs;
use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast;

use crate::ctx::Ctx;

/// `Naming.fun_def`
pub fn fun_def(ctx: &Arc<Ctx>, mut fd: nast::FunDef) -> nast::FunDef {
    let filename = fd.fun.span.filename().clone();
    crate::naming_phase_error::emit(elab::elaborate_fun_def(
        &ctx.tco,
        &filename,
        &mut fd,
        Default::default(),
    ));
    fd
}

/// `Naming.class_`
pub fn class_(ctx: &Arc<Ctx>, mut c: nast::Class_) -> nast::Class_ {
    let filename = c.span.filename().clone();
    crate::naming_phase_error::emit(elab::elaborate_class_(
        &ctx.tco,
        &filename,
        &mut c,
        Default::default(),
    ));
    c
}

/// `Naming.module_`
pub fn module_(ctx: &Arc<Ctx>, mut md: nast::ModuleDef) -> nast::ModuleDef {
    let filename = md.span.filename().clone();
    crate::naming_phase_error::emit(elab::elaborate_module_def(
        &ctx.tco,
        &filename,
        &mut md,
        Default::default(),
    ));
    md
}

/// `Naming.global_const`
pub fn global_const(ctx: &Arc<Ctx>, mut cst: nast::Gconst) -> nast::Gconst {
    let filename = cst.span.filename().clone();
    crate::naming_phase_error::emit(elab::elaborate_gconst(
        &ctx.tco,
        &filename,
        &mut cst,
        Default::default(),
    ));
    cst
}

/// `Naming.typedef`
pub fn typedef(ctx: &Arc<Ctx>, mut td: nast::Typedef) -> nast::Typedef {
    let filename = td.span.filename().clone();
    crate::naming_phase_error::emit(elab::elaborate_typedef(
        &ctx.tco,
        &filename,
        &mut td,
        Default::default(),
    ));
    td
}

/// `Naming.emit_toplevel_stmt_errors`
fn emit_toplevel_stmt_errors(stmts: &[nast::Stmt]) {
    crate::naming_phase_error::emit(
        stmts
            .iter()
            .map(|aast::Stmt(pos, _)| {
                NamingPhaseError::Naming(NamingError::ToplevelStatement(pos.clone()))
            })
            .collect(),
    );
}

/// `Naming.fun_def_of_stmts`: report the top-level statements (other than
/// markup), and wrap them in an async function returning
/// `Awaitable<void>`, as a script would run them.
pub fn fun_def_of_stmts(ctx: &Arc<Ctx>, stmts: Vec<nast::Stmt>) -> Option<nast::FunDef> {
    // `Provider_context.get_popt ctx`
    let popt = &ctx.tco.po;
    let stmts: Vec<nast::Stmt> = stmts
        .into_iter()
        .filter(|aast::Stmt(_, s)| !matches!(s, aast::Stmt_::Markup(_)))
        .collect();
    emit_toplevel_stmt_errors(&stmts);
    let (first, tail) = stmts.split_first()?;
    let pos = tail.iter().fold(first.0.clone(), |acc, aast::Stmt(p, _)| {
        crate::pos::merge(&acc, p)
    });
    // Match the logic the lowerer does to assign packages to functions based
    // on file name.
    let package = {
        let pos_suffix = pos.filename().path_str().to_string();
        crate::package_provider::get_package_for_file(ctx, &pos_suffix)
            .map(|pkg| aast::PackageMembership::PackageConfigAssignment(pkg.name.1.clone()))
    };
    // `{ empty_with_default with ns_ns_uses; ns_disable_xhp_element_mangling }`
    // with `ns_ns_uses = S_map.union empty_with_default.ns_ns_uses (S_map.of_list
    // popt.auto_namespace_map)` (the first map's binding wins).
    let mut namespace = crate::hh_autoimport::namespace_env_empty_with_default();
    for (k, v) in popt.auto_namespace_map.iter().rev() {
        // (`S_map.of_list`: the last binding of a key wins; then the union.)
        if !namespace.ns_uses.contains_key(k) {
            namespace.ns_uses.insert(k.clone(), v.clone());
        }
    }
    namespace.disable_xhp_element_mangling = popt.disable_xhp_element_mangling;
    let awaitable_void = aast::Hint(
        pos.clone(),
        Box::new(aast::Hint_::Happly(
            ast_defs::Id(
                pos.clone(),
                naming_special_names_rust::classes::AWAITABLE.to_string(),
            ),
            vec![aast::Hint(
                pos.clone(),
                Box::new(aast::Hint_::Hprim(aast::Tprim::Tvoid)),
            )],
        )),
    );
    Some(aast::FunDef {
        // An empty function name is appropriate, as the AST can already
        // include empty function names due to parse errors.
        name: ast_defs::Id(pos.clone(), String::new()),
        namespace: Arc::new(namespace),
        file_attributes: vec![],
        mode: oxidized::file_info::Mode::Mstrict,
        fun: aast::Fun_ {
            span: pos.clone(),
            readonly_this: None,
            tparams: vec![],
            annotation: (),
            readonly_ret: None,
            ret: aast::TypeHint((), Some(awaitable_void)),
            params: vec![],
            body: aast::FuncBody {
                fb_ast: aast::Block(stmts),
            },
            ctxs: None,
            unsafe_ctxs: None,
            // enable top-level await
            fun_kind: ast_defs::FunKind::FAsync,
            user_attributes: aast::UserAttributes(vec![]),
            external: false,
            hidden: false,
            doc_comment: None,
        },
        internal: false,
        module: None,
        tparams: vec![],
        where_constraints: vec![],
        package,
    })
}

/// `Naming.program_filename`: the file of the first definition that has a
/// position.
fn program_filename(defs: &nast::Program) -> crate::relative_path::T {
    for def in defs.0.iter() {
        match def {
            aast::Def::Fun(fun_def) => return fun_def.fun.span.filename().clone(),
            aast::Def::Class(class_) => return class_.span.filename().clone(),
            aast::Def::Stmt(stmt) => return stmt.0.filename().clone(),
            aast::Def::Typedef(typedef) => return typedef.span.filename().clone(),
            aast::Def::Constant(gconst) => return gconst.span.filename().clone(),
            aast::Def::Module(module_def) => return module_def.span.filename().clone(),
            _ => {}
        }
    }
    crate::relative_path::DEFAULT
}

/// `Naming.adjust_toplevel_stmts`: return an updated [Nast.program] where
/// top-level statements are wrapped in a function. This is not an
/// elaboration pass because it affects the entire file and whole-file
/// elaboration passes are not used in `Typing_check_job.calc_errors_and_tast`.
/// Shared logic with `Typing_check_job.calc_errors_and_tast` is in
/// [`fun_def_of_stmts`].
fn adjust_toplevel_stmts(ctx: &Arc<Ctx>, program: nast::Program) -> nast::Program {
    let mut toplevel_defs = vec![];
    let mut toplevel_stmts = vec![];
    for def in program.0 {
        match def {
            aast::Def::Stmt(s) => toplevel_stmts.push(*s),
            def => toplevel_defs.push(def),
        }
    }
    match fun_def_of_stmts(ctx, toplevel_stmts) {
        Some(def) => {
            let mut defs = Vec::with_capacity(toplevel_defs.len() + 1);
            defs.push(aast::Def::Fun(Box::new(def)));
            defs.extend(toplevel_defs);
            aast::Program(defs)
        }
        None => aast::Program(toplevel_defs),
    }
}

/// `Naming.program`: the naming of a whole file (`Tast_provider`).
pub fn program(ctx: &Arc<Ctx>, program: nast::Program) -> nast::Program {
    let filename = program_filename(&program);
    let mut program = adjust_toplevel_stmts(ctx, program);
    crate::naming_phase_error::emit(elab::elaborate_program(
        &ctx.tco,
        &filename,
        &mut program,
        Default::default(),
    ));
    // `elab_core_program` visits every definition, class aliases included,
    // which `elab::elaborate_program` (the definitions as
    // `Typing_check_job.calc_errors_and_tast` names them) leaves alone.
    for def in program.0.iter_mut() {
        if let aast::Def::ClassAlias(ca) = def {
            crate::naming_phase_error::emit(elab::elaborate_class_alias(
                &ctx.tco,
                &filename,
                ca,
                Default::default(),
            ));
        }
    }
    program
}
