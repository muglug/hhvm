// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Checks on the named AST that need no type information: the port of
//! `typing/nast_check/*.ml` (and of `Nast_check.program`, which runs them),
//! and of `typing/nast_init_check.ml`.
//!
//! Each check lives in the module named after its OCaml file.
//!
//! - `nast_visitor` is the traversal most checks share (`Nast_visitor`), with
//!   the environment of `nast_check_env`.
//! - `stateful_aast_visitor` is the traversal of the two checks that keep a
//!   state of their own (`unbound_name_check`, `function_pointer_check`).
//! - `nast_init_check` is run per class by typing in OCaml
//!   (`Typing_class.class_wellformedness_checks`).

mod attribute_nast_checks;
mod class_tparams_check;
mod const_prohibited_check;
mod control_context_check;
mod decl_init_check;
mod duplicate_class_member_check;
mod duplicate_xhp_attribute_check;
mod dynamically_callable_attr_check;
mod function_pointer_check;
mod global_const_check;
mod illegal_name_check;
mod inout_check;
mod interface_check;
mod list_rvalue_check;
mod naming_coroutine_check;
mod nast_check_env;
mod nast_class_method_check;
mod nast_generics_check;
pub(crate) mod nast_init_check;
mod nast_visitor;
mod package_expression_check;
mod placeholder_check;
mod private_final_check;
mod prop_modifier_prohibited_check;
mod read_from_append_check;
mod shape_name_check;
mod stateful_aast_visitor;
mod type_structure_leak_check;
mod unbound_name_check;
mod well_formed_internal_trait;

use naming_special_names_rust as sn;
use oxidized::diagnostics::Diagnostic;
use oxidized::experimental_features::FeatureStatus;
use oxidized::message::Message;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast;
use oxidized::scoured_comments::ScouredComments;

use crate::ctx::Ctx;
use crate::diagnostics;

/// The errors of the checks, in the order they are found.
#[derive(Default)]
pub struct Errors(Vec<Diagnostic>);

impl Errors {
    /// `Diagnostics.add_diagnostic (X.to_user_diagnostic error)`, for the
    /// structured errors (`Naming_error`, `Nast_check_error`, ...).
    pub fn add(&mut self, error: impl Into<NamingPhaseError>) {
        if let Some(diagnostic) = crate::naming_errors::to_diagnostic(error.into()) {
            self.0.push(diagnostic);
        }
    }
}

/// `Naming_attributes`
mod attrs {
    use oxidized::nast;
    use oxidized::pos::Pos;

    pub fn find<'a>(x: &str, xs: &'a nast::UserAttributes) -> Option<&'a nast::UserAttribute> {
        xs.0.iter().find(|ua| ua.name.1 == x)
    }

    pub fn find2<'a>(
        x1: &str,
        x2: &str,
        xs: &'a nast::UserAttributes,
    ) -> Option<&'a nast::UserAttribute> {
        xs.0.iter().find(|ua| ua.name.1 == x1 || ua.name.1 == x2)
    }

    pub fn mem(x: &str, xs: &nast::UserAttributes) -> bool {
        find(x, xs).is_some()
    }

    pub fn mem2(x1: &str, x2: &str, xs: &nast::UserAttributes) -> bool {
        find2(x1, x2, xs).is_some()
    }

    pub fn mem_pos<'a>(x: &str, xs: &'a nast::UserAttributes) -> Option<&'a Pos> {
        find(x, xs).map(|ua| &ua.name.0)
    }
}

/// `Typechecker_options` accessors for options that the configuration sets
/// (`const_attribute`, `const_static_props`, `is_systemlib`). They return an
/// `Option` because `hh_config` did not read these options at first, and a
/// check that read them then would have reported errors the configuration
/// turns off; `utils/hh_config/hh_config.rs` now reads them as
/// `Server_config.load_config` does, so `HH_CONFIG_READS_THEM` is on.
mod tcopt {
    use crate::ctx::Ctx;

    const HH_CONFIG_READS_THEM: bool = true;

    /// `Typechecker_options.const_attribute`
    pub fn const_attribute(ctx: &Ctx) -> Option<bool> {
        HH_CONFIG_READS_THEM.then_some(ctx.tco.tco_const_attribute)
    }

    /// `Typechecker_options.const_static_props`
    pub fn const_static_props(ctx: &Ctx) -> Option<bool> {
        HH_CONFIG_READS_THEM.then_some(ctx.tco.po.const_static_props)
    }

    /// `Typechecker_options.is_systemlib`
    pub fn is_systemlib(ctx: &Ctx) -> Option<bool> {
        HH_CONFIG_READS_THEM.then_some(ctx.tco.po.is_systemlib)
    }
}

/// `Typechecker_options.is_unstable_feature_enabled`, for a definition of a
/// file with the given file attributes: `Typing_check_job` adds the features
/// of `<<file: __EnableUnstableFeatures(...)>>` to the options before it runs
/// the checks (`Typing_toplevel.set_tcopt_unstable_features`).
fn is_unstable_feature_enabled(
    ctx: &Ctx,
    file_attributes: &[nast::FileAttribute],
    name: &str,
) -> bool {
    let enabled_by_file = file_attributes.iter().any(|fa| {
        attrs::find(
            sn::user_attributes::ENABLE_UNSTABLE_FEATURES,
            &fa.user_attributes,
        )
        .is_some_and(|ua| {
            ua.params
                .iter()
                .any(|param| matches!(&param.2, nast::Expr_::String(s) if s == name))
        })
    });
    enabled_by_file
        || ctx.tco.tco_enabled_unstable_features.contains(name)
        || matches!(
            ctx.tco.po.experimental_features.get(name),
            Some(FeatureStatus::OngoingRelease)
        )
}

fn file_attributes(def: &nast::Def) -> &[nast::FileAttribute] {
    match def {
        nast::Def::Fun(fd) => &fd.file_attributes,
        nast::Def::Class(c) => &c.file_attributes,
        nast::Def::Typedef(t) => &t.file_attributes,
        _ => &[],
    }
}

/// `Nast_check.visitor`: the handlers, in the order they are run in at each
/// node.
fn handlers<'a>(ctx: &'a Ctx, def: &'a nast::Def) -> Vec<Box<dyn nast_visitor::Handler<'a> + 'a>> {
    if ctx.tco.tco_skip_tast_checks {
        return vec![];
    }
    let mut handlers: Vec<Box<dyn nast_visitor::Handler<'a> + 'a>> = vec![];
    if !is_unstable_feature_enabled(ctx, file_attributes(def), "with_refinement_alias") {
        handlers.push(Box::new(type_structure_leak_check::TypeStructureLeakCheck));
    }
    // `Pessimisation_node_recording.handler` (when
    // `record_fine_grained_dependencies` is set) records dependency graph
    // nodes and reports nothing: there is nothing to port while there is no
    // dependency graph.
    handlers.push(Box::new(const_prohibited_check::ConstProhibitedCheck));
    handlers.push(Box::new(
        prop_modifier_prohibited_check::PropModifierProhibitedCheck,
    ));
    handlers.push(Box::new(inout_check::InoutCheck));
    handlers.push(Box::new(naming_coroutine_check::NamingCoroutineCheck));
    handlers.push(Box::new(interface_check::InterfaceCheck));
    handlers.push(Box::new(illegal_name_check::IllegalNameCheck));
    handlers.push(Box::new(class_tparams_check::ClassTparamsCheck));
    handlers.push(Box::new(control_context_check::ControlContextCheck));
    handlers.push(Box::new(read_from_append_check::ReadFromAppendCheck));
    handlers.push(Box::new(
        dynamically_callable_attr_check::DynamicallyCallableAttrCheck,
    ));
    handlers.push(Box::new(nast_generics_check::NastGenericsCheck));
    handlers.push(Box::new(nast_class_method_check::NastClassMethodCheck));
    handlers.push(Box::new(global_const_check::GlobalConstCheck));
    handlers.push(Box::new(
        duplicate_class_member_check::DuplicateClassMemberCheck,
    ));
    handlers.push(Box::new(shape_name_check::ShapeNameCheck));
    handlers.push(Box::new(
        duplicate_xhp_attribute_check::DuplicateXhpAttributeCheck,
    ));
    handlers.push(Box::new(attribute_nast_checks::AttributeNastChecks));
    handlers.push(Box::new(list_rvalue_check::ListRvalueCheck));
    handlers.push(Box::new(placeholder_check::PlaceholderCheck));
    handlers.push(Box::new(private_final_check::PrivateFinalCheck));
    handlers.push(Box::new(
        well_formed_internal_trait::WellFormedInternalTrait,
    ));
    handlers.push(Box::new(package_expression_check::PackageExpressionCheck));
    handlers
}

/// `Nast_check.def`, then what `Typing_toplevel` runs of `Nast_init_check`.
fn check_def<'a>(ctx: &'a Ctx, def: &'a nast::Def, errors: &mut Errors) {
    // `(visitor ctx)#go_def ctx d`
    let mut visitor = nast_visitor::IterWith {
        handlers: handlers(ctx, def),
        errors,
    };
    visitor.go_def(ctx, def);

    // `let v = stateful_visitor ctx in v#on_def v#initial_state d`
    let mut stateful_visitor = stateful_aast_visitor::Checker {
        visitor: stateful_aast_visitor::Combined(
            unbound_name_check::UnboundNameCheck::new(ctx),
            function_pointer_check::FunctionPointerCheck,
        ),
        errors,
    };
    stateful_visitor.on_def(def);

    // `Typing_class.class_wellformedness_checks`
    if let nast::Def::Class(c) = def {
        nast_init_check::class_(ctx, c, errors);
    }
}

/// The definitions that `Typing_check_job.calc_errors_and_tast` checks
/// (`Nast.get_defs`), in the order it checks them in: functions, classes,
/// typedefs, constants, modules.
fn get_defs(program: &nast::Program) -> Vec<&nast::Def> {
    fn collect<'a>(defs: &'a [nast::Def], acc: &mut [Vec<&'a nast::Def>; 5]) {
        for def in defs {
            match def {
                nast::Def::Fun(_) => acc[0].push(def),
                nast::Def::Class(_) => acc[1].push(def),
                nast::Def::Typedef(_) => acc[2].push(def),
                nast::Def::Constant(_) => acc[3].push(def),
                nast::Def::Module(_) => acc[4].push(def),
                nast::Def::Namespace(ns) => collect(&ns.1, acc),
                // Top-level statements are named (for the errors of naming)
                // but neither checked nor typed.
                nast::Def::Stmt(_)
                | nast::Def::ClassAlias(_)
                | nast::Def::NamespaceUse(_)
                | nast::Def::SetNamespaceEnv(_)
                | nast::Def::SetModule(_)
                | nast::Def::FileAttributes(_) => {}
            }
        }
    }
    let mut acc: [Vec<&nast::Def>; 5] = Default::default();
    collect(&program.0, &mut acc);
    acc.into_iter().flatten().collect()
}

/// The `HH_FIXME` comments of the file an error is in.
///
/// The caller of `check_program` has them (`parse::NamedFile::comments`) but
/// does not pass them, so the file is parsed again. This only happens for a
/// file in which a check found something; `check_program_with_comments` is
/// the entry point that does not need it.
fn scoured_comments(ctx: &Ctx, error: &Diagnostic) -> Option<ScouredComments> {
    use aast_parser::AastParser;
    use file_provider::FileProvider;
    use parser_core_types::indexed_source_text::IndexedSourceText;
    use parser_core_types::source_text::SourceText;

    let Message(pos, _) = &error.claim;
    let path = std::sync::Arc::new(pos.filename().clone());
    let text = ctx.files.get((&*path).into()).ok()?;
    let indexed = IndexedSourceText::new(SourceText::make(path, &text));
    let result = AastParser::from_text(&ctx.parser_env, &indexed, Default::default()).ok()?;
    Some(result.scoured_comments)
}

fn run_checks(ctx: &Ctx, program: &nast::Program) -> Vec<Diagnostic> {
    let mut errors = Errors::default();
    for def in get_defs(program) {
        check_def(ctx, def, &mut errors);
    }
    errors.0
}

/// Drop the errors that have an `HH_FIXME`.
///
/// `ScouredComments::misuses` are the `HH_FIXME`s in declarations (outside of
/// function bodies) whose code is not in `allowed_decl_fixme_codes`. They
/// silence errors here as the others do: like `diagnostics::is_fixmed`, this
/// does not tell which codes may be silenced where (the options that say so
/// do not reach `hh single` yet).
fn drop_fixmed(errors: &mut Vec<Diagnostic>, comments: &ScouredComments) {
    errors.retain(|error| {
        let Message(pos, _) = &error.claim;
        !diagnostics::is_fixmed(&comments.fixmes, pos, error.code)
            && !diagnostics::is_fixmed(&comments.misuses, pos, error.code)
    });
}

/// Run every check on the definitions of a named file.
pub fn check_program(ctx: &Ctx, program: &nast::Program, out: &mut Vec<Diagnostic>) {
    let mut errors = run_checks(ctx, program);
    if let Some(comments) = errors
        .first()
        .and_then(|error| scoured_comments(ctx, error))
    {
        drop_fixmed(&mut errors, &comments);
    }
    out.extend(errors);
}

/// `check_program`, given the comments of the file (for its `HH_FIXME`s).
pub fn check_program_with_comments(
    ctx: &Ctx,
    program: &nast::Program,
    comments: &ScouredComments,
    out: &mut Vec<Diagnostic>,
) {
    let mut errors = run_checks(ctx, program);
    drop_fixmed(&mut errors, comments);
    out.extend(errors);
}
