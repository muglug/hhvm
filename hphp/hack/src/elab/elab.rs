// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

#![feature(box_patterns)]

mod elab_utils;
mod env;
mod lambda_captures;
mod lift_await;
mod pass;
mod passes;
mod transform;
mod validate_await;

/// Private convenience module for simplifying imports in pass implementations.
mod prelude {
    pub use std::ops::ControlFlow;
    pub use std::ops::ControlFlow::Break;
    pub use std::ops::ControlFlow::Continue;

    #[allow(unused_imports)]
    pub use std::rc::Rc;

    pub use naming_special_names_rust as sn;
    #[allow(unused_imports)]
    pub use oxidized::naming_error::NamingError;
    #[allow(unused_imports)]
    pub use oxidized::naming_error::UnsupportedFeature;
    #[allow(unused_imports)]
    pub use oxidized::naming_phase_error::ExperimentalFeature;
    #[allow(unused_imports)]
    pub use oxidized::naming_phase_error::NamingPhaseError;
    pub use oxidized::nast;
    #[allow(unused_imports)]
    pub use oxidized::nast_check_error::NastCheckError;
    #[allow(unused_imports)]
    pub use oxidized::parsing_error::ParsingError;

    #[allow(unused_imports)]
    pub(crate) use crate::elab_utils;
    pub use crate::env::Env;
    pub use crate::pass::Pass;
    #[allow(unused_imports)]
    pub use crate::transform::Transform;
}

use std::path::Path;
use std::sync::Arc;

use env::Env;
use env::ProgramSpecificOptions;
use hash::HashSet;
use oxidized::experimental_features::FeatureName;
use oxidized::namespace_env;
use oxidized::namespace_env::Mode;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast;
use oxidized::typechecker_options::TypecheckerOptions;
use pass::Pass;
use relative_path::RelativePath;
use transform::Transform;
use vec1::Vec1;

/// Provided for use in hackc as a simple collection of knobs outside of namespace env.
#[derive(Clone, Debug, Default)]
pub struct CodegenOpts {
    pub textual_remove_memoize: bool,
    pub emit_checked_unsafe_cast: bool,
}

/// Provided for use in hackc, where we have an `ns_env` in hand already.
/// Expected to behave the same as `elaborate_program` when `po_codegen` is
/// `true`.
pub fn elaborate_program_for_codegen(
    ns_env: Arc<namespace_env::Env>,
    path: &RelativePath,
    program: &mut nast::Program,
    opts: &CodegenOpts,
    active_experimental_features: HashSet<FeatureName>,
) -> Result<(), Vec1<NamingPhaseError>> {
    assert!(matches!(ns_env.mode, Mode::ForCodegen));
    let po = oxidized::parser_options::ParserOptions {
        codegen: true,
        disable_xhp_element_mangling: ns_env.disable_xhp_element_mangling,
        // Do not copy the auto_ns_map; it's not read in this crate except via
        // elaborate_namespaces_visitor, which uses the one in `ns_env` here
        ..Default::default()
    };
    let tco = TypecheckerOptions {
        po,
        ..Default::default()
    };
    elaborate_namespaces_visitor::elaborate_program(ns_env, program);
    let mut env = make_env(&tco, path, active_experimental_features);
    elaborate_common(&env, program);
    elaborate_package_expr(&env, program);
    elaborate_for_codegen(&env, program, opts);
    // Passes below here can emit errors
    lift_await::elaborate_program(&mut env, program, tco.po.codegen);
    let errs = env.into_errors();
    match Vec1::try_from_vec(errs) {
        Err(_) => Ok(()),
        Ok(v) => Err(v),
    }
}

/// Name a whole file.
///
/// For codegen (`tco.po.codegen`), only namespaces are elaborated.
///
/// For the typechecker this is what `Typing_check_job.calc_errors_and_tast`
/// does with a file, as far as naming is concerned: each definition of the
/// file is named on its own (as `Naming.fun_def`, `Naming.class_`, ... do),
/// and top-level statements are reported (`Naming.fun_def_of_stmts`) but
/// neither named nor checked. On return the program is the flat list of the
/// named definitions, in source order: namespace blocks are flattened, and
/// what `Naming_elab_defs` removes is removed, as are top-level statements.
pub fn elaborate_program(
    tco: &TypecheckerOptions,
    path: &RelativePath,
    program: &mut nast::Program,
    active_experimental_features: HashSet<FeatureName>,
) -> Vec<NamingPhaseError> {
    elaborate_namespaces_visitor::elaborate_program(ns_env(tco), program);
    let mut env = make_env(tco, path, active_experimental_features);
    elaborate_common(&env, program);
    if tco.po.codegen {
        return env.into_errors();
    }
    name_program(&mut env, program)
}

pub fn elaborate_fun_def(
    tco: &TypecheckerOptions,
    path: &RelativePath,
    f: &mut nast::FunDef,
    active_experimental_features: HashSet<FeatureName>,
) -> Vec<NamingPhaseError> {
    elaborate_namespaces_visitor::elaborate_fun_def(ns_env(tco), f);
    let mut env = make_env(tco, path, active_experimental_features);
    elaborate_common(&env, f);
    if tco.po.codegen {
        return env.into_errors();
    }
    name_fun_def(&mut env, f)
}

pub fn elaborate_class_(
    tco: &TypecheckerOptions,
    path: &RelativePath,
    c: &mut nast::Class_,
    active_experimental_features: HashSet<FeatureName>,
) -> Vec<NamingPhaseError> {
    elaborate_namespaces_visitor::elaborate_class_(ns_env(tco), c);
    let mut env = make_env(tco, path, active_experimental_features);
    elaborate_common(&env, c);
    if tco.po.codegen {
        return env.into_errors();
    }
    name_class_(&mut env, c)
}

pub fn elaborate_module_def(
    tco: &TypecheckerOptions,
    path: &RelativePath,
    m: &mut nast::ModuleDef,
    active_experimental_features: HashSet<FeatureName>,
) -> Vec<NamingPhaseError> {
    elaborate_namespaces_visitor::elaborate_module_def(ns_env(tco), m);
    let mut env = make_env(tco, path, active_experimental_features);
    elaborate_common(&env, m);
    if tco.po.codegen {
        return env.into_errors();
    }
    name_module_def(&mut env, m)
}

pub fn elaborate_gconst(
    tco: &TypecheckerOptions,
    path: &RelativePath,
    c: &mut nast::Gconst,
    active_experimental_features: HashSet<FeatureName>,
) -> Vec<NamingPhaseError> {
    elaborate_namespaces_visitor::elaborate_gconst(ns_env(tco), c);
    let mut env = make_env(tco, path, active_experimental_features);
    elaborate_common(&env, c);
    if tco.po.codegen {
        return env.into_errors();
    }
    name_gconst(&mut env, c)
}

pub fn elaborate_typedef(
    tco: &TypecheckerOptions,
    path: &RelativePath,
    t: &mut nast::Typedef,
    active_experimental_features: HashSet<FeatureName>,
) -> Vec<NamingPhaseError> {
    elaborate_namespaces_visitor::elaborate_typedef(ns_env(tco), t);
    let mut env = make_env(tco, path, active_experimental_features);
    elaborate_common(&env, t);
    if tco.po.codegen {
        return env.into_errors();
    }
    name_typedef(&mut env, t)
}

/// There is no `Naming.stmt`: a statement is named as the definitions are
/// (captures, `await` validation, then the naming passes).
pub fn elaborate_stmt(
    tco: &TypecheckerOptions,
    path: &RelativePath,
    t: &mut nast::Stmt,
    active_experimental_features: HashSet<FeatureName>,
) -> Vec<NamingPhaseError> {
    elaborate_namespaces_visitor::elaborate_stmt(ns_env(tco), t);
    let mut env = make_env(tco, path, active_experimental_features);
    elaborate_common(&env, t);
    if tco.po.codegen {
        return env.into_errors();
    }
    lambda_captures::elaborate_stmt(&mut env, t);
    let direct = env.take_errors();
    validate_await::validate_stmt(&env, t);
    elaborate_for_typechecking(&env, t);
    emitted(direct, env.take_errors())
}

// -- Naming for the typechecker (`naming/naming.ml`) --------------------------
//
// Each definition is named as `Naming.elab_elem` does: after the namespaces
// are elaborated (done by the callers), the captures of lambdas are computed
// (`Naming_captures`), the uses of `await` are validated
// (`Naming_validate_await`, for functions and classes only), and then the
// naming passes run.

fn name_fun_def(env: &mut Env, f: &mut nast::FunDef) -> Vec<NamingPhaseError> {
    lambda_captures::elaborate_fun_def(env, f);
    let direct = env.take_errors();
    validate_await::validate_fun_def(env, f);
    elaborate_for_typechecking(env, f);
    emitted(direct, env.take_errors())
}

fn name_class_(env: &mut Env, c: &mut nast::Class_) -> Vec<NamingPhaseError> {
    lambda_captures::elaborate_class_(env, c);
    let direct = env.take_errors();
    validate_await::validate_class_(env, c);
    elaborate_for_typechecking(env, c);
    emitted(direct, env.take_errors())
}

fn name_typedef(env: &mut Env, t: &mut nast::Typedef) -> Vec<NamingPhaseError> {
    lambda_captures::elaborate_typedef(env, t);
    let direct = env.take_errors();
    elaborate_for_typechecking(env, t);
    emitted(direct, env.take_errors())
}

fn name_gconst(env: &mut Env, c: &mut nast::Gconst) -> Vec<NamingPhaseError> {
    lambda_captures::elaborate_gconst(env, c);
    let direct = env.take_errors();
    elaborate_for_typechecking(env, c);
    emitted(direct, env.take_errors())
}

fn name_module_def(env: &mut Env, m: &mut nast::ModuleDef) -> Vec<NamingPhaseError> {
    lambda_captures::elaborate_module_def(env, m);
    let direct = env.take_errors();
    elaborate_for_typechecking(env, m);
    emitted(direct, env.take_errors())
}

/// The errors of one definition, in the order OCaml reports them.
///
/// `direct` are the errors `Naming_captures` adds to the diagnostics as it
/// finds them. The errors `raised` by `Naming_validate_await` and by the
/// naming passes are accumulated (`Naming_phase_error.add`, which prepends to
/// one list per kind of error) and only emitted when the definition is done
/// (`Naming_phase_error.emit`): kind by kind, the last one raised first. The
/// exception is `Naming_validate_clone_return_hint`, which also adds its
/// error directly.
fn emitted(direct: Vec<NamingPhaseError>, raised: Vec<NamingPhaseError>) -> Vec<NamingPhaseError> {
    use oxidized::nast_check_error::NastCheckError;
    let mut out = direct;
    let (mut naming, mut nast_check, mut unexpected_hints) = (vec![], vec![], vec![]);
    let (mut malformed_accesses, mut experimental_features, mut parsing) = (vec![], vec![], vec![]);
    for err in raised {
        match err {
            NamingPhaseError::NastCheck(NastCheckError::CloneReturnType(_)) => out.push(err),
            NamingPhaseError::Naming(_) => naming.push(err),
            NamingPhaseError::NastCheck(_) => nast_check.push(err),
            NamingPhaseError::UnexpectedHint(_) => unexpected_hints.push(err),
            NamingPhaseError::MalformedAccess(_) => malformed_accesses.push(err),
            NamingPhaseError::ExperimentalFeature(_) => experimental_features.push(err),
            NamingPhaseError::Parsing(_) => parsing.push(err),
        }
    }
    for errs in [
        naming,
        nast_check,
        unexpected_hints,
        malformed_accesses,
        experimental_features,
        parsing,
    ] {
        out.extend(errs.into_iter().rev());
    }
    out
}

/// `Typing_check_job.calc_errors_and_tast`, as far as naming is concerned.
fn name_program(env: &mut Env, program: &mut nast::Program) -> Vec<NamingPhaseError> {
    use nast::Def;

    // `Nast.get_defs`: the definitions of the file, those of namespace blocks
    // included, in source order. `Naming_elab_defs` gives the definitions that
    // are kept even though they are not named.
    fn flatten(defs: Vec<Def>, out: &mut Vec<Def>, stmts: &mut Vec<nast::Stmt>) {
        for def in defs {
            match def {
                Def::Namespace(ns) => flatten(ns.1, out, stmts),
                Def::Stmt(stmt) => stmts.push(*stmt),
                Def::FileAttributes(_) | Def::NamespaceUse(_) | Def::SetNamespaceEnv(_) => {}
                Def::Fun(_)
                | Def::Class(_)
                | Def::ClassAlias(_)
                | Def::Typedef(_)
                | Def::Constant(_)
                | Def::Module(_)
                | Def::SetModule(_) => out.push(def),
            }
        }
    }
    let mut defs = vec![];
    let mut stmts = vec![];
    flatten(std::mem::take(&mut program.0), &mut defs, &mut stmts);

    // "Some of our tests depend upon the order of [calc_tast] being exactly as
    // follows, i.e. funs first, classes next, and so on."
    let mut errs = vec![];
    for def in defs.iter_mut() {
        if let Def::Fun(f) = def {
            errs.extend(name_fun_def(env, f));
        }
    }
    for def in defs.iter_mut() {
        if let Def::Class(c) = def {
            errs.extend(name_class_(env, c));
        }
    }
    for def in defs.iter_mut() {
        if let Def::Typedef(t) = def {
            errs.extend(name_typedef(env, t));
        }
    }
    for def in defs.iter_mut() {
        if let Def::Constant(c) = def {
            errs.extend(name_gconst(env, c));
        }
    }
    for def in defs.iter_mut() {
        if let Def::Module(m) = def {
            errs.extend(name_module_def(env, m));
        }
    }
    program.0 = defs;

    // `Naming.fun_def_of_stmts`: top-level statements are an error, markup
    // aside. (`Naming_phase_error.emit` again: the last statement first.)
    errs.extend(
        stmts
            .into_iter()
            .rev()
            .filter(|nast::Stmt(_, stmt_)| !matches!(stmt_, nast::Stmt_::Markup(_)))
            .map(|nast::Stmt(pos, _)| {
                NamingPhaseError::Naming(oxidized::naming_error::NamingError::ToplevelStatement(
                    pos,
                ))
            }),
    );
    errs
}

fn ns_env(tco: &oxidized::global_options::GlobalOptions) -> Arc<namespace_env::Env> {
    // `Env::empty` copies the maps of the auto-imported names (hundreds of
    // strings) each time, and this runs for every definition: the last
    // environment made on this thread is kept, and given again for the same
    // options (it is immutable behind the `Arc`).
    type Last = (Vec<(String, String)>, bool, bool, Arc<namespace_env::Env>);
    thread_local! {
        static LAST: std::cell::RefCell<Option<Last>> = const { std::cell::RefCell::new(None) };
    }
    let po = &tco.po;
    LAST.with_borrow_mut(|last| {
        match last {
            Some((map, codegen, disable, env))
                if *codegen == po.codegen
                    && *disable == po.disable_xhp_element_mangling
                    && *map == po.auto_namespace_map =>
            {
                Arc::clone(env)
            }
            _ => {
                let env = Arc::new(namespace_env::Env::empty(
                    po.auto_namespace_map.clone(),
                    if po.codegen {
                        Mode::ForCodegen
                    } else {
                        Mode::ForTypecheck
                    },
                    po.disable_xhp_element_mangling,
                ));
                *last = Some((
                    po.auto_namespace_map.clone(),
                    po.codegen,
                    po.disable_xhp_element_mangling,
                    Arc::clone(&env),
                ));
                env
            }
        }
    })
}

/// `Naming.filename_in_allowed`: the file is one of `allowed_files`, or is
/// under one of them that ends with `*` (a prefix of the name, not of the path).
fn filename_in_allowed(allowed_files: &[String], path: &Path) -> bool {
    let filename = path.to_string_lossy();
    allowed_files.iter().any(|spec| match spec.strip_suffix('*') {
        Some(allowed_dir) => filename.starts_with(allowed_dir),
        None => !spec.is_empty() && *spec == filename,
    })
}

fn make_env(
    tco: &TypecheckerOptions,
    rel_path: &RelativePath,
    active_experimental_features: HashSet<FeatureName>,
) -> Env {
    let path = rel_path.path();
    // OCaml goes by the name of the file (`Naming.mk_env`).
    let is_hhi = rel_path.is_hhi() || path.extension().is_some_and(|ext| ext == "hhi");

    let allow_module_declarations = tco.tco_allow_all_files_for_module_declarations
        || filename_in_allowed(&tco.tco_allowed_files_for_module_declarations, path);

    let allow_ignore_readonly =
        filename_in_allowed(&tco.tco_allowed_files_for_ignore_readonly, path);

    Env::new(
        tco,
        &ProgramSpecificOptions {
            is_hhi,
            allow_module_declarations,
            allow_ignore_readonly,
        },
        active_experimental_features,
    )
}

/// Run the passes which are common to codegen and typechecking.
/// For now, these passes may not emit errors.
fn elaborate_common<T: Transform>(_env: &Env, _node: &mut T) {
    // Shape/tuple destructure disambiguation is now handled in the lowerer
    // (ExprLocation::LvaluePosition), so no common passes remain.
}

/// The naming passes of the typechecker: the `passes` of `naming/naming.ml`, in
/// the same order.
///
/// OCaml splits the passes into a top-down and a bottom-up traversal and
/// combines each kind in the order of the list. A pass here has both kinds of
/// handlers, so one pass stands for a `top_down_pass` / `bottom_up_pass` pair.
/// The passes `$p`, each in its default state, run as one: nested
/// [`pass::Pair`]s, which call each pass statically and clone without
/// allocating (the traversal clones the pass at every node).
macro_rules! passes {
    ($p:ty $(,)?) => { <$p>::default() };
    ($p:ty, $($rest:ty),+ $(,)?) => { pass::Pair(<$p>::default(), passes!($($rest),+)) };
}

fn elaborate_for_typechecking<T: Transform>(env: &Env, node: &mut T) {
    #[rustfmt::skip]
    let mut passes = passes![
        // Stop on `Invalid` expressions
        passes::guard_invalid::GuardInvalidPass,

        // -- Canonicalization passes -----------------------------------------

        // Remove top-level file attributes, noop and markup statements
        passes::elab_defs::ElabDefsPass,

        // Remove function bodies when in hhi mode
        passes::elab_func_body::ElabFuncBodyPass,

        // Flatten `Block` statements
        passes::elab_block::ElabBlockPass,

        // Strip `Hsoft` hints or replace with `Hlike`
        passes::elab_hint_hsoft::ElabHintHsoftPass,

        // Elaborate `Happly` to canonical representation, if any
        passes::elab_hint_happly::ElabHintHapplyPass,

        // Elaborate class identifier expressions (`CIexpr`) to canonical
        // representation: `CIparent`, `CIself`, `CIstatic`, `CI` _or_
        // `CIexpr (_,_, Lvar _ | This )`
        passes::elab_class_id::ElabClassIdPass,

        // Elaborate `Collection` to `ValCollection` or `KeyValCollection`
        passes::elab_expr_collection::ElabExprCollectionPass,

        // Check that user attributes are well-formed
        passes::elab_user_attributes::ElabUserAttributesPass,

        // Replace import expressions with invalid expression marker
        passes::elab_expr_import::ElabExprImportPass,

        // Elaborate local variables to canonical representation
        passes::elab_expr_lvar::ElabExprLvarPass,

        // Warn of explicit use of builtin enum classes; make subtyping of
        // enum classes explicit
        passes::elab_enum_class::ElabEnumClassPass,

        // Elaborate class members & xhp attributes
        passes::elab_class_members::ElabClassMembersPass,

        // Elaborate special function calls to canonical representation, if any
        passes::elab_call::ElabCallPass,

        // Elaborate invariant calls to canonical representation
        passes::elab_expr_call_hh_invariant::ElabExprCallHhInvariantPass,

        // -- Mark invalid hints and expressions & miscellaneous validation ---

        // Replace invalid uses of `void` and `noreturn` with `Herr`
        passes::elab_hint_retonly::ElabHintRetonlyPass,

        // Replace invalid uses of wildcard hints with `Herr`
        passes::elab_hint_wildcard::ElabHintWildcardPass,

        // Replace uses to `self` in shape field names with referenced class
        passes::elab_shape_field_name::ElabShapeFieldNamePass,

        // Replace invalid uses of `this` hints with `Herr`
        passes::elab_hint_this::ElabHintThisPass,

        // Replace invalid `Haccess` root hints with `Herr`
        passes::elab_hint_haccess::ElabHintHaccessPass,

        // Validate / replace invalid uses of dynamic classes in `New` and `Class_get`
        // expressions
        passes::elab_dynamic_class_name::ElabDynamicClassNamePass,

        // Replace non-constant class or global constant with invalid expression marker
        passes::elab_const_expr::ElabConstExprPass,

        // Replace malformed key / value bindings in as expressions with invalid
        // local var markers
        passes::elab_as_expr::ElabAsExprPass,

        // Validate hints used in `Cast` expressions
        passes::validate_expr_cast::ValidateExprCastPass,

        // Validate where `dynamic` can be used in a hint
        passes::validate_dynamic_hint::ValidateDynamicHintPass,

        // Check for duplicate function parameter names
        passes::validate_fun_params::ValidateFunParamsPass,

        // Validate use of `require implements`, `require extends` and
        // `require class` declarations for traits, interfaces and classes
        passes::validate_class_req::ValidateClassReqPass,

        // Validation dealing with common xhp naming errors
        passes::validate_xhp_name::ValidateXhpNamePass,

        // Validate polymorphic lambda expressions, ensuring return hint and all
        // parameter hints are provided
        passes::validate_polymorphic_lambda_expr::ValidatePolymorphicLambdaExprPass,

        // -- Elaboration & validation under typechecker options --------------

        // Add `supportdyn` and `Like` wrappers everywhere - under `everything-sdt`
        // typechecker option
        passes::elab_everything_sdt::ElabEverythingSdtPass,

        // Validate constructors under
        // `consistent-explicit_consistent_constructors` typechecker option
        passes::validate_class_consistent_construct::ValidateClassConsistentConstructPass,

        // Validate  use of `SupportDyn` class - depends on `enable-supportdyn`
        // and `everything_sdt` typechecker options
        passes::validate_supportdyn::ValidateSupportDynPass,

        // Validate use of module definitions - depends on:
        // - `allow_all_files_for_module_declarations`
        // - `allowed_files_for_module_declarations`
        // typechecker options
        passes::validate_module::ValidateModulePass,

        // Validate use of `optional` in function type hints
        passes::validate_function_hint_optional_parameters::ValidateFunctionHintOptionalParametersPass,

        // Reject `shape(..., T...)` typed open shapes unless tco_typed_open_shapes
        // is enabled
        passes::validate_typed_open_shape::ValidateTypedOpenShapePass,

        // Reject named variadic parameters in function type hints unless
        // tco_named_variadic_type is enabled
        passes::validate_named_variadic_type::ValidateNamedVariadicTypePass,

        // Reject variadic named parameters on function definitions (e.g.
        // `named int...`) unless tco_variadic_named_parameters is enabled
        passes::validate_variadic_named_parameter::ValidateVariadicNamedParameterPass,

        // Validate that return type of __clone is void
        passes::validate_clone_return_type::ValidateCloneReturnType,
    ];

    node.transform(env, &mut passes);
}

fn elaborate_package_expr<T: Transform>(env: &Env, node: &mut T) {
    #[rustfmt::skip]
    let mut passes = pass::Passes { passes: vec![
            Box::<passes::elab_expr_package::ElabExprPackagePass>::default()
    ]};
    node.transform(env, &mut passes);
    env.assert_no_errors();
}

fn elaborate_for_codegen<T: Transform>(env: &Env, node: &mut T, opts: &CodegenOpts) {
    let mut passes: Vec<Box<dyn Pass>> = Vec::new();

    if opts.textual_remove_memoize {
        passes.push(Box::<passes::remove_memo_attr::RemoveMemoAttr>::default());
    }
    // Insert assertion that the package being require-package accessed is loaded
    passes.push(Box::<passes::elab_require_package::ElabRequirePackagePass>::default());

    passes.push(Box::new(passes::drop_unsafe_cast::DropUnsafeCast {
        emit_checked_unsafe_cast: opts.emit_checked_unsafe_cast,
    }));

    let mut passes = pass::Passes { passes };
    node.transform(env, &mut passes);
    env.assert_no_errors();
}
