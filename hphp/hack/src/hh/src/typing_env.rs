// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_env.ml`. See `hh/PORTING.md`.
//!
//! The functions are those of `typing_env.mli`, in the order of
//! `typing_env.ml`. As PORTING.md prescribes, a function that returns `env`
//! (or `env * x`) in OCaml takes `&mut Env` and returns `()` (or `x`); a
//! function that only reads the environment takes `&Env`. Labelled and
//! optional arguments are positional, in the order of the `.mli`.
//!
//! - [`deps`] is the port of `typing/env/deps.ml` (the OCaml module `Deps`,
//!   which is in the same library as `Typing_env` and has no file of its own
//!   in this crate).
//! - [`expose_to_tast_env`] is `Typing_env.Expose_to_tast_env`.
//! - [`fake_members`] is `Typing_env.FakeMembers`, [`log`] is
//!   `Typing_env.Log`.
//!
//! Several functions of the OCaml are wrapped in `log_env_change`, which
//! takes the environment before and after. The environment before is only
//! needed when logging is on for that function, so it is only copied then
//! (`with_log_env_change`).

use std::rc::Rc;
use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::ast_defs::ClassishKind;
use oxidized::file_info;
use oxidized::local_id;
use oxidized::local_id::LocalId;
use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::naming_types;
use oxidized::nast;
use oxidized::package;
use oxidized::pos::Pos;
use oxidized::pos_or_decl;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typechecker_options::TypecheckerOptions;
use pos::ToOxidized;
use relative_path::RelativePath;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_counters;
pub use crate::decl_enforceability::ClassOrTypedefResult;
use crate::decl_entry;
use crate::decl_provider;
use crate::expression_id;
use crate::folded_class as cls;
use crate::folded_class::ClassElt;
use crate::internal_type_set as ity_set;
use crate::tast;
use crate::tvid;
use crate::type_parameter_env as tp_env;
use crate::typing_continuations as c;
use crate::typing_defs;
use crate::typing_defs_constraints::ConstraintType;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::deref_constraint_type;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core::Capability;
use crate::typing_defs_core::ConsistentKind;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Exact;
use crate::typing_defs_core::LoclTparam;
use crate::typing_defs_core::ParamMode;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::ValKind;
use crate::typing_defs_core::deref;
use crate::typing_defs_core::get_fp_mode;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::map_reason;
use crate::typing_defs_core::mk;
use crate::typing_env_return_info;
use crate::typing_env_types;
use crate::typing_env_types::Env;
use crate::typing_env_types::ExprTreeEnv;
use crate::typing_error;
use crate::typing_fake_members as fake;
use crate::typing_inference_env as inf;
use crate::typing_kinding_defs as k_defs;
use crate::typing_local_packages;
use crate::typing_local_types;
use crate::typing_local_types::Local;
use crate::typing_logic;
use crate::typing_per_cont_env as lenvc;
use crate::typing_pessimisation_deps;
use crate::typing_reason;
use crate::typing_reason::Blame;
use crate::typing_reason::T as Reason;
use crate::typing_set as ty_set;

/// `Tvid.Set.t`
pub type TvidSet = tvid::set::T;

/// `Internal_type_set.t`
type ITySet = ity_set::T;

/// `S_set.t`
type SSet = im::OrdSet<String>;

/// The port of `typing/env/deps.ml`: the dependencies that the functions of
/// `Typing_env` record.
pub mod deps {
    // I assume we don't want to implicitly add
    // dependencies in our dependency-adding machinery

    use oxidized::decl_reference::DeclReference;
    use pos::Pos as _;

    use super::ClassElt;
    use super::Env;
    use super::cls;
    use super::decl_entry;
    use super::decl_provider;
    use super::typing_pessimisation_deps;
    use crate::typing_deps;
    use crate::typing_deps::dep;
    use crate::typing_deps::dep::Variant as Dep;

    // `Pos_or_decl.is_hhi`. The positions of the decls of `hackrs` (`BPos`)
    // are tested with `BPos::is_hhi`, which is the same test.

    pub fn get_current_decl(env: &Env) -> Option<DeclReference> {
        env.decl_env.droot.as_ref().map(dep::to_decl_reference)
    }

    fn add_fine_dep_if_enabled(env: &Env, dependency: &Dep) {
        let decl_env = &env.decl_env;
        let ctx = &decl_env.ctx;
        // We resolve the dependency to its origin. See
        // [Typing_extends.add_pessimisation_dependency] for details.
        let dependency_on_origin = || match dependency {
            Dep::Method(class_name, method_name) => {
                let origin_name = decl_entry::to_option(decl_provider::get_class(
                    None, ctx, class_name,
                ))
                .and_then(|cls| cls::get_method(&cls, method_name))
                .map(|elt| elt.ce_origin);
                let origin_name = origin_name.unwrap_or_else(|| class_name.clone());
                Dep::Method(origin_name, method_name.clone())
            }
            Dep::SMethod(class_name, method_name) => {
                let origin_name = decl_entry::to_option(decl_provider::get_class(
                    None, ctx, class_name,
                ))
                .and_then(|cls| cls::get_smethod(&cls, method_name))
                .map(|elt| elt.ce_origin);
                let origin_name = origin_name.unwrap_or_else(|| class_name.clone());
                Dep::SMethod(origin_name, method_name.clone())
            }
            _ => dependency.clone(),
        };
        // `Typechecker_options.record_fine_grained_dependencies`
        if env.genv.tcopt.tco_record_fine_grained_dependencies {
            let dependency = dependency_on_origin();
            typing_pessimisation_deps::try_add_fine_dep(
                &crate::provider_context::get_deps_mode(ctx),
                decl_env.droot.as_ref(),
                decl_env.droot_member.as_ref(),
                &dependency,
            )
        }
    }

    fn mark_declared_fine(mode: &typing_deps::mode::T, dep: &Dep) {
        typing_pessimisation_deps::try_add_fine_dep(mode, Some(&Dep::Declares), None, dep)
    }

    /// Not in the OCaml: whether `add_dependency_edge` has an effect (in a
    /// batch check it has none: no dependency is recorded), so that callers
    /// can skip building the dependency (strings, class names).
    /// Whether `add_dependency_edge` records anything (callers that skip
    /// lookups made only for their dependency edges test it).
    pub fn records_dependency_edges(env: &Env) -> bool {
        let decl_env = &env.decl_env;
        (decl_env.droot.is_some() && !typing_deps::add_idep_is_noop(&decl_env.ctx.deps_mode))
            || env.genv.tcopt.tco_record_fine_grained_dependencies
    }

    /// `add_dependency_edge env dep`, with the dependency built only when
    /// it is recorded.
    fn add_dependency_edge(env: &Env, dep: impl FnOnce() -> Dep) {
        if !records_dependency_edges(env) {
            return;
        }
        let dep = &dep();
        // Not in the OCaml: see `type_expansions::recording`.
        if crate::type_expansions::recording::is_active() {
            crate::type_expansions::recording::record_dep(dep)
        }
        let decl_env = &env.decl_env;
        if let Some(root) = &decl_env.droot {
            let ctx = &decl_env.ctx;
            typing_deps::add_idep(&ctx.deps_mode, root, dep);
        }
        add_fine_dep_if_enabled(env, dep)
    }

    /// Not in the OCaml: `add_dependency_edge env dep` for a dependency that
    /// a cached localization recorded (for another definition) when it was
    /// computed (`typing_phase`'s `MakeTyCache::extra`).
    pub(crate) fn add_recorded_dependency_edge(env: &Env, dep: &Dep) {
        add_dependency_edge(env, || dep.clone())
    }

    fn mark_declared(env: &Env, dep: &Dep) {
        let mode = crate::provider_context::get_deps_mode(&env.decl_env.ctx);
        typing_deps::add_idep(&mode, &Dep::Declares, dep);
        mark_declared_fine(&mode, dep);
    }

    pub fn mark_class_constant_declared(env: &Env, class_name: &str, const_name: &str) {
        mark_declared(
            env,
            &Dep::Const(class_name.to_string(), const_name.to_string()),
        )
    }

    pub fn mark_typeconst_declared(env: &Env, class_name: &str, typeconst_name: &str) {
        mark_declared(
            env,
            &Dep::Const(class_name.to_string(), typeconst_name.to_string()),
        )
    }

    pub fn mark_property_declared(
        env: &Env,
        is_static: bool,
        class_name: &str,
        property_name: &str,
    ) {
        mark_declared(
            env,
            &if is_static {
                Dep::SProp(class_name.to_string(), property_name.to_string())
            } else {
                Dep::Prop(class_name.to_string(), property_name.to_string())
            },
        )
    }

    pub fn mark_method_declared(env: &Env, is_static: bool, class_name: &str, method_name: &str) {
        mark_declared(
            env,
            &if is_static {
                Dep::SMethod(class_name.to_string(), method_name.to_string())
            } else {
                Dep::Method(class_name.to_string(), method_name.to_string())
            },
        )
    }

    pub fn mark_constructor_declared(env: &Env, class_name: &str) {
        mark_declared(env, &Dep::Constructor(class_name.to_string()))
    }

    pub fn mark_xhp_attribute_declared(env: &Env, class_name: &str, attr_name: &str) {
        mark_declared(
            env,
            &Dep::Prop(class_name.to_string(), attr_name.to_string()),
        )
    }

    pub fn make_depend_on_gconst(env: &Env, name: &str, def: Option<&decl_provider::GconstDecl>) {
        match def {
            Some(cst) if cst.pos.is_hhi() => {}
            _ => add_dependency_edge(env, || Dep::GConst(name.to_string())),
        }
    }

    pub fn make_depend_on_fun(env: &Env, name: &str, fd: &decl_entry::T<decl_provider::FunDecl>) {
        match fd {
            decl_entry::T::Found(fd) if fd.pos.is_hhi() => {}
            _ => add_dependency_edge(env, || Dep::Fun(name.to_string())),
        }
    }

    fn make_depend_on_class_name(env: &Env, class_name: &str) {
        add_dependency_edge(env, || Dep::Type(class_name.to_string()))
    }

    pub fn make_depend_on_class(env: &Env, x: &str, cd: &decl_entry::T<cls::T>) {
        match cd {
            decl_entry::T::Found(cd) if cls::pos_is_hhi(cd) => {}
            _ => make_depend_on_class_name(env, x),
        }
    }

    fn make_depend_on_constructor_name(env: &Env, class_name: &str) {
        make_depend_on_class_name(env, class_name);
        add_dependency_edge(env, || Dep::Constructor(class_name.to_string()));
    }

    pub fn make_depend_on_constructor(env: &Env, class_: &cls::T) {
        if !cls::pos_is_hhi(class_) {
            make_depend_on_constructor_name(env, &cls::name(class_));
            if let Some(ce) = cls::construct(class_).0 {
                make_depend_on_constructor_name(env, &ce.ce_origin)
            }
        }
    }

    pub fn make_depend_on_module_name(env: &Env, module_name: &str) {
        add_dependency_edge(env, || Dep::Module(module_name.to_string()))
    }

    pub fn make_depend_on_module(env: &Env, name: &str, md: Option<&decl_provider::ModuleDecl>) {
        match md {
            Some(md) if md.pos.is_hhi() => {}
            _ => make_depend_on_module_name(env, name),
        }
    }

    pub fn make_depend_on_parent(
        env: &Env,
        skip_constructor_dep: bool,
        name: &str,
        class_: &decl_entry::T<cls::T>,
    ) {
        match class_ {
            decl_entry::T::Found(cd) if cls::pos_is_hhi(cd) => {}
            _ => {
                if !skip_constructor_dep {
                    make_depend_on_constructor_name(env, name)
                };
                add_dependency_edge(env, || Dep::Extends(name.to_string()))
            }
        }
    }

    pub fn add_member_dep(
        is_method: bool,
        is_static: bool,
        env: &Env,
        class_: &cls::T,
        mid: &str,
        class_elt_opt: Option<&ClassElt>,
    ) {
        let add_dep = |cid: &str| {
            add_dependency_edge(env, || {
                let (cid, mid) = (cid.to_string(), mid.to_string());
                match (is_method, is_static) {
                    (true, true) => Dep::SMethod(cid, mid),
                    (true, false) => Dep::Method(cid, mid),
                    (false, true) => Dep::SProp(cid, mid),
                    (false, false) => Dep::Prop(cid, mid),
                }
            })
        };
        // (Not in the OCaml: nothing to build when nothing is recorded.)
        if !records_dependency_edges(env) {
            return;
        }
        if !cls::pos_is_hhi(class_) {
            make_depend_on_class_name(env, &cls::name(class_));
            add_dep(&cls::name(class_));
            if let Some(ce) = class_elt_opt {
                add_dep(&ce.ce_origin)
            }
        }
    }

    pub fn make_depend_on_class_const(env: &Env, class_: &cls::T, name: &str) {
        // (Not in the OCaml: nothing to build when nothing is recorded.)
        if !cls::pos_is_hhi(class_) && records_dependency_edges(env) {
            make_depend_on_class_name(env, &cls::name(class_));
            add_dependency_edge(env, || Dep::Const(cls::name(class_), name.to_string()))
        }
    }

    pub fn make_depend_on_typedef(
        env: &Env,
        name: &str,
        td: &decl_entry::T<decl_provider::TypedefDecl>,
    ) {
        match td {
            decl_entry::T::Found(td) if td.pos.is_hhi() => {}
            _ => make_depend_on_class_name(env, name),
        }
    }
}

/// Expose the subset of Typing_env that is safe to use
/// in tast checks: that is, anything that depends only
/// on the tast and providers (not mutable or visitor state).
///
/// You can use this to avoid the evil Tast_env.tast_env_as_typing_env
pub mod expose_to_tast_env {
    pub use super::consts;
    pub use super::get_class;
    pub use super::get_class_or_typedef;
    pub use super::get_class_or_typedef_tparams;
    pub use super::get_const;
    pub use super::get_construct;
    pub use super::valid_newable_class;
    pub use super::get_enum;
    pub use super::get_fun;
    pub use super::get_gconst;
    pub use super::get_method;
    pub use super::get_parent_class;
    pub use super::get_parent_id;
    pub use super::get_prop;
    pub use super::get_self_class;
    pub use super::get_self_id;
    pub use super::get_self_ty;
    pub use super::get_static_member;
    pub use super::get_tcopt;
    pub use super::get_typeconst;
    pub use super::get_typedef;
    pub use super::inside_expr_tree;
    pub use super::is_enum;
    pub use super::is_enum_class;
    pub use super::is_in_expr_tree;
    pub use super::is_typedef;
    pub use crate::decl_enforceability::ClassOrTypedefResult;
    /// `type env`
    pub use crate::typing_env_types::Env;
}

pub fn show_env(_env: &Env) -> String {
    "<env>".to_string()
}

pub fn pp_env(_fmt: &mut std::fmt::Formatter<'_>, _env: &Env) {
    println!("<env>")
}

/// see .mli
// (A reference: cloning the `Arc`, which all the threads share, at each
// call would write its count from every thread. Callers clone if they keep it.)
pub fn get_tcopt(env: &Env) -> &Arc<TypecheckerOptions> {
    &env.genv.tcopt
}

pub fn map_tcopt(env: &mut Env, f: impl FnOnce(TypecheckerOptions) -> TypecheckerOptions) {
    let tcopt = f(TypecheckerOptions::clone(&env.genv.tcopt));
    Rc::make_mut(&mut env.genv).tcopt = Arc::new(tcopt);
}

pub fn get_deps_mode(env: &Env) -> crate::typing_deps::mode::T {
    crate::provider_context::get_deps_mode(&env.decl_env.ctx)
}

pub fn get_ctx(env: &Env) -> Arc<Ctx> {
    Arc::clone(&env.decl_env.ctx)
}

pub fn get_file(env: &Env) -> Arc<RelativePath> {
    Arc::clone(&env.genv.file)
}

pub fn get_current_decl_and_file(env: &Env) -> pos_or_decl::Ctx {
    pos_or_decl::Ctx {
        file: RelativePath::clone(&env.genv.file),
        decl: deps::get_current_decl(env),
    }
}

/// Check that the position is in the current decl and if it is, resolve
/// it with the current file.
pub fn fill_in_pos_filename_if_in_current_decl(env: &Env, pos: &PosOrDecl) -> Option<Pos> {
    crate::pos_or_decl::fill_in_filename_if_in_current_decl(&get_current_decl_and_file(env), pos)
}

/// This will check that the first position of the given reasons is in the
/// current decl and if yes use it as primary error position. If no,
/// it will error at a default position in the current file and log the failed
/// assertion.
/// This also sets the error code to the code for unification error
/// if none is provided.
pub fn unify_error_assert_primary_pos_in_current_decl(
    env: &Env,
) -> typing_error::reasons_callback::T {
    typing_error::reasons_callback::unify_error_assert_primary_pos_in_current_decl(
        get_current_decl_and_file(env),
    )
}

/// This will check that the first position of the given reasons is in the
/// current decl and if yes use it as primary error position. If no,
/// it will error at a default position in the current file and log the failed
/// assertion.
/// This also sets the error code to the code for invalid type hint error
/// if none is provided.
pub fn invalid_type_hint_assert_primary_pos_in_current_decl(
    env: &Env,
) -> typing_error::reasons_callback::T {
    typing_error::reasons_callback::invalid_type_hint_assert_primary_pos_in_current_decl(
        get_current_decl_and_file(env),
    )
}

pub fn get_tracing_info(env: &Env) -> Option<decl_counters::TracingInfo> {
    env.tracing_info.as_deref().cloned()
}

pub fn set_log_level(env: &mut Env, key: &str, log_level: isize) {
    env.log_levels.insert(key.to_string(), log_level);
}

pub use crate::typing_env_types::get_log_level;

/// Whether `log_env_change_ function_name ~level _ (env, _)` logs.
fn logs_env_change(function_name: &str, level: Option<isize>, env: &Env) -> bool {
    let level = level.unwrap_or(1);
    get_log_level(env, function_name) >= 1 || get_log_level(env, "env") >= level
}

/// `(new_env, res)` is the result of a computation on `old_env`: the
/// difference between the two environments is logged, if the log level asks
/// for it, and `res` is returned.
pub fn log_env_change_<Res>(
    function_name: &str,
    level: Option<isize>,
    old_env: &Env,
    new_env: &Env,
    res: Res,
) -> Res {
    if logs_env_change(function_name, level, new_env) {
        let pos = inf::get_current_pos_from_tyvar_stack(&old_env.inference_env)
            .unwrap_or_else(|| old_env.genv.callable_pos.clone());
        crate::typing_log::log_env_diff(&pos, Some(function_name), old_env, new_env)
    };
    res
}

pub fn log_env_change(name: &str, level: Option<isize>, old_env: &Env, new_env: &Env) {
    log_env_change_(name, level, old_env, new_env, ())
}

/// The `old_env` that `log_env_change name ?level old_env new_env` will
/// need, saved only if that call will log (as in [`with_log_env_change`]):
/// holding a copy of the environment makes its next write copy all its
/// fields. Finish with [`log_env_change_opt`].
pub fn old_env_for_log(name: &str, level: Option<isize>, env: &Env) -> Option<Env> {
    if logs_env_change(name, level, env) {
        Some(env.clone())
    } else {
        None
    }
}

/// `log_env_change name ?level old_env new_env`, for an `old_env` from
/// [`old_env_for_log`].
pub fn log_env_change_opt(name: &str, level: Option<isize>, old_env: Option<Env>, new_env: &Env) {
    if let Some(old_env) = old_env {
        log_env_change(name, level, &old_env, new_env)
    }
}

/// `log_env_change_ function_name ?level env @@ body`, where `body` is a
/// computation on `env`. The log levels are part of the environment, but no
/// `body` this is used with changes them, so whether to log is known before
/// `body` runs, and the environment is only copied when it is needed.
fn with_log_env_change<Res>(
    function_name: &str,
    level: Option<isize>,
    env: &mut Env,
    body: impl FnOnce(&mut Env) -> Res,
) -> Res {
    if logs_env_change(function_name, level, env) {
        let old_env = env.clone();
        let res = body(env);
        log_env_change_(function_name, level, &old_env, env, res)
    } else {
        body(env)
    }
}

pub fn expand_var(env: &mut Env, r: Reason, v: tvid::T) -> Ty {
    expand_var_ref(env, &r, v)
}

/// [`expand_var`] with a borrowed reason.
fn expand_var_ref(env: &mut Env, r: &Reason, v: tvid::T) -> Ty {
    // `Inf.expand_var`. Resolve through a shared borrow first, so that an
    // environment that shares its fields with a copy is duplicated only when
    // a chain of aliases is shortened (the only write of `expand_var`).
    match inf::expand_var_shared_ref(&env.inference_env, r, v) {
        Ok(ty) => ty,
        Err(pending) => inf::expand_var_pending(&mut env.inference_env, r.clone(), v, pending),
    }
}

pub fn rank_of_tvar(env: &Env, tvid: tvid::T) -> isize {
    inf::get_rank(&env.inference_env, tvid)
}

/// Generate a fresh type variable type with optional variance and
/// the given reason information
pub fn fresh_type_reason(
    variance: Option<ast_defs::Variance>,
    env: &mut Env,
    p: Pos,
    r: impl FnOnce(tvid::T) -> Reason,
) -> Ty {
    with_log_env_change("fresh_type_reason", None, env, |env| {
        { let e = &mut **env; inf::fresh_type_reason(
            variance,
            None,
            &mut e.inference_env,
            &mut e.tvar_id_provider,
            p,
            r,
        ) }
    })
}

/// Generate a fresh type variable type with variance not yet recorded
pub fn fresh_type(env: &mut Env, p: Pos) -> Ty {
    with_log_env_change("fresh_type", None, env, |env| {
        { let e = &mut **env; inf::fresh_type(None, &mut e.inference_env, &mut e.tvar_id_provider, p) }
    })
}

/// Generate a fresh type variable type with a specified ranks for use
/// in subtyping of rank-n polymorphic types
pub fn fresh_type_invariant_with_rank(env: &mut Env, rank: isize, p: Pos) -> Ty {
    with_log_env_change("fresh_type_invariant_with_rank", None, env, |env| {
        { let e = &mut **env; inf::fresh_type_invariant_with_rank(
            &mut e.inference_env,
            &mut e.tvar_id_provider,
            rank,
            p,
        ) }
    })
}

/// Generate a fresh type variable type that is assumed to be invariant, so
/// it won't be solved automatically at the end of the scope
pub fn fresh_type_invariant(env: &mut Env, p: Pos) -> Ty {
    with_log_env_change("fresh_type_invariant", None, env, |env| {
        { let e = &mut **env; inf::fresh_type_invariant(&mut e.inference_env, &mut e.tvar_id_provider, p) }
    })
}

/// Generate a fresh type variable to stand for an unknown type in the
/// case of type errors.
pub fn fresh_type_error(env: &mut Env, p: Pos) -> Ty {
    with_log_env_change("fresh_type_error", None, env, |env| {
        let p_ = p.clone();
        { let e = &mut **env; inf::fresh_type_reason(
            Some(ast_defs::Variance::Invariant),
            Some(true),
            &mut e.inference_env,
            &mut e.tvar_id_provider,
            p,
            |tvid| typing_reason::type_variable_error(p_, tvid),
        ) }
    })
}

pub fn fresh_type_error_contravariant(env: &mut Env, p: Pos) -> Ty {
    with_log_env_change("fresh_type_error_contravariant", None, env, |env| {
        let p_ = p.clone();
        { let e = &mut **env; inf::fresh_type_reason(
            Some(ast_defs::Variance::Contravariant),
            Some(true),
            &mut e.inference_env,
            &mut e.tvar_id_provider,
            p,
            |tvid| typing_reason::type_variable_error(p_, tvid),
        ) }
    })
}

pub fn add_subtype_prop(env: &mut Env, prop: typing_logic::SubtypeProp) {
    with_log_env_change("add_subtype_prop", None, env, |env| {
        inf::add_subtype_prop(&mut env.inference_env, prop)
    })
}

fn empty_bounds() -> ty_set::T {
    ty_set::T::default()
}

pub fn tyvar_is_solved(env: &Env, var: tvid::T) -> bool {
    inf::tyvar_is_solved(&env.inference_env, var)
}

pub fn make_tyvar_no_more_occur_in_tyvar(env: &mut Env, v: tvid::T, no_more_in: tvid::T) {
    inf::make_tyvar_no_more_occur_in_tyvar(&mut env.inference_env, v, no_more_in)
}

/// `type simplify_unions = env -> locl_ty -> env * locl_ty`
pub type SimplifyUnions = fn(&mut Env, Ty) -> Ty;

/// What `typing_union.ml` puts in `simplify_unions_ref` when the program is
/// initialised: `Typing_union.simplify_unions`, with its optional arguments
/// left out.
fn typing_union_simplify_unions(env: &mut Env, ty: Ty) -> Ty {
    crate::typing_union::simplify_unions(env, None, None, ty)
}

/// `Typing_union.simplify_unions`, which OCaml can only reach through a
/// reference because `Typing_union` depends on `Typing_env`.
///
/// In OCaml the reference holds a function that fails until the
/// initialisation of the module `Typing_union` sets it, before anything is
/// typechecked. Rust has no module initialisation, so the reference is the
/// value that initialisation gives it; nothing assigns it another, so it is
/// immutable (no lock to take when calling it).
#[allow(non_upper_case_globals)]
pub static simplify_unions_ref: SimplifyUnions = typing_union_simplify_unions;

fn simplify_unions(env: &mut Env, ty: Ty) -> Ty {
    let f: SimplifyUnions = simplify_unions_ref;
    f(env, ty)
}

fn bind(env: &mut Env, v: tvid::T, ty: Ty) {
    inf::bind(&mut env.inference_env, None, v, ty)
}

/// Unions and intersections containing unsolved type variables may remain
/// in an unsimplified form once those type variables get solved.
///
/// For example, consider the union (#1 | int) where #1 is an unsolved type variable.
/// If #1 gets solved to int, then this union will remain in the unsimplified form
/// (int | int) which compromise the robustness of some of our logic and might
/// cause performance issues (by creating big unsimplified unions).
///
/// To solve this problem, we wrap each union and intersection in a type var,
/// so we'd get `#2 -> (#1 | int)` (This is done in Typing_union and
/// Typing_intersection), and register that #1 occurs in #2 in
/// [env.tyvar_occurrences]. Then when #1 gets solved, we simplify #2.
///
/// This function deals with this simplification.
///
/// The simplification is recursive: simplifying a type variable will
/// trigger simplification of its own occurrences.
fn simplify_occurrences(env: &mut Env, v: tvid::T, r: &Reason) {
    fn simplify_occurrences(env: &mut Env, v: tvid::T, r: &Reason, seen_tyvars: &mut TvidSet) {
        let vars = inf::get_tyvar_occurrences_set(&env.inference_env, v);
        for &v_ in vars.iter() {
            // This type variable is now solved and does not contain any unsolved
            // type variable, so we can remove it from its occurrences.
            make_tyvar_no_more_occur_in_tyvar(env, v, v_);
            // Only simplify when the type of v' does not contain any more
            // unsolved type variables.
            if !inf::contains_unsolved_tyvars(&env.inference_env, v_) {
                simplify_type_of_var(env, v_, r, seen_tyvars)
            }
        }
    }
    fn simplify_type_of_var(env: &mut Env, v: tvid::T, r: &Reason, seen_tyvars: &mut TvidSet) {
        if seen_tyvars.contains(&v) {
            // TODO raise exception.
        } else {
            seen_tyvars.insert(v);
            match inf::get_direct_binding(&env.inference_env, v) {
                None => panic!("Can only simplify type of bounded variables"),
                Some(ty) => {
                    // Only simplify the type of variables which are bound directly to a
                    // concrete type to preserve the variable aliasings and save some memory.
                    let is_tvar = matches!(get_node(&ty), Ty_::Tvar(_));
                    match is_tvar {
                        true => {}
                        false => {
                            let ty = simplify_unions(env, ty);
                            // we only call this function when v does not recursively contain unsolved
                            // type variables, so ty here should not contain unsolved type variables and
                            // it is safe to simply bind it without reupdating the type var occurrences.
                            let ty = map_reason(ty, |solution| {
                                typing_reason::solved(v, solution, r.clone())
                            });
                            bind(env, v, ty);
                        }
                    };
                    simplify_occurrences(env, v, r, seen_tyvars)
                }
            }
        }
    }
    if !inf::contains_unsolved_tyvars(&env.inference_env, v) {
        simplify_occurrences(env, v, r, &mut TvidSet::new())
    }
}

/// [add env v ty] addd the solution [ty] of a type variable [v] to the environment.
/// In other words, after calling [add], type variable [v] will
/// be associated to type [ty], and [get_type env r v] will return [(env, ty)].
pub fn add(env: &mut Env, tyvar_pos: Option<Pos>, v: tvid::T, ty: Ty) {
    let tyvar_pos = tyvar_pos.unwrap_or(Pos::NONE);
    let r = get_reason(&ty).clone();
    inf::add(&mut env.inference_env, Some(tyvar_pos), v, ty);
    simplify_occurrences(env, v, &r);
}

pub fn get_type(env: &mut Env, r: Reason, var: tvid::T) -> Ty {
    // `Inf.get_type`, resolved through a shared borrow first (see
    // `expand_var`).
    match inf::get_type_shared(&env.inference_env, r, var) {
        Ok(ty) => ty,
        Err(pending) => inf::apply_shortening(&mut env.inference_env, pending),
    }
}

/// If the provided type is a type variable, expand it.
pub fn expand_type(env: &mut Env, ty: Ty) -> Ty {
    match get_node(&ty) {
        Ty_::Tvar(tvid) => {
            let tvid = *tvid;
            expand_var_ref(env, get_reason(&ty), tvid)
        }
        _ => ty,
    }
}

pub fn expand_internal_type(env: &mut Env, ty: InternalType) -> InternalType {
    match ty {
        InternalType::LoclType(ty) => {
            let ty = expand_type(env, ty);
            InternalType::LoclType(ty)
        }
        _ => ty,
    }
}

pub fn get_tyvar_pos(env: &Env, var: tvid::T) -> Pos {
    inf::get_tyvar_pos(&env.inference_env, var)
}

pub fn get_tyvar_lower_bounds(env: &Env, var: tvid::T) -> ITySet {
    inf::get_tyvar_lower_bounds(&env.inference_env, var)
}

pub fn set_tyvar_lower_bounds(env: &mut Env, var: tvid::T, tys: ITySet) {
    inf::set_tyvar_lower_bounds(&mut env.inference_env, var, tys)
}

pub fn get_tyvar_upper_bounds(env: &Env, var: tvid::T) -> ITySet {
    inf::get_tyvar_upper_bounds(&env.inference_env, var)
}

pub fn is_shadow_tyvar(env: &Env, var: tvid::T) -> bool {
    inf::is_shadow(&env.inference_env, var)
}

pub fn fresh_shadow_tyvar(env: &mut Env, pos: Pos) -> tvid::T {
    { let e = &mut **env; inf::fresh_shadow_tyvar(
        &mut e.inference_env,
        &mut e.tvar_id_provider,
        None,
        pos,
    ) }
}

pub fn set_tyvar_upper_bounds(env: &mut Env, var: tvid::T, tys: ITySet) {
    inf::set_tyvar_upper_bounds(&mut env.inference_env, var, tys)
}

pub fn get_tyvar_appears_covariantly(env: &Env, var: tvid::T) -> bool {
    inf::get_tyvar_appears_covariantly(&env.inference_env, var)
}

pub fn get_tyvar_appears_contravariantly(env: &Env, var: tvid::T) -> bool {
    inf::get_tyvar_appears_contravariantly(&env.inference_env, var)
}

pub fn get_tyvar_appears_invariantly(env: &Env, var: tvid::T) -> bool {
    inf::get_tyvar_appears_invariantly(&env.inference_env, var)
}

pub fn get_tyvar_eager_solve_fail(env: &Env, var: tvid::T) -> bool {
    inf::get_tyvar_eager_solve_fail(&env.inference_env, var)
}

pub fn set_tyvar_eager_solve_fail(env: &mut Env, var: tvid::T) {
    inf::set_tyvar_eager_solve_fail(&mut env.inference_env, var)
}

pub fn get_tyvar_type_consts(env: &Env, var: tvid::T) -> im::OrdMap<String, (PosId, Ty)> {
    inf::get_tyvar_type_consts(&env.inference_env, var)
}

pub fn get_tyvar_type_const(env: &Env, var: tvid::T, tid: &PosId) -> Option<(PosId, Ty)> {
    inf::get_tyvar_type_const(&env.inference_env, var, tid)
}

pub fn set_tyvar_type_const(env: &mut Env, var: tvid::T, tconstid: PosId, ty: Ty) {
    inf::set_tyvar_type_const(&mut env.inference_env, var, tconstid, ty)
}

/// What type variables are fresh in the current scope?
pub fn get_current_tyvars(env: &Env) -> Vec<tvid::T> {
    inf::get_current_tyvars(&env.inference_env)
}

/// Open a new "type variable" scope and record this in the environment.
/// Within this scope, you can
/// - generate fresh type variables, using [fresh_type_X] functions
/// - query the currently fresh type variables, using [get_current_tyvars]
/// - close the scope
///
/// The usual usage pattern within type inference is:
///
/// 1. Open a type variable scope using [open_tyvars] before checking an AST node.
///
/// 2. Check the AST node; generate fresh type variables as necessary; make calls
///   to subtyping functions such as [Typing_ops.sub_type] that will record constraints
///   on those type variables.
///
/// 3. Call [set_tyvar_variance] on the type of the expression to correctly set the
///   variance of the type variables.
///
/// 4. Call [Typing_solver.close_tyvars_and_solve] to solve type variables that can
///   be solved immediately, and close the type variable scope.
pub fn open_tyvars(env: &mut Env, p: Pos) {
    inf::open_tyvars(&mut env.inference_env, p)
}

/// Propagate the position for better error reporting.
/// Returns a `restore_pos` function.
/// Call the `restore_pos` function at the end
/// of the scope in cases where you're not throwing
/// the `env` away.
pub fn set_inference_env_pos(env: &mut Env, pos: Option<Pos>) -> Box<dyn Fn(&mut Env)> {
    // `Inf.set_pos`. Writing the position the environment already has (the
    // common case) changes nothing, and is skipped: a write through an
    // environment that shares its fields with a copy copies them all.
    let old_pos = inf::get_pos_ref(&env.inference_env).clone();
    if old_pos != pos {
        let _ = inf::set_pos(&mut env.inference_env, pos);
    }
    Box::new(move |env: &mut Env| {
        if *inf::get_pos_ref(&env.inference_env) != old_pos {
            let _ = inf::set_pos(&mut env.inference_env, old_pos.clone());
        }
    })
}

/// Close the current type variable scope.
/// You might want to call [Typing_solver.close_tyvars_and_solve] instead.
pub fn close_tyvars(env: &mut Env) {
    inf::close_tyvars(&mut env.inference_env)
}

pub fn wrap_ty_in_var(env: &mut Env, r: Reason, ty: Ty) -> Ty {
    { let e = &mut **env; inf::wrap_ty_in_var(&mut e.inference_env, &mut e.tvar_id_provider, r, ty) }
}

pub use crate::typing_env_types::next_cont_opt;

pub fn all_continuations(env: &Env) -> Vec<c::T> {
    lenvc::all_continuations(&env.lenv.per_cont_env)
}

pub use crate::typing_env_types::get_tpenv;

pub fn get_global_tpenv(env: &Env) -> tp_env::T {
    env.tpenv.clone()
}

pub use crate::typing_env_types::get_equal_bounds;
pub use crate::typing_env_types::get_lower_bounds;
pub use crate::typing_env_types::get_pos_and_kind_of_generic;
pub use crate::typing_env_types::get_upper_bounds;

pub fn get_reified(env: &Env, name: &str) -> aast::ReifyKind {
    let tpenv = get_tpenv(env);
    let local = tp_env::get_reified(&tpenv, name);
    let global = tp_env::get_reified(&env.tpenv, name);
    match (local, global) {
        (aast::ReifyKind::Reified, _) | (_, aast::ReifyKind::Reified) => aast::ReifyKind::Reified,
        (aast::ReifyKind::SoftReified, _) | (_, aast::ReifyKind::SoftReified) => {
            aast::ReifyKind::SoftReified
        }
        _ => aast::ReifyKind::Erased,
    }
}

pub fn get_enforceable(env: &Env, name: &str) -> bool {
    let tpenv = get_tpenv(env);
    let local = tp_env::get_enforceable(&tpenv, name);
    let global = tp_env::get_enforceable(&env.tpenv, name);
    local || global
}

pub fn get_newable(env: &Env, name: &str) -> bool {
    let tpenv = get_tpenv(env);
    let local = tp_env::get_newable(&tpenv, name);
    let global = tp_env::get_newable(&env.tpenv, name);
    local || global
}

pub fn get_require_dynamic(env: &Env, name: &str) -> bool {
    let tpenv = get_tpenv(env);
    let local = tp_env::get_require_dynamic(&tpenv, name);
    let global = tp_env::get_require_dynamic(&env.tpenv, name);
    local || global
}

/// `{ env with lenv = { env.lenv with per_cont_env = f env.lenv.per_cont_env } }`,
/// without keeping the old map alive while the new one is built.
fn update_per_cont_env(env: &mut Env, f: impl FnOnce(lenvc::T) -> lenvc::T) {
    let per_cont_env = std::mem::take(&mut env.lenv.per_cont_env);
    env.lenv.per_cont_env = f(per_cont_env);
}

pub fn env_with_tpenv(env: &mut Env, tpenv: tp_env::T) {
    update_per_cont_env(env, |per_cont_env| {
        lenvc::update_cont_entry(c::T::Next, per_cont_env, |mut entry| {
            entry.tpenv = tpenv;
            entry
        })
    })
}

pub fn env_with_global_tpenv(env: &mut Env, tpenv: tp_env::T) {
    env.tpenv = tpenv
}

pub fn add_upper_bound_global(env: &mut Env, name: &str, ty: Ty) {
    {
        // The OCaml drops the environment (and the type) that `expand_type`
        // returns: expand in a copy.
        let ety = expand_type(&mut env.clone(), ty.clone());
        if let (r, Ty_::Tgeneric(formal_super)) = deref(&ety) {
            tp_env::add_lower_bound(
                None,
                &mut env.tpenv,
                formal_super,
                mk((r, Ty_::Tgeneric(name.to_string()))),
            )
        }
    }
    tp_env::add_upper_bound(None, &mut env.tpenv, name.to_string(), ty)
}

pub fn add_lower_bound_global(env: &mut Env, name: &str, ty: Ty) {
    {
        // The OCaml drops the environment (and the type) that `expand_type`
        // returns: expand in a copy.
        let ety = expand_type(&mut env.clone(), ty.clone());
        if let (r, Ty_::Tgeneric(formal_super)) = deref(&ety) {
            tp_env::add_upper_bound(
                None,
                &mut env.tpenv,
                formal_super,
                mk((r, Ty_::Tgeneric(name.to_string()))),
            )
        }
    }
    tp_env::add_lower_bound(None, &mut env.tpenv, name.to_string(), ty)
}

/// Add a single new upper bound [ty] to generic parameter [name] in the local
/// type parameter environment of [env].
/// If the optional [intersect] operation is supplied, then use this to avoid
/// adding redundant bounds by merging the type with existing bounds. This makes
/// sense because a conjunction of upper bounds
///   (T <: t1) /\ ... /\ (T <: tn)
/// is equivalent to a single upper bound
///   T <: (t1 & ... & tn)
pub fn add_upper_bound(
    intersect: Option<&mut dyn FnMut(Ty, &[Ty]) -> Vec<Ty>>,
    env: &mut Env,
    name: &str,
    ty: Ty,
) {
    let mut tpenv = get_tpenv(env);
    tp_env::add_upper_bound(intersect, &mut tpenv, name.to_string(), ty);
    env_with_tpenv(env, tpenv)
}

/// Add a single new upper lower [ty] to generic parameter [name] in the
/// local type parameter environment [env].
/// If the optional [union] operation is supplied, then use this to avoid
/// adding redundant bounds by merging the type with existing bounds. This makes
/// sense because a conjunction of lower bounds
///   (t1 <: T) /\ ... /\ (tn <: T)
/// is equivalent to a single lower bound
///   (t1 | ... | tn) <: T
pub fn add_lower_bound(
    union: Option<&mut dyn FnMut(Ty, &[Ty]) -> Vec<Ty>>,
    env: &mut Env,
    name: &str,
    ty: Ty,
) {
    let mut tpenv = get_tpenv(env);
    tp_env::add_lower_bound(union, &mut tpenv, name.to_string(), ty);
    env_with_tpenv(env, tpenv)
}

/// Add type parameters to environment, initially with no bounds.
/// Existing type parameters with the same name will be overridden.
pub fn add_generic_parameters(env: &mut Env, tparaml: &[DeclTparam]) {
    let mut tpenv = get_tpenv(env);
    tp_env::add_generic_parameters(&mut tpenv, tparaml);
    env_with_tpenv(env, tpenv)
}

/// Add type parameters to environment with their bounds.
/// Existing type parameters with the same name will be overridden.
pub fn add_generic_parameters_with_bounds(env: &mut Env, tparams: &[LoclTparam]) {
    let mut tpenv = get_tpenv(env);
    tp_env::add_generic_parameters_with_bounds(&mut tpenv, tparams);
    env_with_tpenv(env, tpenv)
}

/// In OCaml the type parameters can be of either phase (`_ tparam list`);
/// `type_parameter_env::unbind_generic_parameters` takes localized ones.
pub fn unbind_generic_parameters(env: &mut Env, tparams: &[LoclTparam]) {
    let mut tpenv = get_tpenv(env);
    tp_env::unbind_generic_parameters(&mut tpenv, tparams);
    env_with_tpenv(env, tpenv)
}

pub fn is_generic_parameter(env: &Env, name: &str) -> bool {
    tp_env::mem(name, &get_tpenv(env)) || env.fresh_typarams.contains(name)
}

pub fn get_generic_parameters(env: &Env) -> Vec<String> {
    tp_env::get_tparam_names(&tp_env::union(&get_tpenv(env), &env.tpenv))
}

pub fn get_tpenv_size(env: &Env) -> isize {
    tp_env::size(&get_tpenv(env)) + tp_env::size(&env.tpenv)
}

pub fn is_consistent(env: &Env) -> bool {
    tp_env::is_consistent(&get_tpenv(env))
}

pub fn mark_inconsistent(env: &mut Env) {
    let mut tpenv = get_tpenv(env);
    tp_env::mark_inconsistent(&mut tpenv);
    env_with_tpenv(env, tpenv)
}

pub fn fresh_param_name(env: &mut Env, prefix: &str) -> String {
    use std::fmt::Write as _;
    let mut i = 1;
    // (One buffer for all the probes `prefix#1`, `prefix#2`, ...)
    let mut name = String::with_capacity(prefix.len() + 4);
    let name = loop {
        name.clear();
        let _ = write!(name, "{}#{}", prefix, i);
        if is_generic_parameter(env, &name) {
            i += 1
        } else {
            break name;
        }
    };
    env.fresh_typarams.insert(name.clone());
    name
}

/// Generate a fresh generic parameter with a specified prefix but distinct
/// from all generic parameters in the environment
pub fn add_fresh_generic_parameter_by_kind(
    env: &mut Env,
    pos: PosOrDecl,
    prefix: &str,
    kind: k_defs::Kind,
) -> String {
    let name = fresh_param_name(env, prefix);
    let mut tpenv = get_tpenv(env);
    tp_env::add(pos, name.clone(), kind, &mut tpenv);
    env_with_tpenv(env, tpenv);
    name
}

pub fn add_fresh_generic_parameter(
    env: &mut Env,
    pos: PosOrDecl,
    prefix: &str,
    reified: aast::ReifyKind,
    enforceable: bool,
    newable: bool,
) -> String {
    let kind = k_defs::Kind {
        lower_bounds: empty_bounds(),
        upper_bounds: empty_bounds(),
        reified,
        enforceable,
        newable,
        require_dynamic: true,
        rank: 0,
    };
    add_fresh_generic_parameter_by_kind(env, pos, prefix, kind)
}

pub fn is_fresh_generic_parameter(name: &str) -> bool {
    name.contains('#') && !typing_defs::dependent_kind::is_generic_dep_ty(name)
}

use crate::typing_env_types::get_tparams_in_ty_and_acc;

pub fn get_tparams(env: &Env, ty: &Ty) -> SSet {
    get_tparams_in_ty_and_acc(env, SSet::new(), ty)
}

pub fn get_tpenv_tparams(env: &Env) -> SSet {
    tp_env::fold(
        |_x, kind: &k_defs::Kind, acc: SSet| {
            let folder = |ty: &Ty, acc: SSet| {
                // The OCaml drops the environment that `expand_type` returns:
                // expand in a copy.
                let ty = expand_type(&mut env.clone(), ty.clone());
                match get_node(&ty) {
                    Ty_::Tgeneric(_) => acc,
                    _ => get_tparams_in_ty_and_acc(env, acc, &ty),
                }
            };
            let mut acc = acc;
            for ty in kind.upper_bounds.iter() {
                acc = folder(ty, acc)
            }
            for ty in kind.lower_bounds.iter() {
                acc = folder(ty, acc)
            }
            acc
        },
        &get_tpenv(env),
        SSet::new(),
    )
}

/// Replace types for locals with empty environment
pub fn env_with_locals(env: &mut Env, locals: lenvc::T) {
    env.lenv.per_cont_env = locals
}

/// This is used whenever we start checking a method. Retain tpenv from the class type parameters
pub fn reinitialize_locals(env: &mut Env) {
    let locals = lenvc::initial_locals(lenvc::PerContEntry {
        tpenv: get_tpenv(env),
        ..lenvc::empty_entry()
    });
    env_with_locals(env, locals)
}

pub fn set_env_callable_pos(env: &mut Env, callable_pos: Pos) {
    Rc::make_mut(&mut env.genv).callable_pos = callable_pos
}

pub fn set_env_function_pos(env: &mut Env, function_pos: Pos) {
    Rc::make_mut(&mut env.genv).function_pos = function_pos
}

pub fn set_fun_tast_info(env: &mut Env, fun_tast_info: tast::FunTastInfo) {
    env.fun_tast_info = Some(fun_tast_info)
}

pub fn fun_is_constructor(env: &Env) -> bool {
    env.genv.fun_is_ctor
}

pub fn set_fun_is_constructor(env: &mut Env, is_ctor: bool) {
    Rc::make_mut(&mut env.genv).fun_is_ctor = is_ctor
}

pub fn env_with_method_droot_member(env: &mut Env, m: &str, static_: bool) {
    let child = if static_ {
        typing_pessimisation_deps::DependentMember::SMethod(m.to_string())
    } else {
        typing_pessimisation_deps::DependentMember::Method(m.to_string())
    };
    Rc::make_mut(&mut env.decl_env).droot_member = Some(child)
}

pub fn env_with_constructor_droot_member(env: &mut Env) {
    let member = typing_pessimisation_deps::DependentMember::Constructor;
    Rc::make_mut(&mut env.decl_env).droot_member = Some(member)
}

pub fn get_module(env: &Env, name: &str) -> Option<decl_provider::ModuleDecl> {
    let res = decl_provider::get_module(env.tracing_info.as_deref(), &env.decl_env.ctx, name);
    deps::make_depend_on_module(env, name, res.as_ref());
    res
}

pub fn set_current_module(env: &mut Env, m: Option<ast_defs::Id>) {
    Rc::make_mut(&mut env.genv).current_module = m
}

pub fn get_current_module(env: &Env) -> Option<String> {
    env.genv.current_module.as_ref().map(|id| id.1.clone())
}

pub fn get_current_package(env: &Env) -> Option<package::Package> {
    let current_pkg_name = env
        .genv
        .current_package
        .as_ref()
        .map(crate::aast_utils::get_package_name);
    // `Typechecker_options.package_info`
    let info = &env.genv.tcopt.po.package_info;
    current_pkg_name.and_then(|name| crate::package_info::get_package(info, &name))
}

pub fn get_current_package_def_pos(env: &Env) -> Option<Pos> {
    let current_pkg_name = env
        .genv
        .current_package
        .as_ref()
        .map(crate::aast_utils::get_package_name);
    // `Typechecker_options.package_info`
    let info = &env.genv.tcopt.po.package_info;
    current_pkg_name.and_then(|p| {
        crate::package_info::get_package(info, &p).map(|pkg| crate::package::get_package_pos(&pkg))
    })
}

pub fn get_current_package_membership(env: &Env) -> Option<aast::PackageMembership> {
    env.genv.current_package.clone()
}

pub fn set_current_package_membership(env: &mut Env, package: Option<aast::PackageMembership>) {
    Rc::make_mut(&mut env.genv).current_package = package
}

pub fn get_soft_package_requirement(env: &Env) -> Option<ast_defs::Id> {
    env.genv.soft_package_requirement.clone()
}

/// Register the current top-level structure as being dependent on the current
/// module
pub fn make_depend_on_current_module(env: &Env) {
    if let Some(ast_defs::Id(_, mid)) = &env.genv.current_module {
        deps::make_depend_on_module_name(env, mid)
    }
}

pub fn set_internal(env: &mut Env, b: bool) {
    Rc::make_mut(&mut env.genv).this_internal = b
}

pub fn get_internal(env: &Env) -> bool {
    env.genv.this_internal
}

pub fn get_package_by_name(env: &Env, pkg_name: &str) -> Option<package::Package> {
    // `Typechecker_options.package_info`
    let info = &env.genv.tcopt.po.package_info;
    crate::package_info::get_package(info, pkg_name)
}

/// True if package can be assumed to be loaded
pub fn is_package_loaded(env: &Env, package: &str) -> bool {
    use typing_local_packages::LocalPackageRequirement;
    let per_cont_env = &env.lenv.per_cont_env;
    match per_cont_env.get(&c::T::Next) {
        None => false,
        Some(next_cont) => match next_cont.loaded_packages.get(package) {
            None => false,
            Some(info) => match info.status {
                LocalPackageRequirement::Not_exists_in_deployment => false,
                LocalPackageRequirement::Exists_in_deployment
                | LocalPackageRequirement::Unsatisfiable_package_constraints => {
                    // this is dead code due to unsatisfiable package checks; returning
                    // true to not emit additional errors
                    true
                }
            },
        },
    }
}

/// Get list of all packages assumed to be loaded in the current environment,
/// along with the position where they were loaded (RequirePackage or if package)
pub fn get_loaded_packages_list(env: &Env) -> Vec<package::PosId> {
    use typing_local_packages::LocalPackageRequirement;
    let per_cont_env = &env.lenv.per_cont_env;
    match per_cont_env.get(&c::T::Next) {
        None => vec![],
        Some(next_cont) => {
            let mut acc: Vec<package::PosId> = vec![];
            let loaded_packages: &typing_local_packages::T = &next_cont.loaded_packages;
            for (pkg, info) in loaded_packages.iter() {
                let (pkg, info): (&String, &typing_local_packages::LoadedPackageInfo) = (pkg, info);
                match info.status {
                    LocalPackageRequirement::Exists_in_deployment => {
                        if info.from_includes {
                        } else {
                            acc.push(package::PosId(info.pos.clone(), pkg.clone()))
                        }
                    }
                    LocalPackageRequirement::Not_exists_in_deployment
                    | LocalPackageRequirement::Unsatisfiable_package_constraints => {}
                }
            }
            // `S_map.fold` conses each package onto the list: the packages
            // come out in decreasing order.
            acc.reverse();
            acc
        }
    }
}

/// For error messages.  Computes the list of included packages from both
/// the current package and any loaded packages.
pub fn get_included_packages(env: &Env) -> Vec<(String, String, Pos)> {
    let current_pkg_includes: Vec<(String, String, Pos)> = match get_current_package(env) {
        None => vec![],
        Some(pkg) => {
            let current_pkg_name = &pkg.name.1;
            pkg.includes
                .iter()
                .map(|package::PosId(include_pos, included_name)| {
                    (
                        current_pkg_name.clone(),
                        included_name.clone(),
                        include_pos.clone(),
                    )
                })
                .collect()
        }
    };
    let loaded_packages = get_loaded_packages_list(env);
    let loaded_pkg_includes = loaded_packages
        .iter()
        .flat_map(|package::PosId(_, loaded_pkg_name)| -> Vec<(String, String, Pos)> {
            match get_package_by_name(env, loaded_pkg_name) {
                None => vec![],
                Some(pkg) => pkg
                    .includes
                    .iter()
                    .map(|package::PosId(include_pos, included_name)| {
                        (
                            loaded_pkg_name.clone(),
                            included_name.clone(),
                            include_pos.clone(),
                        )
                    })
                    .collect(),
            }
        });
    current_pkg_includes
        .into_iter()
        .chain(loaded_pkg_includes)
        .collect()
}

pub fn package_allow_classconst_violations(env: &Env) -> bool {
    env.genv.tcopt.tco_package_allow_classconst_violations
}

pub fn package_allow_all_tconst_violations(env: &Env) -> bool {
    env.genv.tcopt.tco_package_allow_all_tconst_violations
}

pub fn package_allow_enforceable_enum_violations(env: &Env) -> bool {
    env.genv.tcopt.tco_package_allow_enforceable_enum_violations
}

/// Add the packages in a RequirePackage attribute to the packages assumed
/// to be loaded
pub fn assert_packages_loaded_from_attr<Ex, En>(
    env: &mut Env,
    attr: &[aast::UserAttribute<Ex, En>],
) {
    if let Some(attr) =
        crate::naming_attributes::find(sn::user_attributes::REQUIRE_PACKAGE, attr)
    {
        let pos = &attr.name.0;
        let tcopt = Arc::clone(get_tcopt(env));
        // `Typechecker_options.package_info`
        let package_info = &tcopt.po.package_info;
        update_per_cont_env(env, |per_cont_env| {
            attr.params
                .iter()
                .fold(per_cont_env, |per_cont_env, param| match param {
                    aast::Expr(_, _, aast::Expr_::String(pkg)) => {
                        lenvc::assert_package_loaded_in_cont(
                            package_info,
                            c::T::Next,
                            pos.clone(),
                            pkg.to_string(),
                            typing_local_packages::LocalPackageRequirement::Exists_in_deployment,
                            per_cont_env,
                        )
                    }
                    _ => per_cont_env,
                })
        })
    }
}

pub fn set_soft_package_from_attr(env: &mut Env, attr: &[nast::UserAttribute]) {
    if let Some(attr) =
        crate::naming_attributes::find(sn::user_attributes::SOFT_REQUIRE_PACKAGE, attr)
    {
        if let [aast::Expr(_, _, aast::Expr_::String(pkg_name))] = attr.params.as_slice() {
            let pos = attr.name.0.clone();
            Rc::make_mut(&mut env.genv).soft_package_requirement =
                Some(ast_defs::Id(pos, pkg_name.to_string()));
        }
    }
}

/// Get type alias declaration from the appropriate backend and add dependency.
pub fn get_typedef(env: &Env, x: &str) -> decl_entry::T<decl_provider::TypedefDecl> {
    let td = decl_provider::get_typedef(env.tracing_info.as_deref(), &env.decl_env.ctx, x);
    deps::make_depend_on_typedef(env, x, &td);
    td
}

pub fn is_typedef(env: &Env, x: &str) -> bool {
    if is_generic_parameter(env, x) {
        false
    } else {
        match crate::naming_provider::get_type_kind(&env.decl_env.ctx, x) {
            Some(naming_types::KindOfType::TTypedef) => true,
            _ => false,
        }
    }
}

pub fn should_expand_type_alias(
    env: &Env,
    visibility_behavior: &typing_defs::VisibilityBehavior,
    name: &str,
    td: &ty::decl::ty::TypedefType<R>,
) -> bool {
    use ty::decl::ty::TypedefTypeAssignment;
    use typing_defs::VisibilityBehavior;
    match &td.type_assignment {
        TypedefTypeAssignment::CaseType(..) => match visibility_behavior {
            VisibilityBehavior::AlwaysExpandNewtype => true,
            VisibilityBehavior::ResolveTypeStructure(None) => false,
            VisibilityBehavior::ResolveTypeStructure(Some(t)) => t != name,
            VisibilityBehavior::ExpandVisibleNewtypeOnly
            | VisibilityBehavior::NeverExpandNewtype => false,
        },
        TypedefTypeAssignment::SimpleTypeDef(td_vis, _td_type) => {
            let td_module = &td.module;
            match td_vis {
                aast::TypedefVisibility::Opaque => match visibility_behavior {
                    VisibilityBehavior::ResolveTypeStructure(_)
                    | VisibilityBehavior::AlwaysExpandNewtype => true,
                    VisibilityBehavior::NeverExpandNewtype => false,
                    VisibilityBehavior::ExpandVisibleNewtypeOnly => {
                        // `match get_typedef_path ctx name with Some s ->
                        // Relative_path.equal s (get_file env) | None -> false`
                        // (None: not the right place to raise an error).
                        crate::naming_provider::typedef_path_is(
                            &env.decl_env.ctx,
                            name,
                            &env.genv.file,
                        )
                    }
                },
                aast::TypedefVisibility::OpaqueModule => match visibility_behavior {
                    VisibilityBehavior::ResolveTypeStructure(_)
                    | VisibilityBehavior::AlwaysExpandNewtype => true,
                    VisibilityBehavior::NeverExpandNewtype => false,
                    VisibilityBehavior::ExpandVisibleNewtypeOnly => {
                        get_current_module(env)
                            == td_module.as_ref().map(|m| m.id_ref().as_str().to_string())
                    }
                },
                aast::TypedefVisibility::Transparent => true,
            }
        }
    }
}

pub fn is_typedef_visible(env: &Env, name: &str, td: &ty::decl::ty::TypedefType<R>) -> bool {
    should_expand_type_alias(
        env,
        &typing_defs::default_visibility_behaviour(),
        name,
        td,
    )
}

/// Get class declaration from the appropriate backend and add dependency.
pub fn get_class(env: &Env, name: &str) -> decl_entry::T<cls::T> {
    let res = decl_provider::get_class(env.tracing_info.as_deref(), &env.decl_env.ctx, name);
    deps::make_depend_on_class(env, name, &res);
    res
}

fn get_parent(env: &Env, skip_constructor_dep: bool, name: &str) -> decl_entry::T<cls::T> {
    let res = get_class(env, name);
    deps::make_depend_on_parent(env, skip_constructor_dep, name, &res);
    res
}

pub fn add_parent_dep(env: &Env, skip_constructor_dep: bool, name: &str) {
    let _ = get_parent(env, skip_constructor_dep, name);
}

pub fn get_class_or_typedef(env: &Env, x: &str) -> decl_entry::T<ClassOrTypedefResult<cls::T>> {
    if is_typedef(env, x) {
        decl_entry::map(get_typedef(env, x), |td| {
            ClassOrTypedefResult::TypedefResult(td)
        })
    } else {
        decl_entry::map(get_class(env, x), |cd| ClassOrTypedefResult::ClassResult(cd))
    }
}

/// The type parameters of a class or typedef (`get_class_or_typedef_tparams`),
/// shared with its declaration instead of copied: a slice through `Deref`.
pub enum DeclTparams {
    NotFound,
    Class(cls::T),
    Typedef(decl_provider::TypedefDecl),
}

impl std::ops::Deref for DeclTparams {
    type Target = [DeclTparam];
    fn deref(&self) -> &[DeclTparam] {
        match self {
            DeclTparams::NotFound => &[],
            DeclTparams::Class(cls::T(_, cls::typing_class_types::ClassT(c, _), _)) => &c.tparams,
            DeclTparams::Typedef(td) => &td.tparams,
        }
    }
}

pub fn get_class_or_typedef_tparams(env: &Env, x: &str) -> DeclTparams {
    match get_class_or_typedef(env, x) {
        decl_entry::T::Found(ClassOrTypedefResult::TypedefResult(td)) => DeclTparams::Typedef(td),
        decl_entry::T::Found(ClassOrTypedefResult::ClassResult(cls)) => {
            // `Cls.tparams cls`, without the copy (what it counts is counted).
            let cls::T(decl, _, _) = &cls;
            cls::decl_counters::count_subdecl(
                decl.as_ref(),
                cls::decl_counters::SubdeclKind::Tparams,
                || (),
            );
            DeclTparams::Class(cls)
        }
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => DeclTparams::NotFound,
    }
}

/// Get function declaration from the appropriate backend and add dependency.
pub fn get_fun(env: &Env, x: &str) -> decl_entry::T<decl_provider::FunDecl> {
    let res = decl_provider::get_fun(env.tracing_info.as_deref(), &env.decl_env.ctx, x);
    deps::make_depend_on_fun(env, x, &res);
    res
}

pub fn get_enum_constraint(env: &Env, x: &str) -> decl_entry::T<Option<DeclTy>> {
    decl_entry::bind(get_class(env, x), |tc| match cls::enum_type(&tc) {
        None => decl_entry::T::DoesNotExist,
        Some(e) => decl_entry::T::Found(e.constraint),
    })
}

// TODO: do we want to introduce a Cls.enum_class_type ?

/// see .mli
pub fn get_enum(env: &Env, x: &str) -> decl_entry::T<cls::T> {
    decl_entry::bind(get_class(env, x), |tc| {
        if cls::enum_type(&tc).is_some() {
            decl_entry::T::Found(tc)
        } else {
            decl_entry::T::DoesNotExist
        }
    })
}

pub fn is_enum(env: &Env, x: &str) -> bool {
    match get_enum(env, x) {
        // `Ast_defs.is_c_enum`
        decl_entry::T::Found(cls) => matches!(cls::kind(&cls), ClassishKind::Cenum),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
    }
}

/// see .mli
pub fn is_enum_class(env: &Env, x: &str) -> bool {
    match get_enum(env, x) {
        // `Ast_defs.is_c_enum_class`
        decl_entry::T::Found(cls) => matches!(cls::kind(&cls), ClassishKind::CenumClass(_)),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
    }
}

/// Get type constant declaration from the appropriate backend and add dependency.
pub fn get_typeconst(env: &Env, class_: &cls::T, mid: &str) -> Option<ty::decl::TypeConst<R>> {
    deps::make_depend_on_class_const(env, class_, mid);
    cls::get_typeconst(class_, mid)
}

// Used to access class constants.

/// Get class constant declaration from the appropriate backend and add dependency.
pub fn get_const(env: &Env, class_: &cls::T, mid: &str) -> Option<ty::decl::ClassConst<R>> {
    deps::make_depend_on_class_const(env, class_, mid);
    cls::get_const(class_, mid)
}

/// Get class constants declaration from the appropriate backend and add dependency.
pub fn consts(env: &Env, class_: &cls::T) -> Vec<(String, ty::decl::ClassConst<R>)> {
    deps::make_depend_on_class(
        env,
        &cls::name(class_),
        &decl_entry::T::Found(class_.clone()),
    );
    cls::consts(class_)
}

/// Used to access "global constants". That is constants that were
/// introduced with "const X = ...;" at topelevel, or "define('X', ...);"
pub fn get_gconst(env: &Env, cst_name: &str) -> Option<decl_provider::GconstDecl> {
    let res = decl_provider::get_gconst(env.tracing_info.as_deref(), &env.decl_env.ctx, cst_name);
    deps::make_depend_on_gconst(env, cst_name, res.as_ref());
    res
}

/// Get static member declaration of a class from the appropriate backend and add dependency.
pub fn get_static_member(
    is_method: bool,
    env: &Env,
    class_: &cls::T,
    mid: &str,
) -> Option<ClassElt> {
    // The type of a member is stored separately in the heap. This means that
    // any user of the member also has a dependency on the class where the member
    // originated.
    let ce_opt = if is_method {
        cls::get_smethod(class_, mid)
    } else {
        cls::get_sprop(class_, mid)
    };
    deps::add_member_dep(is_method, true, env, class_, mid, ce_opt.as_ref());
    ce_opt
}

/// `suggest_member` of the OCaml, before the function of the `.mli` shadows
/// it.
fn suggest_member_of(members: Vec<(String, ClassElt)>, mid: &str) -> Option<(PosOrDecl, String)> {
    let pairs: Vec<(PosOrDecl, String)> = members
        .into_iter()
        .map(|(x, ce)| {
            // `get_pos ty`, where `ty` is `Lazy.force ce.ce_type`
            (crate::decl_utils::get_pos(&ce.ce_type).to_oxidized(), x)
        })
        .collect();
    crate::string_utils::most_similar(None, mid, &pairs, |pair: &(PosOrDecl, String)| {
        pair.1.clone()
    })
}

pub fn suggest_static_member(
    is_method: bool,
    class_: &cls::T,
    mid: &str,
) -> Option<(PosOrDecl, String)> {
    let mid = mid.to_ascii_lowercase();
    let members = if is_method {
        cls::smethods(class_)
    } else {
        cls::sprops(class_)
    };
    suggest_member_of(members, &mid)
}

/// Get class method declaration from the appropriate backend and add dependency.
pub fn get_method(env: &Env, class_: &cls::T, mid: &str) -> Option<ClassElt> {
    // The type of a member is stored separately in the heap. This means that
    // any user of the member also has a dependency on the class where the member
    // originated.
    let ce_opt = cls::get_method(class_, mid);
    deps::add_member_dep(true, false, env, class_, mid, ce_opt.as_ref());
    ce_opt
}

/// Get class property declaration from the appropriate backend and add dependency.
pub fn get_prop(env: &Env, class_: &cls::T, mid: &str) -> Option<ClassElt> {
    // The type of a member is stored separately in the heap. This means that
    // any user of the member also has a dependency on the class where the member
    // originated.
    let ce_opt = cls::get_prop(class_, mid);
    deps::add_member_dep(false, false, env, class_, mid, ce_opt.as_ref());
    ce_opt
}

pub fn suggest_member(is_method: bool, class_: &cls::T, mid: &str) -> Option<(PosOrDecl, String)> {
    let mid = mid.to_ascii_lowercase();
    let members = if is_method {
        cls::methods(class_)
    } else {
        cls::props(class_)
    };
    suggest_member_of(members, &mid)
}

/// Get class constructor declaration from the appropriate backend and add dependency.
pub fn get_construct(env: &Env, class_: &cls::T) -> (Option<ClassElt>, ConsistentKind) {
    deps::make_depend_on_constructor(env, class_);
    cls::construct(class_)
}

/// Check whether a class is a valid newable bound, recording a constructor
/// dependency when its consistency is inspected.
pub fn valid_newable_class(env: &Env, class_: &cls::T) -> bool {
    if crate::ast_defs::is_c_class(cls::kind(class_)) {
        cls::final_(class_)
            || !matches!(get_construct(env, class_).1, ConsistentKind::Inconsistent)
    } else {
        // There is currently a bug with interfaces that allows constructors to
        // change their signature, so they are not considered here.
        // TODO: T41093452
        false
    }
}

pub fn get_return(env: &Env) -> typing_env_return_info::T {
    env.genv.return_.clone()
}

pub fn set_return(env: &mut Env, x: typing_env_return_info::T) {
    Rc::make_mut(&mut env.genv).return_ = x
}

pub fn get_readonly(env: &Env) -> bool {
    env.genv.readonly
}

pub fn set_readonly(env: &mut Env, x: bool) {
    Rc::make_mut(&mut env.genv).readonly = x
}

pub fn get_params(env: &Env) -> im::OrdMap<LocalId, (Ty, Pos, Option<Ty>)> {
    env.genv.params.clone()
}

fn set_params(env: &mut Env, params: im::OrdMap<LocalId, (Ty, Pos, Option<Ty>)>) {
    Rc::make_mut(&mut env.genv).params = params
}

pub fn set_param(env: &mut Env, x: LocalId, param: (Ty, Pos, Option<Ty>)) {
    Rc::make_mut(&mut env.genv).params.insert(x, param);
}

pub fn clear_params(env: &mut Env) {
    set_params(env, im::OrdMap::new())
}

pub fn with_env<A>(env: &mut Env, f: impl FnOnce(&mut Env) -> A) -> A {
    let ret = get_return(env);
    let params = get_params(env);
    let result = f(env);
    set_params(env, params);
    set_return(env, ret);
    result
}

pub fn with_origin<A>(
    env: &mut Env,
    origin: decl_counters::Origin,
    f: impl FnOnce(&mut Env) -> A,
) -> A {
    // Without tracing information, the environment is not
    // changed: writing `None` over `None` would copy the fields of an
    // environment that shares them with a copy.
    let ti1 = match &env.tracing_info {
        None => return f(env),
        Some(ti1) => Rc::clone(ti1),
    };
    // Writing a value equal to the one there is skipped (each write may copy
    // the fields of an environment shared with a copy).
    if ti1.origin != origin {
        env.tracing_info = Some(Rc::new(decl_counters::TracingInfo {
            origin,
            ..(*ti1).clone()
        }));
    }
    let result = f(env);
    if !matches!(&env.tracing_info, Some(ti) if Rc::ptr_eq(ti, &ti1)) {
        env.tracing_info = Some(ti1);
    }
    result
}

pub fn with_origin2<A, B>(
    env: &mut Env,
    origin: decl_counters::Origin,
    f: impl FnOnce(&mut Env) -> (A, B),
) -> (A, B) {
    // Without tracing information, the environment is not
    // changed: writing `None` over `None` would copy the fields of an
    // environment that shares them with a copy.
    let ti1 = match &env.tracing_info {
        None => return f(env),
        Some(ti1) => Rc::clone(ti1),
    };
    // Writing a value equal to the one there is skipped (each write may copy
    // the fields of an environment shared with a copy).
    if ti1.origin != origin {
        env.tracing_info = Some(Rc::new(decl_counters::TracingInfo {
            origin,
            ..(*ti1).clone()
        }));
    }
    let (r1, r2) = f(env);
    if !matches!(&env.tracing_info, Some(ti) if Rc::ptr_eq(ti, &ti1)) {
        env.tracing_info = Some(ti1);
    }
    (r1, r2)
}

pub fn is_static(env: &Env) -> bool {
    env.genv.static_
}

pub fn get_val_kind(env: &Env) -> ValKind {
    env.genv.val_kind
}

/// see .mli
pub fn get_self_ty(env: &Env) -> Option<Ty> {
    env.genv.self_.as_ref().map(|(_, ty)| ty.clone())
}

pub fn get_self_class_type(env: &Env) -> Option<(PosId, Exact, Vec<Ty>)> {
    match &env.genv.self_ {
        Some((_, self_)) => match get_node(self_) {
            Ty_::Tclass(id, exact, tys) => Some((id.clone(), exact.clone(), tys.clone())),
            _ => None,
        },
        None => None,
    }
}

/// see .mli
pub fn get_self_id(env: &Env) -> Option<String> {
    env.genv.self_.as_ref().map(|(id, _)| id.clone())
}

pub fn get_self_class(env: &Env) -> decl_entry::T<cls::T> {
    let self_ = decl_entry::of_option_or_does_not_exist(get_self_id(env));
    decl_entry::bind(self_, |name| get_class(env, &name))
}

pub fn get_parent_ty(env: &Env) -> Option<DeclTy> {
    env.genv.parent.as_ref().map(|(_, ty)| ty.clone())
}

/// see .mli
pub fn get_parent_id(env: &Env) -> Option<String> {
    env.genv.parent.as_ref().map(|(id, _)| id.clone())
}

pub fn get_parent_class(env: &Env) -> decl_entry::T<cls::T> {
    let self_ = decl_entry::of_option_or_does_not_exist(get_parent_id(env));
    decl_entry::bind(self_, |name| get_class(env, &name))
}

pub fn get_fn_kind(env: &Env) -> ast_defs::FunKind {
    env.genv.fun_kind
}

pub fn set_fn_kind(env: &mut Env, fn_type: ast_defs::FunKind) {
    Rc::make_mut(&mut env.genv).fun_kind = fn_type
}

pub fn set_support_dynamic_type(env: &mut Env, b: bool) {
    Rc::make_mut(&mut env.genv).this_support_dynamic_type = b
}

pub fn set_no_auto_likes(env: &mut Env, b: bool) {
    Rc::make_mut(&mut env.genv).no_auto_likes = b
}

pub fn set_needs_concrete(env: &mut Env, b: bool) {
    Rc::make_mut(&mut env.genv).needs_concrete = b
}

pub fn set_everything_sdt(env: &mut Env, b: bool) {
    map_tcopt(env, |mut tcopt| {
        tcopt.po.everything_sdt = b;
        tcopt
    })
}

pub fn get_support_dynamic_type(env: &Env) -> bool {
    env.genv.this_support_dynamic_type
}

pub fn get_no_auto_likes(env: &Env) -> bool {
    env.genv.no_auto_likes
}

/// Whether `static` bound to exactly this class satisfies `__NeedsConcrete`:
/// the class is non-abstract, or final without an inherited
/// `__ConsistentConstruct`.
pub fn is_concrete_class(env: &Env, class_: &cls::T) -> bool {
    let has_final_class_consistency = || match get_construct(env, class_).1 {
        ConsistentKind::FinalClass => true,
        ConsistentKind::Inconsistent | ConsistentKind::ConsistentConstruct => false,
    };
    !cls::abstract_(class_) || (cls::final_(class_) && has_final_class_consistency())
}

fn containing_class_is_final_and_concrete(env: &Env) -> bool {
    match decl_entry::to_option(get_self_class(env)) {
        Some(class_) => cls::final_(&class_) && is_concrete_class(env, &class_),
        None => false,
    }
}

/// when true, the receiver of `static::foo()` is a concrete class
/// in the sense of [is_concrete_class]
pub fn static_points_to_concrete_class(env: &Env) -> bool {
    // if we're in a __NeedsConcrete method, `static` points to a concrete class
    env.genv.needs_concrete
    // if we're in an instance method or constructor then the class must be instantiable and therefore concrete
        || !is_static(env)
        || containing_class_is_final_and_concrete(env)
}

pub fn set_self(env: &mut Env, self_id: String, self_ty: Ty) {
    Rc::make_mut(&mut env.genv).self_ = Some((self_id, self_ty))
}

/// Run a given function with self unset in the environment.
/// Restore self after the function finishes executing. This is used when
/// checking attributes applied to a class, because the self keyword is not
/// allowed as part of an argument to an attribute
pub fn run_with_no_self<A>(env: &mut Env, f: impl FnOnce(&mut Env) -> A) -> A {
    let self_ = Rc::make_mut(&mut env.genv).self_.take();
    let result = f(env);
    Rc::make_mut(&mut env.genv).self_ = self_;
    result
}

pub fn set_parent(env: &mut Env, parent_id: String, parent_ty: DeclTy) {
    Rc::make_mut(&mut env.genv).parent = Some((parent_id, parent_ty))
}

pub fn set_static(env: &mut Env) {
    Rc::make_mut(&mut env.genv).static_ = true
}

pub fn set_val_kind(env: &mut Env, x: ValKind) {
    Rc::make_mut(&mut env.genv).val_kind = x
}

pub fn set_mode(env: &mut Env, mode: file_info::Mode) {
    Rc::make_mut(&mut env.decl_env).mode = mode
}

pub fn get_mode(env: &Env) -> file_info::Mode {
    env.decl_env.mode
}

pub fn is_strict(env: &Env) -> bool {
    // `File_info.is_strict`
    matches!(get_mode(env), file_info::Mode::Mstrict)
}

pub fn is_hhi(env: &Env) -> bool {
    // `File_info.is_hhi`
    matches!(get_mode(env), file_info::Mode::Mhhi)
}

// ---------------------------------------------------------------------------
// Locals
// ---------------------------------------------------------------------------

pub fn set_local_(env: &mut Env, x: LocalId, ty: Local) {
    update_per_cont_env(env, |per_cont_env| {
        lenvc::add_to_cont(c::T::Next, x, ty, per_cont_env)
    })
}

pub fn make_expression_id(env: &Env) -> expression_id::T {
    expression_id::make(&env.expression_id_provider)
}

/// We maintain 2 states for a local: the type
/// that the local currently has, and an expression_id generated from
/// the last assignment to this local.
pub fn set_local(
    immutable: Option<bool>,
    macro_splice_vars: Option<im::OrdMap<LocalId, (Pos, Ty)>>,
    env: &mut Env,
    x: LocalId,
    new_type: Ty,
    pos: Pos,
) {
    let immutable = immutable.unwrap_or(false);
    let new_type = match get_node(&new_type) {
        Ty_::Tunion(tyl) if tyl.len() == 1 => tyl[0].clone(),
        _ => new_type,
    };
    // `Typechecker_options.tco_dynamic_inference`
    let dynamic_inference = env.genv.tcopt.tco_dynamic_inference;
    // What is read from the next continuation: the expression id of the
    // local and, for dynamic inference, its type if it has a shadow type
    // variable.
    let (prev_eid, prev_shadow_ty) = match env.lenv.per_cont_env.get(&c::T::Next) {
        None => return,
        Some(next_cont) => match next_cont.local_types.get(&x) {
            None => (None, None),
            Some(local) => (
                Some(local.eid.clone()),
                match get_node(&local.ty) {
                    Ty_::Tdynamic(Some(_)) if dynamic_inference => Some(local.ty.clone()),
                    _ => None,
                },
            ),
        },
    };
    let expr_id = match prev_eid {
        None => make_expression_id(env),
        Some(eid) => eid,
    };
    let expr_id = if immutable {
        expression_id::make_immutable(expr_id)
    } else {
        expr_id
    };
    // Dynamic inference: when a local is assigned type `dynamic`, allocate a
    // fresh shadow type variable and attach it via Tdynamic(Some v). The shadow
    // type variable tracks how the local is used by accumulating upper bounds.
    // If the local is re-assigned to a non-dynamic type, we preserve the existing
    // shadow type variable from the previous binding so constraints aren't lost.
    let new_type = match get_node(&new_type) {
        Ty_::Tdynamic(None) if dynamic_inference => {
            // `Local_id.to_string`
            let local_name = local_id::get_name(&x).clone();
            let v = { let e = &mut **env; inf::fresh_shadow_tyvar(
                &mut e.inference_env,
                &mut e.tvar_id_provider,
                Some(local_name),
                pos.clone(),
            ) };
            mk((get_reason(&new_type).clone(), Ty_::Tdynamic(Some(v))))
        }
        Ty_::Tdynamic(Some(_)) => new_type,
        _ => {
            if dynamic_inference {
                match prev_shadow_ty {
                    Some(ty) => ty,
                    None => new_type,
                }
            } else {
                new_type
            }
        }
    };
    let local = Local {
        ty: new_type,
        pos,
        eid: expr_id,
        macro_splice_vars,
    };
    set_local_(env, x, local)
}

pub fn is_using_var(env: &Env, x: &LocalId) -> bool {
    env.lenv.local_using_vars.contains(x)
}

pub fn set_using_var(env: &mut Env, x: LocalId) {
    env.lenv.local_using_vars.insert(x);
}

pub fn unset_local(env: &mut Env, local: &LocalId) {
    update_per_cont_env(env, |per_cont_env| {
        lenvc::remove_from_cont(
            c::T::Next,
            local,
            lenvc::remove_from_cont(c::T::Catch, local, per_cont_env),
        )
    });
    env.lenv.local_using_vars.remove(local);
}

pub fn tany(_env: &Env) -> Ty_ {
    typing_defs::make_tany()
}

fn local_undefined_error(
    env: &Env,
    p: Option<&Pos>,
    x: &LocalId,
    ctx: &lenvc::PerContEntry,
) {
    // A local, its entry and, for the locals outside of an expression tree,
    // the DSL of the tree.
    type Candidate<'a> = (&'a LocalId, &'a Local, Option<&'a aast::ClassName>);
    // When inside an expression tree, the user may forget to splice in a
    // variable. If that happens we want to suggest splicing in that
    // variable.
    fn all_outer_locals(env: &Env) -> Vec<Candidate<'_>> {
        match &env.in_expr_tree {
            None => vec![],
            Some(ExprTreeEnv { outer_locals, dsl }) => {
                let mut locals: Vec<Candidate<'_>> = vec![];
                for (k, v) in outer_locals.iter() {
                    // $this doesn't have a position. In general best to avoid
                    // suggestions that lack positions.
                    if crate::local_id::is_user_denotable(k) && !crate::pos::equal_none(&v.pos) {
                        locals.push((k, v, Some(dsl)))
                    }
                }
                // `LID.Map.fold` conses each local onto the list: they come
                // out in decreasing order.
                locals.reverse();
                locals
            }
        }
    }
    match p {
        Some(p) => {
            // `LID.to_string`
            let lid = local_id::get_name(x).clone();
            // suggest_most_similar: Ignore fake locals
            let mut all_locals: Vec<Candidate<'_>> = vec![];
            for (k, v) in ctx.local_types.iter() {
                if crate::local_id::is_user_denotable(k) {
                    all_locals.push((k, v, None))
                }
            }
            // `LID.Map.fold` conses each local onto the list (they come out
            // in decreasing order), which starts as the locals outside of the
            // expression tree:
            // Prefer suggesting variables within the current scope
            all_locals.reverse();
            all_locals.extend(all_outer_locals(env));
            let var_name = |candidate: &Candidate<'_>| local_id::get_name(candidate.0).clone();
            let (most_similar, in_dsl) =
                match crate::string_utils::most_similar(None, &lid, &all_locals, var_name) {
                    Some((k, local, dsl)) => (
                        Some((local_id::get_name(k).clone(), local.pos.clone())),
                        dsl,
                    ),
                    None => (None, None),
                };
            let error = match in_dsl {
                None => NamingError::Undefined {
                    pos: p.clone(),
                    var_name: lid,
                    did_you_mean: most_similar,
                },
                Some(dsl) => NamingError::UndefinedInExprTree {
                    pos: p.clone(),
                    var_name: lid,
                    dsl: Some(dsl.1.clone()),
                    did_you_mean: most_similar,
                },
            };
            // `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic
            // error custom_err_config)`. The renderer of naming errors of this
            // crate does not take the custom error configuration of the
            // options.
            if let Some(diagnostic) =
                crate::naming_errors::to_diagnostic(NamingPhaseError::Naming(error))
            {
                crate::diagnostics_state::add_diagnostic(diagnostic)
            }
        }
        None => {}
    }
}

/// The local the OCaml makes up for a variable that has none: its type is
/// `nothing`.
fn nothing_local(env: &Env) -> Local {
    Local {
        ty: crate::typing_make_type::nothing(typing_reason::none()),
        pos: Pos::NONE,
        eid: make_expression_id(env),
        macro_splice_vars: None,
    }
}

fn get_local_in_ctx(
    undefined_err_fun: impl FnOnce(&LocalId, &lenvc::PerContEntry),
    env: &Env,
    x: &LocalId,
    ctx_opt: Option<&lenvc::PerContEntry>,
) -> Option<Local> {
    let not_found_is_ok =
        |x: &LocalId, ctx: &lenvc::PerContEntry| fake::is_valid(&ctx.fake_members, x);
    match ctx_opt {
        None => {
            // If the continuation is absent, we are in dead code so the variable should
            // have type nothing.
            Some(nothing_local(env))
        }
        Some(ctx) => {
            let lcl = ctx.local_types.get(x);
            match lcl {
                None => {
                    if not_found_is_ok(x, ctx) {
                    } else {
                        undefined_err_fun(x, ctx)
                    }
                }
                Some(_) => {}
            };
            lcl.cloned()
        }
    }
}

fn get_local_ty_in_ctx(
    undefined_err_fun: impl FnOnce(&LocalId, &lenvc::PerContEntry),
    env: &Env,
    x: &LocalId,
    ctx_opt: Option<&lenvc::PerContEntry>,
) -> (bool, Local) {
    match get_local_in_ctx(undefined_err_fun, env, x, ctx_opt) {
        None => (false, nothing_local(env)),
        Some(local) => (true, local),
    }
}

fn get_local_in_next_continuation(
    error_if_undef_at_pos: Option<&Pos>,
    env: &Env,
    x: &LocalId,
) -> (bool, Local) {
    let p = error_if_undef_at_pos;
    let undefined_err_fun =
        |x: &LocalId, ctx: &lenvc::PerContEntry| local_undefined_error(env, p, x, ctx);
    // `next_cont_opt env`
    let next_cont = env.lenv.per_cont_env.get(&c::T::Next);
    get_local_ty_in_ctx(undefined_err_fun, env, x, next_cont)
}

fn get_local_(error_if_undef_at_pos: Option<&Pos>, env: &Env, x: &LocalId) -> (bool, Local) {
    get_local_in_next_continuation(error_if_undef_at_pos, env, x)
}

pub fn get_local(env: &Env, x: &LocalId) -> Local {
    get_local_(None, env, x).1
}

pub fn get_locals<Ex>(
    quiet: Option<bool>,
    env: &Env,
    plids: &[aast::CaptureLid<Ex>],
) -> typing_local_types::T {
    let quiet = quiet.unwrap_or(false);
    // `next_cont_opt env`
    let next_cont = env.lenv.per_cont_env.get(&c::T::Next);
    let mut locals = typing_local_types::empty();
    for aast::CaptureLid(_, aast::Lid(p, lid)) in plids {
        let error_if_undef_at_pos = if quiet { None } else { Some(p) };
        let undefined_err_fun = |x: &LocalId, ctx: &lenvc::PerContEntry| {
            local_undefined_error(env, error_if_undef_at_pos, x, ctx)
        };
        match get_local_in_ctx(undefined_err_fun, env, lid, next_cont) {
            None => {}
            Some(ty_eid) => {
                locals.insert(lid.clone(), ty_eid);
            }
        }
    }
    locals
}

pub fn set_locals(env: &mut Env, locals: &typing_local_types::T) {
    for (lid, ty) in locals.iter() {
        set_local_(env, lid.clone(), ty.clone())
    }
}

pub fn is_local_defined(env: &Env, x: &LocalId) -> bool {
    let next_cont = env.lenv.per_cont_env.get(&c::T::Next);
    next_cont.is_some() && get_local_(None, env, x).0
}

pub fn get_local_check_defined(env: &Env, lid: &aast::Lid) -> Local {
    let aast::Lid(p, x) = lid;
    get_local_(Some(p), env, x).1
}

/// The environment is updated in both cases: `Error` is the OCaml's
/// `Error (env, err)`.
pub fn set_local_expr_id(
    env: &mut Env,
    x: &LocalId,
    new_eid: expression_id::T,
) -> Result<(), typing_error::T> {
    let local = match env.lenv.per_cont_env.get(&c::T::Next) {
        None => return Ok(()),
        Some(next_cont) => match next_cont.local_types.get(x) {
            Some(local) if !(local.eid == new_eid) => local.clone(),
            _ => return Ok(()),
        },
    };
    let Local {
        ty,
        pos,
        eid,
        macro_splice_vars,
    } = local;
    let local = Local {
        ty,
        pos: pos.clone(),
        eid: new_eid,
        macro_splice_vars,
    };
    update_per_cont_env(env, |per_cont_env| {
        lenvc::add_to_cont(c::T::Next, x.clone(), local, per_cont_env)
    });
    if expression_id::is_immutable(eid) {
        Err(typing_error::primary(
            typing_error::primary::T::Immutable_local(pos),
        ))
    } else {
        Ok(())
    }
}

pub fn get_local_expr_id(env: &Env, x: &LocalId) -> Option<expression_id::T> {
    match env.lenv.per_cont_env.get(&c::T::Next) {
        None => {
            // dead code
            None
        }
        Some(next_cont) => {
            let lcl = next_cont.local_types.get(x);
            lcl.map(|x| x.eid.clone())
        }
    }
}

pub fn set_fake_members(env: &mut Env, fake_members: fake::T) {
    update_per_cont_env(env, |per_cont_env| {
        lenvc::update_cont_entry(c::T::Next, per_cont_env, |mut entry| {
            entry.fake_members = fake_members;
            entry
        })
    })
}

pub fn set_loaded_packages(env: &mut Env, loaded_packages: typing_local_packages::T) {
    update_per_cont_env(env, |per_cont_env| {
        lenvc::update_cont_entry(c::T::Next, per_cont_env, |mut entry| {
            entry.loaded_packages = loaded_packages;
            entry
        })
    })
}

pub fn get_fake_members(env: &Env) -> fake::T {
    match env.lenv.per_cont_env.get(&c::T::Next) {
        None => fake::empty(),
        Some(next_cont) => next_cont.fake_members.clone(),
    }
}

fn update_lost_info(name: &str, blame: &Blame, env: &mut Env, ty: Ty) -> Ty {
    let info = |r: Reason| typing_reason::lost_info((name.to_string(), r, blame.clone()));
    fn update_ty(
        env: &mut Env,
        seen_tyvars: &mut TvidSet,
        info: &dyn Fn(Reason) -> Reason,
        ty: Ty,
    ) -> Ty {
        let ty = expand_type(env, ty);
        match deref(&ty) {
            (_, Ty_::Tvar(v)) => {
                if seen_tyvars.contains(&v) {
                    ty
                } else {
                    seen_tyvars.insert(v);
                    let bs = get_tyvar_lower_bounds(env, v);
                    let ((), bs) = ity_set::fold_map(&bs, (), |(), ty| {
                        ((), update_ty_i(env, seen_tyvars, info, ty))
                    });
                    set_tyvar_lower_bounds(env, v, bs);
                    let bs = get_tyvar_upper_bounds(env, v);
                    let ((), bs) = ity_set::fold_map(&bs, (), |(), ty| {
                        ((), update_ty_i(env, seen_tyvars, info, ty))
                    });
                    set_tyvar_upper_bounds(env, v, bs);
                    ty
                }
            }
            (r, Ty_::Toption(ty)) => {
                let ty = update_ty(env, seen_tyvars, info, ty);
                mk((info(r), Ty_::Toption(ty)))
            }
            (r, Ty_::Tunion(tyl)) => {
                let tyl = tyl
                    .into_iter()
                    .map(|ty| update_ty(env, seen_tyvars, info, ty))
                    .collect();
                mk((info(r), Ty_::Tunion(tyl)))
            }
            _ => map_reason(ty, info),
        }
    }
    fn update_ty_i(
        env: &mut Env,
        seen_tyvars: &mut TvidSet,
        info: &dyn Fn(Reason) -> Reason,
        ty: InternalType,
    ) -> InternalType {
        match ty {
            InternalType::LoclType(ty) => {
                let ty = update_ty(env, seen_tyvars, info, ty);
                InternalType::LoclType(ty)
            }
            InternalType::ConstraintType(ty) => {
                let (r, ty) = deref_constraint_type(&ty);
                InternalType::ConstraintType(mk_constraint_type((info(r), ty)))
            }
        }
    }
    update_ty(env, &mut TvidSet::new(), &info, ty)
}

fn forget_generic(forget: impl FnOnce(fake::T, Blame) -> fake::T, env: &mut Env, blame: Blame) {
    let fake_members = get_fake_members(env);
    let fake_members = forget(fake_members, blame);
    set_fake_members(env, fake_members)
}

pub fn forget_members(env: &mut Env, blame: Blame) {
    forget_generic(fake::forget, env, blame)
}

pub fn forget_prefixed_members(env: &mut Env, lid: &LocalId, blame: Blame) {
    forget_generic(
        |fake_members, blame| fake::forget_prefixed(fake_members, lid, blame),
        env,
        blame,
    )
}

pub fn forget_suffixed_members(env: &mut Env, suffix: &str, blame: Blame) {
    forget_generic(
        |fake_members, blame| fake::forget_suffixed(fake_members, suffix, blame),
        env,
        blame,
    )
}

pub fn forget_static_named_members(env: &mut Env, member_name: &str, blame: Blame) {
    forget_generic(
        |fake_members, blame| fake::forget_static_named(fake_members, member_name, blame),
        env,
        blame,
    )
}

/// `Typing_env.FakeMembers`
pub mod fake_members {
    use super::*;

    pub fn update_fake_members(env: &mut Env, fake_members: fake::T) {
        update_per_cont_env(env, |per_cont_env| {
            lenvc::update_cont_entry(c::T::Next, per_cont_env, |mut entry| {
                entry.fake_members = fake_members;
                entry
            })
        })
    }

    pub fn is_valid(env: &Env, obj: &nast::Expr, member_name: &str) -> bool {
        match obj {
            aast::Expr(_, _, aast::Expr_::This) | aast::Expr(_, _, aast::Expr_::Lvar(_)) => {
                let fake_members = get_fake_members(env);
                let id = fake::make_id(obj, member_name);
                fake::is_valid(&fake_members, &id)
            }
            _ => false,
        }
    }

    pub fn is_valid_static(env: &Env, cid: &nast::ClassId_, member_name: &str) -> bool {
        let name = fake::make_static_id(cid, member_name);
        let fake_members = get_fake_members(env);
        fake::is_valid(&fake_members, &name)
    }

    pub fn check_static_invalid(
        env: &mut Env,
        cid: &nast::ClassId_,
        member_name: &str,
        ty: Ty,
    ) -> Ty {
        let fake_members = get_fake_members(env);
        let fake_id = fake::make_static_id(cid, member_name);
        match fake::is_invalid(&fake_members, &fake_id) {
            None => ty,
            // `LID.to_string fake_id`
            Some(blame) => update_lost_info(local_id::get_name(&fake_id), &blame, env, ty),
        }
    }

    pub fn check_instance_invalid(
        env: &mut Env,
        obj: &nast::Expr,
        member_name: &str,
        ty: Ty,
    ) -> Ty {
        match obj {
            aast::Expr(_, _, aast::Expr_::This) | aast::Expr(_, _, aast::Expr_::Lvar(_)) => {
                let fake_members = get_fake_members(env);
                let fake_id = fake::make_id(obj, member_name);
                match fake::is_invalid(&fake_members, &fake_id) {
                    None => ty,
                    // `LID.to_string fake_id`
                    Some(blame) => {
                        update_lost_info(local_id::get_name(&fake_id), &blame, env, ty)
                    }
                }
            }
            _ => ty,
        }
    }

    fn add_member(env: &mut Env, fake_id: LocalId, pos: Pos) {
        let fake_members = get_fake_members(env);
        let fake_members = fake::add(fake_members, fake_id, pos);
        set_fake_members(env, fake_members)
    }

    pub fn make(env: &mut Env, obj_name: &nast::Expr, member_name: &str, pos: Pos) -> LocalId {
        let my_fake_local_id = fake::make_id(obj_name, member_name);
        add_member(env, my_fake_local_id.clone(), pos);
        my_fake_local_id
    }

    pub fn make_static(
        env: &mut Env,
        class_name: &nast::ClassId_,
        member_name: &str,
        pos: Pos,
    ) -> LocalId {
        let my_fake_local_id = fake::make_static_id(class_name, member_name);
        add_member(env, my_fake_local_id.clone(), pos);
        my_fake_local_id
    }
}

// ---------------------------------------------------------------------------
// Sets up/cleans up the environment when typing anonymous function / lambda
// ---------------------------------------------------------------------------

pub fn closure<A>(env: &mut Env, f: impl FnOnce(&mut Env) -> A) -> A {
    // Remember parts of the environment specific to the enclosing function
    // that will be overwritten when typing a lambda
    let old_lenv = env.lenv.clone();
    let old_return = get_return(env);
    let old_params = get_params(env);
    let outer_fun_kind = get_fn_kind(env);
    let outer_check_status = env.checked.clone();
    let old_in_lambda = env.in_lambda;
    env.in_lambda = true;
    // Typing
    let ret = f(env);
    // Restore the environment fields that were clobbered
    env.in_lambda = old_in_lambda;
    env.lenv = old_lenv;
    set_params(env, old_params);
    set_return(env, old_return);
    set_fn_kind(env, outer_fun_kind);
    env.checked = outer_check_status;
    ret
}

pub fn in_try<A>(env: &mut Env, f: impl FnOnce(&mut Env) -> A) -> A {
    let old_in_try = env.in_try;
    env.in_try = true;
    let result = f(env);
    env.in_try = old_in_try;
    result
}

/// Return the subset of env which is saved in the Typed AST's EnvAnnotation.
pub fn save(local_tpenv: &tp_env::T, env: &Env) -> tast::SavedEnv {
    tast::SavedEnv {
        tcopt: Arc::clone(get_tcopt(env)),
        inference_env: env.inference_env.clone(),
        tpenv: tp_env::union(local_tpenv, &env.tpenv),
        fun_tast_info: env.fun_tast_info.clone(),
        checked: env.checked.clone(),
    }
}

fn tvid_set_union(a: TvidSet, b: &TvidSet) -> TvidSet {
    let mut a = a;
    a.extend(b.iter().copied());
    a
}

/// Compute the type variables appearing covariantly (positively)
/// resp. contravariantly (negatively) in a given type ty.
/// Return a pair of sets of positive and negative type variables
/// (as well as an updated environment).
pub fn get_tyvars(env: &mut Env, ty: &Ty) -> (TvidSet, TvidSet) {
    let mut acc = (TvidSet::new(), TvidSet::new());
    get_tyvars_into(env, ty, Polarity::Positive, &mut acc);
    acc
}

/// Where the type variables of a part of a type go in the result of
/// `get_tyvars` of the whole type.
///
/// The OCaml returns a pair of sets for each part and unions them (swapped
/// for a contravariant part, the union of both for an invariant one) into
/// the pair of the whole. Here every part adds its variables to one
/// accumulator, on the side its polarity says: the sets are the same, and
/// the parts are visited in the same order (`expand_var` and the decl
/// lookups have effects).
#[derive(Clone, Copy)]
enum Polarity {
    Positive,
    Negative,
    /// Both sets (an invariant position).
    Both,
}

impl Polarity {
    fn flip(self) -> Polarity {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
            Polarity::Both => Polarity::Both,
        }
    }

    /// The polarity of a type argument of variance `variance`.
    fn with_variance(self, variance: ast_defs::Variance) -> Polarity {
        match variance {
            ast_defs::Variance::Covariant => self,
            ast_defs::Variance::Contravariant => self.flip(),
            ast_defs::Variance::Invariant => Polarity::Both,
        }
    }
}

fn add_tyvar_with_polarity(acc: &mut (TvidSet, TvidSet), polarity: Polarity, v: tvid::T) {
    match polarity {
        Polarity::Positive => {
            acc.0.insert(v);
        }
        Polarity::Negative => {
            acc.1.insert(v);
        }
        Polarity::Both => {
            acc.0.insert(v);
            acc.1.insert(v);
        }
    }
}

/// `get_tyvars env ty`, added to `acc` with `polarity`.
fn get_tyvars_into(env: &mut Env, ty: &Ty, polarity: Polarity, acc: &mut (TvidSet, TvidSet)) {
    // Not in the OCaml, which visits it: a type without type variables has
    // none (see `typing_defs_core::ty_flags`). (The visit looks up the classes
    // and aliases of the type, for their variances: when that records
    // dependency edges, it is done.)
    if !ty.may_have_tyvars() && !deps::records_dependency_edges(env) {
        return;
    }
    // `get_tyvars_i env (LoclType ty)`, without building the internal type:
    // `expand_internal_type` on a `LoclType` is `expand_type`.
    match get_node(ty) {
        Ty_::Tvar(v) => {
            let expanded = expand_var_ref(env, get_reason(ty), *v);
            get_tyvars_locl_into(env, &expanded, polarity, acc)
        }
        _ => get_tyvars_locl_into(env, ty, polarity, acc),
    }
}

/// The `LoclType` case of `get_tyvars_i`: `ety` is an expanded type.
fn get_tyvars_locl_into(
    env: &mut Env,
    ety: &Ty,
    polarity: Polarity,
    acc: &mut (TvidSet, TvidSet),
) {
    match get_node(ety) {
        Ty_::Tvar(v) => add_tyvar_with_polarity(acc, polarity, *v),
        Ty_::Tany(_) | Ty_::Tnonnull | Ty_::Tdynamic(_) | Ty_::Tprim(_) | Ty_::Tneg(_) => {}
        Ty_::Toption(ty) => get_tyvars_into(env, ty, polarity, acc),
        Ty_::Ttuple(tuple) => {
            match &tuple.extra {
                TupleExtra::Tvariadic(t_variadic) => get_tyvars_into(env, t_variadic, polarity, acc),
                TupleExtra::Tsplat(t_splat) => get_tyvars_into(env, t_splat, polarity, acc),
            };
            for ty in tuple.required.iter() {
                get_tyvars_into(env, ty, polarity, acc)
            }
            for ty in tuple.optional.iter() {
                get_tyvars_into(env, ty, polarity, acc)
            }
        }
        Ty_::Tunion(tyl) | Ty_::Tintersection(tyl) => {
            for ty in tyl.iter() {
                get_tyvars_into(env, ty, polarity, acc)
            }
        }
        Ty_::Tshape(ShapeType::ShapeSimple(shape)) => {
            for sft in shape.fields.values() {
                get_tyvars_into(env, &sft.ty, polarity, acc)
            }
        }
        Ty_::Tshape(ShapeType::ShapeSplat(shape)) => {
            for ty in shape.ss_elems.iter() {
                get_tyvars_into(env, ty, polarity, acc)
            }
        }
        Ty_::Tfun(ft) => {
            for fp in ft.params.iter() {
                match get_fp_mode(fp) {
                    // Parameters are treated contravariantly
                    ParamMode::FPnormal => get_tyvars_into(env, &fp.type_, polarity.flip(), acc),
                    // Inout parameters are both co- and contra-variant
                    ParamMode::FPinout => get_tyvars_into(env, &fp.type_, Polarity::Both, acc),
                }
            }
            match &ft.implicit_params.capability {
                Capability::CapDefaults(_) => {}
                Capability::CapTy(ty) => get_tyvars_into(env, ty, polarity, acc),
            };
            get_tyvars_into(env, &ft.ret, polarity, acc)
        }
        Ty_::Tnewtype(name, tyl, _) => {
            if tyl.is_empty() {
            } else {
                match get_typedef(env, name) {
                    decl_entry::T::Found(td) => {
                        for (tp, ty) in td.tparams.iter().zip(tyl.iter()) {
                            get_tyvars_into(env, ty, polarity.with_variance(tp.variance), acc)
                        }
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                }
            }
        }
        Ty_::Tdependent(_, ty) => get_tyvars_into(env, ty, polarity, acc),
        Ty_::Tgeneric(_) => {}
        Ty_::Tclass((_, cid), _, tyl) => {
            if tyl.is_empty() {
            } else {
                match get_class(env, cid) {
                    decl_entry::T::Found(cls) => {
                        // `List.map ~f:(fun t -> t.tp_variance) (Cls.tparams cls)`,
                        // without copying the type parameters.
                        let cls::T(decl, cls::typing_class_types::ClassT(c, _), _) = &cls;
                        let variancel: Vec<ast_defs::Variance> =
                            cls::decl_counters::count_subdecl(
                                decl.as_ref(),
                                cls::decl_counters::SubdeclKind::Tparams,
                                || c.tparams.iter().map(|t| t.variance).collect(),
                            );
                        for (variance, ty) in variancel.into_iter().zip(tyl.iter()) {
                            get_tyvars_into(env, ty, polarity.with_variance(variance), acc)
                        }
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                }
            }
        }
        Ty_::TvecOrDict(ty1, ty2) => {
            get_tyvars_into(env, ty1, polarity, acc);
            get_tyvars_into(env, ty2, polarity, acc)
        }
        Ty_::Tlabel(_name) => {}
        Ty_::Taccess(taccess) => get_tyvars_into(env, &taccess.0, polarity, acc),
        Ty_::TclassPtr(ty) => get_tyvars_into(env, ty, polarity, acc),
    }
}

fn get_tyvars_i(env: &mut Env, ty: &InternalType) -> (TvidSet, TvidSet) {
    let mut acc = (TvidSet::new(), TvidSet::new());
    let pol = Polarity::Positive;
    // `expand_internal_type` only changes a `LoclType`, and `get_tyvars`
    // expands it.
    match ty {
        InternalType::LoclType(ty) => get_tyvars_into(env, ty, pol, &mut acc),
        InternalType::ConstraintType(ty) => match deref_constraint_type(ty) {
            (_, ConstraintType_::Tdestructure(d)) => {
                for ty in d.required.iter() {
                    get_tyvars_into(env, ty, pol, &mut acc)
                }
                for ty in d.optional.iter() {
                    get_tyvars_into(env, ty, pol, &mut acc)
                }
                match &d.variadic {
                    Some(ty) => get_tyvars_into(env, ty, pol, &mut acc),
                    None => {}
                }
            }
            (_, ConstraintType_::ThasMember(hm)) => get_tyvars_into(env, &hm.type_, pol, &mut acc),
            (_, ConstraintType_::ThasTypeMember(htm)) => {
                // `(posup ∪ neglo, poslo ∪ negup)`: the lower bound is
                // contravariant.
                get_tyvars_into(env, &htm.lower, pol.flip(), &mut acc);
                get_tyvars_into(env, &htm.upper, pol, &mut acc)
            }
            (_, ConstraintType_::TcanIndex(ci)) => {
                get_tyvars_into(env, &ci.key, pol, &mut acc);
                get_tyvars_into(env, &ci.val, pol, &mut acc)
            }
            (_, ConstraintType_::TcanIndexAssign(cia)) => {
                get_tyvars_into(env, &cia.key, pol, &mut acc);
                get_tyvars_into(env, &cia.write, pol, &mut acc);
                get_tyvars_into(env, &cia.val, pol, &mut acc)
            }
            (_, ConstraintType_::TcanTraverse(ct)) => {
                get_tyvars_into(env, &ct.val, pol, &mut acc);
                match &ct.key {
                    None => {}
                    Some(ct_key) => get_tyvars_into(env, ct_key, pol, &mut acc),
                }
            }
            (
                _,
                ConstraintType_::TtypeSwitch {
                    predicate: _,
                    ty_true,
                    ty_false,
                },
            ) => {
                get_tyvars_into(env, &ty_true, pol, &mut acc);
                get_tyvars_into(env, &ty_false, pol, &mut acc)
            }
            (_, ConstraintType_::ThasConst { name: _, ty }) => get_tyvars_into(env, &ty, pol, &mut acc),
        },
    }
    acc
}

fn set_tyvar_appears_covariantly_and_propagate(env: &mut Env, var: tvid::T) {
    if get_tyvar_appears_covariantly(env, var) {
    } else {
        inf::set_tyvar_appears_covariantly(&mut env.inference_env, var);
        let lower_bounds = get_tyvar_lower_bounds(env, var);
        update_variance_of_tyvars_occurring_in_lower_bounds(env, &lower_bounds)
    }
}

fn set_tyvar_appears_contravariantly_and_propagate(env: &mut Env, var: tvid::T) {
    if get_tyvar_appears_contravariantly(env, var) {
    } else {
        inf::set_tyvar_appears_contravariantly(&mut env.inference_env, var);
        let upper_bounds = get_tyvar_upper_bounds(env, var);
        update_variance_of_tyvars_occurring_in_upper_bounds(env, &upper_bounds)
    }
}

fn update_variance_of_tyvars_occurring_in_lower_bounds(env: &mut Env, tys: &ITySet) {
    for ty in tys.iter() {
        update_variance_of_tyvars_occurring_in_lower_bound(env, ty)
    }
}

fn update_variance_of_tyvars_occurring_in_upper_bounds(env: &mut Env, tys: &ITySet) {
    for ty in tys.iter() {
        update_variance_of_tyvars_occurring_in_upper_bound(env, ty)
    }
}

/// `let (env, ety) = expand_internal_type env ty in
///  match ety with LoclType ty when is_tyvar ty -> ..`: whether `ty` is a type
/// variable once expanded.
fn expands_to_tyvar(env: &mut Env, ty: &InternalType) -> bool {
    match ty {
        InternalType::LoclType(ty) => match get_node(ty) {
            Ty_::Tvar(v) => {
                let ety = expand_var_ref(env, get_reason(ty), *v);
                matches!(get_node(&ety), Ty_::Tvar(_))
            }
            _ => false,
        },
        InternalType::ConstraintType(_) => false,
    }
}

fn update_variance_of_tyvars_occurring_in_lower_bound(env: &mut Env, ty: &InternalType) {
    if expands_to_tyvar(env, ty) {
    } else {
        let (positive, negative) = get_tyvars_i(env, ty);
        // These are the functions of `Typing_inference_env`: the ones of this
        // module, which propagate, are defined after this point in the OCaml.
        for var in positive {
            inf::set_tyvar_appears_covariantly(&mut env.inference_env, var)
        }
        for var in negative {
            inf::set_tyvar_appears_contravariantly(&mut env.inference_env, var)
        }
    }
}

fn update_variance_of_tyvars_occurring_in_upper_bound(env: &mut Env, ty: &InternalType) {
    if expands_to_tyvar(env, ty) {
    } else {
        let (positive, negative) = get_tyvars_i(env, ty);
        // These are the functions of `Typing_inference_env`: the ones of this
        // module, which propagate, are defined after this point in the OCaml.
        for var in positive {
            inf::set_tyvar_appears_contravariantly(&mut env.inference_env, var)
        }
        for var in negative {
            inf::set_tyvar_appears_covariantly(&mut env.inference_env, var)
        }
    }
}

pub fn set_tyvar_appears_covariantly(env: &mut Env, var: tvid::T) {
    set_tyvar_appears_covariantly_and_propagate(env, var)
}

pub fn set_tyvar_appears_contravariantly(env: &mut Env, var: tvid::T) {
    set_tyvar_appears_contravariantly_and_propagate(env, var)
}

/// After a type variable var has been "solved", or bound to a type ty, we need
/// to update the variance of type variables occurring in ty. Suppose that
/// variable var is marked "appears covariantly", i.e. it appears (at least) in
/// positive positions in the type of an expression. Then when we substitute ty
/// for var, variables that appear positively in ty must now be marked as
/// appearing covariantly; variables that appear negatively in ty must now be
/// marked as appearing contravariantly. And the dual, if the variable var is marked
/// "appears contravariantly".
pub fn update_variance_after_bind(env: &mut Env, var: tvid::T, ty: &Ty) {
    let appears_contravariantly = get_tyvar_appears_contravariantly(env, var);
    let appears_covariantly = get_tyvar_appears_covariantly(env, var);
    let (positive, negative) = get_tyvars(env, ty);
    for var in positive {
        if appears_contravariantly {
            set_tyvar_appears_contravariantly(env, var)
        };
        if appears_covariantly {
            set_tyvar_appears_covariantly(env, var)
        }
    }
    for var in negative {
        if appears_contravariantly {
            set_tyvar_appears_covariantly(env, var)
        };
        if appears_covariantly {
            set_tyvar_appears_contravariantly(env, var)
        }
    }
}

pub fn set_tyvar_variance_i(
    env: &mut Env,
    flip: Option<bool>,
    for_all_vars: Option<bool>,
    ty: &InternalType,
) {
    let flip = flip.unwrap_or(false);
    let for_all_vars = for_all_vars.unwrap_or(false);
    with_log_env_change("set_tyvar_variance", None, env, |env| {
        let current = get_current_tyvars(env);
        if !for_all_vars && current.is_empty() {
        } else {
            let (positive, negative) = get_tyvars_i(env, ty);
            let (positive, negative) = if flip {
                (negative, positive)
            } else {
                (positive, negative)
            };
            let tyvars: Vec<tvid::T> = if for_all_vars {
                tvid_set_union(positive.clone(), &negative).into_iter().collect()
            } else {
                current
            };
            for var in tyvars {
                if positive.contains(&var) {
                    set_tyvar_appears_covariantly(env, var)
                };
                if negative.contains(&var) {
                    set_tyvar_appears_contravariantly(env, var)
                }
            }
        }
    })
}

pub fn set_tyvar_variance(
    env: &mut Env,
    flip: Option<bool>,
    for_all_vars: Option<bool>,
    ty: &Ty,
) {
    let flip = flip.unwrap_or(false);
    let for_all_vars = for_all_vars.unwrap_or(false);
    set_tyvar_variance_i(
        env,
        Some(flip),
        Some(for_all_vars),
        &InternalType::LoclType(ty.clone()),
    )
}

pub fn add_tyvar_upper_bound(
    intersect: Option<&mut dyn FnMut(InternalType, &[InternalType]) -> Vec<InternalType>>,
    env: &mut Env,
    var: tvid::T,
    ty: InternalType,
) {
    with_log_env_change("add_tyvar_upper_bound", None, env, |env| {
        inf::add_tyvar_upper_bound(intersect, &mut env.inference_env, var, ty)
    })
}

/// Add a single new upper bound [ty] to type variable [var] in [env.inference_env].
/// If the optional [intersect] operation is supplied, then use this to avoid
/// adding redundant bounds by merging the type with existing bounds. This makes
/// sense because a conjunction of upper bounds
///   (v <: t1) /\ ... /\ (v <: tn)
/// is equivalent to a single upper bound
///   v <: (t1 & ... & tn)
pub fn add_tyvar_upper_bound_and_update_variances(
    intersect: Option<&mut dyn FnMut(InternalType, &[InternalType]) -> Vec<InternalType>>,
    env: &mut Env,
    var: tvid::T,
    ty: InternalType,
) {
    with_log_env_change("add_tyvar_upper_bound", None, env, |env| {
        add_tyvar_upper_bound(intersect, env, var, ty.clone());
        if get_tyvar_appears_contravariantly(env, var) {
            update_variance_of_tyvars_occurring_in_upper_bound(env, &ty)
        }
    })
}

/// Remove type variable `upper_var` from the upper bounds on `var`, if it exists
pub fn remove_tyvar_upper_bound(env: &mut Env, var: tvid::T, upper_var: tvid::T) {
    with_log_env_change("remove_tyvar_upper_bound", None, env, |env| {
        inf::remove_tyvar_upper_bound(&mut env.inference_env, var, upper_var)
    })
}

/// Remove type variable `lower_var` from the lower bounds on `var`, if it exists
pub fn remove_tyvar_lower_bound(env: &mut Env, var: tvid::T, lower_var: tvid::T) {
    with_log_env_change("remove_tyvar_lower_bound var", None, env, |env| {
        inf::remove_tyvar_lower_bound(&mut env.inference_env, var, lower_var)
    })
}

pub fn add_tyvar_lower_bound(
    union: Option<&mut dyn FnMut(InternalType, &[InternalType]) -> Vec<InternalType>>,
    env: &mut Env,
    var: tvid::T,
    ty: InternalType,
) {
    with_log_env_change("add_tyvar_lower_bound", None, env, |env| {
        inf::add_tyvar_lower_bound(union, &mut env.inference_env, var, ty)
    })
}

/// Add a single new lower bound [ty] to type variable [var] in [env.tvenv].
/// If the optional [union] operation is supplied, then use this to avoid
/// adding redundant bounds by merging the type with existing bounds. This makes
/// sense because a conjunction of lower bounds
///   (t1 <: v) /\ ... /\ (tn <: v)
/// is equivalent to a single lower bound
///   (t1 | ... | tn) <: v
pub fn add_tyvar_lower_bound_and_update_variances(
    union: Option<&mut dyn FnMut(InternalType, &[InternalType]) -> Vec<InternalType>>,
    env: &mut Env,
    var: tvid::T,
    ty: InternalType,
) {
    with_log_env_change("add_tyvar_lower_bound", None, env, |env| {
        add_tyvar_lower_bound(union, env, var, ty.clone());
        if get_tyvar_appears_covariantly(env, var) {
            update_variance_of_tyvars_occurring_in_lower_bound(env, &ty)
        }
    })
}

pub fn get_all_tyvars(env: &Env) -> Vec<tvid::T> {
    inf::get_vars(&env.inference_env)
}

/// Remove solved variable from environment by replacing it by its binding.
pub fn remove_var(
    env: &mut Env,
    var: tvid::T,
    search_in_upper_bounds_of: &TvidSet,
    search_in_lower_bounds_of: &TvidSet,
) {
    with_log_env_change("remove_var", None, env, |env| {
        inf::remove_var(
            &mut env.inference_env,
            var,
            search_in_upper_bounds_of,
            search_in_lower_bounds_of,
        )
    })
}

/// `Typing_env.Log`
pub mod log {
    use super::*;

    /// Convert a type variable from an environment into json
    pub fn tyvar_to_json(
        p_locl_ty: impl Fn(&Ty) -> String,
        p_internal_type: impl Fn(&InternalType) -> String,
        env: &Env,
        v: tvid::T,
    ) -> serde_json::Value {
        inf::log::tyvar_to_json(p_locl_ty, p_internal_type, &env.inference_env, v)
    }

    pub fn expand_env(env: &Env, expand_env: &typing_defs::ExpandEnv) -> Vec<(String, String)> {
        let typing_defs::ExpandEnv {
            type_expansions,
            make_internal_opaque,
            visibility_behavior,
            substs: _,
            no_substs: _,
            this_ty,
            on_error: _,
            wildcard_action: _,
            ish_weakening,
            under_type_constructor: _,
            simplify_intersections: _,
        } = expand_env;
        if typing_env_types::get_log_level(env, "expand_env") == 0 {
            vec![]
        } else {
            vec![
                (
                    "visibility_behavior".to_string(),
                    typing_defs::show_visibility_behavior(visibility_behavior),
                ),
                ("this_ty".to_string(), crate::typing_print::debug(env, this_ty)),
                (
                    "type_expansions".to_string(),
                    crate::type_expansions::to_log_string(type_expansions),
                ),
                (
                    "make_internal_opaque".to_string(),
                    make_internal_opaque.to_string(),
                ),
                ("ish_weakening".to_string(), ish_weakening.to_string()),
            ]
        }
    }
}

pub fn update_reason(_env: &Env, ty: Ty, f: impl FnOnce(Reason) -> Reason) -> Ty {
    map_reason(ty, f)
}

pub fn update_cty_reason(
    _env: &Env,
    cty: ConstraintType,
    f: impl FnOnce(Reason) -> Reason,
) -> ConstraintType {
    let (r, cstr) = deref_constraint_type(&cty);
    mk_constraint_type((f(r), cstr))
}

pub fn update_ity_reason(
    t: &Env,
    ity: InternalType,
    f: impl FnOnce(Reason) -> Reason,
) -> InternalType {
    match ity {
        InternalType::LoclType(lty) => InternalType::LoclType(update_reason(t, lty, f)),
        InternalType::ConstraintType(cty) => {
            InternalType::ConstraintType(update_cty_reason(t, cty, f))
        }
    }
}

/// see .mli
pub fn inside_expr_tree(env: &mut Env, expr_tree_hint: aast::ClassName) {
    let outer_locals = match env.lenv.per_cont_env.get(&c::T::Next) {
        None => typing_local_types::empty(),
        Some(cont) => cont.local_types.clone(),
    };
    env.in_expr_tree = Some(ExprTreeEnv {
        dsl: expr_tree_hint,
        outer_locals,
    })
}

pub fn outside_expr_tree(env: &mut Env, macro_variables: Option<&[aast::Lid]>) {
    let macro_locals = match macro_variables {
        None => None,
        Some(lids) => {
            let mut local_env = typing_local_types::empty();
            for aast::Lid(pos, local_id) in lids {
                let ty = fresh_type_invariant(env, pos.clone());
                let local = Local {
                    ty,
                    pos: pos.clone(),
                    eid: expression_id::make(&env.expression_id_provider),
                    macro_splice_vars: None,
                };
                local_env =
                    typing_local_types::add_to_local_types(local_id.clone(), local, local_env);
            }
            Some(local_env)
        }
    };
    env.in_expr_tree = None;
    env.in_macro_splice = macro_locals;
}

pub fn with_inside_expr_tree<A, B>(
    env: &mut Env,
    expr_tree_hint: aast::ClassName,
    f: impl FnOnce(&mut Env) -> (A, B),
) -> (A, B) {
    let old_in_expr_tree = env.in_expr_tree.clone();
    inside_expr_tree(env, expr_tree_hint);
    let (r1, r2) = f(env);
    env.in_expr_tree = old_in_expr_tree;
    (r1, r2)
}

pub fn with_outside_expr_tree<A, B>(
    env: &mut Env,
    macro_variables: Option<&[aast::Lid]>,
    f: impl FnOnce(&mut Env, Option<aast::ClassName>) -> (A, B),
) -> (A, B, Option<im::OrdMap<LocalId, (Pos, Ty)>>) {
    let old_in_expr_tree = env.in_expr_tree.clone();
    let old_in_macro_splice = env.in_macro_splice.clone();
    let dsl = match &old_in_expr_tree {
        Some(ExprTreeEnv {
            dsl: cls,
            outer_locals: _,
        }) => Some(cls.clone()),
        _ => None,
    };
    outside_expr_tree(env, macro_variables);
    let (r1, r2) = f(env, dsl);
    let new_macro_type_mapping = env.in_macro_splice.as_ref().map(|locals| {
        locals
            .iter()
            .map(|(lid, local)| (lid.clone(), (local.pos.clone(), local.ty.clone())))
            .collect::<im::OrdMap<LocalId, (Pos, Ty)>>()
    });
    env.in_expr_tree = old_in_expr_tree;
    env.in_macro_splice = old_in_macro_splice;
    (r1, r2, new_macro_type_mapping)
}

/// see .mli
pub fn is_in_expr_tree(env: &Env) -> bool {
    env.in_expr_tree.is_some()
}

pub fn rank_of_tparam(env: &Env, tparam: &str) -> isize {
    tp_env::get_rank(&env.tpenv, tparam)
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use relative_path::Prefix;

    use super::*;

    fn env() -> Env {
        let ctx = Ctx::new(Path::new("/"), Default::default()).unwrap();
        let file = Arc::new(RelativePath::make(Prefix::Root, "f.php".into()));
        typing_env_types::empty(None, None, Arc::new(ctx), file, None)
    }

    fn lid(name: &str) -> LocalId {
        local_id::make_unscoped(name)
    }

    /// A position that is different for each `line`.
    fn pos(line: usize) -> Pos {
        Pos::from_lnum_bol_offset(
            Arc::new(RelativePath::make(Prefix::Root, "f.php".into())),
            (line, 0, 0),
            (line, 0, 1),
        )
    }

    /// The type `Tgeneric name`: enough to tell the types of the tests apart.
    fn ty(name: &str) -> Ty {
        mk((typing_reason::none(), Ty_::Tgeneric(name.to_string())))
    }

    fn name_of(ty: &Ty) -> String {
        match get_node(ty) {
            Ty_::Tgeneric(name) => name.clone(),
            Ty_::Tunion(tyl) if tyl.is_empty() => "nothing".to_string(),
            _ => panic!("the tests only make Tgeneric"),
        }
    }

    #[test]
    fn locals() {
        let mut env = env();
        assert!(!is_local_defined(&env, &lid("$x")));
        set_local(None, None, &mut env, lid("$x"), ty("A"), pos(1));
        assert!(is_local_defined(&env, &lid("$x")));
        let local = get_local(&env, &lid("$x"));
        assert_eq!(name_of(&local.ty), "A");
        assert_eq!(local.pos, pos(1));

        // A union of one type is that type.
        let union = mk((typing_reason::none(), Ty_::Tunion(vec![ty("B")])));
        set_local(None, None, &mut env, lid("$y"), union, pos(2));
        assert_eq!(name_of(&get_local(&env, &lid("$y")).ty), "B");

        // A local that is not defined has the type nothing.
        let undefined = get_local(&env, &lid("$z"));
        assert_eq!(name_of(&undefined.ty), "nothing");
        assert_eq!(undefined.pos, Pos::NONE);

        unset_local(&mut env, &lid("$x"));
        assert!(!is_local_defined(&env, &lid("$x")));
        assert!(is_local_defined(&env, &lid("$y")));

        let captured = get_locals(
            Some(true),
            &env,
            &[
                aast::CaptureLid((), aast::Lid(pos(3), lid("$y"))),
                aast::CaptureLid((), aast::Lid(pos(3), lid("$x"))),
            ],
        );
        assert_eq!(captured.keys().cloned().collect::<Vec<_>>(), vec![lid("$y")]);

        let mut other = self::env();
        set_locals(&mut other, &captured);
        assert!(is_local_defined(&other, &lid("$y")));
    }

    #[test]
    fn locals_in_dead_code() {
        // Without a next continuation, nothing is set, and every local has
        // the type nothing.
        let mut env = env();
        update_per_cont_env(&mut env, |locals| lenvc::drop_cont(c::T::Next, locals));
        set_local(None, None, &mut env, lid("$x"), ty("A"), pos(1));
        assert!(next_cont_opt(&env).is_none());
        assert!(!is_local_defined(&env, &lid("$x")));
        assert_eq!(name_of(&get_local(&env, &lid("$x")).ty), "nothing");
        assert_eq!(get_local_expr_id(&env, &lid("$x")), None);
        assert!(set_local_expr_id(&mut env, &lid("$x"), 42).is_ok());
    }

    #[test]
    fn expression_ids() {
        let mut env = env();
        set_local(None, None, &mut env, lid("$x"), ty("A"), pos(1));
        let eid = get_local_expr_id(&env, &lid("$x")).unwrap();
        // An assignment keeps the expression id of the local.
        set_local(None, None, &mut env, lid("$x"), ty("B"), pos(2));
        assert_eq!(get_local_expr_id(&env, &lid("$x")), Some(eid));
        // Another local gets another one.
        set_local(None, None, &mut env, lid("$y"), ty("A"), pos(3));
        assert_ne!(get_local_expr_id(&env, &lid("$y")), Some(eid));

        // The copies of an environment draw from the same provider.
        let copy = env.clone();
        let id1 = make_expression_id(&env);
        let id2 = make_expression_id(&copy);
        let id3 = make_expression_id(&env);
        assert!(id1 != id2 && id2 != id3 && id1 != id3);

        // Setting the same id changes nothing; another one replaces it.
        assert!(set_local_expr_id(&mut env, &lid("$x"), eid).is_ok());
        assert!(set_local_expr_id(&mut env, &lid("$x"), id1).is_ok());
        assert_eq!(get_local_expr_id(&env, &lid("$x")), Some(id1));
        assert!(set_local_expr_id(&mut env, &lid("$absent"), id1).is_ok());
    }

    #[test]
    fn immutable_locals() {
        let mut env = env();
        set_local(Some(true), None, &mut env, lid("$x"), ty("A"), pos(1));
        let eid = get_local_expr_id(&env, &lid("$x")).unwrap();
        assert!(expression_id::is_immutable(eid));
        let new_eid = make_expression_id(&env);
        match set_local_expr_id(&mut env, &lid("$x"), new_eid) {
            Err(typing_error::T::Primary(prim)) => match &*prim {
                typing_error::primary::T::Immutable_local(p) => assert_eq!(*p, pos(1)),
                _ => panic!("expected the error Immutable_local"),
            },
            _ => panic!("expected the error Immutable_local"),
        }
        // The environment is updated even so.
        assert_eq!(get_local_expr_id(&env, &lid("$x")), Some(new_eid));
    }

    #[test]
    fn using_vars() {
        let mut env = env();
        set_local(None, None, &mut env, lid("$x"), ty("A"), pos(1));
        assert!(!is_using_var(&env, &lid("$x")));
        set_using_var(&mut env, lid("$x"));
        assert!(is_using_var(&env, &lid("$x")));
        unset_local(&mut env, &lid("$x"));
        assert!(!is_using_var(&env, &lid("$x")));
    }

    #[test]
    fn fake_members_of_the_environment() {
        let mut env = env();
        let this = aast::Expr((), Pos::NONE, aast::Expr_::This);
        let call = aast::Expr((), Pos::NONE, aast::Expr_::Null);
        assert!(!fake_members::is_valid(&env, &this, "f"));
        let id = fake_members::make(&mut env, &this, "f", pos(1));
        assert_eq!(local_id::get_name(&id), "$this->f");
        assert!(fake_members::is_valid(&env, &this, "f"));
        assert!(!fake_members::is_valid(&env, &this, "g"));
        // Only `$this` and locals have fake members.
        assert!(!fake_members::is_valid(&env, &call, "f"));

        // A fake member that is valid is not an undefined local.
        assert!(!is_local_defined(&env, &id));

        let blame = Blame::Blame(pos(2), typing_reason::BlameSource::BScall);
        forget_members(&mut env, blame.clone());
        assert!(!fake_members::is_valid(&env, &this, "f"));
        assert_eq!(fake::is_invalid(&get_fake_members(&env), &id), Some(blame));

        // The type of an invalidated member says what was lost.
        let ty_ = fake_members::check_instance_invalid(&mut env, &this, "f", ty("A"));
        assert_eq!(name_of(&ty_), "A");
        assert!(matches!(
            &**get_reason(&ty_),
            crate::typing_reason::T_::LostInfo(name, _, _) if name == "$this->f"
        ));
        // Nothing is known about this one: the type is unchanged.
        let ty_ = fake_members::check_instance_invalid(&mut env, &this, "g", ty("A"));
        assert!(!matches!(&**get_reason(&ty_), crate::typing_reason::T_::LostInfo(..)));

        fake_members::make(&mut env, &this, "g", pos(3));
        forget_suffixed_members(&mut env, "f", Blame::Blame(pos(4), typing_reason::BlameSource::BSassignment));
        assert!(fake_members::is_valid(&env, &this, "g"));
        forget_prefixed_members(
            &mut env,
            &typing_defs::this(),
            Blame::Blame(pos(5), typing_reason::BlameSource::BSassignment),
        );
        assert!(!fake_members::is_valid(&env, &this, "g"));
    }

    #[test]
    fn a_copy_of_an_environment_is_independent() {
        let mut env = env();
        set_local(None, None, &mut env, lid("$x"), ty("A"), pos(1));
        let saved = env.clone();

        set_local(None, None, &mut env, lid("$x"), ty("B"), pos(2));
        set_self(&mut env, "\\C".to_string(), ty("C"));
        set_fn_kind(&mut env, ast_defs::FunKind::FAsync);
        set_static(&mut env);
        set_mode(&mut env, file_info::Mode::Mhhi);
        set_log_level(&mut env, "show", 2);
        set_everything_sdt(&mut env, true);
        let name = fresh_param_name(&mut env, "T");
        env_with_method_droot_member(&mut env, "m", true);

        assert_eq!(name_of(&get_local(&env, &lid("$x")).ty), "B");
        assert_eq!(get_self_id(&env), Some("\\C".to_string()));
        assert!(matches!(get_fn_kind(&env), ast_defs::FunKind::FAsync));
        assert!(is_static(&env) && is_hhi(&env) && !is_strict(&env));
        assert_eq!(get_log_level(&env, "show"), 2);
        assert!(get_tcopt(&env).po.everything_sdt);
        assert!(is_generic_parameter(&env, &name));
        assert!(env.decl_env.droot_member.is_some());

        assert_eq!(name_of(&get_local(&saved, &lid("$x")).ty), "A");
        assert_eq!(get_self_id(&saved), None);
        assert!(matches!(get_fn_kind(&saved), ast_defs::FunKind::FSync));
        assert!(!is_static(&saved) && !is_hhi(&saved) && is_strict(&saved));
        assert_eq!(get_log_level(&saved, "show"), 0);
        assert!(!get_tcopt(&saved).po.everything_sdt);
        assert!(!is_generic_parameter(&saved, &name));
        assert!(saved.decl_env.droot_member.is_none());
    }

    #[test]
    fn scoped_changes_are_undone() {
        let mut env = env();
        set_local(None, None, &mut env, lid("$x"), ty("A"), pos(1));
        set_param(&mut env, lid("$p"), (ty("P"), pos(2), None));
        set_self(&mut env, "\\C".to_string(), ty("C"));

        let seen = with_env(&mut env, |env| {
            clear_params(env);
            set_return(
                env,
                typing_env_return_info::T {
                    return_type: ty("R"),
                    return_disposable: true,
                    return_ignore_readonly: false,
                },
            );
            get_params(env).len()
        });
        assert_eq!(seen, 0);
        assert_eq!(get_params(&env).len(), 1);
        assert!(!get_return(&env).return_disposable);

        let seen = closure(&mut env, |env| {
            let in_lambda = env.in_lambda;
            reinitialize_locals(env);
            set_fn_kind(env, ast_defs::FunKind::FAsync);
            clear_params(env);
            (in_lambda, is_local_defined(env, &lid("$x")))
        });
        assert_eq!(seen, (true, false));
        assert!(!env.in_lambda);
        assert!(is_local_defined(&env, &lid("$x")));
        assert!(matches!(get_fn_kind(&env), ast_defs::FunKind::FSync));
        assert_eq!(get_params(&env).len(), 1);

        assert!(in_try(&mut env, |env| env.in_try));
        assert!(!env.in_try);

        let seen = run_with_no_self(&mut env, |env| get_self_id(env));
        assert_eq!(seen, None);
        assert_eq!(get_self_id(&env), Some("\\C".to_string()));

        let dsl = ast_defs::Id(pos(3), "\\Dsl".to_string());
        let (in_tree, outer) = with_inside_expr_tree(&mut env, dsl, |env| {
            let outer = env.in_expr_tree.as_ref().unwrap().outer_locals.len();
            (is_in_expr_tree(env), outer)
        });
        assert_eq!((in_tree, outer), (true, 1));
        assert!(!is_in_expr_tree(&env));
    }

    #[test]
    fn fresh_generic_parameters() {
        let mut env = env();
        assert_eq!(fresh_param_name(&mut env, "T"), "T#1");
        assert_eq!(fresh_param_name(&mut env, "T"), "T#2");
        assert_eq!(fresh_param_name(&mut env, "Tk"), "Tk#1");
        assert!(is_generic_parameter(&env, "T#2"));
        assert!(!is_generic_parameter(&env, "T#3"));

        assert!(is_fresh_generic_parameter("T#1"));
        assert!(!is_fresh_generic_parameter("T"));
        // An expression dependent type is not a fresh generic parameter.
        assert!(!is_fresh_generic_parameter("<expr#1>::T"));

        let name = add_fresh_generic_parameter(
            &mut env,
            PosOrDecl::NONE,
            "T",
            aast::ReifyKind::Reified,
            true,
            false,
        );
        assert_eq!(name, "T#3");
        assert!(matches!(get_reified(&env, &name), aast::ReifyKind::Reified));
        assert!(get_enforceable(&env, &name) && !get_newable(&env, &name));
        assert!(get_require_dynamic(&env, &name));
        assert_eq!(get_generic_parameters(&env), vec![name.clone()]);
        assert!(get_pos_and_kind_of_generic(&env, &name).is_some());

        // The type parameters of the local environment are those of the
        // next continuation.
        assert!(is_consistent(&env));
        mark_inconsistent(&mut env);
        assert!(!is_consistent(&env));
    }
}
