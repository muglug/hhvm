// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/env/deps.ml`: the dependencies that the functions of
//! `Typing_env` record.

// I assume we don't want to implicitly add
// dependencies in our dependency-adding machinery

// `Pos_or_decl.is_hhi`. The positions of the decls of `hackrs` (`BPos`)
// are tested with `BPos::is_hhi`, which is the same test.

use oxidized::decl_reference::DeclReference;
use pos::Pos as _;

use crate::decl_entry;
use crate::decl_provider;
use crate::folded_class as cls;
use crate::folded_class::ClassElt;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep::Variant as Dep;
use crate::typing_env_types::Env;
use crate::typing_pessimisation_deps;

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

/// Not in the OCaml: whether `add_dependency_edge` records anything (in a
/// batch check nothing is recorded), so that callers can skip building
/// the dependency (strings, class names), and lookups made only for their
/// dependency edges.
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
    // Not in the OCaml, which localizes every time: while a localization
    // is recorded for `typing_phase`'s cache, its edges are kept with the
    // entry (`type_expansions::recording`), so that a later hit for another
    // definition records them again (`add_recorded_dependency_edge`) and
    // the edges stay those of the OCaml.
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
