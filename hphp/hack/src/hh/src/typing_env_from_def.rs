// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_env_from_def.ml`. See `hh/PORTING.md`.
//!
//! Construct a Typing_env from an AAST toplevel definition.
//!
//! `Provider_context.t` is stored in the environment that is built, so it is
//! taken by value (`Arc<Ctx>`), as `Typing_env_types.empty` takes it.

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use pos::BPos;
use pos::Positioned;
use pos::TypeName;
use ty::decl::Ty_ as DeclTy_;
use ty::reason::Reason as _;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_counters;
use crate::decl_hint;
use crate::typing_defs_core::DeclTy;
use crate::typing_deps::dep;
use crate::typing_env as env;
use crate::typing_env_types;
use crate::typing_env_types::Env;
use crate::typing_error_utils;
use crate::typing_make_type as make_type;
use crate::typing_phase;
use crate::typing_reason as reason;

pub fn fun_env<Ex, En>(
    origin: Option<decl_counters::Origin>,
    ctx: Arc<Ctx>,
    fd: &aast::FunDef<Ex, En>,
) -> Env {
    let file = Arc::new(fd.name.0.filename().clone());
    let droot = Some(dep::Variant::Fun(fd.name.1.clone()));
    let env = typing_env_types::empty(origin, Some(fd.mode), ctx, file, droot);
    env
}

/// Given a class definition construct a type consisting of the
/// class instantiated at its generic parameters.
pub fn get_self_from_c<Ex, En>(c: &aast::Class_<Ex, En>) -> DeclTy {
    let tparams: Vec<DeclTy> = c
        .tparams
        .iter()
        .map(|tp| {
            let ast_defs::Id(p, s) = &tp.name;
            DeclTy::new(
                R::witness_from_decl(BPos::from(p)),
                DeclTy_::Tgeneric(TypeName::new(s)),
            )
        })
        .collect();
    let ast_defs::Id(name_pos, name) = &c.name;
    let name_pos = BPos::from(name_pos);
    DeclTy::new(
        R::witness_from_decl(name_pos.clone()),
        DeclTy_::Tapply(Box::new((
            Positioned::new(name_pos, TypeName::new(name)),
            tparams.into_boxed_slice(),
        ))),
    )
}

/// Set 'self' identifier and type in environment.
fn set_self<Ex, En>(env: &mut Env, c: &aast::Class_<Ex, En>) {
    let self_id = c.name.1.clone();
    let self_ = get_self_from_c(c);
    // For enums, localize makes self:: into an abstract type, which we don't
    // want
    let self_ty = match c.kind {
        ast_defs::ClassishKind::CenumClass(_) | ast_defs::ClassishKind::Cenum => {
            make_type::class_type(reason::witness(c.name.0.clone()), c.name.1.clone(), vec![])
        }
        ast_defs::ClassishKind::Cinterface
        | ast_defs::ClassishKind::Cclass(_)
        | ast_defs::ClassishKind::Ctrait => {
            let (ty_err_opt, res) = typing_phase::localize_no_subst(env, true, &self_);
            if let Some(err) = &ty_err_opt {
                typing_error_utils::add_typing_error(err, env)
            }
            res
        }
    };
    env::set_self(env, self_id, self_ty.clone());
    env::add_upper_bound(None, env, sn::typehints::THIS, self_ty.clone());
    if c.final_ {
        env::add_lower_bound(None, env, sn::typehints::THIS, self_ty)
    }
}

fn set_parent<Ex, En>(env: &mut Env, c: &aast::Class_<Ex, En>) {
    // In order to type-check a class, we need to know what "parent"
    // refers to. Sometimes people write "parent::", when that happens,
    // we need to know the type of parent.
    match c.extends.first().map(|h| (h, &*h.1)) {
        Some((parent_ty, aast::Hint_::Happly(ast_defs::Id(_, parent_id), _))) => {
            let parent_ty = decl_hint::hint(&env.decl_env, parent_ty);
            env::set_parent(env, parent_id.clone(), parent_ty)
        }
        // The only case where we have more than one parent class is when
        // dealing with interfaces and interfaces cannot use parent.
        Some(_) | None => {}
    }
}

pub fn class_env<Ex, En>(
    origin: Option<decl_counters::Origin>,
    ctx: Arc<Ctx>,
    c: &aast::Class_<Ex, En>,
) -> Env {
    let file = Arc::new(c.name.0.filename().clone());
    let droot = Some(dep::Variant::Type(c.name.1.clone()));
    let mut env = typing_env_types::empty(origin, Some(c.mode), ctx, file, droot);
    env::set_current_module(&mut env, c.module.clone());
    set_self(&mut env, c);
    set_parent(&mut env, c);
    env
}

pub fn typedef_env<Ex, En>(
    origin: Option<decl_counters::Origin>,
    ctx: Arc<Ctx>,
    t: &aast::Typedef<Ex, En>,
) -> Env {
    let t_kind = match &t.assignment {
        aast::TypedefAssignment::SimpleTypeDef(aast::TypedefVisibilityAndHint { vis: _, hint }) => {
            hint
        }
        aast::TypedefAssignment::CaseType(variant, _rest) => &variant.hint,
    };
    let file = Arc::new(t_kind.0.filename().clone());
    let droot = Some(dep::Variant::Type(t.name.1.clone()));
    let env = typing_env_types::empty(origin, Some(t.mode), ctx, file, droot);
    env
}

pub fn gconst_env<Ex, En>(
    origin: Option<decl_counters::Origin>,
    ctx: Arc<Ctx>,
    cst: &aast::Gconst<Ex, En>,
) -> Env {
    let file = Arc::new(cst.name.0.filename().clone());
    let droot = Some(dep::Variant::GConst(cst.name.1.clone()));
    let mut env = typing_env_types::empty(origin, Some(cst.mode), ctx, file, droot);
    env::set_current_module(&mut env, cst.module.clone());
    env
}

pub fn module_env<Ex, En>(
    origin: Option<decl_counters::Origin>,
    ctx: Arc<Ctx>,
    md: &aast::ModuleDef<Ex, En>,
) -> Env {
    let file = Arc::new(md.name.0.filename().clone());
    let droot = Some(dep::Variant::Module(md.name.1.clone()));
    typing_env_types::empty(origin, Some(md.mode), ctx, file, droot)
}
