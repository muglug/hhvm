// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_env.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::decl_reference::DeclReference;
use oxidized::file_info;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typechecker_options::TypecheckerOptions;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::typing_deps::dep;
use crate::typing_pessimisation_deps;

/// `Decl_defs.decl_class_type`: the folded class, as the decl stores keep it.
pub type DeclClassType = Arc<ty::decl::FoldedClass<R>>;

#[derive(Clone)]
pub struct Env {
    pub mode: file_info::Mode,
    /// `Typing_deps.Dep.dependent Typing_deps.Dep.variant option`
    pub droot: Option<dep::Variant>,
    /// The child/member of [droot] currently under consideration.
    /// Used for fine-grained dependency tracking.
    pub droot_member: Option<typing_pessimisation_deps::DependentMember>,
    pub ctx: Arc<Ctx>,
}

fn root_decl_reference(env: &Env) -> Option<DeclReference> {
    env.droot.as_ref().map(dep::to_decl_reference)
}

pub fn make_decl_pos(env: &Env, pos: &Pos) -> PosOrDecl {
    // TODO: fail if root_decl_reference returns None
    crate::pos_or_decl::make_decl_pos_of_option(pos, root_decl_reference(env))
}

pub fn make_decl_posed<A>(env: &Env, posed: (Pos, A)) -> (PosOrDecl, A) {
    // TODO: fail if root_decl_reference returns None
    crate::positioned::make_for_decl_of_option(posed, root_decl_reference(env))
}

pub fn tcopt(env: &Env) -> Arc<TypecheckerOptions> {
    // `Provider_context.get_tcopt`
    Arc::clone(&env.ctx.tco)
}

/// `Decl_store.class_entries S_map.t`
pub type ClassCache = im::OrdMap<String, crate::decl_store::ClassEntries>;

/// Auxiliary constant fallback function that returns [None].
pub fn no_fallback(_: &Env, _: &str) -> Option<DeclClassType> {
    None
}

/// Lookup the class from the cache.
///
/// If [shmem_fallback] and the class is not in the cache, look for the
/// class in the classes heap.
///
/// If the class is not in the cache, and [shmem_fallback] is false or the
/// class is not in the classes heap, call and return [fallback].
///
/// If a class is returned, add a dependency to the class.
pub fn get_class_and_add_dep(
    cache: &ClassCache,
    shmem_fallback: bool,
    fallback: impl Fn(&Env, &str) -> Option<DeclClassType>,
    env: &Env,
    x: &str,
) -> Option<DeclClassType> {
    let res: Option<DeclClassType> = match cache.get(x) {
        Some(c) => Some(c.0.clone()),
        None if shmem_fallback => (crate::decl_store::get().get_class)(x),
        None => None,
    };
    match res {
        Some(c) => Some(c),
        None => fallback(env, x),
    }
}
