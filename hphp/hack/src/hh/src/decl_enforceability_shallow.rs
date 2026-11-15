// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_enforceability_shallow.ml`.

use std::sync::Arc;

use oxidized::naming_types::KindOfType;
use oxidized::typechecker_options::TypecheckerOptions;
use pos::BPos;
use ty::decl::ShallowClass;
use ty::decl::Ty;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_enforceability;
use crate::decl_enforceability::ClassOrTypedefResult;
use crate::decl_enforceability::FunKind;
use crate::decl_entry;
use crate::decl_provider::naming_provider_get_type_kind;
use crate::decl_provider_internals;

fn is_typedef(ctx: &Arc<Ctx>, x: &str) -> bool {
    match naming_provider_get_type_kind(ctx, x) {
        Some(KindOfType::TTypedef) => true,
        _ => false,
    }
}

pub struct Provider;

impl decl_enforceability::Provider for Provider {
    type T = Arc<Ctx>;

    type ClassT = Arc<ShallowClass<R>>;

    fn get_tcopt(ctx: &Arc<Ctx>) -> &Arc<TypecheckerOptions> {
        // Provider_context.get_tcopt
        &ctx.tco
    }

    fn get_class(ctx: &Arc<Ctx>, name: &str) -> Option<Arc<ShallowClass<R>>> {
        decl_provider_internals::get_shallow_class(ctx, name)
    }

    fn get_class_or_typedef(
        ctx: &Arc<Ctx>,
        x: &str,
    ) -> Option<ClassOrTypedefResult<Arc<ShallowClass<R>>>> {
        if is_typedef(ctx, x) {
            match decl_entry::to_option(decl_provider_internals::get_typedef_without_pessimise(
                ctx, x,
            )) {
                None => None,
                Some(td) => Some(ClassOrTypedefResult::TypedefResult(td)),
            }
        } else {
            match Self::get_class(ctx, x) {
                None => None,
                Some(cd) => Some(ClassOrTypedefResult::ClassResult(cd)),
            }
        }
    }
}

// module ShallowContextAccess = Decl_enforceability.ShallowContextAccess (Provider)
type ShallowContextAccess = decl_enforceability::ShallowContextAccess<Provider>;

// include Decl_enforceability.Pessimize (ShallowContextAccess)

/// If the return type is not enforceable, turn it into a like type (~ty) otherwise
/// return the original function type. Also add supportdyn<mixed> to the type parameters.
pub fn pessimise_fun_type(
    fun_kind: FunKind,
    this_class: Option<&Arc<ShallowClass<R>>>,
    no_auto_likes: bool,
    cannot_override: bool,
    ctx: &Arc<Ctx>,
    p: &BPos,
    ty: &Ty<R>,
) -> Ty<R> {
    decl_enforceability::pessimize::pessimise_fun_type::<ShallowContextAccess>(
        fun_kind,
        this_class,
        no_auto_likes,
        cannot_override,
        ctx,
        p,
        ty,
    )
}
