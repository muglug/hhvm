// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_missing_override_attribute.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).
//!
//! (linting is not fanout-aware, so it's safe to use non-dep-aware
//! functions here)

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::typing_defs_core::CeVisibility;

use crate::ctx::Ctx;
use crate::decl_entry;
use crate::decl_provider;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::ClassElt;

fn has_override_attribute(m: &tast::Method_) -> bool {
    m.user_attributes
        .0
        .iter()
        .any(|ua| ua.name.1 == sn::user_attributes::OVERRIDE)
}

fn is_interface(c: &cls::T) -> bool {
    crate::ast_defs::is_c_interface(cls::kind(c))
}

/// Do not emit an error for classes implementing an interface method, but do
/// emit errors for interfaces overriding interface methods, classes overriding
/// class methods, classes overriding trait methods, etc.
fn both_are_or_are_not_interfaces(c1: &cls::T, c2: &cls::T) -> bool {
    is_interface(c1) == is_interface(c2)
}

/// Return true only if 1) the given method is public or protected, or 2) the
/// given ancestor is a trait (since a user of the trait will inherit private
/// trait methods)
fn should_check_ancestor_method(ancestor_class: &cls::T, ancestor_method: &ClassElt) -> bool {
    if crate::ast_defs::is_c_trait(cls::kind(ancestor_class)) {
        true
    } else {
        match ancestor_method.ce_visibility {
            CeVisibility::Vpublic
            | CeVisibility::Vprotected(_)
            | CeVisibility::Vinternal(_)
            | CeVisibility::VprotectedInternal { .. } => true,
            CeVisibility::Vprivate(_) => false,
        }
    }
}

fn parent_hint_name(aast::Hint(_p, hint): &aast::Hint) -> Option<&str> {
    match &**hint {
        aast::Hint_::Happly(name, _) => Some(&name.1),
        aast::Hint_::Hrefinement(hint, _) => parent_hint_name(hint),
        aast::Hint_::Hprim(_)
        | aast::Hint_::Hoption(_)
        | aast::Hint_::Hlike(_)
        | aast::Hint_::Hfun(_)
        | aast::Hint_::Htuple(_)
        | aast::Hint_::HclassPtr(..)
        | aast::Hint_::Hshape(_)
        | aast::Hint_::Haccess(..)
        | aast::Hint_::Hsoft(_)
        | aast::Hint_::Hmixed
        | aast::Hint_::Hwildcard
        | aast::Hint_::Hnonnull
        | aast::Hint_::Habstr(_)
        | aast::Hint_::HvecOrDict(..)
        | aast::Hint_::Hthis
        | aast::Hint_::Hdynamic
        | aast::Hint_::Hnothing
        | aast::Hint_::Hunion(_)
        | aast::Hint_::Hintersection(_)
        | aast::Hint_::HfunContext(_)
        | aast::Hint_::Hvar(_) => None,
    }
}

fn ancestors_providing_methods(c: &tast::Class_) -> Vec<&str> {
    let reqs = c.reqs.iter().filter_map(|aast::ClassReq(hint, req_kind)| match req_kind {
        // We only care if this is a parent that is a class.
        aast::RequireKind::RequireExtends => Some(hint),
        aast::RequireKind::RequireImplements
        | aast::RequireKind::RequireClass
        | aast::RequireKind::RequireThisAs => None,
    });
    c.extends
        .iter()
        .chain(c.implements.iter())
        .chain(c.uses.iter())
        .chain(reqs)
        .filter_map(parent_hint_name)
        .collect()
}

fn check_methods(ctx: &Arc<Ctx>, c: &tast::Class_, cls: &cls::T, static_: bool) {
    let ancestor_names = ancestors_providing_methods(c);
    let get_method = if static_ {
        cls::get_smethod
    } else {
        cls::get_method
    };
    let (_, static_methods, c_methods) = crate::aast::split_methods(&c.methods);
    let methods = if static_ { static_methods } else { c_methods };
    // For each method of the shallow class...
    methods
        .into_iter()
        // ... which doesn't have the override attribute,
        .filter(|m| !has_override_attribute(m))
        // ... and is not the constructor,
        .filter(|m| m.name.1 != sn::members::__CONSTRUCT)
        .for_each(|m| {
            let (p, mid) = (&m.name.0, &m.name.1);
            let matching_ancestor = ancestor_names
                .iter()
                // inspect each ancestor, and if it has a method with the same name,
                // and either that method is non-private or the ancestor is a trait,
                .filter_map(|c| {
                    let ancestor = decl_entry::to_option(decl_provider::get_class(None, ctx, c))?;
                    let m = match get_method(&ancestor, mid) {
                        None => None,
                        Some(ancestor_method) => {
                            if should_check_ancestor_method(&ancestor, &ancestor_method) {
                                Some(ancestor_method)
                            } else {
                                None
                            }
                        }
                    }?;
                    // get the class which defined that method,
                    decl_entry::to_option(decl_provider::get_class(None, ctx, &m.ce_origin))
                })
                .collect::<Vec<_>>()
                .into_iter()
                // as long as it and this class are of the same kind.
                .filter(|a| both_are_or_are_not_interfaces(cls, a))
                // If such a class exists...
                .next();
            match matching_ancestor {
                Some(ancestor) => {
                    // ...then this method should have had the override attribute.
                    let first_attr_pos = m.user_attributes.0.first().map(|ua| &ua.name.0);
                    crate::lints_diagnostics::missing_override_attribute(
                        &m.span,
                        first_attr_pos,
                        *p,
                        &cls::name(&ancestor),
                        mid,
                    )
                }
                None => {}
            }
        })
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        let cid = &c.name.1;
        let ctx = tast_env::get_ctx(env);
        match decl_provider::get_class(None, &ctx, cid) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            decl_entry::T::Found(cls) => {
                check_methods(&ctx, c, &cls, false);
                check_methods(&ctx, c, &cls, true)
            }
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
