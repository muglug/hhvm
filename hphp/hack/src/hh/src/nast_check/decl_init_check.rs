// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the part of `decl/decl_init_check.ml` that works on the AST of a
//! class (the part that works on shallow declarations is in
//! `hackrs/folded_decl_provider`): helpers for checking the initialization of
//! class properties by looking at the declarations of the ancestors.

use std::collections::BTreeSet;
use std::sync::Arc;

use oxidized::ast_defs::Abstraction;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::Visibility;
use oxidized::file_info::Mode;
use oxidized::nast;
use ty::decl::folded::FoldedClass;

use super::attrs;
use super::sn;
use crate::ctx::Ctx;
use crate::ctx::R;

/// Property names: those of the AST, and those of the declarations (which
/// are interned).
pub type Props<'a> = BTreeSet<&'a str>;

/// `"parent::" ^ SN.Members.__construct`
pub const PARENT_INIT_PROP: &str = "parent::__construct";

/// `get_class_add_dep`
fn get_class_add_dep(ctx: &Ctx, name: &str) -> Option<Arc<FoldedClass<R>>> {
    // (`Decl_provider.get_class`)
    crate::ctx::naming_table_lookups::get_class(ctx, name)
}

/// The name of the class a hint is an application of: `Happly ((_, name), _)`.
fn happly_name(hint: &nast::Hint) -> Option<&str> {
    match &*hint.1 {
        nast::Hint_::Happly(nast::Id(_, name), _) => Some(name),
        _ => None,
    }
}

/// `Aast.split_methods`: the constructor of a class (the last one, if there
/// are several).
pub fn constructor(c: &nast::Class_) -> Option<&nast::Method_> {
    c.methods
        .iter()
        .rev()
        .find(|m| m.name.1 == sn::members::__CONSTRUCT)
}

/// If we need to call `parent::__construct`, we treat it as if it were a
/// class variable that needs to be initialized. It's a bit hacky but it
/// works. The idea here is that if the parent needs to be initialized, we add
/// a phony class variable.
fn add_parent_construct<'a>(
    ctx: &Ctx,
    c: &'a nast::Class_,
    props: &mut Props<'a>,
    parent_hint: &nast::Hint,
) {
    if let Some(parent) = happly_name(parent_hint) {
        if let Some(class) = get_class_add_dep(ctx, parent) {
            // `dc_need_init`
            if class.has_concrete_constructor() && constructor(c).is_some() {
                props.insert(PARENT_INIT_PROP);
            }
        }
    }
}

/// `parent`
pub fn parent<'a>(ctx: &Ctx, c: &'a nast::Class_, acc: &mut Props<'a>) {
    if matches!(c.mode, Mode::Mhhi) {
    } else if matches!(c.kind, ClassishKind::Ctrait) {
        // `split_reqs`: `req_extends @ req_this_as`
        for kind in [
            nast::RequireKind::RequireExtends,
            nast::RequireKind::RequireThisAs,
        ] {
            for nast::ClassReq(hint, req_kind) in &c.reqs {
                if *req_kind == kind {
                    add_parent_construct(ctx, c, acc, hint);
                }
            }
        }
    } else if let Some(parent_ty) = c.extends.first() {
        add_parent_construct(ctx, c, acc, parent_ty);
    }
}

fn is_lateinit(cv: &nast::ClassVar) -> bool {
    attrs::mem(sn::user_attributes::LATE_INIT, &cv.user_attributes)
}

/// `prop_may_need_init`
pub fn prop_may_need_init(cv: &nast::ClassVar) -> bool {
    if cv.xhp_attr.is_some() {
        false
    } else if is_lateinit(cv) {
        false
    } else {
        match &cv.type_.1 {
            None => false,
            Some(nast::Hint(_, hint_)) => match &**hint_ {
                nast::Hint_::Hoption(_) | nast::Hint_::Hmixed => false,
                _ => cv.expr.is_none(),
            },
        }
    }
}

/// `own_props`
pub fn own_props<'a>(c: &'a nast::Class_, props: &mut Props<'a>) {
    for cv in &c.vars {
        if prop_may_need_init(cv) {
            props.insert(&cv.id.1);
        }
    }
}

/// `init_not_required_props`
pub fn init_not_required_props<'a>(c: &'a nast::Class_, props: &mut Props<'a>) {
    for cv in &c.vars {
        if !prop_may_need_init(cv) {
            props.insert(&cv.id.1);
        }
    }
}

/// `parent_props`
pub fn parent_props<'a>(ctx: &Ctx, c: &'a nast::Class_, props: &mut Props<'a>) {
    for parent in &c.extends {
        if let Some(parent) = happly_name(parent) {
            if let Some(tc) = get_class_add_dep(ctx, parent) {
                props.extend(tc.deferred_init_members.iter().map(|name| name.as_str()));
            }
        }
    }
}

/// `trait_props`
pub fn trait_props<'a>(ctx: &Ctx, c: &'a nast::Class_, props: &mut Props<'a>) {
    for trait_hint in &c.uses {
        let Some(trait_) = happly_name(trait_hint) else {
            continue;
        };
        let Some(class) = get_class_add_dep(ctx, trait_) else {
            continue;
        };
        // If our current class defines its own constructor, completely ignore
        // the fact that the trait may have had one defined and merge in all of
        // its members.
        // If the curr. class does not have its own constructor, only fold in
        // the trait members if it would not have had its own constructor when
        // defining `dc_deferred_init_members`. See logic in `class_` for
        // Ast_defs.Cclass (Abstract) to see where this deviated for traits.
        let merge = match &class.constructor.elt {
            None => true,
            Some(cstr) if cstr.origin.as_str() != trait_ || cstr.is_abstract() => true,
            Some(_) => constructor(c).is_some(),
        };
        if merge {
            props.extend(class.deferred_init_members.iter().map(|name| name.as_str()));
        }
    }
}

/// `get_private_deferred_init_props`: the private init-requiring props of
/// the class from its NAST.
fn get_private_deferred_init_props(c: &nast::Class_) -> Props<'_> {
    c.vars
        .iter()
        .filter(|cv| prop_may_need_init(cv) && cv.visibility == Visibility::Private)
        .map(|cv| cv.id.1.as_str())
        .collect()
}

/// `private_deferred_init_props`
pub fn private_deferred_init_props(has_own_cstr: bool, c: &nast::Class_) -> Props<'_> {
    match c.kind {
        ClassishKind::Cclass(Abstraction::Abstract) if !has_own_cstr => {
            get_private_deferred_init_props(c)
        }
        ClassishKind::Ctrait => get_private_deferred_init_props(c),
        ClassishKind::Cclass(_)
        | ClassishKind::Cinterface
        | ClassishKind::Cenum
        | ClassishKind::CenumClass(_) => Props::new(),
    }
}

/// `parent_initialized_members`: all members initialized in the parents of
/// `c`, s.t. they should not be readable within `c`'s `__construct` method
/// until _after_ `parent::__construct` has been called.
pub fn parent_initialized_members<'a>(ctx: &Ctx, c: &'a nast::Class_) -> Props<'a> {
    let mut acc = Props::new();
    for parent in &c.extends {
        if let Some(parent) = happly_name(parent) {
            if let Some(class) = get_class_add_dep(ctx, parent) {
                acc.extend(
                    class
                        .props
                        .iter()
                        .filter(|(_, elt)| elt.needs_init())
                        .map(|(name, _)| name.as_str()),
                );
            }
        }
    }
    acc
}
