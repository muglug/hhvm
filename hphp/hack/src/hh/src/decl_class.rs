// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_class.ml`.
//!
//! This modules deals with looking up class members of folded classes.
//! Folded classes do not store type information of their members for storage
//! efficiency, since folded class members pertains to multiple folded classes.
//! Therefore we need to lookup type information for those members from inside
//! shallow classes. This is what this module does.

use std::sync::Arc;
use std::sync::LazyLock;

use hash::IndexMap;
use naming_special_names_rust as sn;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typing_defs_core::ConsistentKind;
use oxidized::typing_defs_flags::ClassEltFlags;
use pos::BPos;
use pos::ToOxidized;
use pos::TypeName;
use ty::decl::FoldedClass;
use ty::decl::FoldedElement;
use ty::decl::SubstContext;
use ty::decl::Ty;
use ty::decl::folded::Constructor;
use ty::decl::ty::FunElt;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_instantiate as inst;
// module Members = Decl_members.Make (Decl_enforceability_shallow.Provider)
use crate::decl_members as members;
use crate::decl_provider_internals;
use crate::decl_utils;
use crate::folded_class::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MemberLookupError {
    MLEShallowClassNotFound,
    MLEMemberNotFound,
}

fn show_member_lookup_error(err: MemberLookupError) -> &'static str {
    match err {
        MemberLookupError::MLEShallowClassNotFound => "Decl_class.MLEShallowClassNotFound",
        MemberLookupError::MLEMemberNotFound => "Decl_class.MLEMemberNotFound",
    }
}

/// Raise an exception when the class element can't be found.
///
/// Note that this exception can be raised in two modes:
///
/// 1. A Provider_context.t was not available (e.g, Zoncolan execution) and the
///    element was not in the member heaps. A bug in decling or invalidation has
///    occurred, potentially due to files being changed on disk while Hack was
///    decling. No [member_lookup_error] is available, because we didn't do
///    a lazy member lookup.
/// 2. A Provider_context.t was available (regular Hack execution with eviction),
///    the element was not in the member heap, so we tried falling back to disk.
///    However, the element could not be found in the origin class. This might be
///    due to an inconsistent decl heap (e.g., due to files being changed on disk
///    while Hack was decling) or because the file containing the element was
///    changed while type checking. In this case, we have a
///    [member_lookup_error] available.
///
/// `exception Decl_heap_elems_bug of string` is a panic: nothing in the
/// typechecker handles it.
fn raise_decl_heap_elems_bug(
    err: Option<MemberLookupError>,
    child_class_name: &str,
    elt_origin: &str,
    member_name: &str,
) -> ! {
    let data = format!(
        "could not find {}::{} (inherited by {}) ({})",
        elt_origin,
        member_name,
        child_class_name,
        err.map(show_member_lookup_error)
            .unwrap_or("no lazy member lookup performed")
    );
    // `Hh_logger.log` and `Hack_event_logger.decl_consistency_bug` only log.
    panic!("Decl_class.Decl_heap_elems_bug({:?})", data)
}

fn unpack_member_lookup_result<A>(
    child_class_name: &str,
    elt_origin: &str,
    member_name: &str,
    res: Option<Result<A, MemberLookupError>>,
) -> A {
    let res = match res {
        None => Err(None),
        Some(res) => res.map_err(Some),
    };
    match res {
        Ok(a) => a,
        Err(err) => raise_decl_heap_elems_bug(err, child_class_name, elt_origin, member_name),
    }
}

fn apply_substs(
    substs: &IndexMap<TypeName, SubstContext<R>>,
    class_context: TypeName,
    (pos, ty): (BPos, Ty<R>),
) -> (BPos, Ty<R>) {
    match substs.get(&class_context) {
        None => (pos, ty),
        Some(SubstContext {
            subst,
            class_context: next_class_context,
            from_req_extends: _,
        }) => apply_substs(
            substs,
            *next_class_context,
            (pos, inst::instantiate(subst, &ty)),
        ),
    }
}

fn element_to_class_elt(pty: Lazy<(BPos, Ty<R>)>, elt: &FoldedElement) -> ClassElt {
    let FoldedElement {
        flags: ce_flags,
        origin: ce_origin,
        visibility: ce_visibility,
        deprecated: ce_deprecated,
        sealed_allowlist: ce_sealed_allowlist,
        overlapping_tparams: ce_overlapping_tparams,
        package_requirement: ce_package_requirement,
    } = elt;
    let (ce_pos, ce_type) = {
        let pty2 = Arc::clone(&pty);
        (
            lazy(move || PosOrDecl::from(LazyLock::force(&pty2).0.clone())),
            lazy(move || LazyLock::force(&pty).1.clone()),
        )
    };
    ClassElt {
        ce_visibility: ce_visibility.clone().to_oxidized(),
        ce_origin: ce_origin.as_str().to_string(),
        ce_type,
        ce_deprecated: ce_deprecated.map(|x| String::from_utf8_lossy(x.as_bytes()).to_string()),
        ce_pos,
        ce_flags: *ce_flags,
        ce_sealed_allowlist: (ce_sealed_allowlist.as_ref())
            .map(|s| s.iter().map(|x| x.as_str().to_string()).collect()),
        ce_overlapping_tparams: (ce_overlapping_tparams.as_ref())
            .map(|s| s.iter().map(|x| x.as_str().to_string()).collect()),
        ce_package_requirement: ce_package_requirement.clone(),
    }
}

fn fun_elt_to_ty(fe: FunElt<R>) -> (BPos, Ty<R>) {
    (fe.pos, fe.ty)
}

/// `Decl_store.lookup_or ~bypass kind x f`, where `bypass` is false without
/// a context and `not (Typechecker_options.populate_member_heaps tcopt)`
/// with one.
///
/// The member heaps of `Decl_store` hold what `f` computes (class folding
/// puts it there, and `lookup_or` does when it is missing): they are a
/// cache of `f x`. The Rust decl layer has no such heap (the member stores
/// of hackrs's `ShallowDeclStore` hold the types the members were declared
/// with, not the result of `Decl_members.build_*`), so the result is
/// always `f x`, as it is in the OCaml when `bypass` is true.
fn lookup_store_or<K, V>(_ctx: Option<&Arc<Ctx>>, x: K, f: impl FnOnce(K) -> V) -> V {
    f(x)
}

fn find_method_in_shallow_class(
    ctx: &Arc<Ctx>,
    is_static: bool,
    elt_origin: &str,
    no_auto_likes: bool,
    sm_name: &str,
) -> Result<FunElt<R>, MemberLookupError> {
    match decl_provider_internals::get_shallow_class(ctx, elt_origin) {
        None => Err(MemberLookupError::MLEShallowClassNotFound),
        Some(class_) => {
            let methods = if is_static {
                &class_.static_methods
            } else {
                &class_.methods
            };
            match (methods.iter()).find(|m| m.name.id_ref().as_str() == sm_name) {
                None => Err(MemberLookupError::MLEMemberNotFound),
                Some(sm) => Ok(members::build_method(ctx, Some(&class_), no_auto_likes, sm)),
            }
        }
    }
}

fn find_method(
    ctx: Option<&Arc<Ctx>>,
    child_class_name: &str,
    no_auto_likes: bool,
    x: (&str, &str),
) -> (BPos, Ty<R>) {
    let fun_elt = lookup_store_or(ctx, x, |x| {
        let (elt_origin, sm_name) = x;
        unpack_member_lookup_result(
            child_class_name,
            elt_origin,
            sm_name,
            ctx.map(|ctx| {
                find_method_in_shallow_class(ctx, false, elt_origin, no_auto_likes, sm_name)
            }),
        )
    });
    fun_elt_to_ty(fun_elt)
}

fn find_static_method(
    ctx: Option<&Arc<Ctx>>,
    child_class_name: &str,
    no_auto_likes: bool,
    x: (&str, &str),
) -> (BPos, Ty<R>) {
    let fun_elt = lookup_store_or(ctx, x, |x| {
        let (elt_origin, sm_name) = x;
        unpack_member_lookup_result(
            child_class_name,
            elt_origin,
            sm_name,
            ctx.map(|ctx| {
                find_method_in_shallow_class(ctx, true, elt_origin, no_auto_likes, sm_name)
            }),
        )
    });
    fun_elt_to_ty(fun_elt)
}

fn find_property_in_shallow_class(
    ctx: &Arc<Ctx>,
    elt_origin: &str,
    sp_name: &str,
) -> Result<Ty<R>, MemberLookupError> {
    match decl_provider_internals::get_shallow_class(ctx, elt_origin) {
        None => Err(MemberLookupError::MLEShallowClassNotFound),
        Some(class_) => {
            match (class_.props.iter()).find(|prop| prop.name.id_ref().as_str() == sp_name) {
                None => Err(MemberLookupError::MLEMemberNotFound),
                Some(sp) => Ok(members::build_property(ctx, Some(&class_), sp)),
            }
        }
    }
}

fn find_property(
    ctx: Option<&Arc<Ctx>>,
    child_class_name: &str,
    x: (&str, &str),
) -> (BPos, Ty<R>) {
    let ty = lookup_store_or(ctx, x, |x| {
        let (elt_origin, sp_name) = x;
        unpack_member_lookup_result(
            child_class_name,
            elt_origin,
            sp_name,
            ctx.map(|ctx| find_property_in_shallow_class(ctx, elt_origin, sp_name)),
        )
    });
    (decl_utils::get_pos(&ty), ty)
}

fn find_static_property_in_shallow_class(
    ctx: &Arc<Ctx>,
    elt_origin: &str,
    sp_name: &str,
) -> Result<Ty<R>, MemberLookupError> {
    match decl_provider_internals::get_shallow_class(ctx, elt_origin) {
        None => Err(MemberLookupError::MLEShallowClassNotFound),
        Some(class_) => {
            match (class_.static_props.iter())
                .find(|prop| prop.name.id_ref().as_str() == sp_name)
            {
                None => Err(MemberLookupError::MLEMemberNotFound),
                Some(sp) => Ok(members::build_property(ctx, Some(&class_), sp)),
            }
        }
    }
}

fn find_static_property(
    ctx: Option<&Arc<Ctx>>,
    child_class_name: &str,
    x: (&str, &str),
) -> (BPos, Ty<R>) {
    let ty = lookup_store_or(ctx, x, |x| {
        let (elt_origin, sp_name) = x;
        unpack_member_lookup_result(
            child_class_name,
            elt_origin,
            sp_name,
            ctx.map(|ctx| find_static_property_in_shallow_class(ctx, elt_origin, sp_name)),
        )
    });
    (decl_utils::get_pos(&ty), ty)
}

fn find_constructor_in_shallow_class(
    ctx: &Arc<Ctx>,
    elt_origin: &str,
) -> Result<FunElt<R>, MemberLookupError> {
    match decl_provider_internals::get_shallow_class(ctx, elt_origin) {
        None => Err(MemberLookupError::MLEShallowClassNotFound),
        Some(class_) => match &class_.constructor {
            None => Err(MemberLookupError::MLEMemberNotFound),
            Some(method_) => Ok(members::build_constructor(method_)),
        },
    }
}

fn find_constructor(
    ctx: Option<&Arc<Ctx>>,
    child_class_name: &str,
    elt_origin: &str,
) -> FunElt<R> {
    lookup_store_or(ctx, elt_origin, |elt_origin| {
        unpack_member_lookup_result(
            child_class_name,
            elt_origin,
            sn::members::__CONSTRUCT,
            ctx.map(|ctx| find_constructor_in_shallow_class(ctx, elt_origin)),
        )
    })
}

/// The OCaml is given `dc.dc_substs`. The lazy value has to own them: it is
/// given the folded class they are part of.
fn map_element(
    dc: &Arc<FoldedClass<R>>,
    find: impl FnOnce((&str, &str)) -> (BPos, Ty<R>) + Send + 'static,
    name: &str,
    elt: &FoldedElement,
) -> ClassElt {
    let pty = {
        let dc = Arc::clone(dc);
        let elt_origin = elt.origin;
        let name = name.to_string();
        lazy(move || {
            let pty = find((elt_origin.as_str(), &name));
            apply_substs(&dc.substs, elt_origin, pty)
        })
    };
    element_to_class_elt(pty, elt)
}

/// Lookup the type signature of a class property.
///
/// [Decl_defs.element] only points to where the type signature of an element
/// can be found (i.e. in which class). This function looks up the actual type
/// signature and returns it, together with the original metadata.
///
/// If no [Provider_context.t] is passed or it cannot be found
/// a [Decl_heap_elems_bug] exception is raised.
///
/// Note that the lookup is lazy. The type signature is wrapped in a lazy value.
/// The lookup will only happen when you try to force the lazy value. (See the
/// definition of [Typing_defs.class_elt].)
pub fn lookup_property_type_lazy(
    ctx: Option<&Arc<Ctx>>,
    dc: &Arc<FoldedClass<R>>,
    name: &str,
    elt: &FoldedElement,
) -> ClassElt {
    let ctx = ctx.cloned();
    let child_class_name = dc.name;
    map_element(
        dc,
        move |x| find_property(ctx.as_ref(), child_class_name.as_str(), x),
        name,
        elt,
    )
}

/// Lookup the type of a class static property.
///
/// See [lookup_property_type_lazy] for more information.
pub fn lookup_static_property_type_lazy(
    ctx: Option<&Arc<Ctx>>,
    dc: &Arc<FoldedClass<R>>,
    name: &str,
    elt: &FoldedElement,
) -> ClassElt {
    let ctx = ctx.cloned();
    let child_class_name = dc.name;
    map_element(
        dc,
        move |x| find_static_property(ctx.as_ref(), child_class_name.as_str(), x),
        name,
        elt,
    )
}

/// Lookup the type of a class method.
///
/// See [lookup_property_type_lazy] for more information.
pub fn lookup_method_type_lazy(
    ctx: Option<&Arc<Ctx>>,
    dc: &Arc<FoldedClass<R>>,
    name: &str,
    element: &FoldedElement,
) -> ClassElt {
    let ctx = ctx.cloned();
    let child_class_name = dc.name;
    let no_auto_likes = element.flags.contains(ClassEltFlags::NO_AUTO_LIKES);
    map_element(
        dc,
        move |x| find_method(ctx.as_ref(), child_class_name.as_str(), no_auto_likes, x),
        name,
        element,
    )
}

/// Lookup the type of a class static method.
///
/// See [lookup_property_type_lazy] for more information.
pub fn lookup_static_method_type_lazy(
    ctx: Option<&Arc<Ctx>>,
    dc: &Arc<FoldedClass<R>>,
    name: &str,
    element: &FoldedElement,
) -> ClassElt {
    let ctx = ctx.cloned();
    let child_class_name = dc.name;
    let no_auto_likes = element.flags.contains(ClassEltFlags::NO_AUTO_LIKES);
    map_element(
        dc,
        move |x| find_static_method(ctx.as_ref(), child_class_name.as_str(), no_auto_likes, x),
        name,
        element,
    )
}

/// Lookup the type of a class constructor.
///
/// See [lookup_property_type_lazy] for more information.
///
/// The OCaml is given `dc_substs` and `dc_construct`. The lazy value has to
/// own the substitutions: this is given the folded class they are part of
/// (`dc.substs`, and `dc.constructor` for `dc_construct`).
pub fn lookup_constructor_lazy(
    ctx: Option<&Arc<Ctx>>,
    child_class_name: &str,
    dc: &Arc<FoldedClass<R>>,
) -> (Option<ClassElt>, ConsistentKind) {
    let Constructor { elt, consistency } = &dc.constructor;
    match (elt, *consistency) {
        (None, consistent) => (None, consistent),
        (Some(elt), consistent) => {
            let pty = {
                let ctx = ctx.cloned();
                let child_class_name = child_class_name.to_string();
                let dc = Arc::clone(dc);
                let elt_origin = elt.origin;
                lazy(move || {
                    let pty = fun_elt_to_ty(find_constructor(
                        ctx.as_ref(),
                        &child_class_name,
                        elt_origin.as_str(),
                    ));
                    apply_substs(&dc.substs, elt_origin, pty)
                })
            };
            let class_elt = element_to_class_elt(pty, elt);
            (Some(class_elt), consistent)
        }
    }
}
