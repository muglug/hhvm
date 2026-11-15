// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/folded_class.ml`. See `hh/PORTING.md`.
//!
//! The class API of the typechecker (`Cls` in the OCaml typing code): a view
//! of a folded class (`ty::decl::FoldedClass`) that includes all inherited
//! members and their types.
//!
//! A folded class does not hold the types of its methods and properties, only
//! the class each of them comes from (`ty::decl::FoldedElement`). The type of
//! a member is found in the shallow declaration of that class and brought to
//! the folded class by the substitutions the folded class recorded
//! (`FoldedClass::substs`). The OCaml does this in `Decl_class`, through
//! `Decl_members`; hackrs has no equivalent (its `ShallowDeclStore` gives the
//! type a member was declared with, nothing more).
//!
//! `Folded_class` is built on `crate::typing_class_types`, `crate::decl_counters`,
//! `crate::decl_class`, `crate::decl_members` and `crate::decl_inherit`.
//!
//! None of the functions here records a dependency: as in the OCaml, that is
//! done by the functions of `Typing_env` that wrap them.

use std::fmt;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::LazyLock;

use hash::IndexMap;
use naming_special_names_rust as sn;
use oxidized::aast_defs::PackageMembership;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::XhpEnumValue;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typing_defs::PackageRequirement;
use oxidized::typing_defs_core::CeVisibility;
use oxidized::typing_defs_core::ConsistentKind;
use oxidized::typing_defs_flags::ClassEltFlags;
use pos::BPos;
use pos::ClassConstName;
use pos::MethodName;
use pos::PropName;
use pos::ToOxidized;
use pos::TypeConstName;
use pos::TypeName;
use ty::decl::ClassConst;
use ty::decl::EnumType;
use ty::decl::Requirement;
use ty::decl::Tparam;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::TypeConst;
use ty::decl::folded::ConstraintRequirement;
use ty::decl_error::DeclError;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_class;
use crate::decl_counters;
use crate::decl_counters::SubdeclKind;
use crate::decl_inherit;
use crate::decl_provider_internals;
use crate::decl_utils;
use crate::typing_class_types::ClassT as TypingClassT;

/// `'a Lazy.t`: computed the first time it is dereferenced, and shared by its
/// clones.
pub type Lazy<A> = Arc<LazyLock<A, Box<dyn FnOnce() -> A + Send>>>;

/// `lazy (f ())`
pub fn lazy<A>(f: impl FnOnce() -> A + Send + 'static) -> Lazy<A> {
    Arc::new(LazyLock::new(Box::new(f)))
}

/// `Typing_defs.class_elt`: a method or a property of a class, inherited ones
/// included.
///
/// `oxidized::typing_defs::ClassElt` is not it: its type is an oxidized type
/// that has to be there when the element is built, whereas the type of an
/// element is a decl type (`ty::decl::Ty`) that is only looked up when it is
/// asked for (`Lazy.force ce.ce_type` is `&*ce.ce_type`, or
/// `LazyLock::force(&ce.ce_type)`).
#[derive(Clone)]
pub struct ClassElt {
    pub ce_visibility: CeVisibility,
    pub ce_type: Lazy<Ty<R>>,
    /// identifies the class from which this elt originates
    pub ce_origin: String,
    pub ce_deprecated: Option<String>,
    /// pos of the type of the elt
    pub ce_pos: Lazy<PosOrDecl>,
    pub ce_flags: ClassEltFlags,
    pub ce_sealed_allowlist: Option<im::OrdSet<String>>,
    pub ce_overlapping_tparams: Option<im::OrdSet<String>>,
    pub ce_package_requirement: Option<PackageRequirement>,
}

impl fmt::Debug for ClassElt {
    // `[@@deriving show]` forces the lazy values.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ClassElt")
            .field("ce_visibility", &self.ce_visibility)
            .field("ce_type", &**self.ce_type)
            .field("ce_origin", &self.ce_origin)
            .field("ce_deprecated", &self.ce_deprecated)
            .field("ce_pos", &**self.ce_pos)
            .field("ce_flags", &self.ce_flags)
            .field("ce_sealed_allowlist", &self.ce_sealed_allowlist)
            .field("ce_overlapping_tparams", &self.ce_overlapping_tparams)
            .field("ce_package_requirement", &self.ce_package_requirement)
            .finish()
    }
}

// This entire file is "private". Its sole consumer is Decl_provider.ml.

pub type ClassT = TypingClassT;

pub fn make(x: TypingClassT) -> ClassT {
    x
}

/// This type "t" is what all APIs operate upon. It includes
/// a "decl option". This provides context about how the specified
/// class_t was fetched in the first place. It's used solely for telemetry,
/// so that telemetry about APIs can be easily correlated with telemetry
/// to the original call to the [get] which fetched the class_t in the
/// first place.
///
/// It also references the provider context that was used to query the class_t,
/// as it might be needed when querying its members when the shallow decl where it
/// was defines is evicted. For Zoncolan, this Provider_context.t is not
/// available, as Zoncolan doesn't support eviction.
#[derive(Clone)]
pub struct T(
    pub Option<decl_counters::Decl>,
    pub ClassT,
    /// An `Rc` handle that the thread shares (see `Decl_provider.get_class`),
    /// so that copying a `T` does not write the reference count of the
    /// context, which all the threads share.
    pub Option<Rc<Arc<Ctx>>>,
);

impl fmt::Debug for T {
    // `[@@deriving show]`, with the first and the last components opaque.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("")
            .field(&format_args!("<opaque>"))
            .field(&self.1)
            .field(&format_args!("<opaque>"))
            .finish()
    }
}

/// `S_map.bindings`: the bindings of a map of the folded class, in increasing
/// order of the keys.
fn bindings<K: AsRef<str>, V>(m: &IndexMap<K, V>) -> Vec<(&str, &V)> {
    let mut l: Vec<(&str, &V)> = m.iter().map(|(k, v)| (k.as_ref(), v)).collect();
    l.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
    l
}

// module ApiShallow

pub fn abstract_(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Abstract, || {
        let TypingClassT(c, _) = t;
        // `dc_abstract` is `Decl_folded_class.class_is_abstract`
        c.is_abstract()
    })
}

pub fn final_(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Final, || {
        let TypingClassT(c, _) = t;
        c.is_final
    })
}

pub fn has_const_attribute(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Const, || {
        let TypingClassT(c, _) = t;
        c.is_const
    })
}

pub fn kind(t: &T) -> ClassishKind {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Kind, || {
        let TypingClassT(c, _) = t;
        c.kind
    })
}

pub fn allow_multiple_instantiations(t: &T) -> bool {
    let T(_decl, TypingClassT(c, _), _ctx) = t;
    c.allow_multiple_instantiations
}

pub fn is_xhp(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::IsXhp, || {
        let TypingClassT(c, _) = t;
        c.is_xhp
    })
}

pub fn name(t: &T) -> String {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Name, || {
        let TypingClassT(c, _) = t;
        c.name.as_str().to_string()
    })
}

pub fn pos(t: &T) -> PosOrDecl {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Pos, || {
        let TypingClassT(c, _) = t;
        PosOrDecl::from(c.pos.clone())
    })
}

/// `Pos_or_decl.is_hhi (pos t)`, without converting the position of the
/// declaration (which allocates) only to read the prefix of its file.
pub fn pos_is_hhi(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Pos, || {
        let TypingClassT(c, _) = t;
        pos::Pos::is_hhi(&c.pos)
    })
}

pub fn tparams(t: &T) -> Vec<Tparam<R, Ty<R>>> {
    tparams_ref(t).to_vec()
}

/// [`tparams`], borrowed from the class: OCaml returns the list of the class
/// itself, and most callers only read it.
pub fn tparams_ref(t: &T) -> &[Tparam<R, Ty<R>>] {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Tparams, || {
        let TypingClassT(c, _) = t;
        &c.tparams[..]
    })
}

pub fn enum_type(t: &T) -> Option<EnumType<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::EnumType, || {
        let TypingClassT(c, _) = t;
        c.enum_type.clone()
    })
}

pub fn xhp_enum_values(t: &T) -> im::OrdMap<String, Vec<XhpEnumValue>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::XhpEnumValues, || {
        let TypingClassT(c, _) = t;
        (c.xhp_enum_values.iter())
            .map(|(k, v)| {
                (
                    k.as_str().to_string(),
                    v.iter()
                        .map(|x| x.clone().to_oxidized())
                        .collect::<Vec<_>>(),
                )
            })
            .collect()
    })
}

pub fn xhp_marked_empty(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::XhpMarkedEmpty, || {
        let TypingClassT(c, _) = t;
        c.xhp_marked_empty
    })
}

pub fn sealed_whitelist(t: &T) -> Option<im::OrdSet<String>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::SealedWhitelist, || {
        let TypingClassT(c, _) = t;
        (c.sealed_whitelist.as_ref()).map(|s| s.iter().map(|x| x.as_str().to_string()).collect())
    })
}

pub fn get_docs_url(t: &T) -> Option<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::DocsUrl, || {
        let TypingClassT(c, _) = t;
        c.docs_url.clone()
    })
}

pub fn get_module(t: &T) -> Option<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Module, || {
        let TypingClassT(c, _) = t;
        c.module.as_ref().map(|m| m.id_ref().as_str().to_string())
    })
}

pub fn get_package(t: &T) -> Option<PackageMembership> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Module, || {
        let TypingClassT(c, _) = t;
        c.package.clone()
    })
}

pub fn internal(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Internal, || {
        let TypingClassT(c, _) = t;
        c.is_internal
    })
}

pub fn tests_bypass_visibility(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::TestsBypassVisibility, || {
        let TypingClassT(c, _) = t;
        c.tests_bypass_visibility
    })
}

pub fn allow_unchecked_enum_values(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllowUncheckedEnumValues, || {
        let TypingClassT(c, _) = t;
        c.allow_unchecked_enum_values
    })
}

pub fn is_module_level_trait(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::IsModuleLevelTrait, || {
        let TypingClassT(c, _) = t;
        c.is_module_level_trait
    })
}

pub fn decl_errors(t: &T) -> Vec<DeclError<BPos>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::DeclErrors, || {
        let TypingClassT(c, _) = t;
        c.decl_errors.to_vec()
    })
}

pub fn get_support_dynamic_type(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::SupportDynamicType, || {
        let TypingClassT(c, _) = t;
        c.support_dynamic_type
    })
}

// module ApiLazy

/// Direct use of `construct` will not register a dependency. You probably
/// want to use `Typing_env.get_construct` instead
pub fn construct(t: &T) -> (Option<ClassElt>, ConsistentKind) {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Construct, || {
        let TypingClassT(cls, members) = t;
        let mut construct = members.construct.lock().unwrap();
        match &*construct {
            Some(x) => x.clone(),
            None => {
                let x = decl_class::lookup_constructor_lazy(ctx.as_deref(), cls.name.as_str(), cls);
                *construct = Some(x.clone());
                x
            }
        }
    })
}

pub fn need_init(t: &T) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::NeedInit, || {
        let TypingClassT(c, _) = t;
        // `dc_need_init` is `has_concrete_cstr` in `Decl_folded_class.class_decl`
        c.has_concrete_constructor()
    })
}

pub fn get_ancestor(t: &T, ancestor: &str) -> Option<Ty<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::GetAncestor(ancestor), || {
        let TypingClassT(c, _) = t;
        c.ancestors.get(&TypeName(crate::ctx::symbol(ancestor))).cloned()
    })
}

pub fn has_ancestor(t: &T, ancestor: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::HasAncestor(ancestor), || {
        let TypingClassT(c, _) = t;
        c.ancestors.contains_key(&TypeName(crate::ctx::symbol(ancestor)))
    })
}

pub fn requires_ancestor(t: &T, ancestor: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(
        decl.as_ref(),
        SubdeclKind::RequiresAncestor(ancestor),
        || {
            let TypingClassT(c, _) = t;
            c.req_ancestors_extends.contains(&TypeName(crate::ctx::symbol(ancestor)))
        },
    )
}

/// Direct use of `get_const` will not register a dependency. You probably
/// want to use `Typing_env.get_const` instead
pub fn get_const(t: &T, id: &str) -> Option<ClassConst<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::GetConst(id), || {
        let TypingClassT(c, _) = t;
        c.consts.get(&ClassConstName(crate::ctx::symbol(id))).cloned()
    })
}

pub fn has_const(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::HasConst(id), || {
        let TypingClassT(c, _) = t;
        c.consts.contains_key(&ClassConstName(crate::ctx::symbol(id)))
    })
}

/// Direct use of `get_typeconst` will not register a dependency. You
/// probably want to use `Typing_env.get_typeconst` instead
pub fn get_typeconst(t: &T, id: &str) -> Option<TypeConst<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::GetTypeconst(id), || {
        let TypingClassT(c, _) = t;
        c.type_consts.get(&TypeConstName(crate::ctx::symbol(id))).cloned()
    })
}

pub fn has_typeconst(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::HasTypeconst(id), || {
        let TypingClassT(c, _) = t;
        c.type_consts.contains_key(&TypeConstName(crate::ctx::symbol(id)))
    })
}

/// Return the enforceability of the typeconst with the given name. A
/// typeconst is enforceable if it was declared with the <<__Enforceable>>
/// attribute, or if it overrides some ancestor typeconst with that attribute.
/// Only enforceable typeconsts may be used in [is] or [as] expressions. The
/// overriding behavior makes this expensive to compute in shallow decl, which
/// is why this separate accessor is provided (rather than making this
/// information available in the [ttc_enforceable] field, whose semantics
/// differ between legacy and shallow decl due to the perf cost in shallow).
pub fn get_typeconst_enforceability(t: &T, id: &str) -> Option<(PosOrDecl, bool)> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(
        decl.as_ref(),
        SubdeclKind::GetTypeconstEnforceability(id),
        || {
            let TypingClassT(c, _) = t;
            (c.type_consts.get(&TypeConstName(crate::ctx::symbol(id)))).map(|t| {
                // `ttc_enforceable`: `ty::decl::ty::Enforceable` is the position
                // of the attribute, if there is one.
                match &t.enforceable.0 {
                    Some(pos) => (PosOrDecl::from(pos.clone()), true),
                    None => (Pos::NONE, false),
                }
            })
        },
    )
}

/// Direct use of `get_prop` will not register a dependency. You probably
/// want to use `Typing_env.get_prop` instead
pub fn get_prop(t: &T, id: &str) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::GetProp(id), || {
        let TypingClassT(c, members) = t;
        let mut props = members.props.lock().unwrap();
        match props.get(id) {
            Some(elt) => Some(elt.clone()),
            None => match c.props.get(&PropName(crate::ctx::symbol(id))) {
                None => None,
                Some(elt) => {
                    let elt = decl_class::lookup_property_type_lazy(ctx.as_deref(), c, id, elt);
                    props.insert(id.to_string(), elt.clone());
                    Some(elt)
                }
            },
        }
    })
}

pub fn has_prop(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::HasProp(id), || {
        let TypingClassT(c, _) = t;
        c.props.contains_key(&PropName(crate::ctx::symbol(id)))
    })
}

/// Direct use of `get_sprop` will not register a dependency. You probably
/// want to use `Typing_env.get_static_member` instead
pub fn get_sprop(t: &T, id: &str) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::GetSprop(id), || {
        let TypingClassT(c, members) = t;
        let mut static_props = members.static_props.lock().unwrap();
        match static_props.get(id) {
            Some(elt) => Some(elt.clone()),
            None => match c.static_props.get(&PropName(crate::ctx::symbol(id))) {
                None => None,
                Some(elt) => {
                    let elt =
                        decl_class::lookup_static_property_type_lazy(ctx.as_deref(), c, id, elt);
                    static_props.insert(id.to_string(), elt.clone());
                    Some(elt)
                }
            },
        }
    })
}

pub fn has_sprop(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::HasSprop(id), || {
        let TypingClassT(c, _) = t;
        c.static_props.contains_key(&PropName(crate::ctx::symbol(id)))
    })
}

/// Direct use of `get_method` will not register a dependency. You probably
/// want to use `Typing_env.get_method` instead
pub fn get_method(t: &T, id: &str) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::GetMethod(id), || {
        let TypingClassT(c, members) = t;
        let mut methods = members.methods.lock().unwrap();
        match methods.get(id) {
            Some(elt) => Some(elt.clone()),
            None => match c.methods.get(&MethodName(crate::ctx::symbol(id))) {
                None => None,
                Some(elt) => {
                    let elt = decl_class::lookup_method_type_lazy(ctx.as_deref(), c, id, elt);
                    methods.insert(id.to_string(), elt.clone());
                    Some(elt)
                }
            },
        }
    })
}

pub fn has_method(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::HasMethod(id), || {
        let TypingClassT(c, _) = t;
        c.methods.contains_key(&MethodName(crate::ctx::symbol(id)))
    })
}

/// Direct use of `get_smethod` will not register a dependency. You probably
/// want to use `Typing_env.get_static_member` instead
pub fn get_smethod(t: &T, id: &str) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::GetSmethod(id), || {
        let TypingClassT(c, members) = t;
        let mut static_methods = members.static_methods.lock().unwrap();
        match static_methods.get(id) {
            Some(elt) => Some(elt.clone()),
            None => match c.static_methods.get(&MethodName(crate::ctx::symbol(id))) {
                None => None,
                Some(elt) => {
                    let elt = decl_class::lookup_static_method_type_lazy(ctx.as_deref(), c, id, elt);
                    static_methods.insert(id.to_string(), elt.clone());
                    Some(elt)
                }
            },
        }
    })
}

pub fn has_smethod(t: &T, id: &str) -> bool {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::HasSmethod(id), || {
        let TypingClassT(c, _) = t;
        c.static_methods.contains_key(&MethodName(crate::ctx::symbol(id)))
    })
}

pub fn get_any_method(is_static: bool, cls: &T, id: &str) -> Option<ClassElt> {
    // tally is already done inside the following three methods
    if id == sn::members::__CONSTRUCT {
        construct(cls).0
    } else if is_static {
        get_smethod(cls, id)
    } else {
        get_method(cls, id)
    }
}

// module ApiEager

pub fn all_ancestor_req_names(t: &T) -> Vec<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllAncestorReqNames, || {
        // The two below will traverse ancestors in different orders.
        // But if the typechecker discovers errors in different order, no matter.
        let TypingClassT(c, _) = t;
        // S_set.elements
        let mut names: Vec<String> = (c.req_ancestors_extends.iter())
            .map(|x| x.as_str().to_string())
            .collect();
        names.sort();
        names
    })
}

pub fn all_ancestors(t: &T) -> Vec<(String, Ty<R>)> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllAncestors, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.ancestors).into_iter())
            .map(|(k, ty)| (k.to_string(), ty.clone()))
            .collect()
    })
}

pub fn all_ancestor_names(t: &T) -> Vec<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllAncestors, || {
        let TypingClassT(c, _) = t;
        // S_map.ordered_keys
        (bindings(&c.ancestors).into_iter())
            .map(|(k, _)| k.to_string())
            .collect()
    })
}

/// All the require extends and require implements requirements
/// These requirements impose a strict subtype constraint
pub fn all_ancestor_reqs(t: &T) -> Vec<Requirement<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllAncestorReqs, || {
        let TypingClassT(c, _) = t;
        c.req_ancestors.to_vec()
    })
}

/// All the require class and require this as requirements
/// These requirements impose non-strict subtype constraint
/// and are not included in all_ancestor_reqs or
/// all_ancestor_req_names.
pub fn all_ancestor_req_constraints_requirements(t: &T) -> Vec<ConstraintRequirement<R>> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllAncestorReqs, || {
        let TypingClassT(c, _) = t;
        c.req_constraints_ancestors.to_vec()
    })
}

/// Projection out of all_ancestor_req_constraints_requirements
pub fn all_ancestor_req_class_requirements(t: &T) -> Vec<Requirement<R>> {
    (all_ancestor_req_constraints_requirements(t).into_iter())
        .filter_map(|r| match r {
            ConstraintRequirement::CREqual(c) => Some(c),
            ConstraintRequirement::CRSubtype(_) => None,
        })
        .collect()
}

/// Projection out of all_ancestor_req_constraints_requirements
pub fn all_ancestor_req_this_as_requirements(t: &T) -> Vec<Requirement<R>> {
    (all_ancestor_req_constraints_requirements(t).into_iter())
        .filter_map(|r| match r {
            ConstraintRequirement::CREqual(_) => None,
            ConstraintRequirement::CRSubtype(c) => Some(c),
        })
        .collect()
}

/// `Typing_defs.to_requirement`
fn to_requirement(cr: ConstraintRequirement<R>) -> Requirement<R> {
    match cr {
        ConstraintRequirement::CREqual(r) | ConstraintRequirement::CRSubtype(r) => r,
    }
}

pub fn upper_bounds_on_this(t: &T) -> Vec<Ty<R>> {
    upper_bounds_on_this_iter(t).cloned().collect()
}

/// [`upper_bounds_on_this`], borrowed from the class (in the same order: the
/// constraint requirements, then the other requirements), without copying
/// the requirements first.
pub fn upper_bounds_on_this_iter(t: &T) -> impl Iterator<Item = &Ty<R>> {
    // tally is already done by all_ancestors and upper_bounds
    let T(decl, tc, _ctx) = t;
    let TypingClassT(c, _) = tc;
    let reqs = decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllAncestorReqs, || {
        &c.req_ancestors[..]
    });
    let constraint_reqs =
        decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllAncestorReqs, || {
            &c.req_constraints_ancestors[..]
        });
    (constraint_reqs.iter())
        .map(|cr| match cr {
            ConstraintRequirement::CREqual(r) | ConstraintRequirement::CRSubtype(r) => &r.ty,
        })
        .chain(reqs.iter().map(|req| &req.ty))
}

/// Direct use of `consts` will not register a dependency. You probably want
/// to use `Typing_env.consts` instead
pub fn consts(t: &T) -> Vec<(String, ClassConst<R>)> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Consts, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.consts).into_iter())
            .map(|(id, cc)| (id.to_string(), cc.clone()))
            .collect()
    })
}

pub fn typeconsts(t: &T) -> Vec<(String, TypeConst<R>)> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Typeconsts, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.type_consts).into_iter())
            .map(|(id, tc)| (id.to_string(), tc.clone()))
            .collect()
    })
}

pub fn props(t: &T) -> Vec<(String, ClassElt)> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Props, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.props).into_iter())
            .map(|(id, elt)| {
                (
                    id.to_string(),
                    decl_class::lookup_property_type_lazy(ctx.as_deref(), c, id, elt),
                )
            })
            .collect()
    })
}

/// Not in the OCaml: the `ce_origin` of the property `id` of `props t`
/// (what `List.find (props t)` by name, then `ce_origin`, gives), without
/// building the class elements of all the properties.
pub fn prop_origin(t: &T, id: &str) -> Option<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Props, || {
        let TypingClassT(c, _) = t;
        (c.props.get(&PropName(crate::ctx::symbol(id)))).map(|elt| elt.origin.as_str().to_string())
    })
}

pub fn sprops(t: &T) -> Vec<(String, ClassElt)> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::SProps, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.static_props).into_iter())
            .map(|(id, elt)| {
                (
                    id.to_string(),
                    decl_class::lookup_static_property_type_lazy(ctx.as_deref(), c, id, elt),
                )
            })
            .collect()
    })
}

pub fn methods(t: &T) -> Vec<(String, ClassElt)> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::Methods, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.methods).into_iter())
            .map(|(id, elt)| {
                (
                    id.to_string(),
                    decl_class::lookup_method_type_lazy(ctx.as_deref(), c, id, elt),
                )
            })
            .collect()
    })
}

pub fn smethods(t: &T) -> Vec<(String, ClassElt)> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::SMethods, || {
        let TypingClassT(c, _) = t;
        (bindings(&c.static_methods).into_iter())
            .map(|(id, elt)| {
                (
                    id.to_string(),
                    decl_class::lookup_static_method_type_lazy(ctx.as_deref(), c, id, elt),
                )
            })
            .collect()
    })
}

pub fn overridden_method(
    t: &T,
    method_name: &str,
    is_static: bool,
    get_class: impl Fn(&Arc<Ctx>, &str) -> Option<T>,
) -> Option<ClassElt> {
    let T(decl, t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::OverriddenMethod, || {
        let ctx = ctx.as_deref()?;
        let get_method = |ty: &Ty<R>| -> Option<ClassElt> {
            let (_, class_name, _) = decl_utils::unwrap_class_type(ty);
            let cls = get_class(ctx, class_name.id_ref().as_str())?;
            get_any_method(is_static, &cls, method_name)
        };
        let TypingClassT(cls, _members) = t;
        let shallow_class = decl_provider_internals::get_shallow_class(ctx, cls.name.as_str())?;
        decl_inherit::find_overridden_method(&shallow_class, get_method)
    })
}

fn get_static_member_from_req_constraints(
    t: &T,
    get_member: impl Fn(&T) -> Option<ClassElt>,
    get_class: impl Fn(&Arc<Ctx>, &str) -> Option<T>,
) -> Option<ClassElt> {
    let T(decl, _t, ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::AllAncestorReqs, || {
        let ctx = ctx.as_deref()?;
        let req_constraints: Vec<Ty<R>> = (all_ancestor_req_constraints_requirements(t)
            .into_iter())
        .map(|cr| to_requirement(cr).ty)
        .collect();
        req_constraints
            .iter()
            .find_map(|req_ty| match req_ty.node_ref() {
                Ty_::Tapply(id_and_args) => {
                    let cn = id_and_args.0.id_ref().as_str();
                    let req_class = get_class(ctx, cn)?;
                    get_member(&req_class)
                }
                _ => None,
            })
    })
}

/// For a trait with `require class Foo` or `require this as Foo`, search `Foo`
/// for a static method. Returns the class element if found.
/// Intended for use in IDE and Glean after the innitial decl search failed.
pub fn get_smethod_from_req_constraints(
    cls: &T,
    method_name: &str,
    get_class: impl Fn(&Arc<Ctx>, &str) -> Option<T>,
) -> Option<ClassElt> {
    get_static_member_from_req_constraints(
        cls,
        |req_class| get_smethod(req_class, method_name),
        get_class,
    )
}

/// For a trait with `require class Foo` or `require this as Foo`, search `Foo`
/// for a static property. Returns the class element if found.
/// Intended for use in IDE and Glean after the innitial decl search failed.
pub fn get_sprop_from_req_constraints(
    cls: &T,
    prop_name: &str,
    get_class: impl Fn(&Arc<Ctx>, &str) -> Option<T>,
) -> Option<ClassElt> {
    get_static_member_from_req_constraints(
        cls,
        |req_class| get_sprop(req_class, prop_name),
        get_class,
    )
}

pub fn deferred_init_members(t: &T) -> im::OrdSet<String> {
    let T(decl, t, _ctx) = t;
    decl_counters::count_subdecl(decl.as_ref(), SubdeclKind::DeferredInitMembers, || {
        let TypingClassT(c, _) = t;
        (c.deferred_init_members.iter())
            .map(|x| x.as_str().to_string())
            .collect()
    })
}

#[cfg(test)]
mod tests {
    use oxidized::typechecker_options::TypecheckerOptions;
    use ty::decl::Typeconst;

    use super::*;
    use crate::decl_entry;
    use crate::decl_provider;
    use crate::decl_provider::testing::class;
    use crate::decl_provider::testing::ctx_of;
    use crate::typing_class_types;

    const SRC: &str = r#"<?hh

interface I<Ti> {
  const type TI = int;
  public function iface(Ti $x): void;
}

abstract class A<Ta1, Ta2> implements I<Ta2> {
  const int CA = 1;
  abstract const type TAbs as arraykey;
  const type TConcrete = string;
  <<__Enforceable>>
  const type TEnf = int;
  public ?Ta1 $prop_a = null;
  protected static vec<Ta2> $sprop_a = vec[];
  private int $priv_a = 0;
  public function __construct(protected Ta1 $ctor_prop) {}
  public function test(Ta1 $x, Ta2 $y): void {}
  public function iface(Ta2 $x): void {}
  public static function smeth(Ta1 $x): Ta2 { throw new Exception(); }
  final protected function prot(): Ta2 { throw new Exception(); }
  public function generic<Tm>(Tm $x, Ta1 $y): Tm { return $x; }
  public function cast<Tb>(Ta1 $x): Tb { throw new Exception(); }
  abstract public function abs(): Ta1;
  private function priv(): void {}
}

class B<Tb> extends A<Tb, int> {
  const type TAbs = int;
  public function abs(): Tb { throw new Exception(); }
}

final class C extends B<string> {
  const string CC = 'c';
  public function own(): void {}
}

trait Tr {
  require extends B<int>;
  require implements I<int>;
  public function from_trait(): this { return $this; }
  public static int $tr_sprop = 0;
}

trait TrClass {
  require class C;
  public static function tr_static(): int { return 1; }
}

class D extends B<int> {
  use Tr;
}

enum E: int as arraykey {
  X = 1;
  Y = 2;
}

enum class EC: arraykey {
  int ONE = 1;
}

<<__ConsistentConstruct>>
class Consistent {
  public function __construct(int $x) {}
}

class ConsistentChild extends Consistent {}

class NoCtor {}

abstract class AbsCtor {
  abstract public function __construct();
}
"#;

    fn ctx() -> Arc<Ctx> {
        static CTX: LazyLock<Arc<Ctx>> =
            LazyLock::new(|| ctx_of(SRC, TypecheckerOptions::default()));
        Arc::clone(&CTX)
    }

    fn cls(name: &str) -> T {
        class(&ctx(), name)
    }

    /// The declared type of an element, as hackrs prints decl types.
    fn ty(ce: &ClassElt) -> String {
        (**ce.ce_type).to_string()
    }

    fn names<A>(l: Vec<(String, A)>) -> Vec<String> {
        l.into_iter().map(|(name, _)| name).collect()
    }

    /// The line, and the first and last columns, of a position.
    fn span(pos: &Pos) -> (usize, usize, usize) {
        pos.info_pos()
    }

    /// The elements can; a class (`T`) stays on the thread whose class
    /// cache it comes from (its handles are `Rc`s: see `TypingClassT`).
    #[test]
    fn elements_can_be_shared_between_threads() {
        fn assert_send_sync<A: Send + Sync>() {}
        assert_send_sync::<ClassElt>();
    }

    #[test]
    fn what_the_class_was_declared_as() {
        let (a, b, c, i) = (cls("\\A"), cls("\\B"), cls("\\C"), cls("\\I"));
        assert_eq!(name(&c), "\\C");
        assert_eq!(
            kind(&c),
            ClassishKind::Cclass(oxidized::ast_defs::Abstraction::Concrete)
        );
        assert_eq!(
            kind(&a),
            ClassishKind::Cclass(oxidized::ast_defs::Abstraction::Abstract)
        );
        assert_eq!(kind(&i), ClassishKind::Cinterface);
        assert_eq!(kind(&cls("\\Tr")), ClassishKind::Ctrait);
        assert_eq!(kind(&cls("\\E")), ClassishKind::Cenum);
        assert_eq!(
            (abstract_(&a), abstract_(&b), abstract_(&c), abstract_(&i)),
            (true, false, false, true)
        );
        assert_eq!((final_(&a), final_(&b), final_(&c)), (false, false, true));
        assert!(!has_const_attribute(&c) && !is_xhp(&c) && !internal(&c));
        assert_eq!(get_module(&c), None);
        assert_eq!(get_docs_url(&c), None);
        assert_eq!(sealed_whitelist(&c), None);
        assert!(decl_errors(&c).is_empty());
        assert!(!get_support_dynamic_type(&c));
        // `class C` is on line 33 of the file.
        assert_eq!(pos(&c).filename().path_str(), "test.php");
        assert_eq!(span(&pos(&c)), (33, 13, 13));
        let tparam_names = |t: &T| -> Vec<String> {
            (tparams(t).iter())
                .map(|tp| tp.name.id_ref().as_str().to_string())
                .collect()
        };
        assert_eq!(tparam_names(&a), vec!["Ta1", "Ta2"]);
        assert_eq!(tparam_names(&b), vec!["Tb"]);
        assert!(tparam_names(&c).is_empty());
    }

    #[test]
    fn ancestors_have_their_type_arguments() {
        let (a, b, c) = (cls("\\A"), cls("\\B"), cls("\\C"));
        let ancestor = |t: &T, name: &str| get_ancestor(t, name).map(|ty| ty.to_string());
        assert_eq!(ancestor(&c, "\\B").as_deref(), Some("B<string>"));
        assert_eq!(ancestor(&c, "\\A").as_deref(), Some("A<string, int>"));
        assert_eq!(ancestor(&c, "\\I").as_deref(), Some("I<int>"));
        assert_eq!(ancestor(&b, "\\A").as_deref(), Some("A<Tb, int>"));
        assert_eq!(ancestor(&b, "\\I").as_deref(), Some("I<int>"));
        assert_eq!(ancestor(&a, "\\I").as_deref(), Some("I<Ta2>"));
        assert_eq!(ancestor(&c, "\\C"), None);
        assert_eq!(ancestor(&c, "\\Nope"), None);
        assert!(has_ancestor(&c, "\\A") && has_ancestor(&c, "\\I"));
        assert!(!has_ancestor(&a, "\\B") && !has_ancestor(&c, "\\Nope"));
        // In the order of the names, as `S_map.bindings` gives them.
        let all: Vec<(String, String)> = (all_ancestors(&c).into_iter())
            .map(|(name, ty)| (name, ty.to_string()))
            .collect();
        assert_eq!(
            all,
            vec![
                ("\\A".to_string(), "A<string, int>".to_string()),
                ("\\B".to_string(), "B<string>".to_string()),
                ("\\I".to_string(), "I<int>".to_string()),
            ]
        );
        assert_eq!(all_ancestor_names(&c), vec!["\\A", "\\B", "\\I"]);
        assert_eq!(
            all_ancestor_names(&cls("\\D")),
            vec!["\\A", "\\B", "\\I", "\\Tr"]
        );
    }

    #[test]
    fn inherited_methods_have_the_types_of_the_inheriting_class() {
        let (a, b, c) = (cls("\\A"), cls("\\B"), cls("\\C"));
        let method = |t: &T, name: &str| {
            let ce = get_method(t, name).unwrap_or_else(|| panic!("no method {}", name));
            (ty(&ce), ce.ce_origin.clone())
        };
        let from_a = |ty: &str| (ty.to_string(), "\\A".to_string());
        assert_eq!(
            method(&a, "test"),
            from_a("(function(Ta1 $x, Ta2 $y): void)")
        );
        assert_eq!(
            method(&b, "test"),
            from_a("(function(Tb $x, int $y): void)")
        );
        assert_eq!(
            method(&c, "test"),
            from_a("(function(string $x, int $y): void)")
        );
        assert_eq!(method(&c, "iface"), from_a("(function(int $x): void)"));
        assert_eq!(method(&c, "prot"), from_a("(function(): int)"));
        // Overridden in B.
        assert_eq!(method(&a, "abs"), from_a("(function(): Ta1)"));
        assert_eq!(
            method(&c, "abs"),
            ("(function(): string)".to_string(), "\\B".to_string())
        );
        assert_eq!(
            method(&c, "own"),
            ("(function(): void)".to_string(), "\\C".to_string())
        );
        // Through a trait.
        assert_eq!(
            method(&cls("\\D"), "from_trait"),
            ("(function(): this)".to_string(), "\\Tr".to_string())
        );
        assert_eq!(
            method(&cls("\\D"), "test"),
            from_a("(function(int $x, int $y): void)")
        );

        assert!(has_method(&c, "test") && !has_method(&c, "smeth") && !has_method(&c, "nope"));
        assert!(get_method(&c, "nope").is_none() && get_method(&c, "smeth").is_none());

        let smeth = get_smethod(&c, "smeth").unwrap();
        assert_eq!(ty(&smeth), "(function(string $x): int)");
        assert_eq!(smeth.ce_origin, "\\A");
        assert_eq!(
            ty(&get_smethod(&b, "smeth").unwrap()),
            "(function(Tb $x): int)"
        );
        assert!(has_smethod(&c, "smeth") && !has_smethod(&c, "test"));
        assert!(get_smethod(&c, "test").is_none());

        assert_eq!(
            names(methods(&c)),
            vec!["abs", "cast", "generic", "iface", "own", "prot", "test"]
        );
        assert_eq!(names(smethods(&c)), vec!["smeth"]);
        let all: Vec<String> = methods(&c).iter().map(|(_, ce)| ty(ce)).collect();
        assert_eq!(all[6], "(function(string $x, int $y): void)");
    }

    #[test]
    fn type_parameters_of_methods() {
        let (a, b, c) = (cls("\\A"), cls("\\B"), cls("\\C"));
        let method = |t: &T, name: &str| ty(&get_method(t, name).unwrap());
        // A method's own type parameter is not substituted.
        assert_eq!(method(&a, "generic"), "(function<Tm>(Tm $x, Ta1 $y): Tm)");
        assert_eq!(
            method(&c, "generic"),
            "(function<Tm>(Tm $x, string $y): Tm)"
        );
        // `A::cast<Tb>(Ta1): Tb` in `B<Tb> extends A<Tb, int>`: the method's
        // `Tb` is renamed away from the `Tb` that `Ta1` becomes.
        assert_eq!(method(&a, "cast"), "(function<Tb>(Ta1 $x): Tb)");
        assert_eq!(method(&b, "cast"), "(function<Tb#0>(Tb $x): Tb#0)");
        assert_eq!(method(&c, "cast"), "(function<Tb#0>(string $x): Tb#0)");
    }

    #[test]
    fn visibility_origin_and_flags_of_elements() {
        let (a, c) = (cls("\\A"), cls("\\C"));
        let test = get_method(&c, "test").unwrap();
        assert_eq!(test.ce_visibility, CeVisibility::Vpublic);
        assert_eq!(test.ce_origin, "\\A");
        assert_eq!(test.ce_deprecated, None);
        assert_eq!(test.ce_flags, ClassEltFlags::empty());
        // The position of the element is where it was declared: line 18 of
        // the file, in `A`.
        assert_eq!(span(&test.ce_pos), (18, 19, 22));

        let prot = get_method(&c, "prot").unwrap();
        assert_eq!(
            prot.ce_visibility,
            CeVisibility::Vprotected("\\A".to_string())
        );
        assert!(prot.ce_flags.contains(ClassEltFlags::FINAL));

        // Private members are not inherited.
        let private = CeVisibility::Vprivate("\\A".to_string());
        assert_eq!(get_method(&a, "priv").unwrap().ce_visibility, private);
        assert!(get_method(&c, "priv").is_none() && !has_method(&c, "priv"));
        assert_eq!(get_prop(&a, "priv_a").unwrap().ce_visibility, private);
        assert!(get_prop(&c, "priv_a").is_none() && !has_prop(&c, "priv_a"));

        assert!(
            get_method(&a, "abs")
                .unwrap()
                .ce_flags
                .contains(ClassEltFlags::ABSTRACT)
        );
        assert!(
            !get_method(&c, "abs")
                .unwrap()
                .ce_flags
                .contains(ClassEltFlags::ABSTRACT)
        );
    }

    #[test]
    fn properties() {
        let (a, b, c) = (cls("\\A"), cls("\\B"), cls("\\C"));
        let prop = |t: &T, name: &str| ty(&get_prop(t, name).unwrap());
        assert_eq!(prop(&a, "prop_a"), "?Ta1");
        assert_eq!(prop(&b, "prop_a"), "?Tb");
        assert_eq!(prop(&c, "prop_a"), "?string");
        // Declared by the constructor of A.
        let ctor_prop = get_prop(&c, "ctor_prop").unwrap();
        assert_eq!(ty(&ctor_prop), "string");
        assert_eq!(ctor_prop.ce_origin, "\\A");
        assert_eq!(
            ctor_prop.ce_visibility,
            CeVisibility::Vprotected("\\A".to_string())
        );
        assert_eq!(names(props(&c)), vec!["ctor_prop", "prop_a"]);
        assert_eq!(names(props(&a)), vec!["ctor_prop", "priv_a", "prop_a"]);
        assert!(has_prop(&c, "prop_a") && !has_prop(&c, "$sprop_a") && !has_prop(&c, "nope"));

        // Static properties are named with their `$`.
        let sprop = get_sprop(&c, "$sprop_a").unwrap();
        assert_eq!(ty(&sprop), "HH\\vec<int>");
        assert_eq!(sprop.ce_origin, "\\A");
        assert_eq!(ty(&get_sprop(&a, "$sprop_a").unwrap()), "HH\\vec<Ta2>");
        assert!(get_sprop(&c, "sprop_a").is_none() && get_sprop(&c, "prop_a").is_none());
        assert!(has_sprop(&c, "$sprop_a") && !has_sprop(&c, "prop_a"));
        assert_eq!(names(sprops(&c)), vec!["$sprop_a"]);
        assert_eq!(names(sprops(&cls("\\D"))), vec!["$sprop_a", "$tr_sprop"]);
        assert!(deferred_init_members(&c).is_empty());
    }

    #[test]
    fn constructors() {
        let ctor = |name: &str| {
            let (ce, consistent) = construct(&cls(name));
            (ce.map(|ce| (ty(&ce), ce.ce_origin.clone())), consistent)
        };
        let from_a = |ty: &str| Some((ty.to_string(), "\\A".to_string()));
        assert_eq!(
            ctor("\\A"),
            (
                from_a("(function(Ta1 $ctor_prop): void)"),
                ConsistentKind::Inconsistent
            )
        );
        assert_eq!(
            ctor("\\B"),
            (
                from_a("(function(Tb $ctor_prop): void)"),
                ConsistentKind::Inconsistent
            )
        );
        assert_eq!(
            ctor("\\C"),
            (
                from_a("(function(string $ctor_prop): void)"),
                ConsistentKind::FinalClass
            )
        );
        let consistent = Some((
            "(function(int $x): void)".to_string(),
            "\\Consistent".to_string(),
        ));
        assert_eq!(
            ctor("\\Consistent"),
            (consistent.clone(), ConsistentKind::ConsistentConstruct)
        );
        assert_eq!(
            ctor("\\ConsistentChild"),
            (consistent, ConsistentKind::ConsistentConstruct)
        );
        assert_eq!(ctor("\\NoCtor"), (None, ConsistentKind::Inconsistent));
        assert_eq!(ctor("\\I"), (None, ConsistentKind::Inconsistent));

        // A class needs to be initialised when it has a constructor that is
        // not abstract.
        assert!(need_init(&cls("\\A")) && need_init(&cls("\\C")));
        assert!(need_init(&cls("\\ConsistentChild")));
        assert!(!need_init(&cls("\\NoCtor")) && !need_init(&cls("\\AbsCtor")));
        assert!(construct(&cls("\\AbsCtor")).0.is_some());

        let c = cls("\\C");
        let any =
            |is_static: bool, name: &str| get_any_method(is_static, &c, name).map(|ce| ty(&ce));
        assert_eq!(
            any(false, "__construct").as_deref(),
            Some("(function(string $ctor_prop): void)")
        );
        assert_eq!(
            any(true, "__construct").as_deref(),
            Some("(function(string $ctor_prop): void)")
        );
        assert_eq!(
            any(true, "smeth").as_deref(),
            Some("(function(string $x): int)")
        );
        assert_eq!(any(false, "smeth"), None);
        assert_eq!(any(false, "own").as_deref(), Some("(function(): void)"));
        assert_eq!(any(true, "own"), None);
        // The constructor is not a method.
        assert!(get_method(&c, "__construct").is_none());
    }

    #[test]
    fn constants() {
        let (a, c) = (cls("\\A"), cls("\\C"));
        let cc = get_const(&c, "CC").unwrap();
        assert_eq!(cc.ty.to_string(), "string");
        assert_eq!(cc.origin.as_str(), "\\C");
        assert_eq!(cc.kind, ty::decl::ClassConstKind::CCConcrete);
        let ca = get_const(&c, "CA").unwrap();
        assert_eq!(ca.ty.to_string(), "int");
        assert_eq!(ca.origin.as_str(), "\\A");
        assert!(get_const(&a, "CC").is_none() && get_const(&c, "Nope").is_none());
        assert!(has_const(&c, "CA") && has_const(&c, "CC"));
        assert!(!has_const(&a, "CC") && !has_const(&c, "Nope"));
        // Every class has a constant `class`, and one for each type constant.
        assert_eq!(
            names(consts(&c)),
            vec!["CA", "CC", "TAbs", "TConcrete", "TEnf", "TI", "class"]
        );
        assert_eq!(
            get_const(&a, "TAbs").unwrap().kind,
            ty::decl::ClassConstKind::CCAbstract(false)
        );
        assert_eq!(
            get_const(&c, "TAbs").unwrap().kind,
            ty::decl::ClassConstKind::CCConcrete
        );
        assert_eq!(get_const(&c, "class").unwrap().origin.as_str(), "\\C");
    }

    #[test]
    fn type_constants() {
        let (a, c) = (cls("\\A"), cls("\\C"));
        match get_typeconst(&a, "TAbs").unwrap().kind {
            Typeconst::TCAbstract(atc) => {
                assert_eq!(atc.as_constraint.unwrap().to_string(), "arraykey");
                assert!(atc.super_constraint.is_none() && atc.default.is_none());
            }
            Typeconst::TCConcrete(_) => panic!(),
        }
        // Made concrete by B.
        let tabs = get_typeconst(&c, "TAbs").unwrap();
        assert_eq!(tabs.origin.as_str(), "\\B");
        match tabs.kind {
            Typeconst::TCConcrete(tc) => assert_eq!(tc.ty.to_string(), "int"),
            Typeconst::TCAbstract(_) => panic!(),
        }
        // From the interface.
        let ti = get_typeconst(&c, "TI").unwrap();
        assert_eq!(ti.origin.as_str(), "\\I");
        assert_eq!(ti.name.id_ref().as_str(), "TI");
        assert!(get_typeconst(&c, "CA").is_none() && get_typeconst(&c, "Nope").is_none());
        assert!(has_typeconst(&c, "TConcrete") && !has_typeconst(&c, "CA"));
        assert_eq!(
            names(typeconsts(&c)),
            vec!["TAbs", "TConcrete", "TEnf", "TI"]
        );

        assert_eq!(
            get_typeconst_enforceability(&c, "TAbs"),
            Some((Pos::NONE, false))
        );
        assert_eq!(get_typeconst_enforceability(&c, "Nope"), None);
        // The position is that of the attribute, on line 12 of the file.
        let (pos, enforceable) = get_typeconst_enforceability(&c, "TEnf").unwrap();
        assert!(enforceable);
        assert_eq!(span(&pos).0, 12);
    }

    #[test]
    fn enums() {
        let e = cls("\\E");
        let enum_type_ = enum_type(&e).unwrap();
        assert_eq!(enum_type_.base.to_string(), "int");
        assert_eq!(
            enum_type_.constraint.as_ref().unwrap().to_string(),
            "arraykey"
        );
        assert!(enum_type_.includes.is_empty());
        assert_eq!(
            get_ancestor(&e, "\\HH\\BuiltinEnum").unwrap().to_string(),
            "HH\\BuiltinEnum<E>"
        );
        // The constants of an enum have the type of the enum.
        assert_eq!(get_const(&e, "X").unwrap().ty.to_string(), "E");
        assert_eq!(names(consts(&e)), vec!["X", "Y", "class"]);
        // Its methods are those of `BuiltinEnum<E>`.
        let get_values = get_smethod(&e, "getValues").unwrap();
        assert_eq!(ty(&get_values), "(function(): HH\\dict<string, E>)");
        assert_eq!(get_values.ce_origin, "\\HH\\BuiltinEnum");

        let ec = cls("\\EC");
        assert_eq!(
            kind(&ec),
            ClassishKind::CenumClass(oxidized::ast_defs::Abstraction::Concrete)
        );
        let enum_type_ = enum_type(&ec).unwrap();
        assert_eq!(enum_type_.base.to_string(), "arraykey");
        assert!(enum_type_.constraint.is_none());
        assert_eq!(
            get_const(&ec, "ONE").unwrap().ty.to_string(),
            "HH\\MemberOf<EC, int>"
        );
        assert_eq!(
            get_ancestor(&ec, "\\HH\\BuiltinEnumClass")
                .unwrap()
                .to_string(),
            "HH\\BuiltinEnumClass<HH\\MemberOf<EC, arraykey>>"
        );

        assert!(enum_type(&cls("\\C")).is_none());

        // What `Decl_enum` makes of them.
        let enum_kind = |t: &T, is_enum_class: bool| {
            let name = pos::Positioned::new(BPos::none(), TypeName::new(name(t)));
            crate::decl_enum::enum_kind(
                &name,
                is_enum_class,
                false,
                enum_type(t).as_ref(),
                None,
                |ancestor| get_ancestor(t, ancestor),
            )
        };
        let kind_e = enum_kind(&e, false).unwrap();
        assert_eq!(kind_e.base.to_string(), "int");
        assert_eq!(kind_e.type_.to_string(), "E");
        assert_eq!(kind_e.constraint_.unwrap().to_string(), "arraykey");
        assert!(kind_e.interface.is_none());
        let kind_ec = enum_kind(&ec, true).unwrap();
        assert_eq!(kind_ec.base.to_string(), "HH\\MemberOf<EC, arraykey>");
        assert_eq!(kind_ec.type_.to_string(), "EC");
        assert_eq!(kind_ec.interface.unwrap().to_string(), "arraykey");
        assert!(enum_kind(&cls("\\C"), false).is_none());
    }

    #[test]
    fn requirements() {
        let tr = cls("\\Tr");
        let reqs: Vec<String> = (all_ancestor_reqs(&tr).iter())
            .map(|req| req.ty.to_string())
            .collect();
        assert_eq!(reqs, vec!["B<int>", "I<int>"]);
        assert!(requires_ancestor(&tr, "\\B") && requires_ancestor(&tr, "\\I"));
        assert!(!requires_ancestor(&tr, "\\C"));
        // `require extends B<int>` also requires what B extends.
        assert_eq!(all_ancestor_req_names(&tr), vec!["\\A", "\\B", "\\I"]);
        assert!(all_ancestor_req_constraints_requirements(&tr).is_empty());
        let upper_bounds: Vec<String> = (upper_bounds_on_this(&tr).iter())
            .map(|ty| ty.to_string())
            .collect();
        assert_eq!(upper_bounds, vec!["B<int>", "I<int>"]);
        // The members of the required class are members of the trait.
        assert_eq!(
            ty(&get_method(&tr, "test").unwrap()),
            "(function(int $x, int $y): void)"
        );
        assert!(
            get_method(&tr, "test")
                .unwrap()
                .ce_flags
                .contains(ClassEltFlags::SYNTHESIZED)
        );

        let tr_class = cls("\\TrClass");
        assert!(all_ancestor_reqs(&tr_class).is_empty());
        assert!(all_ancestor_req_names(&tr_class).is_empty());
        let req_classes: Vec<String> = (all_ancestor_req_class_requirements(&tr_class).iter())
            .map(|req| req.ty.to_string())
            .collect();
        assert_eq!(req_classes, vec!["C"]);
        assert!(all_ancestor_req_this_as_requirements(&tr_class).is_empty());
        let upper_bounds: Vec<String> = (upper_bounds_on_this(&tr_class).iter())
            .map(|ty| ty.to_string())
            .collect();
        assert_eq!(upper_bounds, vec!["C"]);

        // `require class C` does not make the members of C members of the
        // trait: they are looked for in C.
        assert!(get_smethod(&tr_class, "smeth").is_none());
        let get_class = |ctx: &Arc<Ctx>, name: &str| {
            decl_entry::to_option(decl_provider::get_class(None, ctx, name))
        };
        let smeth = get_smethod_from_req_constraints(&tr_class, "smeth", get_class).unwrap();
        assert_eq!(ty(&smeth), "(function(string $x): int)");
        assert!(get_smethod_from_req_constraints(&tr_class, "nope", get_class).is_none());
        let sprop = get_sprop_from_req_constraints(&tr_class, "$sprop_a", get_class).unwrap();
        assert_eq!(ty(&sprop), "HH\\vec<int>");
        assert!(get_sprop_from_req_constraints(&tr, "$sprop_a", get_class).is_none());
    }

    #[test]
    fn elements_are_looked_up_once_for_a_class() {
        let c = cls("\\C");
        let test1 = get_method(&c, "test").unwrap();
        let test2 = get_method(&c, "test").unwrap();
        // The same lazy type.
        assert!(Arc::ptr_eq(&test1.ce_type, &test2.ce_type));
        assert!(Arc::ptr_eq(&test1.ce_pos, &test2.ce_pos));
        let (ctor1, _) = construct(&c);
        let (ctor2, _) = construct(&c);
        assert!(Arc::ptr_eq(
            &ctor1.unwrap().ce_type,
            &ctor2.unwrap().ce_type
        ));
        // And for the class as it is fetched again.
        let test3 = get_method(&cls("\\C"), "test").unwrap();
        assert!(Arc::ptr_eq(&test1.ce_type, &test3.ce_type));
        // `methods` looks every element up again.
        let (_, test4) = methods(&c).pop().unwrap();
        assert!(!Arc::ptr_eq(&test1.ce_type, &test4.ce_type));
        assert_eq!(ty(&test1), ty(&test4));
    }

    #[test]
    fn the_type_of_an_element_is_only_looked_up_when_asked_for() {
        // Without a context there is nowhere to look the type up, which is
        // only found out when the type is asked for.
        let T(_, class_t, _) = cls("\\C");
        let class_t = typing_class_types::make_class_t(Arc::clone(&class_t.0));
        let c = T(None, make(class_t), None);
        let test = get_method(&c, "test").unwrap();
        assert_eq!(test.ce_origin, "\\A");
        assert_eq!(test.ce_visibility, CeVisibility::Vpublic);
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ty(&test)));
        let message = *panic.unwrap_err().downcast::<String>().unwrap();
        assert_eq!(
            message,
            "Decl_class.Decl_heap_elems_bug(\"could not find \\\\A::test (inherited by \\\\C) (no lazy member lookup performed)\")"
        );
        let (ctor, consistent) = construct(&c);
        assert_eq!(consistent, ConsistentKind::FinalClass);
        let ctor = ctor.unwrap();
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ty(&ctor)));
        assert!(panic.is_err());
    }

    #[test]
    fn instantiate_ce() {
        use ty::reason::Reason;
        let b = cls("\\B");
        let test = get_method(&b, "test").unwrap();
        let float = Ty::prim(R::none(), ty::decl::Prim::Tfloat);
        let subst = crate::decl_instantiate::make_subst(&tparams(&b), &[float]);
        let instantiated = crate::decl_instantiate::instantiate_ce(&subst, &test);
        assert_eq!(ty(&instantiated), "(function(float $x, int $y): void)");
        assert_eq!(ty(&test), "(function(Tb $x, int $y): void)");
        assert!(Arc::ptr_eq(&instantiated.ce_pos, &test.ce_pos));
        assert_eq!(instantiated.ce_origin, "\\A");
    }

    #[test]
    fn member_types_are_pessimised_with_everything_sdt() {
        let src = r#"<?hh
class P<Tc> {
  public int $enforced = 0;
  public function two<T>(T $x, Tc $y): int { return 1; }
  public static function stwo<T>(T $x, int $y): void {}
}

class P2 extends P<float> {}

<<__NoAutoDynamic>>
class Q<Tc> {
  public function two<T>(T $x, Tc $y): int { return 1; }
}
"#;
        let mut tco = TypecheckerOptions::default();
        tco.po.everything_sdt = true;
        let ctx = ctx_of(src, tco);
        // The type parameters of a method are made to support dynamic
        // (`Decl_enforceability.Pessimize`), before the substitution.
        let p2 = class(&ctx, "\\P2");
        assert_eq!(
            ty(&get_method(&p2, "two").unwrap()),
            "(function<T as HH\\supportdyn<mixed>>(T $x, float $y): int)"
        );
        assert_eq!(
            ty(&get_smethod(&p2, "stwo").unwrap()),
            "(function<T as HH\\supportdyn<mixed>>(T $x, int $y): void)"
        );
        // An enforced type is left alone.
        assert_eq!(ty(&get_prop(&p2, "enforced").unwrap()), "int");
        assert!(get_support_dynamic_type(&p2));
        // Not in a class that opts out.
        let q = class(&ctx, "\\Q");
        assert_eq!(
            ty(&get_method(&q, "two").unwrap()),
            "(function<T>(T $x, Tc $y): int)"
        );
        assert!(!get_support_dynamic_type(&q));

        // Without the option nothing is.
        let ctx = ctx_of(src, TypecheckerOptions::default());
        let p2 = class(&ctx, "\\P2");
        assert_eq!(
            ty(&get_method(&p2, "two").unwrap()),
            "(function<T>(T $x, float $y): int)"
        );
    }
}
