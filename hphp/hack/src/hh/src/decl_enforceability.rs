// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_enforceability.ml`. See `hh/PORTING.md`.
//!
//! The functors of the OCaml map as follows:
//!
//! - the module types `Provider`, `ContextAccess` and `ShallowProvider` are
//!   traits, whose functions have no receiver (a module is a type that
//!   implements the trait);
//! - `ShallowContextAccess (Provider)` is the type
//!   `ShallowContextAccess<P>`, which implements `ContextAccess`;
//! - the functions of `Enforce (ContextAccess)` and `Pessimize (Provider)`
//!   are the functions of the modules `enforce` and `pessimize`, generic in
//!   the argument of the functor: `E.get_enforcement` for
//!   `module E = Enforce (CA)` is `enforce::get_enforcement::<CA>`.
//!
//! `supportdyn_mixed` and `add_supportdyn_constraints` are those of the crate
//! `hackrs/decl_enforceability`, which class folding uses.

use std::marker::PhantomData;
use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::typechecker_options::TypecheckerOptions;
pub use oxidized::typing_reason::PessimiseReason;
use pos::BPos;
use ty::decl;
use ty::decl::ShallowClass;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::ty::TypedefCaseTypeVariant;
use ty::decl::ty::TypedefType;
use ty::decl::ty::TypedefTypeAssignment;
use ty::reason::Reason as _;
use ty::reason::ReasonImpl;
use ty::reason::WitnessDecl;

use crate::ctx::Ctx;
use crate::ctx::R;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Enf {
    /// The type is fully enforced
    Enforced(Ty<R>),
    /// The type is not fully enforced, but is enforced at the given ty, if
    /// present
    Unenforced(Option<Ty<R>>, PessimiseReason),
}

#[derive(Clone, Debug)]
pub enum ClassOrTypedefResult<A> {
    ClassResult(A),
    TypedefResult(Arc<TypedefType<R>>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FunKind {
    Function,
    AbstractMethod,
    ConcreteMethod,
}

/// `Typing_reason.pessimised_return`
fn reason_pessimised_return(p: &BPos, pr: PessimiseReason) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::PessimisedReturn(p.clone(), pr)))
}

/// `Typing_reason.pessimised_prop`
fn reason_pessimised_prop(p: &BPos, pr: PessimiseReason) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::PessimisedProp(p.clone(), pr)))
}

/// `Typing_reason.pessimised_inout`
fn reason_pessimised_inout(p: &BPos) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::PessimisedInout(p.clone())))
}

/// `Typing_reason.support_dynamic_type_assume`
fn reason_support_dynamic_type_assume(p: &BPos) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::SupportDynamicTypeAssume(p.clone())))
}

/// `Typing_make_type.arraykey`, on a decl type
fn make_type_arraykey(r: R) -> Ty<R> {
    Ty::new(r, Ty_::Tprim(aast::Tprim::Tarraykey))
}

/// `Typing_make_type.union`, on decl types
fn make_type_union(r: R, mut tyl: Vec<Ty<R>>) -> Ty<R> {
    match tyl.len() {
        1 => tyl.pop().unwrap(),
        _ => Ty::new(r, Ty_::Tunion(tyl.into())),
    }
}

/// `Typing_make_type.intersection`, on decl types
fn make_type_intersection(r: R, mut tyl: Vec<Ty<R>>) -> Ty<R> {
    match tyl.len() {
        // `mixed r` is `mk (r, Toption (nonnull r))`
        0 => Ty::new(r.clone(), Ty_::Toption(Ty::new(r, Ty_::Tnonnull))),
        1 => tyl.pop().unwrap(),
        _ => Ty::new(r, Ty_::Tintersection(tyl.into())),
    }
}

/// `Typing_make_type.is_dynamic_or_like_or_mixed`
fn is_dynamic_or_like_or_mixed(ty: &Ty<R>) -> bool {
    match ty.node_ref() {
        Ty_::Tdynamic | Ty_::Tlike(_) | Ty_::Tmixed => true,
        _ => false,
    }
}

/// `Typing_make_type.like`, on a decl type
fn make_type_like(r: R, ty: &Ty<R>) -> Ty<R> {
    if is_dynamic_or_like_or_mixed(ty) {
        ty.clone()
    } else {
        match ty.node_ref() {
            Ty_::Tapply(id_and_args)
                if id_and_args.0.id().as_str() == sn::classes::SUPPORT_DYN
                    && matches!(&id_and_args.1[..], [inner_ty] if is_dynamic_or_like_or_mixed(inner_ty)) =>
            {
                ty.clone()
            }
            _ => Ty::new(r, Ty_::Tlike(ty.clone())),
        }
    }
}

/// `Typing_defs.is_any`
fn is_any(t: &Ty<R>) -> bool {
    match t.node_ref() {
        Ty_::Tany => true,
        _ => false,
    }
}

fn noautodynamic(this_class: Option<&ShallowClass<R>>) -> bool {
    match this_class {
        None => false,
        Some(sc) => sc
            .user_attributes
            .iter()
            .any(|ua| ua.name.id().as_str() == sn::user_attributes::NO_AUTO_DYNAMIC),
    }
}

fn implicit_sdt_for_class(
    tcopt: &TypecheckerOptions,
    this_class: Option<&ShallowClass<R>>,
) -> bool {
    tcopt.po.everything_sdt && !noautodynamic(this_class)
}

fn make_unenforced(ty: Enf, pr: PessimiseReason) -> Enf {
    match ty {
        Enf::Enforced(ty) => Enf::Unenforced(Some(ty), pr),
        Enf::Unenforced(..) => ty,
    }
}

pub fn supportdyn_mixed(p: &BPos, r: &R) -> Ty<R> {
    hackrs_decl_enforceability::supportdyn_mixed(p.clone(), r.clone())
}

/// Add as supportdyn<mixed> constraints to the type parameters
pub fn add_supportdyn_constraints(
    p: &BPos,
    tparams: &[decl::Tparam<R, Ty<R>>],
) -> Vec<decl::Tparam<R, Ty<R>>> {
    let mut tparams = tparams.to_vec();
    hackrs_decl_enforceability::add_supportdyn_constraints(p, &mut tparams);
    tparams
}

/// Add as supportdyn<mixed> constraints to the type parameters if in implicit
/// pessimisation mode.
pub fn maybe_add_supportdyn_constraints(
    this_class: Option<&ShallowClass<R>>,
    ctx: &Ctx,
    p: &BPos,
    tparams: &[decl::Tparam<R, Ty<R>>],
) -> Vec<decl::Tparam<R, Ty<R>>> {
    if implicit_sdt_for_class(&ctx.tco, this_class) {
        add_supportdyn_constraints(p, tparams)
    } else {
        tparams.to_vec()
    }
}

/// A set of (class name, type constant name).
type VisitedSet = im::OrdSet<(String, String)>;

pub trait Provider {
    /// `T` is the type of the context that classes and typedefs can be found
    /// in
    type T;

    /// `ClassT` is the type that represents a class
    type ClassT: Clone;

    /// (Borrowed: a copy of the `Arc` of the options writes a reference
    /// count that every thread shares.)
    fn get_tcopt(t: &Self::T) -> &Arc<TypecheckerOptions>;

    fn get_class_or_typedef(t: &Self::T, name: &str) -> Option<ClassOrTypedefResult<Self::ClassT>>;

    fn get_class(t: &Self::T, name: &str) -> Option<Self::ClassT>;
}

pub trait ContextAccess: Provider {
    /// `get_typeconst_type(ctx, cls, name)` gets the definition of the type
    /// constant `name` from `cls` or ancestor if it exists.
    fn get_typeconst_type(t: &Self::T, cls: &Self::ClassT, name: &str) -> Option<Ty<R>>;

    fn get_tparams(cls: &Self::ClassT) -> Vec<decl::Tparam<R, Ty<R>>>;

    fn is_final(cls: &Self::ClassT) -> bool;

    fn get_name(cls: &Self::ClassT) -> String;

    /// `get_enum_type(cls)` returns the enumeration type if `cls` is an enum.
    fn get_enum_type(cls: &Self::ClassT) -> Option<decl::EnumType<R>>;
}

pub mod enforce {
    use super::*;

    fn is_mixed(ty: &Ty<R>) -> bool {
        match ty.node_ref() {
            Ty_::Tapply(id_and_args)
                if id_and_args.1.len() == 1
                    && id_and_args.0.id().as_str() == sn::classes::SUPPORT_DYN =>
            {
                is_mixed(&id_and_args.1[0])
            }
            Ty_::Tmixed => true,
            _ => false,
        }
    }

    fn is_arraykey(ty: &Ty<R>) -> bool {
        match ty.node_ref() {
            Ty_::Tprim(aast::Tprim::Tarraykey) => true,
            _ => false,
        }
    }

    fn add_to_visited<CA: ContextAccess>(
        visited: &VisitedSet,
        cd: &CA::ClassT,
        ty: &str,
    ) -> VisitedSet {
        let name = CA::get_name(cd);
        visited.update((name, ty.to_string()))
    }

    fn mem_visited<CA: ContextAccess>(visited: &VisitedSet, cd: &CA::ClassT, ty: &str) -> bool {
        let name = CA::get_name(cd);
        visited.contains(&(name, ty.to_string()))
    }

    /* Find the class definition that ty represents, by expanding Taccess. Since
    expanding one Taccess might give us another type containing Taccess, we
    keep a set of visited type constant definitions and terminate if we reach
    a cycle. */
    fn get_owner<CA: ContextAccess>(
        this_class: Option<&CA::ClassT>,
        visited: &VisitedSet,
        ctx: &CA::T,
        ty: &Ty<R>,
    ) -> Option<CA::ClassT> {
        match ty.node_ref() {
            Ty_::Tthis => this_class.cloned(),
            Ty_::Tapply(id_and_args) => CA::get_class(ctx, id_and_args.0.id().as_str()),
            Ty_::Taccess(taccess) => {
                let tcname = taccess.type_const.id().as_str();
                let (visited, cd, ty) =
                    get_owner_and_type::<CA>(this_class, visited, ctx, &taccess.ty, tcname)?;
                get_owner::<CA>(Some(&cd), &visited, ctx, &ty)
            }
            _ => None,
        }
    }

    /* Lookup tcname in the class that ty represents. */
    fn get_owner_and_type<CA: ContextAccess>(
        this_class: Option<&CA::ClassT>,
        visited: &VisitedSet,
        ctx: &CA::T,
        ty: &Ty<R>,
        tcname: &str,
    ) -> Option<(VisitedSet, CA::ClassT, Ty<R>)> {
        let cd = get_owner::<CA>(this_class, visited, ctx, ty)?;
        if mem_visited::<CA>(visited, &cd, tcname) {
            None
        } else {
            let ty = CA::get_typeconst_type(ctx, &cd, tcname)?;
            Some((add_to_visited::<CA>(visited, &cd, tcname), cd, ty))
        }
    }

    /* Resolve an access t::T to a type that is not an access */
    fn resolve_access<CA: ContextAccess>(
        this_class: Option<&CA::ClassT>,
        ctx: &CA::T,
        ty: &Ty<R>,
        tcname: &str,
    ) -> Option<Ty<R>> {
        /* We need to maintain a visited set because there can be cycles between bounds on type constants */
        fn resolve_access<CA: ContextAccess>(
            this_class: Option<&CA::ClassT>,
            visited: &VisitedSet,
            ctx: &CA::T,
            ty: &Ty<R>,
            tcname: &str,
        ) -> Option<Ty<R>> {
            let (visited, cd, ty) = get_owner_and_type::<CA>(this_class, visited, ctx, ty, tcname)?;
            match ty.node_ref() {
                Ty_::Taccess(taccess) => resolve_access::<CA>(
                    Some(&cd),
                    &visited,
                    ctx,
                    &taccess.ty,
                    taccess.type_const.id().as_str(),
                ),
                _ => Some(ty),
            }
        }
        resolve_access::<CA>(this_class, &VisitedSet::new(), ctx, ty, tcname)
    }

    /* Unenforced type without an intersection */
    fn unenforced(pr: PessimiseReason) -> Enf {
        Enf::Unenforced(None, pr)
    }

    /// What `enforcement` closes over in the OCaml.
    struct Closure<'a, CA: ContextAccess> {
        top_enforced: bool,
        this_class: Option<&'a CA::ClassT>,
        tc_enforced: bool,
        ty_pos: &'a BPos,
    }

    /* is_dynamic_enforceable controls whether the type dynamic is considered enforceable.
    It isn't at the top-level of a type, but is as an argument to a reified generic. */
    fn enforcement<CA: ContextAccess>(
        closure: &Closure<'_, CA>,
        is_dynamic_enforceable: bool,
        ctx: &CA::T,
        visited: &im::OrdSet<String>,
        ty: &Ty<R>,
    ) -> Enf {
        let Closure {
            top_enforced,
            this_class,
            tc_enforced,
            ty_pos,
        } = *closure;
        match ty.node_ref() {
            Ty_::Tthis => match this_class {
                None => unenforced(PessimiseReason::PRthis),
                Some(c) => {
                    if CA::is_final(c) && CA::get_tparams(c).is_empty() {
                        Enf::Enforced(ty.clone())
                    } else {
                        unenforced(PessimiseReason::PRthis)
                    }
                }
            },
            Ty_::Tapply(id_and_args) => {
                let (pos_id, tyl) = &**id_and_args;
                let name = pos_id.id().as_str();
                match &tyl[..] {
                    [ty1, ty2]
                        if top_enforced
                            && name == sn::collections::DICT
                            && is_arraykey(ty1)
                            && is_mixed(ty2) =>
                    {
                        Enf::Enforced(ty.clone())
                    }
                    [ty1]
                        if top_enforced && name == sn::collections::KEYSET && is_arraykey(ty1) =>
                    {
                        Enf::Enforced(ty.clone())
                    }
                    [ty1] if top_enforced && name == sn::collections::VEC && is_mixed(ty1) => {
                        Enf::Enforced(ty.clone())
                    }
                    /* Look through supportdyn, just as we look through ~ */
                    [ty] if name == sn::classes::SUPPORT_DYN => {
                        enforcement(closure, is_dynamic_enforceable, ctx, visited, ty)
                    }
                    tyl => {
                        /* Cyclic type definition error will be produced elsewhere */
                        if visited.contains(name) {
                            unenforced(PessimiseReason::PRopaque)
                        } else {
                            /* The pessimised definition depends on the class or typedef being referenced,
                            but we aren't adding any dependency edges here. It is therefore critical that
                            we are sure thay are added elsewhere. Currently, that is when we revisit this type
                            in Typing_enforceability when we are typechecking the function/property definition
                            it is part of. */
                            match CA::get_class_or_typedef(ctx, name) {
                                Some(ClassOrTypedefResult::TypedefResult(td)) => {
                                    match &td.type_assignment {
                                        TypedefTypeAssignment::CaseType(
                                            TypedefCaseTypeVariant { hint: td_type, .. },
                                            variants,
                                        ) if variants.is_empty() => {
                                            /* Expand type definition one step and compute its enforcement.
                                             * While case types are Tnewtype in the type system, at runtime
                                             * they are enforced transparently. TODO(dreeves) Case types
                                             * may need to be intersected with their cover types at most. */
                                            enforcement(
                                                closure,
                                                is_dynamic_enforceable,
                                                ctx,
                                                &visited.update(name.to_string()),
                                                td_type,
                                            )
                                        }
                                        TypedefTypeAssignment::SimpleTypeDef(
                                            aast::TypedefVisibility::Transparent,
                                            td_type,
                                        ) => enforcement(
                                            closure,
                                            is_dynamic_enforceable,
                                            ctx,
                                            &visited.update(name.to_string()),
                                            td_type,
                                        ),
                                        TypedefTypeAssignment::CaseType(..) => {
                                            unenforced(PessimiseReason::PRcase)
                                        }
                                        TypedefTypeAssignment::SimpleTypeDef(
                                            aast::TypedefVisibility::Opaque,
                                            td_type,
                                        ) => {
                                            let td_pos = &td.pos;
                                            let td_as_constraint = &td.as_constraint;
                                            let transparent = ty_pos.file() == td_pos.file();
                                            let exp_ty = enforcement(
                                                closure,
                                                is_dynamic_enforceable,
                                                ctx,
                                                &visited.update(name.to_string()),
                                                td_type,
                                            );
                                            if transparent {
                                                /* When transparent, look through to the RHS. But if the RHS
                                                 * resolves to an opaque type (PRopaque), don't expose its
                                                 * enforcement - that would leak the inner type's constraint
                                                 * through this transparent wrapper. */
                                                match exp_ty {
                                                    Enf::Unenforced(
                                                        _,
                                                        PessimiseReason::PRopaque,
                                                    ) => unenforced(PessimiseReason::PRopaque),
                                                    _ => exp_ty,
                                                }
                                            } else {
                                                /* Similar to enums, newtypes must not be pessimised to their
                                                 * enforced types, otherwise for `newtype N = int;`, pessimising
                                                 * `N` to `~N & int` tells the truth, but breaks N's opaqueness.
                                                 * For `newtype N as O = P;` we want to allow `N` to override `O`,
                                                 * but it is not safe to just use the constraint to get `~N & O`.
                                                 * Consider `newtype N as IE = IE;` and `enum IE : int { A = 4; }`.
                                                 * `N` will only be enforced at `int`, whereas `~N & IE` lies
                                                 * that the value is definitely a member of `IE`. We could look at
                                                 * the enforcement of `O`, but it is valid to have newtypes point
                                                 * to enforced values but be constrained by unenforced ones, e.g.
                                                 * `newtype N as G<int> = int; newtype G<T> as T = T;`. Looking at
                                                 * `N`'s constraint's enforcement would take us to just `~N`. This
                                                 * could not override a non-pessimised `int`, which is a shame
                                                 * because we know N is an int.
                                                 *
                                                 * To compromise, if `newtype N as O = P;` is enforced at `Q`, we
                                                 * pessimise `N` to `~N & (O | Q)`. This allows the value to flow
                                                 * into an `O` if `Q` is a subtype of `O`, while making sure we
                                                 * are intersecting only with something the runtime verifies i.e.
                                                 * some type at least as large as `Q`.
                                                 * */
                                                match (exp_ty, td_as_constraint) {
                                                    (
                                                        Enf::Enforced(ty)
                                                        | Enf::Unenforced(Some(ty), _),
                                                        Some(cstr),
                                                    ) => Enf::Unenforced(
                                                        Some(make_type_union(
                                                            cstr.reason().clone(),
                                                            vec![cstr.clone(), ty],
                                                        )),
                                                        PessimiseReason::PRopaque,
                                                    ),
                                                    _ => unenforced(PessimiseReason::PRopaque),
                                                }
                                            }
                                        }
                                        TypedefTypeAssignment::SimpleTypeDef(
                                            aast::TypedefVisibility::OpaqueModule,
                                            _,
                                        ) => unenforced(PessimiseReason::PRopaque),
                                    }
                                }
                                Some(ClassOrTypedefResult::ClassResult(cls)) => {
                                    match CA::get_enum_type(&cls) {
                                        Some(et) => {
                                            /* for `enum E : int`, pessimising `E` to `~E & int` violates the
                                             * opacity of the enum, allowing the value to flow to a position
                                             * expecting `int`. We instead weaken our pessimised type to
                                             * `~E & arraykey`. For transparent enums `enum F : int as int`,
                                             * we pessimise to `~F & int`. */
                                            let intersected_type = match et.constraint {
                                                Some(constraint) => constraint,
                                                None => {
                                                    make_type_arraykey(et.base.reason().clone())
                                                }
                                            };
                                            make_unenforced(
                                                enforcement(
                                                    closure,
                                                    is_dynamic_enforceable,
                                                    ctx,
                                                    &visited.update(name.to_string()),
                                                    &intersected_type,
                                                ),
                                                PessimiseReason::PRenum,
                                            )
                                        }
                                        None => {
                                            let tparams = CA::get_tparams(&cls);
                                            // `List.for_all2`: `Unequal_lengths`, or
                                            // `Ok` of whether all pairs satisfy the
                                            // predicate.
                                            let all = if tyl.len() != tparams.len() {
                                                None
                                            } else {
                                                Some(tyl.iter().zip(tparams.iter()).all(
                                                    |(targ, tparam)| match tparam.reified {
                                                        aast::ReifyKind::Erased => false,
                                                        aast::ReifyKind::SoftReified => false,
                                                        aast::ReifyKind::Reified => {
                                                            match enforcement(
                                                                closure, true, ctx, visited, targ,
                                                            ) {
                                                                Enf::Unenforced(..) => false,
                                                                Enf::Enforced(_) => true,
                                                            }
                                                        }
                                                    },
                                                ))
                                            };
                                            match all {
                                                Some(false) | None => {
                                                    unenforced(PessimiseReason::PRgenericApply)
                                                }
                                                Some(true) => Enf::Enforced(ty.clone()),
                                            }
                                        }
                                    }
                                }
                                None => unenforced(PessimiseReason::PRgenericApply),
                            }
                        }
                    }
                }
            }
            Ty_::Tgeneric(_) => {
                /* Previously we allowed dynamic ~> T when T is an __Enforceable generic,
                 * that is, when it's valid on the RHS of an `is` or `as` expression.
                 * However, `is` / `as` checks have different behavior than runtime checks
                 * for `tuple`s and `shapes`s; `is` / `as` will shallow-ly check declared
                 * fields but typehint enforcement only checks that we have the right
                 * array type (`varray` for `tuple`, `darray` for `shape`). This means
                 * it's unsound to allow this coercion.
                 *
                 * Additionally, higher kinded generics (i.e., with type arguments) cannot
                 * be enforced at the moment; they are disallowed to have upper bounds.
                 */
                unenforced(PessimiseReason::PRgenericParam)
            }
            Ty_::Trefinement(_) => unenforced(PessimiseReason::PRrefinement),
            Ty_::Taccess(taccess) if tc_enforced => {
                match resolve_access::<CA>(
                    this_class,
                    ctx,
                    &taccess.ty,
                    taccess.type_const.id().as_str(),
                ) {
                    None => unenforced(PessimiseReason::PRtypeconst),
                    Some(ty) => enforcement(closure, is_dynamic_enforceable, ctx, visited, &ty),
                }
            }
            Ty_::Taccess(_) => unenforced(PessimiseReason::PRtypeconst),
            Ty_::Tlike(ty) => enforcement(closure, is_dynamic_enforceable, ctx, visited, ty),
            Ty_::Tprim(aast::Tprim::Tvoid | aast::Tprim::Tnoreturn) => {
                unenforced(PessimiseReason::PRvoidOrNoreturn)
            }
            Ty_::Tprim(_) => Enf::Enforced(ty.clone()),
            Ty_::Tany => Enf::Enforced(ty.clone()),
            Ty_::Tnonnull => Enf::Enforced(ty.clone()),
            Ty_::Tdynamic => {
                if is_dynamic_enforceable {
                    Enf::Enforced(ty.clone())
                } else {
                    unenforced(PessimiseReason::PRdynamic)
                }
            }
            Ty_::Ttuple(_) | Ty_::Tshape(_) => unenforced(PessimiseReason::PRtupleOrShape),
            Ty_::Tunion(tyl) if tyl.is_empty() => Enf::Enforced(ty.clone()),
            /* Shouldn't happen */
            Ty_::Tunion(_) | Ty_::Tintersection(_) | Ty_::Twildcard => {
                unenforced(PessimiseReason::PRunionOrIntersection)
            }
            Ty_::Tfun(_) => unenforced(PessimiseReason::PRfun),
            Ty_::Tmixed => Enf::Enforced(ty.clone()),
            Ty_::TvecOrDict(key_and_val) => {
                let (ty1, ty2) = &**key_and_val;
                if top_enforced && is_arraykey(ty1) && is_mixed(ty2) {
                    Enf::Enforced(ty.clone())
                } else {
                    /* With no parameters, we enforce varray_or_darray just like array */
                    let el_ty = ty2;
                    if is_any(el_ty) {
                        Enf::Enforced(ty.clone())
                    } else {
                        unenforced(PessimiseReason::PRgenericApply)
                    }
                }
            }
            Ty_::Toption(ty_) => {
                match enforcement(closure, is_dynamic_enforceable, ctx, visited, ty_) {
                    // `Enforced ty` in the OCaml is the type inside the
                    // option: the name shadows the one of the option.
                    Enf::Enforced(_) => Enf::Enforced(ty_.clone()),
                    Enf::Unenforced(Some(ety), pr) => {
                        Enf::Unenforced(Some(Ty::new(ty_.reason().clone(), Ty_::Toption(ety))), pr)
                    }
                    Enf::Unenforced(None, pr) => Enf::Unenforced(None, pr),
                }
            }
            Ty_::TclassPtr(_) => {
                /* TODO(T199606542) See if it is necessary to mimic enforcement of classname<T>
                 * Ultimately, all class<T> types will enforce that at least a class pointer
                 * flowed through them, if not the specific class. */
                unenforced(PessimiseReason::PRclassptr)
            }
        }
    }

    /// When `top_enforced` is true, erased container type arguments are
    /// treated as enforced if they are top types for their positions. e.g.
    /// dict<arraykey, mixed>
    pub fn get_enforcement<CA: ContextAccess>(
        top_enforced: bool,
        return_from_async: bool,
        this_class: Option<&CA::ClassT>,
        ctx: &CA::T,
        ty: &Ty<R>,
    ) -> Enf {
        let tcopt = CA::get_tcopt(ctx);
        let tc_enforced = tcopt
            .tco_legacy_experimental_features
            .contains("experimental_consider_type_const_enforceable");
        let ty_pos = ty.pos();
        let closure = Closure::<CA> {
            top_enforced,
            this_class,
            tc_enforced,
            ty_pos,
        };
        let empty = crate::im_empty::ord_set();
        if return_from_async {
            match ty.node_ref() {
                Ty_::Tapply(id_and_args)
                    if id_and_args.1.len() == 1
                        && sn::classes::AWAITABLE == id_and_args.0.id().as_str() =>
                {
                    enforcement(&closure, false, ctx, &empty, &id_and_args.1[0])
                }
                _ => enforcement(&closure, false, ctx, &empty, ty),
            }
        } else {
            enforcement(&closure, false, ctx, &empty, ty)
        }
    }
}

/// `Provider with type class_t := Shallow_decl_defs.shallow_class`
pub trait ShallowProvider: Provider<ClassT = Arc<ShallowClass<R>>> {}

impl<P: Provider<ClassT = Arc<ShallowClass<R>>>> ShallowProvider for P {}

/// `ShallowContextAccess (Provider)`
pub struct ShallowContextAccess<P>(PhantomData<P>);

impl<P: ShallowProvider> Provider for ShallowContextAccess<P> {
    type T = P::T;

    type ClassT = Arc<ShallowClass<R>>;

    fn get_tcopt(t: &Self::T) -> &Arc<TypecheckerOptions> {
        P::get_tcopt(t)
    }

    fn get_class_or_typedef(t: &Self::T, name: &str) -> Option<ClassOrTypedefResult<Self::ClassT>> {
        P::get_class_or_typedef(t, name)
    }

    fn get_class(t: &Self::T, name: &str) -> Option<Self::ClassT> {
        P::get_class(t, name)
    }
}

impl<P: ShallowProvider> ContextAccess for ShallowContextAccess<P> {
    fn get_typeconst_type(ctx: &Self::T, c: &Self::ClassT, id: &str) -> Option<Ty<R>> {
        use decl::Typeconst;
        /* Look for id directly defined in the given shallow class. Assume there is
        only one, since it is an error to have multiple definitions. */
        let find_locally = |c: &ShallowClass<R>| -> Option<Typeconst<R>> {
            c.typeconsts.iter().find_map(|stc| {
                if id == stc.name.id().as_str() {
                    Some(stc.kind.clone())
                } else {
                    None
                }
            })
        };
        fn class_type_to_shallow_class<P: ShallowProvider>(
            ctx: &P::T,
            cty: &Ty<R>,
        ) -> Option<Arc<ShallowClass<R>>> {
            match cty.node_ref() {
                Ty_::Tapply(id_and_args) => P::get_class(ctx, id_and_args.0.id().as_str()),
                _ => None,
            }
        }
        /* Find the first concrete definition of id in the list. If there is none, return
        the first abstract one, kept in found_abstract */
        fn find_in_list<P: ShallowProvider>(
            ctx: &P::T,
            find_locally: &dyn Fn(&ShallowClass<R>) -> Option<Typeconst<R>>,
            visited: &im::OrdSet<String>,
            mut found_abstract: Option<Typeconst<R>>,
            ctys: &[&Ty<R>],
        ) -> Option<Typeconst<R>> {
            for cty in ctys {
                let c = class_type_to_shallow_class::<P>(ctx, cty);
                match c {
                    None => {}
                    Some(c) => match find_in_class::<P>(ctx, find_locally, visited, &c) {
                        None => {}
                        Some(new_abstract @ Typeconst::TCAbstract(_)) => match found_abstract {
                            None => found_abstract = Some(new_abstract),
                            _ => {}
                        },
                        Some(res @ Typeconst::TCConcrete(_)) => return Some(res),
                    },
                }
            }
            found_abstract
        }
        /* Look for id in c, either locally, or inherited */
        fn find_in_class<P: ShallowProvider>(
            ctx: &P::T,
            find_locally: &dyn Fn(&ShallowClass<R>) -> Option<Typeconst<R>>,
            visited: &im::OrdSet<String>,
            c: &ShallowClass<R>,
        ) -> Option<Typeconst<R>> {
            if visited.contains(c.name.id().as_str()) {
                None
            } else {
                match find_locally(c) {
                    Some(tc) => Some(tc),
                    None => find_in_list::<P>(
                        ctx,
                        find_locally,
                        &visited.update(c.name.id().as_str().to_string()),
                        None,
                        &(c.extends.iter())
                            .chain(c.implements.iter())
                            .chain(c.uses.iter())
                            .chain(c.req_extends.iter())
                            .chain(c.req_implements.iter())
                            .collect::<Vec<_>>(),
                    ),
                }
            }
        }
        let tc = find_in_class::<P>(ctx, &find_locally, &crate::im_empty::ord_set(), c)?;
        match tc {
            Typeconst::TCAbstract(abstract_) => abstract_.as_constraint,
            Typeconst::TCConcrete(concrete) => Some(concrete.ty),
        }
    }

    fn get_tparams(sc: &Self::ClassT) -> Vec<decl::Tparam<R, Ty<R>>> {
        sc.tparams.to_vec()
    }

    fn is_final(sc: &Self::ClassT) -> bool {
        sc.is_final
    }

    fn get_name(cd: &Self::ClassT) -> String {
        cd.name.id().as_str().to_string()
    }

    fn get_enum_type(sc: &Self::ClassT) -> Option<decl::EnumType<R>> {
        sc.enum_type.clone()
    }
}

pub mod pessimize {
    use ty::decl::ty::FunParamFlags;
    use ty::decl::ty::FunTypeFlags;

    use super::*;

    /// `module E = Enforce (ShallowContextAccess (Provider))`
    fn get_enforcement<P: ShallowProvider>(
        top_enforced: bool,
        return_from_async: bool,
        this_class: Option<&Arc<ShallowClass<R>>>,
        ctx: &P::T,
        ty: &Ty<R>,
    ) -> Enf {
        enforce::get_enforcement::<ShallowContextAccess<P>>(
            top_enforced,
            return_from_async,
            this_class,
            ctx,
            ty,
        )
    }

    fn make_like_type(
        reason: R,
        intersect_with: Option<Ty<R>>,
        return_from_async: bool,
        ty: &Ty<R>,
    ) -> Ty<R> {
        fn like_and_intersect(intersect_with: Option<Ty<R>>, r: R, ty: &Ty<R>) -> Ty<R> {
            let like_ty = make_type_like(r.clone(), ty);
            match intersect_with {
                None => like_ty,
                Some(enf_ty) => make_type_intersection(r, vec![enf_ty, like_ty]),
            }
        }
        fn like_if_not_void(intersect_with: Option<Ty<R>>, reason: R, ty: &Ty<R>) -> Ty<R> {
            match ty.node_ref() {
                Ty_::Tprim(aast::Tprim::Tvoid | aast::Tprim::Tnoreturn) => ty.clone(),
                _ => like_and_intersect(intersect_with, reason, ty),
            }
        }
        if return_from_async {
            match ty.node_ref() {
                Ty_::Tapply(id_and_args)
                    if id_and_args.1.len() == 1
                        && sn::classes::AWAITABLE == id_and_args.0.id().as_str() =>
                {
                    let (pos_name, tyl) = &**id_and_args;
                    // The reason is the one of the type argument, as in the
                    // OCaml (where `ty` is rebound to it).
                    let ty = &tyl[0];
                    Ty::new(
                        ty.reason().clone(),
                        Ty_::Tapply(Box::new((
                            pos_name.clone(),
                            [like_and_intersect(intersect_with, reason, ty)].into(),
                        ))),
                    )
                }
                _ => like_if_not_void(intersect_with, reason, ty),
            }
        } else {
            like_if_not_void(intersect_with, reason, ty)
        }
    }

    pub fn implicit_sdt_for_class<P: ShallowProvider>(
        ctx: &P::T,
        this_class: Option<&Arc<ShallowClass<R>>>,
    ) -> bool {
        super::implicit_sdt_for_class(P::get_tcopt(ctx), this_class.map(|c| &**c))
    }

    /// Pessimise the type of a property if in implicit pessimisation mode and
    /// no_auto_likes is false
    pub fn pessimise_prop_type<P: ShallowProvider>(
        is_xhp_attr: bool,
        this_class: Option<&Arc<ShallowClass<R>>>,
        no_auto_likes: bool,
        ctx: &P::T,
        p: &BPos,
        ty: &Ty<R>,
    ) -> Ty<R> {
        if implicit_sdt_for_class::<P>(ctx, this_class) && !no_auto_likes {
            match get_enforcement::<P>(true, false, this_class, ctx, ty) {
                Enf::Enforced(_) => {
                    if is_xhp_attr {
                        make_like_type(
                            reason_pessimised_prop(p, PessimiseReason::PRxhp),
                            None,
                            false,
                            ty,
                        )
                    } else {
                        ty.clone()
                    }
                }
                Enf::Unenforced(_, pr) => {
                    make_like_type(reason_pessimised_prop(p, pr), None, false, ty)
                }
            }
        } else {
            ty.clone()
        }
    }

    fn update_return_ty(ft: decl::FunType<R, Ty<R>>, ty: Ty<R>) -> decl::FunType<R, Ty<R>> {
        decl::FunType { ret: ty, ..ft }
    }

    /* We do not pessimise parameter types *except* for inout parameters,
     * which we pessimise regardless of enforcement, because override doesn't
     * preserve enforcement e.g. `inout int` might beoverridden by `inout C::MyTypeConstant`
     */
    fn pessimise_param_type(
        pessimise_param: bool,
        fp: &decl::FunParam<R, Ty<R>>,
    ) -> decl::FunParam<R, Ty<R>> {
        // `get_fp_mode fp`
        if !fp.flags.contains(FunParamFlags::INOUT) {
            /* FPnormal */
            if pessimise_param {
                decl::FunParam {
                    ty: make_like_type(
                        reason_support_dynamic_type_assume(&fp.pos),
                        None,
                        false,
                        &fp.ty,
                    ),
                    ..fp.clone()
                }
            } else {
                fp.clone()
            }
        } else {
            /* FPinout */
            decl::FunParam {
                ty: make_like_type(reason_pessimised_inout(&fp.pos), None, false, &fp.ty),
                ..fp.clone()
            }
        }
    }

    /*
      How we pessimise a function depends on how the type is enforced and where the
      function is defined.

      The goal is to pessimise non-enforced return types to like types, while also
      avoiding hierarchy errors.

      Abstract methods do not have bodies to enforce anything, so we
      always pessimise their returns. For Concrete methods, if the type is only partially
      enforced, we pessimise and also intersect with the partially enforced type to
      avoid hierarchy errors.

    */
    /// If the return type is not enforceable, turn it into a like type (~ty)
    /// otherwise return the original function type. Also add
    /// supportdyn<mixed> to the type parameters.
    pub fn pessimise_fun_type<P: ShallowProvider>(
        fun_kind: FunKind,
        this_class: Option<&Arc<ShallowClass<R>>>,
        no_auto_likes: bool,
        cannot_override: bool,
        ctx: &P::T,
        p: &BPos,
        ty: &Ty<R>,
    ) -> Ty<R> {
        match ty.node_ref() {
            Ty_::Tfun(ft) => {
                let ft = decl::FunType {
                    tparams: add_supportdyn_constraints(p, &ft.tparams).into(),
                    ..(**ft).clone()
                };
                if no_auto_likes {
                    Ty::new(ty.reason().clone(), Ty_::Tfun(Box::new(ft)))
                } else {
                    let return_from_async = ft.flags.contains(FunTypeFlags::ASYNC);
                    let ret_ty = ft.ret.clone();
                    let pessimise_param = ft.params.len() <= 1
                        && match fun_kind {
                            FunKind::Function => {
                                match get_enforcement::<P>(
                                    true,
                                    return_from_async,
                                    this_class,
                                    ctx,
                                    &ret_ty,
                                ) {
                                    Enf::Enforced(_) => true,
                                    _ => false,
                                }
                            }
                            FunKind::ConcreteMethod if cannot_override => {
                                match get_enforcement::<P>(
                                    true,
                                    return_from_async,
                                    this_class,
                                    ctx,
                                    &ret_ty,
                                ) {
                                    Enf::Enforced(_) => true,
                                    _ => false,
                                }
                            }
                            _ => false,
                        };
                    let ft = decl::FunType {
                        params: ft
                            .params
                            .iter()
                            .map(|fp| pessimise_param_type(pessimise_param, fp))
                            .collect(),
                        ..ft
                    };
                    /* For the this type, although not enforced (because of generics), it's very
                     * unlikely that we will get errors if we do not pessimise it.
                     */
                    let optimistically_do_not_pessimise = match ret_ty.node_ref() {
                        Ty_::Tthis => true,
                        _ => false,
                    };
                    match fun_kind {
                        FunKind::AbstractMethod => {
                            let reason = match get_enforcement::<P>(
                                false,
                                return_from_async,
                                this_class,
                                ctx,
                                &ret_ty,
                            ) {
                                Enf::Enforced(_) => reason_pessimised_return(
                                    ret_ty.pos(),
                                    PessimiseReason::PRabstract,
                                ),
                                Enf::Unenforced(_, pr) => {
                                    reason_pessimised_return(ret_ty.pos(), pr)
                                }
                            };
                            let ret = make_like_type(reason, None, return_from_async, &ret_ty);
                            Ty::new(
                                ty.reason().clone(),
                                Ty_::Tfun(Box::new(update_return_ty(ft, ret))),
                            )
                        }
                        FunKind::ConcreteMethod | FunKind::Function => {
                            if optimistically_do_not_pessimise {
                                Ty::new(ty.reason().clone(), Ty_::Tfun(Box::new(ft)))
                            } else {
                                match get_enforcement::<P>(
                                    cannot_override,
                                    return_from_async,
                                    this_class,
                                    ctx,
                                    &ret_ty,
                                ) {
                                    Enf::Enforced(_) => {
                                        Ty::new(ty.reason().clone(), Ty_::Tfun(Box::new(ft)))
                                    }
                                    Enf::Unenforced(enf_ty_opt, pr) => {
                                        /* For partially enforced type such as enums, we intersect with the
                                         * base type for concrete method return types in order to avoid
                                         * issues with hierarchies e.g. overriding a method that returns
                                         * the base type
                                         */
                                        let intersect_with = match fun_kind {
                                            FunKind::ConcreteMethod => enf_ty_opt,
                                            _ => None,
                                        };
                                        let ret = make_like_type(
                                            reason_pessimised_return(ret_ty.pos(), pr),
                                            intersect_with,
                                            return_from_async,
                                            &ret_ty,
                                        );
                                        Ty::new(
                                            ty.reason().clone(),
                                            Ty_::Tfun(Box::new(update_return_ty(ft, ret))),
                                        )
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => ty.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use pos::FunName;
    use pos::Prefix;
    use pos::RelativePath;
    use pos::TypeName;
    use ty::decl::ty::FunParamFlags;
    use ty::reason::Reason;

    use super::*;

    /// `Decl_enforceability_shallow.Provider`, over the shallow decls of the
    /// context.
    struct ShallowDecls;

    impl Provider for ShallowDecls {
        type T = Arc<Ctx>;

        type ClassT = Arc<ShallowClass<R>>;

        fn get_tcopt(ctx: &Arc<Ctx>) -> &Arc<TypecheckerOptions> {
            &ctx.tco
        }

        fn get_class_or_typedef(
            ctx: &Arc<Ctx>,
            name: &str,
        ) -> Option<ClassOrTypedefResult<Self::ClassT>> {
            match ctx.shallow_decls.get_typedef(TypeName::new(name)).unwrap() {
                Some(td) => Some(ClassOrTypedefResult::TypedefResult(td)),
                None => Self::get_class(ctx, name).map(ClassOrTypedefResult::ClassResult),
            }
        }

        fn get_class(ctx: &Arc<Ctx>, name: &str) -> Option<Self::ClassT> {
            ctx.shallow_decls.get_class(TypeName::new(name)).unwrap()
        }
    }

    type CA = ShallowContextAccess<ShallowDecls>;

    const HEADER: &str = "<?hh\n<<file:__EnableUnstableFeatures('union_intersection_type_hints', 'like_type_hints', 'case_types', 'class_type')>>\n";

    fn make_ctx(files: &[&str], set: impl FnOnce(&mut TypecheckerOptions)) -> Arc<Ctx> {
        let mut tco = TypecheckerOptions::default();
        tco.po.allow_unstable_features = true;
        set(&mut tco);
        let ctx = Arc::new(Ctx::new(Path::new("/"), tco).unwrap());
        for (i, src) in files.iter().enumerate() {
            let path = RelativePath::new(Prefix::Root, format!("test{}.php", i));
            ctx.files.set(path, format!("{}{}", HEADER, src));
            let decls = ctx.decl_parser.parse(path).unwrap();
            assert!(!decls.is_empty());
            ctx.declare_file(path, decls);
        }
        ctx
    }

    fn fun_ty(ctx: &Ctx, name: &str) -> Ty<R> {
        let decl = ctx.shallow_decls.get_fun(FunName::new(name)).unwrap();
        decl.unwrap_or_else(|| panic!("no function {}", name))
            .ty
            .clone()
    }

    fn fun_type(ty: &Ty<R>) -> &decl::FunType<R, Ty<R>> {
        match ty.node_ref() {
            Ty_::Tfun(ft) => ft,
            ty_ => panic!("not a function type: {:?}", ty_),
        }
    }

    /// The types of the parameters of a function, and of its return.
    fn tys(ctx: &Ctx, name: &str) -> (Vec<Ty<R>>, Ty<R>) {
        let ty = fun_ty(ctx, name);
        let ft = fun_type(&ty);
        (
            ft.params.iter().map(|fp| fp.ty.clone()).collect(),
            ft.ret.clone(),
        )
    }

    fn class(ctx: &Arc<Ctx>, name: &str) -> Arc<ShallowClass<R>> {
        ShallowDecls::get_class(ctx, name).unwrap_or_else(|| panic!("no class {}", name))
    }

    /// The enforcement, in short: "E <ty>" when enforced, "U <reason>" when
    /// not, or "U <reason> <ty>" when partially enforced.
    fn show(enf: &Enf) -> String {
        match enf {
            Enf::Enforced(ty) => format!("E {:?}", ty),
            Enf::Unenforced(None, pr) => format!("U {:?}", pr),
            Enf::Unenforced(Some(ty), pr) => format!("U {:?} {:?}", pr, ty),
        }
    }

    fn enforcements(
        ctx: &Arc<Ctx>,
        fun: &str,
        top_enforced: bool,
        this_class: Option<&Arc<ShallowClass<R>>>,
    ) -> Vec<String> {
        let (params, _) = tys(ctx, fun);
        params
            .iter()
            .map(|ty| {
                show(&enforce::get_enforcement::<CA>(
                    top_enforced,
                    false,
                    this_class,
                    ctx,
                    ty,
                ))
            })
            .collect()
    }

    const DECLS: &str = "
        final class Fin {}
        class C {}
        class G<T> {}
        class RG<reify T> {}
        enum E: int { A = 1; }
        enum F: int as int { A = 1; }
        type Tr = ?int;
        newtype Nt = int;
        type Cyc1 = Cyc2;
        type Cyc2 = Cyc1;
        case type One = int;
        case type Two = int | string;
        abstract class WithTC {
          abstract const type TA as arraykey;
          const type TC = int;
          const type TD = this::TC;
          const type TLoop = this::TLoop;
        }
        function prims(int $a, ?int $b, mixed $c, nonnull $d, dynamic $e, nothing $f, ~int $g, null $h): void {}
        function collections(vec<int> $a, vec<mixed> $b, dict<arraykey, mixed> $c, keyset<arraykey> $d, dict<string, mixed> $e, vec_or_dict<arraykey, mixed> $f, vec_or_dict<int> $g): void {}
        function classes<T>(C $a, G<int> $b, RG<int> $c, RG<vec<int>> $d, RG<dynamic> $e, G $f, Unknown $g, T $h, this $i): void {}
        function enums(E $a, F $b, ?E $c): void {}
        function typedefs(Tr $a, Nt $b, Other $c, OtherAs $d, OtherAsE $e, Cyc1 $f, One $g, Two $h, OtherModule $i): void {}
        function structural((int, string) $a, shape('a' => int) $b, (function(): int) $c, class<C> $d, (int | string) $e, (C & Fin) $f, C with { type T = int } $g): void {}
        function access(WithTC::TC $a, WithTC::TA $b, WithTC::TD $c, WithTC::TLoop $d, WithTC::TNone $e, Unknown::T $f): void {}
        async function asynchronous(): Awaitable<int> { return 1; }
        function returns_void(): void {}
    ";

    const OTHER_FILE: &str = "
        newtype Other = int;
        newtype OtherAs as arraykey = int;
        newtype OtherAsE as arraykey = E;
        module newtype OtherModule = int;
    ";

    #[test]
    fn enforcement() {
        let ctx = make_ctx(&[DECLS, OTHER_FILE], |_| {});
        let get = |fun: &str, top_enforced: bool| enforcements(&ctx, fun, top_enforced, None);

        assert_eq!(
            get("\\prims", false),
            // `?int` is enforced at `int`, and `~int` too.
            [
                "E int",
                "E int",
                "E mixed",
                "E nonnull",
                "U PRdynamic",
                "E nothing",
                "E int",
                "E null"
            ]
        );
        assert_eq!(
            get("\\collections", false),
            [
                "U PRgenericApply",
                "U PRgenericApply",
                "U PRgenericApply",
                "U PRgenericApply",
                "U PRgenericApply",
                "U PRgenericApply",
                "U PRgenericApply",
            ]
        );
        // Top types as arguments of erased containers are enforced.
        assert_eq!(
            get("\\collections", true),
            [
                "U PRgenericApply",
                "E HH\\vec<mixed>",
                "E HH\\dict<arraykey, mixed>",
                "E HH\\keyset<arraykey>",
                "U PRgenericApply",
                "E vec_or_dict<arraykey, mixed>",
                "U PRgenericApply",
            ]
        );
        assert_eq!(
            get("\\classes", false),
            [
                "E C",
                "U PRgenericApply",
                "E RG<int>",
                "U PRgenericApply",
                // `dynamic` is enforceable as the argument of a reified generic.
                "E RG<dynamic>",
                "U PRgenericApply",
                "U PRgenericApply",
                "U PRgenericParam",
                "U PRthis",
            ]
        );
        assert_eq!(
            get("\\enums", false),
            ["U PRenum arraykey", "U PRenum int", "U PRenum ?arraykey"]
        );
        assert_eq!(
            get("\\typedefs", false),
            [
                "E int",
                // A newtype of the same file is looked through.
                "E int",
                "U PRopaque",
                "U PRopaque (arraykey | int)",
                "U PRopaque (arraykey | arraykey)",
                "U PRopaque",
                "E int",
                "U PRcase",
                "U PRopaque",
            ]
        );
        assert_eq!(
            get("\\structural", false),
            [
                "U PRtupleOrShape",
                "U PRtupleOrShape",
                "U PRfun",
                "U PRclassptr",
                "U PRunionOrIntersection",
                "U PRunionOrIntersection",
                "U PRrefinement",
            ]
        );
        assert_eq!(get("\\access", false), ["U PRtypeconst"; 6]);

        // `this` is enforced in a final class without type parameters.
        let this = &tys(&ctx, "\\classes").0[8];
        let enf = |c: &str| {
            show(&enforce::get_enforcement::<CA>(
                false,
                false,
                Some(&class(&ctx, c)),
                &ctx,
                this,
            ))
        };
        assert_eq!(enf("\\Fin"), "E this");
        assert_eq!(enf("\\C"), "U PRthis");

        // The type under `Awaitable` is the one that is enforced when
        // returning from an async function.
        let ret = tys(&ctx, "\\asynchronous").1;
        let enf = |return_from_async| {
            show(&enforce::get_enforcement::<CA>(
                false,
                return_from_async,
                None,
                &ctx,
                &ret,
            ))
        };
        assert_eq!(enf(true), "E int");
        assert_eq!(enf(false), "U PRgenericApply");
        let ret = tys(&ctx, "\\returns_void").1;
        assert_eq!(
            show(&enforce::get_enforcement::<CA>(
                false, false, None, &ctx, &ret
            )),
            "U PRvoidOrNoreturn"
        );

        // The reasons: the enum is enforced at `arraykey` with the reason of
        // its base; the bound of a newtype gives its reason to the union.
        let (enums, _) = tys(&ctx, "\\enums");
        let e = class(&ctx, "\\E");
        match enforce::get_enforcement::<CA>(false, false, None, &ctx, &enums[0]) {
            Enf::Unenforced(Some(ty), PessimiseReason::PRenum) => {
                assert_eq!(ty.reason(), e.enum_type.as_ref().unwrap().base.reason())
            }
            enf => panic!("{:?}", enf),
        }
        let (typedefs, _) = tys(&ctx, "\\typedefs");
        let other_as = ctx
            .shallow_decls
            .get_typedef(TypeName::new("\\OtherAs"))
            .unwrap()
            .unwrap();
        match enforce::get_enforcement::<CA>(false, false, None, &ctx, &typedefs[3]) {
            Enf::Unenforced(Some(ty), PessimiseReason::PRopaque) => {
                assert_eq!(
                    ty.reason(),
                    other_as.as_constraint.as_ref().unwrap().reason()
                )
            }
            enf => panic!("{:?}", enf),
        }
    }

    #[test]
    fn enforcement_of_type_constants() {
        let ctx = make_ctx(&[DECLS, OTHER_FILE], |tco| {
            tco.tco_legacy_experimental_features
                .insert("experimental_consider_type_const_enforceable".to_string());
        });
        assert_eq!(
            enforcements(&ctx, "\\access", false, None),
            [
                "E int",
                // The bound of an abstract type constant.
                "E arraykey",
                "E int",
                // A cycle, a missing constant, a missing class.
                "U PRtypeconst",
                "U PRtypeconst",
                "U PRtypeconst",
            ]
        );
    }

    #[test]
    fn typeconsts_of_shallow_classes() {
        let ctx = make_ctx(
            &["
                interface I { abstract const type T as arraykey; const type U = string; }
                interface J { const type T = int; }
                abstract class P implements I { abstract const type V; }
                trait Tr { const type W = bool; }
                class K extends P implements J { use Tr; const type V = float; }
                abstract class L extends P {}
                abstract class Loop1 extends Loop2 {}
                abstract class Loop2 extends Loop1 {}
            "],
            |_| {},
        );
        let get = |c: &str, id: &str| {
            CA::get_typeconst_type(&ctx, &class(&ctx, c), id).map(|ty| format!("{:?}", ty))
        };
        let some = |s: &str| Some(s.to_string());
        // Defined in the class.
        assert_eq!(get("\\K", "V"), some("float"));
        // The concrete definition wins over the abstract one found first.
        assert_eq!(get("\\K", "T"), some("int"));
        assert_eq!(get("\\K", "U"), some("string"));
        assert_eq!(get("\\K", "W"), some("bool"));
        // Only abstract: its bound, if it has one.
        assert_eq!(get("\\L", "T"), some("arraykey"));
        assert_eq!(get("\\L", "V"), None);
        assert_eq!(get("\\L", "Nope"), None);
        assert_eq!(get("\\Loop1", "T"), None);

        let k = class(&ctx, "\\K");
        assert_eq!(CA::get_name(&k), "\\K");
        assert!(!CA::is_final(&k));
        assert!(CA::get_tparams(&k).is_empty());
        assert!(CA::get_enum_type(&k).is_none());
    }

    const PESSIMISE: &str = "
        <<__NoAutoDynamic>> class NoAuto {}
        class C {}
        enum E: int { A = 1; }
        function enforced<T, <<__NoAutoBound>> Tu>(int $a, string $b): int { return 1; }
        function returns_this(): this {}
        function returns_void(vec<int> $a, vec<int> $b): void {}
        function returns_vec(): vec<int> { return vec[]; }
        function one_param(vec<int> $a): int { return 1; }
        function with_inout(inout int $a, int $b): int { return 1; }
        async function async_void(int $a, int $b): Awaitable<void> {}
        function returns_enum(): E { return E::A; }
    ";

    #[test]
    fn supportdyn_constraints() {
        let sdt = make_ctx(&[PESSIMISE], |tco| tco.po.everything_sdt = true);
        let no_sdt = make_ctx(&[PESSIMISE], |_| {});
        let ty = fun_ty(&no_sdt, "\\enforced");
        let ft = fun_type(&ty);
        let p = ty.pos();
        let bounds = |tparams: &[decl::Tparam<R, Ty<R>>]| -> Vec<Vec<String>> {
            tparams
                .iter()
                .map(|tp| {
                    tp.constraints
                        .iter()
                        .map(|(_, ty)| format!("{:?}", ty))
                        .collect()
                })
                .collect()
        };
        let expected = vec![vec!["HH\\supportdyn<mixed>".to_string()], vec![]];
        assert_eq!(bounds(&ft.tparams), vec![Vec::<String>::new(), vec![]]);
        let with = add_supportdyn_constraints(p, &ft.tparams);
        assert_eq!(bounds(&with), expected);
        let bound = &with[0].constraints[0].1;
        assert_eq!(bound.reason(), &R::witness_from_decl(p.clone()));
        assert_eq!(
            bound,
            &supportdyn_mixed(p, &R::witness_from_decl(p.clone()))
        );

        let no_auto = class(&sdt, "\\NoAuto");
        let c = class(&sdt, "\\C");
        let maybe = |ctx: &Ctx, this_class: Option<&ShallowClass<R>>| {
            bounds(&maybe_add_supportdyn_constraints(
                this_class,
                ctx,
                p,
                &ft.tparams,
            ))
        };
        assert_eq!(maybe(&sdt, None), expected);
        assert_eq!(maybe(&sdt, Some(&c)), expected);
        assert_eq!(maybe(&sdt, Some(&no_auto)), bounds(&ft.tparams));
        assert_eq!(maybe(&no_sdt, None), bounds(&ft.tparams));

        assert!(pessimize::implicit_sdt_for_class::<ShallowDecls>(
            &sdt, None
        ));
        assert!(pessimize::implicit_sdt_for_class::<ShallowDecls>(
            &sdt,
            Some(&c)
        ));
        assert!(!pessimize::implicit_sdt_for_class::<ShallowDecls>(
            &sdt,
            Some(&no_auto)
        ));
        assert!(!pessimize::implicit_sdt_for_class::<ShallowDecls>(
            &no_sdt,
            Some(&c)
        ));
    }

    #[test]
    fn pessimise_fun_type() {
        // (The decl parser is not asked to pessimise: the types below are the
        // ones written.)
        let ctx = make_ctx(&[PESSIMISE], |_| {});
        let pessimise =
            |fun: &str, fun_kind: FunKind, no_auto_likes: bool, cannot_override: bool| {
                let ty = fun_ty(&ctx, fun);
                let p = ty.pos().clone();
                pessimize::pessimise_fun_type::<ShallowDecls>(
                    fun_kind,
                    None,
                    no_auto_likes,
                    cannot_override,
                    &ctx,
                    &p,
                    &ty,
                )
            };
        let show = |ty: &Ty<R>| format!("{:?}", ty);

        // With enforced types, only the bounds of the type parameters change.
        let ty = pessimise("\\enforced", FunKind::Function, false, false);
        assert_eq!(
            show(&ty),
            "(function<T as HH\\supportdyn<mixed>, Tu>(int $a, string $b): int)"
        );
        assert_eq!(ty.reason(), fun_ty(&ctx, "\\enforced").reason());
        // The same when likes are not wanted, whatever the types.
        for fun in ["\\returns_vec", "\\one_param", "\\with_inout"] {
            assert_eq!(
                pessimise(fun, FunKind::ConcreteMethod, true, false),
                fun_ty(&ctx, fun)
            );
        }
        // `this` is optimistically not pessimised.
        assert_eq!(
            pessimise("\\returns_this", FunKind::ConcreteMethod, false, false),
            fun_ty(&ctx, "\\returns_this")
        );
        // `void` never becomes a like type, even for an abstract method.
        for fun_kind in [
            FunKind::Function,
            FunKind::ConcreteMethod,
            FunKind::AbstractMethod,
        ] {
            assert_eq!(
                pessimise("\\returns_void", fun_kind, false, false),
                fun_ty(&ctx, "\\returns_void")
            );
        }
        // Not a function type: unchanged.
        let int = fun_type(&fun_ty(&ctx, "\\enforced")).ret.clone();
        assert_eq!(
            pessimize::pessimise_fun_type::<ShallowDecls>(
                FunKind::Function,
                None,
                false,
                false,
                &ctx,
                int.pos(),
                &int
            ),
            int
        );

        let witness = |w: WitnessDecl<BPos>| R::mk(|| ReasonImpl::FromWitnessDecl(w));

        // An unenforced return type becomes a like type, whose reason says
        // why, at the position of the return type.
        let written = fun_ty(&ctx, "\\returns_vec");
        let ty = pessimise("\\returns_vec", FunKind::Function, false, false);
        assert_eq!(show(&ty), "(function(): ~HH\\vec<int>)");
        assert_eq!(ty.reason(), written.reason());
        let ret = &fun_type(&ty).ret;
        let written_ret = &fun_type(&written).ret;
        assert_eq!(
            ret.reason(),
            &witness(WitnessDecl::PessimisedReturn(
                written_ret.pos().clone(),
                PessimiseReason::PRgenericApply
            ))
        );
        match ret.node_ref() {
            Ty_::Tlike(inner) => assert_eq!(inner, written_ret),
            ty_ => panic!("{:?}", ty_),
        }

        // The only parameter of a function whose return type is enforced is
        // assumed to accept dynamic.
        let written = fun_ty(&ctx, "\\one_param");
        let ty = pessimise("\\one_param", FunKind::Function, false, false);
        assert_eq!(show(&ty), "(function(~HH\\vec<int> $a): int)");
        let param = &fun_type(&ty).params[0];
        let written_param = &fun_type(&written).params[0];
        assert_eq!(
            param.ty.reason(),
            &witness(WitnessDecl::SupportDynamicTypeAssume(
                written_param.pos.clone()
            ))
        );
        assert_eq!(fun_type(&ty).ret, fun_type(&written).ret);
        // Not so for a method that can be overridden, nor an abstract one
        // (whose return type is pessimised although enforced).
        assert_eq!(
            show(&pessimise(
                "\\one_param",
                FunKind::ConcreteMethod,
                false,
                false
            )),
            "(function(HH\\vec<int> $a): int)"
        );
        assert_eq!(
            show(&pessimise(
                "\\one_param",
                FunKind::ConcreteMethod,
                false,
                true
            )),
            "(function(~HH\\vec<int> $a): int)"
        );
        let ty = pessimise("\\one_param", FunKind::AbstractMethod, false, false);
        assert_eq!(show(&ty), "(function(HH\\vec<int> $a): ~int)");
        assert_eq!(
            fun_type(&ty).ret.reason(),
            &witness(WitnessDecl::PessimisedReturn(
                fun_type(&written).ret.pos().clone(),
                PessimiseReason::PRabstract
            ))
        );

        // inout parameters are pessimised whatever their type.
        let written = fun_ty(&ctx, "\\with_inout");
        assert!(
            fun_type(&written).params[0]
                .flags
                .contains(FunParamFlags::INOUT)
        );
        let ty = pessimise("\\with_inout", FunKind::Function, false, false);
        assert_eq!(show(&ty), "(function(inout ~int $a, int $b): int)");
        assert_eq!(
            fun_type(&ty).params[0].ty.reason(),
            &witness(WitnessDecl::PessimisedInout(
                fun_type(&written).params[0].pos.clone()
            ))
        );
        assert_eq!(fun_type(&ty).params[1], fun_type(&written).params[1]);

        // A partially enforced return type: the like type, intersected with
        // what is enforced for a concrete method.
        let written = fun_ty(&ctx, "\\returns_enum");
        let reason = witness(WitnessDecl::PessimisedReturn(
            fun_type(&written).ret.pos().clone(),
            PessimiseReason::PRenum,
        ));
        let ty = pessimise("\\returns_enum", FunKind::Function, false, false);
        assert_eq!(show(&ty), "(function(): ~E)");
        assert_eq!(fun_type(&ty).ret.reason(), &reason);
        let ty = pessimise("\\returns_enum", FunKind::ConcreteMethod, false, false);
        assert_eq!(show(&ty), "(function(): (arraykey & ~E))");
        let ret = &fun_type(&ty).ret;
        assert_eq!(ret.reason(), &reason);
        match ret.node_ref() {
            Ty_::Tintersection(tys) => {
                // `arraykey` has the reason of the base of the enum.
                let e = class(&ctx, "\\E");
                assert_eq!(tys[0].reason(), e.enum_type.as_ref().unwrap().base.reason());
                assert_eq!(tys[1].reason(), &reason);
            }
            ty_ => panic!("{:?}", ty_),
        }

        // Returning from an async function, the like type goes under
        // `Awaitable` (even for `void`), which takes the reason of its
        // argument.
        let written = fun_ty(&ctx, "\\async_void");
        let written_ret = &fun_type(&written).ret;
        let written_void = match written_ret.node_ref() {
            Ty_::Tapply(id_and_args) => id_and_args.1[0].clone(),
            ty_ => panic!("{:?}", ty_),
        };
        for fun_kind in [FunKind::Function, FunKind::AbstractMethod] {
            let ty = pessimise("\\async_void", fun_kind, false, false);
            assert_eq!(
                show(&ty),
                "(function(int $a, int $b): HH\\Awaitable<~void>)"
            );
            let ret = &fun_type(&ty).ret;
            assert_eq!(ret.reason(), written_void.reason());
            match ret.node_ref() {
                Ty_::Tapply(id_and_args) => {
                    assert_eq!(
                        id_and_args.1[0].reason(),
                        &witness(WitnessDecl::PessimisedReturn(
                            written_ret.pos().clone(),
                            PessimiseReason::PRvoidOrNoreturn
                        ))
                    );
                }
                ty_ => panic!("{:?}", ty_),
            }
        }
    }

    #[test]
    fn pessimise_prop_type() {
        let sdt = make_ctx(&[PESSIMISE], |tco| tco.po.everything_sdt = true);
        let no_sdt = make_ctx(&[PESSIMISE], |_| {});
        // Types as written (the decl parser of `no_sdt` does not pessimise).
        let (params, ret) = tys(&no_sdt, "\\one_param");
        let vec_int = params[0].clone();
        let int = ret;
        let prop = |ctx: &Arc<Ctx>, is_xhp_attr: bool, no_auto_likes: bool, ty: &Ty<R>| {
            pessimize::pessimise_prop_type::<ShallowDecls>(
                is_xhp_attr,
                None,
                no_auto_likes,
                ctx,
                ty.pos(),
                ty,
            )
        };
        // Not in implicit pessimisation mode, or no likes wanted: unchanged.
        assert_eq!(prop(&no_sdt, false, false, &vec_int), vec_int);
        assert_eq!(prop(&sdt, false, true, &vec_int), vec_int);
        // Enforced: unchanged.
        assert_eq!(prop(&sdt, false, false, &int), int);
        // Unenforced, or the attribute of an XHP class: a like type, whose
        // reason says why.
        let witness = |w: WitnessDecl<BPos>| R::mk(|| ReasonImpl::FromWitnessDecl(w));
        for (is_xhp_attr, ty, shown, pr) in [
            (
                false,
                &vec_int,
                "~HH\\vec<int>",
                PessimiseReason::PRgenericApply,
            ),
            (true, &int, "~int", PessimiseReason::PRxhp),
        ] {
            let pessimised = prop(&sdt, is_xhp_attr, false, ty);
            assert_eq!(format!("{:?}", pessimised), shown);
            assert_eq!(
                pessimised.reason(),
                &witness(WitnessDecl::PessimisedProp(ty.pos().clone(), pr))
            );
            match pessimised.node_ref() {
                Ty_::Tlike(inner) => assert_eq!(inner, ty),
                ty_ => panic!("{:?}", ty_),
            }
        }
    }
}
