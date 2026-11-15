// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_partial_enforcement.ml`. See `hh/PORTING.md`.
//!
//! The types here are declared types (`ty::decl::Ty`). `crate::typing_make_type`
//! has the functions of `Typing_make_type` for localized types only, so the
//! ones this module uses on declared types (`mixed`, `nullable`, `nonnull`,
//! `intersection`) are written below as in `typing_make_type.ml`: note that
//! `MakeType.mixed` is `?nonnull`, not `Tmixed`.

use oxidized::aast_defs::Tprim;
use oxidized::ast_defs;
use pos::Positioned;
use pos::TypeName;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::ty::TypedefTypeAssignment;
use ty::reason::Reason as _;

use crate::ctx::R;
use crate::decl_entry;
use crate::folded_class as cls;
use crate::typing_defs_core::DeclTy;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env::ClassOrTypedefResult;
use crate::typing_env_types::Env;

/// `MakeType.nonnull r`, on a decl type
fn make_type_nonnull(r: R) -> DeclTy {
    Ty::new(r, Ty_::Tnonnull)
}

/// `MakeType.mixed r` (`mk (r, Toption (nonnull r))`), on a decl type
fn make_type_mixed(r: R) -> DeclTy {
    let nonnull = make_type_nonnull(r.clone());
    Ty::new(r, Ty_::Toption(nonnull))
}

/// `MakeType.nullable r ty`, on a decl type
fn make_type_nullable(r: R, ty: DeclTy) -> DeclTy {
    // Cheap avoidance of double nullable
    match ty.node_ref() {
        Ty_::Toption(_) => Ty::new(r, ty.node_ref().clone()),
        Ty_::Tunion(tyl) if tyl.is_empty() => Ty::new(r, Ty_::Tprim(Tprim::Tnull)),
        _ => Ty::new(r, Ty_::Toption(ty)),
    }
}

/// `MakeType.intersection r tyl`, on decl types
fn make_type_intersection(r: R, mut tyl: Vec<DeclTy>) -> DeclTy {
    match tyl.len() {
        0 => make_type_mixed(r),
        1 => tyl.pop().unwrap(),
        _ => Ty::new(r, Ty_::Tintersection(tyl.into_boxed_slice())),
    }
}

/// For a decl type ty, return the type ety that the runtime will enforce.
/// It's possible that ty </: ety because the runtime breaks through abstraction
/// boundaries. For example, for enum E : int as arraykey
/// we have get_enforced_type(E) = int, but E </: int.
///
/// If ty=ety then we say that the type is "fully enforced"
/// Resolve type parameters wrt to class_def_opt, if present
pub fn get_enforced_type(env: &Env, class_def_opt: Option<&cls::T>, ty: &DeclTy) -> DeclTy {
    let default = || make_type_mixed(R::none());
    match ty.node_ref() {
        // An enum type is enforced at its underlying type
        Ty_::Tapply(id_and_args) if env::is_enum(env, id_and_args.0.id_ref().as_str()) => {
            let name = id_and_args.0.id_ref().as_str();
            match env::get_class(env, name) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => default(),
                decl_entry::T::Found(tc) => match cls::enum_type(&tc) {
                    None => default(),
                    Some(e) => get_enforced_type(env, None, &e.base),
                },
            }
        }
        Ty_::Tapply(id_and_args) => {
            let (pos_id, tyargs) = &**id_and_args;
            match env::get_class_or_typedef(env, pos_id.id_ref().as_str()) {
                decl_entry::T::Found(ClassOrTypedefResult::ClassResult(_class_info)) => {
                    // Non-generic types are fully enforced
                    if tyargs.is_empty() {
                        ty.clone()
                    }
                    // Generic types are not enforced at their type arguments
                    else {
                        default()
                    }
                }
                decl_entry::T::Found(ClassOrTypedefResult::TypedefResult(typedef_info)) => {
                    // Enforcement "sees through" type aliases and newtype, but does not instantiate generic arguments
                    // The same is true of newtypes
                    match &typedef_info.type_assignment {
                        TypedefTypeAssignment::SimpleTypeDef(_, td_type) => {
                            get_enforced_type(env, None, td_type)
                        }
                        TypedefTypeAssignment::CaseType(variant, variants)
                            if variants.is_empty() =>
                        {
                            get_enforced_type(env, None, &variant.hint)
                        }
                        TypedefTypeAssignment::CaseType(..) => default(),
                    }
                }
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => default(),
            }
        }
        Ty_::Tgeneric(name) => {
            match class_def_opt {
                None => default(),
                Some(cd) => {
                    let tparams = cls::tparams(cd);
                    match tparams
                        .iter()
                        .find(|tp| tp.name.id_ref().as_str() == name.as_str())
                    {
                        None => default(),
                        Some(tp) => {
                            let bounds: Vec<DeclTy> = tp
                                .constraints
                                .iter()
                                .filter_map(|(cstr, ty)| match cstr {
                                    ast_defs::ConstraintKind::ConstraintAs
                                    | ast_defs::ConstraintKind::ConstraintEq => {
                                        // Do not follow bounds that are themselves generic parameters
                                        // as HHVM doesn't enforce these
                                        match ty.node_ref() {
                                            Ty_::Tgeneric(_) => None,
                                            _ => Some(get_enforced_type(env, class_def_opt, ty)),
                                        }
                                    }
                                    ast_defs::ConstraintKind::ConstraintSuper => None,
                                })
                                .collect();
                            match bounds.len() {
                                0 => default(),
                                1 => bounds.into_iter().next().unwrap(),
                                _ => make_type_intersection(R::none(), bounds),
                            }
                        }
                    }
                }
            }
            // This is enforced but only at its class, which we can't express
            // in Hack types. So we use the enclosing class as an approximation.
        }
        Ty_::Tthis => match class_def_opt {
            None => default(),
            Some(cd) => {
                // OCaml evaluates the arguments of the constructor from right
                // to left.
                let tyargs: Vec<DeclTy> = cls::tparams(cd)
                    .iter()
                    .map(|_| {
                        // TODO akenn
                        Ty::new(R::none(), Ty_::Tunion(Box::new([])))
                    })
                    .collect();
                let name = cls::name(cd);
                let pos = cls::pos(cd);
                Ty::new(
                    R::none(),
                    Ty_::Tapply(Box::new((
                        Positioned::new(pos::BPos::from(pos), TypeName::new(name)),
                        tyargs.into_boxed_slice(),
                    ))),
                )
            }
        },
        Ty_::Toption(t) => {
            let ety = get_enforced_type(env, class_def_opt, t);
            make_type_nullable(R::none(), ety)
        }
        Ty_::Tlike(t) => get_enforced_type(env, class_def_opt, t),
        // Special case for intersections, as these are used to describe partial enforcement
        Ty_::Tintersection(tys) => {
            let tys: Vec<DeclTy> = tys
                .iter()
                .map(|t| get_enforced_type(env, class_def_opt, t))
                .collect();
            make_type_intersection(ty.reason().clone(), tys)
        }
        Ty_::Tshape(_) | Ty_::Ttuple(_) => make_type_nonnull(R::none()),
        Ty_::Tprim(_) | Ty_::Tnonnull => ty.clone(),
        Ty_::Trefinement(_)
        | Ty_::Tmixed
        | Ty_::Twildcard
        | Ty_::Tany
        | Ty_::Tdynamic
        | Ty_::Tfun(_)
        | Ty_::Tunion(_)
        | Ty_::TvecOrDict(_)
        | Ty_::Taccess(_)
        | Ty_::TclassPtr(_) => default(),
    }
}
