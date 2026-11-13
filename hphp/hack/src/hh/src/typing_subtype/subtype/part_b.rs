// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 2523-4772): module `Subtype` from `simplify_funs` up to and including `simplify`.
//! See `hh/PORTING.md`.
//!
//! Function subtyping (`simplify_funs`), class and newtype subtyping
//! (variance), shape subtyping (simple shapes, and shape splats through the
//! rows of `Typing_shape_normalize` and the corners procedure of
//! `Typing_corners`), and the entry point `simplify`.
//!
//! # Signatures
//!
//! As in `part_a.rs`: `~subtype_env` is `&subtype_env::T`, `~this_ty` is
//! `Option<&Ty>`, `~fail` is `Option<typing_error::T>` by value, and the
//! environment is where the OCaml has it (last, or in the place of `~env`
//! among the labelled arguments). Tuples stay tuples.
//!
//! - The functions that the other parts call (`simplify`, `simplify_funs`,
//!   `simplify_subtype_classes`, `simplify_subtype_variance_for_non_injective`,
//!   `simplify_subtype_shape_splat`, `simplify_subtype_shape`) take the
//!   reasons and types they store by value, the type arguments as slices and
//!   the field maps of shapes by reference. The helpers that only this part
//!   calls take reasons (`~r`) and rows by reference.
//! - `simplify_funs` takes its two `Reason.t * locl_fun_type` pairs by value,
//!   as `toplevel.rs` (`subtype_funs`) calls it.
//! - `simplify_subtype_variance_for_injective` is applied partially in OCaml
//!   (it returns `simplify_subtype_variance_for_injective_loop` waiting for
//!   the variances, the type arguments and the environment): here it takes
//!   all of them.
//! - `simplify_subtype_shape_type` returns a partial application of
//!   `simplify` (`env -> env * TL.subtype_prop`): here a closure
//!   `FnOnce(&mut Env) -> SubtypeProp` that does not borrow the environment
//!   (its `subtype_env` is borrowed, or owned when it is a changed copy).
//!   `simplify_subtype_shape_projection` and
//!   `shape_project_and_simplify_subtype` return such a closure in their
//!   `Ok`, boxed ([`PropK`]), since the two `Ok` cases build different
//!   closures.
//! - The polymorphic variant `` `Required ty | `Optional ty | `Absent `` is
//!   [`ShapeProjection`].
//! - `Typing_corners.Cache.t`, a record of `ref`s that all its copies share,
//!   is passed as `&mut typing_corners::cache::T`.
//! - A label (`TShapeField.t option`) is `Option<&TShapeField>`, the key type
//!   of the shape maps and of `TShapeSet`.
//! - `subrow_infer_same_var` returns `(env * TL.subtype_prop) option`: it
//!   returns `Option<SubtypeProp>`, and on `None` its caller goes on with the
//!   environment it had before the call, which `subrow_infer_couple`
//!   restores.
//!
//! # Calls into `Typing_shape_normalize.Row` and `Typing_corners`
//!
//! `Row.t` is `row::T`, `Row.normalized` is `row::Normalized`,
//! `Splat_elem.Set` is `typing_corners::splat_elem::set`, `Assignment.t` is
//! `typing_corners::assignment::T`. As those modules take them: rows by
//! reference, normalized rows by value (`as_row`, `normalized_to_ty`,
//! `fold_normalized`; a normalized row that the OCaml goes on using after
//! `as_row` is cloned), shape types and simple shapes by value, every
//! `Reason.t` by value, field records by reference to the predicates of
//! `Field` and by value to `merge`, `meet` and `join`; the results are owned.
//!
//! # Physical equality on shapes
//!
//! As in `typing_union.rs` (`union_shapes`): `phys_equal fdm_sub fdm_super`
//! on two field maps is `std::ptr::eq` (true when the two shapes share their
//! node; it only skips work, see `simplify_subtype_shape`), and `phys_equal
//! f1 f2` on two field records is "same optionality and physically equal
//! types" ([`phys_equal_shape_field_type`]). `TShapeMap.merge` keeps, where
//! both maps have a key, the key of the first map: the OCaml keeps the key of
//! whichever of the two trees is the higher at that node, which `BTreeMap`s
//! cannot reproduce. (The position of that key is the `decl_pos` of
//! `Missing_field`.)


use naming_special_names_rust as sn;
use oxidized::ast_defs::ReifyKind;
use oxidized::ast_defs::Variance;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

#[allow(unused_imports)]
use super::*;
use crate::ast_defs;
use crate::decl_entry;
use crate::diagnostics_state;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::markdown_lite;
use crate::pos_or_decl;
use crate::quickfix;
use crate::tvid;
use crate::typing_corners;
use crate::typing_defs;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Exact;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_field;
use crate::typing_defs_core::t_shape_map::TShapeField;
use crate::typing_defs_core::t_shape_map::TShapeMap;
use crate::typing_dynamic_utils;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::or;
use crate::typing_logic_helpers::valid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_phase;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::FieldKind;
use crate::typing_reason::T as Reason;
use crate::typing_shape_normalize::row;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype_ask;
use crate::typing_union;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// The projection of a shape on a field (`s |_ f`, see `shape_projection`):
/// `` `Required ty ``, `` `Optional ty `` or `` `Absent `` (a polymorphic
/// variant in OCaml).
#[derive(Clone, Debug)]
pub(crate) enum ShapeProjection {
    Required(Ty),
    Optional(Ty),
    Absent,
}

/// A proposition waiting for its environment: what OCaml has as a partial
/// application `env -> env * TL.subtype_prop` (see the module
/// documentation).
pub(crate) type PropK<'a> = Box<dyn FnOnce(&mut Env) -> tl::SubtypeProp + 'a>;

/// `phys_equal` on two field records: the same optionality and physically
/// equal types (see the module documentation).
fn phys_equal_shape_field_type(f1: &ShapeFieldType, f2: &ShapeFieldType) -> bool {
    f1.optional == f2.optional && typing_defs_core::phys_equal(&f1.ty, &f2.ty)
}

pub fn simplify_funs(
    subtype_env: &subtype_env::T,
    check_return: bool,
    for_override: bool,
    super_like: bool,
    (r_sub, ft_sub): (Reason, &FunType),
    (r_super, ft_super): (Reason, &FunType),
    env: &mut Env,
) -> tl::SubtypeProp {
    // We should always have instantiated polymorphic function types by this point
    if !ft_sub.instantiated {
        diagnostics_state::internal_error(
            pos_or_decl::unsafe_to_raw_pos(reason::to_pos(&r_sub)),
            "Unexpected polymorphic function type",
        )
    }
    if !ft_super.instantiated {
        diagnostics_state::internal_error(
            pos_or_decl::unsafe_to_raw_pos(reason::to_pos(&r_super)),
            "Unexpected polymorphic function type",
        )
    }
    let arg_posl = subtype_env.has_member_arg_posl.clone();
    let subtype_env = &subtype_env::T {
        has_member_arg_posl: None,
        ..subtype_env.clone()
    };
    // OCaml evaluates the two operands of `&&&` right to left, so the last
    // operand of the chain below is evaluated first, before any conjunct: the
    // return type is likened and, for overrides, stripped of dynamic (which
    // can allocate a fresh type variable) in the environment this function is
    // given. The other operands are partial applications, which do nothing
    // until they are applied.
    let return_check = if check_return {
        // Finally do covariant subtyping on return type
        let ty_super = sd::liken(super_like, env, ft_super.ret.clone());
        let subtype_env = if for_override {
            // When overriding in Sound Dynamic, we allow t to override dynamic if
            // t is a dynamic-aware subtype of dynamic. We also allow Awaitable<t>
            // to override Awaitable<dynamic> and and Awaitable<t> to
            // override ~Awaitable<dynamic>.
            let ty_super = typing_dynamic_utils::strip_dynamic(&mut env.clone(), ty_super.clone());
            match get_node(&ty_super) {
                Ty_::Tdynamic(_) => subtype_env::set_is_dynamic_aware(subtype_env.clone(), true),
                Ty_::Tclass((_, class_name), _, tyl)
                    if matches!(tyl.as_slice(), [ty]
                        if class_name == sn::classes::AWAITABLE && typing_defs::is_dynamic(ty)) =>
                {
                    subtype_env::set_is_dynamic_aware(subtype_env.clone(), true)
                }
                _ => subtype_env.clone(),
            }
        } else {
            subtype_env.clone()
        };
        // Update the provenance for the subtype:
        //  i) Record the flow from the parent function types
        //  ii) Record the projection on the return type of that function
        //  iii) Record the flow from the subtype into that return type
        let ty_sub = env::update_reason(env, ft_sub.ret.clone(), |r_sub_prj| {
            reason::prj_fn_ret(r_sub.clone(), r_sub_prj, r_super.clone())
        });
        Some((subtype_env, ty_sub, ty_super))
    } else {
        None
    };
    // First apply checks on attributes and variadic arity
    let p = simplify_subtype_funs_attributes(subtype_env, (&r_sub, &ft_sub), (&r_super, &ft_super));
    // Now do contravariant subtyping on parameters. The named-variadic
    // entry (if present) is stripped here and handled separately below —
    // it is not a required parameter and must not participate in either
    // positional matching or name-by-name matching.
    let p = and(env, p, |env| {
        simplify_subtype_params(
            subtype_env,
            arg_posl,
            for_override,
            (
                r_sub.clone(),
                0,
                typing_defs::ft_params_without_named_variadic(&ft_sub),
                typing_defs::ft_has_positional_variadic(&ft_sub),
            ),
            (
                r_super.clone(),
                0,
                typing_defs::ft_params_without_named_variadic(&ft_super),
                typing_defs::ft_has_positional_variadic(&ft_super),
            ),
            env,
        )
    });
    let p = and(env, p, |env| {
        simplify_subtype_named_variadic(
            subtype_env,
            (r_sub.clone(), &ft_sub),
            (r_super.clone(), &ft_super),
            env,
        )
    });
    // `simplify_subtype_implicit_params_help ft_super.ft_implicit_params ft_sub.ft_implicit_params`
    let p = and(env, p, |env| {
        simplify_subtype_implicit_params(
            subtype_env,
            &ft_super.implicit_params,
            &ft_sub.implicit_params,
            env,
        )
    });
    and(env, p, |env| match return_check {
        Some((subtype_env, ty_sub, ty_super)) => simplify(
            &subtype_env,
            None,
            Lhs {
                sub_supportdyn: None,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            env,
        ),
        None => valid(env),
    })
}

// == Class / newtype subtyping ===========================================

#[allow(clippy::too_many_arguments)]
pub(crate) fn simplify_subtype_variance_for_injective_loop(
    subtype_env: &subtype_env::T,
    sub_supportdyn: Option<&Reason>,
    super_like: bool,
    nm: &str,
    ctor_kind: reason::CtorKind,
    idx: isize,
    variance_reifiedl: &[(Variance, ReifyKind)],
    (r_sub, children_tyl): (Reason, &[Ty]),
    (r_super, super_tyl): (Reason, &[Ty]),
    env: &mut Env,
) -> tl::SubtypeProp {
    let simplify_subtype_help =
        |sub_supportdyn: Option<&Reason>, ty_sub: &Ty, ty_super: &Ty, env: &mut Env| {
            simplify(
                subtype_env,
                None,
                Lhs {
                    sub_supportdyn,
                    ty_sub,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super,
                },
                env,
            )
        };

    match (variance_reifiedl, children_tyl, super_tyl) {
        ([], _, _) | (_, [], _) | (_, _, []) => valid(env),
        (
            [(variance, _reify_kind), variance_reifiedl @ ..],
            [child, childrenl @ ..],
            [super_, superl @ ..],
        ) => {
            let prop = |env: &mut Env| match variance {
                Variance::Covariant => {
                    let ty_sub = env::update_reason(env, child.clone(), |r_sub_prj| {
                        reason::prj_ctor_co(
                            r_sub.clone(),
                            r_sub_prj,
                            r_super.clone(),
                            ctor_kind,
                            nm.to_string(),
                            idx,
                            false,
                        )
                    });
                    let ty_super = sd::liken(super_like, env, super_.clone());
                    simplify_subtype_help(sub_supportdyn, &ty_sub, &ty_super, env)
                }
                Variance::Contravariant => {
                    let ty_super = typing_defs_core::map_reason(super_.clone(), |r_super_prj| {
                        reason::prj_ctor_contra(
                            r_sub.clone(),
                            r_super.clone(),
                            r_super_prj,
                            ctor_kind,
                            nm.to_string(),
                            idx,
                            false,
                        )
                    });
                    let ty_sub = child;
                    simplify_subtype_help(sub_supportdyn, &ty_super, ty_sub, env)
                }
                Variance::Invariant => {
                    let covariant_prop = |env: &mut Env| {
                        let ty_sub = env::update_reason(env, child.clone(), |r_sub_prj| {
                            reason::prj_ctor_co(
                                r_sub.clone(),
                                r_sub_prj,
                                r_super.clone(),
                                ctor_kind,
                                nm.to_string(),
                                idx,
                                true,
                            )
                        });
                        let ty_super = sd::liken(super_like, env, super_.clone());
                        simplify_subtype_help(sub_supportdyn, &ty_sub, &ty_super, env)
                    };
                    let contravariant_prop = |env: &mut Env| {
                        let f = |r_super_prj| {
                            reason::prj_ctor_contra(
                                r_sub.clone(),
                                r_super.clone(),
                                r_super_prj,
                                ctor_kind,
                                nm.to_string(),
                                idx,
                                true,
                            )
                        };
                        let ty_sub = sd::liken(super_like, env, child.clone());
                        let ty_super = typing_defs_core::map_reason(super_.clone(), f);
                        simplify_subtype_help(sub_supportdyn, &ty_super, &ty_sub, env)
                    };
                    let p = covariant_prop(env);
                    and(env, p, contravariant_prop)
                }
            };
            let p = prop(env);
            and(env, p, |env| {
                simplify_subtype_variance_for_injective_loop(
                    subtype_env,
                    sub_supportdyn,
                    super_like,
                    nm,
                    ctor_kind,
                    idx + 1,
                    variance_reifiedl,
                    (r_sub.clone(), childrenl),
                    (r_super.clone(), superl),
                    env,
                )
            })
        }
    }
}

/// The OCaml applies this function to its first six arguments and returns
/// `simplify_subtype_variance_for_injective_loop` waiting for the others:
/// here it takes them all.
#[allow(clippy::too_many_arguments)]
pub(crate) fn simplify_subtype_variance_for_injective(
    subtype_env: &subtype_env::T,
    sub_supportdyn: Option<&Reason>,
    super_like: bool,
    cid: &str,
    ctor_kind: reason::CtorKind,
    class_sub: Option<&cls::T>,
    variance_reifiedl: &[(Variance, ReifyKind)],
    (r_sub, children_tyl): (Reason, &[Ty]),
    (r_super, super_tyl): (Reason, &[Ty]),
    env: &mut Env,
) -> tl::SubtypeProp {
    // Before looping through the generic arguments, check to see if we should push
    // supportdyn onto them. This depends on the generic class itself.
    let sub_supportdyn = match (sub_supportdyn, class_sub) {
        (None, _) | (_, None) => None,
        (Some(_), Some(class_sub)) => {
            if cid == sn::collections::TRAVERSABLE
                || cid == sn::collections::KEYED_TRAVERSABLE
                || cid == sn::collections::CONTAINER
                || cls::has_ancestor(class_sub, sn::collections::CONTAINER)
            {
                sub_supportdyn
            } else {
                None
            }
        }
    };
    simplify_subtype_variance_for_injective_loop(
        subtype_env,
        sub_supportdyn,
        super_like,
        cid,
        ctor_kind,
        0,
        variance_reifiedl,
        (r_sub, children_tyl),
        (r_super, super_tyl),
        env,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn simplify_subtype_classes(
    fail: subtype_env::Fail,
    subtype_env: &subtype_env::T,
    sub_supportdyn: Option<&Reason>,
    this_ty: Option<&Ty>,
    super_like: bool,
    // The class types are borrowed (OCaml passes pointers to them): they are
    // copied only where a new type is built from them.
    (r_sub, (class_id_sub, exact_sub, tyl_sub)): (Reason, (&PosId, &Exact, &[Ty])),
    (r_super, (class_id_super, exact_super, tyl_super)): (Reason, (&PosId, &Exact, &[Ty])),
    env: &mut Env,
) -> tl::SubtypeProp {
    // `invalid_env` is `invalid ~fail`.
    let (cid_super, cid_sub) = (&class_id_super.1, &class_id_sub.1);
    let (exact_match, both_exact) = match (exact_sub, exact_super) {
        (Exact::Nonexact(_), Exact::Exact) => (false, false),
        (Exact::Exact, Exact::Exact) => (true, true),
        (_, _) => (true, false),
    };
    if cid_super == cid_sub {
        if tyl_sub.is_empty() && tyl_super.is_empty() && exact_match {
            valid(env)
        } else {
            // This is side-effecting as it registers a dependency
            let class_def_sub = env::get_class(env, cid_sub);
            // `Cls.tparams tc`, used twice below (borrowed).
            let tparams_sub = match &class_def_sub {
                decl_entry::T::Found(tc) => Some(cls::tparams_ref(tc)),
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
            };
            // If class is final then exactness is superfluous
            let (has_generics, is_final) = match (&class_def_sub, &tparams_sub) {
                (decl_entry::T::Found(tc), Some(tparams)) => {
                    // The components of the tuple are evaluated right to left.
                    let is_final = cls::final_(tc);
                    let has_generics = !tparams.is_empty();
                    (has_generics, is_final)
                }
                _ => (false, false),
            };
            if !(exact_match || is_final) {
                invalid(fail, env)
            } else if has_generics && tyl_super.is_empty() {
                // C<t> <: C where C represents all possible instantiations of C's generics
                valid(env)
            } else if has_generics && tyl_sub.is_empty() {
                // C </: C<t>, since C's generic can be instantiated to other things than t
                invalid(fail, env)
            } else {
                let variance_reifiedl: Vec<(Variance, ReifyKind)> = if tyl_sub.is_empty() {
                    vec![]
                } else if both_exact {
                    // Subtyping exact class types following variance
                    // annotations is unsound in general (see T142810099).
                    // When the class is exact, we must treat all generic
                    // parameters as invariant.
                    tyl_sub
                        .iter()
                        .map(|_| (Variance::Invariant, ReifyKind::Erased))
                        .collect()
                } else {
                    match &tparams_sub {
                        None => tyl_sub
                            .iter()
                            .map(|_| (Variance::Invariant, ReifyKind::Erased))
                            .collect(),
                        Some(tparams) => tparams.iter().map(|t| (t.variance, t.reified)).collect(),
                    }
                };
                let class_sub = decl_entry::to_option(class_def_sub);
                simplify_subtype_variance_for_injective(
                    subtype_env,
                    sub_supportdyn,
                    super_like,
                    cid_sub,
                    reason::CtorKind::CtorClass,
                    class_sub.as_ref(),
                    &variance_reifiedl,
                    (r_sub, tyl_sub),
                    (r_super, tyl_super),
                    env,
                )
            }
        }
    } else if !exact_match {
        invalid(fail, env)
    } else {
        let class_def_sub = env::get_class(env, cid_sub);
        match class_def_sub {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                // This should have been caught already in the naming phase
                valid(env)
            }
            decl_entry::T::Found(class_sub) => {
                // We handle the case where a generic A<T> is used as A for the sub-class.
                // This works because there will be no locls to substitute for type parameters
                // T in the type build by get_ancestor. If T does show up in that type, then
                // the call to simplify subtype will fail. This is what we expect since we
                // would need it to be a sub-type of the super-type for all T. If T is not there,
                // then simplify_subtype should succeed.
                //
                // (The fields of the record are evaluated right to left.)
                //
                // Not in the OCaml: it is built only where it is used (it has
                // no effect), not when the class is a trait or an interface
                // without upper bounds on `this` (the usual case: 2.6 million
                // of the 2.7 million comparisons of different classes on the
                // benchmark sample).
                let make_ety_env = || {
                    let ety_this_ty = match this_ty {
                        // FIXME(T59448452): Unsound in general
                        Some(this_ty) => this_ty.clone(),
                        None => mk((
                            r_sub.clone(),
                            Ty_::Tclass(class_id_sub.clone(), exact_sub.clone(), tyl_sub.to_vec()),
                        )),
                    };
                    ExpandEnv {
                        this_ty: ety_this_ty,
                        substs: t_utils::make_locl_subst_for_class_tparams(&class_sub, tyl_sub),
                        ..typing_defs::empty_expand_env()
                    }
                };
                let up_obj = cls::get_ancestor(&class_sub, cid_super);
                match up_obj {
                    Some(up_obj) => {
                        // Since we have provided no `Typing_error.Reasons_callback.t`
                        // in the `expand_env`, this will not generate any errors
                        let ety_env = make_ety_env();
                        let (_ty_err_opt, up_obj) = typing_phase::localize(&ety_env, env, &up_obj);
                        let up_obj = env::update_reason(env, up_obj, |ancestor| {
                            reason::axiom_extends(r_sub.clone(), ancestor)
                        });

                        match get_node(&up_obj) {
                            Ty_::Tclass(class_id_sub, exact_sub, tyl_sub) => {
                                let r_sub = get_reason(&up_obj).clone();
                                let subtype_env = subtype_env::possibly_add_violated_constraint(
                                    subtype_env.clone(),
                                    r_sub.clone(),
                                    r_super.clone(),
                                );
                                let ity_super = InternalType::LoclType(mk((
                                    r_super.clone(),
                                    Ty_::Tclass(
                                        class_id_super.clone(),
                                        exact_super.clone(),
                                        tyl_super.to_vec(),
                                    ),
                                )));
                                let ity_sub = InternalType::LoclType(up_obj.clone());
                                let fail = subtype_env::fail(&subtype_env, ity_sub, ity_super);
                                simplify_subtype_classes(
                                    fail.into(),
                                    &subtype_env,
                                    sub_supportdyn,
                                    this_ty,
                                    super_like,
                                    (r_sub, (class_id_sub, exact_sub, tyl_sub)),
                                    (r_super, (class_id_super, exact_super, tyl_super)),
                                    env,
                                )
                            }
                            _ => {
                                // The superclass must be classish
                                invalid(fail, env)
                            }
                        }
                    }
                    None => {
                        if (ast_defs::is_c_trait(cls::kind(&class_sub))
                            || ast_defs::is_c_interface(cls::kind(&class_sub)))
                            && cls::upper_bounds_on_this_iter(&class_sub).next().is_none()
                        {
                            // `try_upper_bounds_on_this [] env`
                            invalid(fail, env)
                        } else if ast_defs::is_c_trait(cls::kind(&class_sub))
                            || ast_defs::is_c_interface(cls::kind(&class_sub))
                        {
                            let ety_env = make_ety_env();
                            let reqs_non_strict: Vec<DeclTy> =
                                cls::all_ancestor_req_constraints_requirements(&class_sub)
                                    .into_iter()
                                    .map(|cr| typing_defs::to_requirement(cr).ty)
                                    .collect();
                            let ctx = UpperBoundsOnThis {
                                reqs_non_strict: &reqs_non_strict,
                                ety_env: &ety_env,
                                fail: &fail,
                                subtype_env,
                                sub_supportdyn,
                                this_ty,
                                super_like,
                                r_sub: &r_sub,
                                r_super: &r_super,
                                class_id_super,
                                exact_super,
                                tyl_super,
                            };
                            try_upper_bounds_on_this(
                                &ctx,
                                &cls::upper_bounds_on_this(&class_sub),
                                env,
                            )
                        } else {
                            invalid(fail, env)
                        }
                    }
                }
            }
        }
    }
}

/// What the local `try_upper_bounds_on_this` of `simplify_subtype_classes`
/// uses of the enclosing function.
struct UpperBoundsOnThis<'a> {
    reqs_non_strict: &'a [DeclTy],
    ety_env: &'a ExpandEnv,
    fail: &'a subtype_env::Fail<'a>,
    subtype_env: &'a subtype_env::T,
    sub_supportdyn: Option<&'a Reason>,
    this_ty: Option<&'a Ty>,
    super_like: bool,
    r_sub: &'a Reason,
    r_super: &'a Reason,
    class_id_super: &'a PosId,
    exact_super: &'a Exact,
    tyl_super: &'a [Ty],
}

/// The local `let rec try_upper_bounds_on_this up_objs env` of
/// `simplify_subtype_classes`.
fn try_upper_bounds_on_this(
    ctx: &UpperBoundsOnThis<'_>,
    up_objs: &[DeclTy],
    env: &mut Env,
) -> tl::SubtypeProp {
    match up_objs {
        [] => {
            // It's crucial that we don't lose updates to tpenv in
            // env that were introduced by Phase.localize.
            // TODO: avoid this requirement
            invalid(ctx.fail.clone(), env)
        }
        [ub_obj_typ, up_objs @ ..]
            if ctx
                .reqs_non_strict
                .iter()
                .any(|req| typing_defs_core::equal_decl_ty(ub_obj_typ, req)) =>
        {
            // `require class` constraints do not induce subtyping,
            // so skipping them
            try_upper_bounds_on_this(ctx, up_objs, env)
        }
        [ub_obj_typ, up_objs @ ..] => {
            // A trait is never the runtime type, but it can be used
            // as a constraint if it has requirements for its using classes
            // Since we have provided no `Typing_error.Reasons_callback.t`
            // in the `expand_env`, this will not generate any errors
            let (_ty_err_opt, ub_obj_typ) = typing_phase::localize(ctx.ety_env, env, ub_obj_typ);
            let prop = |env: &mut Env| match get_node(&ub_obj_typ) {
                cls_sub @ Ty_::Tclass(class_id_sub, exact_sub, tyl_sub) => {
                    let ity_super = InternalType::LoclType(mk((
                        ctx.r_super.clone(),
                        Ty_::Tclass(
                            ctx.class_id_super.clone(),
                            ctx.exact_super.clone(),
                            ctx.tyl_super.to_vec(),
                        ),
                    )));
                    // Retain reason / position for original subclass, not the upper bound
                    let ity_sub = InternalType::LoclType(mk((ctx.r_sub.clone(), cls_sub.clone())));
                    let fail = subtype_env::fail(ctx.subtype_env, ity_sub, ity_super);
                    simplify_subtype_classes(
                        fail.into(),
                        ctx.subtype_env,
                        ctx.sub_supportdyn,
                        ctx.this_ty,
                        ctx.super_like,
                        (ctx.r_sub.clone(), (class_id_sub, exact_sub, tyl_sub)),
                        (
                            ctx.r_super.clone(),
                            (ctx.class_id_super, ctx.exact_super, ctx.tyl_super),
                        ),
                        env,
                    )
                }
                _ => invalid(ctx.fail.clone(), env),
            };
            // `let ( ||| ) = ( ||| ) ~fail in env |> prop ||| try_upper_bounds_on_this up_objs`
            let p1 = prop(env);
            or(ctx.fail.clone(), env, p1, |env| {
                try_upper_bounds_on_this(ctx, up_objs, env)
            })
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn simplify_subtype_variance_for_non_injective(
    subtype_env: &subtype_env::T,
    sub_supportdyn: Option<&Reason>,
    super_like: bool,
    cid: &str,
    class_sub: Option<&cls::T>,
    variance_reifiedl: &[(Variance, ReifyKind)],
    (r_sub, children_tyl): (Reason, &[Ty]),
    (r_super, super_tyl): (Reason, &[Ty]),
    lty_sub: Ty,
    lty_super: Ty,
    env: &mut Env,
) -> tl::SubtypeProp {
    let p = simplify_subtype_variance_for_injective(
        subtype_env,
        sub_supportdyn,
        super_like,
        cid,
        reason::CtorKind::CtorNewtype,
        class_sub,
        variance_reifiedl,
        (r_sub, children_tyl),
        (r_super, super_tyl),
        env,
    );

    if subtype_env.require_completeness && !tl::is_valid(&p) {
        // If we require completeness, then we can still use the incomplete
        // N<t1, .., tn> <: N<u1, .., un> to t1 <:v1> u1 /\ ... /\ tn <:vn> un
        // simplification if all of the latter constraints already hold.
        // If they don't already hold, there is nothing we can (soundly) simplify.
        if subtype_env.require_soundness {
            mk_issubtype_prop(
                sub_supportdyn,
                subtype_env.is_dynamic_aware,
                env,
                InternalType::LoclType(lty_sub),
                InternalType::LoclType(lty_super),
            )
        } else {
            tl::valid()
        }
    } else {
        p
    }
}

// == Shape splat subtyping ===============================================

/// Entry point for shape-splat subtyping  Normalize both shapes then dispatch
/// on presence of type variables:
/// - no tyvar: ground corner procedure;
/// - sub/super only: single-side inference;
/// - one-each: couple via a fresh mid row;
/// - multiple on both sides: the decoupled fallback.
pub(crate) fn simplify_subtype_shape_splat(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    this_ty: Option<&Ty>,
    super_like: bool,
    (supportdyn_sub, r_sub, shape_type_sub): (bool, Reason, ShapeType),
    (supportdyn_super, r_super, shape_type_super): (bool, Reason, ShapeType),
) -> tl::SubtypeProp {
    let (err_opt, norm_sub, norm_super) = {
        let on_error = &subtype_env.on_error;
        let (err_sub, norm_sub) =
            row::normalize(on_error.clone(), r_sub.clone(), shape_type_sub, env);
        let (err_super, norm_super) =
            row::normalize(on_error.clone(), r_super.clone(), shape_type_super, env);
        // `Option.merge err_sub err_super ~f:Typing_error.both`
        let err_opt = match (err_sub, err_super) {
            (Some(err_sub), Some(err_super)) => Some(typing_error::both(err_sub, err_super)),
            (Some(err), None) | (None, Some(err)) => Some(err),
            (None, None) => None,
        };
        (err_opt, norm_sub, norm_super)
    };
    // Create an empty cache for the corners procedure
    let mut cache = typing_corners::cache::create();
    let cache = &mut cache;
    match err_opt {
        fail @ Some(_) => invalid(fail, env),
        None => {
            let sub_supportdyn_reason = if supportdyn_sub {
                Some(r_sub.clone())
            } else {
                None
            };
            let simplify_normalized =
                |env: &mut Env, norm_sub: row::Normalized, norm_super: row::Normalized| {
                    let ty_sub = row::normalized_to_ty(env, r_sub.clone(), norm_sub);
                    let ty_super = row::normalized_to_ty(env, r_super.clone(), norm_super);
                    simplify_(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn: sub_supportdyn_reason.as_ref(),
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_supportdyn: supportdyn_super,
                            super_like,
                            ty_super: &ty_super,
                        },
                        env,
                    )
                };
            match (
                row::as_row(norm_sub.clone()),
                row::as_row(norm_super.clone()),
            ) {
                (None, _) | (_, None) => simplify_normalized(env, norm_sub, norm_super),
                (Some(norm_sub), Some(norm_super)) => {
                    let simple_sub = row::as_simple(&norm_sub);
                    let simple_super = row::as_simple(&norm_super);
                    let super_is_top_shape = match &simple_super {
                        Some(ShapeTypeSimple {
                            fields: s_fields,
                            unknown_value: s_unknown_value,
                            origin: _,
                        }) => s_fields.is_empty() && t_utils::is_mixed(env, s_unknown_value),
                        None => false,
                    };
                    if !supportdyn_super && super_is_top_shape {
                        // [shape(...)] is the top row. Its [supportdyn] counterpart still
                        // imposes dynamic-support obligations on every field.
                        valid(env)
                    } else if row::is_bottom(&norm_sub) {
                        valid(env)
                    } else if row::is_bottom(&norm_super) {
                        // A non-bottom subrow may still be opaque and constrained to [nothing].
                        let ty_sub = row::to_ty(r_sub.clone(), &norm_sub);
                        let ty_super = row::to_ty(r_super.clone(), &norm_super);
                        simplify_(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn: None,
                                ty_sub: &ty_sub,
                            },
                            Rhs {
                                super_supportdyn: false,
                                super_like,
                                ty_super: &ty_super,
                            },
                            env,
                        )
                    } else {
                        let sv_sub = typing_corners::spread_tyvar_ids(&norm_sub);
                        let sv_super = typing_corners::spread_tyvar_ids(&norm_super);
                        match (sv_sub.as_slice(), sv_super.as_slice()) {
                            ([_, _, ..], _) if subtype_env.report_ambiguous_shape_splat => {
                                tl::SubtypeProp::AmbiguousShapeSplat(sv_sub.clone())
                            }
                            ([], []) => match (simple_sub, simple_super) {
                                (
                                    Some(ShapeTypeSimple {
                                        origin: origin_sub,
                                        unknown_value: kind_sub,
                                        fields: fdm_sub,
                                    }),
                                    Some(ShapeTypeSimple {
                                        origin: origin_super,
                                        unknown_value: kind_super,
                                        fields: fdm_super,
                                    }),
                                ) => {
                                    if typing_defs_core::same_type_origin(
                                        &origin_super,
                                        &origin_sub,
                                    ) {
                                        // Same origin fast path
                                        valid(env)
                                    } else {
                                        // Dispatch to simple shape subtyping
                                        simplify_subtype_shape(
                                            subtype_env,
                                            env,
                                            this_ty,
                                            super_like,
                                            (supportdyn_sub, r_sub.clone(), kind_sub, &fdm_sub),
                                            (
                                                supportdyn_super,
                                                r_super.clone(),
                                                kind_super,
                                                &fdm_super,
                                            ),
                                        )
                                    }
                                }
                                _ => {
                                    // At least one type is a splat and neither have tyvars so use the
                                    // ground corners procedure
                                    subrow_splat(
                                        subtype_env,
                                        env,
                                        cache,
                                        this_ty,
                                        super_like,
                                        &r_sub,
                                        &norm_sub,
                                        &norm_super,
                                    )
                                }
                            },
                            ([], [_, ..]) => {
                                // At least one type variable in the supertype, none in the subtype
                                subrow_infer_super(
                                    subtype_env,
                                    env,
                                    cache,
                                    this_ty,
                                    super_like,
                                    &r_sub,
                                    &norm_sub,
                                    &norm_super,
                                    &sv_super,
                                )
                            }
                            ([_, ..], []) => {
                                // At least one type variable in the subtype, none in the supertype
                                subrow_infer_sub(
                                    subtype_env,
                                    env,
                                    cache,
                                    this_ty,
                                    super_like,
                                    &r_sub,
                                    &norm_sub,
                                    &norm_super,
                                    &sv_sub,
                                )
                            }
                            ([sub_v], [super_v]) => {
                                // Exactly one tyvar in each of the sub- and supertypes; solve using
                                // a fresh coupled tyvar acting as upper bound for one and lower bound
                                // for the other.
                                subrow_infer_couple(
                                    subtype_env,
                                    env,
                                    cache,
                                    this_ty,
                                    super_like,
                                    &r_sub,
                                    &norm_sub,
                                    *sub_v,
                                    &norm_super,
                                    *super_v,
                                )
                            }
                            ([_, ..], [_, ..]) => {
                                // Multiple spread vars on at least one side: decoupled fallback.
                                // Resolve the other side's spread vars to their current solutions,
                                // then run single-side inference each way.
                                let solved_super = typing_corners::solve_spread_vars(
                                    env,
                                    r_sub.clone(),
                                    &norm_super,
                                );
                                let prop_sub = match row::as_row(solved_super.clone()) {
                                    Some(super_) => subrow_infer_sub(
                                        subtype_env,
                                        env,
                                        cache,
                                        this_ty,
                                        super_like,
                                        &r_sub,
                                        &norm_sub,
                                        &super_,
                                        &sv_sub,
                                    ),
                                    None => {
                                        let ty_sub = row::to_ty(r_sub.clone(), &norm_sub);
                                        let ty_super = row::normalized_to_ty(
                                            env,
                                            r_super.clone(),
                                            solved_super,
                                        );
                                        simplify_(
                                            subtype_env,
                                            this_ty,
                                            Lhs {
                                                sub_supportdyn: sub_supportdyn_reason.as_ref(),
                                                ty_sub: &ty_sub,
                                            },
                                            Rhs {
                                                super_supportdyn: supportdyn_super,
                                                super_like,
                                                ty_super: &ty_super,
                                            },
                                            env,
                                        )
                                    }
                                };
                                let solved_sub = typing_corners::solve_spread_vars(
                                    env,
                                    r_sub.clone(),
                                    &norm_sub,
                                );
                                let prop_super = match row::as_row(solved_sub.clone()) {
                                    Some(sub_) => subrow_infer_super(
                                        subtype_env,
                                        env,
                                        cache,
                                        this_ty,
                                        super_like,
                                        &r_sub,
                                        &sub_,
                                        &norm_super,
                                        &sv_super,
                                    ),
                                    None => {
                                        let ty_sub =
                                            row::normalized_to_ty(env, r_sub.clone(), solved_sub);
                                        let ty_super = row::to_ty(r_super.clone(), &norm_super);
                                        simplify_(
                                            subtype_env,
                                            this_ty,
                                            Lhs {
                                                sub_supportdyn: sub_supportdyn_reason.as_ref(),
                                                ty_sub: &ty_sub,
                                            },
                                            Rhs {
                                                super_supportdyn: supportdyn_super,
                                                super_like,
                                                ty_super: &ty_super,
                                            },
                                            env,
                                        )
                                    }
                                };
                                tl::conj(prop_sub, prop_super)
                            }
                        }
                    }
                }
            }
        }
    }
}

// -- Splat subtyping -----------------------------------------------------

/// At least one type is a splat and neither type contains tyvars; apply
/// the ground corners procedure per label
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_splat(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    sub: &row::T,
    super_: &row::T,
) -> tl::SubtypeProp {
    let labels = typing_corners::subrow_labels(cache, env, sub, super_, r.clone());
    let mut acc = valid(env);
    for label in labels.iter() {
        acc = and(env, acc, |env| {
            subrow_splat_at(
                subtype_env,
                env,
                cache,
                this_ty,
                super_like,
                r,
                sub,
                super_,
                label.as_ref(),
            )
        });
    }
    acc
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_splat_at(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    sub: &row::T,
    super_: &row::T,
    label: Option<&TShapeField>,
) -> tl::SubtypeProp {
    let live_super =
        typing_corners::splat_elem::set::of_list(typing_corners::row_live_spread_at(super_, label));
    // Attribute field failures to a named supertype spread elem live at this label.
    let blame: Option<(PosOrDecl, String)> = typing_corners::splat_elem::set::elements(&live_super)
        .iter()
        .find_map(|ty| match get_node(ty) {
            Ty_::Tgeneric(name) | Ty_::Tnewtype(name, _, _) => Some((get_pos(ty), name.clone())),
            _ => None,
        });
    // Attribute unknown-tail failures only when checking the tail projection.
    let tail_blame = match label {
        Some(_) => None,
        None => blame.clone(),
    };
    // `f env ~sub ~super`, and `~init:valid ~conj:( &&& )`.
    //
    // Check subfields at all corner assignments
    let result = typing_corners::check_subrow_corners(
        cache,
        env,
        sub,
        super_,
        label,
        r.clone(),
        |env| valid(env),
        |env, acc, k| and(env, acc, k),
        |env, sub, super_| {
            subrow_subfield(
                subtype_env,
                env,
                this_ty,
                super_like,
                r,
                tail_blame.as_ref(),
                blame.as_ref(),
                label,
                sub,
                super_,
            )
        },
    );
    match result {
        Ok(typing_corners::Computation::Computed(prop)) => prop,
        Ok(typing_corners::Computation::Empty) => valid(env),
        Ok(typing_corners::Computation::UnsupportedCycle(info)) => report_shape_splat_failure(
            subtype_env,
            r,
            sub,
            super_,
            env,
            ShapeSplatFailure::UnsupportedCycle(info),
        ),
        Err(missing) => report_shape_splat_failure(
            subtype_env,
            r,
            sub,
            super_,
            env,
            ShapeSplatFailure::MissingAssignment(missing),
        ),
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_subfield(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    tail_blame: Option<&(PosOrDecl, String)>,
    blame: Option<&(PosOrDecl, String)>,
    label: Option<&TShapeField>,
    sub: ShapeFieldType,
    super_: ShapeFieldType,
) -> tl::SubtypeProp {
    match label {
        Some(field_name) => {
            // Map a field descriptor to a shape projection: an [Opt nothing] field
            // denotes an absent label
            let to_proj = |fd: &ShapeFieldType| {
                if fd.optional && typing_defs::is_nothing(&fd.ty) {
                    ShapeProjection::Absent
                } else if fd.optional {
                    ShapeProjection::Optional(fd.ty.clone())
                } else {
                    ShapeProjection::Required(fd.ty.clone())
                }
            };
            let on_type_mismatch = match blame {
                None => None,
                Some((decl_pos, name)) => subtype_env.on_error.clone().map(|on_error| {
                    reasons_callback::prepend_on_apply(
                        on_error,
                        secondary::T::Splat_field_not_known {
                            pos: reason::to_pos(r),
                            decl_pos: decl_pos.clone(),
                            name: name.clone(),
                            field: t_utils::get_printable_shape_field_name(&field_name.0)
                                .to_string(),
                        },
                    )
                }),
            };
            // (The arguments are evaluated right to left; `to_proj` has no
            // effect.)
            match simplify_subtype_shape_projection(
                on_type_mismatch,
                subtype_env,
                this_ty,
                super_like,
                env,
                (false, r, to_proj(&sub)),
                (false, r, to_proj(&super_)),
                field_name,
            ) {
                Ok(f) => f(env),
                Err(fail) => invalid(fail, env),
            }
        }
        None => {
            if typing_corners::field::requiredness_lte(&sub, &super_) {
                simplify_(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &sub.ty,
                    },
                    Rhs {
                        super_supportdyn: false,
                        super_like,
                        ty_super: &super_.ty,
                    },
                    env,
                )
            } else {
                let (decl_pos, name) = match tail_blame {
                    Some((pos, name)) => (pos.clone(), Some(name.clone())),
                    None => (reason::to_pos(r), None),
                };
                let fail = subtype_env.on_error.clone().map(|on_error| {
                    typing_error::apply_reasons(
                        secondary::T::Splat_may_require_fields {
                            pos: reason::to_pos(r),
                            decl_pos,
                            name,
                        },
                        on_error,
                    )
                });
                invalid(fail, env)
            }
        }
    }
}

// -- Splat inference -----------------------------------------------------

/// Infer lower bounds for the super row's spread type variables. The sub row
/// has no unsolved spread variables, so its projected fields determine what
/// each super type variable must accept.
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_infer_super(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    sub: &row::T,
    super_: &row::T,
    super_spread_vars: &[tvid::T],
) -> tl::SubtypeProp {
    let mut acc = valid(env);
    for v in super_spread_vars.iter().copied() {
        acc = and(env, acc, |env| {
            match typing_corners::partition_at_tyvar(super_, v) {
                None => valid(env),
                Some((pre_elems, post_elems)) => {
                    let (super_pre, super_post) = {
                        let on_error = &subtype_env.on_error;
                        let (_e1, super_pre) = {
                            let shape_ty = ShapeType::ShapeSplat(ShapeTypeSplat {
                                ss_elems: pre_elems,
                            });
                            row::normalize(on_error.clone(), r.clone(), shape_ty, env)
                        };
                        let (_e2, super_post) = {
                            let shape_ty = ShapeType::ShapeSplat(ShapeTypeSplat {
                                ss_elems: post_elems,
                            });
                            row::normalize(on_error.clone(), r.clone(), shape_ty, env)
                        };
                        (super_pre, super_post)
                    };
                    match (row::as_row(super_pre), row::as_row(super_post)) {
                        (Some(super_pre), Some(super_post)) => {
                            if !row::is_bottom(&super_pre) && !row::is_bottom(&super_post) {
                                match subrow_infer_super_part(
                                    subtype_env,
                                    env,
                                    cache,
                                    this_ty,
                                    super_like,
                                    r,
                                    mk((r.clone(), Ty_::Tvar(v))),
                                    sub,
                                    &super_pre,
                                    &super_post,
                                    super_,
                                ) {
                                    Ok(prop) => prop,
                                    Err(failure) => report_shape_splat_failure(
                                        subtype_env,
                                        r,
                                        sub,
                                        super_,
                                        env,
                                        failure,
                                    ),
                                }
                            } else {
                                valid(env)
                            }
                        }
                        (None, _) | (_, None) => {
                            // A partition cannot currently distribute a union. Keep this
                            // conservative fallback if that invariant changes.
                            invalid(None, env)
                        }
                    }
                }
            }
        });
    }
    acc
}

/// Build a shape lower bound for the spread variable, using fresh type variables
/// for fields it may contribute. Generate per-field constraints relating the
/// subtype's fields to those variables and to fields contributed by the prefix
/// and suffix. Fields fully masked by the suffix are checked directly and do
/// not constrain the spread variable.
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_infer_super_part(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    spread_var_ty: Ty,
    sub: &row::T,
    super_pre: &row::T,
    super_post: &row::T,
    super_: &row::T,
) -> ShapeSplatResult<tl::SubtypeProp> {
    let labels = typing_corners::subrow_labels(cache, env, sub, super_, r.clone());
    let mut known: TShapeMap<ShapeFieldType> = TShapeMap::new();
    let mut unknown = make_type::nothing(r.clone());
    // `props` is the OCaml list built by consing, the last label's first:
    // here in the order of the labels.
    let mut props: Vec<tl::SubtypeProp> = vec![];
    for label in labels.iter() {
        let (field, prop) = subrow_infer_super_part_at(
            subtype_env,
            env,
            cache,
            this_ty,
            super_like,
            r,
            sub,
            super_pre,
            super_post,
            super_,
            label.as_ref(),
        )?;
        match label {
            Some(lbl) => {
                known.insert(lbl.clone(), field);
            }
            None => unknown = field.ty,
        }
        props.push(prop);
    }
    let bound = row::of_simple(ShapeTypeSimple {
        origin: TypeOrigin::MissingOrigin,
        unknown_value: unknown,
        fields: known,
    });
    let bound_ty = row::to_ty(r.clone(), &bound);
    let prop_resid = simplify_(
        subtype_env,
        this_ty,
        Lhs {
            sub_supportdyn: None,
            ty_sub: &bound_ty,
        },
        Rhs {
            super_supportdyn: false,
            super_like,
            ty_super: &spread_var_ty,
        },
        env,
    );
    // `List.fold_left props ~init:prop_resid ~f:TL.conj`
    let mut prop = prop_resid;
    for p in props.into_iter().rev() {
        prop = tl::conj(prop, p);
    }
    Ok(prop)
}

/// Infer [label]'s field in the spread variable's lower-bound shape and generate
/// the constraints needed at that label for every corner assignment. Where the
/// spread variable is live, use a fresh field type and constrain the subtype
/// field against the rightmost-wins merge of [super_pre], that fresh field, and
/// [super_post]. Where [super_post] masks the variable, check the subtype field
/// directly against [super_post]. If the variable need not contribute the field
/// in any case, represent that lack of a requirement as an absent field
///
/// The OCaml returns `(env, (field, prop))`, or the failure.
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_infer_super_part_at(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    sub: &row::T,
    super_pre: &row::T,
    super_post: &row::T,
    super_: &row::T,
    label: Option<&TShapeField>,
) -> ShapeSplatResult<(ShapeFieldType, tl::SubtypeProp)> {
    let absent = ShapeFieldType {
        optional: true,
        ty: make_type::nothing(r.clone()),
    };
    let live_names = {
        // (The arguments of `union` are evaluated right to left;
        // `row_live_spread_at` has no effect.)
        let live_super = typing_corners::splat_elem::set::of_list(
            typing_corners::row_live_spread_at(super_, label),
        );
        let live_sub = typing_corners::splat_elem::set::of_list(
            typing_corners::row_live_spread_at(sub, label),
        );
        typing_corners::splat_elem::set::union(&live_sub, &live_super)
    };
    let assignments = shape_splat_assignments(cache, env, &live_names, label, r)?;
    let assignments = match assignments {
        None => return Ok((absent, tl::valid())),
        Some(assignments) => assignments,
    };
    // `info` is built by consing and then reversed: here in the order of the
    // assignments.
    let mut info: Vec<(bool, ShapeFieldType, typing_corners::assignment::T)> = vec![];
    for assignment in assignments {
        let fd_post = project_shape_splat(env, super_post, label, &assignment)?;
        let fd_sub = project_shape_splat(env, sub, label, &assignment)?;
        info.push((
            typing_corners::field::is_required(&fd_post),
            fd_sub,
            assignment,
        ));
    }
    let live: Vec<&(bool, ShapeFieldType, typing_corners::assignment::T)> =
        info.iter().filter(|(masked, _, _)| !masked).collect();
    match live.as_slice() {
        [] => {
            // the spread tyvar is overwritten by [super_post] everywhere: it
            // contributes nothing to the lower bound at this label. The field is absent,
            // optional-[nothing], not required-[nothing], which would make the
            // inferred row uninhabited.
            let mut prop = tl::valid();
            for (_, fd_sub, assignment) in info.iter() {
                prop = shape_splat_conj(env, prop, |env| {
                    let fd_super = project_shape_splat(env, super_post, label, assignment)?;
                    let prop = subrow_subfield(
                        subtype_env,
                        env,
                        this_ty,
                        super_like,
                        r,
                        None,
                        None,
                        label,
                        fd_sub.clone(),
                        fd_super,
                    );
                    Ok(prop)
                })?;
            }
            Ok((absent, prop))
        }
        _ => {
            let is_opt = live
                .iter()
                .any(|(_, fd_sub, _)| typing_corners::field::is_optional(fd_sub));
            // A field which contributes `nothing` must not appear as required since
            // this means the shape is uninhabited
            let mut contributes_nothing = true;
            for (_, fd_sub, assignment) in live.iter() {
                let discharged = contributes_nothing;
                contributes_nothing = if !discharged {
                    false
                } else if typing_corners::field::is_absent(fd_sub, env) {
                    // [nothing] fits under anything; no need to probe
                    true
                } else {
                    let fd_post = project_shape_splat(env, super_post, label, assignment)?;
                    let base = if is_opt {
                        let fd_pre = project_shape_splat(env, super_pre, label, assignment)?;
                        typing_union::union(env, None, None, fd_pre.ty, fd_post.ty)
                    } else {
                        fd_post.ty
                    };
                    // The environment this probe leaves is dropped.
                    let p = simplify_(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn: None,
                            ty_sub: &fd_sub.ty,
                        },
                        Rhs {
                            super_supportdyn: false,
                            super_like,
                            ty_super: &base,
                        },
                        &mut env.clone(),
                    );
                    tl::is_valid(&p)
                };
            }
            let flex = env::fresh_type(env, Pos::NONE);
            let mut prop = tl::valid();
            for (masked, fd_sub, assignment) in info.iter() {
                prop = shape_splat_conj(env, prop, |env| {
                    if *masked {
                        let fd_super = project_shape_splat(env, super_post, label, assignment)?;
                        let prop = subrow_subfield(
                            subtype_env,
                            env,
                            this_ty,
                            super_like,
                            r,
                            None,
                            None,
                            label,
                            fd_sub.clone(),
                            fd_super,
                        );
                        Ok(prop)
                    } else {
                        let fd_pre = project_shape_splat(env, super_pre, label, assignment)?;
                        if typing_corners::field::is_optional(fd_sub)
                            && typing_corners::field::is_required(&fd_pre)
                        {
                            // Opt </:_req Req
                            let prop = invalid(None, env);
                            Ok(prop)
                        } else {
                            let fd_post = project_shape_splat(env, super_post, label, assignment)?;
                            let ty = typing_union::union(env, None, None, flex.clone(), fd_post.ty);
                            let super_base = if is_opt {
                                typing_union::union(env, None, None, fd_pre.ty, ty)
                            } else {
                                ty
                            };
                            let prop = simplify_(
                                subtype_env,
                                this_ty,
                                Lhs {
                                    sub_supportdyn: None,
                                    ty_sub: &fd_sub.ty,
                                },
                                Rhs {
                                    super_supportdyn: false,
                                    super_like,
                                    ty_super: &super_base,
                                },
                                env,
                            );
                            Ok(prop)
                        }
                    }
                })?;
            }
            let field = if contributes_nothing {
                ShapeFieldType {
                    optional: true,
                    ty: make_type::nothing(r.clone()),
                }
            } else {
                ShapeFieldType {
                    optional: is_opt,
                    ty: flex,
                }
            };
            Ok((field, prop))
        }
    }
}

/// Infer upper bounds for the sub row's spread inference variables. The super
/// row has no unsolved spread variables, so its projected fields determine what
/// each sub variable may provide.
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_infer_sub(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    sub: &row::T,
    super_: &row::T,
    sub_spread_vars: &[tvid::T],
) -> tl::SubtypeProp {
    let mut acc = valid(env);
    for v in sub_spread_vars.iter().copied() {
        acc = and(env, acc, |env| {
            match typing_corners::partition_at_tyvar(sub, v) {
                None => valid(env),
                Some((pre_elems, post_elems)) => {
                    let (sub_pre, sub_post) = {
                        let on_error = &subtype_env.on_error;
                        let (_e1, sub_pre) = {
                            let shape_ty = ShapeType::ShapeSplat(ShapeTypeSplat {
                                ss_elems: pre_elems,
                            });
                            row::normalize(on_error.clone(), r.clone(), shape_ty, env)
                        };
                        let (_e2, sub_post) = {
                            let shape_ty = ShapeType::ShapeSplat(ShapeTypeSplat {
                                ss_elems: post_elems,
                            });
                            row::normalize(on_error.clone(), r.clone(), shape_ty, env)
                        };
                        (sub_pre, sub_post)
                    };
                    match (row::as_row(sub_pre), row::as_row(sub_post)) {
                        (Some(sub_pre), Some(sub_post)) => {
                            if !row::is_bottom(&sub_pre) && !row::is_bottom(&sub_post) {
                                match subrow_infer_sub_part(
                                    subtype_env,
                                    env,
                                    cache,
                                    this_ty,
                                    super_like,
                                    r,
                                    mk((r.clone(), Ty_::Tvar(v))),
                                    &sub_pre,
                                    &sub_post,
                                    sub,
                                    super_,
                                ) {
                                    Ok(prop) => prop,
                                    Err(failure) => report_shape_splat_failure(
                                        subtype_env,
                                        r,
                                        sub,
                                        super_,
                                        env,
                                        failure,
                                    ),
                                }
                            } else {
                                valid(env)
                            }
                        }
                        (None, _) | (_, None) => {
                            // A partition cannot currently distribute a union. Keep this
                            // conservative fallback if that invariant changes.
                            invalid(None, env)
                        }
                    }
                }
            }
        });
    }
    acc
}

/// Construct an upper-bound shape for a sub-row spread type variable after
/// partitioning the sub row into [sub_pre] and [sub_post]. For each field, infer
/// what the variable may contribute and generate constraints checking that the
/// rightmost-wins merge of [sub_pre], the variable, and [sub_post] is a subtype
/// of [super]. Finally constrain the spread type variable below the constructed
/// bound.
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_infer_sub_part(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    spread_var_ty: Ty,
    sub_pre: &row::T,
    sub_post: &row::T,
    sub: &row::T,
    super_: &row::T,
) -> ShapeSplatResult<tl::SubtypeProp> {
    let labels = typing_corners::subrow_labels(cache, env, sub, super_, r.clone());
    let mut known: TShapeMap<ShapeFieldType> = TShapeMap::new();
    let mut unknown = make_type::mixed(r.clone());
    // `props` is the OCaml list built by consing, the last label's first:
    // here in the order of the labels.
    let mut props: Vec<tl::SubtypeProp> = vec![];
    for label in labels.iter() {
        let (field, prop) = subrow_infer_sub_part_at(
            subtype_env,
            env,
            cache,
            this_ty,
            super_like,
            r,
            sub_pre,
            sub_post,
            sub,
            super_,
            label.as_ref(),
        )?;
        match label {
            Some(lbl) => {
                known.insert(lbl.clone(), field);
            }
            None => unknown = field.ty,
        }
        props.push(prop);
    }
    let bound = row::of_simple(ShapeTypeSimple {
        origin: TypeOrigin::MissingOrigin,
        unknown_value: unknown,
        fields: known,
    });

    let bound_ty = row::to_ty(r.clone(), &bound);
    let prop_resid = simplify_(
        subtype_env,
        this_ty,
        Lhs {
            sub_supportdyn: None,
            ty_sub: &spread_var_ty,
        },
        Rhs {
            super_supportdyn: false,
            super_like,
            ty_super: &bound_ty,
        },
        env,
    );
    // `List.fold_left props ~init:prop_resid ~f:TL.conj`
    let mut prop = prop_resid;
    for p in props.into_iter().rev() {
        prop = tl::conj(prop, p);
    }
    Ok(prop)
}

/// Infer [label]'s field in the spread variable's upper-bound shape and generate
/// constraints for every corner assignment. If [sub_post] masks the variable,
/// check [sub_post] directly against [super]. Otherwise, require the variable
/// to mask any optional or incompatible [sub_pre] field, bound its field type by
/// the live [super] field types, and check the remaining fixed contributions.
/// If the variable is always masked, give it the unconstrained top field.
///
/// The OCaml returns `(env, (field, prop))`, or the failure.
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_infer_sub_part_at(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    sub_pre: &row::T,
    sub_post: &row::T,
    sub: &row::T,
    super_: &row::T,
    label: Option<&TShapeField>,
) -> ShapeSplatResult<(ShapeFieldType, tl::SubtypeProp)> {
    let top = ShapeFieldType {
        optional: true,
        ty: make_type::mixed(r.clone()),
    };
    let live_names = {
        // (The arguments of `union` are evaluated right to left;
        // `row_live_spread_at` has no effect.)
        let live_super = typing_corners::splat_elem::set::of_list(
            typing_corners::row_live_spread_at(super_, label),
        );
        let live_sub = typing_corners::splat_elem::set::of_list(
            typing_corners::row_live_spread_at(sub, label),
        );
        typing_corners::splat_elem::set::union(&live_sub, &live_super)
    };
    let assignments = shape_splat_assignments(cache, env, &live_names, label, r)?;
    let assignments = match assignments {
        None => return Ok((top, tl::valid())),
        Some(assignments) => assignments,
    };
    // `info` is built by consing and then reversed: here in the order of the
    // assignments.
    let mut info: Vec<(bool, ShapeFieldType, typing_corners::assignment::T)> = vec![];
    for assignment in assignments {
        let fd_post = project_shape_splat(env, sub_post, label, &assignment)?;
        let fd_super = project_shape_splat(env, super_, label, &assignment)?;
        info.push((
            typing_corners::field::is_required(&fd_post),
            fd_super,
            assignment,
        ));
    }
    let live: Vec<&(bool, ShapeFieldType, typing_corners::assignment::T)> =
        info.iter().filter(|(masked, _, _)| !masked).collect();
    match live.as_slice() {
        [] => {
            // the spread var is overwritten by [sub_post] everywhere: its upper bound
            // is the top field
            let mut prop = tl::valid();
            for (_, fd_super, assignment) in info.iter() {
                prop = shape_splat_conj(env, prop, |env| {
                    let fd_sub = project_shape_splat(env, sub_post, label, assignment)?;
                    let prop = subrow_subfield(
                        subtype_env,
                        env,
                        this_ty,
                        super_like,
                        r,
                        None,
                        None,
                        label,
                        fd_sub,
                        fd_super.clone(),
                    );
                    Ok(prop)
                })?;
            }
            Ok((top, prop))
        }
        _ => {
            // The spread var must be [Req] iff, at some live assignment, the field is [Req]
            // in super and [Opt] in [sub_pre], or [sub_pre]'s type does not fit super (so the
            // var must mask [sub_pre]). At the [None] unknown label the contribution is
            // opt-only.
            //
            // (Each probe projects in a copy of the environment, which it then
            // drops; a projection which fails returns the environment it
            // left.)
            let is_req = match label {
                None => false,
                Some(_) => {
                    let mut is_required = false;
                    for (_, fd_super, assignment) in live.iter() {
                        let mut env_probe = env.clone();
                        let fd_pre =
                            match project_shape_splat(&mut env_probe, sub_pre, label, assignment) {
                                Ok(fd_pre) => fd_pre,
                                Err(failure) => {
                                    *env = env_probe;
                                    return Err(failure);
                                }
                            };
                        let required = typing_corners::field::is_required(fd_super)
                            && typing_corners::field::is_optional(&fd_pre)
                            || {
                                let prop = simplify_(
                                    subtype_env,
                                    this_ty,
                                    Lhs {
                                        sub_supportdyn: None,
                                        ty_sub: &fd_pre.ty,
                                    },
                                    Rhs {
                                        super_supportdyn: false,
                                        super_like,
                                        ty_super: &fd_super.ty,
                                    },
                                    &mut env_probe,
                                );
                                tl::is_unsat(&prop)
                            };
                        if required {
                            is_required = true;
                            break;
                        }
                    }
                    is_required
                }
            };
            // Decompose the field obligation instead of introducing a fresh tyvar:
            // [(fixed | tyvar) <: super] iff both [fixed <: super] and
            // [tyvar<: super].
            let upper_ty = make_type::intersection(
                r.clone(),
                live.iter()
                    .map(|(_, fd_super, _)| sd::liken(super_like, env, fd_super.ty.clone()))
                    .collect(),
            );
            let mut prop = tl::valid();
            for (masked, fd_super, assignment) in info.iter() {
                prop = shape_splat_conj(env, prop, |env| {
                    if *masked {
                        let fd_sub = project_shape_splat(env, sub_post, label, assignment)?;
                        let prop = subrow_subfield(
                            subtype_env,
                            env,
                            this_ty,
                            super_like,
                            r,
                            None,
                            None,
                            label,
                            fd_sub,
                            fd_super.clone(),
                        );
                        Ok(prop)
                    } else {
                        let fd_post = project_shape_splat(env, sub_post, label, assignment)?;
                        let sub_base = if is_req {
                            fd_post.ty
                        } else {
                            let fd_pre = project_shape_splat(env, sub_pre, label, assignment)?;
                            make_type::union(r.clone(), vec![fd_pre.ty, fd_post.ty])
                        };
                        let prop = simplify_(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn: None,
                                ty_sub: &sub_base,
                            },
                            Rhs {
                                super_supportdyn: false,
                                super_like,
                                ty_super: &fd_super.ty,
                            },
                            env,
                        );
                        Ok(prop)
                    }
                })?;
            }
            Ok((
                ShapeFieldType {
                    optional: !is_req,
                    ty: upper_ty,
                },
                prop,
            ))
        }
    }
}

/// Both sub- and super rows have a single type variable. Dispatch on whether
/// it's the type variable in both positions
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_infer_couple(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    sub: &row::T,
    sub_spread_var: tvid::T,
    super_: &row::T,
    super_spread_var: tvid::T,
) -> tl::SubtypeProp {
    if tvid::equal(sub_spread_var, super_spread_var) {
        match subrow_infer_same_var(
            subtype_env,
            env,
            cache,
            this_ty,
            super_like,
            r,
            sub,
            super_,
            sub_spread_var,
        ) {
            Ok(Some(prop)) => prop,
            Ok(None) => subrow_infer_couple_mid(
                subtype_env,
                env,
                cache,
                this_ty,
                super_like,
                r,
                sub,
                sub_spread_var,
                super_,
                super_spread_var,
            ),
            Err(failure) => report_shape_splat_failure(subtype_env, r, sub, super_, env, failure),
        }
    } else {
        subrow_infer_couple_mid(
            subtype_env,
            env,
            cache,
            this_ty,
            super_like,
            r,
            sub,
            sub_spread_var,
            super_,
            super_spread_var,
        )
    }
}

/// For splat rows of the form [A, V, B] <: [V, D], derive per-label bounds
/// [lo <: V <: hi]. Since we don't have presence variables, the
/// [subrow_infer_couple_mid] fallback has to assume all fields are required
/// but here we can assume optional and improve completeness for just this case.
/// Return [None] when the rows don't have this layout .
///
/// The OCaml returns `TL.subtype_prop option shape_splat_result`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_infer_same_var(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    sub: &row::T,
    super_: &row::T,
    v: tvid::T,
) -> ShapeSplatResult<Option<tl::SubtypeProp>> {
    // This is a speculative fast path. On [None], discard any environment
    // changes made while probing and retry the general algorithm from the
    // original environment.
    let initial_env = env.clone();
    // An empty element list is the empty CLOSED shape (the merge identity), NOT the
    // bottom row that [normalize_row] would collapse it to.
    let to_shape = |env: &mut Env, elems: Vec<Ty>| -> Option<row::T> {
        if elems.is_empty() {
            let s_fields = TShapeMap::new();
            let s_unknown_value = make_type::nothing(r.clone());
            Some(row::of_simple(ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                unknown_value: s_unknown_value,
                fields: s_fields,
            }))
        } else {
            let (_e, normalized) = {
                let shape_ty = ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems: elems });
                let on_error = subtype_env.on_error.clone();
                row::normalize(on_error, r.clone(), shape_ty, env)
            };
            row::fold_normalized(
                normalized,
                |shape_row| {
                    if row::is_bottom(&shape_row) {
                        None
                    } else {
                        Some(shape_row)
                    }
                },
                |_| {
                    // Leave this special case and use coupled inference instead.
                    None
                },
                |_| {
                    // Leave this special case and use coupled inference instead.
                    None
                },
            )
        }
    };
    let bottom_field = ShapeFieldType {
        optional: false,
        ty: make_type::nothing(r.clone()),
    };
    match (
        typing_corners::partition_at_tyvar(sub, v),
        typing_corners::partition_at_tyvar(super_, v),
    ) {
        (Some((sub_pre_e, sub_post_e)), Some((super_pre_e, super_post_e)))
            if super_pre_e.is_empty() =>
        {
            // Normalize sequentially to thread [env] and stop at a bottom segment.
            let sub_pre = match to_shape(env, sub_pre_e) {
                None => {
                    *env = initial_env;
                    return Ok(None);
                }
                Some(sub_pre) => sub_pre,
            };
            let sub_post = match to_shape(env, sub_post_e) {
                None => {
                    *env = initial_env;
                    return Ok(None);
                }
                Some(sub_post) => sub_post,
            };
            let super_post = match to_shape(env, super_post_e) {
                None => {
                    *env = initial_env;
                    return Ok(None);
                }
                Some(super_post) => super_post,
            };
            let mut labels: Vec<Option<TShapeField>> = vec![None];
            labels.extend(
                typing_corners::subrow_label_set(cache, env, sub, super_, r.clone())
                    .into_iter()
                    .map(Some),
            );
            let add_field = |known: &mut TShapeMap<ShapeFieldType>,
                             unknown: &mut Ty,
                             label: &Option<TShapeField>,
                             fd: ShapeFieldType| match label {
                Some(lbl) => {
                    known.insert(lbl.clone(), fd);
                }
                None => *unknown = fd.ty,
            };
            // `label_props` is built by consing: here in the order of the
            // assignments.
            let mut bounds_at_label = |env: &mut Env,
                                       label: Option<&TShapeField>|
             -> ShapeSplatResult<(
                ShapeFieldType,
                ShapeFieldType,
                Vec<tl::SubtypeProp>,
            )> {
                let live_names = {
                    // (The arguments of `union` are evaluated right to left;
                    // `row_live_spread_at` has no effect.)
                    let live_super = typing_corners::splat_elem::set::of_list(
                        typing_corners::row_live_spread_at(super_, label),
                    );
                    let live_sub = typing_corners::splat_elem::set::of_list(
                        typing_corners::row_live_spread_at(sub, label),
                    );
                    typing_corners::splat_elem::set::union(&live_sub, &live_super)
                };
                let assignments = shape_splat_assignments(cache, env, &live_names, label, r)?;
                let top_field = ShapeFieldType {
                    optional: true,
                    ty: make_type::mixed(r.clone()),
                };
                match assignments {
                    None => Ok((bottom_field.clone(), top_field, vec![])),
                    Some(assignments) => {
                        let mut lower = bottom_field.clone();
                        let mut upper = top_field;
                        let mut label_props: Vec<tl::SubtypeProp> = vec![];
                        for assignment in assignments.iter() {
                            let a = project_shape_splat(env, &sub_pre, label, assignment)?;
                            let b = project_shape_splat(env, &sub_post, label, assignment)?;
                            let d = project_shape_splat(env, &super_post, label, assignment)?;
                            if typing_corners::field::is_required(&d) {
                                if typing_corners::field::is_required(&b) {
                                    // Both sides are masked: LHS=b and RHS=d.
                                    let prop = subrow_subfield(
                                        subtype_env,
                                        env,
                                        this_ty,
                                        super_like,
                                        r,
                                        None,
                                        None,
                                        label,
                                        b,
                                        d,
                                    );
                                    label_props.push(prop);
                                } else {
                                    // The super masks the shared var. Its upper bound
                                    // masks [sub_pre], while [sub_post]'s optional type
                                    // must independently fit under [d].
                                    upper = typing_corners::field::meet(upper, d.clone(), env);
                                    let prop = simplify_(
                                        subtype_env,
                                        this_ty,
                                        Lhs {
                                            sub_supportdyn: None,
                                            ty_sub: &b.ty,
                                        },
                                        Rhs {
                                            super_supportdyn: false,
                                            super_like,
                                            ty_super: &d.ty,
                                        },
                                        env,
                                    );
                                    label_props.push(prop);
                                }
                            } else if typing_corners::field::is_required(&b) {
                                // The sub masks the shared var, which must cover [b].
                                lower = typing_corners::field::join(lower, b, env);
                            } else {
                                // Neither side masks it, so it must absorb the sub-side
                                // fixed field.
                                let merged = typing_corners::field::merge(a, b, env);
                                lower = typing_corners::field::join(lower, merged, env);
                            }
                        }
                        Ok((lower, upper, label_props))
                    }
                }
            };
            let mut lo_known: TShapeMap<ShapeFieldType> = TShapeMap::new();
            let mut lo_unknown = make_type::nothing(r.clone());
            let mut hi_known: TShapeMap<ShapeFieldType> = TShapeMap::new();
            let mut hi_unknown = make_type::mixed(r.clone());
            // `props` is the OCaml list `List.rev_append label_props props`:
            // the last label's propositions first, each label's in the order
            // of its assignments. Here, each label's propositions (in the
            // order of its assignments), in the order of the labels.
            let mut props: Vec<Vec<tl::SubtypeProp>> = vec![];
            for label in labels.iter() {
                let (lower, upper, label_props) = bounds_at_label(env, label.as_ref())?;
                add_field(&mut lo_known, &mut lo_unknown, label, lower);
                add_field(&mut hi_known, &mut hi_unknown, label, upper);
                props.push(label_props);
            }
            let lo = row::of_simple(ShapeTypeSimple {
                fields: lo_known,
                unknown_value: lo_unknown,
                origin: TypeOrigin::MissingOrigin,
            });
            let hi = row::of_simple(ShapeTypeSimple {
                fields: hi_known,
                unknown_value: hi_unknown,
                origin: TypeOrigin::MissingOrigin,
            });

            let v_ty = mk((r.clone(), Ty_::Tvar(v)));
            let lo_ty = row::to_ty(r.clone(), &lo);
            let prop_lo = simplify_(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &lo_ty,
                },
                Rhs {
                    super_supportdyn: false,
                    super_like,
                    ty_super: &v_ty,
                },
                env,
            );

            let hi_ty = row::to_ty(r.clone(), &hi);
            let prop_hi = simplify_(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &v_ty,
                },
                Rhs {
                    super_supportdyn: false,
                    super_like,
                    ty_super: &hi_ty,
                },
                env,
            );
            // `List.fold_left (prop_lo :: prop_hi :: props) ~init:TL.valid ~f:TL.conj`
            let mut prop = tl::valid();
            prop = tl::conj(prop, prop_lo);
            prop = tl::conj(prop, prop_hi);
            for p in props.into_iter().rev().flatten() {
                prop = tl::conj(prop, p);
            }
            Ok(Some(prop))
        }
        _ => {
            *env = initial_env;
            Ok(None)
        }
    }
}

/// Couple spread variables through a fresh simple row [mid], reducing the
/// original check to [sub <: mid <: super]. Its known fields are required
/// because it is not inferable (we have no 'presence' variables), so this can
/// reject solutions where the only valid intermediary has an optional field.
#[allow(clippy::too_many_arguments)]
pub(crate) fn subrow_infer_couple_mid(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    cache: &mut typing_corners::cache::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    r: &Reason,
    sub: &row::T,
    sub_spread_var: tvid::T,
    super_: &row::T,
    super_spread_var: tvid::T,
) -> tl::SubtypeProp {
    // `TShapeSet.fold`, in the order of the labels.
    let mut known: TShapeMap<ShapeFieldType> = TShapeMap::new();
    for lbl in typing_corners::subrow_label_set(cache, env, sub, super_, r.clone()) {
        let flex = env::fresh_type(env, Pos::NONE);
        known.insert(
            lbl,
            ShapeFieldType {
                optional: false,
                ty: flex,
            },
        );
    }
    let unknown = env::fresh_type(env, Pos::NONE);
    let mid = row::of_simple(ShapeTypeSimple {
        fields: known,
        unknown_value: unknown,
        origin: TypeOrigin::MissingOrigin,
    });
    let prop_sub = subrow_infer_sub(
        subtype_env,
        env,
        cache,
        this_ty,
        super_like,
        r,
        sub,
        &mid,
        &[sub_spread_var],
    );
    let prop_super = subrow_infer_super(
        subtype_env,
        env,
        cache,
        this_ty,
        super_like,
        r,
        &mid,
        super_,
        &[super_spread_var],
    );
    tl::conj(prop_sub, prop_super)
}

// == Simple shape subtyping ==============================================

pub(crate) fn simplify_subtype_shape(
    subtype_env: &subtype_env::T,
    env: &mut Env,
    this_ty: Option<&Ty>,
    super_like: bool,
    (supportdyn_sub, r_sub, shape_kind_sub, fdm_sub): (
        bool,
        Reason,
        Ty,
        &TShapeMap<ShapeFieldType>,
    ),
    (supportdyn_super, r_super, shape_kind_super, fdm_super): (
        bool,
        Reason,
        Ty,
        &TShapeMap<ShapeFieldType>,
    ),
) -> tl::SubtypeProp {
    // (The components of the tuple are evaluated right to left.)
    let super_kind_is_nothing = t_utils::is_nothing(env, &shape_kind_super);
    let sub_kind_is_nothing = t_utils::is_nothing(env, &shape_kind_sub);
    match (sub_kind_is_nothing, super_kind_is_nothing) {
        // An open shape cannot subtype a closed shape
        (false, true) => {
            let fail = subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Shape_fields_unknown {
                        pos: reason::to_pos(&r_sub),
                        decl_pos: reason::to_pos(&r_super),
                    },
                    on_error,
                )
            });
            invalid(fail, env)
        }
        // Otherwise, all projections must subtype
        (sub_unknown_is_nothing, _) => {
            let unknown_tails_identical =
                typing_defs_core::phys_equal(&shape_kind_sub, &shape_kind_super)
                    && supportdyn_sub == supportdyn_super;
            if std::ptr::eq(fdm_sub, fdm_super) && unknown_tails_identical {
                // Fast path: identical field maps and shape kinds
                valid(env)
            } else {
                // Use TShapeMap.merge to iterate both maps in O(n) instead of
                // constructing a TShapeSet in O(n log n). Collect field names
                // that need subtype checking (skip physically identical fields).
                //
                // (The keys of both maps, with the key of `fdm_sub` where both
                // have one: see the module documentation.)
                // The keys are walked in their order in both maps at once,
                // with what each map has for them (which the projections use
                // instead of looking the keys up again).
                let fields_to_check: Vec<ShapeFieldEntries<'_>> = merge_shape_maps(fdm_sub, fdm_super)
                    .into_iter()
                    .filter(|(_, f1, f2)| match (f1, f2) {
                        (Some(f1), Some(f2)) if phys_equal_shape_field_type(f1, f2) => false,
                        _ => true,
                    })
                    .collect();
                // The projections are made in the environment this function
                // is given (`~env`), the propositions in the environment that
                // the previous one leaves.
                let env_given = env.clone();
                let init = if sub_unknown_is_nothing || unknown_tails_identical {
                    // Either the subtype's unknown-field upper bound is provably
                    // [nothing], or both unknown-field projections are identical.
                    valid(env)
                } else {
                    // Otherwise ensure the proposition holds
                    simplify_subtype_shape_unknown_fields(
                        subtype_env,
                        this_ty,
                        super_like,
                        env,
                        (supportdyn_sub, &r_sub, &shape_kind_sub),
                        (supportdyn_super, &r_super, &shape_kind_super),
                    )
                };
                let mut acc = init;
                for (field_name, found_sub, found_super) in fields_to_check {
                    let res = shape_project_and_simplify_subtype(
                        subtype_env,
                        this_ty,
                        super_like,
                        &env_given,
                        (supportdyn_sub, &r_sub, &shape_kind_sub, found_sub),
                        (supportdyn_super, &r_super, &shape_kind_super, found_super),
                        field_name,
                    );
                    acc = match res {
                        Ok(prop) => and(env, acc, prop),
                        Err(fail) => and(env, acc, |env| invalid(fail, env)),
                    };
                }
                acc
            }
        }
    }
}

/// Unknown fields are optional projections at every label absent from both
/// field maps. Comparing their types once represents all of those labels.
pub(crate) fn simplify_subtype_shape_unknown_fields(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    super_like: bool,
    env: &mut Env,
    (supportdyn_sub, r_sub, shape_kind_sub): (bool, &Reason, &Ty),
    (supportdyn_super, r_super, shape_kind_super): (bool, &Reason, &Ty),
) -> tl::SubtypeProp {
    // (`let ... and ...` evaluates its bindings in order.)
    let ty_sub = shape_projection_type(supportdyn_sub, env, r_sub, shape_kind_sub.clone());
    let ty_super = shape_projection_type(supportdyn_super, env, r_super, shape_kind_super.clone());
    let prop = simplify_subtype_shape_type(
        std::borrow::Cow::Borrowed(subtype_env),
        this_ty,
        super_like,
        env,
        supportdyn_sub,
        r_sub,
        ty_sub,
        ty_super,
    );
    prop(env)
}

/// Helper function to project out a field and then simplify subtype
#[allow(clippy::too_many_arguments)]
/// A key of either of two shape maps, with what each map has for it (the key
/// is that of the first map when both have it).
type ShapeFieldEntries<'a> = (
    &'a TShapeField,
    Option<&'a ShapeFieldType>,
    Option<&'a ShapeFieldType>,
);

/// The keys of both maps in increasing order, each once, as `TShapeMap.merge`
/// visits them (one pass over both sorted maps).
fn merge_shape_maps<'a>(
    m1: &'a TShapeMap<ShapeFieldType>,
    m2: &'a TShapeMap<ShapeFieldType>,
) -> Vec<ShapeFieldEntries<'a>> {
    let mut res = Vec::with_capacity(m1.len().max(m2.len()));
    let (mut i1, mut i2) = (m1.iter().peekable(), m2.iter().peekable());
    loop {
        match (i1.peek(), i2.peek()) {
            (None, None) => break,
            (Some(_), None) => {
                let (k, v) = i1.next().unwrap();
                res.push((k, Some(v), None))
            }
            (None, Some(_)) => {
                let (k, v) = i2.next().unwrap();
                res.push((k, None, Some(v)))
            }
            (Some((k1, _)), Some((k2, _))) => match k1.cmp(k2) {
                std::cmp::Ordering::Less => {
                    let (k, v) = i1.next().unwrap();
                    res.push((k, Some(v), None))
                }
                std::cmp::Ordering::Greater => {
                    let (k, v) = i2.next().unwrap();
                    res.push((k, None, Some(v)))
                }
                std::cmp::Ordering::Equal => {
                    let (k, v1) = i1.next().unwrap();
                    let (_, v2) = i2.next().unwrap();
                    res.push((k, Some(v1), Some(v2)))
                }
            },
        }
    }
    res
}

/// The shape maps are represented by what they have for `field_name`
/// (`TShapeMap.find_opt field_name shape_map`, found by the caller).
pub(crate) fn shape_project_and_simplify_subtype<'a>(
    subtype_env: &'a subtype_env::T,
    this_ty: Option<&'a Ty>,
    super_like: bool,
    env: &Env,
    (supportdyn_sub, r_sub, shape_kind_sub, found_sub): (
        bool,
        &Reason,
        &Ty,
        Option<&ShapeFieldType>,
    ),
    (supportdyn_super, r_super, shape_kind_super, found_super): (
        bool,
        &Reason,
        &Ty,
        Option<&ShapeFieldType>,
    ),
    field_name: &TShapeField,
) -> Result<PropK<'a>, Option<typing_error::T>> {
    let proj_sub =
        shape_projection_of_found(supportdyn_sub, env, field_name, shape_kind_sub, found_sub, r_sub);
    let proj_super = shape_projection_of_found(
        supportdyn_super,
        env,
        field_name,
        shape_kind_super,
        found_super,
        r_super,
    );
    simplify_subtype_shape_projection(
        None,
        subtype_env,
        this_ty,
        super_like,
        env,
        (supportdyn_sub, r_sub, proj_sub),
        (supportdyn_super, r_super, proj_super),
        field_name,
    )
}

/// `Typing_utils.get_printable_shape_field_name field_name` as a `String`
/// (the `to_string` of the `BString` it gives: invalid UTF-8 is replaced as
/// `String::from_utf8_lossy` does), built directly.
fn printable_shape_field_name(field_name: &TShapeField) -> String {
    use crate::typing_defs_core::PosByteString;
    use crate::typing_defs_core::PosString;
    use crate::typing_defs_core::TshapeFieldName;
    match &field_name.0 {
        TshapeFieldName::TSFregexGroup(PosString(_, s)) => s.clone(),
        TshapeFieldName::TSFlitStr(PosByteString(_, s)) => String::from_utf8_lossy(s).into_owned(),
        TshapeFieldName::TSFclassConst(..) => {
            t_utils::get_printable_shape_field_name(&field_name.0).to_string()
        }
    }
}

/// For two particular projections `p1` and `p2`, `p1` <: `p2` iff:
///  - `p1` = `Required ty1`, `p2` = `Required ty2`, and `ty1` <: `ty2`
///  - `p1` = `Required ty1`, `p2` = `Optional ty2`, and `ty1` <: `ty2`
///  - `p1` = `Optional ty1`, `p2` = `Optional ty2`, and `ty1` <: `ty2`
///  - `p1` = `Absent`, `p2` = `Optional ty2`
///  - `p1` = `Absent`, `p2` = `Absent`
/// We therefore need to handle all other cases appropriately.
///
/// `?on_type_mismatch` is the first parameter (`None` for the default).
#[allow(clippy::too_many_arguments)]
pub(crate) fn simplify_subtype_shape_projection<'a>(
    on_type_mismatch: Option<reasons_callback::T>,
    subtype_env: &'a subtype_env::T,
    this_ty: Option<&'a Ty>,
    super_like: bool,
    env: &Env,
    (supportdyn_sub, r_sub, proj_sub): (bool, &Reason, ShapeProjection),
    (_supportdyn_super, r_super, proj_super): (bool, &Reason, ShapeProjection),
    field_name: &TShapeField,
) -> Result<PropK<'a>, Option<typing_error::T>> {
    let field_pos = t_shape_field::pos(&field_name.0);
    // The OCaml computes the printable name first; it is only used by the
    // error cases (and has no effect), so it is computed on first use.
    let printable_name = std::cell::LazyCell::new(|| printable_shape_field_name(field_name));
    type Projected = Option<((FieldKind, Ty), (FieldKind, Ty))>;
    let res: Result<Projected, Option<typing_error::T>> = match (proj_sub, proj_super) {
        // ***** "Successful" cases - 5 / 9 total cases *****
        (ShapeProjection::Required(ty_sub), ShapeProjection::Required(ty_super)) => Ok(Some((
            (FieldKind::Required, ty_sub),
            (FieldKind::Required, ty_super),
        ))),
        (ShapeProjection::Required(ty_sub), ShapeProjection::Optional(ty_super)) => Ok(Some((
            (FieldKind::Required, ty_sub),
            (FieldKind::Optional, ty_super),
        ))),
        (ShapeProjection::Optional(ty_sub), ShapeProjection::Optional(ty_super)) => Ok(Some((
            (FieldKind::Optional, ty_sub),
            (FieldKind::Optional, ty_super),
        ))),
        (ShapeProjection::Absent, ShapeProjection::Optional(_))
        | (ShapeProjection::Absent, ShapeProjection::Absent) => Ok(None),
        // ***** Error cases - 4 / 9 total cases *****
        (ShapeProjection::Required(ty_sub), ShapeProjection::Absent) => {
            let r_field_sub = get_reason(&env::update_reason(env, ty_sub, |r_sub_prj| {
                reason::prj_shape(
                    r_sub.clone(),
                    r_sub_prj,
                    r_super.clone(),
                    printable_name.clone(),
                    FieldKind::Required,
                    FieldKind::Absent,
                )
            }))
            .clone();
            let r_field_super = reason::missing_field();
            let ty_err_opt = subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Missing_field {
                        pos: reason::to_pos(r_super),
                        decl_pos: field_pos.clone(),
                        name: printable_name.clone(),
                        reason_sub: r_field_sub,
                        reason_super: r_field_super,
                    },
                    on_error,
                )
            });
            Err(ty_err_opt)
        }
        (ShapeProjection::Optional(ty_sub), ShapeProjection::Absent) => {
            // An optional field [?f => S] is compatible with an absent field only if
            // [S <: nothing]. If [S] is an unsolved type variable, as in shape-splat
            // inference, return the subtype obligation so inference can solve it to
            // [nothing]; otherwise report the more precise missing-field error.
            let ty_sub_expanded = env::expand_type(&mut env.clone(), ty_sub.clone());
            match get_node(&ty_sub_expanded) {
                Ty_::Tvar(_) => Ok(Some((
                    (FieldKind::Optional, ty_sub),
                    (FieldKind::Absent, make_type::nothing(r_super.clone())),
                ))),
                _ => {
                    let r_field_sub = get_reason(&env::update_reason(env, ty_sub, |r_sub_prj| {
                        reason::prj_shape(
                            r_sub.clone(),
                            r_sub_prj,
                            r_super.clone(),
                            printable_name.clone(),
                            FieldKind::Optional,
                            FieldKind::Absent,
                        )
                    }))
                    .clone();
                    let r_field_super = reason::missing_field();
                    let ty_err_opt = subtype_env.on_error.clone().map(|on_error| {
                        typing_error::apply_reasons(
                            secondary::T::Missing_field {
                                pos: reason::to_pos(r_super),
                                decl_pos: field_pos.clone(),
                                name: printable_name.clone(),
                                reason_sub: r_field_sub,
                                reason_super: r_field_super,
                            },
                            on_error,
                        )
                    });
                    Err(ty_err_opt)
                }
            }
        }
        (ShapeProjection::Optional(ty_sub), ShapeProjection::Required(ty_super)) => {
            let r_field_sub = get_reason(&env::update_reason(env, ty_sub, |r_sub_prj| {
                reason::prj_shape(
                    r_sub.clone(),
                    r_sub_prj,
                    r_super.clone(),
                    printable_name.clone(),
                    FieldKind::Optional,
                    FieldKind::Required,
                )
            }))
            .clone();
            let r_field_super = get_reason(&ty_super).clone();
            let ty_err_opt = subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Required_field_is_optional {
                        pos: reason::to_pos(r_sub),
                        decl_pos: reason::to_pos(r_super),
                        name: printable_name.clone(),
                        def_pos: get_pos(&ty_super),
                        reason_sub: r_field_sub,
                        reason_super: r_field_super,
                    },
                    on_error,
                )
            });

            Err(ty_err_opt)
        }
        (ShapeProjection::Absent, ShapeProjection::Required(ty_super)) => {
            let quickfixes_opt = match reason::predicates::unpack_shape_literal_opt(r_sub) {
                Some(p) => {
                    let fix_pos =
                        crate::pos::shrink_to_end(&crate::pos::shrink_by_one_char_both_sides(&p));
                    Some(vec![quickfix::make_eager_default_hint_style(
                        "Add field ".to_string() + &markdown_lite::md_codify(&printable_name),
                        format!(", '{}' => TODO", *printable_name),
                        fix_pos,
                    )])
                }
                None => None,
            };
            let r_field_sub = {
                let r_sub_prj = reason::missing_field();
                reason::prj_shape(
                    r_sub.clone(),
                    r_sub_prj,
                    r_super.clone(),
                    printable_name.clone(),
                    FieldKind::Absent,
                    FieldKind::Required,
                )
            };
            let r_field_super = get_reason(&ty_super).clone();
            let ty_err_opt = subtype_env.on_error.clone().map(|on_error| {
                // `Option.value_map ~default:on_error ~f:(Reasons_callback.add_quickfixes on_error) quickfixes_opt`
                let on_error = match quickfixes_opt {
                    None => on_error,
                    Some(qfxs) => reasons_callback::add_quickfixes(on_error, qfxs),
                };
                typing_error::apply_reasons(
                    secondary::T::Missing_field {
                        decl_pos: field_pos.clone(),
                        pos: reason::to_pos(r_sub),
                        name: printable_name.clone(),
                        reason_sub: r_field_sub,
                        reason_super: r_field_super,
                    },
                    on_error,
                )
            });

            Err(ty_err_opt)
        }
    };

    match res {
        Ok(None) => Ok(Box::new(|env: &mut Env| valid(env))),
        Ok(Some(((kind_sub, ty_sub), (kind_super, ty_super)))) => {
            // (`printable_name` is used by the error cases only: it is not
            // built yet, so it is built here, and not copied.)
            let ty_sub = env::update_reason(env, ty_sub, |r_sub_prj| {
                reason::prj_shape(
                    r_sub.clone(),
                    r_sub_prj,
                    r_super.clone(),
                    printable_shape_field_name(field_name),
                    kind_sub,
                    kind_super,
                )
            });
            // [on_type_mismatch] replaces the message for the type obligation only.
            // The requiredness errors above are already phrased in the user's terms
            // and must keep their own wording.
            // (Borrowed when it is the one given: the closure is applied
            // where `subtype_env` lives.)
            let subtype_env = match on_type_mismatch {
                None => std::borrow::Cow::Borrowed(subtype_env),
                Some(on_error) => std::borrow::Cow::Owned(subtype_env::map_on_error(
                    subtype_env.clone(),
                    |_| on_error,
                )),
            };
            Ok(Box::new(simplify_subtype_shape_type(
                subtype_env,
                this_ty,
                super_like,
                env,
                supportdyn_sub,
                r_sub,
                ty_sub,
                ty_super,
            )))
        }
        Err(err) => Err(err),
    }
}

/// The OCaml returns `simplify ~subtype_env ~this_ty ~lhs ~rhs`, waiting for
/// the environment: here a closure that owns what it needs (it does not
/// borrow `env`, which only likens the supertype).
#[allow(clippy::too_many_arguments)]
pub(crate) fn simplify_subtype_shape_type<'a>(
    subtype_env: std::borrow::Cow<'a, subtype_env::T>,
    this_ty: Option<&'a Ty>,
    super_like: bool,
    env: &Env,
    supportdyn_sub: bool,
    r_sub: &Reason,
    ty_sub: Ty,
    ty_super: Ty,
) -> impl FnOnce(&mut Env) -> tl::SubtypeProp + use<'a> {
    let ty_super = sd::liken(super_like, env, ty_super);
    let sub_supportdyn = if supportdyn_sub {
        Some(r_sub.clone())
    } else {
        None
    };
    move |env: &mut Env| {
        let lhs = Lhs {
            sub_supportdyn: sub_supportdyn.as_ref(),
            ty_sub: &ty_sub,
        };
        let rhs = Rhs {
            super_like: false,
            super_supportdyn: false,
            ty_super: &ty_super,
        };
        simplify(&subtype_env, this_ty, lhs, rhs, env)
    }
}

pub(crate) fn shape_projection_type(supportdyn: bool, env: &Env, r: &Reason, ty: Ty) -> Ty {
    if supportdyn
        && !subtype_ask::is_sub_type_for_union_i(
            env,
            None,
            &InternalType::LoclType(ty.clone()),
            &InternalType::LoclType(make_type::supportdyn_mixed(r.clone())),
        )
    {
        make_type::supportdyn(r.clone(), ty)
    } else {
        ty
    }
}

/// Shape projection for shape type `s` and field `f` (`s |_ f`) is defined as:
///  - if `f` appears in `s` as `f => ty` then `s |_ f` = `Required ty`
///  - if `f` appears in `s` as `?f => ty` then `s |_ f` = `Optional ty`
///  - if `f` does not appear in `s` and `s` is closed, then `s |_ f` = `Absent`
///  - if `f` does not appear in `s` and `s` is open, then `s |_ f` = `Optional mixed`
///
///  EXCEPT
///  - `?f => nothing` should be ignored, and treated as `Absent`.
///    Such a field cannot be given a value, and so is effectively not present.
pub(crate) fn shape_projection(
    supportdyn: bool,
    env: &Env,
    field_name: &TShapeField,
    shape_kind: &Ty,
    shape_map: &TShapeMap<ShapeFieldType>,
    r: &Reason,
) -> ShapeProjection {
    shape_projection_of_found(supportdyn, env, field_name, shape_kind, shape_map.get(field_name), r)
}

/// [`shape_projection`], given what the shape map has for `field_name`.
fn shape_projection_of_found(
    supportdyn: bool,
    env: &Env,
    field_name: &TShapeField,
    shape_kind: &Ty,
    found: Option<&ShapeFieldType>,
    r: &Reason,
) -> ShapeProjection {
    let make_supportdyn = |ty: Ty| shape_projection_type(supportdyn, env, r, ty);
    match found {
        Some(ShapeFieldType {
            ty: sft_ty,
            optional: sft_optional,
        }) => match (get_node(sft_ty), *sft_optional) {
            (Ty_::Tunion(tyl), true) if tyl.is_empty() => ShapeProjection::Absent,
            (_, true) => ShapeProjection::Optional(make_supportdyn(sft_ty.clone())),
            (_, false) => ShapeProjection::Required(make_supportdyn(sft_ty.clone())),
        },
        None => {
            if t_utils::is_nothing(env, shape_kind) {
                ShapeProjection::Absent
            } else {
                let printable_name = printable_shape_field_name(field_name);
                let ty = typing_defs_core::with_reason(
                    shape_kind.clone(),
                    reason::missing_optional_field((reason::to_pos(r), printable_name)),
                );
                ShapeProjection::Optional(make_supportdyn(ty))
            }
        }
    }
}

// == Entry point ===========================================================

pub fn simplify(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    lhs: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    if log::should_log(env, subtype_env, &lhs, &rhs) {
        // `Log.log` prints `lhs` and `rhs`, which the continuation consumes:
        // it is given copies.
        let (log_lhs, log_rhs) = (lhs.clone(), rhs.clone());
        log::log(env, subtype_env, this_ty, &log_lhs, &log_rhs, |env| {
            simplify_(subtype_env, this_ty, lhs, rhs, env)
        })
    } else {
        // This path should be fast, so we make sure not to create a closure unlike the other path.
        simplify_(subtype_env, this_ty, lhs, rhs, env)
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Arc;

    use oxidized::ast_defs::Tprim;
    use oxidized::typing_defs_core::PosByteString;
    use oxidized::typing_defs_core::TshapeFieldName;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn env() -> Env {
        let ctx = crate::ctx::Ctx::new(Path::new("/"), Default::default()).unwrap();
        let file = Arc::new(RelativePath::make(Prefix::Root, "f.php".into()));
        crate::typing_env_types::empty(None, None, Arc::new(ctx), file, None)
    }

    fn prim(p: Tprim) -> Ty {
        mk((reason::none(), Ty_::Tprim(p)))
    }

    fn lit(name: &str) -> TShapeField {
        TShapeField(TshapeFieldName::TSFlitStr(PosByteString(
            PosOrDecl::NONE,
            name.into(),
        )))
    }

    fn subtype_env_with(on_error: Option<reasons_callback::T>) -> subtype_env::T {
        subtype_env::create(
            None, None, None, None, None, None, None, None, None, None, false, 2, on_error,
        )
    }

    #[test]
    fn phys_equal_shape_field_type_() {
        // `?int`: a node with a component (the nodes of `mk` without
        // components, such as `int`, are shared, so two of them with the same
        // reason are the same node).
        let opt_int = || mk((reason::none(), Ty_::Toption(prim(Tprim::Tint))));
        let f = ShapeFieldType {
            optional: false,
            ty: opt_int(),
        };
        // A copy of the record shares the type's node.
        assert!(phys_equal_shape_field_type(&f, &f.clone()));
        // An equal type built separately is another value.
        assert!(!phys_equal_shape_field_type(
            &f,
            &ShapeFieldType {
                optional: false,
                ty: opt_int(),
            }
        ));
        assert!(!phys_equal_shape_field_type(
            &f,
            &ShapeFieldType {
                optional: true,
                ty: f.ty.clone(),
            }
        ));
    }

    #[test]
    fn shape_projection_of_known_fields() {
        let env = env();
        let int = prim(Tprim::Tint);
        let mut fields: TShapeMap<ShapeFieldType> = TShapeMap::new();
        fields.insert(
            lit("a"),
            ShapeFieldType {
                optional: false,
                ty: int.clone(),
            },
        );
        fields.insert(
            lit("b"),
            ShapeFieldType {
                optional: true,
                ty: int.clone(),
            },
        );
        fields.insert(
            lit("c"),
            ShapeFieldType {
                optional: true,
                ty: make_type::nothing(reason::none()),
            },
        );
        fields.insert(
            lit("d"),
            ShapeFieldType {
                optional: false,
                ty: make_type::nothing(reason::none()),
            },
        );
        let kind = make_type::mixed(reason::none());
        let proj =
            |name: &str| shape_projection(false, &env, &lit(name), &kind, &fields, &reason::none());
        // Without supportdyn, the field's own type (the same value).
        assert!(
            matches!(proj("a"), ShapeProjection::Required(ty) if typing_defs_core::phys_equal(&ty, &int))
        );
        assert!(
            matches!(proj("b"), ShapeProjection::Optional(ty) if typing_defs_core::phys_equal(&ty, &int))
        );
        // `?c => nothing` is absent; `d => nothing` is required.
        assert!(matches!(proj("c"), ShapeProjection::Absent));
        assert!(matches!(proj("d"), ShapeProjection::Required(ty) if typing_defs::is_nothing(&ty)));
    }

    #[test]
    fn shape_projection_requiredness_errors() {
        let env = env();
        let int = prim(Tprim::Tint);
        let field = lit("f");
        let with_error = subtype_env_with(Some(reasons_callback::unify_error_at(Pos::NONE)));
        let without_error = subtype_env_with(None);
        // The continuation borrows the subtype environment it is given: the
        // bound makes the closure generic over that borrow.
        fn generic_over_env<F>(f: F) -> F
        where
            F: for<'s> Fn(
                &'s subtype_env::T,
                ShapeProjection,
                ShapeProjection,
            ) -> Result<PropK<'s>, Option<typing_error::T>>,
        {
            f
        }
        let project = generic_over_env(|subtype_env, sub, sup| {
            simplify_subtype_shape_projection(
                None,
                subtype_env,
                None,
                false,
                &env,
                (false, &reason::none(), sub),
                (false, &reason::none(), sup),
                &field,
            )
        });
        // Absent <: Absent and Absent <: Optional hold.
        let mut env_ = env.clone();
        match project(
            &with_error,
            ShapeProjection::Absent,
            ShapeProjection::Absent,
        ) {
            Ok(k) => assert!(tl::is_valid(&k(&mut env_))),
            Err(_) => panic!("Absent <: Absent"),
        }
        match project(
            &with_error,
            ShapeProjection::Absent,
            ShapeProjection::Optional(int.clone()),
        ) {
            Ok(k) => assert!(tl::is_valid(&k(&mut env_))),
            Err(_) => panic!("Absent <: Optional"),
        }
        // Required </: Absent, Optional </: Required, Absent </: Required,
        // Optional int </: Absent: an error when there is a callback.
        for (sub, sup) in [
            (
                ShapeProjection::Required(int.clone()),
                ShapeProjection::Absent,
            ),
            (
                ShapeProjection::Optional(int.clone()),
                ShapeProjection::Required(int.clone()),
            ),
            (
                ShapeProjection::Absent,
                ShapeProjection::Required(int.clone()),
            ),
            (
                ShapeProjection::Optional(int.clone()),
                ShapeProjection::Absent,
            ),
        ] {
            assert!(matches!(
                project(&with_error, sub.clone(), sup.clone()),
                Err(Some(_))
            ));
            assert!(matches!(project(&without_error, sub, sup), Err(None)));
        }
    }

    #[test]
    fn variance_loop_without_arguments() {
        let mut env = env();
        let subtype_env = subtype_env_with(None);
        // No variance, no argument: nothing to check.
        let p = simplify_subtype_variance_for_injective_loop(
            &subtype_env,
            None,
            false,
            "\\C",
            reason::CtorKind::CtorClass,
            0,
            &[],
            (reason::none(), &[prim(Tprim::Tint)]),
            (reason::none(), &[prim(Tprim::Tint)]),
            &mut env,
        );
        assert!(tl::is_valid(&p));
        let p = simplify_subtype_variance_for_injective_loop(
            &subtype_env,
            None,
            false,
            "\\C",
            reason::CtorKind::CtorClass,
            0,
            &[(Variance::Covariant, ReifyKind::Erased)],
            (reason::none(), &[]),
            (reason::none(), &[prim(Tprim::Tint)]),
            &mut env,
        );
        assert!(tl::is_valid(&p));
    }
}
