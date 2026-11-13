// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_enum.ml`. See `hh/PORTING.md`.
//!
//! Module used to enforce that Enum subclasses are used reasonably.
//! Exports the Enum type as the type of all constants, checks that constants
//! have the proper type, and restricts what types can be used for enums.

use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::BPos;
use pos::Positioned;
use pos::TypeName;
use ty::decl::Typeconst;

use crate::ast_defs;
use crate::decl_entry;
use crate::decl_enum;
use crate::folded_class as cls;
use crate::naming_special_names as sn;
use crate::pos_or_decl;
use crate::type_expansions;
use crate::typing_defs::ClassElt;
use crate::typing_defs::TypedefTypeAssignment;
use crate::typing_defs::get_ce_xhp_attr;
use crate::typing_defs::is_dynamic;
use crate::typing_defs::is_nothing;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DeclTy_;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_make_type as make_type;
use crate::typing_ops;
use crate::typing_phase as phase;
use crate::typing_print;
use crate::typing_reason as reason;
use crate::typing_reason::Ureason;
use crate::typing_utils;

/// `(Cls.pos tc, Cls.name tc)`, as `Decl_enum.enum_kind` takes it.
fn cls_pos_id(tc: &cls::T) -> Positioned<TypeName, BPos> {
    Positioned::new(BPos::from(cls::pos(tc)), TypeName::new(cls::name(tc)))
}

/// `Option.(Typing_env.get_typeconst env tc Naming_special_names.FB.tInner >>= ...)`
fn tinner(env: &Env, tc: &cls::T) -> Option<DeclTy> {
    match typing_env::get_typeconst(env, tc, sn::fb::INNER) {
        None => None,
        Some(t) =>
        // TODO(T88552052) This code was taking the default of abstract
        // type constants as a value
        {
            match t.kind {
                Typeconst::TCConcrete(c) => Some(c.ty),
                Typeconst::TCAbstract(a) => match a.default {
                    Some(t) => Some(t),
                    None => None,
                },
            }
        }
    }
}

pub fn member_type(env: &Env, member_ce: &ClassElt) -> DeclTy {
    let default_result: DeclTy = (*member_ce.ce_type).clone();
    if get_ce_xhp_attr(member_ce).is_none() {
        default_result
    } else {
        let (stripped_ty, has_like) = match default_result.node_ref() {
            DeclTy_::Tlike(ty) => (ty.clone(), true),
            _ => (default_result.clone(), false),
        };
        match stripped_ty.node_ref() {
            DeclTy_::Tapply(id_and_args) => {
                let enum_id = &id_and_args.0;
                // XHP attribute type transform is necessary to account for
                // non-first class Enums:
                //
                // attribute MyEnum x; // declaration: MyEnum
                // $this->:x;          // usage: MyEnumType
                let maybe_enum = typing_env::get_class(env, enum_id.id_ref().as_str());
                match maybe_enum {
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => default_result,
                    decl_entry::T::Found(tc) => {
                        // The arguments, from the last to the first.
                        let inner = tinner(env, &tc);
                        let enum_type = cls::enum_type(&tc);
                        let name = cls_pos_id(&tc);
                        match decl_enum::enum_kind(
                            &name,
                            ast_defs::is_c_enum_class(cls::kind(&tc)),
                            false,
                            enum_type.as_ref(),
                            inner.as_ref(),
                            |ancestor| cls::get_ancestor(&tc, ancestor),
                        ) {
                            None => default_result,
                            Some(decl_enum::T {
                                base: _,
                                type_: enum_ty,
                                constraint_: _,
                                interface: _,
                            }) => {
                                let ty = DeclTy::new(
                                    default_result.reason().clone(),
                                    enum_ty.node_ref().clone(),
                                );
                                if has_like {
                                    DeclTy::new(default_result.reason().clone(), DeclTy_::Tlike(ty))
                                } else {
                                    ty
                                }
                            }
                        }
                    }
                }
            }
            _ => default_result,
        }
    }
}

fn enum_check_const(
    ty_exp: &Ty,
    env: &mut Env,
    cc: &nast::ClassConst,
    t: &Ty,
) -> Option<typing_error::T> {
    if typing_utils::is_tyvar_error(env, ty_exp) || typing_utils::is_tyvar_error(env, t) {
        None
    } else {
        let p = cc.id.0.clone();
        typing_ops::sub_type(
            p,
            Ureason::URenum,
            env,
            t.clone(),
            ty_exp.clone(),
            callback::constant_does_not_match_enum_type(),
        )
    }
}

/// Enforcement of case types for enum/enum classes is wonky.
/// Forbid for now until we can more thoroughly audit the behavior
fn check_if_case_type(env: &Env, pos: &PosOrDecl, ty: &Ty) {
    match get_node(ty) {
        Ty_::Tnewtype(name, _, _) => match typing_env::get_typedef(env, name) {
            decl_entry::T::Found(td)
                if matches!(td.type_assignment, TypedefTypeAssignment::CaseType(..)) =>
            {
                let ty_name = {
                    let env = env.clone();
                    let ty = ty.clone();
                    Lazy::new(move || typing_print::full_strip_ns(true, &env, &ty))
                };
                typing_error_utils::add_typing_error(
                    &typing_error::enum_(primary::enum_::T::Enum_type_bad_case_type {
                        pos: pos_or_decl::unsafe_to_raw_pos(pos.clone()),
                        ty_name,
                        case_type_decl_pos: PosOrDecl::from(td.pos.clone()),
                    }),
                    env,
                )
            }
            _ => {}
        },
        _ => {}
    }
}

fn is_valid_base(env: &Env, pos: &PosOrDecl, ty: &Ty) -> bool {
    typing_utils::is_tyvar_error(env, ty)
        || match get_node(ty) {
            Ty_::Tprim(_) | Ty_::Tnonnull => true,
            Ty_::Toption(lty) => is_valid_base(env, pos, lty),
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: TupleExtra::Tvariadic(t_variadic),
            }) => {
                t_required.iter().all(|t| is_valid_base(env, pos, t))
                    && t_optional.iter().all(|t| is_valid_base(env, pos, t))
                    && is_nothing(t_variadic)
            }
            Ty_::Ttuple(TupleType {
                extra: TupleExtra::Tsplat(_),
                ..
            }) => false,
            Ty_::Tnewtype(_, ltys, lty) => {
                check_if_case_type(env, pos, ty);
                std::iter::once(lty)
                    .chain(ltys.iter())
                    .all(|t| is_valid_base(env, pos, t))
            }
            Ty_::Tclass(_, _, ltys) => ltys.iter().all(|t| is_valid_base(env, pos, t)),
            Ty_::Tunion(tyl) if tyl.len() == 2 && is_dynamic(&tyl[0]) => {
                is_valid_base(env, pos, &tyl[1])
            }
            Ty_::Tunion(tyl) if tyl.len() == 2 && is_dynamic(&tyl[1]) => {
                is_valid_base(env, pos, &tyl[0])
            }
            // `TShapeMap.for_all`: OCaml's `Map.for_all` visits the root of
            // the tree first, then its left and right subtrees, where this
            // visits the fields in key order. The tree is not known here; the
            // result is the same, but when a field is not valid, which other
            // fields have been visited (and reported `check_if_case_type`
            // errors) first can differ.
            Ty_::Tshape(ShapeType::ShapeSimple(s)) => s
                .fields
                .values()
                .all(|sfty| is_valid_base(env, pos, &sfty.ty)),
            Ty_::Tshape(ShapeType::ShapeSplat(_)) => false,
            Ty_::Tany(_)
            | Ty_::Tdynamic(_)
            | Ty_::Tfun(_)
            | Ty_::Tvar(_)
            | Ty_::Tgeneric(_)
            | Ty_::Tunion(_)
            | Ty_::Tintersection(_)
            | Ty_::TvecOrDict(..)
            | Ty_::Taccess(_)
            | Ty_::Tdependent(..)
            | Ty_::Tlabel(_)
            | Ty_::Tneg(_) => false,
            Ty_::TclassPtr(_) => true,
        }
}

/// Check that the `as` bound or the underlying type of an enum is a subtype of
/// arraykey. For enum class, check that it is a denotable closed type:
/// no free type parameters are allowed, and we also prevent uncertain cases,
/// like any, or dynamic. The free status of type parameter is caught during
/// naming (Unbound name), so we only check the kind of type that is used.
fn enum_class_check_type(
    env: &mut Env,
    pos: &PosOrDecl,
    ur: Ureason,
    ty_interface: Option<&Ty>,
    ty: &Ty,
    _on_error: callback::T,
) {
    let ty_arraykey = make_type::arraykey(reason::implicit_upper_bound((
        pos.clone(),
        "arraykey".to_string(),
    )));
    let ty_err_opt = match ty_interface {
        Some(interface) => {
            if !is_valid_base(env, pos, interface) {
                let ty_name = {
                    let env = env.clone();
                    let interface = interface.clone();
                    Lazy::new(move || typing_print::full_strip_ns(true, &env, &interface))
                };
                typing_error_utils::add_typing_error(
                    &typing_error::enum_(primary::enum_::T::Enum_type_bad {
                        pos: pos_or_decl::unsafe_to_raw_pos(pos.clone()),
                        is_enum_class: true,
                        ty_name,
                        trail: vec![],
                    }),
                    env,
                )
            }
            None
        }
        None => {
            check_if_case_type(env, pos, ty);
            let callback = {
                let ty_name = {
                    let env = env.clone();
                    let ty = ty.clone();
                    Lazy::new(move || typing_print::full_strip_ns(true, &env, &ty))
                };
                callback::always(primary::T::Enum(primary::enum_::T::Enum_type_bad {
                    pos: pos_or_decl::unsafe_to_raw_pos(pos.clone()),
                    is_enum_class: false,
                    ty_name,
                    trail: vec![],
                }))
            };
            typing_ops::sub_type(
                pos_or_decl::unsafe_to_raw_pos(pos.clone()),
                ur,
                env,
                ty.clone(),
                ty_arraykey,
                callback,
            )
        }
    };
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
}

/// The environment that localization returns is dropped: the cycles are
/// reported with it, on a copy.
fn check_cyclic_constraint(env: &Env, (p, enum_name): (&Pos, String), constraint_ty: &DeclTy) {
    let mut env = env.clone();
    let env = &mut env;
    let (_ty_err1, cycles, _) = phase::localize_no_subst_report_cycles(
        env,
        false,
        (p.clone(), type_expansions::expandable::T::Enum(enum_name)),
        constraint_ty,
    );
    if let Some(err) = &type_expansions::report(&cycles) {
        typing_error_utils::add_typing_error(err, env)
    }
}

/// Check an enum declaration of the form
///
///    enum class E : <ty_exp>
///
/// Also that each type constant is of type `ty_exp`.
pub fn enum_class_check(
    env: &mut Env,
    name_pos: &Pos,
    tc: &cls::T,
    consts: &[nast::ClassConst],
    const_types: &[Ty],
) {
    let pos = cls::pos(tc);
    let add_like =
        typing_env::get_support_dynamic_type(env) && typing_env::get_tcopt(env).po.everything_sdt;
    let enum_info_opt: Option<decl_enum::T> = {
        // The arguments, from the last to the first.
        let inner = tinner(env, tc);
        let enum_type = cls::enum_type(tc);
        let name = cls_pos_id(tc);
        decl_enum::enum_kind(
            &name,
            ast_defs::is_c_enum_class(cls::kind(tc)),
            add_like,
            enum_type.as_ref(),
            inner.as_ref(),
            |ancestor| cls::get_ancestor(tc, ancestor),
        )
    };
    let ty_err_opt = match enum_info_opt {
        Some(decl_enum::T {
            base: ty_exp,
            type_: _,
            constraint_: ty_constraint,
            interface: ty_interface,
        }) => {
            let (ty_err1, ty_exp) = phase::localize_no_subst(env, false, &ty_exp);
            if let Some(err) = &ty_err1 {
                typing_error_utils::add_typing_error(err, env)
            }
            let (ty_err2, ty_interface) = match &ty_interface {
                Some(dty) => {
                    let (ty_err, lty) = phase::localize_no_subst(env, false, dty);
                    (ty_err, Some(lty))
                }
                None => (None, None),
            };
            if let Some(err) = &ty_err2 {
                typing_error_utils::add_typing_error(err, env)
            }
            // Check that ty_exp <: arraykey
            enum_class_check_type(
                env,
                &pos,
                Ureason::URenumUnderlying,
                ty_interface.as_ref(),
                &ty_exp,
                callback::enum_underlying_type_must_be_arraykey(),
            );
            // Check that ty_exp <: ty_constraint <: arraykey
            let ty_err_opt = match &ty_constraint {
                None => None,
                Some(ty) => {
                    check_cyclic_constraint(env, (name_pos, cls::name(tc)), ty);
                    let (ty_err1, ty) = phase::localize_no_subst(env, false, ty);
                    if let Some(err) = &ty_err1 {
                        typing_error_utils::add_typing_error(err, env)
                    }
                    enum_class_check_type(
                        env,
                        &pos,
                        Ureason::URenumCstr,
                        None, // Enum classes do not have constraints
                        &ty,
                        callback::enum_constraint_must_be_arraykey(),
                    );
                    typing_ops::sub_type(
                        pos_or_decl::unsafe_to_raw_pos(pos.clone()),
                        Ureason::URenumIncompatibleCstr,
                        env,
                        ty_exp.clone(),
                        ty,
                        callback::enum_subtype_must_have_compatible_constraint(),
                    )
                }
            };
            // `List.fold2_exn`, consing the errors onto `Option.to_list ty_err_opt`:
            // the list is in the reverse order of the constants, the error of the
            // constraint last.
            if consts.len() != const_types.len() {
                panic!(
                    "Invalid_argument(\"length mismatch in fold2_exn: {} <> {}\")",
                    consts.len(),
                    const_types.len()
                )
            }
            let mut ty_errs: Vec<typing_error::T> = ty_err_opt.into_iter().collect();
            for (c, cty) in consts.iter().zip(const_types.iter()) {
                match enum_check_const(&ty_exp, env, c, cty) {
                    Some(ty_err) => ty_errs.push(ty_err),
                    None => {}
                }
            }
            ty_errs.reverse();
            typing_error::multiple_opt(ty_errs)
        }
        None => None,
    };
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
}
