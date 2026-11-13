// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_structure.ml`. See `hh/PORTING.md`.
//!
//! This module implements the typing for type_structure.
//!
//! `make_ts` builds the declared type `TypeStructure<T>` (a `hackrs` type,
//! `crate::typing_defs_core::DeclTy`) and localizes it with `T` substituted.
//! `Decl_subst.make_locl` is `crate::typing_phase::decl_subst_make_locl`
//! (`crate::decl_subst::make_locl` maps to `oxidized` types, which have the
//! declared phase only).

use naming_special_names_rust as sn;
use oxidized::pos::Pos;
use pos::BPos;
use pos::Positioned;
use pos::TypeName;
use ty::decl::Ty_ as DeclTy_;
use ty::reason::Reason as _;

use crate::ctx::R;
use crate::decl_entry;
use crate::pos_or_decl;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::empty_expand_env_with_on_error;
use crate::typing_defs::is_nothing;
use crate::typing_defs::shape_field_map;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::PosByteString;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_map;
use crate::typing_defs_core::with_reason;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_make_type as make_type;
use crate::typing_phase;
use crate::typing_reason;
use crate::typing_solver;
use crate::typing_utils;

/// `TShapeMap.t` of shape field types
type ShapeMap = t_shape_map::T<ShapeFieldType>;

fn make_ts(env: &mut Env, ty: Ty) -> Ty {
    let r = get_reason(&ty).clone();
    match typing_env::get_typedef(env, sn::fb::TYPE_STRUCTURE) {
        decl_entry::T::Found(td) => {
            // Typedef parameters can not have constraints
            let params: Vec<DeclTy> = td
                .tparams
                .iter()
                .map(|tp| {
                    DeclTy::new(
                        R::witness_from_decl(tp.name.pos().clone()),
                        DeclTy_::Tgeneric(tp.name.id()),
                    )
                })
                .collect();
            let ts = DeclTy::apply(
                R::none(),
                Positioned::new(
                    BPos::from(&pos_or_decl::none),
                    TypeName::new(sn::fb::TYPE_STRUCTURE),
                ),
                params.into_boxed_slice(),
            );
            let ety_env = ExpandEnv {
                substs: typing_phase::decl_subst_make_locl(&td.tparams[..], &[ty]),
                ..empty_expand_env_with_on_error(reasons_callback::invalid_type_hint(
                    pos_or_decl::unsafe_to_raw_pos(typing_reason::to_pos(&r)),
                ))
            };
            let (ty_err, ty) = typing_phase::localize(&ety_env, env, &ts);
            let ty = with_reason(ty, r);
            if let Some(ty_err) = ty_err {
                typing_error_utils::add_typing_error(&ty_err, env)
            }
            ty
        }
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
            // Should not hit this because TypeStructure should always be defined
            make_type::dynamic(r)
        }
    }
}

/// Does this type contain only enum or object instances?
/// These are the types that can be represented using classname
pub fn is_enum_or_classish(env: &Env, ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tnewtype(cid, _, _) if typing_env::is_enum(env, cid) => true,
        Ty_::Tintersection(tys) => tys.iter().any(|ty| is_enum_or_classish(env, ty)),
        Ty_::Tunion(tys) => tys.iter().all(|ty| is_enum_or_classish(env, ty)),
        Ty_::Tclass((_, x), _, _)
            if !(x == sn::collections::VEC
                || x == sn::collections::DICT
                || x == sn::collections::KEYSET) =>
        {
            true
        }
        Ty_::Tgeneric(_) => {
            // `let (_env, tyl) = ...`: the environment is dropped.
            let tyl = typing_utils::get_concrete_supertypes(
                None,
                Some(true), // expand_supportdyn
                None,
                false, // abstract_enum
                &mut env.clone(),
                ty.clone(),
            );
            tyl.iter().any(|ty| is_enum_or_classish(env, ty))
        }
        _ => false,
    }
}

/// Whether the field is the string literal `name` (`TSFlit_str (_, name)`).
fn is_lit_str(field: &t_shape_map::Key, name: &str) -> bool {
    match &field.0 {
        TshapeFieldName::TSFlitStr(PosByteString(_, s)) => s == name,
        TshapeFieldName::TSFregexGroup(_) | TshapeFieldName::TSFclassConst(_, _) => false,
    }
}

pub fn transform_shapemap(
    nullable: Option<bool>,
    env: &mut Env,
    pos: Pos,
    ty: Ty,
    shape: ShapeMap,
) -> ShapeMap {
    let nullable = nullable.unwrap_or(false);
    let (ty_err_opt, ty) =
        typing_solver::expand_type_and_solve(env, None, "a shape", pos.clone(), ty);
    if let Some(ty_err) = ty_err_opt {
        typing_error_utils::add_typing_error(&ty_err, env)
    }
    let ty = typing_env::expand_type(env, ty);
    match get_node(&ty) {
        Ty_::Toption(ty) => {
            let ty = ty.clone();
            transform_shapemap(Some(true), env, pos, ty, shape)
        }
        _ => {
            let base_type = typing_utils::get_base_type(None, env, ty.clone());
            // If the abstract type is unbounded we do not specialize at all
            let is_unbound = matches!(get_node(&base_type), Ty_::Tgeneric(_));
            let is_generic = matches!(get_node(&ty), Ty_::Tgeneric(_));
            let (supportdyn, ty) = typing_utils::strip_supportdyn(env, ty);
            let base_type = typing_utils::get_base_type(Some(false), env, ty.clone());
            let (supportdyn_bound, base_type) = typing_utils::strip_supportdyn(env, base_type);
            let base_type = if is_unbound {
                make_type::mixed(get_reason(&base_type).clone())
            } else {
                base_type
            };
            // Does this type contain only enum or object instances?
            // These are the types that can be represented using classname
            // (The OCaml closure captures the environment of this point.)
            let env_of_is_enum_or_classish = env.clone();
            let is_enum_or_classish = |ty: &Ty| is_enum_or_classish(&env_of_is_enum_or_classish, ty);
            let supportdyn = supportdyn || supportdyn_bound;
            // `TShapeMap.fold transform_shape_field shape (env, TShapeMap.empty)`
            let mut acc = ShapeMap::new();
            for (field, sft) in shape {
                transform_shape_field(
                    env,
                    nullable,
                    &ty,
                    &base_type,
                    is_generic,
                    supportdyn,
                    &is_enum_or_classish,
                    field,
                    sft,
                    &mut acc,
                );
            }
            acc
        }
    }
}

/// `transform_shape_field field { sft_ty; sft_optional } (env, shape)` of
/// `transform_shapemap`, with the variables it closes over as arguments.
fn transform_shape_field(
    env: &mut Env,
    nullable: bool,
    ty: &Ty,
    base_type: &Ty,
    is_generic: bool,
    supportdyn: bool,
    is_enum_or_classish: &dyn Fn(&Ty) -> bool,
    field: t_shape_map::Key,
    sft: ShapeFieldType,
    shape: &mut ShapeMap,
) {
    let ShapeFieldType {
        ty: sft_ty,
        optional: sft_optional,
    } = sft;
    // Accumulates the provided type for this iteration of the fold, adding
    // it to the accumulation ShapeMap for the current field. Since the
    // field must have been explicitly set, we set sft_optional to false.
    // (Each field is added once to a map that starts empty.)
    let acc_field_with_type = |shape: &mut ShapeMap, field: t_shape_map::Key, sft_ty: Ty| {
        shape.insert(
            field,
            ShapeFieldType {
                optional: false,
                ty: sft_ty,
            },
        );
    };
    let sft_ty = typing_env::expand_type(env, sft_ty);
    let r = get_reason(base_type).clone();
    match (get_node(&sft_ty), get_node(base_type)) {
        (Ty_::Toption(fty), _) if is_lit_str(&field, "nullable") && nullable => {
            acc_field_with_type(shape, field, fty.clone())
        }
        (Ty_::Toption(fty), Ty_::Toption(_)) if is_lit_str(&field, "nullable") => {
            acc_field_with_type(shape, field, fty.clone())
        }
        (Ty_::Toption(fty), _) if is_lit_str(&field, "classname") && is_enum_or_classish(ty) => {
            acc_field_with_type(shape, field, fty.clone())
        }
        // Required elements in a tuple type
        (
            _,
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: _,
                extra: _,
            }),
        ) if is_lit_str(&field, "elem_types") => {
            let t_required: Vec<Ty> = t_required
                .iter()
                .map(|ty| make_ts(env, ty.clone()))
                .collect();
            acc_field_with_type(shape, field, make_type::tuple(r, t_required))
        }
        // Optional elements in a tuple type
        (
            _,
            Ty_::Ttuple(TupleType {
                required: _,
                optional: t_optional,
                extra: TupleExtra::Tvariadic(_),
            }),
        ) if is_lit_str(&field, "optional_elem_types") && !t_optional.is_empty() => {
            let t_optional: Vec<Ty> = t_optional
                .iter()
                .map(|ty| make_ts(env, ty.clone()))
                .collect();
            acc_field_with_type(shape, field, make_type::tuple(r, t_optional))
        }
        (
            _,
            Ty_::Ttuple(TupleType {
                required: _,
                optional: _,
                extra: TupleExtra::Tvariadic(t_variadic),
            }),
        ) if is_lit_str(&field, "variadic_type") && !is_nothing(t_variadic) => {
            let t_variadic = make_ts(env, t_variadic.clone());
            acc_field_with_type(shape, field, t_variadic)
        }
        (_, Ty_::Tfun(funty)) if is_lit_str(&field, "param_types") => {
            let tyl: Vec<Ty> = funty.params.iter().map(|x| x.type_.clone()).collect();
            let tyl: Vec<Ty> = tyl.into_iter().map(|ty| make_ts(env, ty)).collect();
            acc_field_with_type(shape, field, make_type::tuple(r, tyl))
        }
        (_, Ty_::Tfun(funty)) if is_lit_str(&field, "return_type") => {
            let ty = make_ts(env, funty.ret.clone());
            acc_field_with_type(shape, field, make_type::tuple(r, vec![ty]))
        }
        (
            _,
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value: shape_kind,
                fields,
            })),
        ) if is_lit_str(&field, "fields") => {
            let fields = shape_field_map::map_env(|env, ty| make_ts(env, ty), env, fields.clone());
            let ty = mk((
                r.clone(),
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: TypeOrigin::MissingOrigin,
                    unknown_value: shape_kind.clone(),
                    fields,
                })),
            ));
            let ty = if supportdyn {
                make_type::supportdyn(r, ty)
            } else {
                ty
            };
            acc_field_with_type(shape, field, ty)
        }
        // For generics we cannot specialize the generic_types field. Consider:
        //
        //  class C<T> {}
        //  class D extends C<int> {}
        //
        //  function test<T as C<int>>(TypeStructure<T> $ts): TypeStructure<int> {
        //    return $ts['generic_types'][0];
        //  }
        //
        // For test(TypeStructure<D>) there will not be a generic_types field
        (_, _) if is_lit_str(&field, "generic_types") && is_generic => {
            acc_field_with_type(shape, field, sft_ty.clone())
        }
        (_, Ty_::Tclass(_, _, tyl)) if is_lit_str(&field, "generic_types") && !tyl.is_empty() => {
            let tyl: Vec<Ty> = tyl.iter().map(|ty| make_ts(env, ty.clone())).collect();
            acc_field_with_type(shape, field, make_type::tuple(r, tyl))
        }
        (_, _)
            if is_lit_str(&field, "kind")
                || is_lit_str(&field, "name")
                || is_lit_str(&field, "alias") =>
        {
            acc_field_with_type(shape, field, sft_ty.clone())
        }
        _ => {
            // If the field is marked optional (as it should be, apart from kind)
            // then leave it alone
            if sft_optional {
                shape.insert(
                    field,
                    ShapeFieldType {
                        optional: sft_optional,
                        ty: sft_ty.clone(),
                    },
                );
            }
        }
    }
}
