// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_array_access_util.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;
use oxidized::nast;

use crate::pos_or_decl;
use crate::typing_defs::is_nothing;
use crate::typing_defs_constraints::CanIndex;
use crate::typing_defs_constraints::CiAccessKind;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_map;
use crate::typing_env as env_;
use crate::typing_env_types::Env;
use crate::typing_log;
use crate::typing_make_type as make_type;
use crate::typing_shapes;

/// Like widen_for_array_get, but for when constraint_can_index is on.
pub fn widen_for_array_get_ci(ci: &CanIndex, env: &mut Env, ty: Ty) -> Option<Ty> {
    let CanIndex {
        access_kind: ci_access_kind,
        index_expr,
        expr_pos,
        ..
    } = ci;
    let lhs_of_null_coalesce = match ci_access_kind {
        CiAccessKind::CiNormal => false,
        CiAccessKind::CiLhsOfNullCoalesce | CiAccessKind::CiDestructureOptional => true,
    };
    typing_log::log_with_level(env, "typing", 1, || {
        typing_log::log_types(
            &pos_or_decl::of_raw_pos(expr_pos.clone()),
            env,
            &[typing_log::LogStructure::LogHead(
                "widen_for_array_get".to_string(),
                vec![typing_log::LogStructure::LogType(
                    "ty".to_string(),
                    ty.clone(),
                )],
            )],
        )
    });
    match get_node(&ty) {
        // The null type is valid only with a null-coalescing use of array get
        Ty_::Tprim(Tprim::Tnull) if lhs_of_null_coalesce => Some(ty),
        // dynamic is valid for array get
        Ty_::Tdynamic(_) => Some(ty),
        // All class-based containers, and keyset, vec and dict, are subtypes of
        // some instantiation of KeyedContainer
        Ty_::Tclass((_, cn), _, _)
            if cn == sn::collections::VECTOR
                || cn == sn::collections::VEC
                || cn == sn::collections::MAP
                || cn == sn::collections::DICT
                || cn == sn::collections::KEYSET
                || cn == sn::collections::CONST_MAP
                || cn == sn::collections::IMM_MAP
                || cn == sn::collections::KEYED_CONTAINER
                || cn == sn::collections::ANY_ARRAY
                || cn == sn::collections::CONST_VECTOR
                || cn == sn::collections::IMM_VECTOR =>
        {
            let r = get_reason(&ty).clone();
            let element_ty = env_::fresh_type_invariant(env, expr_pos.clone());
            let index_ty = env_::fresh_type_invariant(env, expr_pos.clone());
            let ty = make_type::keyed_container(r, index_ty, element_ty);
            Some(ty)
        }
        // The same is true of PHP arrays
        Ty_::TvecOrDict(_, _) => {
            let r = get_reason(&ty).clone();
            let element_ty = env_::fresh_type_invariant(env, expr_pos.clone());
            let index_ty = env_::fresh_type_invariant(env, expr_pos.clone());
            let ty = make_type::keyed_container(r, index_ty, element_ty);
            Some(ty)
        }
        // For tuples, we just freshen the element types
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: TupleExtra::Tvariadic(t_variadic),
        }) => {
            // requires integer literal
            match index_expr {
                // Should freshen type variables
                nast::Expr(_, _, nast::Expr_::Int(_)) => {
                    let r = get_reason(&ty).clone();
                    let t_required: Vec<Ty> = t_required
                        .iter()
                        .map(|_ty| env_::fresh_type_invariant(env, expr_pos.clone()))
                        .collect();
                    let t_optional: Vec<Ty> = t_optional
                        .iter()
                        .map(|_ty| env_::fresh_type_invariant(env, expr_pos.clone()))
                        .collect();
                    let t_variadic = if is_nothing(t_variadic) {
                        t_variadic.clone()
                    } else {
                        env_::fresh_type_invariant(env, expr_pos.clone())
                    };
                    Some(mk((
                        r,
                        Ty_::Ttuple(TupleType {
                            required: t_required,
                            optional: t_optional,
                            extra: TupleExtra::Tvariadic(t_variadic),
                        }),
                    )))
                }
                _ => None,
            }
        }
        // Whatever the lower bound, construct an open, singleton shape type.
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            fields: fdm,
            origin: _,
            unknown_value: _,
        })) => {
            let r = get_reason(&ty).clone();
            // `do_with_field_expr` only reads the environment (it reports the
            // error of a bad field name in it); the callback goes on with the
            // same environment, mutably.
            let env_for_field = env.clone();
            typing_shapes::do_with_field_expr(
                &env_for_field,
                index_expr,
                None,
                |field_name: TshapeFieldName| {
                    match fdm.get(&t_shape_map::TShapeField(field_name.clone())) {
                        // If field is in the lower bound but is optional, then no upper bound makes sense
                        // unless this is a null-coalesce access
                        Some(ShapeFieldType {
                            optional: true,
                            ty: _,
                        }) if !lhs_of_null_coalesce => None,
                        _ => {
                            let element_ty = env_::fresh_type_invariant(env, expr_pos.clone());
                            let rest_ty = env_::fresh_type_invariant(env, expr_pos.clone());
                            let mut upper_fdm = t_shape_map::T::new();
                            upper_fdm.insert(
                                t_shape_map::TShapeField(field_name),
                                ShapeFieldType {
                                    optional: lhs_of_null_coalesce,
                                    ty: element_ty,
                                },
                            );
                            let upper_shape_ty = make_type::shape(r, rest_ty, upper_fdm);
                            Some(upper_shape_ty)
                        }
                    }
                },
            )
        }
        _ => None,
    }
}
