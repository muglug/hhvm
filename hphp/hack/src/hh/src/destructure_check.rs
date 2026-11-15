// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/destructure_check.ml`. See `hh/PORTING.md`.
//!
//! Structural validation for shape and tuple destructuring patterns.
//!
//! This check catches errors we do not catch in subtyping, such as:
//! ```text
//!   $s : shape('a' => int, 'b' => string);
//!   shape('a' => $a) = $s;            // error: missing required field 'b'
//!
//!   $s : shape('a' => int, ...);
//!   shape('a' => $a) = $s;            // error: missing `...` for open shape
//!
//!   $s : shape('a' => int);
//!   shape('a' => $a, 'z' => $z) = $s; // error: field 'z' doesn't exist
//!
//!   $t : (int, string);
//!   tuple($a) = $t;                   // error: arity mismatch
//! ```
//!
//! See `Typing_destructure` for the inference-time constraint emission
//! that this check complements.

use std::cmp::Ordering;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;

use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs;
use crate::typing_defs::ShapeFieldType;
use crate::typing_defs::ShapeType;
use crate::typing_defs::ShapeTypeSimple;
use crate::typing_defs::TupleExtra;
use crate::typing_defs::TupleType;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs::get_reason;
use crate::typing_defs::t_shape_field;
use crate::typing_defs::t_shape_map::TShapeField;
use crate::typing_defs::t_shape_map::TShapeMap;
use crate::typing_error;
use crate::typing_error::primary::shape_and_tuple_destructure;
use crate::typing_error_utils;
use crate::typing_make_type;

/// `shape_info` (the fields `shape_is_open`, ... without their prefix)
#[derive(Clone, Debug)]
pub struct ShapeInfo {
    pub is_open: bool,
    pub required_fields: Vec<TShapeField>,
    pub all_fields: Vec<TShapeField>,
}

/// `tuple_info` (the fields `tuple_arity`, ... without their prefix)
#[derive(Clone, Debug)]
pub struct TupleInfo {
    pub arity: Option<isize>,
    pub has_variadic_tail: bool,
}

/// `List.dedup_and_sort ~compare:Typing_defs.TShapeField.compare` (Base): a
/// stable sort, then of each run of equal elements the last one.
fn dedup_and_sort(mut l: Vec<TShapeField>) -> Vec<TShapeField> {
    if l.len() <= 1 {
        return l;
    }
    l.sort_by(|x, y| t_shape_field::compare(&x.0, &y.0));
    let mut res: Vec<TShapeField> = Vec::with_capacity(l.len());
    for x in l {
        match res.last_mut() {
            Some(last) if t_shape_field::compare(&last.0, &x.0) == Ordering::Equal => *last = x,
            _ => res.push(x),
        }
    }
    res
}

pub fn extract_shape_info(s_fields: &TShapeMap<ShapeFieldType>, s_unknown_value: &Ty) -> ShapeInfo {
    ShapeInfo {
        is_open: !typing_defs::is_nothing(s_unknown_value),
        // `TShapeMap.fold` in the order of the keys, each key put at the
        // head of the list: in decreasing order.
        required_fields: s_fields
            .iter()
            .rev()
            .filter(|(_, sft)| !sft.optional)
            .map(|(k, _)| k.clone())
            .collect(),
        all_fields: s_fields.keys().cloned().collect(),
    }
}

pub fn aggregate_shape_intersection(shapes: &[ShapeInfo]) -> ShapeInfo {
    ShapeInfo {
        is_open: shapes.iter().all(|s| s.is_open),
        required_fields: dedup_and_sort(
            shapes
                .iter()
                .flat_map(|s| s.required_fields.iter().cloned())
                .collect(),
        ),
        all_fields: dedup_and_sort(
            shapes
                .iter()
                .flat_map(|s| s.all_fields.iter().cloned())
                .collect(),
        ),
    }
}

pub fn extract_tuple_info(t_required: &[Ty], t_optional: &[Ty], t_extra: &TupleExtra) -> TupleInfo {
    TupleInfo {
        arity: Some((t_required.len() + t_optional.len()) as isize),
        has_variadic_tail: match t_extra {
            TupleExtra::Tvariadic(ty) => !typing_defs::is_nothing(ty),
            TupleExtra::Tsplat(_) => true,
        },
    }
}

pub fn aggregate_tuple_intersection(tuples: &[TupleInfo]) -> TupleInfo {
    let arities: Vec<isize> = tuples.iter().filter_map(|t| t.arity).collect();
    match arities.split_first() {
        None => TupleInfo {
            arity: None,
            has_variadic_tail: false,
        },
        Some((a, rest)) => {
            if rest.iter().all(|b| a == b) {
                TupleInfo {
                    arity: Some(*a),
                    has_variadic_tail: tuples.iter().all(|t| t.has_variadic_tail),
                }
            } else {
                TupleInfo {
                    arity: Some(-1),
                    has_variadic_tail: false,
                }
            }
        }
    }
}

pub fn walk_shapes(env: &tast_env::Env, ty: &Ty, on_shape: &mut dyn FnMut(ShapeInfo)) {
    let ety = tast_env::expand_type(&mut env.clone(), ty.clone());
    match get_node(&ety) {
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            fields: s_fields,
            unknown_value: s_unknown_value,
            ..
        })) => on_shape(extract_shape_info(s_fields, s_unknown_value)),
        Ty_::Tshape(ShapeType::ShapeSplat(_)) => {}
        Ty_::Tdynamic(_) => {}
        Ty_::Tunion(tyl) if tyl.is_empty() => {}
        Ty_::Tunion(tyl) => {
            for ty in tyl {
                walk_shapes(env, ty, on_shape)
            }
        }
        Ty_::Tintersection(tyl) => {
            // Each list of infos is an OCaml list: its head is the last
            // element of the vector.
            let member_infos: Vec<Vec<ShapeInfo>> = tyl
                .iter()
                .map(|ty| {
                    let mut infos = vec![];
                    walk_shapes(env, ty, &mut |info| infos.push(info));
                    infos
                })
                .collect();
            if member_infos.iter().all(|infos| infos.len() <= 1) {
                // `List.filter_map member_infos ~f:List.hd`
                let shapes: Vec<ShapeInfo> = member_infos
                    .into_iter()
                    .filter_map(|mut infos| infos.pop())
                    .collect();
                match shapes.as_slice() {
                    [] => {}
                    shapes => on_shape(aggregate_shape_intersection(shapes)),
                }
            }
        }
        Ty_::Tnewtype(cid, tyl, _) if tyl.len() == 1 && cid == sn::classes::SUPPORT_DYN => {
            walk_shapes(env, &tyl[0], on_shape)
        }
        Ty_::Tgeneric(_) => {
            let upper_bounds =
                tast_env::get_concrete_supertypes(None, false, &mut env.clone(), ety.clone());
            match upper_bounds.as_slice() {
                [] => {}
                _ => {
                    let inter =
                        typing_make_type::intersection(get_reason(&ety).clone(), upper_bounds);
                    walk_shapes(env, &inter, on_shape)
                }
            }
        }
        Ty_::Tnewtype(_, _, bound) => walk_shapes(env, bound, on_shape),
        Ty_::Tdependent(_, bound) => walk_shapes(env, bound, on_shape),
        Ty_::Tany(_)
        | Ty_::Tnonnull
        | Ty_::Toption(_)
        | Ty_::Tprim(_)
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::TvecOrDict(_, _)
        | Ty_::Taccess(_)
        | Ty_::TclassPtr(_)
        | Ty_::Tvar(_)
        | Ty_::Tclass(_, _, _)
        | Ty_::Tneg(_)
        | Ty_::Tlabel(_) => {}
    }
}

pub fn walk_tuples(env: &tast_env::Env, ty: &Ty, on_tuple: &mut dyn FnMut(TupleInfo)) {
    let ety = tast_env::expand_type(&mut env.clone(), ty.clone());
    match get_node(&ety) {
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        }) => on_tuple(extract_tuple_info(t_required, t_optional, t_extra)),
        Ty_::Tdynamic(_) => {}
        Ty_::Tunion(tyl) if tyl.is_empty() => {}
        Ty_::Tunion(tyl) => {
            for ty in tyl {
                walk_tuples(env, ty, on_tuple)
            }
        }
        Ty_::Tintersection(tyl) => {
            // Each list of infos is an OCaml list: its head is the last
            // element of the vector.
            let member_infos: Vec<Vec<TupleInfo>> = tyl
                .iter()
                .map(|ty| {
                    let mut infos = vec![];
                    walk_tuples(env, ty, &mut |info| infos.push(info));
                    infos
                })
                .collect();
            if member_infos.iter().all(|infos| infos.len() <= 1) {
                // `List.filter_map member_infos ~f:List.hd`
                let tuples: Vec<TupleInfo> = member_infos
                    .into_iter()
                    .filter_map(|mut infos| infos.pop())
                    .collect();
                match tuples.as_slice() {
                    [] => {}
                    tuples => on_tuple(aggregate_tuple_intersection(tuples)),
                }
            }
        }
        Ty_::Tnewtype(cid, tyl, _) if tyl.len() == 1 && cid == sn::classes::SUPPORT_DYN => {
            walk_tuples(env, &tyl[0], on_tuple)
        }
        Ty_::Tgeneric(_) => {
            let upper_bounds =
                tast_env::get_concrete_supertypes(None, false, &mut env.clone(), ety.clone());
            match upper_bounds.as_slice() {
                [] => {}
                _ => {
                    let inter =
                        typing_make_type::intersection(get_reason(&ety).clone(), upper_bounds);
                    walk_tuples(env, &inter, on_tuple)
                }
            }
        }
        Ty_::Tnewtype(_, _, bound) => walk_tuples(env, bound, on_tuple),
        Ty_::Tdependent(_, bound) => walk_tuples(env, bound, on_tuple),
        Ty_::Tany(_)
        | Ty_::Tnonnull
        | Ty_::Toption(_)
        | Ty_::Tprim(_)
        | Ty_::Tfun(_)
        | Ty_::Tshape(_)
        | Ty_::TvecOrDict(_, _)
        | Ty_::Taccess(_)
        | Ty_::TclassPtr(_)
        | Ty_::Tvar(_)
        | Ty_::Tclass(_, _, _)
        | Ty_::Tneg(_)
        | Ty_::Tlabel(_) => {}
    }
}

pub fn field_name_string(sf_name: &TShapeField) -> String {
    match &sf_name.0 {
        typing_defs::TshapeFieldName::TSFlitStr(typing_defs::PosByteString(_, s)) => {
            format!("'{}'", s)
        }
        typing_defs::TshapeFieldName::TSFclassConst((_, cls), typing_defs::PosString(_, mem)) => {
            format!("{}::{}", cls, mem)
        }
        typing_defs::TshapeFieldName::TSFregexGroup(typing_defs::PosString(_, s)) => {
            format!("/{}/", s)
        }
    }
}

pub fn add_error(env: &tast_env::Env, error: shape_and_tuple_destructure::T) {
    typing_error_utils::add_typing_error(
        &typing_error::primary(typing_error::primary::T::ShapeAndTupleDestructure(error)),
        env,
    )
}

pub fn is_under_dynamic(env: &tast_env::Env) -> bool {
    tast::is_under_dynamic_assumptions(env.checked)
}

/// `Typing_defs.TShapeField.of_ast Pos_or_decl.of_raw_pos`
fn t_shape_field_of_ast(name: &ast_defs::ShapeFieldName) -> TShapeField {
    TShapeField(t_shape_field::of_ast(
        |p| pos_or_decl::of_raw_pos(p.clone()),
        name,
    ))
}

/// Example:
/// ```text
///   $sh : shape('a' => int, ...);
///   shape('a' => $a) = $sh;  // error: missing `...`
/// ```
pub fn check_missing_ellipsis(
    env: &tast_env::Env,
    shape_pat: &tast::DestructureShape,
    info: &ShapeInfo,
) {
    if !shape_pat.ellipsis && info.is_open {
        add_error(
            env,
            shape_and_tuple_destructure::T::MissingEllipsis(shape_pat.pos.clone()),
        )
    }
}

/// Example:
/// ```text
///   $sh : shape('a' => int, 'b' => string);
///   shape('a' => $a) = $sh;  // error: missing required field 'b'
/// ```
pub fn check_missing_required_fields(
    env: &tast_env::Env,
    shape_pat: &tast::DestructureShape,
    info: &ShapeInfo,
) {
    if !shape_pat.ellipsis {
        let missing_fields: Vec<&TShapeField> = info
            .required_fields
            .iter()
            .filter(|sf_name| {
                !shape_pat.fields.iter().any(|shape_field| {
                    t_shape_field::compare(&t_shape_field_of_ast(&shape_field.name).0, &sf_name.0)
                        == Ordering::Equal
                })
            })
            .collect();
        match missing_fields.as_slice() {
            [] => {}
            missing => {
                let field_names = missing
                    .iter()
                    .map(|sf_name| field_name_string(sf_name))
                    .collect::<Vec<_>>()
                    .join(", ");
                add_error(
                    env,
                    shape_and_tuple_destructure::T::MissingRequiredFields {
                        pos: shape_pat.pos.clone(),
                        field_names,
                    },
                )
            }
        }
    }
}

/// Example:
/// ```text
///   $sh : shape('a' => int);
///   shape('a' => $a, 'z' => $z) = $sh;  // error: field 'z' doesn't exist
/// ```
pub fn check_unknown_fields(
    env: &tast_env::Env,
    shape_pat: &tast::DestructureShape,
    info: &ShapeInfo,
) {
    for shape_field in &shape_pat.fields {
        let sf_name = t_shape_field_of_ast(&shape_field.name);
        let field_is_known = info
            .all_fields
            .iter()
            .any(|f| t_shape_field::compare(&f.0, &sf_name.0) == Ordering::Equal);
        if !field_is_known {
            let field_pos = match &shape_field.name {
                ast_defs::ShapeFieldName::SFlitStr((pos, _)) => pos,
                ast_defs::ShapeFieldName::SFclassConst(ast_defs::Id(pos, _), _) => pos,
                ast_defs::ShapeFieldName::SFclassname(ast_defs::Id(pos, _)) => pos,
            };
            add_error(
                env,
                shape_and_tuple_destructure::T::UnknownField {
                    pos: field_pos.clone(),
                    field_name: field_name_string(&sf_name),
                },
            )
        }
    }
}

pub fn validate_shape_member(
    env: &tast_env::Env,
    shape_pat: &tast::DestructureShape,
    info: &ShapeInfo,
    under_dynamic: bool,
) {
    if !under_dynamic {
        check_missing_ellipsis(env, shape_pat, info);
        check_missing_required_fields(env, shape_pat, info);
        check_unknown_fields(env, shape_pat, info)
    }
}

pub fn check_shape(env: &tast_env::Env, rhs_ty: &Ty, shape_pat: &tast::DestructureShape) {
    let under_dynamic = is_under_dynamic(env);
    walk_shapes(env, rhs_ty, &mut |info| {
        validate_shape_member(env, shape_pat, &info, under_dynamic)
    })
}

pub fn validate_tuple_member(
    env: &tast_env::Env,
    tuple_pat: &tast::DestructureTuple,
    info: &TupleInfo,
) {
    let pat_arity = tuple_pat.entries.len() as isize;
    match info.arity {
        Some(tuple_arity) if tuple_arity >= 0 => {
            if !tuple_pat.ellipsis && pat_arity != tuple_arity {
                add_error(
                    env,
                    shape_and_tuple_destructure::T::TupleArityMismatch {
                        pos: tuple_pat.pos.clone(),
                        pat_arity,
                        tuple_arity,
                    },
                )
            }
            if tuple_pat.ellipsis && !info.has_variadic_tail && pat_arity > tuple_arity {
                add_error(
                    env,
                    shape_and_tuple_destructure::T::TupleArityExceeds {
                        pos: tuple_pat.pos.clone(),
                        pat_arity,
                        tuple_arity,
                    },
                )
            }
        }
        Some(_) => add_error(
            env,
            shape_and_tuple_destructure::T::TupleArityUnionConflict(tuple_pat.pos.clone()),
        ),
        None => {}
    }
}

pub fn check_tuple(env: &tast_env::Env, rhs_ty: &Ty, tuple_pat: &tast::DestructureTuple) {
    walk_tuples(env, rhs_ty, &mut |info| {
        validate_tuple_member(env, tuple_pat, &info)
    })
}

/// The object `handler`.
struct DestructureCheck;

impl<'a> tast_visitor::Handler<'a> for DestructureCheck {
    fn at_expr(&mut self, env: &tast_env::Env, e: &'a tast::Expr) {
        let aast::Expr(ty, _pos, expr_) = e;
        match expr_ {
            aast::Expr_::DestructureShape(shape_pat) => check_shape(env, ty, shape_pat),
            aast::Expr_::DestructureTuple(tuple_pat) => check_tuple(env, ty, tuple_pat),
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(DestructureCheck)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(s: &str) -> TShapeField {
        TShapeField(typing_defs::TshapeFieldName::TSFlitStr(
            typing_defs::PosByteString(oxidized::pos::Pos::NONE, s.into()),
        ))
    }

    #[test]
    fn tuple_intersection() {
        let t = |arity, v| TupleInfo {
            arity,
            has_variadic_tail: v,
        };
        let r = aggregate_tuple_intersection(&[t(Some(2), true), t(None, false), t(Some(2), true)]);
        assert_eq!((r.arity, r.has_variadic_tail), (Some(2), false));
        let r = aggregate_tuple_intersection(&[t(Some(2), true), t(Some(3), true)]);
        assert_eq!((r.arity, r.has_variadic_tail), (Some(-1), false));
        let r = aggregate_tuple_intersection(&[t(None, true)]);
        assert_eq!((r.arity, r.has_variadic_tail), (None, false));
    }

    #[test]
    fn shape_intersection_sorts_and_dedups() {
        let s = |req: &[&str], all: &[&str], open| ShapeInfo {
            is_open: open,
            required_fields: req.iter().map(|s| lit(s)).collect(),
            all_fields: all.iter().map(|s| lit(s)).collect(),
        };
        let r = aggregate_shape_intersection(&[
            s(&["b", "a"], &["a", "b"], true),
            s(&["a"], &["a", "c"], false),
        ]);
        assert!(!r.is_open);
        let names = |l: &[TShapeField]| l.iter().map(field_name_string).collect::<Vec<_>>();
        assert_eq!(names(&r.required_fields), vec!["'a'", "'b'"]);
        assert_eq!(names(&r.all_fields), vec!["'a'", "'b'", "'c'"]);
    }
}
