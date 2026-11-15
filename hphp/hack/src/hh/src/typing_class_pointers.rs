// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_class_pointers.ml`. See `hh/PORTING.md`.
//!
//! `typing_class_pointers.ml` has no `.mli`. `string_of_class_id_` and
//! `check_string_coercion_point` are polymorphic in the annotations of the
//! AST in OCaml (they are called on NAST and TAST nodes), so they are generic
//! here.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::naming_special_names::classes::C_STRING;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::ty_equal;
use crate::typing_dynamic_utils;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_make_type;
use crate::typing_utils;
use crate::typing_warning;
use crate::typing_warning_utils;

pub fn error_at_cls_const_expr(env: &Env, pos: Pos, cls_name: String) {
    typing_error_utils::add_typing_error(
        &typing_error::primary(primary::T::ClassConstToString { pos, cls_name }),
        env,
    )
}

pub fn error_at_cls_ptr_type(env: &Env, pos: Pos, ty: String) {
    typing_error_utils::add_typing_error(
        &typing_error::primary(primary::T::ClassPointerToString { pos, ty }),
        env,
    )
}

pub fn warning_at_classname_type(env: &Env, pos: Pos, cls_name: String, ty_pos: PosOrDecl) {
    typing_warning_utils::add(
        env,
        (
            pos,
            typing_warning::Kind::STRING_TO_CLASS_POINTER,
            typing_warning::string_to_class_pointer::T { cls_name, ty_pos },
        ),
    )
}

pub fn error_at_classname_type(env: &Env, pos: Pos, cls_name: String, ty_pos: PosOrDecl) {
    typing_error_utils::add_typing_error(
        &typing_error::primary(primary::T::StringToClassPointer {
            pos,
            cls_name,
            ty_pos,
        }),
        env,
    )
}

pub fn string_of_class_id_<Ex, En>(cid: &aast::ClassId_<Ex, En>) -> String {
    match cid {
        aast::ClassId_::CIparent => "parent".to_string(),
        aast::ClassId_::CIself => "self".to_string(),
        aast::ClassId_::CIstatic => "static".to_string(),
        // <expr>::class is banned
        aast::ClassId_::CIexpr(_) => "".to_string(),
        aast::ClassId_::CI(ast_defs::Id(_, name)) => name.clone(),
        aast::ClassId_::CIreified(ast_defs::Id(_, name)) => name.clone(),
    }
}

/// OCaml returns `unit` and drops the environment that
/// `Typing_dynamic_utils.strip_dynamic` gives back: the environment is only
/// read.
pub fn check_string_coercion_point<Ex, En>(env: &Env, expr: &aast::Expr<Ex, En>, ty: &Ty) {
    if env.emit_string_coercion_error {
        match expr {
            aast::Expr(_, pos, aast::Expr_::ClassConst(cc))
                if (cc.1).1 == sn::members::M_CLASS =>
            {
                let (aast::ClassId(_, _, cid_), _) = &**cc;
                match cid_ {
                    // nameof T is illegal (T187575261)
                    aast::ClassId_::CIreified(_) => {}
                    _ => {
                        let check = |ty: &Ty| match get_node(ty) {
                            Ty_::Tclass((_, id), _, _) if id == C_STRING => {
                                error_at_cls_const_expr(env, pos.clone(), string_of_class_id_(cid_))
                            }
                            Ty_::Tprim(ast_defs::Tprim::Tarraykey) => {
                                error_at_cls_const_expr(env, pos.clone(), string_of_class_id_(cid_))
                            }
                            _ => {}
                        };
                        let ty = typing_dynamic_utils::strip_dynamic(&mut env.clone(), ty.clone());
                        match get_node(&ty) {
                            Ty_::Toption(ty) => check(ty),
                            _ => check(&ty),
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Weaken class-typed expression at runtime string coercion points
pub fn coerce_to_name(env: &mut Env, ty: Ty) -> Ty {
    let ety = typing_env::expand_type(env, ty.clone());
    let (stripped, inner) = typing_utils::strip_supportdyn(env, ety.clone());
    let rewrap = |ty: Ty| {
        if stripped {
            typing_make_type::supportdyn(get_reason(&ety).clone(), ty)
        } else {
            ty
        }
    };
    let r = get_reason(&inner).clone();
    match get_node(&inner) {
        Ty_::TclassPtr(ty_inner) => rewrap(typing_make_type::classname(r, vec![ty_inner.clone()])),
        Ty_::Tunion(tyl) => {
            let tyl: Vec<Ty> = tyl
                .iter()
                .map(|ty| coerce_to_name(env, ty.clone()))
                .collect();
            rewrap(mk((r, Ty_::Tunion(tyl))))
        }
        Ty_::Tintersection(tyl) => {
            let tyl: Vec<Ty> = tyl
                .iter()
                .map(|ty| coerce_to_name(env, ty.clone()))
                .collect();
            rewrap(mk((r, Ty_::Tintersection(tyl))))
        }
        Ty_::Tgeneric(_) | Ty_::Tnewtype(_, _, _) => {
            let bound = typing_utils::get_base_type(Some(false), env, inner.clone());
            match get_node(&bound) {
                Ty_::TclassPtr(ty_inner) => {
                    rewrap(typing_make_type::classname(r, vec![ty_inner.clone()]))
                }
                _ => ty,
            }
        }
        _ => ty,
    }
}

/// Whether a value of [ty] can be, or contain as a container value, a string
/// that isn't a class pointer. Like types are trusted, as in refinement.
pub fn may_hold_string(expanding: Option<&[Ty]>, env: &mut Env, ty: &Ty) -> bool {
    let expanding = expanding.unwrap_or(&[]);
    let ety = typing_env::expand_type(env, ty.clone());
    let (_, ety) = typing_utils::strip_supportdyn(env, ety);
    fn exists(expanding: &[Ty], env: &mut Env, tyl: &[Ty]) -> bool {
        let mut found = false;
        for ty in tyl {
            if !found {
                found = may_hold_string(Some(expanding), env, ty);
            }
        }
        found
    }
    fn for_all(expanding: &[Ty], env: &mut Env, tyl: &[Ty]) -> bool {
        let mut all = true;
        for ty in tyl {
            if all {
                all = may_hold_string(Some(expanding), env, ty);
            }
        }
        all
    }
    match get_node(&ety) {
        Ty_::TclassPtr(_) | Ty_::Tfun(_) | Ty_::Tlabel(_) | Ty_::Tdynamic(_) => false,
        Ty_::Tprim(ast_defs::Tprim::Tarraykey) => true,
        Ty_::Tprim(_) => false,
        Ty_::Tclass((_, name), _, tyl) => {
            // A string is also an instance of some interfaces, e.g. Stringish
            if name == C_STRING
                || typing_utils::is_sub_type_for_union(
                    env,
                    &typing_make_type::string(crate::typing_reason::none()),
                    &ety,
                )
            {
                true
            } else {
                // The value type of vec<T>, dict<K, T>, KeyedContainer<K, T>, ...
                match tyl.last() {
                    Some(ty) => may_hold_string(Some(expanding), env, ty),
                    None => false,
                }
            }
        }
        Ty_::Toption(ty) => may_hold_string(Some(expanding), env, ty),
        Ty_::Tunion(tyl) => exists(expanding, env, tyl),
        Ty_::Tintersection(tyl) => for_all(expanding, env, tyl),
        Ty_::TvecOrDict(_, ty) => may_hold_string(Some(expanding), env, ty),
        Ty_::Ttuple(TupleType {
            required,
            optional,
            extra: TupleExtra::Tvariadic(ty) | TupleExtra::Tsplat(ty),
        }) => {
            let mut tyl = vec![ty.clone()];
            tyl.extend(required.iter().cloned());
            tyl.extend(optional.iter().cloned());
            exists(expanding, env, &tyl)
        }
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            unknown_value,
            fields,
            ..
        })) => {
            // `TShapeMap.fold (fun _ sft acc -> sft.sft_ty :: acc) s_fields []`:
            // the fields, last key first.
            let mut tyl = vec![unknown_value.clone()];
            tyl.extend(fields.values().rev().map(|sft| sft.ty.clone()));
            exists(expanding, env, &tyl)
        }
        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
            exists(expanding, env, ss_elems)
        }
        Ty_::Tgeneric(_) | Ty_::Tnewtype(_, _, _) | Ty_::Tdependent(_, _)
            if !expanding.iter().any(|t| ty_equal(None, t, &ety)) =>
        {
            let bounds =
                typing_utils::get_concrete_supertypes(None, Some(false), None, false, env, ety.clone());
            if bounds.is_empty() {
                true
            } else {
                let mut expanding_ = vec![ety.clone()];
                expanding_.extend(expanding.iter().cloned());
                for_all(&expanding_, env, &bounds)
            }
        }
        Ty_::Tnonnull
        | Ty_::Tany(_)
        | Ty_::Tvar(_)
        | Ty_::Tneg(_)
        | Ty_::Taccess(_)
        | Ty_::Tgeneric(_)
        | Ty_::Tnewtype(_, _, _)
        | Ty_::Tdependent(_, _) => true,
    }
}

#[cfg(test)]
mod tests {
    use oxidized::nast;

    use super::*;

    #[test]
    fn string_of_class_ids() {
        assert_eq!(string_of_class_id_(&nast::ClassId_::CIparent), "parent");
        assert_eq!(string_of_class_id_(&nast::ClassId_::CIself), "self");
        assert_eq!(string_of_class_id_(&nast::ClassId_::CIstatic), "static");
        assert_eq!(
            string_of_class_id_(&nast::ClassId_::CI(ast_defs::Id(
                Pos::NONE,
                "\\C".to_string()
            ))),
            "\\C"
        );
        assert_eq!(
            string_of_class_id_(&nast::ClassId_::CIreified(ast_defs::Id(
                Pos::NONE,
                "T".to_string()
            ))),
            "T"
        );
    }
}
