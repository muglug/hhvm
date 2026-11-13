// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_class_pointers.ml`. See `hh/PORTING.md`.
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

use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
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

/// `Naming_special_names.Classes.cString` (`naming_special_names_rust` does
/// not have it).
const C_STRING: &str = "\\HH\\string";

pub fn error_at_cls_const_expr(env: &Env, pos: Pos, cls_name: String) {
    typing_error_utils::add_typing_error(
        &typing_error::primary(primary::T::Class_const_to_string { pos, cls_name }),
        env,
    )
}

pub fn error_at_cls_ptr_type(env: &Env, pos: Pos, ty: String) {
    typing_error_utils::add_typing_error(
        &typing_error::primary(primary::T::Class_pointer_to_string { pos, ty }),
        env,
    )
}

pub fn warning_at_classname_type(env: &Env, pos: Pos, cls_name: String, ty_pos: PosOrDecl) {
    typing_warning_utils::add(
        env,
        (
            pos,
            typing_warning::Kind::String_to_class_pointer,
            typing_warning::string_to_class_pointer::T { cls_name, ty_pos },
        ),
    )
}

pub fn error_at_classname_type(env: &Env, pos: Pos, cls_name: String, ty_pos: PosOrDecl) {
    typing_error_utils::add_typing_error(
        &typing_error::primary(primary::T::String_to_class_pointer {
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
pub fn coerce_to_name(level: isize, env: &mut Env, ty: Ty) -> Ty {
    if level < 1 {
        ty
    } else {
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
            Ty_::TclassPtr(ty_inner) => {
                rewrap(typing_make_type::classname(r, vec![ty_inner.clone()]))
            }
            Ty_::Tunion(tyl) if level >= 2 => {
                let tyl: Vec<Ty> = tyl
                    .iter()
                    .map(|ty| coerce_to_name(level, env, ty.clone()))
                    .collect();
                rewrap(mk((r, Ty_::Tunion(tyl))))
            }
            Ty_::Tintersection(tyl) if level >= 2 => {
                let tyl: Vec<Ty> = tyl
                    .iter()
                    .map(|ty| coerce_to_name(level, env, ty.clone()))
                    .collect();
                rewrap(mk((r, Ty_::Tintersection(tyl))))
            }
            Ty_::Tgeneric(_) | Ty_::Tnewtype(_, _, _) if level >= 3 => {
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
