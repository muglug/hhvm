// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/codemod_type_printer.ml`. See `hh/PORTING.md`.
//! (`Non_denotable` is the `Err` of `print_ty_exn`.)

use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs_core::FunParam;
use crate::typing_defs_core::ParamMode;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;

pub struct NonDenotable;

fn strip_ns(str: &str) -> String {
    let str_ = crate::utils::strip_ns(str);
    // If we had more than one '\\' patternm then we must keep the first '\\'
    // otherwise it will cause an error (we are detecting types from the root
    // namespace)
    if str_.contains('\\') {
        str.to_string()
    } else {
        str_.to_string()
    }
}

fn print_ty_exn(allow_nothing: bool, ty: &Ty) -> Result<String, NonDenotable> {
    let p = |ty: &Ty| print_ty_exn(false, ty);
    Ok(match ty.get_node() {
        Ty_::Tprim(prim) => crate::aast_defs::string_of_tprim(*prim),
        Ty_::Tunion(tys) if tys.is_empty() && allow_nothing => "nothing".to_string(),
        Ty_::Tany(_)
        | Ty_::Tvar(_)
        | Ty_::Tdependent(..)
        | Ty_::Tunion(_)
        | Ty_::Tintersection(_)
        | Ty_::Tlabel(_)
        | Ty_::Tneg(_) => return Err(NonDenotable),
        Ty_::Tnonnull => "nonnull".to_string(),
        Ty_::Tdynamic(_) => "dynamic".to_string(),
        Ty_::Tgeneric(s) => s.clone(),
        Ty_::Toption(ty) => match ty.get_node() {
            Ty_::Tnonnull => "mixed".to_string(),
            _ => format!("?{}", p(ty)?),
        },
        Ty_::Tfun(ft) => {
            let mut params = ft
                .params
                .iter()
                .map(print_fun_param_exn)
                .collect::<Result<Vec<_>, _>>()?;
            if crate::typing_defs_core::get_ft_variadic(ft) {
                params.push("...".to_string())
            }
            format!("(function({}): {})", params.join(", "), p(&ft.ret)?)
        }
        Ty_::Ttuple(t) => {
            let mut all = t.required.iter().map(p).collect::<Result<Vec<_>, _>>()?;
            for ty in &t.optional {
                all.push(format!("optional {}", p(ty)?))
            }
            match &t.extra {
                TupleExtra::Tvariadic(t_variadic) => {
                    if !crate::typing_defs::is_nothing(t_variadic) {
                        all.push(format!("{}...", p(t_variadic)?))
                    }
                }
                TupleExtra::Tsplat(t_splat) => all.push(format!("...{}", p(t_splat)?)),
            }
            format!("({})", all.join(", "))
        }
        Ty_::Tshape(ShapeType::ShapeSimple(s)) => {
            let mut fields = s
                .fields
                .iter()
                .map(|(name, sft)| print_shape_field_exn(&name.0, sft))
                .collect::<Result<Vec<_>, _>>()?;
            let shape_kind = &s.unknown_value;
            if !crate::typing_defs::is_nothing(shape_kind) {
                let tail = match shape_kind.get_node() {
                    Ty_::Toption(ty) if crate::typing_defs::is_nonnull(ty) => "...".to_string(),
                    Ty_::Tintersection(tys) if tys.is_empty() => "...".to_string(),
                    _ => format!("{}...", p(shape_kind)?),
                };
                fields.push(tail)
            }
            format!("shape({})", fields.join(", "))
        }
        Ty_::Tshape(ShapeType::ShapeSplat(s)) => {
            let fields = s
                .ss_elems
                .iter()
                .map(|ty| Ok(format!("...{}", p(ty)?)))
                .collect::<Result<Vec<_>, _>>()?;
            format!("shape({})", fields.join(", "))
        }
        Ty_::Tnewtype(name, tyl, _) if tyl.is_empty() => crate::utils::strip_ns(name).to_string(),
        Ty_::Tnewtype(name, tyl, _) => format!("{}<{}>", crate::utils::strip_ns(name), print_tyl_exn(tyl)?),
        Ty_::Tclass(id, _, tyl) if tyl.is_empty() => strip_ns(&id.1),
        Ty_::Tclass(id, _, tyl) => format!("{}<{}>", crate::utils::strip_ns(&id.1), print_tyl_exn(tyl)?),
        Ty_::TvecOrDict(ty1, ty2) => format!("vec_or_dict<{}, {}>", p(ty1)?, p(ty2)?),
        Ty_::Taccess(t) => format!("{}::{}", p(&t.0)?, (t.1).1),
        Ty_::TclassPtr(ty) => format!("class<{}>", p(ty)?),
    })
}

fn print_tyl_exn(tyl: &[Ty]) -> Result<String, NonDenotable> {
    Ok(tyl
        .iter()
        .map(|ty| print_ty_exn(false, ty))
        .collect::<Result<Vec<_>, _>>()?
        .join(", "))
}

fn print_fun_param_exn(param: &FunParam) -> Result<String, NonDenotable> {
    Ok(match crate::typing_defs_core::get_fp_mode(param) {
        ParamMode::FPinout => format!("inout {}", print_ty_exn(false, &param.type_)?),
        _ => print_ty_exn(false, &param.type_)?,
    })
}

fn print_shape_field_exn(name: &TshapeFieldName, sft: &ShapeFieldType) -> Result<String, NonDenotable> {
    Ok(format!(
        "{}{} => {}",
        if sft.optional { "?" } else { "" },
        print_shape_field_name(name),
        print_ty_exn(false, &sft.ty)?
    ))
}

fn print_shape_field_name(name: &TshapeFieldName) -> String {
    let s = String::from_utf8_lossy(&crate::typing_defs_core::t_shape_field::name(name)).into_owned();
    match name {
        TshapeFieldName::TSFlitStr(_) => format!("'{}'", s),
        _ => s,
    }
}

pub fn print(allow_nothing: Option<bool>, ty: &Ty) -> Option<String> {
    print_ty_exn(allow_nothing.unwrap_or(false), ty).ok()
}
