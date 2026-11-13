// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_skeleton.ml`. See `hh/PORTING.md`.
//!
//! Generate method skeletons based on the known type.
//!
//! The types printed here are declared types (`ty::decl::Ty`), whose layout
//! differs from the OCaml `decl_ty` in a few places: a simple shape is
//! `ShapeTypeSimple(unknown_value, fields)` (no origin), `Tany` and
//! `Tdynamic` carry nothing, and the names in shape-field keys have no
//! positions. `Typing_defs.is_nothing` and `get_ft_variadic` at the declared
//! phase are written here ([`is_nothing_decl`], [`get_ft_variadic_decl`]):
//! the crate has them for the inferred phase only. A literal shape-field name
//! is a byte string, printed with `String::from_utf8_lossy` (the OCaml
//! prints the bytes as they are; they differ only for a name that is not
//! UTF-8).

use naming_special_names_rust as sn;
use oxidized::pos::Pos;
use ty::decl;

use crate::aast_defs;
use crate::class_refinement;
use crate::folded_class::ClassElt;
use crate::pos;
use crate::typing_defs_core;
use crate::typing_defs_core::DeclFunParam;
use crate::typing_defs_core::DeclFunType;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_flags::FunTypeFlags;
use crate::utils;

/// We keep track of the skeleton in two parts: a prefix and a suffix.
///
/// The cursor is intended to be moved in-between the prefix and suffix after
/// inserting the skeleton.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct T {
    prefix: String,
    suffix: Option<String>,
}

/// Convert the skeleton to a string
pub fn to_string(t: &T) -> String {
    let T { prefix, suffix } = t;
    match suffix {
        None => prefix.clone(),
        Some(suffix) => format!("{}{}", prefix, suffix),
    }
}

/// Add a suffix to the skeleton
pub fn add_suffix(s: &str, t: T) -> T {
    let suffix = format!("{}{}", t.suffix.as_deref().unwrap_or(""), s);
    T {
        suffix: Some(suffix),
        ..t
    }
}

/// Strip at the end of the skeleton. Noop if the skeleton
/// does not end in the given suffix
pub fn strip_suffix(s: &str, t: T) -> T {
    let suffix = t.suffix.map(|suffix| {
        if suffix.ends_with(s) {
            suffix[..suffix.len() - s.len()].to_string()
        } else {
            suffix
        }
    });
    T { suffix, ..t }
}

/// Add a prefix to the skeleton
pub fn add_prefix(s: &str, t: T) -> T {
    let prefix = format!("{}{}", s, t.prefix);
    T { prefix, ..t }
}

/// Where to put the cursor of the skeleton was inserted at the given position
pub fn cursor_after_insert(pos: &Pos, t: &T) -> Pos {
    let T { prefix, suffix: _ } = t;
    pos::shrink_to_end(&pos::advance_string(prefix, pos))
}

/// `Typing_defs.is_nothing` at the declared phase.
fn is_nothing_decl(ty: &DeclTy) -> bool {
    match ty.node_ref() {
        decl::Ty_::Tunion(tys) if tys.is_empty() => true,
        _ => false,
    }
}

/// `Typing_defs.get_ft_variadic` at the declared phase.
fn get_ft_variadic_decl(ft: &DeclFunType) -> bool {
    ft.flags.contains(FunTypeFlags::VARIADIC)
}

/// Given a type declaration, return user-denotable syntax that
/// represents it. This is lossy: we use mixed if there's no better
/// syntax.
fn strip_supportdyn(ty: &DeclTy) -> &DeclTy {
    match ty.node_ref() {
        decl::Ty_::Tapply(x) => {
            let (name, args) = &**x;
            match &args[..] {
                [ty] if name.id_ref().as_str() == sn::classes::SUPPORT_DYN => {
                    strip_supportdyn(ty)
                }
                _ => ty,
            }
        }
        _ => ty,
    }
}

fn of_decl_ty(ty: &DeclTy) -> String {
    // TODO: when we start supporting NoAutoDynamic, revisit this
    let ty = strip_supportdyn(ty);
    match ty.node_ref() {
        decl::Ty_::Tprim(p) => aast_defs::string_of_tprim(*p),
        decl::Ty_::Tmixed | decl::Ty_::Twildcard | decl::Ty_::Tany => "mixed".to_string(),
        decl::Ty_::Tnonnull => "nonnull".to_string(),
        decl::Ty_::Tdynamic => "dynamic".to_string(),
        decl::Ty_::Tthis => "this".to_string(),
        decl::Ty_::Toption(ty) => {
            // TODO: when we start supporting NoAutoDynamic, revisit this
            match strip_supportdyn(ty).node_ref() {
                decl::Ty_::Tnonnull => "mixed".to_string(),
                _ => format!("?{}", of_decl_ty(ty)),
            }
        }
        decl::Ty_::Tfun(f) => {
            let mut params: Vec<String> = f.params.iter().map(of_fun_param).collect();
            if get_ft_variadic_decl(f) {
                params.push("...".to_string());
            }
            format!("(function({}): {})", params.join(", "), of_decl_ty(&f.ret))
        }
        decl::Ty_::Tgeneric(name) => utils::strip_all_ns(name.as_str()).to_string(),
        decl::Ty_::Tapply(x) => {
            let (name, args) = &**x;
            let name = utils::strip_all_ns(name.id_ref().as_str());
            match &args[..] {
                [] => name.to_string(),
                args => {
                    let args: Vec<String> = args.iter().map(of_decl_ty).collect();
                    format!("{}<{}>", name, args.join(", "))
                }
            }
        }
        // TODO akenn: open tuples
        decl::Ty_::Ttuple(tuple) => {
            let decl::ty::TupleType(t_required, _t_optional, _t_extra) = &**tuple;
            let args: Vec<String> = t_required.iter().map(of_decl_ty).collect();
            format!("({})", args.join(", "))
        }
        decl::Ty_::Tshape(shape) => match &**shape {
            decl::ty::ShapeType::Simple(decl::ty::ShapeTypeSimple(kind, fields)) => {
                // `TShapeMap.fold (fun key ty acc -> of_shape_field key ty :: acc)
                // fields []`: in decreasing order of the keys.
                let fields: Vec<String> = fields
                    .iter()
                    .rev()
                    .map(|(key, ty)| of_shape_field(key, ty))
                    .collect();
                let fields_with_ellipsis = if is_nothing_decl(kind) {
                    // Closed shape
                    fields
                } else {
                    // Open shape TODO akenn non-mixed open
                    let mut fields = fields;
                    fields.push("...".to_string());
                    fields
                };
                format!("shape({})", fields_with_ellipsis.join(", "))
            }
            decl::ty::ShapeType::Splat(ss_elems) => {
                let fields: Vec<String> = ss_elems
                    .iter()
                    .map(|ty| format!("...{}", of_decl_ty(ty)))
                    .collect();
                format!("shape({})", fields.join(", "))
            }
        },
        decl::Ty_::Tunion(tys) if tys.is_empty() => "nothing".to_string(),
        decl::Ty_::Tunion(_) => "mixed".to_string(),
        decl::Ty_::Tintersection(_) => "mixed".to_string(),
        decl::Ty_::TvecOrDict(x) => {
            let (key_ty, val_ty) = &**x;
            format!(
                "vec_or_dict<{}, {}>",
                of_decl_ty(key_ty),
                of_decl_ty(val_ty)
            )
        }
        decl::Ty_::Tlike(ty) => of_decl_ty(ty),
        decl::Ty_::Taccess(taccess) => {
            let decl::TaccessType { ty, type_const } = &**taccess;
            format!("{}::{}", of_decl_ty(ty), type_const.id_ref().as_str())
        }
        decl::Ty_::Trefinement(x) => {
            let decl::TrefinementType { ty, refinement: rs } = &**x;
            format!(
                "{} with {}",
                of_decl_ty(ty),
                class_refinement::to_string_decl(of_decl_ty, rs)
            )
        }
        decl::Ty_::TclassPtr(ty) => format!("class<{}>", of_decl_ty(ty)),
    }
}

fn of_fun_param(fp: &DeclFunParam) -> String {
    of_decl_ty(&fp.ty)
}

fn of_shape_field(
    name: &decl::ty::TshapeFieldName,
    sft: &decl::ShapeFieldType<crate::ctx::R>,
) -> String {
    let name_s = match name {
        decl::ty::TshapeFieldName::TSFregexGroup(s) => s.as_str().to_string(),
        decl::ty::TshapeFieldName::TSFlitStr(s) => {
            format!("\"{}\"", String::from_utf8_lossy(s.as_bytes()))
        }
        decl::ty::TshapeFieldName::TSFclassConst(c_name, const_name) => {
            format!("{}::{}", c_name.as_str(), const_name.as_str())
        }
    };
    let name_s = if sft.optional {
        format!("?{}", name_s)
    } else {
        name_s
    };
    format!("{} => {}", name_s, of_decl_ty(&sft.ty))
}

fn param_source(param: &DeclFunParam, variadic: bool) -> String {
    let name = match &param.name {
        Some(name) => name.as_str(),
        None => "$_",
    };
    let ty_s = of_decl_ty(&param.ty);
    format!("{} {}{}", ty_s, if variadic { "..." } else { "" }, name)
}

/// Is this type of the form Awaitable<something> ?
fn is_awaitable(ty: &DeclTy) -> bool {
    match ty.node_ref() {
        decl::Ty_::Tapply(x) if x.0.id_ref().as_str() == sn::classes::AWAITABLE => true,
        decl::Ty_::Tlike(ty) => is_awaitable(ty),
        _ => false,
    }
}

fn params_source(variadic: bool, params: &[DeclFunParam]) -> String {
    let n = params.len();
    let explicit_params: Vec<String> = params
        .iter()
        .enumerate()
        .map(|(i, p)| param_source(p, variadic && i + 1 == n))
        .collect();
    explicit_params.join(", ")
}

fn of_implicit_params(
    impl_params: &decl::ty::FunImplicitParams<crate::ctx::R, DeclTy>,
) -> String {
    match &impl_params.capability {
        decl::ty::Capability::CapDefaults(_) => "".to_string(),
        decl::ty::Capability::CapTy(t) => match t.node_ref() {
            decl::Ty_::Tintersection(tys) => {
                let contexts: Vec<String> = tys.iter().map(of_decl_ty).collect();
                format!("[{}]", contexts.join(", "))
            }
            _ => "".to_string(),
        },
    }
}

/// Generates source code for a method skeleton that matches [meth],
/// with the appropriate static modifier and override attribute.
pub fn of_method(
    name: &str,
    meth: &ClassElt,
    is_static: bool,
    is_override: bool,
    open_braces: bool,
) -> T {
    // TODO: when we start supporting NoAutoDynamic, revisit this
    let ce_type: &DeclTy = &meth.ce_type;
    let ty_ = strip_supportdyn(ce_type).node_ref();
    let (params, return_ty, async_modifier, capabilities) = match ty_ {
        decl::Ty_::Tfun(ft) => (
            params_source(get_ft_variadic_decl(ft), &ft.params),
            of_decl_ty(&ft.ret),
            if is_awaitable(&ft.ret) { "async " } else { "" },
            of_implicit_params(&ft.implicit_params),
        ),
        _ => ("".to_string(), "mixed".to_string(), "", "".to_string()),
    };

    let prefix = format!(
        "\n{}  {} {}{}function {}({}){}: {} {{",
        if is_override {
            "  <<__Override>>\n"
        } else {
            ""
        },
        typing_defs_core::string_of_visibility(&meth.ce_visibility),
        if is_static { "static " } else { "" },
        async_modifier,
        name,
        params,
        capabilities,
        return_ty
    );
    let prefix = if open_braces {
        prefix + "\n    "
    } else {
        prefix
    };
    let suffix = "}\n".to_string();
    let suffix = if open_braces {
        format!("\n  {}", suffix)
    } else {
        suffix
    };
    T {
        prefix,
        suffix: Some(suffix),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(prefix: &str, suffix: Option<&str>) -> T {
        T {
            prefix: prefix.to_string(),
            suffix: suffix.map(|s| s.to_string()),
        }
    }

    #[test]
    fn suffixes_and_prefixes() {
        assert_eq!(to_string(&t("a", None)), "a");
        assert_eq!(to_string(&t("a", Some("b"))), "ab");
        assert_eq!(add_suffix("c", t("a", None)), t("a", Some("c")));
        assert_eq!(add_suffix("c", t("a", Some("b"))), t("a", Some("bc")));
        assert_eq!(strip_suffix("c", t("a", Some("bc"))), t("a", Some("b")));
        assert_eq!(strip_suffix("x", t("a", Some("bc"))), t("a", Some("bc")));
        assert_eq!(strip_suffix("x", t("a", None)), t("a", None));
        assert_eq!(add_prefix("z", t("a", Some("b"))), t("za", Some("b")));
    }
}
