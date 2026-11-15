// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Sym_def` (`write_symbol_info/sym_def.ml`).
//!
//! [SymbolOccurrence.t] don't contain all information for computing xrefs.
//! - Occurrence of kind "Class" can refer to classes, traits, interfaces, enum, typedefs
//! - Members occurrence come with their "receiver" class but not the "origin" class
//!   (e.g. in Foo::Bar, Bar origin can be a parent of Foo).
//!
//! [resolve] gets these information from an occurrence. It is mostly a specialized and
//! simplified implementation of [ServerSymbolDefinition.go].

use oxidized::ast_defs::ClassishKind;
use oxidized::naming_types::KindOfType;
use oxidized::pos::Pos;
use relative_path::RelativePath;

use super::predicate;
use crate::decl_entry;
use crate::decl_provider;
use crate::folded_class;
use crate::format;
use crate::format::Formatter;
use crate::identify_symbol_service;
use crate::naming_provider;
use crate::provider_context;
use crate::symbol_occurrence as so;
use naming_special_names_rust as sn;

/// class_name is the canonical qualified name to a container kind.
/// starts with a backslash
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum T {
    Function { name: String },
    Method { class_name: String, name: String },
    Property { class_name: String, name: String },
    ClassConst { class_name: String, name: String },
    GlobalConst { name: String },
    Class { kind: ClassishKind, name: String },
    Typeconst { class_name: String, name: String },
    Typedef { name: String },
    Module { name: String },
}

/// `pp` (`[@@deriving show]`): `Sym_def.Function {name = "\\f"}`, laid out
/// by `Format` as ppx_deriving's printer does.
pub fn pp(fmt: &mut Formatter, x: &T) {
    let open = |fmt: &mut Formatter, label: &str| {
        format::pp_open_box(fmt, 2);
        format::pp_print_string(fmt, label);
        format::pp_print_string(fmt, " {");
        format::pp_print_cut(fmt);
    };
    let field_string = |fmt: &mut Formatter, name: &str, v: &str| {
        format::pp_open_box(fmt, 0);
        format::pp_print_string(fmt, name);
        format::pp_print_string(fmt, " =");
        format::pp_print_space(fmt);
        format::pp_print_string(fmt, &crate::rt::ocaml_printf::sprintf_s_bytes(v.as_bytes()));
        format::pp_close_box(fmt);
    };
    let semi = |fmt: &mut Formatter| {
        format::pp_print_string(fmt, ";");
        format::pp_print_space(fmt);
    };
    let close = |fmt: &mut Formatter| {
        format::pp_close_box(fmt);
        format::pp_print_string(fmt, "}");
    };
    let one = |fmt: &mut Formatter, label: &str, name: &str| {
        open(fmt, label);
        field_string(fmt, "name", name);
        close(fmt);
    };
    let two = |fmt: &mut Formatter, label: &str, class_name: &str, name: &str| {
        open(fmt, label);
        field_string(fmt, "class_name", class_name);
        semi(fmt);
        field_string(fmt, "name", name);
        close(fmt);
    };
    match x {
        T::Function { name } => one(fmt, "Sym_def.Function", name),
        T::Method { class_name, name } => two(fmt, "Sym_def.Method", class_name, name),
        T::Property { class_name, name } => two(fmt, "Sym_def.Property", class_name, name),
        T::ClassConst { class_name, name } => two(fmt, "Sym_def.ClassConst", class_name, name),
        T::GlobalConst { name } => one(fmt, "Sym_def.GlobalConst", name),
        T::Class { kind, name } => {
            open(fmt, "Sym_def.Class");
            format::pp_open_box(fmt, 0);
            format::pp_print_string(fmt, "kind");
            format::pp_print_string(fmt, " =");
            format::pp_print_space(fmt);
            {
                let unit = |_: &mut Formatter, _: &()| ();
                let mut p = crate::ast_show::P::new(fmt, &unit, &unit);
                crate::ast_show::ast_defs::pp_classish_kind(&mut p, kind);
            }
            format::pp_close_box(fmt);
            semi(fmt);
            field_string(fmt, "name", name);
            close(fmt);
        }
        T::Typeconst { class_name, name } => two(fmt, "Sym_def.Typeconst", class_name, name),
        T::Typedef { name } => one(fmt, "Sym_def.Typedef", name),
        T::Module { name } => one(fmt, "Sym_def.Module", name),
    }
}

/// `show` (`Format.asprintf "%a" pp`).
pub fn show(x: &T) -> String {
    format::asprintf(|fmt| pp(fmt, x))
}

fn get_class(ctx: &provider_context::T, class_name: &str) -> Option<folded_class::T> {
    decl_entry::to_option(decl_provider::get_class(None, ctx, class_name))
}

fn create_class_typedef(ctx: &provider_context::T, class_: &str) -> Option<T> {
    let (_fn, ct) = naming_provider::get_type_path_and_kind(ctx, class_)?;
    match ct {
        KindOfType::TClass => {
            let class_decl = get_class(ctx, class_)?;
            let kind = folded_class::kind(&class_decl);
            Some(T::Class {
                kind,
                name: class_.to_string(),
            })
        }
        KindOfType::TTypedef => Some(T::Typedef {
            name: class_.to_string(),
        }),
    }
}

fn get_only_const(class_: &folded_class::T, const_name: &str) -> Option<String> {
    match folded_class::get_typeconst(class_, const_name) {
        None => folded_class::get_const(class_, const_name).map(|c| c.origin.as_str().to_string()),
        Some(_) => None,
    }
}

pub fn resolve(ctx: &provider_context::T, occ: &so::T<Pos>) -> Option<T> {
    let so::T { name, type_, .. } = occ;
    let get_class_ = |ctx: &provider_context::T, class_name: &str| get_class(ctx, class_name);
    match type_ {
        so::Kind::Attribute(Some(so::OverrideInfo {
            class_name,
            method_name,
            is_static,
        })) => {
            let matching_method = decl_provider::get_overridden_method(ctx, class_name, method_name, *is_static);
            match matching_method {
                decl_entry::T::Found(meth) => Some(T::Method {
                    class_name: meth.ce_origin.clone(),
                    name: method_name.clone(),
                }),
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
            }
        }
        so::Kind::Attribute(None) | so::Kind::Class(_) => create_class_typedef(ctx, name),
        so::Kind::Method(so::ReceiverClass::ClassName(c_name), method_name) => {
            // Classes on typing heap have all the methods from inheritance hierarchy
            // folded together, so we will correctly identify them even if method_name
            // is not defined directly in class c_name
            let class_ = get_class(ctx, c_name)?;
            if method_name == sn::members::__CONSTRUCT {
                match folded_class::construct(&class_).0 {
                    Some(m) => Some(T::Method {
                        class_name: m.ce_origin.clone(),
                        name: method_name.clone(),
                    }),
                    None => {
                        let kind = folded_class::kind(&class_);
                        Some(T::Class {
                            kind,
                            name: c_name.clone(),
                        })
                    }
                }
            } else {
                let m = match folded_class::get_method(&class_, method_name) {
                    Some(m) => Some(m),
                    None => match folded_class::get_smethod(&class_, method_name) {
                        Some(m) => Some(m),
                        // Method not found in class - check require constraints for traits
                        None => folded_class::get_smethod_from_req_constraints(&class_, method_name, get_class_),
                    },
                };
                m.map(|m| T::Method {
                    class_name: m.ce_origin.clone(),
                    name: method_name.clone(),
                })
            }
        }
        so::Kind::Property(so::ReceiverClass::ClassName(c_name), property_name)
        | so::Kind::XhpLiteralAttr(c_name, property_name) => {
            let class_ = get_class(ctx, c_name)?;
            let clean_member_name = identify_symbol_service::clean_member_name(property_name);
            let m = match folded_class::get_prop(&class_, &clean_member_name) {
                Some(m) => Some(m),
                None => match folded_class::get_sprop(&class_, &format!("${}", clean_member_name)) {
                    Some(m) => Some(m),
                    // Property not found in class - check require constraints for traits
                    None => folded_class::get_sprop_from_req_constraints(
                        &class_,
                        &format!("${}", clean_member_name),
                        get_class_,
                    ),
                },
            };
            m.map(|m| T::Property {
                class_name: m.ce_origin.clone(),
                name: clean_member_name,
            })
        }
        so::Kind::Property(so::ReceiverClass::UnknownClass, _) => None,
        so::Kind::ClassConst(so::ReceiverClass::ClassName(_), c) if c == "class" => None,
        so::Kind::ClassConst(so::ReceiverClass::ClassName(c_name), const_name) => {
            let class_ = get_class(ctx, c_name)?;
            let origin = get_only_const(&class_, const_name)?;
            Some(T::ClassConst {
                class_name: origin,
                name: const_name.clone(),
            })
        }
        so::Kind::ClassConst(so::ReceiverClass::UnknownClass, _) => None,
        so::Kind::EnumClassLabel(class_name, name) => {
            // An enum class is a classish with class constants.
            let class_ = get_class(ctx, class_name)?;
            let origin = get_only_const(&class_, name)?;
            Some(T::ClassConst {
                class_name: origin,
                name: name.clone(),
            })
        }
        so::Kind::Function => {
            let _fun_decl = decl_entry::to_option(decl_provider::get_fun(None, ctx, name))?;
            Some(T::Function { name: name.clone() })
        }
        so::Kind::GConst => Some(T::GlobalConst { name: name.clone() }),
        so::Kind::Typeconst(c_name, typeconst_name) => {
            let class_ = get_class(ctx, c_name)?;
            let m = folded_class::get_typeconst(&class_, typeconst_name)?;
            Some(T::Typeconst {
                class_name: m.origin.as_str().to_string(),
                name: typeconst_name.clone(),
            })
        }
        so::Kind::Module => Some(T::Module { name: name.clone() }),
        so::Kind::LocalVar => None,
        so::Kind::TypeVar => None,
        so::Kind::HhFixme => None,
        so::Kind::HhIgnore => None,
        so::Kind::Method(so::ReceiverClass::UnknownClass, _) => None,
        so::Kind::Keyword(_) => None,
        so::Kind::PureFunctionContext => None,
        so::Kind::BuiltInType(_) => None,
        so::Kind::BestEffortArgument(..) => None,
    }
}

pub fn get_kind(ctx: &provider_context::T, class_: &str) -> Option<ClassishKind> {
    let class_decl = get_class(ctx, class_)?;
    Some(folded_class::kind(&class_decl))
}

pub fn get_overridden_method_origin(
    ctx: &provider_context::T,
    class_name: &str,
    method_name: &str,
    is_static: bool,
) -> Result<Option<(String, predicate::ParentContainerType)>, predicate::Failure> {
    let method_ = match decl_entry::to_option(decl_provider::get_overridden_method(
        ctx,
        class_name,
        method_name,
        is_static,
    )) {
        Some(m) => m,
        None => return Ok(None),
    };
    let origin = method_.ce_origin.clone();
    let kind = match get_kind(ctx, &origin) {
        Some(k) => k,
        None => return Ok(None),
    };
    Ok(Some((origin, predicate::get_parent_kind(&kind)?)))
}

/// file in which a t is defined
pub fn filename(ctx: &provider_context::T, t: &T) -> Option<RelativePath> {
    match t {
        T::Function { name } => naming_provider::get_fun_path(ctx, name),
        T::Module { name } => naming_provider::get_module_path(ctx, name),
        T::Class { name, .. } => naming_provider::get_class_path(ctx, name),
        T::Typedef { name } => naming_provider::get_typedef_path(ctx, name),
        T::GlobalConst { name } => naming_provider::get_const_path(ctx, name),
        T::Method { class_name, .. }
        | T::Property { class_name, .. }
        | T::ClassConst { class_name, .. }
        | T::Typeconst { class_name, .. } => naming_provider::get_class_path(ctx, class_name),
    }
}
