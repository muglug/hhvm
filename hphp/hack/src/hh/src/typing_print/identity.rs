// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_print.ml`, the part about identities:
//! `Full.to_string_with_identity` and the user API around it
//! (`full_with_identity`, `full_decl_with_identity`): the type of a symbol
//! as hover shows it.
//!
//! Unlike the other printers, the result is laid out by hackfmt's line
//! solver (`Libhackfmt.format_doc`), not on one line.

use super::full::*;
use super::*;
use crate::symbol_definition as sd;
use crate::symbol_occurrence as so;
use crate::typing_env_types::Env;

/// `print_mod m`
fn print_mod(m: &sd::Modifier) -> Doc {
    cat(text(sd::string_of_modifier(m)), Doc::Space)
}

/// The `prefix` of `to_string_with_identity`.
fn to_string_with_identity_prefix<P>(occurrence: &so::T<P>, definition_opt: Option<&sd::T<P>>) -> Doc {
    match (definition_opt, &occurrence.type_) {
        (None, _) => Doc::Nothing,
        (_, so::Kind::XhpLiteralAttr(..)) => Doc::Nothing,
        (Some(def), _) => match def.modifiers.as_slice() {
            [] => Doc::Nothing,
            // It looks weird if we line break after a single modifier.
            [m] => print_mod(m),
            ms => cat(Doc::Concat(ms.iter().map(print_mod).collect()), Doc::SplitWithBase),
        },
    }
}

fn is_function_or_method<P>(occurrence: &so::T<P>) -> bool {
    matches!(occurrence.type_, so::Kind::Function | so::Kind::Method(..))
}

/// `add_supportdyn_prefix`: for functions and methods, interpret supportdyn
/// as use of <<__SupportDynamicType>> attribute. [tyarg] is the argument of
/// the supportdyn type of [x], if it is one.
fn add_supportdyn_prefix<'t, T, P>(
    env: &Env,
    x: &'t T,
    tyarg: Option<&'t T>,
    occurrence: &so::T<P>,
    prefix: Doc,
) -> (Doc, &'t T) {
    match tyarg {
        Some(tyarg) if is_function_or_method(occurrence) => {
            if show_supportdyn(env) {
                (
                    cat(text("<<__SupportDynamicType>>"), cat(Doc::Newline, prefix)),
                    tyarg,
                )
            } else {
                (prefix, tyarg)
            }
        }
        _ => (prefix, x),
    }
}

/// The keyword of a class, as `Decl_provider.get_class` says.
fn class_keyword(env: &Env, name: &str) -> &'static str {
    use oxidized::ast_defs::ClassishKind as CK;
    match crate::decl_provider::get_class(None, &env.decl_env.ctx, name) {
        crate::decl_entry::T::Found(decl) => match crate::folded_class::kind(&decl) {
            CK::Cclass(_) => "class",
            CK::Cinterface => "interface",
            CK::Ctrait => "trait",
            CK::Cenum => "enum",
            CK::CenumClass(_) => "enum class",
        },
        crate::decl_entry::T::DoesNotExist | crate::decl_entry::T::NotYetAvailable => "class",
    }
}

/// `to_string_with_identity` once the supportdyn prefix is added: [x] is
/// the type to print, [ft] its function type if it is one.
#[allow(clippy::too_many_arguments)]
fn to_string_with_identity<T, P>(
    fuel: &mut Fuel,
    env: &Env,
    x: &T,
    ft: Option<FunTypeView<'_, T>>,
    ty: TyPrinter<'_, T>,
    is_supportdyn_mixed: &dyn Fn(&T) -> bool,
    fun_implicit_params: &dyn Fn(&mut Fuel, &[TparamView<'_, T>], &CapabilityView<'_, T>) -> Doc,
    prefix: Doc,
    constraints: Doc,
    occurrence: &so::T<P>,
) -> String {
    let name = &occurrence.name;
    let body_doc = match (&occurrence.type_, &ft) {
        (so::Kind::Class(class_id_type), _) => {
            let keyword = class_keyword(env, name);
            match class_id_type {
                so::ClassIdType::ExpressionTreeVisitor => {
                    let ty_doc = ty(fuel, x);
                    Doc::Concat(vec![
                        text(keyword),
                        Doc::Space,
                        text_strip_ns(name),
                        Doc::Newline,
                        ty_doc,
                    ])
                }
                _ => Doc::Concat(vec![text(keyword), Doc::Space, text_strip_ns(name)]),
            }
        }
        (so::Kind::Function, Some(ft)) | (so::Kind::Method(_, _), Some(ft)) => {
            let name = match &occurrence.type_ {
                so::Kind::Method(_, name) => name,
                _ => name,
            };
            // Use short names for function types since they display a lot more
            // information to the user.
            let (_, _async_doc, fun_ty_doc) =
                fun_type(fuel, ty, is_supportdyn_mixed, false, ft, fun_implicit_params);
            Doc::Concat(vec![
                text("function"),
                Doc::Space,
                text_strip_all_ns(name),
                fun_ty_doc,
            ])
        }
        (so::Kind::Property(_, name), _) => {
            let ty_doc = ty(fuel, x);
            let name = if name.starts_with('$') {
                // Static property
                name.clone()
            } else {
                // Instance property
                format!("${}", name)
            };
            Doc::Concat(vec![ty_doc, Doc::Space, text(name)])
        }
        (so::Kind::XhpLiteralAttr(..), _) => {
            let ty_doc = ty(fuel, x);
            Doc::Concat(vec![
                text("attribute"),
                Doc::Space,
                ty_doc,
                Doc::Space,
                text_strip_ns(name),
            ])
        }
        (so::Kind::ClassConst(_, name), _) => {
            let ty_doc = ty(fuel, x);
            Doc::Concat(vec![
                text("const"),
                Doc::Space,
                ty_doc,
                Doc::Space,
                text_strip_ns(name),
            ])
        }
        (so::Kind::GConst, _) | (so::Kind::EnumClassLabel(..), _) => {
            let ty_doc = ty(fuel, x);
            Doc::Concat(vec![ty_doc, Doc::Space, text_strip_ns(name)])
        }
        _ => ty(fuel, x),
    };
    let doc = Doc::Concat(vec![prefix, body_doc, constraints]);
    doc::strip(&doc::format_doc(&doc)).to_string()
}

/// `Full.to_string_locl_with_identity`
fn to_string_locl_with_identity<P>(
    fuel: &mut Fuel,
    hide_internals: bool,
    env: &Env,
    x: &Ty,
    occurrence: &so::T<P>,
    definition_opt: Option<&sd::T<P>>,
) -> String {
    let constraints = super::full::constraints_for_type(fuel, hide_internals, &text_strip_ns, env, x);
    let penv = Penv::Loclenv(env);
    let st = TvidSet::new();
    let ty = |fuel: &mut Fuel, t: &Ty| locl_ty(fuel, hide_internals, &text_strip_ns, &st, penv, t);
    let k: TyPrinter<'_, Ty> = &ty;
    let prefix = to_string_with_identity_prefix(occurrence, definition_opt);
    let tyarg = match x.get_node() {
        Ty_::Tnewtype(name, tyargs, _) if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN => {
            Some(&tyargs[0])
        }
        _ => None,
    };
    let (prefix, x) = add_supportdyn_prefix(env, x, tyarg, occurrence, prefix);
    let ft = match x.get_node() {
        Ty_::Tfun(ft) => Some(locl_views::fun_type(ft)),
        _ => None,
    };
    to_string_with_identity(
        fuel,
        env,
        x,
        ft,
        k,
        &|t| is_supportdyn_mixed_locl(penv, t),
        &|fuel, tparams, capability| fun_locl_implicit_params(fuel, k, tparams, capability),
        prefix,
        constraints,
        occurrence,
    )
}

/// `Full.to_string_decl_with_identity`
fn to_string_decl_with_identity<P>(
    fuel: &mut Fuel,
    verbose_fun: bool,
    omit_likes: bool,
    env: &Env,
    x: &DeclTy,
    occurrence: &so::T<P>,
    definition_opt: Option<&sd::T<P>>,
) -> String {
    let penv = Penv::Loclenv(env);
    let st = TvidSet::new();
    let ty = |fuel: &mut Fuel, t: &DeclTy| {
        decl_ty(fuel, &text_strip_ns, &st, penv, verbose_fun, omit_likes, t)
    };
    let k: TyPrinter<'_, DeclTy> = &ty;
    let prefix = to_string_with_identity_prefix(occurrence, definition_opt);
    let tyarg = match x.get_node() {
        decl::Ty_::Tapply((_, name), tyargs) if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN => {
            Some(&tyargs[0])
        }
        _ => None,
    };
    let (prefix, x) = add_supportdyn_prefix(env, x, tyarg, occurrence, prefix);
    let ft = match x.get_node() {
        decl::Ty_::Tfun(ft) => Some(decl_views::fun_type(ft)),
        _ => None,
    };
    to_string_with_identity(
        fuel,
        env,
        x,
        ft,
        k,
        &|t| is_supportdyn_mixed_decl(penv, t),
        &|fuel, tparams, capability| fun_decl_implicit_params(fuel, k, tparams, capability),
        prefix,
        Doc::Nothing,
        occurrence,
    )
}

/// Pretty print a type and all of its associated declaration information.
///
/// `full_with_identity ~hide_internals env x occurrence definition_opt`
pub fn full_with_identity<P>(
    hide_internals: bool,
    env: &Env,
    x: &Ty,
    occurrence: &so::T<P>,
    definition_opt: Option<&sd::T<P>>,
) -> String {
    supply_fuel(None, env.get_tcopt(), |fuel| {
        to_string_locl_with_identity(fuel, hide_internals, env, x, occurrence, definition_opt)
    })
}

/// Pretty print a type and all of its associated declaration information.
///
/// `full_decl_with_identity env ~omit_likes ~verbose_fun x occurrence definition_opt`
pub fn full_decl_with_identity<P>(
    env: &Env,
    omit_likes: bool,
    verbose_fun: bool,
    x: &DeclTy,
    occurrence: &so::T<P>,
    definition_opt: Option<&sd::T<P>>,
) -> String {
    supply_fuel(None, env.get_tcopt(), |fuel| {
        to_string_decl_with_identity(fuel, verbose_fun, omit_likes, env, x, occurrence, definition_opt)
    })
}
