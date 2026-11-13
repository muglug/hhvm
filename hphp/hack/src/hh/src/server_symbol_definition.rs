// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_symbol_definition.ml`. See
//! `hh/PORTING.md`.
//!
//! Owned by **F1** (plan §7.3).
//!
//! `Ide_parser_cache.with_ide_cache` (which only makes the AST provider cache
//! the parses it makes while `f` runs) is not called: nothing outside the
//! process can see whether the parse was cached.
//!
//! The CST of `get_definition_cst_node_from_pos` is
//! `identify_symbol_service::compute_cst` (see there); the node it returns
//! is a copy of the node of that tree.

use std::sync::Arc;

use oxidized::aast;
use oxidized::nast;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax_kind::SyntaxKind;
use parser_core_types::syntax_trait::SyntaxTrait;

use crate::ctx::Ctx;
use crate::decl_entry;
use crate::decl_provider;
use crate::file_content;
use crate::file_outline;
use crate::folded_class as cls;
use crate::full_fidelity_source_text as source_text;
use crate::naming_provider;
use crate::pos::Pos;
use crate::provider_context;
use crate::symbol_definition;
use crate::symbol_occurrence as so;

/// Element type, class name, element name. Class name refers to "origin" class,
/// we expect to find said element in AST/NAST of this class
type ClassElement<'a> = (ClassElement_, &'a str, &'a str);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClassElement_ {
    Constructor,
    Method,
    StaticMethod,
    Property,
    StaticProperty,
    ClassConst,
    Typeconst,
}

pub fn get_class_by_name(ctx: &provider_context::T, x: &str) -> Option<nast::Class_> {
    let fn_ = naming_provider::get_type_path(ctx, x)?;
    crate::ast_provider::find_class_in_file(false, ctx, &fn_, x)
}

fn get_function_by_name(ctx: &provider_context::T, x: &str) -> Option<nast::FunDef> {
    let fn_ = naming_provider::get_fun_path(ctx, x)?;
    crate::ast_provider::find_fun_in_file(false, ctx, &fn_, x)
}

fn get_gconst_by_name(ctx: &provider_context::T, x: &str) -> Option<nast::Gconst> {
    let fn_ = naming_provider::get_const_path(ctx, x)?;
    crate::ast_provider::find_gconst_in_file(false, ctx, &fn_, x)
}

fn get_module_def_by_name(ctx: &provider_context::T, x: &str) -> Option<nast::ModuleDef> {
    let md = naming_provider::get_module_path(ctx, x)?;
    crate::ast_provider::find_module_in_file(false, ctx, &md, x)
}

/// Span information is stored only in parsing AST
fn get_member_def(ctx: &provider_context::T, x: ClassElement<'_>) -> Option<symbol_definition::T<Pos>> {
    let (type_, member_origin, member_name) = x;
    let c = get_class_by_name(ctx, member_origin)?;
    let member_origin = crate::utils::strip_ns(member_origin);
    match type_ {
        ClassElement_::Constructor | ClassElement_::Method | ClassElement_::StaticMethod => {
            let m = c.methods.iter().find(|m| m.name.1 == member_name)?;
            Some(file_outline::summarize_method(member_origin, m))
        }
        ClassElement_::Property | ClassElement_::StaticProperty => {
            let props: Vec<&nast::ClassVar> = c
                .vars
                .iter()
                .chain(c.xhp_attrs.iter().map(|aast::XhpAttr(_, var, _, _)| var))
                .collect();
            let get_prop_name = |cv: &nast::ClassVar| -> String { cv.id.1.clone() };
            let p = props.into_iter().find(|p| get_prop_name(p) == member_name)?;
            Some(file_outline::summarize_property(member_origin, p))
        }
        ClassElement_::ClassConst => {
            let (consts, abs_consts): (Vec<&nast::ClassConst>, Vec<&nast::ClassConst>) =
                c.consts.iter().partition(|cc| match &cc.kind {
                    aast::ClassConstKind::CCConcrete(_) | aast::ClassConstKind::CCAbstract(Some(_)) => {
                        true
                    }
                    aast::ClassConstKind::CCAbstract(None) => false,
                });
            let name_matches = |cc: &&&nast::ClassConst| cc.id.1 == member_name;
            let res = match consts.iter().find(name_matches) {
                Some(cc) => Some(*cc),
                None => abs_consts.iter().find(name_matches).copied(),
            };
            res.map(|cc| file_outline::summarize_class_const(member_origin, cc))
        }
        ClassElement_::Typeconst => {
            let tconsts = &c.typeconsts;
            let t = tconsts.iter().find(|t| t.name.1 == member_name)?;
            Some(file_outline::summarize_class_typeconst(member_origin, t))
        }
    }
}

fn get_local_var_def(ast: &nast::Program, name: &str, p: &Pos) -> Option<symbol_definition::T<Pos>> {
    let (line, char, _) = crate::pos::info_pos(p);
    let pos = file_content::position::from_one_based(line, char);
    let def = crate::server_find_locals::go_from_ast(ast, &pos).into_iter().next();
    def.map(|def| file_outline::summarize_local(name, &def))
}

/// summarize a class, typedef or record
fn summarize_class_typedef(ctx: &provider_context::T, x: &str) -> Option<symbol_definition::T<Pos>> {
    let (fn_, ct) = naming_provider::get_type_path_and_kind(ctx, x)?;
    match ct {
        oxidized::naming_types::KindOfType::TClass => {
            let c = crate::ast_provider::find_class_in_file(false, ctx, &fn_, x)?;
            Some(file_outline::summarize_class(&c, true))
        }
        oxidized::naming_types::KindOfType::TTypedef => {
            let tdef = crate::ast_provider::find_typedef_in_file(false, ctx, &fn_, x)?;
            Some(file_outline::summarize_typedef(&tdef))
        }
    }
}

pub fn go(
    ctx: &provider_context::T,
    ast: Option<&nast::Program>,
    result: &so::T<Pos>,
) -> Option<symbol_definition::T<Pos>> {
    let get_class =
        |ctx: &Arc<Ctx>, class_name: &str| decl_entry::to_option(decl_provider::get_class(None, ctx, class_name));
    let get_decl_class = |c_name: &str| decl_entry::to_option(decl_provider::get_class(None, ctx, c_name));
    match &result.type_ {
        so::Kind::Attribute(Some(so::OverrideInfo {
            class_name,
            method_name,
            is_static,
        })) => {
            let matching_method =
                decl_provider::get_overridden_method(ctx, class_name, method_name, *is_static);
            match matching_method {
                decl_entry::T::Found(meth) => {
                    get_member_def(ctx, (ClassElement_::Method, &meth.ce_origin, method_name))
                }
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
            }
        }
        so::Kind::Attribute(None) => summarize_class_typedef(ctx, &result.name),
        so::Kind::Method(so::ReceiverClass::ClassName(c_name), method_name) => {
            // Classes on typing heap have all the methods from inheritance hierarchy
            // folded together, so we will correctly identify them even if method_name
            // is not defined directly in class c_name
            let class_ = get_decl_class(c_name)?;
            if method_name == naming_special_names_rust::members::__CONSTRUCT {
                match cls::construct(&class_).0 {
                    Some(m) => get_member_def(ctx, (ClassElement_::Constructor, &m.ce_origin, method_name)),
                    None => {
                        let c = get_class_by_name(ctx, c_name)?;
                        Some(file_outline::summarize_class(&c, true))
                    }
                }
            } else {
                match cls::get_method(&class_, method_name) {
                    Some(m) => get_member_def(ctx, (ClassElement_::Method, &m.ce_origin, method_name)),
                    None => match cls::get_smethod(&class_, method_name) {
                        Some(m) => {
                            get_member_def(ctx, (ClassElement_::StaticMethod, &m.ce_origin, method_name))
                        }
                        None => {
                            // Method not found in class - check require constraints for traits
                            let m = cls::get_smethod_from_req_constraints(&class_, method_name, get_class)?;
                            get_member_def(ctx, (ClassElement_::StaticMethod, &m.ce_origin, method_name))
                        }
                    },
                }
            }
        }
        so::Kind::Method(so::ReceiverClass::UnknownClass, _) => None,
        so::Kind::Keyword(_) => None,
        so::Kind::PureFunctionContext => None,
        so::Kind::BuiltInType(_) => None,
        so::Kind::BestEffortArgument(..) => None,
        so::Kind::Property(so::ReceiverClass::ClassName(c_name), property_name)
        | so::Kind::XhpLiteralAttr(c_name, property_name) => {
            let class_ = get_decl_class(c_name)?;
            let property_name = crate::identify_symbol_service::clean_member_name(property_name);
            match cls::get_prop(&class_, &property_name) {
                Some(m) => get_member_def(ctx, (ClassElement_::Property, &m.ce_origin, &property_name)),
                None => match cls::get_sprop(&class_, &format!("${}", property_name)) {
                    Some(m) => get_member_def(
                        ctx,
                        (ClassElement_::StaticProperty, &m.ce_origin, &property_name),
                    ),
                    None => {
                        // Property not found in class - check require constraints for traits
                        let m = cls::get_sprop_from_req_constraints(
                            &class_,
                            &format!("${}", property_name),
                            get_class,
                        )?;
                        get_member_def(
                            ctx,
                            (ClassElement_::StaticProperty, &m.ce_origin, &property_name),
                        )
                    }
                },
            }
        }
        so::Kind::Property(so::ReceiverClass::UnknownClass, _) => None,
        so::Kind::ClassConst(so::ReceiverClass::ClassName(c_name), const_name) => {
            let class_ = get_decl_class(c_name)?;
            let m = cls::get_const(&class_, const_name)?;
            get_member_def(ctx, (ClassElement_::ClassConst, m.origin.as_str(), const_name))
        }
        so::Kind::ClassConst(so::ReceiverClass::UnknownClass, _) => None,
        so::Kind::EnumClassLabel(class_name, member_name) => {
            // An enum class is a classish with class constants.
            let class_ = get_decl_class(class_name)?;
            let m = cls::get_const(&class_, member_name)?;
            get_member_def(ctx, (ClassElement_::ClassConst, m.origin.as_str(), member_name))
        }
        so::Kind::Function => {
            let f = get_function_by_name(ctx, &result.name)?;
            Some(file_outline::summarize_fun(&f))
        }
        so::Kind::GConst => {
            let cst = get_gconst_by_name(ctx, &result.name)?;
            Some(file_outline::summarize_gconst(&cst))
        }
        so::Kind::Class(_) => summarize_class_typedef(ctx, &result.name),
        so::Kind::Typeconst(c_name, typeconst_name) => {
            let class_ = get_decl_class(c_name)?;
            let m = cls::get_typeconst(&class_, typeconst_name)?;
            get_member_def(ctx, (ClassElement_::Typeconst, m.origin.as_str(), typeconst_name))
        }
        so::Kind::LocalVar => match ast {
            None => None,
            Some(ast) => get_local_var_def(ast, &result.name, &result.pos),
        },
        so::Kind::TypeVar => match ast {
            None => None,
            Some(ast) => crate::server_find_type_var::go(ast, &result.pos, &result.name),
        },
        so::Kind::HhFixme => None,
        so::Kind::HhIgnore => None,
        so::Kind::Module => {
            let md = get_module_def_by_name(ctx, &result.name)?;
            Some(file_outline::summarize_module_def(&md))
        }
    }
}

/// `Full_fidelity_positioned_syntax.parentage node position`: the nodes
/// that contain the offset `position`, innermost first.
fn parentage(node: &PositionedSyntax, position: isize) -> Vec<&PositionedSyntax> {
    fn aux<'a>(
        nodes: impl Iterator<Item = &'a PositionedSyntax>,
        mut position: isize,
        acc: &mut Vec<&'a PositionedSyntax>,
    ) {
        for h in nodes {
            let width = h.full_width() as isize;
            if position < width {
                acc.push(h);
                return aux(h.iter_children(), position, acc);
            } else {
                position -= width
            }
        }
    }
    let mut acc = vec![];
    aux(std::iter::once(node), position, &mut acc);
    acc.reverse();
    acc
}

fn get_definition_cst_node_from_pos<P: crate::pos::APos>(
    _ctx: &provider_context::T,
    entry: &provider_context::Entry,
    kind: &symbol_definition::Kind<P>,
    pos: &P,
) -> Option<PositionedSyntax> {
    // `try ... with _ -> None`: the exceptions are those of reading the file
    // and `Position_not_found`, both panics here.
    let (tree, offset) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let source_text = crate::ast_provider::compute_source_text(entry);
        let (_, tree) = crate::identify_symbol_service::compute_cst(entry);
        let (line, start, _) = crate::pos::info_pos(pos);
        let offset = source_text::position_to_offset(&source_text, (line, start));
        (tree, offset)
    }))
    .ok()?;
    let parents = parentage(&tree, offset);
    parents
        .into_iter()
        .find(|syntax| {
            use symbol_definition::ClassishKind as CK;
            use symbol_definition::Kind as K;
            use symbol_definition::MemberKind as MK;
            matches!(
                (kind, syntax.kind()),
                (K::Function, SyntaxKind::FunctionDeclaration)
                    | (
                        K::Classish {
                            classish_kind: CK::Class,
                            ..
                        },
                        SyntaxKind::ClassishDeclaration
                    )
                    | (
                        K::Member {
                            member_kind: MK::Method,
                            ..
                        },
                        SyntaxKind::MethodishDeclaration
                    )
                    | (
                        K::Member {
                            member_kind: MK::Property,
                            ..
                        },
                        SyntaxKind::PropertyDeclaration
                    )
                    | (
                        K::Member {
                            member_kind: MK::Property,
                            ..
                        },
                        SyntaxKind::XHPClassAttribute
                    )
                    | (
                        K::Member {
                            member_kind: MK::ClassConst,
                            ..
                        },
                        SyntaxKind::ConstDeclaration
                    )
                    | (K::GlobalConst, SyntaxKind::ConstDeclaration)
                    | (
                        K::Member {
                            member_kind: MK::ClassConst,
                            ..
                        },
                        SyntaxKind::EnumClassEnumerator
                    )
                    | (
                        K::Member {
                            member_kind: MK::ClassConst,
                            ..
                        },
                        SyntaxKind::Enumerator
                    )
                    | (
                        K::Classish {
                            classish_kind: CK::Enum,
                            ..
                        },
                        SyntaxKind::EnumDeclaration
                    )
                    | (
                        K::Classish {
                            classish_kind: CK::Enum,
                            ..
                        },
                        SyntaxKind::EnumClassDeclaration
                    )
                    | (
                        K::Classish {
                            classish_kind: CK::Interface,
                            ..
                        },
                        SyntaxKind::ClassishDeclaration
                    )
                    | (
                        K::Classish {
                            classish_kind: CK::Trait,
                            ..
                        },
                        SyntaxKind::ClassishDeclaration
                    )
                    | (K::LocalVar, SyntaxKind::VariableExpression)
                    | (
                        K::Member {
                            member_kind: MK::TypeConst,
                            ..
                        },
                        SyntaxKind::TypeConstDeclaration
                    )
                    | (K::Param, SyntaxKind::ParameterDeclaration)
                    | (K::Typedef, SyntaxKind::AliasDeclaration)
            )
        })
        .cloned()
}

pub fn get_definition_cst_node_ctx<P: crate::pos::APos>(
    ctx: &provider_context::T,
    entry: &provider_context::Entry,
    kind: &symbol_definition::Kind<P>,
    pos: &P,
) -> Option<PositionedSyntax> {
    get_definition_cst_node_from_pos(ctx, entry, kind, pos)
}
