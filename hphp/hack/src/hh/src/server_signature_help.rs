// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_signature_help.ml`.

use std::sync::Arc;

use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::syntax_trait::SyntaxTrait;

use crate::ast_provider;
use crate::docblock_parser;
use crate::file_content::position;
use crate::full_fidelity_source_text as source_text;
use crate::identify_symbol_service;
use crate::lsp::signature_help;
use crate::pos::Pos;
use crate::provider_context;
use crate::server_docblock_at;
use crate::server_infer_type;
use crate::server_symbol_definition;
use crate::symbol_occurrence as so;
use crate::tast_env;
use crate::tast_provider;
use crate::typing_defs;
use crate::utils;

/// `Syntax.children` of a list node (the argument list): its elements.
fn children(node: &PositionedSyntax) -> Vec<&PositionedSyntax> {
    node.iter_children().collect()
}

/// `Syntax.trailing_end_offset`
fn trailing_end_offset(node: &PositionedSyntax) -> usize {
    node.leading_start_offset() + node.full_width().saturating_sub(1)
}

/// Returns ((symbol_line, symbol_char), argument_idx) where:
/// - symbol_line: the line number of the function symbol
/// - symbol_char: the column number of the function symbol
/// - argument_idx: index of the function argument that contains the offset.
///
/// For example, given this line:
///
/// ```text
///     25:    $myObject->foo(true, null);
///     offset:                    ^
/// ```
///
/// We would return the following:
///
///     Some ((25, 16), 1)
///
/// Returns None if the given offset is not inside a function call.
fn get_positional_info(
    source_text: &IndexedSourceText<'_>,
    cst: &PositionedSyntax,
    file_offset: usize,
) -> Option<(position::T, isize)> {
    let parent_tree = crate::full_fidelity_positioned_syntax::parentage(cst, file_offset as isize);
    // Search upwards through the parent tree.
    // If we find a function call or constructor, signature help should appear.
    // If we find a lambda first, don't offer help even if we are within a function call!
    let within_lambda = parent_tree
        .iter()
        .find_map(|syntax| match &syntax.syntax {
            SyntaxVariant::LambdaExpression(_) => Some(true),
            SyntaxVariant::ConstructorCall(_) | SyntaxVariant::FunctionCallExpression(_) => Some(false),
            _ => None,
        })
        .unwrap_or(false);
    if within_lambda {
        return None;
    }
    let (callee_node, argument_list) = parent_tree.iter().find_map(|syntax| match &syntax.syntax {
        SyntaxVariant::FunctionCallExpression(children) => {
            Some((&children.function_call_receiver, &children.function_call_argument_list))
        }
        SyntaxVariant::ConstructorCall(children) => {
            Some((&children.constructor_call_type, &children.constructor_call_argument_list))
        }
        _ => None,
    })?;
    let callee_trailing_token = callee_node.trailing_token()?;
    let function_symbol_offset = callee_trailing_token.end_offset();
    let pos = {
        let (l, c) = source_text.offset_to_position(function_symbol_offset as isize);
        position::from_one_based(l, c)
    };
    let arguments = children(argument_list);
    // Add 1 to counteract the -1 in trailing_end_offset.
    let in_args_area = argument_list.leading_start_offset() <= file_offset
        && file_offset <= trailing_end_offset(argument_list) + 1;
    if !in_args_area {
        None
    } else {
        match arguments.as_slice() {
            [] => Some((pos, 0)),
            arguments => arguments.iter().enumerate().find_map(|(idx, child)| {
                // Don't bother range checking if we're in the final argument, since we
                // already checked that in in_args_area up above.
                let matches_end = idx == arguments.len() - 1 || file_offset < trailing_end_offset(child);
                if matches_end { Some((pos, idx as isize)) } else { None }
            }),
        }
    }
}

fn get_occurrence_info(
    ctx: &provider_context::T,
    nast: &oxidized::nast::Program,
    occurrence: &so::T<Pos>,
) -> Option<crate::symbol_definition::T<Pos>> {
    let full_occurrence = match occurrence.type_ {
        so::Kind::Function => {
            let fun_name = utils::expand_namespace(
                &provider_context::get_popt(ctx).auto_namespace_map,
                &occurrence.name,
            );
            so::T {
                name: fun_name,
                ..occurrence.clone()
            }
        }
        _ => occurrence.clone(),
    };
    server_symbol_definition::go(ctx, Some(nast), &full_occurrence)
}

/// Returns signature help for the given location.
pub fn go_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &position::T,
) -> signature_help::Result {
    let source_text = ast_provider::compute_source_text(entry);
    let offset = source_text::position_to_offset(&source_text, position::line_column_one_based(pos));
    let (_, cst) = ast_provider::compute_cst(entry);
    let indexed = IndexedSourceText::new(source_text::source_text(&source_text));
    // (A negative offset is in no node.)
    let (symbol_pos, argument_idx) = if offset < 0 {
        None
    } else {
        get_positional_info(&indexed, &cst, offset as usize)
    }?;
    let results = identify_symbol_service::go_quarantined(ctx, entry, &symbol_pos, false);
    let occurrence = results
        .into_iter()
        .find(|r| matches!(r.type_, so::Kind::Method(..) | so::Kind::Function))?;
    let ast = ast_provider::compute_ast(provider_context::get_popt(ctx), entry);
    let tast_provider::ComputeTast { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    let tast_info_opt = server_infer_type::human_friendly_type_at_pos(false, ctx, &tast, &symbol_pos);
    let def_opt = get_occurrence_info(ctx, &ast, &occurrence);
    let info = tast_info_opt?;
    let ty = server_infer_type::get_type(&info).clone();
    let tast_env = server_infer_type::get_env(&info);
    // Expand splat parameters e.g.
    //   function(int $a, ...(string, bool) $b):void
    // will be shown as
    //   function(int $a, string $b[0], bool $b[1]):void
    let ty = tast_env::expand_splat_param_in_function_type(tast_env, ty);
    let siginfo_label = tast_env::print_ty_with_identity(tast_env, ty.clone(), &occurrence, def_opt.as_ref());
    let siginfo_documentation = {
        let base_class_name = so::enclosing_class(&occurrence);
        def_opt.as_ref().and_then(|def| {
            let path = def.pos.filename().clone();
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            server_docblock_at::go_comments_for_symbol_ctx(&ctx, &entry, def, base_class_name.as_deref())
        })
    };
    let param_docs = siginfo_documentation
        .as_ref()
        .map(|siginfo_documentation| docblock_parser::get_param_docs(siginfo_documentation));
    let ft_params: Vec<typing_defs::FunParam> = match typing_defs::get_node(&ty) {
        typing_defs::Ty_::Tfun(ft) => ft.params.iter().cloned().collect(),
        _ => vec![],
    };
    let params = ft_params
        .iter()
        .map(|param| {
            let parinfo_label = match &param.name {
                Some(s) => s.clone(),
                None => tast_env::print_ty(tast_env, &ty),
            };
            let parinfo_documentation = match &param_docs {
                Some(param_docs) => param_docs.get(&parinfo_label).cloned(),
                None => None,
            };
            signature_help::ParameterInformation {
                label: parinfo_label,
                documentation: parinfo_documentation,
            }
        })
        .collect();
    let signature_information = signature_help::SignatureInformation {
        siginfo_label,
        siginfo_documentation,
        parameters: params,
    };
    Some(signature_help::T {
        signatures: vec![signature_information],
        active_signature: 0,
        active_parameter: argument_idx,
    })
}
