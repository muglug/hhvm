// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_rewrite_lambda_parameters.ml` (the
//! `REWRITE_LAMBDA_PARAMETERS` command, through
//! `Server_rename.get_lambda_parameter_rewrite_patches`). See
//! `hh/PORTING.md`.
//!
//! `Rewriter.aggregating_rewrite_post` over the editable syntax is a
//! post-order traversal of the positioned syntax here (nothing is
//! rewritten: every node is kept); the patches of a node go before those
//! accumulated so far, as in the OCaml.

use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::syntax_trait::SyntaxTrait;

use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::server_rename_types::InsertPatch;
use crate::server_rename_types::Patch;
use crate::tast_type_collector;
use crate::type_visitor::LoclTypeVisitor;
use crate::typing_defs::PhaseTy;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;

struct Finder;

impl LoclTypeVisitor<bool> for Finder {
    fn on_tprim(&mut self, acc: bool, _r: &crate::typing_reason::T, prim: oxidized::ast_defs::Tprim) -> bool {
        use oxidized::ast_defs::Tprim;
        match prim {
            Tprim::Tnull | Tprim::Tvoid | Tprim::Tresource | Tprim::Tnoreturn => true,
            _ => acc,
        }
    }
}

fn is_not_acceptable(ty: &Ty) -> bool {
    Finder.on_type(false, ty)
}

fn print_ty(ty: &Ty) -> Option<String> {
    if is_not_acceptable(ty) {
        None
    } else {
        crate::codemod_type_printer::print(None, ty)
    }
}

struct Positions<'a> {
    file: &'a RelativePath,
    source_text: &'a crate::full_fidelity_source_text::T,
    indexed: IndexedSourceText<'a>,
}

impl Positions<'_> {
    fn pos(&self, start: usize, end: usize) -> oxidized::pos::Pos {
        let p = self.indexed.relative_pos(start, end);
        oxidized::pos::Pos::from_lnum_bol_offset(std::sync::Arc::new(self.file.clone()), p.start, p.end)
    }

    /// `Syntax.position file node`
    fn position(&self, node: &PositionedSyntax) -> oxidized::pos::Pos {
        self.pos(node.start_offset(), node.end_offset())
    }

    /// `Syntax.position_exclusive file node`
    fn position_exclusive(&self, node: &PositionedSyntax) -> oxidized::pos::Pos {
        self.pos(node.start_offset(), node.end_offset() + 1)
    }

    /// `Syntax.text node`
    fn text(&self, node: &PositionedSyntax) -> String {
        let st = crate::full_fidelity_source_text::source_text(self.source_text);
        String::from_utf8_lossy(st.sub(node.start_offset(), node.width())).into_owned()
    }
}

fn get_first_suggested_type_as_string(
    positions: &Positions<'_>,
    type_map: &tast_type_collector::CollectedTypes,
    node: &PositionedSyntax,
) -> Option<String> {
    let pos = positions.position(node);
    let tys = tast_type_collector::get_from_pos_map(&crate::pos::to_absolute(&pos), type_map)?;
    tys.into_iter().find_map(|(env, phase_ty)| match phase_ty {
        PhaseTy::LoclTy(ty) => {
            let mut env = env.clone();
            let ty = crate::tast_env::simplify_unions(&mut env, ty);
            let ty = crate::tast_env::expand_type(&mut env, ty);
            match ty.get_node() {
                Ty_::Tnewtype(name, tys, _) if name == "HackSuggest" && tys.len() == 1 => {
                    let ty = crate::tast_env::simplify_unions(&mut env, tys[0].clone());
                    let ty = crate::tast_env::fully_expand(&env, ty);
                    match print_ty(&ty) {
                        Some(type_str) => Some(type_str),
                        None => {
                            crate::hh_logger::log(&format!(
                                "{} failed to rewrite lambda parameter {}: the suggested type {} is non-denotable",
                                crate::pos::string(&crate::pos::to_absolute(&pos)),
                                positions.text(node),
                                crate::tast_env::print_ty(
                                    &env,
                                    &crate::typing_defs::mk((crate::typing_reason::none(), ty.get_node().clone()))
                                )
                            ));
                            None
                        }
                    }
                }
                _ => None,
            }
        }
        PhaseTy::DeclTy(_) => None,
    })
}

fn get_lambda_parameter_patches(
    positions: &Positions<'_>,
    type_map: &tast_type_collector::CollectedTypes,
    node: &PositionedSyntax,
) -> Vec<Patch> {
    let patch = match &node.syntax {
        SyntaxVariant::Token(_) => get_first_suggested_type_as_string(positions, type_map, node).map(|type_str| {
            let pos = positions.position_exclusive(node);
            Patch::Replace(InsertPatch {
                pos: crate::pos::to_absolute(&pos),
                text: format!("({} {})", type_str, positions.text(node)),
            })
        }),
        SyntaxVariant::ListItem(x) => match &x.list_item.syntax {
            SyntaxVariant::ParameterDeclaration(_) => {
                get_first_suggested_type_as_string(positions, type_map, &x.list_item).map(|type_str| {
                    let pos = positions.position(&x.list_item);
                    Patch::Insert(InsertPatch {
                        pos: crate::pos::to_absolute(&pos),
                        text: format!("{} ", type_str),
                    })
                })
            }
            _ => None,
        },
        _ => None,
    };
    patch.into_iter().collect()
}

fn get_lambda_expression_patches(
    positions: &Positions<'_>,
    type_map: &tast_type_collector::CollectedTypes,
    node: &PositionedSyntax,
) -> Vec<Patch> {
    match &node.syntax {
        SyntaxVariant::LambdaExpression(x) => match &x.lambda_signature.syntax {
            SyntaxVariant::Token(_) => get_lambda_parameter_patches(positions, type_map, &x.lambda_signature),
            SyntaxVariant::LambdaSignature(s) => s
                .lambda_parameters
                .syntax_node_to_list()
                .flat_map(|p| get_lambda_parameter_patches(positions, type_map, p))
                .collect(),
            _ => vec![],
        },
        _ => vec![],
    }
}

pub fn get_patches(ctx: &provider_context::T, file: &RelativePath) -> Vec<Patch> {
    let nast = crate::ast_provider::get_ast(true, ctx, file);
    // We don't need an accurate list of typing errors, so we can skip TAST
    // checks.
    let tast = crate::typing_toplevel::nast_to_tast(false, ctx, &crate::naming::program(ctx, nast));
    let type_map = tast_type_collector::collect_types(ctx, &tast.under_normal_assumptions);
    // `Full_fidelity_source_text.from_file file`: `Sys_utils.cat` raises
    // `Sys_error` when the file cannot be read (as in the OCaml: the server's
    // handler fails and the client is disconnected).
    let content = match crate::sys_utils::cat(&crate::relative_path::to_absolute(file)) {
        Ok(c) => c,
        Err(e) => std::panic::panic_any(format!("Sys_error({:?})", e.0)),
    };
    let source_text = crate::full_fidelity_source_text::make(file, &content);
    let (root, _errors, _state) = positioned_parser::parse_script(
        &crate::full_fidelity_source_text::source_text(&source_text),
        parser_core_types::parser_env::ParserEnv::default(),
    );
    let positions = Positions {
        file,
        source_text: &source_text,
        indexed: IndexedSourceText::new(crate::full_fidelity_source_text::source_text(&source_text)),
    };
    // `Rewriter.aggregating_rewrite_post`
    fn post(
        positions: &Positions<'_>,
        type_map: &tast_type_collector::CollectedTypes,
        node: &PositionedSyntax,
        patches: Vec<Patch>,
    ) -> Vec<Patch> {
        let mut patches = patches;
        for child in node.iter_children() {
            patches = post(positions, type_map, child, patches);
        }
        let mut node_patches = get_lambda_expression_patches(positions, type_map, node);
        node_patches.extend(patches);
        node_patches
    }
    post(&positions, &type_map, &root, vec![])
}
