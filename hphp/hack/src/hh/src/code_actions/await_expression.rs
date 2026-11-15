// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/await_expression.ml`.
//! See `hh/PORTING.md`.

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::token_kind::TokenKind;

use super::aast_reduce;
use super::aast_reduce::NastParams;
use super::aast_reduce::Reducer;
use super::aast_reduce::SNode;
use super::code_action_types as cat;
use super::code_actions_utils as cu;
use crate::ast_provider;
use crate::full_fidelity_source_text as source_text;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor::IterParams;
use crate::typing_defs_core;
use crate::typing_defs_core::Ty_;

#[derive(Clone, Debug)]
struct Candidate {
    expr_pos: Pos,
    containing_stmt_pos: Pos,
}

fn offset_of_pos(st: &source_text::T, pos: &Pos) -> isize {
    let (line, start, _) = crate::pos::info_pos(pos);
    source_text::position_to_offset(st, (line, start))
}

type Acc = Option<Candidate>;

struct Visitor<'s> {
    selection: &'s Pos,
    expr_positions_overlapping_selection: Vec<Pos>,
    in_await: bool,
    stmt_pos: Option<Pos>,
}

impl Visitor<'_> {
    /// We don't want to provide the refactoring in cases like this:
    ///    /*range-start*/
    ///    $x = 1;
    ///    $y = gen_foo();
    ///    /*range-end*/
    fn ensure_valid_selection(&self, c: Acc) -> Acc {
        c.filter(|candidate| {
            self.expr_positions_overlapping_selection
                .iter()
                .all(|p| crate::pos::contains(&candidate.expr_pos, p))
        })
    }
}

impl<'a> Reducer<'a, IterParams, Acc> for Visitor<'_> {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Acc> {
        self
    }
    fn zero(&mut self) -> Acc {
        None
    }
    fn plus(&mut self, a: Acc, b: Acc) -> Acc {
        a.or(b)
    }
    aast_reduce::tast::tast_methods!('a, Acc; method_, class_var, expression_tree);

    fn visit_def(&mut self, env: &mut Env, def: &'a tast::Def) -> Acc {
        let def_pos = match def {
            aast::Def::Fun(fun_def) => fun_def.fun.span.clone(),
            aast::Def::Class(class_def) => class_def.span.clone(),
            aast::Def::Stmt(stmt) => stmt.0.clone(),
            _ => Pos::NONE,
        };
        // Avoid expensive unnecessary traversals
        if crate::pos::contains(&def_pos, self.selection) {
            let r = def.srecurse(env, self);
            self.ensure_valid_selection(r)
        } else {
            None
        }
    }

    fn visit_fun_(&mut self, env: &mut Env, fun_: &'a tast::Fun_) -> Acc {
        self.in_await = false;
        aast_reduce::tast::on_fun_(self, env, fun_)
    }

    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Acc {
        if let aast::Expr_::Await(_) = expr_ {
            // `on_Await`
            self.in_await = true;
        }
        aast_reduce::tast::on_expr_(self, env, expr_)
    }

    fn visit_stmt(&mut self, env: &mut Env, stmt: &'a tast::Stmt) -> Acc {
        self.stmt_pos = Some(stmt.0.clone());
        stmt.srecurse(env, self)
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Acc {
        let aast::Expr(ty, expr_pos, _) = expr;
        if crate::pos::contains(self.selection, expr_pos) {
            self.expr_positions_overlapping_selection.push(expr_pos.clone());
        }
        match expr.srecurse(env, self) {
            None if crate::pos::contains(self.selection, expr_pos) => {
                let needs_await = match typing_defs_core::get_node(ty) {
                    Ty_::Tclass((_, c_name), _, _) => !self.in_await && c_name == sn::classes::AWAITABLE,
                    _ => false,
                };
                if needs_await {
                    self.stmt_pos.as_ref().map(|containing_stmt_pos| Candidate {
                        expr_pos: expr_pos.clone(),
                        containing_stmt_pos: containing_stmt_pos.clone(),
                    })
                } else {
                    None
                }
            }
            candidate_opt => candidate_opt,
        }
    }
}

fn find_candidate(ctx: &provider_context::T, tast: &[tast::Def], selection: &Pos) -> Acc {
    let mut v = Visitor {
        selection,
        expr_positions_overlapping_selection: vec![],
        in_await: false,
        stmt_pos: None,
    };
    aast_reduce::tast::go(&mut v, ctx, tast)
}

fn calc_modifier_and_signature_edits(
    path: &RelativePath,
    st: &source_text::T,
    root: &PositionedSyntax,
    pos: &Pos,
) -> Option<Vec<cat::Edit>> {
    let pos_of_offset = |offset: isize| -> Pos {
        let (line, col) = cu::offset_to_position(st, offset);
        let bol = offset - col + 1;
        let triple = (line, bol, offset);
        crate::pos::make_from_lnum_bol_offset(path.clone(), triple, triple)
    };
    let signature_edit_of_type_node = |type_node: &PositionedSyntax| -> Option<cat::Edit> {
        let return_type_string = cu::text(st, type_node);
        if !type_node.is_missing()
            && !return_type_string.starts_with("Awaitable")
            && !return_type_string.starts_with("~Awaitable")
        {
            let return_type_offset = cu::start_offset(type_node);
            let pos = {
                let start_pos = pos_of_offset(return_type_offset);
                let end_pos = pos_of_offset(cu::end_offset(type_node) + 1);
                crate::pos::merge(&start_pos, &end_pos)
            };
            let text = format!("Awaitable<{}>", return_type_string);
            Some(cat::Edit { pos, text })
        } else {
            None
        }
    };
    let parents = cu::parentage(root, offset_of_pos(st, pos));
    parents.into_iter().find_map(|node| match &node.syntax {
        SyntaxVariant::LambdaExpression(x) => {
            let modifier_node = &x.lambda_async;
            let signature_edit_opt = match &x.lambda_signature.syntax {
                SyntaxVariant::LambdaSignature(s) => signature_edit_of_type_node(&s.lambda_type),
                _ => None,
            };
            let modifier_edit_opt = match &modifier_node.syntax {
                SyntaxVariant::Missing => {
                    let offset = cu::start_offset(modifier_node);
                    Some(cat::Edit {
                        pos: pos_of_offset(offset),
                        text: "async ".to_string(),
                    })
                }
                _ => None,
            };
            Some(
                [signature_edit_opt, modifier_edit_opt]
                    .into_iter()
                    .flatten()
                    .collect(),
            )
        }
        SyntaxVariant::FunctionDeclaration(x) => header_edits(&x.function_declaration_header, &signature_edit_of_type_node, &pos_of_offset),
        SyntaxVariant::MethodishDeclaration(x) => {
            header_edits(&x.methodish_function_decl_header, &signature_edit_of_type_node, &pos_of_offset)
        }
        _ => None,
    })
}

/// The edits of a `FunctionDeclaration` or `MethodishDeclaration` whose
/// header is a `FunctionDeclarationHeader` (else no match).
fn header_edits(
    header: &PositionedSyntax,
    signature_edit_of_type_node: &dyn Fn(&PositionedSyntax) -> Option<cat::Edit>,
    pos_of_offset: &dyn Fn(isize) -> Pos,
) -> Option<Vec<cat::Edit>> {
    match &header.syntax {
        SyntaxVariant::FunctionDeclarationHeader(h) => {
            let signature_edit_opt = signature_edit_of_type_node(&h.function_type);
            let modifier_edit_opt = {
                let has_async = match &h.function_modifiers.syntax {
                    SyntaxVariant::SyntaxList(elements) => elements.iter().any(|e| match &e.syntax {
                        SyntaxVariant::Token(t) => t.kind == TokenKind::Async,
                        _ => false,
                    }),
                    SyntaxVariant::Missing => false,
                    _ => false,
                };
                if has_async {
                    None
                } else {
                    let function_keyword_offset = cu::start_offset(&h.function_keyword);
                    Some(cat::Edit {
                        pos: pos_of_offset(function_keyword_offset),
                        text: "async ".to_string(),
                    })
                }
            };
            Some(
                [signature_edit_opt, modifier_edit_opt]
                    .into_iter()
                    .flatten()
                    .collect(),
            )
        }
        _ => None,
    }
}

fn text_before_and_after_expr_in_stmt(st: &source_text::T, c: &Candidate) -> (String, String) {
    let stmt_offset = offset_of_pos(st, &c.containing_stmt_pos);
    let expr_offset = offset_of_pos(st, &c.expr_pos);
    let expr_end_offset = offset_of_pos(st, &crate::pos::shrink_to_end(&c.expr_pos));
    let stmt_end_offset = offset_of_pos(st, &crate::pos::shrink_to_end(&c.containing_stmt_pos));
    let before_text = cu::to_string(source_text::sub(st, stmt_offset, expr_offset - stmt_offset));
    let after_text = cu::to_string(source_text::sub(st, expr_end_offset, stmt_end_offset - expr_end_offset));
    (before_text, after_text)
}

/// Enables us to distinguish whether a change to source code affects the structure of expressions in the AST.
///
/// We only pay attention to the shape of the tree, not what's in a node.
mod expr_structure {
    use super::*;

    #[derive(PartialEq, Eq, Debug)]
    enum T {
        Zero,
        Plus(Box<T>, Box<T>),
        OnExpr(Box<T>),
    }

    struct Visitor;

    impl<'a> Reducer<'a, NastParams, T> for Visitor {
        fn object(&mut self) -> &mut dyn Reducer<'a, NastParams, T> {
            self
        }
        fn zero(&mut self) -> T {
            T::Zero
        }
        fn plus(&mut self, a: T, b: T) -> T {
            T::Plus(Box::new(a), Box::new(b))
        }
        fn visit_expr(&mut self, env: &mut (), expr: &'a aast::Expr<(), ()>) -> T {
            T::OnExpr(Box::new(expr.srecurse(env, self)))
        }
    }

    fn of_nast(nast: &aast::Program<(), ()>) -> T {
        nast.saccept(&mut (), &mut Visitor)
    }

    fn nast_of_program_source_code(popt: &oxidized::parser_options::ParserOptions, s: &str) -> aast::Program<(), ()> {
        let source_text = source_text::make(&crate::relative_path::DEFAULT, s.as_bytes());
        let parser_env = crate::full_fidelity_ast::make_env(
            None,
            None,
            None,
            None,
            Some(false),
            None,
            Some(popt.clone()),
            None,
            crate::relative_path::DEFAULT.clone(),
        );
        let crate::parser_return::T { ast, .. } =
            crate::full_fidelity_ast::from_source_text_with_legacy(&parser_env, &source_text);
        ast
    }

    /// Convert a statement into a program, so we can parse it.
    /// We include an extra semicolon because not all statements end in semicolons.
    /// For example, in braceless lambdas: `() ==> expr_statement`.
    /// Double-semicolon parses OK, so we're all right.
    fn wrap_as_program(s: &str) -> String {
        format!("<?hh\nfunction foo(): void {{ {}; }}", s)
    }

    fn of_stmt_source_code(popt: &oxidized::parser_options::ParserOptions, statement_source_code: &str) -> T {
        of_nast(&nast_of_program_source_code(popt, &wrap_as_program(statement_source_code)))
    }

    pub fn equiv(popt: &oxidized::parser_options::ParserOptions, stmt1: &str, stmt2: &str) -> bool {
        let structure1 = of_stmt_source_code(popt, stmt1);
        let structure2 = of_stmt_source_code(popt, stmt2);
        structure1 == structure2
    }
}

fn calc_await_edit(ctx: &provider_context::T, st: &source_text::T, candidate: &Candidate) -> cat::Edit {
    let (before_text, after_text) = text_before_and_after_expr_in_stmt(st, candidate);
    let orig_expr_text = cu::to_string(cu::sub_of_pos(st, &candidate.expr_pos));
    let with_parentheses = format!("{}(await {}){}", before_text, orig_expr_text, after_text);
    let without_parentheses = format!("{}await {}{}", before_text, orig_expr_text, after_text);
    let text = {
        let popt = provider_context::get_popt(ctx);
        if expr_structure::equiv(popt, &with_parentheses, &without_parentheses) {
            without_parentheses
        } else {
            with_parentheses
        }
    };
    cat::Edit {
        pos: candidate.containing_stmt_pos.clone(),
        text,
    }
}

fn edits_of_candidate(ctx: &provider_context::T, entry: &provider_context::Entry, candidate: &Candidate) -> Vec<cat::Edit> {
    let path = &entry.path;
    let st = ast_provider::compute_source_text(entry);
    let (_, positioned_tree) = crate::ast_provider::compute_cst(entry);
    let mut modifier_and_signature_edits =
        calc_modifier_and_signature_edits(path, &st, &positioned_tree, &candidate.expr_pos).unwrap_or_default();
    let await_edit = calc_await_edit(ctx, &st, candidate);
    modifier_and_signature_edits.push(await_edit);
    modifier_and_signature_edits
}

fn refactor_of_candidate<'a>(
    ctx: &'a provider_context::T,
    entry: &'a provider_context::Entry,
    candidate: Candidate,
) -> cat::Refactor<'a> {
    let edits: cat::LazyEdits<'a> =
        Box::new(move || cat::singleton(entry.path.clone(), edits_of_candidate(ctx, entry, &candidate)));
    cat::Refactor(cat::EditData {
        title: "await expression".to_string(),
        edits,
        selection: None,
        trigger_inline_suggest: false,
    })
}

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    selection: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    if crate::pos::length(selection) != 0 {
        let tast_provider::ComputeTast { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
        find_candidate(ctx, &tast.under_normal_assumptions, selection)
            .map(|c| refactor_of_candidate(ctx, entry, c))
            .into_iter()
            .collect()
    } else {
        vec![]
    }
}
