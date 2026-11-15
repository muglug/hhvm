// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/extract_shape_type.ml`.
//! See `hh/PORTING.md`.
//!
//! `plus_state` is not associative: the visitor is an
//! [`aast_reduce::Reducer`], which combines the values as OCaml does.

use std::rc::Rc;
use std::sync::Arc;

use oxidized::aast;

use super::aast_reduce;
use super::aast_reduce::Reducer;
use super::aast_reduce::SNode;
use super::code_action_types as cat;
use super::code_action_types::type_string;
use super::code_actions_utils as cu;
use crate::ast_provider;
use crate::full_fidelity_source_text as source_text;
use crate::hack_event_logger;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor::IterParams;
use crate::typing_defs_core;
use crate::typing_defs_core::Ty_;

#[derive(Clone)]
enum Candidate {
    OfExpr {
        /// the function or class containing the shape expression
        expr_container_pos: Pos,
        shape_ty_string: Rc<type_string::T>,
    },
    OfHint {
        hint_container_pos: Pos,
        hint_pos: Pos,
    },
}

/// We use distinct titles so we can tell the refactors apart in analytics
fn title_of_candidate(c: &Candidate) -> &'static str {
    match c {
        Candidate::OfExpr { .. } => "Extract shape type",
        Candidate::OfHint { .. } => "Extract shape type to alias",
    }
}

#[derive(Clone)]
enum State {
    Searching(Option<(Pos, Candidate)>),
    SelectedNonShapeType(Pos),
}

/// When searching for an expression of shape type,
/// we don't want to provide the refactor for larger expressions
/// that happen to contain an expression of shape type.
fn plus_state(a: State, b: State) -> State {
    match (&a, &b) {
        (State::Searching(Some(_)), State::Searching(Some((pos_b, _)))) => {
            hack_event_logger::invariant_violation_bug(
                Some(pos_b.filename()),
                Some(&crate::pos::string(&crate::pos::to_absolute(pos_b))),
                None,
                None,
                None,
                "expected only one candidate to be found, since we select the largest shape-typed expression containing the selection",
            );
            // Safe to continue in spite of being in an unexpected situation:
            // We still provide *a* reasonable refactoring by picking arbitrarily
            a
        }
        (State::Searching(_), State::Searching(_)) => match (a, b) {
            (State::Searching(c1), State::Searching(c2)) => State::Searching(c1.or(c2)),
            _ => unreachable!(),
        },
        (State::Searching(Some((pos1, _))), State::SelectedNonShapeType(pos2)) if crate::pos::contains(pos1, pos2) => {
            // A shape can contain a non-shape
            a
        }
        (State::SelectedNonShapeType(pos1), State::SelectedNonShapeType(pos2)) => {
            State::SelectedNonShapeType(crate::pos::merge(pos1, pos2))
        }
        (State::SelectedNonShapeType(_), _) => a,
        (_, State::SelectedNonShapeType(_)) => b,
    }
}

struct Visitor<'s> {
    selection: &'s Pos,
    container_pos: Option<Pos>,
}

impl<'a> Reducer<'a, IterParams, State> for Visitor<'_> {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, State> {
        self
    }
    fn zero(&mut self) -> State {
        State::Searching(None)
    }
    fn plus(&mut self, a: State, b: State) -> State {
        plus_state(a, b)
    }
    aast_reduce::tast::tast_methods!('a, State; expr_, fun_, method_, class_var, expression_tree);

    fn visit_class_(&mut self, env: &mut Env, class_: &'a tast::Class_) -> State {
        let pos = &class_.span;
        if crate::pos::contains(pos, self.selection) {
            self.container_pos = Some(pos.clone());
            class_.srecurse(env, self)
        } else {
            State::Searching(None)
        }
    }

    fn visit_type_hint(&mut self, env: &mut Env, th: &'a tast::TypeHint) -> State {
        // `on_type_hint_`: the hint option of the type hint.
        let r_ex = self.visit_ex(env, &th.0);
        let r_hint = match (&th.1, &self.container_pos) {
            (Some(aast::Hint(hint_pos, h)), Some(hint_container_pos))
                if matches!(**h, aast::Hint_::Hshape(_)) && crate::pos::contains(self.selection, hint_pos) =>
            {
                State::Searching(Some((
                    hint_pos.clone(),
                    Candidate::OfHint {
                        hint_container_pos: hint_container_pos.clone(),
                        hint_pos: hint_pos.clone(),
                    },
                )))
            }
            _ => th.1.saccept(env, self),
        };
        self.plus(r_ex, r_hint)
    }

    fn visit_fun_def(&mut self, env: &mut Env, fd: &'a tast::FunDef) -> State {
        let pos = &fd.fun.span;
        if crate::pos::contains(pos, self.selection) {
            self.container_pos = Some(pos.clone());
            fd.srecurse(env, self)
        } else {
            State::Searching(None)
        }
    }

    fn visit_stmt(&mut self, env: &mut Env, stmt: &'a tast::Stmt) -> State {
        let stmt_pos = &stmt.0;
        if crate::pos::contains(self.selection, stmt_pos) {
            State::SelectedNonShapeType(stmt_pos.clone())
        } else {
            stmt.srecurse(env, self)
        }
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> State {
        let aast::Expr(ty, expr_pos, _) = expr;
        if crate::pos::contains(self.selection, expr_pos) {
            let mut env = env.clone();
            let ty = tast_env::expand_type(&mut env, ty.clone());
            match (typing_defs_core::get_node(&ty), &self.container_pos) {
                (Ty_::Tshape(_), Some(expr_container_pos)) => State::Searching(Some((
                    expr_pos.clone(),
                    Candidate::OfExpr {
                        expr_container_pos: expr_container_pos.clone(),
                        shape_ty_string: Rc::new(type_string::of_locl_ty(&env, ty.clone())),
                    },
                ))),
                _ => State::SelectedNonShapeType(expr_pos.clone()),
            }
        } else {
            expr.srecurse(env, self)
        }
    }
}

fn find_candidate(selection: &Pos, entry: &Arc<provider_context::Entry>, ctx: &provider_context::T) -> Option<Candidate> {
    let tast_provider::ComputeTast { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    let mut v = Visitor {
        selection,
        container_pos: None,
    };
    match aast_reduce::tast::go(&mut v, ctx, &tast.under_normal_assumptions) {
        State::Searching(Some((_, candidate))) => Some(candidate),
        State::Searching(_) | State::SelectedNonShapeType(_) => None,
    }
}

fn snippet_for_decl_of(s: &str) -> String {
    format!("type T${{0:placeholder_}} = {};\n\n", s)
}

const SNIPPET_FOR_USE: &str = "T${0:placeholder_}";

fn edits_of_candidate(st: &source_text::T, path: &RelativePath, candidate: &Candidate) -> cat::Edits {
    let sub_of_pos = |p: &Pos| cu::to_string(cu::sub_of_pos(st, p));
    let edits = match candidate {
        Candidate::OfExpr {
            shape_ty_string,
            expr_container_pos,
        } => {
            let pos = crate::pos::shrink_to_start(expr_container_pos);
            let text = snippet_for_decl_of(&type_string::to_string(shape_ty_string));
            vec![cat::Edit { pos, text }]
        }
        Candidate::OfHint {
            hint_container_pos,
            hint_pos,
        } => {
            let decl_edit = {
                let pos = crate::pos::shrink_to_start(hint_container_pos);
                let text = {
                    let ty_text = sub_of_pos(hint_pos);
                    snippet_for_decl_of(&ty_text)
                };
                cat::Edit { pos, text }
            };
            let use_edit = cat::Edit {
                pos: hint_pos.clone(),
                text: SNIPPET_FOR_USE.to_string(),
            };
            vec![decl_edit, use_edit]
        }
    };
    cat::singleton(path.clone(), edits)
}

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    selection: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    let source_text = ast_provider::compute_source_text(entry);
    let path = entry.path.clone();
    match find_candidate(selection, entry, ctx) {
        None => vec![],
        Some(candidate) => {
            let title = title_of_candidate(&candidate).to_string();
            let edits: cat::LazyEdits<'a> = Box::new(move || edits_of_candidate(&source_text, &path, &candidate));
            vec![cat::Refactor(cat::EditData {
                title,
                edits,
                selection: None,
                trigger_inline_suggest: false,
            })]
        }
    }
}
