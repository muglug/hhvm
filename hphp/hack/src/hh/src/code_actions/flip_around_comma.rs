// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/flip_around_comma.ml`.
//! See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor;
use oxidized::ast_defs;

use super::code_action_types as cat;
use super::code_actions_utils as cu;
use crate::ast_provider;
use crate::full_fidelity_source_text as source_text;
use crate::hack_event_logger;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor;
use crate::tast_visitor::IterParams;
use crate::tast_visitor::Reduce;

mod candidate {
    use super::*;

    /// In `foo(param_a, param_b, param_c)`
    ///                          ^
    ///                          |
    ///                         selection
    ///
    ///   `positions` is the positions of each of the params
    ///   `insertion_index` is 2 (in bounds by construction)
    ///   `pos` is the span from the start of `param_a` to the end of `param_c`
    pub struct T {
        pub positions: Vec<Pos>,
        pub insertion_index: usize,
        pub pos: Pos,
    }

    pub fn create_exn(positions: Vec<Pos>, insertion_index: usize) -> T {
        if insertion_index >= positions.len() {
            hack_event_logger::invariant_violation_bug(
                None,
                None,
                Some(&format!(
                    "insertion index: {} positions length: {}",
                    insertion_index,
                    positions.len()
                )),
                None,
                None,
                "flip around comma: insertion index out of bounds",
            );
            panic!("flip around comma: insertion index out of bounds")
        } else {
            let pos = {
                let first = positions.first().unwrap();
                let last = positions.last().unwrap();
                crate::pos::merge(first, last)
            };
            T {
                insertion_index,
                positions,
                pos,
            }
        }
    }
}

fn list_flip<A>(insertion_index: usize, mut l: Vec<A>) -> Vec<A> {
    // `h1 :: h2 :: tail when i = insertion_index - 1 -> h2 :: h1 :: tail`
    if insertion_index >= 1 && insertion_index < l.len() {
        l.swap(insertion_index - 1, insertion_index)
    }
    l
}

fn find_insertion_index(cursor: &Pos, positions: &[Pos]) -> Option<usize> {
    let is_after_cursor = |pos: &Pos| crate::pos::start_offset(pos) > crate::pos::start_offset(cursor);
    let is_before_cursor = |pos: &Pos| crate::pos::start_offset(pos) < crate::pos::start_offset(cursor);
    if positions.iter().any(is_before_cursor) {
        positions.iter().position(is_after_cursor)
    } else {
        None
    }
}

fn find_candidate(cursor: &Pos, positions: Vec<Pos>) -> Option<candidate::T> {
    find_insertion_index(cursor, &positions)
        .map(|insertion_index| candidate::create_exn(positions, insertion_index))
}

fn pos_of_expr(e: &tast::Expr) -> Pos {
    e.1.clone()
}

fn pos_of_shape_field_name(n: &ast_defs::ShapeFieldName) -> Pos {
    match n {
        ast_defs::ShapeFieldName::SFlitStr(ps) => ps.0.clone(),
        ast_defs::ShapeFieldName::SFclassname(id) => id.0.clone(),
        ast_defs::ShapeFieldName::SFclassConst(_, ps) => ps.0.clone(),
    }
}

fn pos_of_type_hint(h: &tast::TypeHint) -> Pos {
    match &h.1 {
        Some(hint) => hint.0.clone(),
        None => Pos::NONE,
    }
}

fn find_in_positions_params(cursor: &Pos, params: &[tast::FunParam]) -> Option<candidate::T> {
    let is_easy_to_flip = |param: &tast::FunParam| {
        !crate::aast_utils::is_param_variadic(param)
            && param.readonly.is_none()
            && param.visibility.is_none()
            && (match param.callconv {
                ast_defs::ParamKind::Pnormal => true,
                ast_defs::ParamKind::Pinout(_) => false,
            })
            && param.user_attributes.is_empty()
    };
    let pos_of_expr_opt = |e: Option<&tast::Expr>| match e {
        Some(e) => e.1.clone(),
        None => Pos::NONE,
    };
    if params.iter().all(is_easy_to_flip) {
        let positions = params
            .iter()
            .map(|param| {
                [
                    pos_of_expr_opt(crate::aast_utils::get_param_default(param)),
                    pos_of_type_hint(&param.type_hint),
                ]
                .iter()
                .fold(param.pos.clone(), |acc, p| crate::pos::merge(&acc, p))
            })
            .collect();
        find_candidate(cursor, positions)
    } else {
        None
    }
}

struct Visitor<'c> {
    cursor: &'c Pos,
    acc: Option<candidate::T>,
}

impl<'a> Reduce<'a> for Visitor<'_> {
    type Acc = Option<candidate::T>;
    fn zero(&self) -> Self::Acc {
        None
    }
    fn plus(&self, a: Self::Acc, b: Self::Acc) -> Self::Acc {
        a.or(b)
    }
    fn acc(&mut self) -> &mut Self::Acc {
        &mut self.acc
    }
}

impl<'a> aast_visitor::Visitor<'a> for Visitor<'_> {
    type Params = IterParams;
    fn object(&mut self) -> &mut dyn aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }
    tast_visitor::reduce_methods!('a; class_var, expression_tree);

    fn visit_method_(&mut self, env: &mut Env, meth: &'a tast::Method_) -> Result<(), ()> {
        if crate::pos::contains(&meth.span, self.cursor) {
            let (res, r) = tast_visitor::reduce::result(self, |v| tast_visitor::reduce::on_method_(v, env, meth));
            res?;
            let r = r.or_else(|| find_in_positions_params(self.cursor, &meth.params));
            tast_visitor::reduce::add(self, r);
        }
        Ok(())
    }

    fn visit_class_(&mut self, env: &mut Env, class_: &'a tast::Class_) -> Result<(), ()> {
        if crate::pos::contains(&class_.span, self.cursor) {
            class_.recurse(env, self)
        } else {
            Ok(())
        }
    }

    fn visit_fun_(&mut self, env: &mut Env, fun_: &'a tast::Fun_) -> Result<(), ()> {
        if crate::pos::contains(&fun_.span, self.cursor) {
            let (res, r) = tast_visitor::reduce::result(self, |v| tast_visitor::reduce::on_fun_(v, env, fun_));
            res?;
            let r = r.or_else(|| find_in_positions_params(self.cursor, &fun_.params));
            tast_visitor::reduce::add(self, r);
        }
        Ok(())
    }

    fn visit_expr_(&mut self, env: &mut Env, expr: &'a tast::Expr_) -> Result<(), ()> {
        let (res, r) = tast_visitor::reduce::result(self, |v| tast_visitor::reduce::on_expr_(v, env, expr));
        res?;
        let r = r.or_else(|| {
            let positions: Vec<Pos> = match expr {
                aast::Expr_::Call(call) => call
                    .args
                    .iter()
                    .map(|arg| match arg {
                        aast::Argument::Ainout(inout_pos, expr) => crate::pos::merge(inout_pos, &pos_of_expr(expr)),
                        aast::Argument::Anormal(expr) => pos_of_expr(expr),
                        aast::Argument::Anamed(name, expr) => crate::pos::merge(&name.0, &pos_of_expr(expr)),
                    })
                    .collect(),
                aast::Expr_::ValCollection(x) => x.2.iter().map(pos_of_expr).collect(),
                aast::Expr_::List(exprs) | aast::Expr_::Tuple(exprs) => exprs.iter().map(pos_of_expr).collect(),
                aast::Expr_::KeyValCollection(x) => x
                    .2
                    .iter()
                    .map(|aast::Field(e1, e2)| crate::pos::merge(&pos_of_expr(e1), &pos_of_expr(e2)))
                    .collect(),
                aast::Expr_::Shape(fields) => {
                    if fields.iter().any(|field| match field {
                        aast::ShapeExprField::SFSplat(_) => true,
                        aast::ShapeExprField::SFField(_, _) => false,
                    }) {
                        return None;
                    } else {
                        fields
                            .iter()
                            .filter_map(|field| match field {
                                aast::ShapeExprField::SFField(field_name, expr) => {
                                    Some(crate::pos::merge(
                                        &pos_of_shape_field_name(field_name),
                                        &pos_of_expr(expr),
                                    ))
                                }
                                aast::ShapeExprField::SFSplat(_) => None,
                            })
                            .collect()
                    }
                }
                _ => return None,
            };
            find_candidate(self.cursor, positions)
        });
        tast_visitor::reduce::add(self, r);
        Ok(())
    }
}

fn edit_of_candidate(
    path: &RelativePath,
    st: &source_text::T,
    candidate::T {
        insertion_index,
        positions,
        pos,
    }: &candidate::T,
) -> cat::Edits {
    let text = list_flip(
        *insertion_index,
        positions
            .iter()
            .map(|p| cu::to_string(cu::sub_of_pos(st, p)))
            .collect(),
    )
    .join(", ");
    let change = cat::Edit {
        pos: pos.clone(),
        text,
    };
    cat::singleton(path.clone(), vec![change])
}

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    pos: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    if crate::pos::length(pos) == 0 {
        let source_text = ast_provider::compute_source_text(entry);
        let tast_provider::ComputeTast { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
        let path = entry.path.clone();
        let mut v = Visitor { cursor: pos, acc: None };
        let candidate = tast_visitor::reduce::go(&mut v, ctx, &tast.under_normal_assumptions);
        match candidate {
            None => vec![],
            Some(candidate) => {
                let edits: cat::LazyEdits<'a> = Box::new(move || edit_of_candidate(&path, &source_text, &candidate));
                vec![cat::Refactor(cat::EditData {
                    title: "Flip around comma".to_string(),
                    edits,
                    selection: None,
                    trigger_inline_suggest: false,
                })]
            }
        }
    } else {
        vec![]
    }
}
