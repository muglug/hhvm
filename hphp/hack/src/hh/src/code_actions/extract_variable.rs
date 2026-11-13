// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactors/extract_variable.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F7** (plan §7.3).

use std::sync::Arc;

use oxidized::aast;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;

use super::aast_reduce;
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

/// `Str.regexp {|\$placeholder\([0-9]+\)|}` with `Str.string_match _ name 0`
/// (a match at the start of the name).
fn placeholder_regexp() -> &'static regex::Regex {
    static RE: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    RE.get_or_init(|| regex::Regex::new(r"^\$placeholder([0-9]+)").unwrap())
}

#[derive(Clone, Debug)]
struct Candidate {
    /// used for calculating indentation
    prev_stmt_pos: Option<Pos>,
    /// used for calculating indentation
    stmt_pos: Pos,
    /// position of expr or statement corresponding to the selection
    pos: Pos,
    /// used for naming the placeholder of the generated variable
    placeholder_n: isize,
}

type Acc = Option<Candidate>;

struct V<'s> {
    selection: &'s Pos,
    prev_stmt_pos: Option<Pos>,
    stmt_pos: Option<Pos>,
    placeholder_n: isize,
    expr_positions_overlapping_selection: Vec<Pos>,
}

impl V<'_> {
    fn should_traverse(&self, outer: &Pos) -> bool {
        crate::pos::contains(outer, self.selection)
    }

    fn set_stmt_pos(&mut self, pos: &Pos) {
        if !crate::pos::equal(&Pos::NONE, pos) {
            self.prev_stmt_pos = self.stmt_pos.take();
            self.stmt_pos = Some(pos.clone())
        }
    }

    /// filter out invalid selection like this:
    ///       (1 + 2) +  3
    ///            ^-----^ selection
    fn ensure_selection_common_root(&self, c: Acc) -> Acc {
        c.filter(|candidate| {
            self.expr_positions_overlapping_selection.iter().all(|p| {
                crate::pos::contains(&candidate.pos, p) || crate::pos::contains(p, &candidate.pos)
            })
        })
    }
}

impl<'a> Reducer<'a, IterParams, Acc> for V<'_> {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Acc> {
        self
    }
    fn zero(&mut self) -> Acc {
        None
    }
    fn plus(&mut self, a: Acc, b: Acc) -> Acc {
        a.or(b)
    }
    aast_reduce::tast::tast_methods!('a, Acc; expr_, fun_, class_var, expression_tree);

    fn visit_def(&mut self, env: &mut Env, def: &'a tast::Def) -> Acc {
        match def {
            aast::Def::Fun(fun_def) if self.should_traverse(&fun_def.fun.span) => self.visit_fun_def(env, fun_def),
            aast::Def::Class(class_def) if self.should_traverse(&class_def.span) => self.visit_class_(env, class_def),
            aast::Def::Stmt(stmt) if self.should_traverse(&stmt.0) => self.visit_stmt(env, stmt),
            _ => None,
        }
    }

    fn visit_method_(&mut self, env: &mut Env, meth: &'a tast::Method_) -> Acc {
        if self.should_traverse(&meth.span) {
            let r = aast_reduce::tast::on_method_(self, env, meth);
            self.ensure_selection_common_root(r)
        } else {
            None
        }
    }

    fn visit_fun_def(&mut self, env: &mut Env, fd: &'a tast::FunDef) -> Acc {
        let r = fd.srecurse(env, self);
        self.ensure_selection_common_root(r)
    }

    fn visit_lid(&mut self, env: &mut Env, lid: &'a aast::Lid) -> Acc {
        let name = crate::local_id::get_name(&lid.1);
        if let Some(caps) = placeholder_regexp().captures(name) {
            if let Ok(n) = caps[1].parse::<isize>() {
                self.placeholder_n = std::cmp::max(n + 1, self.placeholder_n)
            }
        }
        lid.srecurse(env, self)
    }

    fn visit_func_body(&mut self, env: &mut Env, fb: &'a tast::FuncBody) -> Acc {
        let acc = fb.srecurse(env, self);
        if let Some(aast::Stmt(pos, _)) = fb.fb_ast.0.first() {
            self.set_stmt_pos(pos)
        }
        acc.map(|acc| Candidate {
            placeholder_n: self.placeholder_n,
            ..acc
        })
    }

    fn visit_stmt(&mut self, env: &mut Env, stmt: &'a tast::Stmt) -> Acc {
        self.set_stmt_pos(&stmt.0);
        stmt.srecurse(env, self)
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Acc {
        let aast::Expr(_, pos, expr_) = expr;
        if crate::pos::overlaps(self.selection, pos) {
            self.expr_positions_overlapping_selection.push(pos.clone());
        }
        match (&self.stmt_pos, expr_) {
            (Some(stmt_pos), _) if crate::pos::contains(self.selection, pos) => Some(Candidate {
                prev_stmt_pos: self.prev_stmt_pos.clone(),
                stmt_pos: stmt_pos.clone(),
                pos: pos.clone(),
                // will be adjusted on the way up
                placeholder_n: 0,
            }),
            (_, aast::Expr_::Assign(a)) => {
                let lhs_pos = a.0.1.clone();
                let acc = expr.srecurse(env, self);
                acc.filter(|candidate| !crate::pos::contains(&lhs_pos, &candidate.pos))
            }
            _ => expr.srecurse(env, self),
        }
    }
}

/// Generate a snippet from the placeholder number.
/// This relies on a nonstandard LSP extension recognized by the client:
/// https://fburl.com/code/0vzkqds8. We can implement non-hackily if LSP is updated:
/// https://github.com/microsoft/language-server-protocol/issues/592
fn placeholder_name_of_n(n: isize) -> String {
    format!("$${{0:placeholder{}}}", n)
}

fn offset_of_pos(st: &source_text::T, pos: &Pos) -> isize {
    let (line, start, _) = crate::pos::info_pos(pos);
    source_text::position_to_offset(st, (line, start))
}

/// true iff the expr or stmt at `pos` is in a lambda where the body is not wrapped in curly braces
/// (single expression with an implicit return).
fn is_in_braceless_lambda(st: &source_text::T, root: &PositionedSyntax, pos: &Pos) -> bool {
    let offset = offset_of_pos(st, pos);
    let nodes = cu::parentage(root, offset);
    nodes
        .iter()
        .find_map(|node| match &node.syntax {
            SyntaxVariant::LambdaExpression(x) if cu::start_offset(&x.lambda_body) == offset => {
                Some(&x.lambda_body)
            }
            _ => None,
        })
        .map(|body| !matches!(body.syntax, SyntaxVariant::CompoundStatement(_)))
        .unwrap_or(false)
}

fn indent_of_pos(pos: &Pos) -> String {
    let (_, character) = crate::pos::line_column(pos);
    " ".repeat(character.max(0) as usize)
}

fn slice(st: &source_text::T, start: &Pos, end_: &Pos) -> String {
    let start_offset = offset_of_pos(st, start);
    let end_offset = offset_of_pos(st, end_);
    cu::to_string(source_text::sub(st, start_offset, end_offset - start_offset))
}

fn edits_of_candidate(
    entry: &provider_context::Entry,
    Candidate {
        prev_stmt_pos,
        stmt_pos,
        pos,
        placeholder_n,
    }: &Candidate,
) -> Vec<cat::Edit> {
    let (_, positioned_tree) = crate::identify_symbol_service::compute_cst(entry);
    let st = ast_provider::compute_source_text(entry);
    let placeholder = placeholder_name_of_n(*placeholder_n);
    let stmt_text = {
        let before = slice(&st, stmt_pos, pos);
        let after = slice(&st, &crate::pos::shrink_to_end(pos), &crate::pos::shrink_to_end(stmt_pos));
        format!("{}{}{}", before, placeholder, after)
    };
    let stmt_indent = indent_of_pos(stmt_pos);
    let assignment_text = {
        let exp_string = cu::to_string(cu::sub_of_pos(&st, pos));
        format!("{} = {};\n", placeholder, exp_string)
    };
    let text = if is_in_braceless_lambda(&st, &positioned_tree, stmt_pos) {
        let prev_indent = prev_stmt_pos
            .as_ref()
            .map(indent_of_pos)
            .unwrap_or_else(|| stmt_indent.clone());
        let body_indent = {
            // `Format_env.(default.indent_width)`
            let default_indent = " ".repeat(2);
            format!("{}{}", prev_indent, default_indent)
        };
        format!(
            "{{\n{}return {};\n{}}}",
            format!("{}{}{}", body_indent, assignment_text, body_indent),
            stmt_text,
            prev_indent
        )
    } else {
        format!("{}{}{}", assignment_text, stmt_indent, stmt_text)
    };
    vec![cat::Edit {
        pos: stmt_pos.clone(),
        text,
    }]
}

fn refactor_of_candidate<'a>(
    entry: &'a provider_context::Entry,
    path: RelativePath,
    candidate: Candidate,
) -> cat::Refactor<'a> {
    let edits: cat::LazyEdits<'a> = Box::new(move || cat::singleton(path, edits_of_candidate(entry, &candidate)));
    cat::Refactor(cat::EditData {
        title: "Extract into variable".to_string(),
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
    let path = entry.path.clone();
    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    let mut v = V {
        selection,
        prev_stmt_pos: None,
        stmt_pos: None,
        placeholder_n: 0,
        expr_positions_overlapping_selection: vec![],
    };
    aast_reduce::tast::go(&mut v, ctx, &tast.under_normal_assumptions)
        .map(|c| refactor_of_candidate(entry, path, c))
        .into_iter()
        .collect()
}
