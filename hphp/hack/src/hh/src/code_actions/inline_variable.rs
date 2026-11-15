// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/inline_variable.ml`.
//! See `hh/PORTING.md`.
//!
//! `Var_info.merge` is not associative (and drops `referenced`): the
//! visitor is an [`aast_reduce::Reducer`], which combines the values of the
//! nodes as the OCaml `Tast_visitor.reduce` does.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;

use oxidized::aast;

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

#[derive(Clone, Debug)]
struct Def {
    def_pos: Pos,
    def_rhs_pos: Pos,
    /// iff `def_needs_grouping`, then we need to surround with parentheses when inlining.
    /// ```
    ///   $x = 3 + 4;
    ///   foo($x * 5); --inline--> foo((3+4) * 5)
    /// ```
    def_needs_grouping: bool,
    /// In `$x = 0 + $y`, `$x` depends on `$y`
    def_deps: BTreeSet<String>,
}

struct Candidate {
    name: String,
    def: Def,
    use_pos: Pos,
}

/// Core `Char.is_whitespace`
fn is_whitespace(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | b'\x0b' | b'\x0c' | b'\r')
}

fn remove_leading_whitespace(st: &source_text::T, pos: &Pos) -> Pos {
    fn calc_strip_amount(st: &source_text::T, offset: isize) -> isize {
        let ch = source_text::get(st, offset);
        if offset == 0 || ch == b'\n' {
            0
        } else if is_whitespace(ch) {
            1 + calc_strip_amount(st, offset - 1)
        } else {
            0
        }
    }
    let orig_col_start = crate::pos::line_column(pos).1;
    let strip_amount = calc_strip_amount(st, crate::pos::start_offset(pos) - 1);
    crate::pos::set_col_start(orig_col_start - strip_amount, pos)
}

fn next_char_is_newline(st: &source_text::T, pos: &Pos) -> bool {
    let offset = {
        let (line, col) = crate::pos::end_line_column(pos);
        source_text::position_to_offset(st, (line, col + 1))
    };
    let ch = source_text::get(st, offset);
    ch == b'\n'
}

mod var_info {
    use super::*;

    /// The state of a variable: updated as we traverse the tast
    #[derive(Clone, Debug)]
    pub enum Info {
        UsedNever(Def),
        /// `Used_once` is the "good" state: we only offer to inline variables that are used exactly once
        UsedOnce { use_pos: Pos, def: Def },
        /// `Used_undefined` indicates a use of a variable that is not defined.
        /// We do *not* traverse the AST in the same order as variable bindings,
        /// so we may discover later that the variable is indeed defined.
        /// See [merge] for an example of how `Used_undefined` is used.
        UsedUndefined(Pos),
        Ineligible,
    }

    fn use_pos_of_info(i: &Info) -> Option<&Pos> {
        match i {
            Info::UsedNever(_) => None,
            Info::UsedOnce { use_pos, .. } => Some(use_pos),
            Info::UsedUndefined(use_pos) => Some(use_pos),
            Info::Ineligible => None,
        }
    }

    #[derive(Clone, Debug, Default)]
    pub struct T {
        referenced: BTreeSet<String>,
        infos: BTreeMap<String, Info>,
    }

    /// Useful for calculating the dependencies of a variable. In `$x = 0 + $y`, `$x` depends on `$y`.
    pub fn referenced(t: &T) -> &BTreeSet<String> {
        &t.referenced
    }

    pub fn empty() -> T {
        T::default()
    }

    /// A variable is a candidate iff:
    /// - The variable is not `Ineligible`
    /// - It's the only variable used in the selection
    /// - None of the variable's deps is redefined between the definition and use of the variable.
    pub fn to_candidate_opt(T { infos, .. }: &T, selection: &Pos) -> Option<Candidate> {
        let vars_in_selection: Vec<(&String, &Info)> = infos
            .iter()
            .filter(|(_, info)| match use_pos_of_info(info) {
                Some(use_pos) => crate::pos::contains(use_pos, selection),
                None => false,
            })
            .collect();
        match &vars_in_selection[..] {
            [(name, Info::UsedOnce { def, use_pos })] => {
                let dep_may_have_changed = def.def_deps.iter().any(|dep| {
                    infos.get(dep).is_some_and(|dep_info| match use_pos_of_info(dep_info) {
                        Some(use_pos) => crate::pos::start_offset(use_pos) > crate::pos::end_offset(&def.def_rhs_pos),
                        None => true,
                    })
                });
                if !dep_may_have_changed {
                    Some(Candidate {
                        name: (*name).clone(),
                        def: def.clone(),
                        use_pos: use_pos.clone(),
                    })
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn add_def(T { referenced, mut infos }: T, name: String, def: Def) -> T {
        infos.insert(name, Info::UsedNever(def));
        T { referenced, infos }
    }

    pub fn add_use(T { mut referenced, mut infos }: T, name: String, use_pos: Pos) -> T {
        let new = match infos.remove(&name) {
            None => Info::UsedUndefined(use_pos),
            Some(Info::UsedNever(def)) => Info::UsedOnce { use_pos, def },
            Some(Info::UsedOnce { .. } | Info::UsedUndefined(_) | Info::Ineligible) => Info::Ineligible,
        };
        infos.insert(name.clone(), new);
        referenced.insert(name);
        T { referenced, infos }
    }

    pub fn mark_ineligible(T { referenced, mut infos }: T, name: String) -> T {
        infos.insert(name, Info::Ineligible);
        T { referenced, infos }
    }

    pub fn merge(T { infos: infos1, .. }: T, T { infos: infos2, .. }: T) -> T {
        let mut infos = infos1;
        for (key, v2) in infos2 {
            let v = match infos.remove(&key) {
                None => v2,
                Some(v1) => match (v1, v2) {
                    // This branch is hit for code like the following:
                    // $x = 0;       // $x is `Used_never` here
                    // $_ = $x + 1;  // $x is `Used_undefined` here
                    (Info::UsedNever(def), Info::UsedUndefined(use_pos)) => Info::UsedOnce { def, use_pos },
                    // redefined
                    (_, v2 @ Info::UsedNever(_)) => v2,
                    (_, Info::UsedOnce { .. } | Info::UsedUndefined(_) | Info::Ineligible) => Info::Ineligible,
                },
            };
            infos.insert(key, v);
        }
        T {
            referenced: BTreeSet::new(),
            infos,
        }
    }
}

struct Visitor<'s> {
    selection: &'s Pos,
    in_lvalue: bool,
}

impl<'a> Reducer<'a, IterParams, var_info::T> for Visitor<'_> {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, var_info::T> {
        self
    }
    fn zero(&mut self) -> var_info::T {
        var_info::empty()
    }
    fn plus(&mut self, a: var_info::T, b: var_info::T) -> var_info::T {
        var_info::merge(a, b)
    }
    aast_reduce::tast::tast_methods!('a, var_info::T; expr_, method_, class_var, expression_tree);

    fn visit_class_(&mut self, env: &mut Env, class_: &'a tast::Class_) -> var_info::T {
        if crate::pos::contains(&class_.span, self.selection) {
            class_.srecurse(env, self)
        } else {
            var_info::empty()
        }
    }

    fn visit_fun_(&mut self, env: &mut Env, fun_: &'a tast::Fun_) -> var_info::T {
        if crate::pos::contains(&fun_.span, self.selection) {
            aast_reduce::tast::on_fun_(self, env, fun_)
        } else {
            var_info::empty()
        }
    }

    fn visit_fun_param(&mut self, env: &mut Env, param: &'a tast::FunParam) -> var_info::T {
        let r = param.srecurse(env, self);
        var_info::mark_ineligible(r, param.name.clone())
    }

    fn visit_stmt(&mut self, env: &mut Env, stmt: &'a tast::Stmt) -> var_info::T {
        let aast::Stmt(pos, stmt_) = stmt;
        if let aast::Stmt_::Expr(e) = stmt_ {
            if let aast::Expr_::Assign(a) = &e.2 {
                let (lhs, bop, rhs) = &**a;
                if let (aast::Expr_::Lvar(lid), None) = (&lhs.2, bop) {
                    let name = crate::local_id::get_name(&lid.1).to_string();
                    let def_needs_grouping = matches!(
                        rhs.2,
                        aast::Expr_::Binop(_) | aast::Expr_::Pipe(_) | aast::Expr_::Eif(_)
                    );
                    let rhs_acc = self.visit_expr(env, rhs);
                    let def = Def {
                        def_pos: pos.clone(),
                        def_rhs_pos: rhs.1.clone(),
                        def_needs_grouping,
                        def_deps: var_info::referenced(&rhs_acc).clone(),
                    };
                    let acc = var_info::add_def(rhs_acc, name, def);
                    // `with_in_lvalue (fun () -> self#on_expr env lhs)`
                    let orig_in_lvalue = self.in_lvalue;
                    self.in_lvalue = true;
                    let lhs_acc = self.visit_expr(env, lhs);
                    self.in_lvalue = orig_in_lvalue;
                    return self.plus(acc, lhs_acc);
                }
            }
        }
        stmt.srecurse(env, self)
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> var_info::T {
        match &expr.2 {
            aast::Expr_::Assign(a)
                if a.1.is_some() && matches!(&a.0.2, aast::Expr_::Lvar(_)) =>
            {
                let name = match &a.0.2 {
                    aast::Expr_::Lvar(lid) => crate::local_id::get_name(&lid.1).to_string(),
                    _ => unreachable!(),
                };
                var_info::mark_ineligible(expr.srecurse(env, self), name)
            }
            aast::Expr_::Lvar(lid) if !self.in_lvalue => {
                let aast::Lid(use_pos, lid) = &**lid;
                let name = crate::local_id::get_name(lid).to_string();
                var_info::add_use(var_info::empty(), name, use_pos.clone())
            }
            _ => expr.srecurse(env, self),
        }
    }
}

fn start_of_next_line(st: &source_text::T, path: &RelativePath, pos: &Pos) -> Pos {
    let pos_end = {
        let (orig_end_line, _) = crate::pos::end_line_column(pos);
        let end_line = orig_end_line + 1;
        let end_line_offset = source_text::position_to_offset(st, (end_line, 0));
        (end_line, end_line_offset, end_line_offset)
    };
    crate::pos::make_from_lnum_bol_offset(path.clone(), crate::pos::line_beg_offset(pos), pos_end)
}

fn edits_of_candidate(path: &RelativePath, st: &source_text::T, Candidate { def, use_pos, .. }: &Candidate) -> cat::Edits {
    let change_replace_def = {
        let pos = remove_leading_whitespace(st, &def.def_pos);
        let pos = if next_char_is_newline(st, &def.def_pos) {
            start_of_next_line(st, path, &pos)
        } else {
            pos
        };
        cat::Edit {
            pos,
            text: String::new(),
        }
    };
    let change_replace_use = {
        let text = cu::to_string(cu::sub_of_pos(st, &def.def_rhs_pos));
        let text = if def.def_needs_grouping { format!("({})", text) } else { text };
        cat::Edit {
            pos: use_pos.clone(),
            text,
        }
    };
    cat::singleton(path.clone(), vec![change_replace_def, change_replace_use])
}

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    selection: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    let source_text = ast_provider::compute_source_text(entry);
    let tast_provider::ComputeTast { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    let path = entry.path.clone();
    let mut v = Visitor {
        selection,
        in_lvalue: false,
    };
    let info = aast_reduce::tast::go(&mut v, ctx, &tast.under_normal_assumptions);
    match var_info::to_candidate_opt(&info, selection) {
        None => vec![],
        Some(candidate) => {
            let title = format!("Inline variable {}", candidate.name);
            let edits: cat::LazyEdits<'a> = Box::new(move || edits_of_candidate(&path, &source_text, &candidate));
            vec![cat::Refactor(cat::EditData {
                title,
                edits,
                selection: None,
                trigger_inline_suggest: false,
            })]
        }
    }
}
