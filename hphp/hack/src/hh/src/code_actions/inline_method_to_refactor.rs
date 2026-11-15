// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/inline_method/inline_method_to_refactor.ml`.
//! See `hh/PORTING.md`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use super::code_action_types as cat;
use super::code_actions_utils as cu;
use super::inline_method_rename;
use super::inline_method_rewrite_block;
use super::inline_method_types as t;
use crate::full_fidelity_source_text as source_text;
use crate::pos::Pos;
use crate::relative_path::RelativePath;
use crate::tast;

/// We convert a `return` in the inlined method to a variable assignment.
/// This is the name for the variable, modulo renaming for hygiene
const RETURN_VAR_RAW_NAME: &str = "$res";

fn pos_of_block(block: &tast::Block) -> Option<Pos> {
    let oxidized::aast::Stmt(hd_pos, _) = block.0.first()?;
    let oxidized::aast::Stmt(last_pos, _) = block.0.last()?;
    let pos = crate::pos::merge(hd_pos, last_pos);
    if crate::pos::length(&pos) > 0 { Some(pos) } else { None }
}

pub enum Binding {
    Argument(isize, Pos),
    Default(Pos),
    PositionalVariadic(Vec<(isize, Pos)>),
    NamedVariadic(Vec<(isize, Pos)>),
}

/// `String.chop_prefix_if_exists ~prefix:"$"`
fn chop_dollar(s: &str) -> &str {
    s.strip_prefix('$').unwrap_or(s)
}

fn bind_args(call_args: &[t::CallArg], params: &[t::ParamInfo]) -> Option<Vec<Binding>> {
    let mut named_args: Vec<(&str, (isize, Pos))> = vec![];
    let mut positional_args: Vec<(isize, Pos)> = vec![];
    for (index, arg) in call_args.iter().enumerate() {
        let index = index as isize;
        match arg {
            t::CallArg::Named(name, pos) => named_args.push((name.as_str(), (index, pos.clone()))),
            t::CallArg::Positional(pos) => positional_args.push((index, pos.clone())),
        }
    }
    // `String.Map.of_alist named_args`
    let named_arg_map: BTreeMap<&str, (isize, Pos)> = {
        let mut map = BTreeMap::new();
        for (name, arg) in &named_args {
            if map.insert(*name, arg.clone()).is_some() {
                return None;
            }
        }
        map
    };
    let declared_named_params: BTreeSet<&str> = params
        .iter()
        .filter(|p| p.named && !p.variadic)
        .map(|p| chop_dollar(&p.name))
        .collect();
    let extra_named_args: Vec<(isize, Pos)> = named_args
        .iter()
        .filter(|(name, _)| !declared_named_params.contains(name))
        .map(|(_, arg)| arg.clone())
        .collect();
    if !(extra_named_args.is_empty() || params.iter().any(|p| p.named && p.variadic)) {
        return None;
    }
    // `bind positional_args params`
    let mut positional: std::collections::VecDeque<(isize, Pos)> = positional_args.into();
    let mut bindings = vec![];
    for param in params {
        let binding = if param.variadic {
            if param.named {
                Binding::NamedVariadic(extra_named_args.clone())
            } else {
                Binding::PositionalVariadic(std::mem::take(&mut positional).into())
            }
        } else {
            let arg = if param.named {
                named_arg_map.get(chop_dollar(&param.name)).cloned()
            } else {
                positional.pop_front()
            };
            match arg {
                Some((index, pos)) => Binding::Argument(index, pos),
                None => Binding::Default(param.default.clone()?),
            }
        };
        bindings.push(binding)
    }
    if positional.is_empty() { Some(bindings) } else { None }
}

/// Returns the text of the assignments and the variables to clean up.
fn calc_pre_assignments_text(
    r: &mut inline_method_rename::T,
    st: &source_text::T,
    bindings: &[Binding],
    renamed_param_names: &[String],
    callee_vars: &BTreeSet<String>,
    arg_evaluation_order: &[isize],
) -> (String, Vec<String>) {
    let expr = |pos: &Pos| cu::to_string(cu::sub_of_pos(st, pos));
    let safe_temp_name = |name: String| -> String {
        let mut name = name;
        while callee_vars.contains(&name) {
            name.push('_')
        }
        name
    };
    // `before`: by index. `after`, `cleanup`: in the order they are added
    // (the OCaml lists are in the reverse order).
    let mut before: Vec<(isize, String)> = vec![];
    let mut after: Vec<String> = vec![];
    let mut cleanup: Vec<String> = vec![];
    if renamed_param_names.len() != bindings.len() {
        panic!("Invalid_argument(\"List.zip_exn\")")
    }
    for (param, binding) in renamed_param_names.iter().zip(bindings) {
        match binding {
            Binding::Argument(index, pos) => before.push((*index, format!("{} = {};", param, expr(pos)))),
            Binding::Default(pos) => after.push(format!("{} = {};", param, expr(pos))),
            Binding::PositionalVariadic(args) => {
                let mut temps: Vec<String> = vec![];
                for (index, pos) in args {
                    let raw_name = safe_temp_name(format!("$__inline_method_arg_{}", index));
                    let temp = inline_method_rename::rename(r, &raw_name);
                    before.push((*index, format!("{} = {};", temp, expr(pos))));
                    temps.push(temp);
                }
                let vec = temps.join(", ");
                let release_args = temps
                    .iter()
                    .rev()
                    .map(|temp| format!("{} = null;", temp))
                    .collect::<Vec<_>>()
                    .join(" ");
                after.push(format!("{} = vec[{}]; {}", param, vec, release_args));
                cleanup.push(param.clone());
            }
            Binding::NamedVariadic(args) => {
                for (index, pos) in args {
                    let raw_name = safe_temp_name(format!("$__inline_method_named_arg_{}", index));
                    let temp = inline_method_rename::rename(r, &raw_name);
                    before.push((*index, format!("{} = {};", temp, expr(pos))));
                    cleanup.push(temp);
                }
            }
        }
    }
    // `Int.Map.of_alist_exn before`
    let mut by_index: BTreeMap<isize, String> = BTreeMap::new();
    for (index, text) in before {
        if by_index.insert(index, text).is_some() {
            panic!("Map.of_alist_exn: duplicate key")
        }
    }
    let mut texts: Vec<String> = arg_evaluation_order
        .iter()
        .map(|index| by_index.get(index).expect("Map.find_exn").clone())
        .collect();
    texts.extend(after);
    cleanup.reverse();
    (texts.join(" "), cleanup)
}

fn calc_body_text(
    r: &mut inline_method_rename::T,
    path: &RelativePath,
    st: &source_text::T,
    candidate: &t::Candidate,
) -> String {
    let block_source_text = pos_of_block(&candidate.callee.block)
        .map(|pos| cu::to_string(cu::sub_of_pos(st, &pos)))
        .unwrap_or_default();
    inline_method_rewrite_block::rewrite_block(r, path, &block_source_text, RETURN_VAR_RAW_NAME)
}

fn strip_leading_spaces(st: &source_text::T, pos: &Pos) -> Pos {
    let strip_length = cu::to_string(cu::sub_of_pos(st, &crate::pos::set_col_start(0, pos)))
        .chars()
        .take_while(|c| *c == ' ')
        .count() as isize;
    let col_start = crate::pos::line_column(pos).1;
    crate::pos::set_col_start(col_start - strip_length, pos)
}

/// `Char.is_whitespace`, for `String.lstrip` and `String.rstrip`
fn is_whitespace(ch: char) -> bool {
    matches!(ch, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r')
}

/// Add the inlined method contents before the call site and
/// calculate a variable name for the `return` of the inlined method.
/// We use the return variable when replacing the call site.
fn edit_inline_and_return_var_of_candidate(
    path: &RelativePath,
    st: &source_text::T,
    bindings: &[Binding],
    candidate: &t::Candidate,
) -> (cat::Edit, String) {
    let t::Candidate { caller, callee, call } = candidate;
    let used_vars: BTreeSet<String> = caller.var_names.iter().cloned().collect();
    let mut r = inline_method_rename::create(used_vars);
    let callee_param_names: Vec<String> = callee.params.iter().map(|p| p.name.clone()).collect();
    let param_names = inline_method_rename::rename_all(&mut r, &callee_param_names);
    let callee_vars: BTreeSet<String> = callee.var_names.iter().chain(&callee_param_names).cloned().collect();
    let (assignments_before_body, cleanup) = calc_pre_assignments_text(
        &mut r,
        st,
        bindings,
        &param_names,
        &callee_vars,
        &call.arg_evaluation_order,
    );
    let body = calc_body_text(&mut r, path, st, candidate);
    // Gives the correct `return_var` because `Inline_method_rename.rename` is idempotent
    let return_var = inline_method_rename::rename(&mut r, RETURN_VAR_RAW_NAME);
    let pos = crate::pos::shrink_to_start(&call.call_stmt_pos);
    let start_indent_amount = crate::pos::line_column(&call.call_stmt_pos).1;
    let cleanup = cleanup
        .iter()
        .map(|var| format!("{} = null;", var))
        .collect::<Vec<_>>()
        .join(" ");
    let text = {
        let block = format!("{}{}{}", assignments_before_body, body, cleanup);
        let formatted = inline_method_rewrite_block::format_block(path, &block, start_indent_amount);
        formatted.trim_start_matches(is_whitespace).to_string()
    };
    (cat::Edit { pos, text }, return_var)
}

/// Replace the call with a variable (`return_var`) and adjust
fn edit_replace_call_of_candidate(st: &source_text::T, return_var: &str, candidate: &t::Candidate) -> cat::Edit {
    let t::Candidate { call, callee, .. } = candidate;
    if callee.has_void_return {
        let strip_trailing_semicolon = |p: &Pos| -> Pos {
            let semicolon_pos = crate::pos::shrink_to_end(p);
            if cu::sub_of_pos_length(st, 1, &semicolon_pos) == ";" {
                crate::pos::advance_one(p)
            } else {
                p.clone()
            }
        };
        let pos = strip_trailing_semicolon(&call.call_pos);
        cat::Edit {
            pos,
            text: String::new(),
        }
    } else {
        let pos = call.call_pos.clone();
        cat::Edit {
            pos,
            text: return_var.to_string(),
        }
    }
}

/// Remove the inlined method
fn edit_remove_method_of_candidate(st: &source_text::T, candidate: &t::Candidate) -> cat::Edit {
    let pos = strip_leading_spaces(st, &candidate.callee.method_pos);
    let text = String::new();
    cat::Edit { pos, text }
}

fn edits_of_candidate(
    st: &source_text::T,
    path: &RelativePath,
    bindings: &[Binding],
    candidate: &t::Candidate,
) -> cat::Edits {
    let edit_remove_method = edit_remove_method_of_candidate(st, candidate);
    let (edit_inline, return_var) = edit_inline_and_return_var_of_candidate(path, st, bindings, candidate);
    let edit_replace_call = edit_replace_call_of_candidate(st, &return_var, candidate);
    let call_edits = if candidate.callee.has_void_return {
        vec![cat::Edit {
            text: edit_inline.text.trim_end_matches(is_whitespace).to_string(),
            ..edit_replace_call
        }]
    } else {
        vec![edit_inline, edit_replace_call]
    };
    let mut edits = vec![edit_remove_method];
    edits.extend(call_edits);
    cat::singleton(path.clone(), edits)
}

pub fn to_refactor<'a>(st: source_text::T, path: RelativePath, candidate: t::Candidate) -> Option<cat::Refactor<'a>> {
    let bindings = bind_args(&candidate.call.call_args, &candidate.callee.params)?;
    let edits: cat::LazyEdits<'a> = Box::new(move || edits_of_candidate(&st, &path, &bindings, &candidate));
    Some(cat::Refactor(cat::EditData {
        title: "Inline method".to_string(),
        edits,
        selection: None,
        trigger_inline_suggest: false,
    }))
}
