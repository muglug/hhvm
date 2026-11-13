// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactors/override_method.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F7** (plan §7.3).

use std::collections::BTreeSet;
use std::sync::Arc;

use oxidized::aast;
use oxidized::ast_defs;

use super::aast_reduce;
use super::aast_reduce::Reducer;
use super::aast_reduce::SNode;
use super::code_action_types as cat;
use crate::classish_positions;
use crate::decl_entry;
use crate::folded_class;
use crate::hack_event_logger;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor::IterParams;
use crate::typing_defs;
use crate::typing_defs::ClassElt;
use crate::typing_skeleton;

#[derive(Clone, Debug)]
enum MethodActionLocation {
    OnParentName(String),
    InBetweenClassElements(Pos),
}

#[derive(Clone, Debug)]
struct T {
    title: String,
    skeleton: typing_skeleton::T,
    location: MethodActionLocation,
}

fn stub_method_action(
    location: &MethodActionLocation,
    is_static: bool,
    parent_name: &str,
    (meth_name, meth): &(String, ClassElt),
) -> T {
    let skeleton = typing_skeleton::of_method(meth_name, meth, is_static, true, true);
    let skeleton = match location {
        MethodActionLocation::OnParentName(_) => typing_skeleton::add_suffix("\n", skeleton),
        MethodActionLocation::InBetweenClassElements(_) => {
            typing_skeleton::add_prefix("\n", typing_skeleton::strip_suffix("\n", skeleton))
        }
    };
    let title = format!(
        "Add override for {}::{}",
        crate::utils::strip_ns(parent_name),
        meth_name
    );
    T {
        title,
        skeleton,
        location: location.clone(),
    }
}

/// Return a list of quickfixes for [cls] which add a method that
/// overrides one in [parent_name].
fn override_method_quickfixes(
    location: MethodActionLocation,
    env: &Env,
    cls: &tast::Class_,
    parent_name: &str,
) -> Vec<T> {
    let existing_methods: BTreeSet<&str> = cls.methods.iter().map(|m| m.name.1.as_str()).collect();
    match crate::typing_env::get_class(env, parent_name) {
        decl_entry::T::Found(decl) => {
            // Offer an override action for any inherited method which isn't
            // final or private and that the current class hasn't already
            // overridden.
            let actions_for_methods = |is_static: bool, methods: Vec<(String, ClassElt)>| -> Vec<T> {
                methods
                    .iter()
                    .filter(|(name, meth)| {
                        !existing_methods.contains(name.as_str())
                            && !typing_defs::get_ce_final(meth)
                            && !typing_defs::class_elt_is_private_not_lsb(meth)
                    })
                    .map(|m| stub_method_action(&location, is_static, parent_name, m))
                    .collect()
            };
            let mut result = actions_for_methods(false, folded_class::methods(&decl));
            result.extend(actions_for_methods(true, folded_class::smethods(&decl)));
            result
        }
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
    }
}

fn parent_name_of_class_hint(h: &aast::ClassHint) -> Option<&str> {
    match &*h.1 {
        aast::Hint_::Happly(ast_defs::Id(_, parent_name), _) => Some(parent_name),
        _ => None,
    }
}

/// Quickfixes available at cursor position [cursor_line] and
/// [cursor_col]. These aren't associated with errors, rather they
/// transform code from one valid state to another.
struct V {
    cursor_line: isize,
    cursor_col: isize,
    /// Is the current cursor in between methods?
    inbetween_class: Option<(String, Pos)>,
}

impl<'a> Reducer<'a, IterParams, Vec<T>> for V {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Vec<T>> {
        self
    }
    fn zero(&mut self) -> Vec<T> {
        vec![]
    }
    fn plus(&mut self, mut a: Vec<T>, b: Vec<T>) -> Vec<T> {
        a.extend(b);
        a
    }
    aast_reduce::tast::tast_methods!('a, Vec<T>; expr_, fun_, method_, class_var, expression_tree);

    fn visit_class_(&mut self, env: &mut Env, c: &'a tast::Class_) -> Vec<T> {
        let class_name = &c.name.1;
        let acc = c.srecurse(env, self);

        // When cursor is on parent
        let on_parent_qfs: Vec<Vec<T>> = match c.kind {
            ast_defs::ClassishKind::Cclass(_) => c
                .extends
                .iter()
                .map(|h| {
                    if crate::pos::inside_one_based(&h.0, self.cursor_line, self.cursor_col) {
                        match parent_name_of_class_hint(h) {
                            Some(parent_name) => override_method_quickfixes(
                                MethodActionLocation::OnParentName(class_name.clone()),
                                env,
                                c,
                                parent_name,
                            ),
                            None => vec![],
                        }
                    } else {
                        vec![]
                    }
                })
                .collect(),
            _ => vec![],
        };

        // When cursor is on whitespace in between class body elements
        let inbetween_qfs: Vec<Vec<T>> = match &self.inbetween_class {
            Some((inbetween_class_name, inbetween_class_pos)) if class_name == inbetween_class_name => c
                .extends
                .iter()
                .map(|h| match parent_name_of_class_hint(h) {
                    Some(parent_name) => override_method_quickfixes(
                        MethodActionLocation::InBetweenClassElements(inbetween_class_pos.clone()),
                        env,
                        c,
                        parent_name,
                    ),
                    None => vec![],
                })
                .collect(),
            _ => vec![],
        };

        let mut result: Vec<T> = inbetween_qfs.into_iter().flatten().collect();
        result.extend(on_parent_qfs.into_iter().flatten());
        result.extend(acc);
        result
    }
}

fn to_edits_and_selection(
    classish_positions: &classish_positions::T<Pos>,
    quickfix: &T,
) -> (Vec<cat::Edit>, Option<Pos>) {
    let pos = match &quickfix.location {
        MethodActionLocation::OnParentName(class_name) => {
            match classish_positions::find(
                &classish_positions::CPos::ClassishStartOfBody(class_name.clone()),
                classish_positions,
            ) {
                Some(classish_start) => Some(classish_start),
                None => {
                    hack_event_logger::invariant_violation_bug(
                        None,
                        None,
                        Some(class_name),
                        None,
                        None,
                        "Could not find class position for quickfix",
                    );
                    None
                }
            }
        }
        MethodActionLocation::InBetweenClassElements(pos) => Some(crate::pos::shrink_to_start(pos)),
    };
    match pos {
        Some(pos) => {
            let text = typing_skeleton::to_string(&quickfix.skeleton);
            let selection = typing_skeleton::cursor_after_insert(&pos, &quickfix.skeleton);
            (vec![cat::Edit { pos, text }], Some(selection))
        }
        None => (vec![], None),
    }
}

fn refactor_action<'a>(
    path: &RelativePath,
    classish_positions: &classish_positions::T<Pos>,
    quickfix: T,
) -> cat::Refactor<'a> {
    let (edits, selection) = to_edits_and_selection(classish_positions, &quickfix);
    let path = path.clone();
    let edits: cat::LazyEdits<'a> = Box::new(move || cat::singleton(path, edits));
    let trigger_inline_suggest = selection.is_some();
    cat::Refactor(cat::EditData {
        title: quickfix.title,
        edits,
        selection,
        trigger_inline_suggest,
    })
}

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    pos: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    let (cursor_line, cursor_col) = crate::pos::line_column(pos);
    let (source_text, tree) = crate::identify_symbol_service::compute_cst(entry);
    let path = &entry.path;
    let classish_positions = classish_positions::extract(&tree, &source_text, path);
    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    let inbetween_class = {
        let inbetween_positions = classish_positions::inbetween_body_element_positions(&classish_positions);
        // `List.hd (S_map.elements (S_map.filter_map ...))`
        inbetween_positions.into_iter().find_map(|(cls, posl)| {
            posl.into_iter()
                .find(|whitespace_range| crate::pos::inside_one_based(whitespace_range, cursor_line, cursor_col))
                .map(|p| (cls, p))
        })
    };
    let mut v = V {
        cursor_line,
        cursor_col,
        inbetween_class,
    };
    let override_method_refactorings = aast_reduce::tast::go(&mut v, ctx, &tast.under_normal_assumptions);
    override_method_refactorings
        .into_iter()
        .map(|q| refactor_action(path, &classish_positions, q))
        .collect()
}
