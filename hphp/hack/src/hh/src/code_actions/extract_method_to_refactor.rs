// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactors/extract_method/extract_method_to_refactor.ml`. See
//! `hh/PORTING.md`.

use std::rc::Rc;

use parser_core_types::positioned_syntax::PositionedSyntax;

use super::code_action_types as cat;
use super::code_action_types::type_string;
use super::code_actions_utils as cu;
use super::extract_method_types as t;
use crate::full_fidelity_source_text as source_text;
use crate::pos::Pos;
use crate::relative_path::RelativePath;

type TypeAssocList = Vec<(String, Rc<type_string::T>)>;

/// note: returns None iff there are syntax errros
///
/// (`Full_fidelity_parser_env.make ~mode:File_info.Mstrict ()`: the mode is
/// not an input of the Rust parser.)
fn tree_from_source_text(st: &source_text::T) -> Option<PositionedSyntax> {
    let (root, errors, _state) = positioned_parser::parse_script(
        &source_text::source_text(st),
        parser_core_types::parser_env::ParserEnv::default(),
    );
    if errors.is_empty() { Some(root) } else { None }
}

/// `tree_from_string s |> Option.map Libhackfmt.format_tree`: `hackfmt`
/// parses the text itself (`Relative_path.default` is the empty path).
fn hackfmt(src: &str) -> String {
    let prefix = "<?hh\n";
    let text = format!("{}{}", prefix, src);
    let tree = ::hackfmt::parse(text.as_bytes(), "", false, false);
    if tree.errors.is_empty() {
        let formatted = cu::to_string(::hackfmt::format_tree(None, &tree).into());
        match formatted.strip_prefix(prefix) {
            Some(s) => s.to_string(),
            None => formatted,
        }
    } else {
        src.to_string()
    }
}

fn indent(indent_amount: isize, s: &str) -> String {
    let indentation = " ".repeat(indent_amount as usize);
    s.lines()
        .map(|line| format!("{}{}", indentation, line))
        .collect::<Vec<_>>()
        .join("\n")
}

fn return_type_string_of_candidate(return_: &TypeAssocList, candidate: &t::Candidate) -> String {
    let t::Candidate {
        selection_kind,
        is_async,
        iterator_kind,
        ..
    } = candidate;
    let wrap_return_type = |s: String| -> String {
        match (is_async, iterator_kind) {
            (true, Some(t::IteratorKind::Iterator)) => "AsyncIterator<_, _, _>".to_string(),
            (true, Some(t::IteratorKind::KeyedIterator)) => "AsyncKeyedIterator<_, _, _>".to_string(),
            (false, Some(t::IteratorKind::Iterator)) => "Iterator<_>".to_string(),
            (false, Some(t::IteratorKind::KeyedIterator)) => "KeyedIterator<_>".to_string(),
            (true, None) => format!("Awaitable<{}>", s),
            (false, None) => s,
        }
    };
    match selection_kind {
        t::SelectionKind::SelectionKindExpression(type_string) => wrap_return_type(type_string::to_string(type_string)),
        t::SelectionKind::SelectionKindStatement => wrap_return_type(match return_.as_slice() {
            [] => "void".to_string(),
            [(_, type_string)] => type_string::to_string(type_string),
            _ => format!(
                "({})",
                return_
                    .iter()
                    .map(|(_, type_string)| type_string::to_string(type_string))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }),
    }
}

fn body_string_of_candidate(st: &source_text::T, return_: &TypeAssocList, candidate: &t::Candidate) -> String {
    let t::Candidate {
        selection_kind,
        pos,
        iterator_kind,
        method_pos,
        ..
    } = candidate;
    let raw_body_string = {
        let (first_line, first_col) = crate::pos::line_column(pos);
        let exp_offset = source_text::position_to_offset(st, (first_line, first_col + 1));
        cu::to_string(source_text::sub(st, exp_offset, crate::pos::length(pos)))
    };
    match selection_kind {
        t::SelectionKind::SelectionKindExpression(_) => format!("return {};", raw_body_string),
        t::SelectionKind::SelectionKindStatement => {
            if iterator_kind.is_some() {
                raw_body_string
            } else {
                let method_indent_amount = crate::pos::line_column(method_pos).1;
                let format_as_return = |s: &str| -> String {
                    let whitespace = " ".repeat((2 * method_indent_amount) as usize);
                    format!("\n{}return {};", whitespace, s)
                };
                let return_string = match return_.as_slice() {
                    [] => String::new(),
                    [(var_name, _)] => format_as_return(var_name),
                    _ => format_as_return(&format!(
                        "tuple({})",
                        return_.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>().join(", ")
                    )),
                };
                format!("{}{}", raw_body_string, return_string)
            }
        }
    }
}

fn method_string_of_candidate(
    st: &source_text::T,
    params: &TypeAssocList,
    return_: &TypeAssocList,
    snippet: &str,
    candidate: &t::Candidate,
) -> String {
    let t::Candidate {
        method_is_static,
        is_async,
        method_pos,
        ..
    } = candidate;
    let return_type_string = return_type_string_of_candidate(return_, candidate);
    let body_string = body_string_of_candidate(st, return_, candidate);
    let add_modifiers = |s: String| -> String {
        let static_string = if *method_is_static {
            // The extracted function is static iff the function we are extracting from is static.
            // We could "Principle of Least Privilege" and default to `static` if `this` isn't used *but*
            // that would make things harder to mock and some people like mocking.
            "static "
        } else {
            ""
        };
        let function_kind_string = if *is_async { "async " } else { "" };
        format!("private {}{}{}", static_string, function_kind_string, s)
    };
    let params_string = params
        .iter()
        .map(|(name, type_string)| format!("{} {}", type_string::to_string(type_string), name))
        .collect::<Vec<_>>()
        .join(", ");
    // we format as a function before adding modifiers, since a function is hackfmt-able (a valid top-level form)
    let placeholder_to_replace_with_snippet = "the_function_name";
    let raw_function_string = format!(
        "function {}({}): {} {{\n{}\n}}",
        placeholder_to_replace_with_snippet, params_string, return_type_string, body_string
    );
    let indent_amount = crate::pos::line_column(method_pos).1;
    let add_suffix = |s: String| format!("{}\n\n", s);
    let s = hackfmt(&raw_function_string);
    let s = s.replacen(placeholder_to_replace_with_snippet, snippet, 1);
    let s = add_modifiers(s);
    let s = indent(indent_amount, &s);
    add_suffix(s)
}

fn method_call_string_of_candidate(
    params: &TypeAssocList,
    return_: &TypeAssocList,
    snippet: &str,
    candidate: &t::Candidate,
) -> String {
    let t::Candidate {
        method_is_static,
        selection_kind,
        is_async,
        iterator_kind,
        pos,
        method_pos,
        ..
    } = candidate;
    let args_string = params.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>().join(", ");
    let receiver_string = if *method_is_static { "self::" } else { "$this->" };
    let call_expr = format!("{}{}({})", receiver_string, snippet, args_string);
    let return_names = || return_.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>().join(", ");
    match iterator_kind {
        None => {
            // examples:
            // - `foo($arg1)`
            // - `await foo($arg1, $arg2)`
            let call_expr = if *is_async { format!("await {}", call_expr) } else { call_expr };
            match selection_kind {
                t::SelectionKind::SelectionKindExpression(_) => call_expr,
                t::SelectionKind::SelectionKindStatement => {
                    let fmt_assignment = |lhs_string: &str| format!("{} = {};", lhs_string, call_expr);
                    match return_.as_slice() {
                        [] => format!("{};", call_expr),
                        [(var_name, _)] => fmt_assignment(var_name),
                        _ => fmt_assignment(&format!("list({})", return_names())),
                    }
                }
            }
        }
        Some(iterator_kind) => {
            // example:
            // foreach(self::foo() as $value__) {
            //
            // }
            let await_string = if *is_async { "await " } else { "" };
            let as_string = match iterator_kind {
                t::IteratorKind::Iterator => "$value__",
                t::IteratorKind::KeyedIterator => "$key__ => $value__",
            };
            let comment_and_whitespace = {
                // generate comments like: "/* TODO: assign to $x, $y */"
                // TODO(T152359779): do more work for the user to handle assignments
                let indent_amount = crate::pos::line_column(method_pos).1;
                let call_site_indent_amount = crate::pos::line_column(pos).1;
                let outer_indent = " ".repeat(call_site_indent_amount as usize);
                let inner_indent = " ".repeat((call_site_indent_amount + indent_amount) as usize);
                let of_var_name_string = |var_names_string: &str| {
                    format!(
                        "\n{}/* TODO: assign to {} */\n{}\n{}",
                        inner_indent, var_names_string, inner_indent, outer_indent
                    )
                };
                match return_.as_slice() {
                    [] => format!("\n{}\n{}", inner_indent, outer_indent),
                    [(var_name, _)] => of_var_name_string(var_name),
                    _ => of_var_name_string(&return_names()),
                }
            };
            format!(
                "foreach ({} {}as {}) {{{}}}",
                call_expr, await_string, as_string, comment_and_whitespace
            )
        }
    }
}

fn include_leading_trivia(st: &source_text::T, path: &RelativePath, method_pos: &Pos) -> Pos {
    let new_pos = (|| {
        let root = tree_from_source_text(st)?;
        let (line, start, _) = crate::pos::info_pos(method_pos);
        let offset = source_text::position_to_offset(st, (line, start + 1));
        let parentage = cu::parentage(&root, offset);
        let node = parentage.into_iter().find(|node| node.is_methodish_declaration())?;
        let (line_one_based, _) = cu::leading_start_position(st, node);
        let offset = source_text::position_to_offset(st, (line_one_based, 0));
        let triple = (line_one_based, offset, offset);
        Some(crate::pos::make_from_lnum_bol_offset(path.clone(), triple, triple))
    })();
    match new_pos {
        Some(pos) => pos,
        None => {
            // When not found (such as when there are syntax errors),
            // fall back to just using the start of the method in the Nast
            crate::pos::shrink_to_start(&crate::pos::set_col_start(0, method_pos))
        }
    }
}

fn edits_of_candidate(st: &source_text::T, path: &RelativePath, candidate: &t::Candidate) -> cat::Edits {
    let t::Candidate {
        method_pos,
        params,
        return_,
        pos,
        placeholder_name,
        ..
    } = candidate;
    // (`Map.to_alist ~key_order:`Increasing`: a map has no two bindings of
    // a key, so `List.dedup_and_sort` leaves the list as it is.)
    let type_assoc_list_of =
        |map: &t::VarTys| -> TypeAssocList { map.iter().map(|(k, v)| (k.clone(), v.clone())).collect() };
    let params = type_assoc_list_of(params);
    let return_ = type_assoc_list_of(return_);
    let snippet = format!("${{0:{}}}", placeholder_name);
    let change_add_call = {
        let call_string = method_call_string_of_candidate(&params, &return_, &snippet, candidate);
        cat::Edit {
            pos: pos.clone(),
            text: call_string,
        }
    };
    let change_add_method = {
        let method_pos = include_leading_trivia(st, path, method_pos);
        let method_string = method_string_of_candidate(st, &params, &return_, &snippet, candidate);
        cat::Edit {
            pos: method_pos,
            text: method_string,
        }
    };
    cat::singleton(path.clone(), vec![change_add_method, change_add_call])
}

pub fn of_candidate<'a>(st: source_text::T, path: RelativePath, candidate: t::Candidate) -> cat::Refactor<'a> {
    let edits: cat::LazyEdits<'a> = Box::new(move || edits_of_candidate(&st, &path, &candidate));
    cat::Refactor(cat::EditData {
        title: "Extract into method".to_string(),
        edits,
        selection: None,
        trigger_inline_suggest: false,
    })
}
