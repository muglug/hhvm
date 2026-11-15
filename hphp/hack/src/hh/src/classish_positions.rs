// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `diagnostics/classish_positions.ml`. See `hh/PORTING.md`.
//!
//! The types are those of
//! `oxidized::classish_positions_types` (`include Classish_positions_types`):
//! `Pos<P>` is `'p pos`, `ClassishPositions<P>` is `'p classish_positions`,
//! and `'p t` is [`T`].

use std::collections::BTreeMap;

use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::syntax_trait::SyntaxTrait;
pub use oxidized::classish_positions_types::ClassishPositions;
pub use oxidized::classish_positions_types::Pos as CPos;

use crate::full_fidelity_source_text as source_text;
use crate::pos::Pos;
use crate::relative_path::RelativePath;

/// Positional information for a collection of classes (`'p classish_positions S_map.t`)
pub type T<P> = BTreeMap<String, ClassishPositions<P>>;

type Token = parser_core_types::positioned_token::PositionedToken;

fn classish_body_elements_positions_for(to_pos: &dyn Fn(isize, isize) -> Pos, s: &PositionedSyntax) -> Vec<Pos> {
    let range_for_body_element = |e: &PositionedSyntax| -> Option<Pos> {
        let leading_token = e.leading_token()?;
        let trailing_token = e.trailing_token()?;
        let offset_start = (leading_token.offset + leading_token.leading_width) as isize;
        let offset_end = (trailing_token.offset + trailing_token.leading_width + trailing_token.width) as isize;
        Some(to_pos(offset_start, offset_end))
    };
    match &s.syntax {
        SyntaxVariant::SyntaxList(elements) => elements.iter().filter_map(range_for_body_element).collect(),
        _ => vec![],
    }
}

fn classish_positions_for(to_pos: &dyn Fn(isize, isize) -> Pos, s: &PositionedSyntax) -> Option<ClassishPositions<Pos>> {
    fn map_brace_token<A>(brace: &PositionedSyntax, f: impl FnOnce(&Token) -> A) -> Option<A> {
        match &brace.syntax {
            SyntaxVariant::Token(t) => Some(f(t)),
            _ => None,
        }
    }
    match &s.syntax {
        SyntaxVariant::ClassishBody(cb) => {
            let classish_start_of_body_offset =
                map_brace_token(&cb.classish_body_left_brace, |t| (t.offset + t.width) as isize)?;
            let classish_end_of_body_offset = map_brace_token(&cb.classish_body_right_brace, |t| t.offset as isize)?;
            let classish_just_before_closing_brace_offset =
                map_brace_token(&cb.classish_body_right_brace, |t| (t.offset + t.leading_width) as isize)?;
            let classish_just_after_closing_brace_offset =
                map_brace_token(&cb.classish_body_right_brace, |t| (t.offset + t.leading_width + t.width) as isize)?;
            let classish_body_elements = classish_body_elements_positions_for(to_pos, &cb.classish_body_elements);
            Some(ClassishPositions {
                start_of_body: to_pos(classish_start_of_body_offset, classish_start_of_body_offset),
                end_of_body: to_pos(classish_end_of_body_offset, classish_end_of_body_offset),
                closing_brace: to_pos(
                    classish_just_before_closing_brace_offset,
                    classish_just_after_closing_brace_offset,
                ),
                body_elements: classish_body_elements,
            })
        }
        _ => None,
    }
}

fn namespace_name(st: &source_text::T, s: &PositionedSyntax) -> Option<String> {
    match &s.syntax {
        SyntaxVariant::NamespaceDeclarationHeader(h) => {
            let name_token = &h.namespace_name;
            match &name_token.syntax {
                SyntaxVariant::Token(_) => Some(text(st, name_token)),
                // Anonymous namespace: namespace { ... }
                _ => None,
            }
        }
        _ => None,
    }
}

fn text(st: &source_text::T, node: &PositionedSyntax) -> String {
    let start = (node.leading_start_offset() + node.leading_width()) as isize;
    String::from_utf8_lossy(&source_text::sub(st, start, node.width() as isize)).into_owned()
}

/// Covnert ["Foo"; "Bar"] to \Foo\Bar.
fn name_from_parts(parts: &[String]) -> String {
    parts.iter().map(|p| format!("\\{}", p)).collect()
}

fn classish_positions_of_syntax(
    st: &source_text::T,
    to_pos: &dyn Fn(isize, isize) -> Pos,
    s: &PositionedSyntax,
) -> T<Pos> {
    // `namespace` is the list of the enclosing namespaces, innermost first
    // (OCaml conses), and `namespace @ [name]` is reversed in the name: the
    // OCaml quirk is kept.
    fn aux(
        st: &source_text::T,
        to_pos: &dyn Fn(isize, isize) -> Pos,
        acc: (T<Pos>, Vec<String>),
        s: &PositionedSyntax,
    ) -> (T<Pos>, Vec<String>) {
        let (positions, namespace) = acc;
        match &s.syntax {
            SyntaxVariant::Script(s) => aux(st, to_pos, (positions, namespace), &s.script_declarations),
            SyntaxVariant::SyntaxList(sl) => sl
                .iter()
                .fold((positions, namespace), |acc, s| aux(st, to_pos, acc, s)),
            SyntaxVariant::NamespaceDeclaration(n) => {
                let b = &n.namespace_body;
                match &b.syntax {
                    SyntaxVariant::NamespaceBody(nb) => {
                        // We're looking at: namespace Foo { ... }
                        let inner_namespace = match namespace_name(st, &n.namespace_header) {
                            Some(name) => {
                                let mut ns = vec![name];
                                ns.extend(namespace.iter().cloned());
                                ns
                            }
                            None => namespace.clone(),
                        };
                        let (positions, _) = aux(st, to_pos, (positions, inner_namespace), &nb.namespace_declarations);
                        (positions, namespace)
                    }
                    SyntaxVariant::NamespaceEmptyBody(_) => {
                        // We're looking at: namespace Foo;
                        let namespace = match namespace_name(st, &n.namespace_header) {
                            Some(name) => {
                                let mut ns = vec![name];
                                ns.extend(namespace);
                                ns
                            }
                            None => namespace,
                        };
                        (positions, namespace)
                    }
                    _ => (positions, namespace),
                }
            }
            SyntaxVariant::ClassishDeclaration(c) => match classish_positions_for(to_pos, &c.classish_body) {
                Some(classish_positions) => {
                    let mut parts = namespace.clone();
                    parts.push(text(st, &c.classish_name));
                    let name = name_from_parts(&parts);
                    let mut positions = positions;
                    positions.insert(name, classish_positions);
                    (positions, namespace)
                }
                _ => (positions, namespace),
            },
            _ => (positions, namespace),
        }
    }
    aux(st, to_pos, (BTreeMap::new(), vec![]), s).0
}

/// An empty positional map
pub fn empty<P>() -> T<P> {
    BTreeMap::new()
}

pub fn map_classish_positions<A, B>(f: &impl Fn(&A) -> B, cp: &ClassishPositions<A>) -> ClassishPositions<B> {
    ClassishPositions {
        start_of_body: f(&cp.start_of_body),
        end_of_body: f(&cp.end_of_body),
        closing_brace: f(&cp.closing_brace),
        body_elements: cp.body_elements.iter().map(f).collect(),
    }
}

/// Map over the embedded positions.
pub fn map<A, B>(f: impl Fn(&A) -> B, t: &T<A>) -> T<B> {
    t.iter()
        .map(|(k, v)| (k.clone(), map_classish_positions(&f, v)))
        .collect()
}

pub fn extract(s: &PositionedSyntax, st: &source_text::T, filename: &RelativePath) -> T<Pos> {
    let to_pos =
        |offset_start: isize, offset_end: isize| source_text::relative_pos(filename, st, offset_start, offset_end);
    classish_positions_of_syntax(st, &to_pos, s)
}

/// Map over the embedded positions
pub fn map_pos<A, B>(f: impl FnOnce(&A) -> B, p: &CPos<A>) -> CPos<B> {
    match p {
        CPos::Precomputed(p) => CPos::Precomputed(f(p)),
        CPos::ClassishStartOfBody(s) => CPos::ClassishStartOfBody(s.clone()),
        CPos::ClassishEndOfBody(s) => CPos::ClassishEndOfBody(s.clone()),
        CPos::ClassishClosingBrace(s) => CPos::ClassishClosingBrace(s.clone()),
    }
}

/// Find a position in the map.
pub fn find<P: Clone>(pos: &CPos<P>, t: &T<P>) -> Option<P> {
    let map_class = |class_name: &str, f: &dyn Fn(&ClassishPositions<P>) -> P| t.get(class_name).map(f);
    match pos {
        CPos::Precomputed(pos) => Some(pos.clone()),
        CPos::ClassishStartOfBody(class_name) => map_class(class_name, &|c| c.start_of_body.clone()),
        CPos::ClassishEndOfBody(class_name) => map_class(class_name, &|c| c.end_of_body.clone()),
        CPos::ClassishClosingBrace(class_name) => map_class(class_name, &|c| c.closing_brace.clone()),
    }
}

/// Return a map, mapping class-names to all the ranges in-between body
/// elements (i.e. methods, properties, ...) in that class
pub fn inbetween_body_element_positions(t: &T<Pos>) -> BTreeMap<String, Vec<Pos>> {
    let inbetween_positions_for = |cp: &ClassishPositions<Pos>| -> Vec<Pos> {
        // `List.sort ~compare:(Pos.compare_pos (fun _ _ -> 0))`
        let classish_body_elements = crate::rt::ocaml_list::stable_sort(cp.body_elements.clone(), |a, b| {
            crate::pos::compare_pos(|_, _| std::cmp::Ordering::Equal, a, b)
        });
        let (current_pos, mut posl) = classish_body_elements.into_iter().fold(
            (cp.start_of_body.clone(), vec![]),
            |(current_pos, mut acc): (Pos, Vec<Pos>), next_pos| {
                let whitespace = crate::pos::btw(
                    &crate::pos::shrink_to_end(&current_pos),
                    &crate::pos::shrink_to_start(&next_pos),
                );
                acc.push(whitespace);
                (next_pos, acc)
            },
        );
        // `List.rev (last :: posl)`, where `posl` was consed: the pushes in
        // order, then the last one.
        posl.push(crate::pos::btw(
            &crate::pos::shrink_to_end(&current_pos),
            &crate::pos::shrink_to_start(&cp.end_of_body),
        ));
        posl
    };
    t.iter()
        .map(|(k, v)| (k.clone(), inbetween_positions_for(v)))
        .collect()
}
