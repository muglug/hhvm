// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Util` (`write_symbol_info/util.ml`).

use oxidized::aast;
use oxidized::aast_defs;
use oxidized::ast_defs;
use oxidized::pos::Pos;
use parser_core_types::lexable_token::LexablePositionedToken;
use parser_core_types::lexable_token::LexableToken;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::positioned_token::PositionedToken;
use parser_core_types::syntax::SyntaxVariant;

use super::glean::hack::constraint_kind;
use super::glean::hack::name;
use super::glean::hack::namespace_q_name;
use super::glean::hack::q_name;
use super::glean::hack::reify_kind;
use super::glean::hack::type_const_kind;
use super::glean::hack::variance;
use super::glean::hack::visibility;
use super::glean::src::byte_span;
use crate::full_fidelity_source_text;
use crate::hh_logger;

pub fn is_enum_or_enum_class(k: &ast_defs::ClassishKind) -> bool {
    match k {
        ast_defs::ClassishKind::Cenum | ast_defs::ClassishKind::CenumClass(_) => true,
        ast_defs::ClassishKind::Cinterface
        | ast_defs::ClassishKind::Cclass(_)
        | ast_defs::ClassishKind::Ctrait => false,
    }
}

/// True if source text ends in a newline
pub fn ends_in_newline(source_text: &full_fidelity_source_text::T) -> bool {
    let last_char = full_fidelity_source_text::get(
        source_text,
        full_fidelity_source_text::length(source_text) - 1,
    );
    b'\n' == last_char || b'\r' == last_char
}

pub fn has_tabs_or_multibyte_codepoints(source_text: &full_fidelity_source_text::T) -> bool {
    // `Uutf.String.fold_utf_8`: counts the decoded characters (a malformed
    // sequence counts as one, and is reported as `Malformed`).
    let (num_chars, found_tab_or_malformed) =
        fold_utf_8_count(full_fidelity_source_text::text(source_text));
    found_tab_or_malformed || num_chars < full_fidelity_source_text::length(source_text)
}

/// The fold of `has_tabs_or_multibyte_codepoints` over `Uutf.String.fold_utf_8`:
/// the number of characters (and of malformed sequences), and whether there
/// was a tab or a malformed sequence.
fn fold_utf_8_count(s: &[u8]) -> (isize, bool) {
    let mut num = 0;
    let mut found = false;
    for item in uutf_decode(s) {
        num += 1;
        match item {
            Ok(c) => found = found || c == '\t',
            Err(_) => found = true,
        }
    }
    (num, found)
}

/// The sequence of `` `Uchar u`` (`Ok`) and `` `Malformed bytes`` (`Err`) that
/// `Uutf.String.fold_utf_8` decodes from `s`. As Uutf: the length of each
/// sequence is read from its first byte (`utf_8_len`), a sequence whose
/// continuation bytes are wrong is one malformed sequence of that length,
/// and a sequence cut by the end of the string is the last one.
pub fn uutf_decode(s: &[u8]) -> Vec<Result<char, &[u8]>> {
    fn utf_8_len(b: u8) -> usize {
        match b {
            0x00..=0x7F => 1,
            0x80..=0xC1 => 0,
            0xC2..=0xDF => 2,
            0xE0..=0xEF => 3,
            0xF0..=0xF4 => 4,
            _ => 0,
        }
    }
    /// `r_utf_8 s j l`
    fn r_utf_8(s: &[u8]) -> Result<char, &[u8]> {
        let malformed = Err(s);
        let uchar = |c: u32| char::from_u32(c).map_or(Err(s), Ok);
        match s.len() {
            1 => uchar(s[0] as u32),
            2 => {
                let (b0, b1) = (s[0] as u32, s[1] as u32);
                if b1 >> 6 != 0b10 {
                    malformed
                } else {
                    uchar(((b0 & 0x1F) << 6) | (b1 & 0x3F))
                }
            }
            3 => {
                let (b0, b1, b2) = (s[0] as u32, s[1] as u32, s[2] as u32);
                let c = ((b0 & 0x0F) << 12) | ((b1 & 0x3F) << 6) | (b2 & 0x3F);
                if b2 >> 6 != 0b10 {
                    malformed
                } else {
                    match b0 {
                        0xE0 if !(0xA0..=0xBF).contains(&b1) => malformed,
                        0xED if !(0x80..=0x9F).contains(&b1) => malformed,
                        0xE0 | 0xED => uchar(c),
                        _ if b1 >> 6 != 0b10 => malformed,
                        _ => uchar(c),
                    }
                }
            }
            4 => {
                let (b0, b1, b2, b3) = (s[0] as u32, s[1] as u32, s[2] as u32, s[3] as u32);
                let c = ((b0 & 0x07) << 18) | ((b1 & 0x3F) << 12) | ((b2 & 0x3F) << 6) | (b3 & 0x3F);
                if b3 >> 6 != 0b10 || b2 >> 6 != 0b10 {
                    malformed
                } else {
                    match b0 {
                        0xF0 if !(0x90..=0xBF).contains(&b1) => malformed,
                        0xF4 if !(0x80..=0x8F).contains(&b1) => malformed,
                        0xF0 | 0xF4 => uchar(c),
                        _ if b1 >> 6 != 0b10 => malformed,
                        _ => uchar(c),
                    }
                }
            }
            _ => unreachable!(),
        }
    }
    let mut out = vec![];
    let mut i = 0;
    while i < s.len() {
        let need = utf_8_len(s[i]);
        if need == 0 {
            out.push(Err(&s[i..i + 1]));
            i += 1;
            continue;
        }
        let rem = s.len() - i;
        if rem < need {
            out.push(Err(&s[i..]));
            break;
        }
        out.push(r_utf_8(&s[i..i + need]));
        i += need;
    }
    out
}

/// Split name or subnamespace from its parent namespace, and return
/// either Some (parent, name), or None if the name has no parent namespace.
/// The trailing slash is removed from the parent.
fn split_name(s: &str) -> Option<(String, String)> {
    match s.rfind('\\') {
        None => None,
        Some(pos) => {
            let name_start = pos + 1;
            let name = &s[name_start..];
            let parent_namespace = &s[..name_start - 1];
            if parent_namespace.is_empty() || name.is_empty() {
                None
            } else {
                Some((parent_namespace.to_string(), name.to_string()))
            }
        }
    }
}

/// The position that `tokens_to_pos_id` makes (`Full_fidelity_source_text.relative_pos`),
/// with the offsets the OCaml's has (`Pos.info_raw`).
///
/// `Line_break_map.offset_to_file_pos_triple`, which the OCaml's
/// `relative_pos` calls, keeps the line of its last lookup in global state
/// (`last_offset`, `curr_index`) shared by every source text, reset only when
/// a source text is made (`Line_break_map.make`), and searches from it: after
/// a lookup in another file it can find a line that starts after the
/// offset. The position then has a dummy end (offset -1: `File_pos_small`
/// has no negative column) instead of the real one. This happens in the
/// facts of the OCaml (a namespace declaration whose span starts at -1), and
/// [`line_break_map`] does the same lookups with the same state, so as to
/// write the same offsets; `pos` is the real position.
#[derive(Clone, Debug)]
pub struct NamespacePos {
    pub pos: Pos,
    /// `Pos.info_raw`: the start and end offsets, -1 for a dummy one.
    pub info_raw: (isize, isize),
}

/// `Util.make_byte_span` of a [`NamespacePos`] (of its OCaml offsets).
pub fn make_byte_span_of_namespace_pos(pos: &NamespacePos) -> byte_span::T {
    let (start, end) = pos.info_raw;
    byte_span::T {
        start,
        length: end - start,
    }
}

/// The global state of `Line_break_map` (see [`NamespacePos`]), per thread
/// (an OCaml process has one: a worker's job, or `hh_single_type_check`, runs
/// on one thread here).
pub mod line_break_map {
    use std::cell::Cell;

    thread_local! {
        /// `(!last_offset, !curr_index)`
        static STATE: Cell<(isize, isize)> = const { Cell::new((0, 0)) };
    }

    /// `reset_global_state`: what `Line_break_map.make` does first, at each
    /// `Full_fidelity_source_text.make` (the indexer makes the source text of
    /// each file in `File_info.create`).
    pub fn reset_global_state() {
        STATE.with(|s| s.set((0, 0)))
    }

    /// `offset_to_file_pos_triple bolmap offset`: (line, beginning of the
    /// line, offset), the line searched from the last one found.
    pub fn offset_to_file_pos_triple(bolmap: &[isize], offset: isize) -> (isize, isize, isize) {
        let (last_offset, mut curr_index) = STATE.with(|s| s.get());
        let len = bolmap.len() as isize;
        if curr_index >= len {
            curr_index = len - 1;
        }
        let forward_search = |mut i: isize| loop {
            let offset_at_i = bolmap[i as usize];
            if offset < offset_at_i {
                return i - 1;
            } else if i + 1 >= len {
                return len - 1;
            } else {
                i += 1
            }
        };
        let backward_search = |mut i: isize| loop {
            let offset_at_i = bolmap[i as usize];
            if offset >= offset_at_i {
                return i;
            } else if i == 0 {
                return 0;
            } else {
                i -= 1
            }
        };
        let index = if last_offset < offset && curr_index != len - 1 {
            forward_search(curr_index + 1)
        } else if last_offset > offset {
            backward_search(curr_index)
        } else {
            curr_index
        };
        let line_start = bolmap[index as usize];
        STATE.with(|s| s.set((offset, index)));
        (index + 1, line_start, offset)
    }
}

fn tokens_to_pos_id(
    st: &full_fidelity_source_text::T,
    hd: &PositionedToken,
    tl: &[&PositionedToken],
) -> (NamespacePos, String) {
    let path = full_fidelity_source_text::file_path(st);
    let start_offset = hd.leading_start_offset().unwrap_or(0) as isize;
    let text = |t: &PositionedToken| -> String {
        let source = full_fidelity_source_text::source_text(st);
        String::from_utf8_lossy(t.text_raw(&source)).into_owned()
    };
    let name = std::iter::once(hd)
        .chain(tl.iter().copied())
        .map(text)
        .collect::<Vec<_>>()
        .join("\\");
    let end_offset = start_offset + name.len() as isize;
    let pos = full_fidelity_source_text::relative_pos(path, st, start_offset, end_offset);
    // The OCaml's offsets (`relative_pos`: the start, then the end; see
    // `NamespacePos`): an end whose line starts after it is dummy.
    let bolmap = full_fidelity_source_text::offset_map(st);
    let raw = |offset| {
        let (_lnum, bol, offset) = line_break_map::offset_to_file_pos_triple(&bolmap, offset);
        if offset < bol { -1 } else { offset }
    };
    let start = raw(start_offset);
    let end = raw(end_offset);
    (NamespacePos { pos, info_raw: (start, end) }, name)
}

/// `Ast_error`, `Empty_namespace` of `namespace_ast_to_pos_id`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NamespaceError {
    AstError,
    EmptyNamespace,
}

/// Retrieve a namespace identifier and its position from an AST namespace node.
/// Raise Ast_error if the ast doesn't have the expected structure, and Empty_namespace
/// if the namespace is empty. )
pub fn namespace_ast_to_pos_id(
    ns_ast: &PositionedSyntax,
    st: &full_fidelity_source_text::T,
) -> Result<(NamespacePos, String), NamespaceError> {
    fn f(item: &PositionedSyntax) -> Result<&PositionedToken, NamespaceError> {
        match &item.syntax {
            SyntaxVariant::ListItem(li) => match &li.list_item.syntax {
                SyntaxVariant::Token(t) => Ok(&**t),
                _ => Err(NamespaceError::AstError),
            },
            _ => Err(NamespaceError::AstError),
        }
    }
    let (hd, tl) = match &ns_ast.syntax {
        SyntaxVariant::Token(t) => (&**t, vec![]),
        SyntaxVariant::QualifiedName(qn) => match &qn.qualified_name_parts.syntax {
            SyntaxVariant::SyntaxList(l) if !l.is_empty() => {
                let hd = f(&l[0])?;
                let tl = l[1..].iter().map(f).collect::<Result<Vec<_>, _>>()?;
                (hd, tl)
            }
            _ => return Err(NamespaceError::AstError),
        },
        SyntaxVariant::Missing => return Err(NamespaceError::EmptyNamespace),
        _ => return Err(NamespaceError::AstError),
    };
    Ok(tokens_to_pos_id(st, hd, &tl))
}

/// remove generated parameters of the form T/[ctx $f]
pub fn remove_generated_tparams<Ex: Clone, En: Clone>(
    tparams: &[aast_defs::Tparam<Ex, En>],
) -> Vec<aast_defs::Tparam<Ex, En>> {
    let param_name = |tp: &aast_defs::Tparam<Ex, En>| tp.name.1.clone();
    crate::typing_print::split_desugared_ctx_tparams_gen(tparams.to_vec(), param_name).1
}

/// Remove leading slash, if present, so names such as
/// Exception and \Exception are captured by the same fact
pub fn make_name(name: &str) -> name::T {
    name::T::key(crate::utils::strip_ns(name).to_string())
}

pub fn make_namespaceqname(ns: &str) -> namespace_q_name::T {
    namespace_q_name::T::key(match split_name(ns) {
        None => namespace_q_name::Key {
            name: make_name(ns),
            parent: None,
        },
        Some((parent_ns, namespace)) => namespace_q_name::Key {
            name: make_name(&namespace),
            parent: Some(make_namespaceqname(&parent_ns)),
        },
    })
}

pub fn make_qname(qname: &str) -> q_name::T {
    q_name::T::key(match split_name(qname) {
        None => q_name::Key {
            name: make_name(qname),
            namespace_: None,
        },
        Some((ns, name)) => q_name::Key {
            name: make_name(&name),
            namespace_: Some(make_namespaceqname(&ns)),
        },
    })
}

pub fn make_constraint_kind(k: &ast_defs::ConstraintKind) -> constraint_kind::T {
    match k {
        ast_defs::ConstraintKind::ConstraintAs => constraint_kind::T::As,
        ast_defs::ConstraintKind::ConstraintEq => constraint_kind::T::Equal,
        ast_defs::ConstraintKind::ConstraintSuper => constraint_kind::T::Super,
    }
}

pub fn make_visibility(v: &aast::Visibility) -> visibility::T {
    match v {
        aast::Visibility::Private => visibility::T::Private,
        aast::Visibility::Protected => visibility::T::Protected,
        aast::Visibility::Public => visibility::T::Public,
        aast::Visibility::Internal => visibility::T::Internal,
        aast::Visibility::ProtectedInternal => visibility::T::ProtectedInternal,
    }
}

pub fn make_type_const_kind(k: &aast::ClassTypeconst) -> type_const_kind::T {
    match k {
        aast::ClassTypeconst::TCAbstract(_) => type_const_kind::T::Abstract,
        aast::ClassTypeconst::TCConcrete(_) => type_const_kind::T::Concrete,
    }
}

pub fn make_byte_span(pos: &Pos) -> byte_span::T {
    byte_span::T {
        start: pos.info_raw().0 as isize,
        length: (pos.end_offset() - pos.start_offset()) as isize,
    }
}

pub fn make_variance(v: &ast_defs::Variance) -> variance::T {
    match v {
        ast_defs::Variance::Contravariant => variance::T::Contravariant,
        ast_defs::Variance::Covariant => variance::T::Covariant,
        ast_defs::Variance::Invariant => variance::T::Invariant,
    }
}

pub fn make_reify_kind(k: &ast_defs::ReifyKind) -> reify_kind::T {
    match k {
        ast_defs::ReifyKind::Erased => reify_kind::T::Erased,
        ast_defs::ReifyKind::Reified => reify_kind::T::Reified,
        ast_defs::ReifyKind::SoftReified => reify_kind::T::SoftReified,
    }
}

pub fn class_hint_to_qname(h: &aast_defs::ClassHint) -> Option<q_name::T> {
    let aast_defs::Hint(_, chint) = h;
    match &**chint {
        aast_defs::Hint_::Happly(cname, _) => Some(make_qname(&cname.1)),
        chint => {
            hh_logger::log(&format!(
                "Shouldn't happen: expected class hint bug got {}",
                crate::format::asprintf(|f| {
                    let unit = |_: &mut crate::format::Formatter, _: &()| ();
                    let mut p = crate::ast_show::P::new(f, &unit, &unit);
                    crate::ast_show::aast_defs::pp_hint_(&mut p, chint)
                })
            ));
            None
        }
    }
}
