// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Build_fact` (`write_symbol_info/build_fact.ml`).

use oxidized::aast;
use oxidized::ast_defs;
use oxidized::pos::Pos;

use super::glean::fact_id;
use super::glean::hack::argument;
use super::glean::hack::call_argument;
use super::glean::hack::context_;
use super::glean::hack::method_declaration;
use super::glean::hack::module_declaration;
use super::glean::hack::module_membership;
use super::glean::hack::named_kind;
use super::glean::hack::parameter;
use super::glean::hack::readonly_kind;
use super::glean::hack::signature;
use super::glean::hack::type_;
use super::glean::hack::type_info;
use super::glean::hack::user_attribute;
use super::glean::hack::x_ref;
use super::glean::hack::x_ref_target;
use super::glean::src::rel_byte_span;
use super::predicate;
use super::pretty;
use super::util;
use super::xrefs;
use crate::aast_utils;
use crate::full_fidelity_source_text;

pub fn method_decl(
    meth_name: &str,
    con_name: &str,
    con_type: predicate::ParentContainerType,
) -> method_declaration::T {
    let qname = util::make_qname(con_name);
    let name = util::make_name(meth_name);
    let container = predicate::container_decl_qname(con_type, qname);
    method_declaration::T::key(method_declaration::Key { name, container })
}

pub fn attributes<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    attrs: &[aast::UserAttribute<Ex, En>],
) -> Vec<user_attribute::T> {
    attrs
        .iter()
        .map(|attr| {
            let ast_defs::Id(_, name) = &attr.name;
            let name = util::make_name(name);
            // (`List.fold_right`: the parameters from the last one, without
            // effects.)
            let parameters = attr
                .params
                .iter()
                .map(|expr| pretty::expr_to_string(source_text, expr))
                .collect();
            user_attribute::T::key(user_attribute::Key {
                name,
                parameters,
                qname: None,
            })
        })
        .collect()
}

pub fn call_arguments(arguments: Vec<(Option<argument::T>, Pos)>) -> Vec<call_argument::T> {
    let argument = |span, arg_opt| call_argument::T {
        span,
        argument: arg_opt,
    };
    let mut fields = vec![];
    let mut last_start = 0;
    for (arg_opt, pos) in arguments {
        let (start, _) = pos.info_raw();
        let start = start as isize;
        let length = (pos.end_offset() - pos.start_offset()) as isize;
        let rel_span = rel_byte_span::T {
            offset: start - last_start,
            length,
        };
        fields.push(argument(rel_span, arg_opt));
        last_start = start;
    }
    fields
}

/// params come with the string representation for their type
/// and an option type_xref fact
pub fn signature<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    params: Vec<(&aast::FunParam<Ex, En>, Option<type_info::T>, Option<type_::T>)>,
    ctxs_hints: Option<&aast::Contexts>,
    returns: Option<type_::T>,
    returns_type_info: Option<type_info::T>,
) -> signature::T {
    let hint_to_ctx = |hint: &aast::Hint| context_::T::key(pretty::hint_to_string(true, hint));
    let f = |aast::Contexts(_pos, hint): &aast::Contexts| hint.iter().map(hint_to_ctx).collect::<Vec<_>>();
    let ctxs_hints = ctxs_hints.map(f);
    let param = |(p, type_xref, type_): (&aast::FunParam<Ex, En>, Option<type_info::T>, Option<type_::T>)| {
        parameter::T {
            name: util::make_name(&p.name),
            type_,
            default_value: aast_utils::get_param_default(p)
                .map(|e| pretty::expr_to_string(source_text, e)),
            is_inout: match p.callconv {
                ast_defs::ParamKind::Pinout(_) => true,
                ast_defs::ParamKind::Pnormal => false,
            },
            is_variadic: aast_utils::is_param_variadic(p),
            attributes: attributes(source_text, &p.user_attributes),
            type_info: type_xref,
            readonly: p.readonly.as_ref().map(|_| readonly_kind::T::Readonly),
            named: p.named.as_ref().map(|_| named_kind::T::Named),
        }
    };
    let parameters = params.into_iter().map(param).collect();
    signature::T::key(signature::Key {
        returns,
        parameters,
        contexts: ctxs_hints,
        returns_type_info,
    })
}

fn generic_xrefs(sym_pos: impl Iterator<Item = (x_ref_target::T, Vec<pretty::Pos>)>) -> Vec<x_ref::T> {
    let mut xrefs = vec![];
    for (target, pos_list) in sym_pos {
        let mut sorted_pos = pos_list;
        sorted_pos.sort_by(pretty::compare_pos);
        sorted_pos.dedup();
        let mut byte_spans = vec![];
        let mut last_start = 0;
        for pretty::Pos { start, length } in sorted_pos {
            let span = rel_byte_span::T {
                offset: start - last_start,
                length,
            };
            byte_spans.push(span);
            last_start = start;
        }
        let xref = x_ref::T {
            ranges: byte_spans,
            target,
        };
        xrefs.push(xref);
    }
    // there's no specified order for xref arrays, but it helps to avoid non-determinism
    // when diffing dbs
    // (The OCaml conses the xrefs, then sorts them with the stable
    // `List.sort`: the order of equal xrefs is not observable.)
    xrefs.sort();
    xrefs
}

pub fn xrefs(fact_map: &xrefs::FactMap) -> Vec<x_ref::T> {
    let f = |(_fact_id, (target, pos_list)): (&fact_id::T, &(x_ref_target::T, Vec<Pos>))| {
        let util_pos_list = pos_list
            .iter()
            .map(|pos| {
                let start = pos.info_raw().0 as isize;
                let length = (pos.end_offset() - pos.start_offset()) as isize;
                pretty::Pos { start, length }
            })
            .collect();
        (target.clone(), util_pos_list)
    };
    let sym_pos = fact_map.iter().map(f);
    generic_xrefs(sym_pos)
}

pub fn hint_xrefs(sym_pos: Vec<(x_ref_target::T, Vec<pretty::Pos>)>) -> Vec<x_ref::T> {
    generic_xrefs(sym_pos.into_iter())
}

pub fn module_membership(decl_id: fact_id::T, internal: bool) -> module_membership::T {
    module_membership::T {
        declaration: module_declaration::T::Id(decl_id),
        internal,
    }
}
