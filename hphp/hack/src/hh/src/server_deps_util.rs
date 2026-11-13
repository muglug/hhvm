// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_deps_util.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use crate::code_actions::code_actions_utils as cu;
use crate::nast;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path;
use crate::symbol_definition;
use crate::symbol_occurrence;
use crate::symbol_occurrence::Kind;

pub type Occ = symbol_occurrence::T<Pos>;
pub type Def = symbol_definition::T<Pos>;

pub fn symbol_in_call_hierarchy(sym_occ: &Occ) -> bool {
    match &sym_occ.type_ {
        Kind::Class(_) => true,
        Kind::BuiltInType(_) => false,
        Kind::Function => true,
        Kind::Method(..) => true,
        Kind::LocalVar => false,
        Kind::TypeVar => false,
        Kind::Property(..) => true,
        Kind::XhpLiteralAttr(..) => false,
        Kind::ClassConst(..) => false,
        Kind::Typeconst(..) => false,
        Kind::GConst => false,
        Kind::Attribute(_) => true,
        Kind::EnumClassLabel(..) => true,
        Kind::Keyword(_) => false,
        Kind::PureFunctionContext => false,
        Kind::BestEffortArgument(..) => false,
        Kind::HhFixme => false,
        Kind::HhIgnore => false,
        Kind::Module => true,
    }
}

pub fn is_target(target_line: isize, target_char: isize, occ: &Occ) -> bool {
    let (l, start, end_) = crate::pos::info_pos(&occ.pos);
    l == target_line && start <= target_char && target_char - 1 <= end_
}

/// (`phys_equal o occ`: `occ` is an element of `filter_against`.)
pub fn body_symbols<'a>(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    filter_against: &'a [Occ],
    occ: &Occ,
    def: &Def,
) -> Vec<&'a Occ> {
    let node_opt = crate::server_symbol_definition::get_definition_cst_node_ctx(ctx, entry, &def.kind, &def.pos);
    match node_opt {
        None => vec![],
        Some(node) => {
            // `Full_fidelity_positioned_syntax.position (Pos.filename def.pos) node`
            let st = crate::ast_provider::compute_source_text(entry);
            let span_pos = crate::full_fidelity_source_text::relative_pos(
                def.pos.filename(),
                &st,
                cu::start_offset(&node),
                cu::end_offset(&node),
            );
            filter_against
                .iter()
                .filter(|o| !std::ptr::eq(*o, occ) && crate::pos::contains(&span_pos, &o.pos))
                .collect()
        }
    }
}

pub fn get_ast_getdef(ctx: &provider_context::T, entry: &Arc<provider_context::Entry>) -> nast::Program {
    crate::ast_provider::compute_ast(&provider_context::get_popt(ctx), entry)
}

/// `get_def_setup acc_ctx_in file`: the context, the entry and the AST
/// (`get_def` is [`get_def`] with them).
pub fn get_def_setup(
    acc_ctx_in: &provider_context::T,
    file: &str,
) -> (provider_context::T, Arc<provider_context::Entry>, nast::Program) {
    let path = relative_path::create_detect_prefix(file);
    let (acc_ctx_out, entry) = provider_context::add_entry_if_missing(acc_ctx_in, path);
    let ast = get_ast_getdef(&acc_ctx_out, &entry);
    (acc_ctx_out, entry, ast)
}

/// `Server_symbol_definition.go ctx (Some ast)`
pub fn get_def(ctx: &provider_context::T, ast: &nast::Program, occ: &Occ) -> Option<Def> {
    crate::server_symbol_definition::go(ctx, Some(ast), occ)
}
