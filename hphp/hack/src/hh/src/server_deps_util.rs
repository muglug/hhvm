// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_deps_util.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::pos::Pos;
use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::syntax_trait::SyntaxTrait;

use crate::provider_context;
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

pub fn body_symbols<'o>(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    filter_against: &'o [Occ],
    occ: &Occ,
    def: &Def,
) -> Vec<&'o Occ> {
    let node_opt = crate::server_symbol_definition::get_definition_cst_node_ctx(ctx, entry, &def.kind, &def.pos);
    match node_opt {
        None => vec![],
        Some(node) => {
            // `Full_fidelity_positioned_syntax.position (Pos.filename def.pos) node`
            let source_text = crate::ast_provider::compute_source_text(entry);
            let indexed = IndexedSourceText::new(crate::full_fidelity_source_text::source_text(&source_text));
            let p = indexed.relative_pos(node.start_offset(), node.end_offset());
            let span_pos = Pos::from_lnum_bol_offset(Arc::new(def.pos.filename().clone()), p.start, p.end);
            filter_against
                .iter()
                .filter(|o| !std::ptr::eq(*o, occ) && crate::pos::contains(&span_pos, &o.pos))
                .collect()
        }
    }
}

pub fn get_def_setup(
    acc_ctx_in: &provider_context::T,
    file: &str,
) -> (provider_context::T, Arc<provider_context::Entry>, oxidized::nast::Program) {
    let path = crate::relative_path::create_detect_prefix(file);
    let (acc_ctx_out, entry) = provider_context::add_entry_if_missing(acc_ctx_in, path);
    // `get_ast_getdef`: `Server_symbol_definition.go ctx (Some ast)` is
    // applied by the callers to this AST.
    let ast = crate::ast_provider::compute_ast(provider_context::get_popt(&acc_ctx_out), &entry);
    (acc_ctx_out, entry, ast)
}
