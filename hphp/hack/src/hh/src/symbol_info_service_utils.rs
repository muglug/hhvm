// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/symbol_info_service_utils.ml`. See `hh/PORTING.md`.

use oxidized::aast;

use crate::diagnostics_state;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::server_command_types::symbol_info_service::Result;
use crate::server_command_types::symbol_info_service::SymbolFunCall;
use crate::server_command_types::symbol_type;
use crate::tast_provider;

pub type RawResult = Vec<(Vec<SymbolFunCall>, Vec<symbol_type::T>)>;

fn recheck_naming(ctx: &provider_context::T, filename_l: &[RelativePath]) {
    for file in filename_l {
        diagnostics_state::ignore_(|| {
            // We only need to name to find references to locals
            for def in crate::ast_provider::get_ast(false, ctx, file).0 {
                match def {
                    aast::Def::Fun(f) => {
                        let _ = crate::naming::fun_def(ctx, *f);
                    }
                    aast::Def::Class(c) => {
                        let _ = crate::naming::class_(ctx, *c);
                    }
                    _ => {}
                }
            }
        })
    }
}

pub fn helper(ctx: &provider_context::T, mut acc: RawResult, filename_l: &[RelativePath]) -> RawResult {
    let filename_l: Vec<RelativePath> = filename_l.iter().rev().cloned().collect();
    recheck_naming(ctx, &filename_l);
    let tasts: Vec<_> = filename_l
        .iter()
        .map(|path| {
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_unquarantined(&ctx, &entry);
            tast.under_normal_assumptions
        })
        .collect();
    let tasts: Vec<&[crate::tast::Def]> = tasts.iter().map(|t| t.as_slice()).collect();
    let fun_calls = crate::symbol_fun_call_service::find_fun_calls(ctx, &tasts);
    let symbol_types = crate::symbol_type_service::generate_types(ctx, &tasts);
    acc.insert(0, (fun_calls, symbol_types));
    acc
}

/// Format result from '(fun_calls * symbol_types) list' raw result into
/// 'fun_calls list, symbol_types list' and store in SymbolInfoService.result
pub fn format_result(raw_result: RawResult) -> Result {
    let mut result1: Vec<SymbolFunCall> = vec![];
    let mut result2: Vec<symbol_type::T> = vec![];
    for (part1, part2) in raw_result {
        // `List.rev_append part result`
        result1.splice(0..0, part1.into_iter().rev());
        result2.splice(0..0, part2.into_iter().rev());
    }
    Result {
        fun_calls: result1,
        symbol_types: result2,
    }
}
