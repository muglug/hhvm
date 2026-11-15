// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_type_definition.ml`. See
//! `hh/PORTING.md`.
//!
//! Behind `server`: its result type is in `Server_command_types`.
//!
//! It calls `server_infer_type::{T, human_friendly_type_at_pos, get_type,
//! get_env}` and `naming_global::genv::type_pos`
//! (`Naming_global.GEnv.type_pos`).

use std::sync::Arc;

use crate::file_content;
use crate::provider_context;
use crate::server_command_types::go_to_type_definition;
use crate::tast;
use crate::tast_with_dynamic;
use crate::typing_defs;
use crate::typing_defs::Ty_;

fn go_common(
    ctx: &provider_context::T,
    tast: &tast_with_dynamic::T<tast::Program>,
    pos: &file_content::position::T,
) -> go_to_type_definition::Result {
    let info_opt = crate::server_infer_type::human_friendly_type_at_pos(false, ctx, tast, pos);
    match info_opt {
        None => vec![],
        Some(info) => {
            let ty = crate::server_infer_type::get_type(&info);
            fn handle_type(
                ctx: &provider_context::T,
                info: &crate::server_infer_type::T,
                acc: &mut Vec<(crate::pos::Pos, String)>,
                ty: &tast::Ty,
            ) {
                match typing_defs::get_node(ty) {
                    Ty_::Tclass((_, str), _, _) => {
                        match crate::naming_global::genv::type_pos(ctx, str) {
                            None => {}
                            Some(pos) => acc.push((pos, str.clone())),
                        }
                    }
                    Ty_::Toption(ty_) => handle_type(ctx, info, acc, ty_),
                    Ty_::Tunion(ty_lst) => {
                        for y in ty_lst {
                            handle_type(ctx, info, acc, y)
                        }
                    }
                    Ty_::Tfun(fn_type) => {
                        let ret_type = &fn_type.ret;
                        match typing_defs::get_node(ret_type) {
                            Ty_::Tprim(_) => {
                                // default to function definition
                                acc.push((
                                    crate::naming_provider::resolve_position(
                                        ctx,
                                        &typing_defs::get_pos(ty),
                                    ),
                                    crate::tast_env::print_ty(crate::server_infer_type::get_env(info), ty),
                                ))
                            }
                            _ => handle_type(ctx, info, acc, ret_type),
                        }
                    }
                    _ => {}
                }
            }
            // (`acc` is consed: the OCaml list is `acc` backwards.)
            let mut acc = vec![];
            handle_type(ctx, &info, &mut acc, &ty);
            acc.into_iter()
                .rev()
                .map(|(pos, s)| (crate::pos::to_absolute(&pos), s))
                .collect()
        }
    }
}

/// To do with "go to type definition" functionality. For serverless ide
pub fn go_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> go_to_type_definition::Result {
    let crate::tast_provider::ComputeTast { tast, .. } =
        crate::tast_provider::compute_tast_quarantined(ctx, entry);
    go_common(ctx, &tast, pos)
}

#[cfg(test)]
mod tests;
