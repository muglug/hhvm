// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_type_definition.ml`. See
//! `hh/PORTING.md`.
//!
//! Owned by **F1** (plan §7.3). Behind `server`: its result type is in
//! `Server_command_types`, and it calls E1's `Server_infer_type`.
//!
//! Ported in full, but compiled out (`#[cfg(any())]`) until E1's
//! `server_infer_type::{T, human_friendly_type_at_pos, get_type, get_env}`
//! and N1's `naming_global::genv::type_pos` (`Naming_global.GEnv.type_pos`)
//! exist: whoever lands the second of them deletes the `#[cfg(any())]`
//! lines (and fixes the names if they differ).

#[cfg(any())]
use std::sync::Arc;

#[cfg(any())]
use crate::file_content;
#[cfg(any())]
use crate::provider_context;
#[cfg(any())]
use crate::server_command_types::go_to_type_definition;
#[cfg(any())]
use crate::tast;
#[cfg(any())]
use crate::tast_with_dynamic;
#[cfg(any())]
use crate::typing_defs;
#[cfg(any())]
use crate::typing_defs::Ty_;

#[cfg(any())]
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

/// For serverless ide
#[cfg(any())]
pub fn go_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> go_to_type_definition::Result {
    let crate::tast_provider::ComputeTastResult { tast, .. } =
        crate::tast_provider::compute_tast_quarantined(ctx, entry);
    go_common(ctx, &tast, pos)
}
