// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `xhp_check.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Id;
use oxidized::message::Message;
use oxidized::name_context::NameContext;
use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::pos::Pos;

use crate::decl_entry;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::get_reason;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_reason as reason;

pub fn check_xhp_children(env: &Env, pos: &Pos, ty: &Ty) {
    let (is_xhp_child, subty_err_opt) = tast_env::is_xhp_child(env, pos, ty);
    if let Some(err) = &subty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    if !is_xhp_child {
        let ty_str = {
            let env = env.clone();
            let ty = ty.clone();
            typing_error::Lazy::new(move || tast_env::print_error_ty(Some(true), &env, &ty))
        };
        let ty_reason_msg = {
            let r = get_reason(ty).clone();
            ty_str.map(move |ty_str| {
                reason::to_string(&("This is ".to_string() + ty_str), &r)
                    .into_iter()
                    .map(|(pos, msg)| Message(pos, msg.into()))
                    .collect()
            })
        };
        typing_error_utils::add_typing_error(
            &typing_error::xhp(primary::xhp::T::Illegal_xhp_child {
                pos: pos.clone(),
                ty_reason_msg,
            }),
            env,
        )
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        match e {
            aast::Expr(_, _, aast::Expr_::Xml(xml)) => {
                let (_, _, tel) = &**xml;
                for aast::Expr(ty, pos, _) in tel {
                    check_xhp_children(env, pos, ty)
                }
            }
            _ => {}
        }
    }

    fn at_xhp_child(&mut self, env: &Env, child: &'a tast::XhpChild) {
        match child {
            aast::XhpChild::ChildName(Id(p, name))
                if !sn::xhp::is_reserved(name) && !sn::xhp::is_xhp_category(name) =>
            {
                match tast_env::get_class(env, name) {
                    decl_entry::T::Found(_) | decl_entry::T::NotYetAvailable => {}
                    decl_entry::T::DoesNotExist => {
                        // `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic
                        // error custom_err_config)`, where `custom_err_config` is
                        // `Typechecker_options.custom_error_config (Tast_env.get_tcopt env)`:
                        // the renderer of naming errors of this crate does not take
                        // the custom error configuration.
                        if let Some(diagnostic) =
                            crate::naming_errors::to_diagnostic(NamingPhaseError::Naming(
                                NamingError::UnboundName {
                                    pos: p.clone(),
                                    name: name.clone(),
                                    kind: NameContext::ClassContext,
                                },
                            ))
                        {
                            crate::diagnostics_state::add_diagnostic(diagnostic)
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
