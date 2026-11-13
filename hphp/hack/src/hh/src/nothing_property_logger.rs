// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `nothing_property_logger.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::aast;

use crate::ctx::Ctx;
use crate::hh_logger;
use crate::pos;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::*;
use crate::typing_make_type;
use crate::typing_reason;
use crate::typing_tdef_locl;
use crate::yojson::safe as yojson;

/// `object inherit Tast_visitor.handler_base ... end`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        let aast::Class_ { vars: c_vars, .. } = c;
        let print_if_nothing_hint = |cv: &tast::ClassVar| {
            let aast::ClassVar {
                span: cv_span,
                type_: aast::TypeHint(locl_ty, _),
                ..
            } = cv;
            let (_, locl_ty, _) = typing_tdef_locl::force_expand_typedef(
                &empty_expand_env(),
                &mut env.clone(),
                locl_ty.clone(),
            );
            if tast_env::is_sub_type(
                env,
                &locl_ty,
                &typing_make_type::nothing(typing_reason::none()),
            ) {
                let kind = match get_node(&locl_ty) {
                    Ty_::Tany(_) => "tany",
                    _ => "nothing",
                };
                let pos = pos::to_relative_string(cv_span);
                let json = yojson::T::Assoc(vec![
                    ("pos".to_string(), pos::json(&pos)),
                    ("kind".to_string(), yojson::T::String(kind.to_string())),
                ]);
                // unsorted: telemetry/logging, not snapshot-tested
                hh_logger::log(&format!(
                    "[Nothing_property_logger] {}",
                    yojson::to_string(&json)
                ))
            }
        };
        c_vars.iter().for_each(print_if_nothing_hint)
    }
}

/// `create_handler _ctx`
pub fn create_handler(_ctx: &Arc<Ctx>) -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}
