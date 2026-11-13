// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `type_const_check.ml`. See `hh/PORTING.md`.

use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_const_reifiable::check_reifiable;
use crate::typing_defs::AbstractTypeconst;
use crate::typing_defs::ConcreteTypeconst;
use crate::typing_defs::Typeconst;
use crate::typing_enforceable_hint;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_class_typeconst_def(&mut self, env: &Env, tc_def: &'a tast::ClassTypeconstDef) {
        let name = &tc_def.name.1;
        let cls_opt = decl_entry::bind(
            decl_entry::of_option_or_does_not_exist(tast_env::get_self_id(env)),
            |id| tast_env::get_class(env, &id),
        );
        match cls_opt {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            decl_entry::T::Found(cls) => match tast_env::get_typeconst(env, &cls, name) {
                None => {}
                Some(tc) => {
                    match &tc.kind {
                        Typeconst::TCAbstract(AbstractTypeconst {
                            default: Some(ty), ..
                        })
                        | Typeconst::TCConcrete(ConcreteTypeconst { ty }) => {
                            let (tp_pos, enforceable) =
                                cls::get_typeconst_enforceability(&cls, name).unwrap();
                            if enforceable {
                                typing_enforceable_hint::validate_type(
                                    env,
                                    pos_or_decl::unsafe_to_raw_pos(PosOrDecl::from(
                                        tc.name.pos().clone(),
                                    )),
                                    ty,
                                    |pos: Pos, ty_info| {
                                        typing_error_utils::add_typing_error(
                                            &typing_error::primary(
                                                primary::T::Invalid_enforceable_type {
                                                    pos,
                                                    ty_info,
                                                    kind: primary::InvalidEnforceableTypeKind::constant,
                                                    tp_pos: tp_pos.clone(),
                                                    tp_name: name.clone(),
                                                },
                                            ),
                                            env,
                                        )
                                    },
                                )
                            }
                        }
                        _ => {}
                    }
                    if tc.origin.as_str() == cls::name(&cls) {
                        if let Some(attr_pos) = &tc.reifiable {
                            check_reifiable(env, &tc, PosOrDecl::from(attr_pos.clone()))
                        }
                    }
                }
            },
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
