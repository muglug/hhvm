// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `class_pointer_check.ml`. See `hh/PORTING.md`.
//!
//! A place to consolidate some static class pointer checks before inference
//! takes care of them all.

use naming_special_names_rust as sn;
use oxidized::aast;

use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_class_pointers as class_pointer;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_print;

/// The object `handler`.
struct ClassPointerCheck;

impl<'a> tast_visitor::Handler<'a> for ClassPointerCheck {
    fn at_class_const(&mut self, env: &tast_env::Env, cc: &'a tast::ClassConst) {
        match &cc.kind {
            aast::ClassConstKind::CCConcrete(aast::Expr(_ty, pos, aast::Expr_::ClassConst(cc)))
                if cc.1.1 == sn::members::M_CLASS =>
            {
                let aast::ClassId(_cty, _cpos, cid_) = &cc.0;
                match tast_env::get_self_id(env) {
                    Some(e) if tast_env::is_enum(env, &e) => {
                        class_pointer::error_at_cls_const_expr(
                            env,
                            pos.clone(),
                            class_pointer::string_of_class_id_(cid_),
                        )
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn at_expr(&mut self, env: &tast_env::Env, e: &'a tast::Expr) {
        let error = |e: &tast::Expr| match e {
            aast::Expr(_ty, pos, aast::Expr_::ClassConst(cc)) if cc.1.1 == sn::members::M_CLASS => {
                let aast::ClassId(_cty, _cpos, cid_) = &cc.0;
                class_pointer::error_at_cls_const_expr(
                    env,
                    pos.clone(),
                    class_pointer::string_of_class_id_(cid_),
                )
            }
            aast::Expr(ty, pos, _) => {
                let ty_str = typing_print::error(None, env, ty);
                match get_node(ty) {
                    Ty_::TclassPtr(_) if env.genv.tcopt.class_pointer_ban_class_array_key => {
                        class_pointer::error_at_cls_ptr_type(env, pos.clone(), ty_str)
                    }
                    _ => {}
                }
            }
        };
        match &e.2 {
            // $d[C::class]
            aast::Expr_::ArrayGet(ag) if ag.1.is_some() => error(ag.1.as_ref().unwrap()),
            // dict[C::class => ...]
            aast::Expr_::KeyValCollection(kvc) => {
                let (_, _, fields) = &**kvc;
                for aast::Field(key, _val) in fields {
                    error(key)
                }
            }
            // keyset[C::class]
            aast::Expr_::ValCollection(vc)
                if matches!(
                    (vc.0).1,
                    aast::VcKind::Set | aast::VcKind::ImmSet | aast::VcKind::Keyset
                ) =>
            {
                let (_, _, exprs) = &**vc;
                for e in exprs {
                    error(e)
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(ClassPointerCheck)
}
