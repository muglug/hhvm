// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::ClassId;
use nast::ClassId_;
use nast::Expr;
use nast::Expr_;
use nast::FunctionPtrId;
use nast::Id;

use crate::prelude::*;

/// Port of `Naming_elab_dynamic_class_name`.
#[derive(Copy, Clone, Default)]
pub struct ElabDynamicClassNamePass;

impl Pass for ElabDynamicClassNamePass {
    fn on_ty_expr_bottom_up(&mut self, env: &Env, elem: &mut Expr) -> ControlFlow<()> {
        let Expr(_, pos, expr_) = elem;
        let invalid = match expr_ {
            Expr_::New(box (class_id, _, _, _, _)) if is_dynamic(class_id) => {
                let ClassId(_, ci_pos, _) = class_id;
                env.emit_error(NamingError::DynamicNewInStrictMode(ci_pos.clone()));
                // (annot, ci_pos, ci) ==> (annot, pos, CI (ci_pos, unknown)):
                // the class id takes the position of the whole expression
                let ci_pos = std::mem::replace(ci_pos, pos.clone());
                class_id.2 = ClassId_::CI(Id(ci_pos, sn::classes::UNKNOWN.to_string()));
                false
            }
            // TODO[mjt] can we decompose this case further? This is considering
            // both the class_id and the class_get_expr
            Expr_::ClassGet(box (class_id, _, _)) if !is_dynamic(class_id) => false,
            Expr_::ClassGet(box (ClassId(_, _, ClassId_::CIexpr(Expr(_, ci_pos, _))), _, _)) => {
                env.emit_error(NamingError::DynamicClassNameInStrictMode(ci_pos.clone()));
                true
            }
            // TODO[mjt] report error in strict mode
            Expr_::FunctionPointer(box (FunctionPtrId::FPClassConst(class_id, _), _, _))
                if is_dynamic(class_id) =>
            {
                true
            }
            // TODO[mjt] report error in strict mode
            Expr_::ClassConst(box (class_id, _)) if is_dynamic(class_id) => true,
            _ => false,
        };
        if invalid {
            let inner_expr = std::mem::replace(elem, elab_utils::expr::null());
            *elem = elab_utils::expr::invalid(inner_expr);
            Break(())
        } else {
            Continue(())
        }
    }
}

fn is_dynamic(class_id: &ClassId) -> bool {
    match &class_id.2 {
        ClassId_::CIparent
        | ClassId_::CIself
        | ClassId_::CIstatic
        | ClassId_::CI(..)
        | ClassId_::CIreified(..)
        | ClassId_::CIexpr(Expr(
            _,
            _,
            Expr_::Lvar(..)
            | Expr_::This
            | Expr_::Dollardollar(..)
            | Expr_::Await(..)
            | Expr_::Delay(..),
        )) => false,
        ClassId_::CIexpr(_) => true,
    }
}

