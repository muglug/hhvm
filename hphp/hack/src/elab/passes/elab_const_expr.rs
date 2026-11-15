// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use bitflags::bitflags;
use nast::CallExpr;
use nast::Class_;
use nast::ClassConstKind;
use nast::ClassId;
use nast::ClassId_;
use nast::ClassishKind;
use nast::Expr;
use nast::Expr_;
use nast::FunDef;
use nast::Gconst;
use nast::Hint;
use nast::Hint_;
use nast::KvcKind;
use nast::ModuleDef;
use nast::Pos;
use nast::Typedef;
use nast::Uop;
use nast::VcKind;
use oxidized::file_info;

use crate::prelude::*;

/// Port of `Naming_elab_const_expr` (both its top-down and bottom-up pass).
#[derive(Copy, Clone)]
pub struct ElabConstExprPass {
    mode: file_info::Mode,
    flags: Flags,
}

bitflags! {
    #[derive(Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Clone, Copy)]
    struct Flags: u8 {
        const IN_ENUM_CLASS = 1 << 0;
        const ENFORCE_CONST_EXPR = 1 << 1;
    }
}

impl ElabConstExprPass {
    pub fn in_enum_class(&self) -> bool {
        self.flags.contains(Flags::IN_ENUM_CLASS)
    }

    pub fn set_in_enum_class(&mut self, value: bool) {
        self.flags.set(Flags::IN_ENUM_CLASS, value)
    }

    pub fn enforce_const_expr(&self) -> bool {
        self.flags.contains(Flags::ENFORCE_CONST_EXPR)
    }

    pub fn set_enforce_const_expr(&mut self, value: bool) {
        self.flags.set(Flags::ENFORCE_CONST_EXPR, value)
    }
}

impl Default for ElabConstExprPass {
    fn default() -> Self {
        ElabConstExprPass {
            mode: file_info::Mode::Mstrict,
            flags: Flags::default(),
        }
    }
}

/// Report an illegal constant at `pos` and replace the expression with the
/// invalid expression marker.
fn illegal(env: &Env, pos: Pos, elem: &mut Expr) -> ControlFlow<()> {
    env.emit_error(NamingError::IllegalConstant(pos));
    let inner_expr = std::mem::replace(elem, elab_utils::expr::null());
    *elem = elab_utils::expr::invalid(inner_expr);
    Break(())
}

impl Pass for ElabConstExprPass {
    // We can determine that certain expressions are invalid based on one-level
    // pattern matching. We prefer to do this since we can stop the transformation
    // early in these cases. For cases where we need to pattern match on the
    // expression more deeply, we use the bottom-up pass
    fn on_ty_expr_top_down(&mut self, env: &Env, elem: &mut Expr) -> ControlFlow<()> {
        if !self.enforce_const_expr() {
            return Continue(());
        }
        let Expr(_, pos, expr_) = elem;
        // `None` for a valid expression, or the position of the error.
        let illegal_at: Option<Pos> = match &expr_ {
            // -- always valid ---------------------------------------------
            Expr_::Id(..)
            | Expr_::Null
            | Expr_::True
            | Expr_::False
            | Expr_::Int(_)
            | Expr_::Float(_)
            | Expr_::String(_)
            | Expr_::FunctionPointer(..)
            | Expr_::Eif(..)
            | Expr_::Tuple(..)
            | Expr_::Shape(..)
            | Expr_::Upcast(..)
            | Expr_::Package(..)
            | Expr_::PrefixedString(..) => None,

            // -- markers --------------------------------------------------
            Expr_::Invalid(..) | Expr_::Hole(..) => None,

            // -- handled bottom-up ----------------------------------------
            Expr_::Nameof(_) | Expr_::ClassConst(_) => None,

            // -- conditionally valid --------------------------------------
            // NB we can perform this top-down since the all valid hints
            // are already in canonical
            Expr_::As(box nast::As_ {
                hint: Hint(_, box hint_),
                ..
            }) => match hint_ {
                Hint_::Happly(id, _) => Some(id.0.clone()),
                _ => Some(pos.clone()),
            },
            Expr_::Unop(box (uop, _)) => match uop {
                Uop::Uplus | Uop::Uminus | Uop::Utild | Uop::Unot => None,
                _ => Some(pos.clone()),
            },
            Expr_::Binop(..) => None,
            Expr_::Assign(..) => Some(pos.clone()),
            Expr_::ValCollection(box ((_, vc_kind), _, _)) => match vc_kind {
                VcKind::Vec | VcKind::Keyset => None,
                _ => Some(pos.clone()),
            },
            Expr_::KeyValCollection(box ((_, kvc_kind), _, _)) => match kvc_kind {
                KvcKind::Dict => None,
                _ => Some(pos.clone()),
            },
            Expr_::Call(box CallExpr {
                func: Expr(_, _, call_expr_),
                ..
            }) => match call_expr_ {
                Expr_::Id(box id)
                    if id.name() == sn::std_lib_functions::ARRAY_MARK_LEGACY
                        || id.name() == sn::pseudo_functions::UNSAFE_CAST
                        || id.name() == sn::pseudo_functions::UNSAFE_NONNULL_CAST =>
                {
                    None
                }
                _ => Some(pos.clone()),
            },
            Expr_::Omitted => {
                if matches!(self.mode, file_info::Mode::Mhhi) {
                    None
                } else {
                    Some(pos.clone())
                }
            }

            // -- always invalid -------------------------------------------
            Expr_::This
            | Expr_::Lvar(..)
            | Expr_::Lplaceholder(..)
            | Expr_::ArrayGet(..)
            | Expr_::Await(..)
            | Expr_::Delay(..)
            | Expr_::Cast(..)
            | Expr_::ClassGet(..)
            | Expr_::Clone(..)
            | Expr_::Dollardollar(..)
            | Expr_::ETSplice(..)
            | Expr_::Efun(..)
            | Expr_::EnumClassLabel(..)
            | Expr_::ExpressionTree(..)
            | Expr_::Is(..)
            | Expr_::Lfun(..)
            | Expr_::List(..)
            | Expr_::MethodCaller(..)
            | Expr_::New(..)
            | Expr_::ObjGet(..)
            | Expr_::Pair(..)
            | Expr_::Pipe(..)
            | Expr_::ReadonlyExpr(..)
            | Expr_::String2(..)
            | Expr_::Yield(..)
            | Expr_::Xml(..)
            | Expr_::DestructureShape(..)
            | Expr_::DestructureTuple(..) => Some(pos.clone()),

            // -- unexpected expressions -----------------------------------
            // OCaml raises `UnexpectedExpr` here: `Import` and `Collection`
            // are elaborated away (or replaced by the invalid expression
            // marker, which stops the traversal) by passes that run first.
            Expr_::Import(..) | Expr_::Collection(..) => None,
        };
        match illegal_at {
            None => Continue(()),
            Some(pos) => illegal(env, pos, elem),
        }
    }

    // Handle non-constant expressions which require pattern matching on some
    // element of the expression which is not yet transformed in the top-down pass
    fn on_ty_expr_bottom_up(&mut self, env: &Env, elem: &mut Expr) -> ControlFlow<()> {
        if !self.enforce_const_expr() {
            return Continue(());
        }
        let Expr(_, pos, expr_) = elem;
        let is_illegal = match expr_ {
            // We have to handle this case bottom-up since the class identifier
            // will not have been rewritten in the top-down pass
            Expr_::Nameof(box ClassId(_, _, class_id_))
            | Expr_::ClassConst(box (ClassId(_, _, class_id_), _)) => match class_id_ {
                ClassId_::CIstatic => true,
                ClassId_::CIparent
                | ClassId_::CIself
                | ClassId_::CI(..)
                | ClassId_::CIreified(..) => false,
                // NB this relies on `class_id` elaboration having been applied, if
                // it hasn't we would still have `CIstatic` represented as
                // `CIexpr (_,_,Id(_,'static'))`
                ClassId_::CIexpr(Expr(_, _, ci_expr_)) => {
                    !matches!(ci_expr_, Expr_::This | Expr_::Id(..))
                }
            },
            _ => false,
        };
        if is_illegal {
            let pos = pos.clone();
            illegal(env, pos, elem)
        } else {
            Continue(())
        }
    }

    fn on_ty_class__top_down(&mut self, _: &Env, elem: &mut Class_) -> ControlFlow<()> {
        self.set_in_enum_class(match elem.kind {
            ClassishKind::CenumClass(_) => true,
            ClassishKind::Cclass(..)
            | ClassishKind::Cinterface
            | ClassishKind::Cenum
            | ClassishKind::Ctrait => false,
        });
        self.mode = elem.mode;
        Continue(())
    }

    fn on_ty_class_const_kind_top_down(
        &mut self,
        _: &Env,
        elem: &mut ClassConstKind,
    ) -> ControlFlow<()> {
        self.set_enforce_const_expr(
            !self.in_enum_class() && matches!(elem, ClassConstKind::CCConcrete(_)),
        );
        Continue(())
    }

    fn on_ty_typedef_top_down(&mut self, _: &Env, elem: &mut Typedef) -> ControlFlow<()> {
        self.mode = elem.mode;
        Continue(())
    }

    fn on_ty_gconst_top_down(&mut self, _: &Env, elem: &mut Gconst) -> ControlFlow<()> {
        self.mode = elem.mode;
        self.set_enforce_const_expr(true);
        Continue(())
    }

    fn on_ty_fun_def_top_down(&mut self, _: &Env, elem: &mut FunDef) -> ControlFlow<()> {
        self.mode = elem.mode;
        Continue(())
    }

    fn on_ty_module_def_top_down(&mut self, _: &Env, elem: &mut ModuleDef) -> ControlFlow<()> {
        self.mode = elem.mode;
        Continue(())
    }
}
