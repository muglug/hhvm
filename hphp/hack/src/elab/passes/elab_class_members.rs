// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Class_;
use nast::ClassVar;
use nast::ClassishKind;
use nast::Expr;
use nast::Expr_;
use nast::Hint;
use nast::Hint_;
use nast::Id;
use nast::Pos;
use nast::Tprim;
use nast::TypeHint;
use nast::UserAttribute;
use nast::UserAttributes;
use nast::XhpAttr;
use nast::XhpAttrInfo;

use crate::prelude::*;

/// Port of `Naming_elab_class_members`: elaborate class members and xhp
/// attributes.
#[derive(Copy, Clone, Default)]
pub struct ElabClassMembersPass;

impl Pass for ElabClassMembersPass {
    fn on_ty_class__bottom_up(&mut self, env: &Env, elem: &mut Class_) -> ControlFlow<()> {
        let const_attr_opt: Option<UserAttribute> = elem
            .user_attributes
            .iter()
            .find(|ua| ua.name.1 == sn::user_attributes::CONST)
            .cloned();

        // `static_props @ props @ xhp_attrs`
        let (mut static_props, mut props): (Vec<ClassVar>, Vec<ClassVar>) =
            std::mem::take(&mut elem.vars)
                .into_iter()
                .partition(|cv| cv.is_static);
        static_props.iter_mut().for_each(elab_class_prop);
        props
            .iter_mut()
            .for_each(|cv| elab_non_static_class_prop(const_attr_opt.as_ref(), cv));
        let xhp_attrs: Vec<ClassVar> = std::mem::take(&mut elem.xhp_attrs)
            .into_iter()
            .map(|xhp_attr| elab_xhp_attr(env, xhp_attr))
            .collect();

        let mut vars = static_props;
        vars.append(&mut props);
        vars.extend(xhp_attrs);
        elem.vars = vars;

        // If this is an interface mark all methods as abstract
        if matches!(elem.kind, ClassishKind::Cinterface) {
            elem.methods.iter_mut().for_each(|m| m.abstract_ = true)
        }

        Continue(())
    }
}

// TODO[mjt] is there no other way of determining this?
fn is_xhp(cv_name: &str) -> bool {
    cv_name.starts_with(':')
}

fn elab_class_prop(cv: &mut ClassVar) {
    cv.xhp_attr = if is_xhp(&cv.id.1) {
        Some(XhpAttrInfo {
            like: None,
            tag: None,
            enum_values: vec![],
        })
    } else {
        None
    };
}

fn elab_non_static_class_prop(const_attr_opt: Option<&UserAttribute>, cv: &mut ClassVar) {
    elab_class_prop(cv);
    if let Some(ua) = const_attr_opt {
        if !cv
            .user_attributes
            .iter()
            .any(|ua| ua.name.1 == sn::user_attributes::CONST)
        {
            cv.user_attributes.0.insert(0, ua.clone())
        }
    }
}

fn exists_both<T>(p1: impl Fn(&T) -> bool, p2: impl Fn(&T) -> bool, xs: &[T]) -> (bool, bool) {
    let (mut b1, mut b2) = (false, false);
    for x in xs {
        if b1 && b2 {
            break;
        }
        b1 = b1 || p1(x);
        b2 = b2 || p2(x);
    }
    (b1, b2)
}

fn xhp_attr_hint(pos: &Pos, items: &[Expr]) -> Hint_ {
    let is_int = |e: &Expr| matches!(e.2, Expr_::Int(_));
    let is_string = |e: &Expr| matches!(e.2, Expr_::String(_) | Expr_::String2(_));
    match exists_both(is_int, is_string, items) {
        (true, false) => Hint_::Hprim(Tprim::Tint),
        (_, true) => Hint_::Happly(
            Id(pos.clone(), sn::typehints::HH_STRING.to_string()),
            vec![],
        ),
        _ => Hint_::Hmixed,
    }
}

// If we have a like `Hint_` return a reference to the inner `Hint_` otherwise
// return the reference to the outer hint
fn strip_like(hint_: &Hint_) -> &Hint_ {
    if let Hint_::Hlike(Hint(_, inner_hint_)) = hint_ {
        inner_hint_
    } else {
        hint_
    }
}

// Convert an `XhpAttr` into a `ClassVar`
fn elab_xhp_attr(env: &Env, xhp_attr: XhpAttr) -> ClassVar {
    let XhpAttr(type_hint, mut cv, xhp_attr_tag_opt, enum_opt) = xhp_attr;
    let is_required = xhp_attr_tag_opt.is_some();
    let has_default = match &cv.expr {
        Some(Expr(_, _, Expr_::Null)) | None => false,
        Some(_) => true,
    };
    let (xai_like, xai_enum_values) = match cv.xhp_attr.take() {
        Some(xai) => (xai.like, xai.enum_values),
        None => (None, vec![]),
    };
    let TypeHint(type_hint_annot, type_hint_hint_opt) = type_hint;
    // If we have `enum_opt`, a list of expressions, build a hint based on the
    // occurrence of expression literals. If we don't, use the (optional) hint
    // within `type_hint`
    let hint_opt: Option<Hint> = match enum_opt {
        Some((pos, items)) => {
            let hint_ = xhp_attr_hint(&pos, &items);
            Some(Hint(pos, Box::new(hint_)))
        }
        None => type_hint_hint_opt,
    };
    let hint_opt = hint_opt.map(|hint| match strip_like(&hint.1) {
        Hint_::Hoption(_) => {
            if is_required {
                env.emit_error(NamingError::XhpOptionalRequiredAttr {
                    pos: hint.0.clone(),
                    attr_name: cv.id.1.clone(),
                })
            }
            hint
        }
        Hint_::Hmixed => hint,
        _ if is_required || has_default => hint,
        _ => Hint(hint.0.clone(), Box::new(Hint_::Hoption(hint))),
    });
    let hint_opt = match (hint_opt, &xai_like) {
        (Some(hint), Some(pos)) => Some(Hint(pos.clone(), Box::new(Hint_::Hlike(hint)))),
        (hint_opt, _) => hint_opt,
    };
    cv.type_ = TypeHint(type_hint_annot, hint_opt);
    cv.xhp_attr = Some(XhpAttrInfo {
        like: xai_like,
        tag: xhp_attr_tag_opt,
        enum_values: xai_enum_values,
    });
    cv.user_attributes = UserAttributes(vec![]);
    cv
}
