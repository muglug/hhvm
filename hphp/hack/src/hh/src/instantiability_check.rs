// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/instantiability_check.ml`. See `hh/PORTING.md`.
//!
//! This TAST check raises an error when an abstract final
//! class or a trait appears outside of classname<_>.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast::ClassPtrKind;
use oxidized::aast::CtxRefinement;
use oxidized::aast::CtxRefinementBounds;
use oxidized::aast::Expr;
use oxidized::aast::Expr_;
use oxidized::aast::Hint;
use oxidized::aast::Hint_;
use oxidized::aast::NastShapeInfo;
use oxidized::aast::Refinement;
use oxidized::aast::ShapeElement;
use oxidized::aast::TupleExtra;
use oxidized::aast::TupleExtraInfo;
use oxidized::aast::TupleInfo;
use oxidized::aast::TypeRefinement;
use oxidized::aast::TypeRefinementBounds;
use oxidized::aast::TypedefAssignment;
use oxidized::aast::TypedefVisibilityAndHint;
use oxidized::aast::WhereConstraintHint;
use oxidized::ast_defs::Id;

use crate::ast_defs;
use crate::decl_entry;
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_env::ClassOrTypedefResult;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_error;
use crate::typing_error::primary::T as Primary;
use crate::typing_error_utils;

fn validate_classname(env: &Env, Hint(pos, hint): &Hint) {
    match &**hint {
        Hint_::Happly(..)
        | Hint_::Hthis
        | Hint_::Hmixed
        | Hint_::Hwildcard
        | Hint_::Hnonnull
        | Hint_::Habstr(..)
        | Hint_::Haccess(..)
        | Hint_::Hdynamic
        | Hint_::Hsoft(..)
        | Hint_::Hlike(..)
        | Hint_::Hnothing => {}
        Hint_::Hrefinement(h, _) => validate_classname(env, h),
        Hint_::HclassPtr(..) // TODO: future Hclass will be valid
        | Hint_::Htuple(..)
        | Hint_::Hunion(..)
        | Hint_::Hintersection(..)
        | Hint_::HvecOrDict(..)
        | Hint_::Hprim(..)
        | Hint_::Hoption(..)
        | Hint_::Hfun(..)
        | Hint_::Hshape(..)
        | Hint_::HfunContext(..)
        | Hint_::Hvar(..) => typing_error_utils::add_typing_error(
            &typing_error::primary(Primary::InvalidClassname(pos.clone())),
            env,
        ),
    }
}

fn check_hint(env: &Env, Hint(pos, hint): &Hint) {
    match &**hint {
        Hint_::Happly(Id(_, class_id), tal) => {
            match tast_env::get_class_or_typedef(env, class_id) {
                decl_entry::T::Found(ClassOrTypedefResult::ClassResult(cls))
                    if {
                        let kind = cls::kind(&cls);
                        let tc_name = cls::name(&cls);
                        (ast_defs::is_c_trait(kind)
                            || (ast_defs::is_c_abstract(kind) && cls::final_(&cls)))
                            && tc_name != sn::collections::DICT
                            && tc_name != sn::collections::KEYSET
                            && tc_name != sn::collections::VEC
                    } =>
                {
                    let tc_pos = cls::pos(&cls);
                    let tc_name = cls::name(&cls);
                    let err = typing_error::primary(Primary::UninstantiableClass {
                        pos: pos.clone(),
                        class_name: tc_name,
                        decl_pos: tc_pos,
                        reason_ty_opt: None,
                    });
                    typing_error_utils::add_typing_error(&err, env)
                }
                _ => {}
            }
            if class_id == sn::classes::CLASS_NAME {
                if let Some(h) = tal.first() {
                    validate_classname(env, h)
                }
            } else {
                tal.iter().for_each(|h| check_hint(env, h))
            }
        }
        Hint_::Hrefinement(h, members) => {
            let check_bounds = |(lower, upper): (&[Hint], &[Hint])| {
                lower.iter().for_each(|h| check_hint(env, h));
                upper.iter().for_each(|h| check_hint(env, h));
            };
            let check_member = |member: &Refinement| match member {
                Refinement::Rtype(_, ref_) => match ref_ {
                    TypeRefinement::TRexact(h) => check_hint(env, h),
                    TypeRefinement::TRloose(TypeRefinementBounds { lower, upper }) => {
                        check_bounds((lower, upper))
                    }
                },
                Refinement::Rctx(_, ref_) => match ref_ {
                    CtxRefinement::CRexact(h) => check_hint(env, h),
                    CtxRefinement::CRloose(CtxRefinementBounds { lower, upper }) => {
                        check_bounds((lower.as_slice(), upper.as_slice()))
                    }
                },
            };
            members.iter().for_each(check_member);
            check_hint(env, h)
        }
        Hint_::Hshape(hm) => check_shape(env, hm),
        Hint_::Haccess(h, ids) => check_access(env, h, ids),
        Hint_::HvecOrDict(hopt1, h2) => {
            if let Some(h) = hopt1 {
                check_hint(env, h)
            }
            check_hint(env, h2)
        }
        Hint_::HclassPtr(ClassPtrKind::CKenum, h) => {
            // similar to Happly case for enumname
            check_hint(env, h)
        }
        Hint_::HclassPtr(ClassPtrKind::CKclass, h) => validate_classname(env, h),
        Hint_::Hoption(h) | Hint_::Hlike(h) | Hint_::Hsoft(h) => check_hint(env, h),
        Hint_::Habstr(..)
        | Hint_::Hprim(..)
        | Hint_::Hdynamic
        | Hint_::Hnonnull
        | Hint_::Hmixed
        | Hint_::Hwildcard
        | Hint_::Hthis
        | Hint_::Hnothing
        | Hint_::HfunContext(..)
        | Hint_::Hvar(..) => {}
        Hint_::Hfun(aast::HintFun {
            is_readonly: _,
            tparams: hf_tparams,
            param_tys: hl,
            param_info: _,
            // TODO: shouldn't we be checking this hint as well?
            variadic_ty: _,
            named_variadic_ty: _,
            ctxs: _,
            return_ty: h,
            is_readonly_return: _,
        }) => {
            hl.iter().for_each(|h| check_hint(env, h));
            check_hint(env, h);
            hf_tparams
                .iter()
                .for_each(|aast::HintTparam { constraints, .. }| {
                    constraints.iter().for_each(|(_, h)| check_hint(env, h))
                })
        }
        Hint_::Hunion(hl) | Hint_::Hintersection(hl) => hl.iter().for_each(|h| check_hint(env, h)),
        Hint_::Htuple(TupleInfo { required, extra }) => {
            required.iter().for_each(|h| check_hint(env, h));
            match extra {
                TupleExtra::Hextra(TupleExtraInfo { optional, variadic }) => {
                    optional.iter().for_each(|h| check_hint(env, h));
                    if let Some(h) = variadic {
                        check_hint(env, h)
                    }
                }
                TupleExtra::Hsplat(h) => check_hint(env, h),
            }
        }
    }
}

fn check_shape(
    env: &Env,
    NastShapeInfo {
        allows_unknown_fields: _,
        field_map,
        unknown_fields_type,
    }: &NastShapeInfo,
) {
    // Check instantiability of both field hints and the operand of each splat,
    // so a splat of a non-instantiable type (abstract-final class, trait) is
    // still reported. A splat of a bare type parameter is a no-op here.
    field_map.iter().for_each(|e| match e {
        ShapeElement::SEField(sfi) => check_hint(env, &sfi.hint),
        ShapeElement::SESplat(h) => check_hint(env, h),
    });
    if let Some(h) = unknown_fields_type {
        check_hint(env, h)
    }
}

/// Need to skip the root of the Haccess element
fn check_access(env: &Env, h: &Hint, _: &[aast::Sid]) {
    match &*h.1 {
        Hint_::Happly(_, hl) => hl.iter().for_each(|h| check_hint(env, h)),
        _ => check_hint(env, h),
    }
}

fn check_tparams(env: &Env, tparams: &[tast::Tparam]) {
    tparams
        .iter()
        .for_each(|t| t.constraints.iter().for_each(|(_ck, h)| check_hint(env, h)))
}

fn check_param(env: &Env, param: &tast::FunParam) {
    // `hint_of_type_hint param.param_type_hint`
    if let Some(h) = &param.type_hint.1 {
        check_hint(env, h)
    }
}

/// `handler`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_typedef(&mut self, env: &Env, t: &'a tast::Typedef) {
        let hints: Vec<&Hint> = match &t.assignment {
            TypedefAssignment::SimpleTypeDef(TypedefVisibilityAndHint { vis: _, hint }) => {
                vec![hint]
            }
            TypedefAssignment::CaseType(variant, variants) => std::iter::once(variant)
                .chain(variants.iter())
                .flat_map(|v| {
                    std::iter::once(&v.hint).chain(
                        v.where_constraints
                            .iter()
                            .flat_map(|WhereConstraintHint(h1, _ck, h2)| [h1, h2]),
                    )
                })
                .collect(),
        };
        hints.into_iter().for_each(|h| check_hint(env, h));
        if let Some(h) = &t.as_constraint {
            check_hint(env, h)
        }
        if let Some(h) = &t.super_constraint {
            check_hint(env, h)
        }
    }

    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        let check_class_vars = |cvar: &tast::ClassVar| {
            // `hint_of_type_hint cvar.cv_type`
            if let Some(h) = &cvar.type_.1 {
                check_hint(env, h)
            }
        };
        c.vars.iter().for_each(check_class_vars);
        check_tparams(env, &c.tparams)
    }

    fn at_fun_def(&mut self, env: &Env, fd: &'a tast::FunDef) {
        check_tparams(env, &fd.tparams)
    }

    fn at_fun_(&mut self, env: &Env, f: &'a tast::Fun_) {
        f.params.iter().for_each(|p| check_param(env, p));
        // `hint_of_type_hint f.f_ret`
        if let Some(h) = &f.ret.1 {
            check_hint(env, h)
        }
    }

    fn at_method_(&mut self, env: &Env, m: &'a tast::Method_) {
        check_tparams(env, &m.tparams);
        m.params.iter().for_each(|p| check_param(env, p));
        // `hint_of_type_hint m.m_ret`
        if let Some(h) = &m.ret.1 {
            check_hint(env, h)
        }
    }

    fn at_hint(&mut self, env: &Env, Hint(_, h): &'a Hint) {
        match &**h {
            Hint_::Hshape(hm) => check_shape(env, hm),
            _ => {}
        }
    }

    fn at_gconst(&mut self, env: &Env, cst: &'a tast::Gconst) {
        if let Some(h) = &cst.type_ {
            check_hint(env, h)
        }
    }

    fn at_expr(&mut self, env: &Env, Expr(_, _, e): &'a tast::Expr) {
        match e {
            Expr_::Is(is) => check_hint(env, &is.1),
            Expr_::As(as_) => check_hint(env, &as_.hint),
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
