// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/string_cast_check.ml`. See `hh/PORTING.md`.
//!
//! Produce an error on (string) casts of objects. Currently it is allowed in
//! HHVM to cast an object if it is Stringish (i.e., has a __toString()
//! method), but all (string) casts of objects will be banned in the future.
//! Eventually, __toString/(string) casts of objects will be removed from HHVM
//! entirely.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Id;
use oxidized::ast_defs::Visibility;
use oxidized::nast_check_error::NastCheckError;
use oxidized::naming_phase_error::NamingPhaseError;

use crate::decl_entry;
use crate::naming_special_names::classes::C_STRING;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;

/// `Diagnostics.add_diagnostic (Nast_check_error.to_user_diagnostic err)`
fn add_nast_check_error(err: NastCheckError) {
    let diagnostic = crate::naming_phase_error::to_user_diagnostic(NamingPhaseError::NastCheck(err));
    crate::diagnostics::add_diagnostic(diagnostic);
}

/// `Happly ((_, id), _)` with `id` being `SN.Classes.cString`.
fn is_happly_string(h: &aast::Hint_) -> bool {
    matches!(h, aast::Hint_::Happly(Id(_, id), _) if C_STRING == id)
}

pub fn check_to_string(m: &tast::Method_) {
    let Id(pos, name) = &m.name;
    if name == sn::members::__TO_STRING {
        if !crate::aast_defs::equal_visibility(m.visibility, Visibility::Public) || m.static_ {
            add_nast_check_error(NastCheckError::ToStringVisibility(pos.clone()));
        }
        match crate::aast::hint_of_type_hint(&m.ret) {
            Some(aast::Hint(_, h))
                if is_happly_string(h)
                    || matches!(&**h, aast::Hint_::Hlike(aast::Hint(_, h)) if is_happly_string(h)) => {}
            Some(aast::Hint(p, _)) => {
                add_nast_check_error(NastCheckError::ToStringReturnsString(p.clone()))
            }
            None => {}
        }
    }
}

pub fn is_stringish(env: &Env, ty: &Ty) -> bool {
    let mut env = env.clone();
    let ety = tast_env::expand_type(&mut env, ty.clone());
    match get_node(&ety) {
        Ty_::Toption(ty_) => is_stringish(&env, ty_),
        Ty_::Tunion(tyl) => tyl.iter().all(|ty| is_stringish(&env, ty)),
        Ty_::Tintersection(tyl) => tyl.iter().any(|ty| is_stringish(&env, ty)),
        Ty_::Tgeneric(_) | Ty_::Tnewtype(..) | Ty_::Tdependent(..) => {
            let tyl = tast_env::get_concrete_supertypes(None, true, &mut env, ty.clone());
            tyl.iter().all(|ty| is_stringish(&env, ty))
        }
        Ty_::Tclass((_, id), _, _) if C_STRING == id => true,
        Ty_::Tclass(x, _, _) => decl_entry::to_option(tast_env::get_class(&env, &x.1)).is_none(),
        // TODO akenn: error tyvar?
        Ty_::Tany(_) | Ty_::Tdynamic(_) | Ty_::Tnonnull | Ty_::Tprim(_) | Ty_::Tneg(_) => true,
        Ty_::TvecOrDict(..)
        | Ty_::Tvar(_)
        | Ty_::Ttuple(_)
        | Ty_::Tfun(_)
        | Ty_::Tshape(_)
        | Ty_::Tlabel(_)
        | Ty_::Taccess(_) => false,
        Ty_::TclassPtr(_) => tast_env::get_tcopt(&env).allow_class_string_cast,
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        let aast::Expr(_, p, expr) = e;
        match expr {
            aast::Expr_::Cast(cast)
                if matches!(&cast.0, aast::Hint(_, h) if matches!(&**h, aast::Hint_::Happly(Id(_, id), _) if C_STRING == id)) =>
            {
                let (_, te) = &**cast;
                let aast::Expr(ty, _, _) = te;
                if !is_stringish(env, ty) {
                    let ty_name = {
                        let env = env.clone();
                        let ty = ty.clone();
                        typing_error::Lazy::new(move || tast_env::print_ty(&env, &ty))
                    };
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::StringCast {
                            pos: p.clone(),
                            ty_name,
                        }),
                        env,
                    )
                }
            }
            _ => {}
        }
    }

    fn at_method_(&mut self, _env: &Env, m: &'a tast::Method_) {
        check_to_string(m)
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
