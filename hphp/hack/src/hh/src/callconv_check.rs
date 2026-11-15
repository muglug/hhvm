// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/callconv_check.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::message::Message;

use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs::get_reason;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_reason;

pub fn check_types(env: &tast_env::Env, e: &tast::Expr) {
    let aast::Expr(_, p, te) = e;
    fn check_types_helper(env: &tast_env::Env, p: &oxidized::pos::Pos, te: &tast::Expr_) {
        match te {
            aast::Expr_::Lvar(_) => {}
            aast::Expr_::ArrayGet(ag) if ag.1.is_some() => {
                let aast::Expr(ty1, _, te1) = &ag.0;
                fn iter(env: &tast_env::Env, ty1: &Ty) -> bool {
                    let ety1 = tast_env::expand_type(&mut env.clone(), ty1.clone());
                    match get_node(&ety1) {
                        Ty_::Tany(_) => true,
                        Ty_::TvecOrDict(_, _)
                        | Ty_::Ttuple(_)
                        | Ty_::Tshape(_)
                        | Ty_::Tdynamic(_) => true,
                        Ty_::Tclass((_, cn), _, _)
                            if cn == sn::collections::DICT
                                || cn == sn::collections::KEYSET
                                || cn == sn::collections::VEC =>
                        {
                            true
                        }
                        Ty_::Tunion(tyl) => tyl.iter().all(|ty| iter(env, ty)),
                        Ty_::Tintersection(tyl) => tyl.iter().any(|ty| iter(env, ty)),
                        Ty_::Tgeneric(_) | Ty_::Tnewtype(_, _, _) | Ty_::Tdependent(_, _) => {
                            let tyl = tast_env::get_concrete_supertypes(
                                None,
                                true,
                                &mut env.clone(),
                                ety1.clone(),
                            );
                            tyl.iter().any(|ty| iter(env, ty))
                        }
                        _ => false,
                    }
                }
                if iter(env, ty1) {
                    check_types_helper(env, p, te1)
                } else {
                    // `lazy (Env.print_error_ty env ty1)`, mapped to the
                    // reasons: computed when the error is reported.
                    let lazy_env = env.clone();
                    let ty1 = ty1.clone();
                    let reasons = typing_error::Lazy::new(move || {
                        let ty_str = tast_env::print_error_ty(None, &lazy_env, &ty1);
                        typing_reason::to_string(&format!("This is {}", ty_str), get_reason(&ty1))
                            .into_iter()
                            .map(|(pos, msg)| Message(pos, msg.into()))
                            .collect()
                    });
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(typing_error::primary::T::InoutArgumentBadType {
                            pos: p.clone(),
                            reasons,
                        }),
                        env,
                    )
                }
            }
            // Other invalid expressions are caught in Nast_check.
            _ => {}
        }
    }
    check_types_helper(env, p, te)
}

/// The object `handler`.
struct CallconvCheck;

impl<'a> tast_visitor::Handler<'a> for CallconvCheck {
    fn at_expr(&mut self, env: &tast_env::Env, e: &tast::Expr) {
        match &e.2 {
            aast::Expr_::Call(call) => {
                for arg in &call.args {
                    match arg {
                        aast::Argument::Anormal(_) => {}
                        aast::Argument::Anamed(_, _) => {}
                        aast::Argument::Ainout(_, e) => check_types(env, e),
                    }
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(CallconvCheck)
}
