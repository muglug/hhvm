// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/invalid_index_check.ml`. See `hh/PORTING.md`.
//!
//! `index_visitor` inherits `Tast_visitor.iter_with_state` with the state
//! `is_lvalue`: its context is `(env, is_lvalue)`.

use bstr::BString;
use naming_special_names_rust as sn;
use oxidized::aast::Expr;
use oxidized::aast::Expr_;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_env::can_subtype;
use crate::tast_visitor;
use crate::typing_coercion;
use crate::typing_defs::Enforcement;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs::get_reason;
use crate::typing_error;
use crate::typing_error::primary::T as Primary;
use crate::typing_error_utils;
use crate::typing_make_type as make_type;
use crate::typing_reason as reason;
use crate::typing_reason::Ureason;

fn equiv_ak_inter_dyn(env: &Env, ty_expect: &Ty) -> bool {
    let r = get_reason(ty_expect);
    let ak_dyn = make_type::intersection(
        r.clone(),
        vec![
            make_type::arraykey(r.clone()),
            make_type::dynamic(r.clone()),
        ],
    );
    can_subtype(env, ty_expect, &ak_dyn) && can_subtype(env, &ak_dyn, ty_expect)
}

/// `Typing_reason.to_string` gives `Message.t`s.
fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, BString::from(msg)))
        .collect()
}

// For new-inference, types of keys in collection types may not be resolved
// until TAST check time. For this reason, we replicate some of the checks that
// are applied in Typing_array_access.array_get here. Specifically, those
// checks that involve the key type from a dictionary-like container, checked
// against the type of the index expression. For example,
// the container might have a type dict<k,t> and the index expression might
// have a type k'. We want k' <: k.
fn array_get(
    array_pos: &Pos,
    expr_pos: &Pos,
    index_pos: &Pos,
    env: &Env,
    array_ty: &Ty,
    index_ty: &Ty,
) {
    let type_index = |is_covariant_index: Option<bool>,
                      env: &Env,
                      ty_have: &Ty,
                      ty_expect: &Ty,
                      reason: Ureason|
     -> Result<(), ()> {
        let is_covariant_index = is_covariant_index.unwrap_or(false);
        let got_error = {
            // The environment of the coercion is dropped.
            let ty_err_opt = typing_coercion::coerce_type(
                Some(true),
                None,
                None,
                index_pos.clone(),
                reason.clone(),
                &mut env.clone(),
                ty_have.clone(),
                ty_expect.clone(),
                Enforcement::Enforced,
                typing_error::callback::index_type_mismatch(),
            );
            ty_err_opt.is_some()
        };
        if !got_error {
            Ok(())
        } else if (can_subtype(env, ty_have, &make_type::dynamic(get_reason(ty_have).clone()))
            // Terrible heuristic to agree with legacy: if we inferred `nothing` for
            // the key type of the array, just let it pass
            || can_subtype(env, ty_expect, &make_type::nothing(get_reason(ty_expect).clone())))
            // If the key is not even an arraykey, we've already produced an error
            || (!can_subtype(env, ty_have, &make_type::arraykey(reason::none())))
            // Keytype of arraykey&dynamic happens when you assign a dynamic into a dict,
            // but the above coercion doesn't work.
            || equiv_ak_inter_dyn(env, ty_expect)
        {
            Ok(())
        } else {
            let reasons_opt = Some({
                let env = env.clone();
                let ty_have = ty_have.clone();
                let ty_expect = ty_expect.clone();
                typing_error::Lazy::new(move || {
                    // The environments are dropped.
                    let ty_have = tast_env::expand_type(&mut env.clone(), ty_have);
                    let ty_expect = tast_env::expand_type(&mut env.clone(), ty_expect);
                    let ty_expect_str = tast_env::print_error_ty(None, &env, &ty_expect);
                    let ty_have_str = tast_env::print_error_ty(None, &env, &ty_have);
                    // The arguments of `@` are evaluated right to left, as in OCaml.
                    let second = reason::to_string(
                        &format!("It is incompatible with {}", ty_have_str),
                        get_reason(&ty_have),
                    );
                    let first = reason::to_string(
                        &format!("This is {}", ty_expect_str),
                        get_reason(&ty_expect),
                    );
                    messages(first.into_iter().chain(second).collect())
                })
            });
            typing_error_utils::add_typing_error(
                &typing_error::primary(Primary::IndexTypeMismatch {
                    pos: index_pos.clone(),
                    msg_opt: Some(reason::string_of_ureason(&reason)),
                    reasons_opt,
                    is_covariant_container: is_covariant_index,
                }),
                env,
            );
            Err(())
        }
    };
    // The environment is dropped. (`expand_type` gives back any type but a
    // type variable as it is: those are matched without a copy.)
    let expanded;
    let ety = match get_node(array_ty) {
        Ty_::Tvar(_) => {
            expanded = tast_env::expand_type(&mut env.clone(), array_ty.clone());
            &expanded
        }
        _ => array_ty,
    };
    match get_node(ety) {
        Ty_::Tunion(tyl) => tyl
            .iter()
            .for_each(|ty| array_get(array_pos, expr_pos, index_pos, env, ty, index_ty)),
        Ty_::Tclass((pos, cn), _, _) if cn == sn::collections::VEC => {
            let _: Result<(), ()> = type_index(
                Some(true),
                env,
                index_ty,
                &make_type::int(reason::idx_vector_from_decl(pos.clone())),
                reason::index_class(cn),
            );
        }
        Ty_::Tclass((_, cn), _, tyl)
            if !tyl.is_empty()
                && (cn == sn::collections::DICT || cn == sn::collections::KEYSET) =>
        {
            let key_ty = &tyl[0];
            // dict and keyset are both covariant in their key types so it is only
            // required that the index be a subtype of the upper bound on that param, i.e., arraykey
            // Here, we first check that we do not have a type error; if we do not, we
            // then check that the indexing expression is a subtype of the key type and
            // raise a distinct error.
            // This allows us to retain the older behavior (which raised an index_type_mismatch error)
            // whilst allowing us to discern between it and errors which can be
            // addressed with `UNSAFE_CAST`
            let arraykey_ty = make_type::arraykey(reason::idx_dict(array_pos.clone()));
            let array_key_res =
                type_index(None, env, index_ty, &arraykey_ty, reason::index_class(cn));
            match array_key_res {
                Err(_) => {
                    // We have raised the more general error
                }
                Ok(_) => {
                    // The index expression _is_ a subtype of arraykey, now check it is a subtype
                    // of the given key_ty
                    let _: Result<(), ()> =
                        type_index(Some(true), env, index_ty, key_ty, reason::index_class(cn));
                }
            }
        }
        Ty_::Tclass((_, cn), _, tyl)
            if !tyl.is_empty()
                && (cn == sn::collections::MAP
                    || cn == sn::collections::CONST_MAP
                    || cn == sn::collections::IMM_MAP
                    || cn == sn::collections::KEYED_CONTAINER
                    || cn == sn::collections::ANY_ARRAY) =>
        {
            let key_ty = &tyl[0];
            let _: Result<(), ()> =
                type_index(None, env, index_ty, key_ty, reason::index_class(cn));
        }
        Ty_::Toption(array_ty) => {
            array_get(array_pos, expr_pos, index_pos, env, array_ty, index_ty)
        }
        Ty_::Tnonnull
        | Ty_::Tprim(_)
        | Ty_::Tfun(_)
        | Ty_::Tvar(_)
        | Ty_::Tclass(..)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::Tdynamic(_)
        | Ty_::Tany(_)
        | Ty_::Tnewtype(..)
        | Ty_::Tdependent(..)
        | _ => {}
    }
}

/// `(env, is_lvalue)`
type Context = (Env, bool);

/// Run `visit` with `is_lvalue` set to `is_lvalue` (`this#on_expr (env,
/// is_lvalue) e`), then restore it.
fn with_is_lvalue(
    c: &mut Context,
    is_lvalue: bool,
    visit: impl FnOnce(&mut Context) -> Result<(), ()>,
) -> Result<(), ()> {
    let saved = std::mem::replace(&mut c.1, is_lvalue);
    let result = visit(c);
    c.1 = saved;
    result
}

/// `index_visitor`
struct IndexVisitor;

fn index_visitor() -> IndexVisitor {
    IndexVisitor
}

impl<'a> tast_visitor::IterWithState<'a, bool> for IndexVisitor {}

impl<'a> Visitor<'a> for IndexVisitor {
    type Params = tast_visitor::StateParams<bool>;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    crate::tast_visitor::iter_with_state_methods!('a);

    // Distinguish between lvalue and rvalue array indexing.
    // Suppose $x : dict<string,int>
    // We want to check rvalue e.g. $y = $x[3], or $z[$x[3]] = 5
    // But not lvalue e.g. $x[3] = 5 or list ($x[3], $w) = e;
    fn visit_expr(&mut self, c: &mut Context, e: &'a tast::Expr) -> Result<(), ()> {
        let Expr(_, p, expr) = e;
        match expr {
            Expr_::ArrayGet(ag) if ag.1.is_some() => {
                let (e1, e2) = &**ag;
                let e2 = e2.as_ref().unwrap();
                let Expr(ty1, p1, _) = e1;
                let Expr(ty2, p2, _) = e2;
                let is_lvalue = c.1;
                if !is_lvalue {
                    array_get(p1, p, p2, &c.0, ty1, ty2);
                }
                with_is_lvalue(c, false, |c| self.visit_expr(c, e1))?;
                with_is_lvalue(c, false, |c| self.visit_expr(c, e2))
            }
            Expr_::Assign(a) => {
                let (lhs, _, rhs) = &**a;
                with_is_lvalue(c, true, |c| self.visit_expr(c, lhs))?;
                with_is_lvalue(c, false, |c| self.visit_expr(c, rhs))
            }
            Expr_::List(el) => {
                for e in el {
                    self.visit_expr(c, e)?;
                }
                Ok(())
            }
            // `super#on_expr`
            _ => e.recurse(c, self),
        }
    }
}

/// `handler`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_fun_def(&mut self, env: &Env, fd: &'a tast::FunDef) {
        let _ = index_visitor().visit_fun_def(&mut (env.clone(), false), fd);
    }

    fn at_method_(&mut self, env: &Env, m: &'a tast::Method_) {
        let _ = index_visitor().visit_method_(&mut (env.clone(), false), m);
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
