// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/reified_check.ml`. See `hh/PORTING.md`.
//!
//! `is_reified`, `tparams_has_reified`, `verify_targ_valid` and
//! `verify_call_targs` are polymorphic in OCaml: they are given the type
//! parameters of localized function types (`locl_ty tparam`) and of class
//! declarations (`decl_ty tparam`). Here these are two types
//! (`typing_defs::Tparam` and `ty::decl::Tparam`), so these functions take
//! any [`TparamFields`]. `verify_targ_valid` reads only `snd targ`, which it
//! is given (the `targ` is a `Tast.targ` or a `unit * hint`).

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::ReifyKind;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::aast_defs;
use crate::ast_defs;
use crate::ctx::R;
use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::naming_special_names::stdlib_functions::GET_CLASS_FROM_TYPE;
use crate::tast;
/// `module Env = Tast_env`
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::type_validator;
use crate::type_validator::TypeValidator;
use crate::typing_defs::attributes;
use crate::typing_defs::*;
use crate::typing_enforceable_hint;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_reified_check;
use crate::typing_set;

/// `Ast_defs.is_c_normal` (which `crate::ast_defs` does not have).
fn is_c_normal(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::Cclass(c) => ast_defs::is_concrete(c),
        ClassishKind::Cenum
        | ClassishKind::CenumClass(_)
        | ClassishKind::Ctrait
        | ClassishKind::Cinterface => false,
    }
}

/// The fields of `'ty Typing_defs.tparam` that this module reads.
trait TparamFields {
    type UserAttribute: attributes::UserAttribute;

    /// `tp_reified`
    fn tp_reified(&self) -> ReifyKind;

    /// `tp_name`
    fn tp_name(&self) -> (PosOrDecl, String);

    /// `tp_user_attributes`
    fn tp_user_attributes(&self) -> &[Self::UserAttribute];
}

impl TparamFields for Tparam {
    type UserAttribute = UserAttribute;

    fn tp_reified(&self) -> ReifyKind {
        self.reified
    }

    fn tp_name(&self) -> (PosOrDecl, String) {
        self.name.clone()
    }

    fn tp_user_attributes(&self) -> &[UserAttribute] {
        &self.user_attributes
    }
}

impl TparamFields for ty::decl::Tparam<R, DeclTy> {
    type UserAttribute = ty::decl::UserAttribute<<R as ty::reason::Reason>::Pos>;

    fn tp_reified(&self) -> ReifyKind {
        self.reified
    }

    fn tp_name(&self) -> (PosOrDecl, String) {
        (
            self.name.pos().clone().to_oxidized(),
            self.name.id_ref().as_str().to_string(),
        )
    }

    fn tp_user_attributes(&self) -> &[Self::UserAttribute] {
        &self.user_attributes
    }
}

fn is_reified<TP: TparamFields>(tparam: &TP) -> bool {
    !(tparam.tp_reified() == ReifyKind::Erased)
}

fn tparams_has_reified<TP: TparamFields>(tparams: &[TP]) -> bool {
    tparams.iter().any(is_reified)
}

fn valid_newable_hint(env: &Env, (tp_pos, tp_name): (PosOrDecl, String), hint: &aast::Hint) {
    let aast::Hint(pos, hint) = hint;
    let err_opt = match &**hint {
        aast::Hint_::Happly(ast_defs::Id(p, h), _) => {
            match tast_env::get_class_or_typedef(env, h) {
                decl_entry::T::Found(tast_env::ClassOrTypedefResult::ClassResult(cls)) => {
                    if !is_c_normal(cls::kind(&cls)) {
                        Some(primary::T::InvalidNewableTypeArgument {
                            tp_pos,
                            tp_name,
                            pos: p.clone(),
                        })
                    } else {
                        None
                    }
                }
                _ => {
                    // This case should never happen
                    Some(primary::T::InvalidNewableTypeArgument {
                        tp_pos,
                        tp_name,
                        pos: p.clone(),
                    })
                }
            }
        }
        aast::Hint_::Habstr(name) => {
            if !tast_env::get_newable(env, name) {
                Some(primary::T::InvalidNewableTypeArgument {
                    tp_pos,
                    tp_name,
                    pos: pos.clone(),
                })
            } else {
                None
            }
        }
        _ => Some(primary::T::InvalidNewableTypeArgument {
            tp_pos,
            tp_name,
            pos: pos.clone(),
        }),
    };
    if let Some(err) = err_opt {
        typing_error_utils::add_typing_error(&typing_error::primary(err), env)
    }
}

fn verify_has_consistent_bound(env: &Env, tparam: &tast::Tparam) {
    let upper_bounds =
        // a newable type parameter cannot be higher-kinded/require arguments
        typing_set::elements(&tast_env::get_upper_bounds(env, &tparam.name.1));
    let bound_classes: Vec<Option<cls::T>> = upper_bounds
        .iter()
        .filter_map(|ty| match get_node(ty) {
            Ty_::Tclass((_, class_id), _, _) => match tast_env::get_class(env, class_id) {
                decl_entry::T::Found(cls) => Some(Some(cls)),
                decl_entry::T::NotYetAvailable => Some(None),
                decl_entry::T::DoesNotExist => None,
            },
            _ => None,
        })
        .collect();
    // List.fold_right bound_classes ~init:(Some []) ~f:(fun cls acc -> ...),
    // which conses: the classes are collected from the last one, then put
    // back in order.
    let valid_classes: Option<Vec<cls::T>> = bound_classes
        .into_iter()
        .rev()
        .fold(Some(vec![]), |acc, cls| {
            let mut acc = acc?;
            let cls = cls?;
            if tast_env::valid_newable_class(env, &cls) {
                acc.push(cls);
                Some(acc)
            } else {
                Some(acc)
            }
        })
        .map(|mut acc| {
            acc.reverse();
            acc
        });
    match valid_classes {
        None => {
            // A class that we queried might or might not exist. Don't emit an error.
        }
        Some(valid_classes) => {
            if 1 != valid_classes.len() {
                let constraints = valid_classes.iter().map(cls::name).collect();
                let ast_defs::Id(pos, tp_name) = &tparam.name;
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::InvalidNewableTyparamConstraints {
                        pos: pos.clone(),
                        tp_name: tp_name.clone(),
                        constraints,
                    }),
                    env,
                )
            }
        }
    }
}

/// When passing targs to a reified position, they must either be concrete types
/// or reified type parameters. This prevents the case of
///
/// class C<reify Tc> {}
/// function f<Tf>(): C<Tf> {}
///
/// where Tf does not exist at runtime.
///
/// (`targ` is `snd targ`.)
fn verify_targ_valid<TP: TparamFields>(
    env: &Env,
    reification: type_validator::Reification,
    tparam: &TP,
    targ: &aast::Hint,
) {
    // There is some subtlety here. If a type *parameter* is declared reified,
    // even if it is soft, we require that the argument be concrete or reified, not soft
    // reified or erased
    if is_reified(tparam) {
        match tparam.tp_reified() {
            ReifyKind::Reified | ReifyKind::SoftReified => {
                let (decl_pos, param_name) = tparam.tp_name();
                let emit_error = |pos: Pos, arg_info| {
                    let err = typing_error::primary(primary::T::InvalidReifiedArg {
                        pos,
                        param_name: param_name.clone(),
                        decl_pos: decl_pos.clone(),
                        arg_info,
                    });
                    typing_error_utils::add_typing_error(&err, env)
                };

                typing_reified_check::validator().validate_hint(
                    env,
                    targ,
                    Some(reification),
                    emit_error,
                )
            }
            ReifyKind::Erased => {}
        }
    };

    if attributes::mem(
        sn::user_attributes::ENFORCEABLE,
        tparam.tp_user_attributes(),
    ) {
        typing_enforceable_hint::validate_hint(env, targ, |pos, ty_info| {
            let (tp_pos, tp_name) = tparam.tp_name();
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::InvalidEnforceableType {
                    kind: primary::InvalidEnforceableTypeKind::Param,
                    pos,
                    ty_info,
                    tp_pos,
                    tp_name,
                }),
                env,
            )
        });
    }

    if attributes::mem(sn::user_attributes::NEWABLE, tparam.tp_user_attributes()) {
        valid_newable_hint(env, tparam.tp_name(), targ)
    }
}

fn verify_call_targs<TP: TparamFields>(
    env: &Env,
    expr_pos: &Pos,
    decl_pos: PosOrDecl,
    tparams: &[TP],
    targs: &[tast::Targ],
    reification: type_validator::Reification,
) {
    if tparams_has_reified(tparams) {
        let tparams_length = tparams.len();
        let targs_length = targs.len();
        if tparams_length != targs_length {
            if targs_length == 0 {
                let decl_pos = Option::unwrap_or(
                    tparams.iter().find_map(|tparam| {
                        if is_reified(tparam) {
                            let (pos, _) = tparam.tp_name();
                            Some(pos)
                        } else {
                            None
                        }
                    }),
                    decl_pos.clone(),
                );
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::RequireArgsReify {
                        decl_pos,
                        pos: expr_pos.clone(),
                    }),
                    env,
                )
            } else {
                // mismatches with targs_length > 0 are not specific to reification and handled
                // elsewhere
            }
        }
    };
    let all_wildcards = targs
        .iter()
        .all(|aast::Targ(_, h)| aast_defs::is_wildcard_hint(h));
    if all_wildcards && tparams_has_reified(tparams) {
        let decl_pos = Option::unwrap_or(
            tparams.iter().find_map(|tparam| {
                if is_reified(tparam) {
                    let (pos, _) = tparam.tp_name();
                    Some(pos)
                } else {
                    None
                }
            }),
            decl_pos.clone(),
        );
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::RequireArgsReify {
                decl_pos,
                pos: expr_pos.clone(),
            }),
            env,
        )
    } else {
        // Unequal_lengths case handled elsewhere
        // (List.iter2 does nothing when the lengths differ)
        if tparams.len() == targs.len() {
            for (tparam, targ) in tparams.iter().zip(targs.iter()) {
                verify_targ_valid(env, reification, tparam, &targ.1)
            }
        }
    }
}

fn get_ft_tparams(env: &Env, fun_ty: &Ty) -> Option<(Vec<Tparam>, bool)> {
    let fun_ty = tast_env::strip_dynamic(env, fun_ty.clone());
    match tast_env::get_underlying_function_type(env, fun_ty) {
        None => None,
        Some((_, fun_ty)) => {
            let is_function_pointer = get_ft_is_function_pointer(&fun_ty);
            Some((fun_ty.tparams.clone(), is_function_pointer))
        }
    }
}

/// `let handler = object inherit Tast_visitor.handler_base ... end`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, x: &'a tast::Expr) {
        // only considering functions where one or more params are reified
        match x {
            aast::Expr(_, call_pos, aast::Expr_::ClassGet(cg))
                if matches!(&cg.0.2, aast::ClassId_::CIreified(_)) =>
            {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::ClassGetReified(call_pos.clone())),
                    env,
                )
            }
            aast::Expr(fun_ty, pos, aast::Expr_::MethodCaller(_)) => {
                match get_ft_tparams(env, fun_ty) {
                    Some((ft_tparams, _)) => {
                        if tparams_has_reified(&ft_tparams) {
                            typing_error_utils::add_typing_error(
                                &typing_error::primary(primary::T::ReifiedFunctionReference(
                                    pos.clone(),
                                )),
                                env,
                            )
                        }
                    }
                    None => {}
                }
            }
            aast::Expr(_, pos, aast::Expr_::FunctionPointer(fp))
                if matches!(
                    &fp.0,
                    aast::FunctionPtrId::FPClassConst(
                        aast::ClassId(_, _, aast::ClassId_::CIreified(_)),
                        _
                    )
                ) && tast_env::is_in_expr_tree(env) =>
            {
                typing_error_utils::add_typing_error(
                    &typing_error::expr_tree(primary::expr_tree::T::ReifiedStaticMethodInExprTree(
                        pos.clone(),
                    )),
                    env,
                )
            }
            aast::Expr(fun_ty, pos, aast::Expr_::FunctionPointer(fp)) => {
                let (_, targs, _) = &**fp;
                match get_ft_tparams(env, fun_ty) {
                    Some((ft_tparams, _)) => verify_call_targs(
                        env,
                        pos,
                        get_pos(fun_ty),
                        &ft_tparams,
                        targs,
                        type_validator::Reification::Resolved,
                    ),
                    None => {}
                }
            }
            aast::Expr(_, pos, aast::Expr_::Call(call)) => {
                let aast::CallExpr {
                    func: aast::Expr(fun_ty, _, expr),
                    targs,
                    ..
                } = &**call;
                let reification =
                    // If need be, we can extend this special casing to all
                    // HH\ReifiedGenerics functions.
                    match expr {
                        aast::Expr_::Id(id) if id.1 == GET_CLASS_FROM_TYPE => {
                            type_validator::Reification::TypeStructure
                        }
                        _ => type_validator::Reification::Resolved,
                    };
                let mut env = env.clone();
                let efun_ty = tast_env::expand_type(&mut env, fun_ty.clone());
                match get_ft_tparams(&env, &efun_ty) {
                    Some((ft_tparams, is_function_pointer)) if !is_function_pointer => {
                        verify_call_targs(
                            &env,
                            pos,
                            get_pos(&efun_ty),
                            &ft_tparams,
                            targs,
                            reification,
                        )
                    }
                    _ => {}
                }
            }
            aast::Expr(_, pos, aast::Expr_::New(new))
                if matches!(&new.0.2, aast::ClassId_::CI(_)) =>
            {
                let (aast::ClassId(_, _, cid_), targs, _, _, _) = &**new;
                let aast::ClassId_::CI(ast_defs::Id(_, class_id)) = cid_ else {
                    unreachable!()
                };
                match tast_env::get_class(env, class_id) {
                    decl_entry::T::Found(cls) => {
                        let tparams = cls::tparams(&cls);
                        let class_pos = cls::pos(&cls);
                        verify_call_targs(
                            env,
                            pos,
                            class_pos,
                            &tparams,
                            targs,
                            type_validator::Reification::Resolved,
                        )
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                }
            }
            aast::Expr(_, pos, aast::Expr_::New(new))
                if matches!(&new.0.2, aast::ClassId_::CIreified(_)) =>
            {
                let aast::ClassId_::CIreified(ast_defs::Id(_, name)) = &new.0.2 else {
                    unreachable!()
                };
                if !tast_env::get_newable(env, name) {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::NewWithoutNewable {
                            pos: pos.clone(),
                            name: name.clone(),
                        }),
                        env,
                    )
                }
            }
            aast::Expr(_, pos, aast::Expr_::New(new))
                if matches!(
                    &new.0.2,
                    aast::ClassId_::CIstatic | aast::ClassId_::CIself | aast::ClassId_::CIparent
                ) =>
            {
                let cid = &new.0.2;
                let t = tast_env::get_self_id(env)
                    .map(|id| tast_env::get_class(env, &id))
                    .and_then(decl_entry::to_option)
                    .map(|cls| cls::tparams(&cls))
                    .map(|tparams| tparams_has_reified(&tparams));
                if let Some(has_reified) = t {
                    if has_reified {
                        let (class_kind, suggested_class_name) = match cid {
                            aast::ClassId_::CIstatic => ("static", None),
                            aast::ClassId_::CIself => ("self", tast_env::get_self_id(env)),
                            aast::ClassId_::CIparent => ("parent", tast_env::get_parent_id(env)),
                            _ => panic!("Unexpected match"),
                        };
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::NewClassReified {
                                pos: pos.clone(),
                                class_kind: class_kind.to_string(),
                                suggested_class_name,
                            }),
                            env,
                        )
                    }
                }
            }
            aast::Expr(_, pos, aast::Expr_::New(new)) => {
                let (aast::ClassId(ty, _, _), targs, _, _, _) = &**new;
                let mut env = env.clone();
                let ty = tast_env::expand_type(&mut env, ty.clone());
                match get_node(&ty) {
                    Ty_::Tclass((_, cid), _, _) => match tast_env::get_class(&env, cid) {
                        decl_entry::T::Found(cls) => {
                            let tparams = cls::tparams(&cls);
                            let class_pos = cls::pos(&cls);
                            verify_call_targs(
                                &env,
                                pos,
                                class_pos,
                                &tparams,
                                targs,
                                type_validator::Reification::Resolved,
                            )
                        }
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                    },
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn at_hint(&mut self, env: &Env, h: &'a tast::Hint) {
        let aast::Hint(_pos, h_) = h;
        match &**h_ {
            aast::Hint_::Happly(ast_defs::Id(_, class_id), hints) => {
                let tc = tast_env::get_class_or_typedef(env, class_id);
                match tc {
                    decl_entry::T::Found(tast_env::ClassOrTypedefResult::ClassResult(tc)) => {
                        let tparams = cls::tparams(&tc);
                        // List.iter2 does nothing when the lengths differ
                        if tparams.len() == hints.len() {
                            for (tp, hint) in tparams.iter().zip(hints.iter()) {
                                verify_targ_valid(
                                    env,
                                    type_validator::Reification::Unresolved,
                                    tp,
                                    hint,
                                )
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn at_tparam(&mut self, env: &Env, tparam: &'a tast::Tparam) {
        // Can't use Attributes.mem here because of a conflict between Nast.user_attributes and Tast.user_attributes
        if tparam
            .user_attributes
            .0
            .iter()
            .any(|ua| sn::user_attributes::NEWABLE == ua.name.1)
        {
            verify_has_consistent_bound(env, tparam)
        }
    }

    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        let ast_defs::Id(pos, name) = &c.name;
        match tast_env::get_class(env, name) {
            decl_entry::T::Found(cls) => match tast_env::get_construct(env, &cls) {
                (_, ConsistentKind::ConsistentConstruct) => {
                    if cls::tparams(&cls)
                        .iter()
                        .any(|t| !(t.reified == ReifyKind::Erased))
                    {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::ConsistentConstructReified(
                                pos.clone(),
                            )),
                            env,
                        )
                    }
                }
                _ => {}
            },
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
        }
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Abstraction;

    use super::*;

    #[test]
    fn is_c_normal_is_concrete_classes_only() {
        assert!(is_c_normal(ClassishKind::Cclass(Abstraction::Concrete)));
        assert!(!is_c_normal(ClassishKind::Cclass(Abstraction::Abstract)));
        assert!(!is_c_normal(ClassishKind::CenumClass(
            Abstraction::Concrete
        )));
        assert!(!is_c_normal(ClassishKind::Cenum));
        assert!(!is_c_normal(ClassishKind::Ctrait));
        assert!(!is_c_normal(ClassishKind::Cinterface));
    }
}
