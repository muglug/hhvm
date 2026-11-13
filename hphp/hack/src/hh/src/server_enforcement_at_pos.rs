// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server_enforcement_at_pos.ml`. See `hh/PORTING.md`.
//!
//! The visitor (`Tast_visitor.reduce` with the overrides of the OCaml's
//! object) keeps its mutable fields (`inside_hint`, `current_*`) in the
//! struct; the results are combined as the OCaml combines them
//! (`self#plus res acc`: the node's own result on the left).

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs;
use oxidized::pos::Pos;

use crate::ctx::Ctx;
use crate::decl_entry;
use crate::decl_provider_internals;
use crate::enforcement_at_pos_service::EnforcedType;
use crate::enforcement_at_pos_service::Enforcement;
use crate::file_content::position;
use crate::folded_class as cls;
use crate::provider_context;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::tast_visitor::IterParams;
use crate::tast_visitor::Reduce;
use crate::tast_visitor::Res;
use crate::tast_visitor::reduce;
use crate::typing_defs::DeclFunParam;
use crate::typing_defs::DeclFunType;
use crate::typing_defs::DeclTy;
use crate::typing_defs::DeclTy_;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::yojson;

type Acc = Option<(Pos, Enforcement)>;

/// A type is "effectively enforced" when the runtime enforces the container
/// type and all erased generic parameters are top types that cannot be
/// violated. We check each type argument positionally:
/// - Key positions accept `arraykey` (the key top type — keys are bounded
///   at `arraykey` and can never be `mixed`)
/// - Value positions accept `mixed` (the global top type)
///
/// For example, `dict<arraykey, mixed>` is effectively enforced.
/// `dict<string, mixed>` is NOT — `string` is a strict subtype of `arraykey`
/// that the runtime does not verify per-element.
pub fn is_effectively_enforced_container(decl_ty: &DeclTy) -> bool {
    fn is_mixed(ty: &DeclTy) -> bool {
        match &**ty.node() {
            DeclTy_::Tmixed => true,
            // Look through supportdyn<mixed> which wraps mixed under SDT
            DeclTy_::Tapply(x) if x.1.len() == 1 && x.0.id().as_str() == sn::classes::SUPPORT_DYN => {
                is_mixed(&x.1[0])
            }
            _ => false,
        }
    }
    let is_arraykey = |ty: &DeclTy| matches!(&**ty.node(), DeclTy_::Tprim(aast::Tprim::Tarraykey));
    let check_args = |n: &str, tyl: &[DeclTy]| match tyl {
        [kty, vty]
            if n == sn::collections::DICT
                || n == sn::collections::KEYED_CONTAINER
                || n == sn::collections::MAP =>
        {
            is_arraykey(kty) && is_mixed(vty)
        }
        [ty] if n == sn::collections::VEC
            || n == sn::collections::CONTAINER
            || n == sn::collections::VECTOR =>
        {
            is_mixed(ty)
        }
        [ty] if n == sn::collections::KEYSET || n == sn::collections::SET => is_arraykey(ty),
        _ => false,
    };
    match &**decl_ty.node() {
        DeclTy_::Tapply(x) => check_args(x.0.id().as_str(), &x.1),
        DeclTy_::Toption(inner) => match &**inner.node() {
            DeclTy_::Tapply(x) => check_args(x.0.id().as_str(), &x.1),
            _ => false,
        },
        _ => false,
    }
}

/// Extract the decl_fun_type from a decl_ty, if it's a function type.
fn get_decl_ft(ty: &DeclTy) -> Option<DeclFunType> {
    match &**ty.node() {
        DeclTy_::Tfun(ft) => Some((**ft).clone()),
        _ => None,
    }
}

/// Extract a class name from a localized type, handling simple class types,
/// dependent types (e.g. from static::), and Tgeneric "this".
fn get_class_name_from_ty(env: &Env, ty: &Ty) -> Option<String> {
    match ty.get_node() {
        Ty_::Tclass(id, _, _) => Some(id.1.clone()),
        Ty_::Tdependent(_, bound_ty) => get_class_name_from_ty(env, bound_ty),
        Ty_::Tgeneric(name) if name == "this" => tast_env::get_self_id(env),
        _ => None,
    }
}

/// Extract a class name from an inferred receiver type only when we can
/// trust the inference. The receiver is trusted when:
/// - The type is exact (e.g. `new C()` produces an exact `C`), or
/// - The TAST was checked only once (no dynamic assumptions) and the
///   type is not a like type (like types indicate the value may be dynamic).
///
/// This allows us to resolve instance method calls and property assignments
/// on non-`$this` receivers when the inferred type is reliable.
fn get_trusted_class_name(checked_once: bool, ty: &Ty) -> Option<String> {
    match ty.get_node() {
        Ty_::Tclass(id, crate::typing_defs::Exact::Exact, _) => Some(id.1.clone()),
        Ty_::Tclass(id, _, _) if checked_once => Some(id.1.clone()),
        _ => None,
    }
}

/// Look up a method's unpessimised fun_type from the shallow class where
/// it is declared, avoiding the like-type wrapping that class folding
/// applies under SDT. Uses the folded class to resolve `ce_origin` for
/// inherited methods, then reads the shallow class of the origin.
fn resolve_shallow_method_type(
    env: &Env,
    ctx: &Arc<Ctx>,
    class_name: &str,
    method_name: &str,
    is_static: bool,
) -> Option<DeclFunType> {
    let c = decl_entry::to_option(tast_env::get_class(env, class_name))?;
    let ce = if is_static {
        tast_env::get_static_member(true, env, &c, method_name)
    } else {
        tast_env::get_method(env, &c, method_name)
    }?;
    let origin = &ce.ce_origin;
    let sc = decl_provider_internals::get_shallow_class(ctx, origin)?;
    let methods = if is_static {
        &sc.static_methods
    } else {
        &sc.methods
    };
    let m = methods.iter().find(|m| m.name.id().as_str() == method_name)?;
    get_decl_ft(&m.ty)
}

/// Look up a constructor's unpessimised fun_type from the shallow class
/// where it is declared. Handles inherited constructors via `ce_origin`.
fn resolve_shallow_constructor_type(
    env: &Env,
    ctx: &Arc<Ctx>,
    class_name: &str,
) -> Option<DeclFunType> {
    let c = decl_entry::to_option(tast_env::get_class(env, class_name))?;
    let (ce_opt, _) = tast_env::get_construct(env, &c);
    let ce = ce_opt?;
    let origin = &ce.ce_origin;
    let sc = decl_provider_internals::get_shallow_class(ctx, origin)?;
    let m = sc.constructor.as_ref()?;
    get_decl_ft(&m.ty)
}

/// Look up a property's unpessimised decl_ty from the shallow class where
/// it is declared. Handles inherited properties via `ce_origin`.
fn resolve_shallow_prop_type(
    env: &Env,
    ctx: &Arc<Ctx>,
    class_name: &str,
    prop_name: &str,
) -> Option<DeclTy> {
    let c = decl_entry::to_option(tast_env::get_class(env, class_name))?;
    let ce = tast_env::get_prop(env, &c, prop_name)?;
    let origin = &ce.ce_origin;
    let sc = decl_provider_internals::get_shallow_class(ctx, origin)?;
    let sp = sc.props.iter().find(|p| p.name.id().as_str() == prop_name)?;
    Some(sp.ty.clone())
}

/// Extract the class name from a class_id_ when syntactically determined.
/// Returns None for CIstatic/CIexpr which depend on runtime dispatch or
/// type inference.
fn get_class_name_from_cid(env: &Env, cid: &aast::ClassId_<tast::Ty, tast::SavedEnv>) -> Option<String> {
    match cid {
        aast::ClassId_::CI(ast_defs::Id(_, name)) => Some(name.clone()),
        aast::ClassId_::CIself => tast_env::get_self_id(env),
        _ => None,
    }
}

/// Given a TAST function expression, look up the called function/method's
/// declaration and return its decl-level fun_type.
/// Uses unpessimised declarations so that SDT like-type wrapping
/// does not obscure the programmer-written type.
///
/// For instance method calls, the receiver is trusted when:
/// - It is `$this` (syntactically determined), or
/// - The inferred type is exact, or
/// - The TAST was checked once and the type is not like-typed.
///
/// Otherwise the receiver type comes from inference which may be
/// inaccurate, and we skip the position.
fn resolve_decl_fun_type(checked_once: bool, env: &Env, func_expr_: &tast::Expr_) -> Option<DeclFunType> {
    let ctx = tast_env::get_ctx(env);
    match func_expr_ {
        aast::Expr_::Id(id) => {
            // Regular function call: foo(...)
            let fe = decl_entry::to_option(decl_provider_internals::get_fun_without_pessimise(
                &ctx, &id.1,
            ))?;
            get_decl_ft(&fe.ty)
        }
        aast::Expr_::ObjGet(x) => match &**x {
            (aast::Expr(_, _, aast::Expr_::This), aast::Expr(_, _, aast::Expr_::Id(mid)), _, _) => {
                // $this->method(...) — enclosing class is syntactically determined
                let name = tast_env::get_self_id(env)?;
                resolve_shallow_method_type(env, &ctx, &name, &mid.1, false)
            }
            (aast::Expr(recv_ty, _, _), aast::Expr(_, _, aast::Expr_::Id(mid)), _, _) => {
                // $obj->method(...) — trust the receiver if exact or checked once
                let name = get_trusted_class_name(checked_once, recv_ty)?;
                resolve_shallow_method_type(env, &ctx, &name, &mid.1, false)
            }
            _ => None,
        },
        aast::Expr_::ClassConst(x) => {
            // Static method call: Class::method(), self::method(), static::method(), parent::method()
            let (aast::ClassId(recv_ty, _, _), (_, method_name)) = &**x;
            let name = get_class_name_from_ty(env, recv_ty)?;
            resolve_shallow_method_type(env, &ctx, &name, method_name, true)
        }
        _ => None,
    }
}

// `Typing_defs` functions on a `decl_ty fun_type` (the Rust ones take a
// localized `fun_type`).

fn get_fp_is_named(fp: &DeclFunParam) -> bool {
    fp.flags.contains(oxidized::typing_defs_flags::FunParamFlags::NAMED)
}

fn get_fp_splat(fp: &DeclFunParam) -> bool {
    fp.flags.contains(oxidized::typing_defs_flags::FunParamFlags::SPLAT)
}

fn get_ft_variadic(ft: &DeclFunType) -> bool {
    ft.flags.contains(oxidized::typing_defs_flags::FunTypeFlags::VARIADIC)
}

/// `Typing_defs.ft_named_variadic_param`
fn ft_named_variadic_param(ft: &DeclFunType) -> Option<&DeclFunParam> {
    if ft.flags.contains(oxidized::typing_defs_flags::FunTypeFlags::NAMED_VARIADIC) {
        ft.params.last()
    } else {
        None
    }
}

/// `Typing_defs.ft_params_without_named_variadic`
fn ft_params_without_named_variadic(ft: &DeclFunType) -> &[DeclFunParam] {
    match ft_named_variadic_param(ft) {
        Some(_) => &ft.params[..ft.params.len() - 1],
        None => &ft.params,
    }
}

/// `Typing_defs.Named_params.name_of_named_param`
fn name_of_named_param(fp: &DeclFunParam) -> Option<String> {
    if get_fp_is_named(fp) {
        fp.name.map(|raw_name| {
            let raw_name = raw_name.as_str();
            raw_name.strip_prefix('$').unwrap_or(raw_name).to_string()
        })
    } else {
        None
    }
}

struct EnforcementVisitor {
    checked_once: bool,
    cursor: position::T,
    acc: Acc,
    /// Type annotations (hints): only match the outermost hint to avoid
    /// reporting enforcement for nested type arguments (e.g. the `int`
    /// inside `Ref<int>` is NOT at an enforced boundary).
    inside_hint: bool,
    current_is_async: bool,
    current_return_hint: Option<tast::Hint>,
    /// Constraint hints from tparams currently in scope.
    current_tparam_constraints: Vec<(String, Vec<(ast_defs::ConstraintKind, tast::Hint)>)>,
}

impl EnforcementVisitor {
    fn cursor_inside(&self, pos: &Pos) -> bool {
        let (line, char) = position::line_column_one_based(&self.cursor);
        crate::pos::inside_one_based(pos, line, char)
    }

    fn decl_ty_to_json(&self, env: &Env, decl_ty: &DeclTy) -> yojson::safe::T {
        let locl_ty = tast_env::localize_no_subst(&mut env.clone(), true, decl_ty);
        tast_env::ty_to_json(env, None, &locl_ty)
    }

    fn make_enforced_type(&self, env: &Env, decl_ty: &DeclTy) -> EnforcedType {
        let ty_str = tast_env::print_decl_ty(None, env, decl_ty);
        let ty_json = self.decl_ty_to_json(env, decl_ty);
        EnforcedType { ty_str, ty_json }
    }

    fn compute_enforcement_result(&self, env: &Env, pos: &Pos, decl_ty: &DeclTy) -> Acc {
        let this_class = decl_entry::to_option(tast_env::get_self_class(env));
        let enforcement = crate::typing_enforceability::get_enforcement(
            Some(true),
            this_class.as_ref(),
            env,
            decl_ty,
        );
        match enforcement {
            crate::typing_defs_core::Enforcement::Enforced => Some((
                pos.clone(),
                Enforcement::Enforced(vec![self.make_enforced_type(env, decl_ty)]),
            )),
            crate::typing_defs_core::Enforcement::Unenforced => {
                if is_effectively_enforced_container(decl_ty) {
                    Some((
                        pos.clone(),
                        Enforcement::Enforced(vec![self.make_enforced_type(env, decl_ty)]),
                    ))
                } else {
                    match &**decl_ty.node() {
                        DeclTy_::Tgeneric(name) => {
                            let bounds =
                                self.find_enforceable_bounds(env, this_class.as_ref(), name.as_str());
                            if bounds.is_empty() {
                                Some((pos.clone(), Enforcement::Unenforced))
                            } else {
                                Some((pos.clone(), Enforcement::Enforced(bounds)))
                            }
                        }
                        _ => Some((pos.clone(), Enforcement::Unenforced)),
                    }
                }
            }
        }
    }

    fn match_arg_to_param(&self, env: &Env, ft: &DeclFunType, args: &[tast::Argument]) -> Acc {
        let split = args
            .iter()
            .position(|arg| {
                let aast::Expr(_, pos, _) = crate::aast_utils::arg_to_expr(arg);
                self.cursor_inside(pos)
            })
            .unwrap_or(args.len());
        let (preceding_args, args_at_cursor) = args.split_at(split);
        let arg = args_at_cursor.first()?;
        let params = ft_params_without_named_variadic(ft);
        let param = match crate::typing_defs::named_params::name_of_arg(arg) {
            Some(name) => {
                let used_names: Vec<String> = preceding_args
                    .iter()
                    .filter_map(crate::typing_defs::named_params::name_of_arg)
                    .collect();
                let named_params: Vec<(String, &DeclFunParam)> = params
                    .iter()
                    .filter_map(|param| name_of_named_param(param).map(|name| (name, param)))
                    .collect();
                let named_param = if used_names.contains(&name) {
                    None
                } else {
                    named_params
                        .iter()
                        .find(|(n, _)| *n == name)
                        .map(|(_, p)| *p)
                };
                named_param.or_else(|| ft_named_variadic_param(ft))
            }
            None => {
                let index = preceding_args
                    .iter()
                    .filter(|arg| crate::typing_defs::named_params::name_of_arg(arg).is_none())
                    .count();
                let positional_params: Vec<&DeclFunParam> =
                    params.iter().filter(|param| !get_fp_is_named(param)).collect();
                match positional_params.get(index) {
                    Some(param) => Some(*param),
                    None => positional_params
                        .last()
                        .copied()
                        .filter(|param| get_ft_variadic(ft) && !get_fp_splat(param)),
                }
            }
        };
        let aast::Expr(_, arg_pos, _) = crate::aast_utils::arg_to_expr(arg);
        let param = param?;
        self.compute_enforcement_result(env, arg_pos, &param.ty)
    }

    /// Look up a generic's upper-bound constraints and return all
    /// enforceable ones. For example, `T as I as J as arraykey` would
    /// return `[I; J; arraykey]` since all are enforced at runtime.
    fn find_enforceable_bounds(&self, env: &Env, this_class: Option<&cls::T>, name: &str) -> Vec<EnforcedType> {
        let constraints = self
            .current_tparam_constraints
            .iter()
            .find_map(|(tp_name, cstrs)| if tp_name == name { Some(cstrs) } else { None });
        match constraints {
            None => vec![],
            Some(cstrs) => cstrs
                .iter()
                .filter_map(|(kind, hint)| match kind {
                    ast_defs::ConstraintKind::ConstraintAs => {
                        let bound_ty = tast_env::hint_to_ty(env, hint);
                        // Skip mixed — it's the implicit bound on every generic
                        // and doesn't add enforcement information.
                        fn is_mixed_bound(ty: &DeclTy) -> bool {
                            match &**ty.node() {
                                DeclTy_::Tmixed => true,
                                DeclTy_::Tapply(x)
                                    if x.1.len() == 1 && x.0.id().as_str() == sn::classes::SUPPORT_DYN =>
                                {
                                    is_mixed_bound(&x.1[0])
                                }
                                _ => false,
                            }
                        }
                        if is_mixed_bound(&bound_ty) {
                            None
                        } else {
                            let bound_enforcement = crate::typing_enforceability::get_enforcement(
                                Some(true),
                                this_class,
                                env,
                                &bound_ty,
                            );
                            match bound_enforcement {
                                crate::typing_defs_core::Enforcement::Enforced => {
                                    Some(self.make_enforced_type(env, &bound_ty))
                                }
                                crate::typing_defs_core::Enforcement::Unenforced => {
                                    // Also check for effectively enforced containers
                                    // e.g. T as vec<mixed> — the bound is effectively
                                    // enforced even though get_enforcement says not.
                                    if is_effectively_enforced_container(&bound_ty) {
                                        Some(self.make_enforced_type(env, &bound_ty))
                                    } else {
                                        None
                                    }
                                }
                            }
                        }
                    }
                    _ => None,
                })
                .collect(),
        }
    }

    fn save_tparams(tparams: &[tast::Tparam]) -> Vec<(String, Vec<(ast_defs::ConstraintKind, tast::Hint)>)> {
        tparams
            .iter()
            .map(|tp| (tp.name.1.clone(), tp.constraints.clone()))
            .collect()
    }

    /// For async functions, unwrap `Awaitable<T>` to get the inner type `T`
    /// since the runtime enforces `T`, not `Awaitable<T>`. For non-async
    /// functions returning `Awaitable<T>`, the return type IS `Awaitable<T>`.
    fn unwrap_awaitable_hint(&self, hint: tast::Hint) -> tast::Hint {
        if self.current_is_async {
            match &*hint.1 {
                aast::Hint_::Happly(ast_defs::Id(_, name), hints)
                    if hints.len() == 1 && name == sn::classes::AWAITABLE =>
                {
                    hints[0].clone()
                }
                _ => hint,
            }
        } else {
            hint
        }
    }
}

impl<'a> Reduce<'a> for EnforcementVisitor {
    type Acc = Acc;

    fn zero(&self) -> Acc {
        None
    }

    fn plus(&self, lhs: Acc, rhs: Acc) -> Acc {
        match (lhs, rhs) {
            (Some(l), Some(r)) => {
                if crate::pos::length(&l.0) <= crate::pos::length(&r.0) {
                    Some(l)
                } else {
                    Some(r)
                }
            }
            (Some(l), None) => Some(l),
            (None, Some(r)) => Some(r),
            (None, None) => None,
        }
    }

    fn acc(&mut self) -> &mut Acc {
        &mut self.acc
    }
}

impl EnforcementVisitor {
    /// `self#plus res acc`, added to the accumulator.
    fn add_plus(&mut self, res: Acc, acc: Acc) {
        let r = self.plus(res, acc);
        reduce::add(self, r)
    }
}

impl<'a> Visitor<'a> for EnforcementVisitor {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a; class_var, expression_tree);

    fn visit_hint(&mut self, env: &mut Env, hint: &'a tast::Hint) -> Res {
        if self.inside_hint {
            // Already inside a hint — this is a nested type argument,
            // skip enforcement check but still recurse for sub-hints.
            hint.recurse(env, self)
        } else {
            self.inside_hint = true;
            let (r, acc) = reduce::result(self, |v| hint.recurse(env, v));
            self.inside_hint = false;
            r?;
            let pos = &hint.0;
            if self.cursor_inside(pos) {
                let decl_ty = tast_env::hint_to_ty(env, hint);
                let res = self.compute_enforcement_result(env, pos, &decl_ty);
                self.add_plus(res, acc)
            } else {
                reduce::add(self, acc)
            }
            Ok(())
        }
    }

    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Res {
        match expr_ {
            // --- Call arguments ---
            aast::Expr_::Call(call_expr) => {
                let (r, acc) = reduce::result(self, |v| reduce::on_expr_(v, env, expr_));
                r?;
                let aast::CallExpr { func, args, .. } = &**call_expr;
                let aast::Expr(_, _, func_expr_) = func;
                match resolve_decl_fun_type(self.checked_once, env, func_expr_) {
                    None => reduce::add(self, acc),
                    Some(ft) => {
                        let res = self.match_arg_to_param(env, &ft, args);
                        self.add_plus(res, acc)
                    }
                }
                Ok(())
            }
            _ => reduce::on_expr_(self, env, expr_),
        }
    }

    fn visit_fun_def(&mut self, env: &mut Env, fd: &'a tast::FunDef) -> Res {
        let saved = self.current_tparam_constraints.clone();
        let mut cstrs = Self::save_tparams(&fd.tparams);
        cstrs.extend(self.current_tparam_constraints.iter().cloned());
        self.current_tparam_constraints = cstrs;
        let res = fd.recurse(env, self);
        self.current_tparam_constraints = saved;
        res
    }

    fn visit_class_(&mut self, env: &mut Env, c: &'a tast::Class_) -> Res {
        let saved = self.current_tparam_constraints.clone();
        let mut cstrs = Self::save_tparams(&c.tparams);
        cstrs.extend(self.current_tparam_constraints.iter().cloned());
        self.current_tparam_constraints = cstrs;
        let res = c.recurse(env, self);
        self.current_tparam_constraints = saved;
        res
    }

    fn visit_fun_(&mut self, env: &mut Env, f: &'a tast::Fun_) -> Res {
        let saved_hint = self.current_return_hint.take();
        let saved_async = self.current_is_async;
        self.current_return_hint = crate::aast::hint_of_type_hint(&f.ret).clone();
        self.current_is_async = f.fun_kind == ast_defs::FunKind::FAsync;
        let res = reduce::on_fun_(self, env, f);
        self.current_return_hint = saved_hint;
        self.current_is_async = saved_async;
        res
    }

    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> Res {
        let saved_hint = self.current_return_hint.take();
        let saved_cstrs = self.current_tparam_constraints.clone();
        let saved_async = self.current_is_async;
        self.current_return_hint = crate::aast::hint_of_type_hint(&m.ret).clone();
        self.current_is_async = m.fun_kind == ast_defs::FunKind::FAsync;
        let mut cstrs = Self::save_tparams(&m.tparams);
        cstrs.extend(self.current_tparam_constraints.iter().cloned());
        self.current_tparam_constraints = cstrs;
        let res = reduce::on_method_(self, env, m);
        self.current_return_hint = saved_hint;
        self.current_tparam_constraints = saved_cstrs;
        self.current_is_async = saved_async;
        res
    }

    // --- Return statements ---
    fn visit_stmt_(&mut self, env: &mut Env, stmt_: &'a tast::Stmt_) -> Res {
        let (r, acc) = reduce::result(self, |v| stmt_.recurse(env, v));
        r?;
        match stmt_ {
            aast::Stmt_::Return(e) => match &**e {
                Some(aast::Expr(_, pos, _)) if self.cursor_inside(pos) => {
                    match self.current_return_hint.clone() {
                        Some(hint) => {
                            let hint = self.unwrap_awaitable_hint(hint);
                            let decl_ty = tast_env::hint_to_ty(env, &hint);
                            let res = self.compute_enforcement_result(env, pos, &decl_ty);
                            self.add_plus(res, acc)
                        }
                        None => reduce::add(self, acc),
                    }
                }
                _ => reduce::add(self, acc),
            },
            _ => reduce::add(self, acc),
        }
        Ok(())
    }

    // --- Constructor arguments, property assignments, array indexing ---
    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Res {
        let (r, acc) = reduce::result(self, |v| expr.recurse(env, v));
        r?;
        let aast::Expr(_, _, expr_) = expr;
        match expr_ {
            // --- Constructor arguments: new ClassName(args) ---
            // The class name is syntactically determined for CI and CIself.
            // CIstatic/CIexpr are excluded as they depend on runtime dispatch.
            aast::Expr_::New(x) => {
                let (aast::ClassId(_, _, cid), _, args, _, _) = &**x;
                let ctx = tast_env::get_ctx(env);
                let ft_opt = get_class_name_from_cid(env, cid)
                    .and_then(|name| resolve_shallow_constructor_type(env, &ctx, &name));
                match ft_opt {
                    None => reduce::add(self, acc),
                    Some(ft) => {
                        let res = self.match_arg_to_param(env, &ft, args);
                        self.add_plus(res, acc)
                    }
                }
            }
            // --- Property assignment RHS ---
            // $this->prop: enclosing class is syntactically determined.
            // $obj->prop: receiver is trusted if the inferred type is exact
            // or the TAST was checked once and the type is not like-typed.
            aast::Expr_::Assign(x)
                if matches!(
                    &**x,
                    (aast::Expr(_, _, aast::Expr_::ObjGet(og)), _, aast::Expr(_, rhs_pos, _))
                        if matches!(&**og, (_, aast::Expr(_, _, aast::Expr_::Id(_)), _, ast_defs::PropOrMethod::IsProp))
                            && self.cursor_inside(rhs_pos)
                ) =>
            {
                let (aast::Expr(_, _, lhs), _, aast::Expr(_, rhs_pos, _)) = &**x;
                let aast::Expr_::ObjGet(og) = lhs else {
                    unreachable!()
                };
                let (aast::Expr(recv_ty, _, recv_expr_), aast::Expr(_, _, prop), _, _) = &**og;
                let aast::Expr_::Id(prop_id) = prop else {
                    unreachable!()
                };
                let prop_name = &prop_id.1;
                let class_name = match recv_expr_ {
                    aast::Expr_::This => tast_env::get_self_id(env),
                    _ => get_trusted_class_name(self.checked_once, recv_ty),
                };
                let ctx = tast_env::get_ctx(env);
                let res = class_name.and_then(|name| {
                    resolve_shallow_prop_type(env, &ctx, &name, prop_name)
                        .and_then(|decl_ty| self.compute_enforcement_result(env, rhs_pos, &decl_ty))
                });
                self.add_plus(res, acc)
            }
            // --- Array index expressions ---
            aast::Expr_::ArrayGet(x)
                if matches!(&**x, (_, Some(aast::Expr(_, idx_pos, _))) if self.cursor_inside(idx_pos)) =>
            {
                let (_, idx) = &**x;
                let idx_pos = &idx.as_ref().unwrap().1;
                let arraykey_ty = DeclTy::prim(<crate::ctx::R as ty::reason::Reason>::none(), aast::Tprim::Tarraykey);
                let res = self.compute_enforcement_result(env, idx_pos, &arraykey_ty);
                self.add_plus(res, acc)
            }
            _ => reduce::add(self, acc),
        }
        Ok(())
    }
}

pub fn enforcement_at_pos(
    checked_once: bool,
    ctx: &provider_context::T,
    tast: &[tast::Def],
    cursor: &position::T,
) -> crate::enforcement_at_pos_service::Result {
    let mut visitor = EnforcementVisitor {
        checked_once,
        cursor: *cursor,
        acc: None,
        inside_hint: false,
        current_is_async: false,
        current_return_hint: None,
        current_tparam_constraints: vec![],
    };
    reduce::go(&mut visitor, ctx, tast).map(|(_, e)| e)
}

pub fn go_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    cursor: &position::T,
) -> crate::enforcement_at_pos_service::Result {
    let crate::tast_provider::ComputeTastResult { tast, .. } =
        crate::tast_provider::compute_tast_quarantined(ctx, entry);
    let checked_once = tast.under_dynamic_assumptions.is_none();
    enforcement_at_pos(checked_once, ctx, &tast.under_normal_assumptions, cursor)
}

pub fn result_to_json_string(
    result: &crate::enforcement_at_pos_service::Result,
    (fn_, pos): (&str, &position::T),
) -> String {
    use yojson::safe::T as J;
    let (line, char) = position::line_column_one_based(pos);
    let mut fields = vec![(
        "position".to_string(),
        J::Assoc(vec![
            ("file".to_string(), J::String(fn_.to_string())),
            ("line".to_string(), J::Int(line)),
            ("character".to_string(), J::Int(char)),
        ]),
    )];
    match result {
        Some(Enforcement::Enforced(types)) => {
            let json_types = types.iter().map(|t| t.ty_json.clone()).collect();
            fields.push(("enforcement".to_string(), J::String("Enforced".to_string())));
            fields.push(("types".to_string(), J::List(json_types)));
        }
        Some(Enforcement::Unenforced) => {
            fields.push(("enforcement".to_string(), J::String("Unenforced".to_string())))
        }
        None => fields.push(("enforcement".to_string(), J::Null)),
    }
    yojson::safe::to_string(&J::Assoc(fields))
}
