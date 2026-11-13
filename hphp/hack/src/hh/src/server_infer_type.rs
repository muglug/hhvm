// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_infer_type.ml`.
//!
//! Owned by **E1** (plan §7.3). Ported by F2 (hover and signature help need
//! `human_friendly_type_at_pos`; F1's `server_type_definition` too).
//!
//! The OCaml visitors patch some nodes before visiting them (the type of the
//! class id of a `new`, the function type of a call). The patched node is a
//! new value, not part of the TAST: its visit is made by a fresh visitor of
//! the same kind (whose result is added to the accumulator), since a
//! visitor over the TAST only visits nodes that live as long as the TAST.

use std::sync::Arc;

use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;

use crate::aast_utils;
use crate::file_content::position;
use crate::identify_symbol_service;
use crate::pos;
use crate::pos::Pos;
use crate::provider_context;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_expand;
use crate::tast_provider;
use crate::tast_visitor;
use crate::tast_visitor::IterParams;
use crate::tast_visitor::Reduce;
use crate::tast_visitor::Res;
use crate::tast_visitor::reduce;
use crate::tast_with_dynamic;
use crate::typing_defs;
use crate::typing_make_type;
use crate::typing_reason;

/// Information gathered from TAST.
/// Type variables occurring are solved with respect to this environment.
#[derive(Clone)]
pub struct T {
    pub env: Env,
    pub ty: tast::Ty,
    pub targs: Vec<tast::Targ>,
}

/// Usually we just want the type, which might be generic
pub fn get_type(x: &T) -> &tast::Ty {
    &x.ty
}

pub fn get_targs(x: &T) -> &[tast::Targ] {
    &x.targs
}

pub fn get_env(x: &T) -> &Env {
    &x.env
}

fn mk_info(env: &Env, ty: &tast::Ty) -> T {
    T {
        env: env.clone(),
        ty: tast_expand::expand_ty(None, None, env, ty.clone()),
        targs: vec![],
    }
}

fn mk_info_with_targs(env: &Env, ty: &tast::Ty, targs: &[tast::Targ]) -> T {
    T {
        env: env.clone(),
        ty: tast_expand::expand_ty(None, None, env, ty.clone()),
        targs: targs.to_vec(),
    }
}

/// Is this expression indexing into a value of type shape?
/// E.g. $some_shope['foo'].
///
/// If so, return the receiver.
fn shape_indexing_receiver<'e>(env: &Env, expr: &'e tast::Expr) -> Option<&'e tast::Expr> {
    match &expr.2 {
        aast::Expr_::ArrayGet(x) => {
            let recv = &x.0;
            let ty = tast_env::fully_expand(env, recv.0.clone());
            match typing_defs::get_node(&ty) {
                typing_defs::Ty_::Tshape(_) => Some(recv),
                _ => None,
            }
        }
        _ => None,
    }
}

fn class_const_ty(env: &Env, cc: &tast::ClassConst) -> Option<tast::Ty> {
    match &cc.type_ {
        Some(hint) => {
            let decl_ty = tast_env::hint_to_ty(env, hint);
            let ty = tast_env::localize_no_subst(&mut env.clone(), true, &decl_ty);
            Some(ty)
        }
        None => {
            let init_expr = match &cc.kind {
                aast::ClassConstKind::CCConcrete(e) => Some(e),
                aast::ClassConstKind::CCAbstract(e_opt) => e_opt.as_ref(),
            };
            init_expr.map(|e| e.0.clone())
        }
    }
}

fn class_id_ty(env: &Env, id: &oxidized::ast_defs::Id) -> tast::Ty {
    let p = &id.0;
    let hint = aast::Hint(p.clone(), Box::new(aast::Hint_::Happly(id.clone(), vec![])));
    let decl_ty = tast_env::hint_to_ty(env, &hint);
    tast_env::localize_no_subst(&mut env.clone(), true, &decl_ty)
}

/// The result for each cursor: the position of the node and its info.
type Acc = Vec<Option<(Pos, T)>>;

/// `base_visitor ~human_friendly ~under_dynamic cursors`
///
/// Return the type of the smallest expression node whose associated span
/// (the Pos.t in its Tast.ExprAnnotation.t) contains the given position.
/// "Smallest" here refers to the size of the node's associated span, in terms of
/// its byte length in the original source file.
///
/// If there is no single smallest node (i.e., multiple expression nodes have
/// spans of the same length containing the given position, where that length is
/// less than the length of all other spans containing the given position),
/// return the type of the first of these nodes visited in a preorder traversal
/// of the Tast.
///
/// (See the OCaml for why.)
struct BaseVisitor<'c> {
    human_friendly: bool,
    under_dynamic: bool,
    cursors: &'c [position::T],
    acc: Acc,
}

impl<'c> BaseVisitor<'c> {
    fn new(human_friendly: bool, under_dynamic: bool, cursors: &'c [position::T]) -> Self {
        BaseVisitor {
            human_friendly,
            under_dynamic,
            cursors,
            acc: cursors.iter().map(|_| None).collect(),
        }
    }

    /// A visitor like this one, for a node made by this one.
    fn fresh(&self) -> Self {
        Self::new(self.human_friendly, self.under_dynamic, self.cursors)
    }

    fn correct_assumptions(&self, env: &Env) -> bool {
        let is_under_dynamic_assumptions =
            tast::is_under_dynamic_assumptions(tast_env::eq_typing_env(env).checked);
        is_under_dynamic_assumptions == self.under_dynamic
    }

    fn select_pos(&self, pos: &Pos, env: &Env, ty: &tast::Ty) -> Acc {
        let correct_assumptions = self.correct_assumptions(env);
        self.cursors
            .iter()
            .map(|cursor| {
                let (line, char) = position::line_column_one_based(cursor);
                if pos::inside_one_based(pos, line, char) && correct_assumptions {
                    Some((pos.clone(), mk_info(env, ty)))
                } else {
                    None
                }
            })
            .collect()
    }

    fn select_pos_targs(&self, pos: &Pos, env: &Env, ty: &tast::Ty, targs: &[tast::Targ]) -> Acc {
        let correct_assumptions = self.correct_assumptions(env);
        self.cursors
            .iter()
            .map(|cursor| {
                let (line, char) = position::line_column_one_based(cursor);
                if pos::inside_one_based(pos, line, char) && correct_assumptions {
                    Some((pos.clone(), mk_info_with_targs(env, ty, targs)))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Visit a node that is not part of the TAST with a fresh visitor, and
    /// add its result.
    fn visit_owned(&mut self, env: &mut Env, f: impl FnOnce(&mut BaseVisitor<'c>, &mut Env) -> Res) -> Res {
        let mut sub = self.fresh();
        let res = f(&mut sub, env);
        reduce::add(self, sub.acc);
        res
    }

    fn on_expr<'a>(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Res {
        let aast::Expr(ty, pos, expr_) = expr;
        // For new expressions such as new C(x,y) when hovering over
        // the C we would like to see the constructor's function signature,
        // not the type of the created instance. Easiest way to arrange this is
        // to patch the type before recursing.
        let patched: Option<tast::Expr> = match expr_ {
            aast::Expr_::New(n) => {
                let (cid, targs, el, e, ctor_ty) = &**n;
                let aast::ClassId(_, pos_cid, cid_) = cid;
                Some(aast::Expr(
                    ty.clone(),
                    pos.clone(),
                    aast::Expr_::New(Box::new((
                        aast::ClassId(ctor_ty.clone(), pos_cid.clone(), cid_.clone()),
                        targs.clone(),
                        el.clone(),
                        e.clone(),
                        ctor_ty.clone(),
                    ))),
                ))
            }
            _ => None,
        };
        let res = self.select_pos(pos, env, ty);
        reduce::add(self, res);
        match &patched {
            Some(patched) => {
                // Not an `Array_get`: no shape indexing receiver.
                self.visit_owned(env, |v, env| patched.recurse(env, v))
            }
            None => match shape_indexing_receiver(env, expr) {
                Some(recv) if self.human_friendly => {
                    // If we're looking at a shape indexing expression, we don't
                    // want to recurse on the string literal.
                    //
                    // For example, if we have the code $user['age'] and hover
                    // over 'age', we want the hover type to be int, not string.
                    self.visit_expr(env, recv)
                }
                _ => expr.recurse(env, self),
            },
        }
    }

    fn on_call<'a>(&mut self, env: &mut Env, call: &'a tast::CallExpr) -> Res {
        let aast::CallExpr {
            func: aast::Expr(ty, pos, expr_),
            targs,
            args,
            unpacked_arg,
        } = call;
        let (sd, ty) = tast_env::strip_supportdyn(env, ty.clone());
        // Intercept function type for call with a literal label argument #Lab
        // or a value of literal type #Lab when parameter is of type EnumClass\Label.
        // Replace parameter type by type #Lab to improve the developer experience when
        // hovering over calls to label-based functions.
        //
        // If the call is through an instance method, replace the type on the inner obj->meth
        // expression so that it gets picked up by the call to super#on_Call.
        let (patched_func, ty) = match typing_defs::deref(&ty) {
            (r, typing_defs::Ty_::Tfun(ft)) => {
                let refine_fp_with_arg =
                    |fp: &typing_defs::FunParam, arg: &tast::Argument| -> typing_defs::FunParam {
                        let aast::Expr(arg_type, p, expr_) = aast_utils::arg_to_expr(arg);
                        let label = match (expr_, typing_defs::get_node(arg_type)) {
                            (aast::Expr_::EnumClassLabel(x), _) if x.0.is_none() => {
                                Some(x.1.clone())
                            }
                            (_, typing_defs::Ty_::Tlabel(label)) => Some(label.clone()),
                            _ => None,
                        };
                        match label {
                            Some(label) => {
                                let label_ty = typing_defs::mk((
                                    typing_reason::witness(p.clone()),
                                    typing_defs::Ty_::Tlabel(label),
                                ));
                                // If function supports dynamic then allow a like-type
                                let fp_type = if sd {
                                    typing_make_type::locl_like(r.clone(), fp.type_.clone())
                                } else {
                                    fp.type_.clone()
                                };
                                if tast_env::is_sub_type(env, &label_ty, &fp_type) {
                                    typing_defs::FunParam {
                                        type_: label_ty,
                                        ..fp.clone()
                                    }
                                } else {
                                    fp.clone()
                                }
                            }
                            None => fp.clone(),
                        }
                    };
                // `List.fold_right`: of the arguments of one name, the first
                // is kept.
                let mut positional_args: Vec<&tast::Argument> = vec![];
                let mut named_args: std::collections::BTreeMap<&str, &tast::Argument> =
                    std::collections::BTreeMap::new();
                for arg in args.iter().rev() {
                    match arg {
                        aast::Argument::Anamed(id, _) => {
                            named_args.insert(id.1.as_str(), arg);
                        }
                        _ => positional_args.push(arg),
                    }
                }
                positional_args.reverse();
                let params_without_named_variadic =
                    typing_defs::ft_params_without_named_variadic(&ft);
                let named_variadic = typing_defs::ft_named_variadic_param(&ft);
                // `replace_label_params_rec positional_args ft_params`
                let mut positional_args = positional_args.into_iter();
                let mut new_params = Vec::with_capacity(ft.params.len());
                for fp in params_without_named_variadic.iter() {
                    if typing_defs::get_fp_splat(fp) {
                        new_params.push(fp.clone())
                    } else {
                        match typing_defs::named_params::name_of_named_param(fp) {
                            Some(name) => {
                                let fp = match named_args.get(name.as_str()) {
                                    Some(arg) => refine_fp_with_arg(fp, arg),
                                    None => fp.clone(),
                                };
                                new_params.push(fp)
                            }
                            None => match positional_args.next() {
                                Some(arg) => new_params.push(refine_fp_with_arg(fp, arg)),
                                None => new_params.push(fp.clone()),
                            },
                        }
                    }
                }
                new_params.extend(named_variadic.cloned());
                // This is an instantiated signature, it makes no sense to include generic parameters
                let ty = typing_defs::mk((
                    r,
                    typing_defs::Ty_::Tfun(std::rc::Rc::new(typing_defs::FunType {
                        params: new_params.into(),
                        tparams: vec![],
                        ..(*ft).clone()
                    })),
                ));
                let expr_ = match expr_ {
                    aast::Expr_::ObjGet(x) => {
                        let (t_lhs, rhs, nf, is_prop) = &**x;
                        let aast::Expr(_, rpos, t_rhs_) = rhs;
                        aast::Expr_::ObjGet(Box::new((
                            t_lhs.clone(),
                            aast::Expr(ty.clone(), rpos.clone(), t_rhs_.clone()),
                            nf.clone(),
                            is_prop.clone(),
                        )))
                    }
                    _ => expr_.clone(),
                };
                (Some(aast::Expr(ty.clone(), pos.clone(), expr_)), ty)
            }
            _ => (None, ty),
        };
        let res = if self.under_dynamic {
            self.select_pos(pos, env, &ty)
        } else {
            self.select_pos_targs(pos, env, &ty, targs)
        };
        reduce::add(self, res);
        // `super#on_Call env call`: the function, the type arguments, the
        // arguments, the unpacked argument.
        match &patched_func {
            Some(func) => self.visit_owned(env, |v, env| v.visit_expr(env, func))?,
            None => self.visit_expr(env, &call.func)?,
        }
        for targ in targs {
            self.visit_targ(env, targ)?;
        }
        for arg in args {
            self.visit_argument(env, arg)?;
        }
        if let Some(e) = unpacked_arg {
            self.visit_expr(env, e)?;
        }
        Ok(())
    }
}

impl<'a> Reduce<'a> for BaseVisitor<'_> {
    type Acc = Acc;

    fn zero(&self) -> Acc {
        self.cursors.iter().map(|_| None).collect()
    }

    fn plus(&self, lhss: Acc, rhss: Acc) -> Acc {
        // A node with position P is not always a parent of every other node with
        // a position contained by P. Some desugaring can cause nodes to be
        // rearranged so that this is no longer the case (e.g., `invariant`).
        //
        // To deal with this, we simply take the smaller node.
        assert_eq!(lhss.len(), rhss.len(), "List.map2_exn");
        lhss.into_iter()
            .zip(rhss)
            .map(|(lhs, rhs)| match (lhs, rhs) {
                (Some(lhs), Some(rhs)) => {
                    if pos::length(&lhs.0) <= pos::length(&rhs.0) {
                        Some(lhs)
                    } else {
                        Some(rhs)
                    }
                }
                (Some(lhs), None) => Some(lhs),
                (None, Some(rhs)) => Some(rhs),
                (None, None) => None,
            })
            .collect()
    }

    fn acc(&mut self) -> &mut Acc {
        &mut self.acc
    }
}

impl<'a> Visitor<'a> for BaseVisitor<'_> {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a; fun_, method_, class_var);

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Res {
        self.on_expr(env, expr)
    }

    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Res {
        match expr_ {
            aast::Expr_::Call(call) => self.on_call(env, call),
            aast::Expr_::EnumClassLabel(x) => {
                let (res, acc) = reduce::result(self, |v| expr_.recurse(env, v));
                res?;
                let r = match &x.0 {
                    Some(id) => {
                        let ty = class_id_ty(env, id);
                        let res = self.select_pos(&id.0, env, &ty);
                        self.plus(res, acc)
                    }
                    None => acc,
                };
                reduce::add(self, r);
                Ok(())
            }
            _ => reduce::on_expr_(self, env, expr_),
        }
    }

    fn visit_fun_param(&mut self, env: &mut Env, fp: &'a tast::FunParam) -> Res {
        let res = self.select_pos(&fp.pos, env, &fp.annotation);
        reduce::add(self, res);
        fp.recurse(env, self)
    }

    fn visit_capture_lid(&mut self, env: &mut Env, cl: &'a aast::CaptureLid<tast::Ty>) -> Res {
        let aast::CaptureLid(ty, aast::Lid(pos, _)) = cl;
        let res = self.select_pos(pos, env, ty);
        reduce::add(self, res);
        cl.recurse(env, self)
    }

    fn visit_xhp_simple(&mut self, env: &mut Env, attribute: &'a aast::XhpSimple<tast::Ty, tast::SavedEnv>) -> Res {
        let pos = &attribute.name.0;
        let res = self.select_pos(pos, env, &attribute.type_);
        reduce::add(self, res);
        attribute.recurse(env, self)
    }

    fn visit_class_id(&mut self, env: &mut Env, cid: &'a aast::ClassId<tast::Ty, tast::SavedEnv>) -> Res {
        match cid {
            // Don't use the resolved class type (the expr_annotation on the class_id
            // type) when hovering over a CIexpr--we will want to show the type the
            // expression is annotated with (e.g., classname<C>) and it will not have a
            // smaller position.
            aast::ClassId(_, _, aast::ClassId_::CIexpr(e)) => self.visit_expr(env, e),
            aast::ClassId(ty, pos, _) => {
                let res = self.select_pos(pos, env, ty);
                reduce::add(self, res);
                cid.recurse(env, self)
            }
        }
    }

    fn visit_class_const(&mut self, env: &mut Env, cc: &'a tast::ClassConst) -> Res {
        let (res, acc) = reduce::result(self, |v| cc.recurse(env, v));
        res?;
        let pos = &cc.id.0;
        let r = match class_const_ty(env, cc) {
            Some(ty) => {
                let res = self.select_pos(pos, env, &ty);
                self.plus(res, acc)
            }
            None => acc,
        };
        reduce::add(self, r);
        Ok(())
    }

    fn visit_stmt_(&mut self, env: &mut Env, s: &'a aast::Stmt_<tast::Ty, tast::SavedEnv>) -> Res {
        match s {
            aast::Stmt_::If(x) => {
                let (cond, then_block, _else_block) = &**x;
                match identify_symbol_service::resugar_invariant_call(env, cond, then_block) {
                    Some(e) => self.visit_owned(env, |v, env| v.visit_expr(env, &e)),
                    None => s.recurse(env, self),
                }
            }
            _ => s.recurse(env, self),
        }
    }

    fn visit_expression_tree(&mut self, env: &mut Env, et: &'a tast_visitor::ExpressionTree) -> Res {
        // If the answer is in a splice, just use the result from the splice,
        // since the contents of a splice are just plain hack and don't need
        // special treatment. If it isn't, use the virtualized expression to
        // get the client type focussed view of the expression tree.
        let (res, splice_results) = reduce::result(self, |v| {
            for s in aast_utils::get_splices_from_et(et) {
                v.visit_stmt(env, s)?;
            }
            Ok(())
        });
        res?;
        let (res, virtual_results) = reduce::result(self, |v| match aast_utils::get_virtual_expr_from_et(et) {
            Some(e) => v.visit_expr(env, e),
            None => v.visit_expr(env, &et.runtime_expr),
        });
        res?;
        let r = splice_results
            .into_iter()
            .zip(virtual_results)
            .map(|(a, b)| a.or(b))
            .collect();
        reduce::add(self, r);
        Ok(())
    }
}

/// `range_visitor cursors`
///
/// Return the type of the node associated with exactly the given range.
///
/// When more than one node has the given range, return the type of the first
/// node visited in a preorder traversal.
struct RangeVisitor<'c> {
    cursors: &'c [(position::T, position::T)],
    acc: Vec<Option<T>>,
}

/// `Pos.exactly_matches_range`
fn exactly_matches_range(p: &Pos, start_line: isize, start_col: isize, end_line: isize, end_col: isize) -> bool {
    let (p_start_line, p_start_col) = pos::line_column(p);
    let (p_end_line, p_end_col) = pos::end_line_column(p);
    p_start_line == start_line
        && p_start_col == start_col - 1
        && p_end_line == end_line
        && p_end_col == end_col - 1
}

impl RangeVisitor<'_> {
    fn select_pos(&self, pos: &Pos, env: &Env, ty: &tast::Ty) -> Vec<Option<T>> {
        self.cursors
            .iter()
            .map(|(start, end_)| {
                let (startl, startc) = position::line_column_one_based(start);
                let (endl, endc) = position::line_column_one_based(end_);
                if exactly_matches_range(pos, startl, startc, endl, endc) {
                    Some(mk_info(env, ty))
                } else {
                    None
                }
            })
            .collect()
    }
}

impl<'a> Reduce<'a> for RangeVisitor<'_> {
    type Acc = Vec<Option<T>>;

    fn zero(&self) -> Self::Acc {
        self.cursors.iter().map(|_| None).collect()
    }

    fn plus(&self, lhss: Self::Acc, rhss: Self::Acc) -> Self::Acc {
        assert_eq!(lhss.len(), rhss.len(), "List.map2_exn");
        // `Option.merge ~f:(fun x _ -> x)`
        lhss.into_iter().zip(rhss).map(|(a, b)| a.or(b)).collect()
    }

    fn acc(&mut self) -> &mut Self::Acc {
        &mut self.acc
    }
}

impl<'a> Visitor<'a> for RangeVisitor<'_> {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a);

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Res {
        let res = self.select_pos(&expr.1, env, &expr.0);
        reduce::add(self, res);
        expr.recurse(env, self)
    }

    fn visit_fun_param(&mut self, env: &mut Env, fp: &'a tast::FunParam) -> Res {
        let res = self.select_pos(&fp.pos, env, &fp.annotation);
        reduce::add(self, res);
        fp.recurse(env, self)
    }

    fn visit_class_id(&mut self, env: &mut Env, cid: &'a aast::ClassId<tast::Ty, tast::SavedEnv>) -> Res {
        let res = self.select_pos(&cid.1, env, &cid.0);
        reduce::add(self, res);
        cid.recurse(env, self)
    }
}

pub fn type_at_pos_fused(
    ctx: &provider_context::T,
    tast: &tast_with_dynamic::T<tast::Program>,
    cursors: &[position::T],
) -> Vec<Option<T>> {
    let mut v = BaseVisitor::new(false, false, cursors);
    reduce::go(&mut v, ctx, &tast.under_normal_assumptions)
        .into_iter()
        .map(|r| r.map(|(_, info)| info))
        .collect()
}

pub fn type_at_pos(
    ctx: &provider_context::T,
    tast: &tast_with_dynamic::T<tast::Program>,
    cursor: &position::T,
) -> Option<T> {
    let mut res = type_at_pos_fused(ctx, tast, std::slice::from_ref(cursor));
    if res.len() == 1 { res.pop().unwrap() } else { None }
}

/// Return the expanded type of smallest expression at this
/// position. Skips string literals in shape indexing expressions so
/// hover results are more relevant.
///
/// If [under_dynamic] is true, look for type produced
///   when env.checked = CUnderDynamicAssumptions
/// Otherwise, look for type produced in normal checking
///   when env.checked = COnce or env.checked = CUnderNormalAssumptions.
pub fn human_friendly_type_at_pos(
    under_dynamic: bool,
    ctx: &provider_context::T,
    tast: &tast_with_dynamic::T<tast::Program>,
    pos: &position::T,
) -> Option<T> {
    let empty = tast::Program::default();
    let tast = if under_dynamic {
        tast.under_dynamic_assumptions.as_ref().unwrap_or(&empty)
    } else {
        &tast.under_normal_assumptions
    };
    let mut v = BaseVisitor::new(true, under_dynamic, std::slice::from_ref(pos));
    let mut res = reduce::go(&mut v, ctx, tast);
    match (res.len(), res.pop()) {
        (1, Some(Some((_, info)))) => Some(info),
        _ => None,
    }
}

pub fn type_at_range_fused(
    ctx: &provider_context::T,
    tast: &tast_with_dynamic::T<tast::Program>,
    cursors: &[(position::T, position::T)],
) -> Vec<Option<T>> {
    let mut v = RangeVisitor {
        cursors,
        acc: cursors.iter().map(|_| None).collect(),
    };
    reduce::go(&mut v, ctx, &tast.under_normal_assumptions)
}

pub fn go_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    cursor: &position::T,
) -> Option<(String, String)> {
    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    let info = type_at_pos(ctx, &tast, cursor)?;
    let env = get_env(&info);
    let ty = get_type(&info);
    Some((
        tast_env::print_ty(env, ty),
        crate::yojson::safe::to_string(&tast_env::ty_to_json(env, None, ty)),
    ))
}
