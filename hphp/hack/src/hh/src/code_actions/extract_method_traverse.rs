// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/extract_method/extract_method_traverse.ml`.
//! See `hh/PORTING.md`.
//!
//! The visitors are [`aast_reduce::Reducer`]s: the regions are accumulated
//! in the order of the OCaml traversal.

use std::collections::BTreeSet;
use std::rc::Rc;
use std::sync::Arc;

use oxidized::aast;

use super::aast_reduce;
use super::aast_reduce::Reducer;
use super::aast_reduce::SNode;
use super::code_action_types::type_string;
use super::extract_method_types as t;
use crate::pos::Pos;
use crate::provider_context;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor::IterParams;

fn calc_placeholder_name(taken_names: &BTreeSet<String>, n: isize) -> String {
    let placeholder = format!("method{}", n);
    if taken_names.contains(&placeholder) {
        calc_placeholder_name(taken_names, n + 1)
    } else {
        placeholder
    }
}

/// tracks what variables are defined
mod scopes {
    use std::collections::BTreeSet;

    /// The head of the OCaml list is the last element.
    pub type T = Vec<BTreeSet<String>>;

    pub fn empty() -> T {
        vec![]
    }

    pub fn enter(mut t: T) -> T {
        t.push(BTreeSet::new());
        t
    }

    pub fn exit(mut t: T) -> T {
        match t.pop() {
            Some(_) => t,
            None => empty(),
        }
    }

    pub fn set_defined(mut t: T, var_name: &str) -> T {
        match t.last_mut() {
            Some(hd) => {
                hd.insert(var_name.to_string());
            }
            None => t.push(BTreeSet::from([var_name.to_string()])),
        }
        t
    }

    pub fn is_defined(t: &T, var_name: &str) -> bool {
        t.iter().any(|vars| vars.contains(var_name))
    }
}

/// We have 3 regions:
/// - pre-selection
/// - selection
/// - post-selection
///
/// [`region::T`] tracks sundry information we collect from a region
mod region {
    use super::scopes;
    use super::t;

    pub struct T {
        /// variables referenced from the region, along with their types
        pub referenced: t::VarTys,
        /// what variables are defined in the region
        pub defined: scopes::T,
        pub iterator_kind: Option<t::IteratorKind>,
        pub is_async: bool,
        /// When a region contains a `return`, that effects whether/how we can extract a method.
        /// As of this writing, we do not provide the refactor if the region containing the selection has a `return`.
        pub has_return: bool,
    }

    pub fn empty() -> T {
        T {
            referenced: t::VarTys::new(),
            defined: scopes::empty(),
            iterator_kind: None,
            is_async: false,
            has_return: false,
        }
    }

    pub fn free(region: &T) -> t::VarTys {
        region
            .referenced
            .iter()
            .filter(|(key, _)| !scopes::is_defined(&region.defined, key))
            .map(|(key, data)| (key.clone(), data.clone()))
            .collect()
    }

    pub fn used_from(defined_in: &T, referenced_from: &T) -> t::VarTys {
        free(referenced_from)
            .into_iter()
            .filter(|(key, _)| scopes::is_defined(&defined_in.defined, key))
            .collect()
    }
}

type Acc = Option<t::Candidate>;

/// `Map.merge_skewed a b ~combine:(fun ~key:_ v1 _v2 -> v1)`
fn merge_skewed_use_first(a: t::VarTys, mut b: t::VarTys) -> t::VarTys {
    b.extend(a);
    b
}

fn plus_candidate(a: Acc, b: Acc) -> Acc {
    match (a, b) {
        (Some(a), Some(b)) => {
            Some(t::Candidate {
                // For these fields, just take [b]'s value, since [a] and [b]
                // are always the same anyway
                method_pos: b.method_pos,
                method_is_static: b.method_is_static,
                placeholder_name: b.placeholder_name,
                selection_kind: b.selection_kind,
                // We grow `pos` to fill the selection
                // and learn more about whether to make an async or static function, etc.
                pos: crate::pos::merge(&a.pos, &b.pos),
                is_async: a.is_async || b.is_async,
                // Note:  if `(a, b)` is `(Some it_kind_a, Some it_kind_b)` then it doesn't matter whether
                // we use a or b assuming the user was consistent in yielding values or yielding key=>value pairs.
                // If the user is inconsistent then hopefully they don't mind we go with `b`.
                iterator_kind: b.iterator_kind.or(a.iterator_kind),
                // `params` are calculated based on variables that are defined in the
                // pre-selection region and used in the selection region.
                // If the same variable has two different types then something weird is happening. Just use b's type.
                params: merge_skewed_use_first(a.params, b.params),
                // `return` is calculated based on variables that are defined in the
                // selection region and used in the post-selection region.
                // If the same variable has two different types, then something weird is happening. Just use b's type.
                return_: merge_skewed_use_first(a.return_, b.return_),
            })
        }
        (a, b) => a.or(b),
    }
}

#[derive(Clone, Copy)]
enum CurrentRegion {
    PreSelection,
    Selection,
    PostSelection,
}

struct PositionsVisitor<'s> {
    selection: &'s Pos,
    method_pos: Pos,
    method_is_static: bool,
    // These fields are used to accumulate context top->down left->right
    /// The region before the user's selection. This is important for finding
    /// the types of variables that are free in the selection, which is used in calculating
    /// the parameter types for the extracted method.
    pre_selection_region: region::T,
    /// The selection region is used for finding which variables
    /// are free in the selection, which is used in calculating parameters for the extracted method.
    /// The selection region is also used for finding the types
    /// of variables that are used in the post-selection region, which is used for calculating
    /// the return of the extracted method.
    selection_region: region::T,
    /// See [selection region]
    post_selection_region: region::T,
    /// positions that overlap the selection, used for ensuring that a selection is valid.
    /// See [ensure_selection_common_root]
    expr_positions_overlapping_selection: Vec<Pos>,
    /// Count of statements in the selection. Used to calculate [selection_kind]
    stmts_in_selection_count: isize,
    /// Whether we are currently in an lvalue. This affects whether a variable is being used or defined.
    in_lvalue: bool,
    placeholder_name: String,
}

fn positions_visitor<'s>(
    selection: &'s Pos,
    method_pos: Pos,
    method_is_static: bool,
    method_names: &BTreeSet<String>,
) -> PositionsVisitor<'s> {
    PositionsVisitor {
        selection,
        method_pos,
        method_is_static,
        pre_selection_region: region::empty(),
        selection_region: region::empty(),
        post_selection_region: region::empty(),
        expr_positions_overlapping_selection: vec![],
        stmts_in_selection_count: 0,
        in_lvalue: false,
        placeholder_name: calc_placeholder_name(method_names, 0),
    }
}

impl PositionsVisitor<'_> {
    fn with_in_lvalue<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let orig_in_lvalue = self.in_lvalue;
        self.in_lvalue = true;
        let res = f(self);
        self.in_lvalue = orig_in_lvalue;
        res
    }

    /// filter out invalid selection like this:
    ///       (1 + 2) +  3
    ///           ^-----^ selection
    /// and this:
    ///       $x = 1 + 2; $y = 3;
    ///       ^--------------^ selection
    ///
    /// We do not offer refactorings for invalid selections.
    fn ensure_selection_common_root(&self, c: Acc) -> Acc {
        c.filter(|candidate| {
            self.expr_positions_overlapping_selection
                .iter()
                .all(|p| crate::pos::contains(&candidate.pos, p) || crate::pos::contains(p, &candidate.pos))
        })
    }

    fn current_region_kind(&self, pos: &Pos) -> CurrentRegion {
        if crate::pos::start_offset(self.selection) > crate::pos::start_offset(pos) {
            CurrentRegion::PreSelection
        } else if crate::pos::contains(self.selection, pos) {
            CurrentRegion::Selection
        } else {
            CurrentRegion::PostSelection
        }
    }

    fn region(&mut self, kind: CurrentRegion) -> &mut region::T {
        match kind {
            CurrentRegion::PreSelection => &mut self.pre_selection_region,
            CurrentRegion::Selection => &mut self.selection_region,
            CurrentRegion::PostSelection => &mut self.post_selection_region,
        }
    }

    fn current_region(&mut self, pos: &Pos) -> &mut region::T {
        let kind = self.current_region_kind(pos);
        self.region(kind)
    }

    fn make(&mut self, acc: Acc, pos: &Pos, ty_string: Rc<type_string::T>) -> Acc {
        if !self.in_lvalue && crate::pos::contains(self.selection, pos) {
            if self.selection_region.has_return {
                None
            } else {
                let params = region::free(&self.selection_region);
                let return_ = t::VarTys::new(); // adjusted after the selection
                let selection_kind = if self.stmts_in_selection_count == 0 {
                    t::SelectionKind::SelectionKindExpression(ty_string)
                } else {
                    t::SelectionKind::SelectionKindStatement
                };
                plus_candidate(
                    acc,
                    Some(t::Candidate {
                        pos: pos.clone(),
                        method_pos: self.method_pos.clone(),
                        method_is_static: self.method_is_static,
                        placeholder_name: self.placeholder_name.clone(),
                        selection_kind,
                        params,
                        return_,
                        is_async: self.selection_region.is_async,
                        iterator_kind: self.selection_region.iterator_kind,
                    }),
                )
            }
        } else {
            acc
        }
    }
}

impl<'a> Reducer<'a, IterParams, Acc> for PositionsVisitor<'_> {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Acc> {
        self
    }
    fn zero(&mut self) -> Acc {
        None
    }
    fn plus(&mut self, a: Acc, b: Acc) -> Acc {
        plus_candidate(a, b)
    }
    aast_reduce::tast::tast_methods!('a, Acc; expr_, class_var, expression_tree);

    fn visit_method_(&mut self, env: &mut Env, meth: &'a tast::Method_) -> Acc {
        let r = aast_reduce::tast::on_method_(self, env, meth);
        let r = self.ensure_selection_common_root(r);
        r.map(|acc| t::Candidate {
            return_: region::used_from(&self.selection_region, &self.post_selection_region),
            ..acc
        })
    }

    fn visit_as_expr(&mut self, env: &mut Env, as_expr: &'a aast::AsExpr<tast::Ty, tast::SavedEnv>) -> Acc {
        self.with_in_lvalue(|this| as_expr.srecurse(env, this))
    }

    fn visit_stmt(&mut self, env: &mut Env, stmt: &'a tast::Stmt) -> Acc {
        let aast::Stmt(pos, stmt_) = stmt;
        if crate::pos::contains(self.selection, pos) {
            self.stmts_in_selection_count += 1
        }
        let region = self.current_region(pos);
        match stmt_ {
            aast::Stmt_::Awaitall(x) => {
                let (tmp_var_block_pairs, _) = &**x;
                for (aast::Lid(_, tmp_lid), _) in tmp_var_block_pairs {
                    let name = crate::local_id::get_name(tmp_lid);
                    region.defined = scopes::set_defined(std::mem::take(&mut region.defined), name);
                }
            }
            aast::Stmt_::Foreach(x) => {
                let (_, as_, _) = &**x;
                let (iterator_kind, is_async) = match as_ {
                    aast::AsExpr::AsV(_) => (Some(t::IteratorKind::Iterator), false),
                    aast::AsExpr::AwaitAsV(..) => (Some(t::IteratorKind::KeyedIterator), true),
                    aast::AsExpr::AsKv(..) => (Some(t::IteratorKind::KeyedIterator), false),
                    aast::AsExpr::AwaitAsKv(..) => (Some(t::IteratorKind::KeyedIterator), true),
                };
                region.iterator_kind = iterator_kind;
                region.is_async = is_async;
            }
            aast::Stmt_::Return(_) => region.has_return = true,
            _ => {}
        }
        let acc = stmt.srecurse(env, self);
        let ty = crate::typing_make_type::void(crate::typing_reason::none());
        let ty_string = Rc::new(type_string::of_locl_ty(env, ty));
        self.make(acc, pos, ty_string)
    }

    fn visit_fun_(&mut self, env: &mut Env, fun_: &'a tast::Fun_) -> Acc {
        let region = self.current_region(&fun_.span);
        for param in &fun_.params {
            region.defined = scopes::set_defined(std::mem::take(&mut region.defined), &param.name);
        }
        aast_reduce::tast::on_fun_(self, env, fun_)
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Acc {
        let aast::Expr(ty, pos, expr_) = expr;
        let ty_string = Rc::new(type_string::of_locl_ty(env, ty.clone()));
        if crate::pos::overlaps(self.selection, pos) {
            self.expr_positions_overlapping_selection.push(pos.clone());
        }
        let region_kind = self.current_region_kind(pos);
        // mutates the regions
        let lfun_or_efun = match expr_ {
            aast::Expr_::Lfun(x) => Some(&x.0),
            aast::Expr_::Efun(x) => Some(&x.fun),
            _ => None,
        };
        let acc = match (lfun_or_efun, expr_) {
            (Some(fun_), _) => {
                {
                    let region = self.region(region_kind);
                    region.defined = scopes::enter(std::mem::take(&mut region.defined));
                }
                let acc = match fun_.body.fb_ast.0.as_slice() {
                    [aast::Stmt(_, aast::Stmt_::Return(e))] if e.is_some() => {
                        // `() ==> 3 + 3` has a `return` in the tast, which we remove because "extract method" isn't
                        // safe for return statements in general. But it's fine to offer the refactor this case: we can extract the `3 + 3`.
                        let e: &'a tast::Expr = (**e).as_ref().unwrap();
                        e.srecurse(env, self)
                    }
                    _ => aast_reduce::tast::on_expr_(self, env, expr_),
                };
                {
                    let region = self.region(region_kind);
                    region.defined = scopes::exit(std::mem::take(&mut region.defined));
                }
                acc
            }
            (None, aast::Expr_::Assign(x)) => {
                let (lhs, _, rhs) = &**x;
                let rhs = self.visit_expr(env, rhs);
                let lhs = self.with_in_lvalue(|this| this.visit_expr(env, lhs));
                self.plus(rhs, lhs)
            }
            (None, aast::Expr_::Lvar(x)) if self.in_lvalue => {
                let aast::Lid(_, lid) = &**x;
                let _: Acc = expr.srecurse(env, self);
                let region = self.region(region_kind);
                region.defined =
                    scopes::set_defined(std::mem::take(&mut region.defined), crate::local_id::get_name(lid));
                None
            }
            (None, aast::Expr_::Lvar(x)) => {
                let aast::Lid(_, lid) = &**x;
                let name = crate::local_id::get_name(lid);
                let region = self.region(region_kind);
                if !scopes::is_defined(&region.defined, name) {
                    region.referenced.insert(name.to_string(), ty_string.clone());
                }
                expr.srecurse(env, self)
            }
            (None, aast::Expr_::Yield(af)) => {
                let iterator_kind = match &**af {
                    aast::Afield::AFvalue(_) => Some(t::IteratorKind::Iterator),
                    aast::Afield::AFkvalue(..) => Some(t::IteratorKind::KeyedIterator),
                };
                self.region(region_kind).iterator_kind = iterator_kind;
                expr.srecurse(env, self)
            }
            (None, aast::Expr_::Await(_)) => {
                self.region(region_kind).is_async = true;
                expr.srecurse(env, self)
            }
            (None, _) => expr.srecurse(env, self),
        };
        self.make(acc, pos, ty_string)
    }
}

/// - Avoid traversing methods outside the selection
/// - Pass information [positions_visitor] needs
struct TopVisitor<'s> {
    selection: &'s Pos,
}

impl<'a> Reducer<'a, IterParams, Acc> for TopVisitor<'_> {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Acc> {
        self
    }
    fn zero(&mut self) -> Acc {
        None
    }
    fn plus(&mut self, a: Acc, b: Acc) -> Acc {
        a.or(b)
    }
    aast_reduce::tast::tast_methods!('a, Acc; expr_, fun_, method_, class_var, expression_tree);

    fn visit_def(&mut self, env: &mut Env, def: &'a tast::Def) -> Acc {
        match def {
            aast::Def::Class(class_) if crate::pos::contains(&class_.span, self.selection) => {
                self.visit_class_(env, class_)
            }
            _ => None,
        }
    }

    fn visit_class_(&mut self, env: &mut Env, class_: &'a tast::Class_) -> Acc {
        let methods = &class_.methods;
        let method_names: BTreeSet<String> = methods.iter().map(|m| m.name.1.clone()).collect();
        methods
            .iter()
            .find(|m| crate::pos::contains(&m.span, self.selection))
            .and_then(|meth| {
                let mut visitor = positions_visitor(self.selection, meth.span.clone(), meth.static_, &method_names);
                visitor.visit_method_(env, meth)
            })
    }
}

pub fn find_candidate(
    selection: &Pos,
    entry: &Arc<provider_context::Entry>,
    ctx: &provider_context::T,
) -> Option<t::Candidate> {
    let tast_provider::ComputeTast { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    let mut v = TopVisitor { selection };
    aast_reduce::tast::go(&mut v, ctx, &tast.under_normal_assumptions)
}
