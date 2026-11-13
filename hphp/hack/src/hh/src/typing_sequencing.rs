// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_sequencing.ml`. See `hh/PORTING.md`.
//!
//! Pass to check for unsequenced modifications to local variables.
//!
//! PHP has a somewhat weird evaluation order (technically unspecified,
//! but...) that can cause us trouble. Evaluation is *usually*
//! left-to-right except that for certain operators, if the left hand side
//! is a variable, it is right-to-left.
//!
//! If we didn't handle this in some way, the typechecker would be unsound,
//! since code like '$x + f($x = array())' typechecks if you assume
//! left-to-right evaluation but will fail at runtime.
//!
//! We deal with this by outlawing unsequenced modification and access
//! to local variables. We consider certain operations to be "sequencing";
//! (that is, they sequence their subexpressions)
//! two expressions are unsequenced if their least common
//! ancestor in the syntax tree is *not* sequencing.
//!
//! Basically everything is sequencing except:
//!   all binops except && and ||, array/object accesses,
//!   array field specifiers, list(...),
//!   assignment (sort of; '$x = $x+1' is OK, '$x = $x++' is not)
//! (The first three correspond to when eval order can get reversed;
//!  the others just correspond to bad code.)
//!
//! This all solves the unsoundness problem without needing to commit the
//! typechecker to exactly understanding the evaluation order and also
//! closes off most of the ways a strict Hack program can observe unusual
//! evaluation order (side-effectful __toString methods can observe it;
//! maybe other ways also).
//!
//! The OCaml objects inheriting `Nast.Visitor_DEPRECATED.visitor` are
//! structs implementing [`Visitor`]; `parent#on_expr` is the default method,
//! `visitor_deprecated::on_expr`. The lists of `env` are `Vec`s with the
//! head of the OCaml list first.

use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Uop;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::pos::Pos;

use crate::diagnostics_state;
use crate::local_id;
use crate::nast::visitor_deprecated;
use crate::nast::visitor_deprecated::Visitor;

/// `Diagnostics.add_diagnostic (Nast_check_error.to_user_diagnostic err)`
fn add_nast_check_error(err: NastCheckError) {
    if let Some(diagnostic) = crate::naming_errors::to_diagnostic(NamingPhaseError::NastCheck(err))
    {
        diagnostics_state::add_diagnostic(diagnostic)
    }
}

#[derive(Clone, Debug)]
struct Env {
    /// tracking will be set when we are under an unsequenced operation
    /// that requires us to be tracking variable accesses
    tracking: bool,
    /// We should maybe use a better data structure than lists.
    used: Vec<aast::Lid>,
    assigned: Vec<aast::Lid>,
}

fn empty_env() -> Env {
    Env {
        tracking: false,
        used: vec![],
        assigned: vec![],
    }
}

fn tracking_env() -> Env {
    Env {
        tracking: true,
        ..empty_env()
    }
}

/// `px :: map`
fn add_id(map: Vec<aast::Lid>, px: &aast::Lid) -> Vec<aast::Lid> {
    let mut map = map;
    map.insert(0, px.clone());
    map
}

fn assign_local(env: Env, id: &aast::Lid) -> Env {
    if env.tracking {
        Env {
            assigned: add_id(env.assigned, id),
            ..env
        }
    } else {
        env
    }
}

fn use_local(env: Env, id: &aast::Lid) -> Env {
    if env.tracking {
        Env {
            used: add_id(env.used, id),
            ..env
        }
    } else {
        env
    }
}

/// Traverse down through list(...) destructuring to find all
/// the "atomic" lvals that are being assigned to.
fn unpack_lvals(e: &nast::Expr) -> Vec<&nast::Expr> {
    fn unpack<'a>(acc: &mut Vec<&'a nast::Expr>, e: &'a nast::Expr) {
        match e {
            aast::Expr(_, _, aast::Expr_::List(es)) => {
                for e in es {
                    unpack(acc, e)
                }
            }
            e => acc.push(e),
        }
    }
    // `List.rev (unpack [] e)`: `unpack` conses the leaves as it finds them,
    // so the result is in the order in which they are found.
    let mut acc = vec![];
    unpack(&mut acc, e);
    acc
}

/// `First id` or `Second e`.
enum Either<'a> {
    First(&'a aast::Lid),
    Second(&'a nast::Expr),
}

fn get_lvar(e: &nast::Expr) -> Either<'_> {
    match e {
        aast::Expr(_, _, aast::Expr_::Lvar(id)) => Either::First(id),
        e => Either::Second(e),
    }
}

/// `List.partition_map l ~f:get_lvar`
fn partition_lvars<'a>(l: Vec<&'a nast::Expr>) -> (Vec<&'a aast::Lid>, Vec<&'a nast::Expr>) {
    let mut firsts = vec![];
    let mut seconds = vec![];
    for e in l {
        match get_lvar(e) {
            Either::First(id) => firsts.push(id),
            Either::Second(e) => seconds.push(e),
        }
    }
    (firsts, seconds)
}

/// Pass that just collects all the variables used (and not just written to)
/// in fragments of code.
/// We need this because a common idiom is to assign to unused variables
/// as a form of documentation, and we want to ignore those variables
/// when doing our sequencing checks.
struct UsedVariablesVisitor;

impl Visitor<local_id::set::T> for UsedVariablesVisitor {
    fn on_lvar(&mut self, acc: local_id::set::T, id: &aast::Lid) -> local_id::set::T {
        let aast::Lid(_, id) = id;
        let mut acc = acc;
        acc.insert(id.clone());
        acc
    }

    /// We have to handle expressions just enough to avoid counting
    /// assignments as uses of variables.
    /// (We do still count operator-assignments)
    fn on_expr(&mut self, acc: local_id::set::T, e: &nast::Expr) -> local_id::set::T {
        let aast::Expr(_, _, e_) = e;
        match e_ {
            aast::Expr_::Assign(a) if a.1.is_none() => {
                let (e1, _, e2) = &**a;
                let (_, not_vars) = partition_lvars(unpack_lvals(e1));
                let mut acc = acc;
                for e in not_vars {
                    acc = self.on_expr(acc, e);
                }
                self.on_expr(acc, e2)
            }
            _ => visitor_deprecated::on_expr(self, acc, e),
        }
    }
}

fn used_variables_visitor() -> UsedVariablesVisitor {
    UsedVariablesVisitor
}

/// Merge a separately checked environment into the current one
fn merge(env: Env, new_env: Env) -> Env {
    if env.tracking {
        let mut used = new_env.used;
        used.extend(env.used);
        let mut assigned = new_env.assigned;
        assigned.extend(env.assigned);
        Env {
            used,
            assigned,
            tracking: true,
        }
    } else {
        empty_env()
    }
}

/// Actual sequence checking pass
///
/// `sequence_visitor ~require_used used_vars`: the helpers that the OCaml
/// declares before the object are methods of the struct, which holds the
/// two arguments.
///
/// `used_vars` (the variables `used_variables_visitor` finds in the block)
/// is only read to filter conflicting writes, which are rare: it is computed
/// the first time it is needed (the visitor that computes it only reads the
/// block).
struct SequenceVisitor<'b> {
    require_used: bool,
    used_vars: std::cell::OnceCell<local_id::set::T>,
    /// The block whose variables `used_vars` are (`None`: no block, an
    /// empty set).
    used_vars_of: Option<&'b nast::Block>,
}

fn sequence_visitor(require_used: bool, used_vars_of: Option<&nast::Block>) -> SequenceVisitor<'_> {
    SequenceVisitor {
        require_used,
        used_vars: std::cell::OnceCell::new(),
        used_vars_of,
    }
}

impl SequenceVisitor<'_> {
    fn used_vars(&self) -> &local_id::set::T {
        self.used_vars.get_or_init(|| match self.used_vars_of {
            Some(block) => used_variables_visitor().on_block(local_id::set::T::new(), &block.0),
            None => local_id::set::T::new(),
        })
    }

    /// Check the used/assigned sets from two unsequenced expressions and report
    /// errors if they conflict.
    /// N.B that the sets are only checked for conflicts against the other
    /// environment and not for other accesses in itself. There may well be
    /// multiple writes to the same location in one env; these will either
    /// have been properly sequenced or an error would already have been reported.
    fn check_unsequenced(&self, env1: &Env, env2: &Env) {
        let id_matches = |aast::Lid(_p1, x1): &aast::Lid, aast::Lid(_p2, x2): &aast::Lid| {
            local_id::equal(x1, x2)
        };
        // (`reads` and `writes` are the lists of the environments, read
        // backwards: see `rev` below.)
        let check_write_conflicts = |reads: &[aast::Lid], writes: &[aast::Lid], id: &aast::Lid| {
            let aast::Lid(p, _) = id;
            let conflicting_reads: Vec<&aast::Lid> =
                reads.iter().rev().filter(|x| id_matches(id, x)).collect();
            let conflicting_writes: Vec<&aast::Lid> =
                writes.iter().rev().filter(|x| id_matches(id, x)).collect();
            // Ignore conflicts when writing to variables that are never read
            // in order to support the idiom where pointless variable
            // assignments are used as documentation.
            let conflicting_writes: Vec<&aast::Lid> = if !self.require_used {
                conflicting_writes
            } else {
                conflicting_writes
                    .into_iter()
                    .filter(|aast::Lid(_, x)| self.used_vars().contains(x))
                    .collect()
            };
            let cleanup = |l: Vec<&aast::Lid>| -> Vec<Pos> {
                l.into_iter().map(|aast::Lid(p, _)| p.clone()).collect()
            };
            if !conflicting_reads.is_empty() {
                add_nast_check_error(NastCheckError::LocalVariableModifiedAndUsed {
                    pos: p.clone(),
                    pos_useds: cleanup(conflicting_reads),
                });
            }
            if !conflicting_writes.is_empty() {
                add_nast_check_error(NastCheckError::LocalVariableModifiedTwice {
                    pos: p.clone(),
                    pos_modifieds: cleanup(conflicting_writes),
                });
            }
        };
        // reversing the lists makes things sorted more naturally in the output
        // (`List.rev`: the lists are read backwards instead of copied.)
        let (reads1, writes1) = (&env1.used, &env1.assigned);
        let (reads2, writes2) = (&env2.used, &env2.assigned);
        for id in writes1.iter().rev() {
            check_write_conflicts(reads2, writes2, id)
        }

        // Only check writes2 for conflicts with the reads from env1,
        // since we've already checked for write/write conflicts.
        for id in writes2.iter().rev() {
            check_write_conflicts(reads1, &[], id)
        }
    }

    fn merge_unsequenced(&self, env: Env, env1: Env, env2: Env) -> Env {
        self.check_unsequenced(&env1, &env2);
        let env = merge(env, env1);
        merge(env, env2)
    }

    fn merge_unsequenced_list(&self, envs: Vec<Env>) -> Env {
        let mut env1 = tracking_env();
        for env2 in envs {
            self.check_unsequenced(&env1, &env2);
            env1 = merge(env1, env2);
        }
        env1
    }

    fn check_unsequenced_exprs(&mut self, env: Env, e1: &nast::Expr, e2: &nast::Expr) -> Env {
        let env1 = self.on_expr(tracking_env(), e1);
        let env2 = self.on_expr(tracking_env(), e2);
        self.merge_unsequenced(env, env1, env2)
    }
}

impl Visitor<Env> for SequenceVisitor<'_> {
    fn on_expr(&mut self, env: Env, e: &nast::Expr) -> Env {
        let aast::Expr(_, _, e_) = e;
        match e_ {
            aast::Expr_::Lvar(id) => use_local(env, id),
            aast::Expr_::Unop(u) => match &**u {
                (
                    Uop::Uincr | Uop::Udecr | Uop::Upincr | Uop::Updecr,
                    aast::Expr(_, _, aast::Expr_::Lvar(id)),
                ) => assign_local(env, id),
                _ => visitor_deprecated::on_expr(self, env, e),
            },
            // Assignment. This is pretty hairy because of list(...)
            // destructuring and the treatment necessary to allow
            // code like '$x = $x + 1'.
            aast::Expr_::Assign(a) => {
                let (e1, _, e2) = &**a;
                // Unpack any list(...) destructuring and separate out locals
                // we are assigning to from other lvals.
                let (lvars, lval_exprs) = partition_lvars(unpack_lvals(e1));
                // Build separate envs for the direct variable assignments and
                // for the other lvals assigned to. We treat all these lvals
                // as unsequenced.
                let lvar_envs: Vec<Env> = lvars
                    .into_iter()
                    .map(|id| assign_local(tracking_env(), id))
                    .collect();
                let lhs_var_env = self.merge_unsequenced_list(lvar_envs);
                let lval_expr_envs: Vec<Env> = lval_exprs
                    .into_iter()
                    .map(|e| self.on_expr(tracking_env(), e))
                    .collect();
                let lval_expr_env = self.merge_unsequenced_list(lval_expr_envs);
                let rhs_env = self.on_expr(tracking_env(), e2);
                // Our lhs local var writes only conflict with other *writes* on
                // the rhs, not with reads (need to allow '$x = $x + 1' but
                // disallow '$x = $x++'), so we do a check_unsequenced against
                // a version of env2 containing only the writes and then merge
                // with the real thing.
                let rhs_writes = Env {
                    assigned: rhs_env.assigned.clone(),
                    ..empty_env()
                };
                self.check_unsequenced(&lhs_var_env, &rhs_writes);

                // Also check local assignments against the other lvalues
                self.check_unsequenced(&lhs_var_env, &lval_expr_env);

                // We've manually handled everything relating to the lhs locals,
                // so merge them into the env and then do a regular unsequenced
                // merge of the non local lhs stuff against the rhs.
                let env = merge(env, lhs_var_env);
                self.merge_unsequenced(env, lval_expr_env, rhs_env)
            }
            // leave && and || sequenced before making all
            // the other binops unsequenced
            aast::Expr_::Binop(b)
                if matches!(b.bop, Bop::Ampamp | Bop::Barbar | Bop::QuestionQuestion) =>
            {
                visitor_deprecated::on_expr(self, env, e)
            }
            // These operations have unsequenced subexpressions.
            aast::Expr_::Binop(b) => {
                let aast::Binop {
                    lhs: e1, rhs: e2, ..
                } = &**b;
                self.check_unsequenced_exprs(env, e1, e2)
            }
            aast::Expr_::ObjGet(og) => {
                let (e1, e2, _, _) = &**og;
                self.check_unsequenced_exprs(env, e1, e2)
            }
            aast::Expr_::ArrayGet(ag) => match &**ag {
                (e1, Some(e2)) => self.check_unsequenced_exprs(env, e1, e2),
                _ => visitor_deprecated::on_expr(self, env, e),
            },
            aast::Expr_::Efun(_) | aast::Expr_::Lfun(_) => {
                // `Efun { ef_fun = f; ef_use = idl; _ } | Lfun (f, idl)`
                let (f, idl): (&nast::Fun_, &[nast::CaptureLid]) = match e_ {
                    aast::Expr_::Efun(ef) => (&ef.fun, &ef.use_),
                    aast::Expr_::Lfun(lf) => (&lf.0, &lf.1),
                    _ => unreachable!(),
                };
                let nb = &f.body;
                // Ignore the current environment and start fresh.
                let _acc = self.on_block(empty_env(), &nb.fb_ast.0);
                // we use all the variables we are capturing
                let mut acc = env;
                for aast::CaptureLid(_, id) in idl {
                    acc = use_local(acc, id);
                }
                acc
            }
            _ => visitor_deprecated::on_expr(self, env, e),
        }
    }

    fn on_field(&mut self, env: Env, f: &nast::Field) -> Env {
        let aast::Field(e1, e2) = f;
        self.check_unsequenced_exprs(env, e1, e2)
    }

    fn on_afield(&mut self, env: Env, af: &nast::Afield) -> Env {
        match af {
            aast::Afield::AFvalue(e) => self.on_expr(env, e),
            aast::Afield::AFkvalue(e1, e2) => self.check_unsequenced_exprs(env, e1, e2),
        }
    }

    /// Handle case to disallow assigning to vars inside case labels.
    fn on_case(&mut self, acc: Env, c: &nast::Case) -> Env {
        let aast::Case(e, b) = c;
        let env = self.on_expr(tracking_env(), e);
        for aast::Lid(p, _) in env.assigned.iter() {
            add_nast_check_error(NastCheckError::AssignDuringCase(p.clone()));
        }
        self.on_block(acc, &b.0)
    }
}

pub fn sequence_check_block(block: &nast::Block) {
    // (`used_vars` is `used_variables_visitor#on_block SSet.empty block`,
    // made when needed.)
    let mut visitor = sequence_visitor(true, Some(block));
    let _ = visitor.on_block(empty_env(), &block.0);
}

pub fn sequence_check_expr(expr: &nast::Expr) {
    let mut visitor = sequence_visitor(false, None);
    let _ = visitor.on_expr(empty_env(), expr);
}
