// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_alias.ml`. See `hh/PORTING.md`.
//!
//! Module determining how long the longest "aliasing chain" of a given
//! block is.
//!
//! The problem:
//!   The type-inference algorithm needs to find a fix point when dealing with
//!   loops.
//!
//! Normally, a fix-point should be reached after 2 iterations. However,
//! there are pathological cases where this is not true.
//! It happens when the code is aliasing locals, because the type of locals
//! can change, a 'chain' of aliases can delay the moment where we reach a
//! fix point.
//!
//! Example:
//! ```text
//!   // $x is an int
//!   $x = $y;
//!   $y = $z;
//!   $z = 'hello';
//!   // $x will only become an int after 3 iterations.
//! ```
//!
//! The OCaml objects inheriting `Nast.Visitor_DEPRECATED.visitor` are
//! structs implementing [`Visitor`]; `parent#on_expr` is the default method,
//! `visitor_deprecated::on_expr`. A `string list` of the maps is a `Vec`
//! with the head of the OCaml list first.

use oxidized::aast;
use oxidized::local_id::LocalId;
use oxidized::nast;

use crate::local_id;
use crate::nast::visitor_deprecated;
use crate::nast::visitor_deprecated::Visitor;
use crate::s_map;
/// `module Fake = Typing_fake_members`
use crate::typing_fake_members as fake;

/// Module computing all the aliased locals.
///
/// if one writes '$y = $z', then the binding $y => $z is added to the map.
/// Note that object/class members are counted are counted as locals
/// (conservatively), because in some cases, they can behave like locals (cf
/// Typing_fake_members).
mod dep {
    use super::*;

    pub fn add(x1: &str, x2: &LocalId, acc: s_map::T<Vec<String>>) -> s_map::T<Vec<String>> {
        let x2 = local_id::to_string(x2);
        let mut prev = acc.get(x1).cloned().unwrap_or_default();
        prev.insert(0, x2);
        let mut acc = acc;
        acc.insert(x1.to_string(), prev);
        acc
    }

    pub fn get(key: &str, acc: &s_map::T<Vec<String>>) -> Vec<String> {
        match acc.get(key) {
            None => vec![],
            Some(kl) => kl.clone(),
        }
    }

    /// `visitor local`
    pub struct DepVisitor<'a> {
        local: &'a str,
    }

    pub fn visitor(local: &str) -> DepVisitor<'_> {
        DepVisitor { local }
    }

    impl Visitor<s_map::T<Vec<String>>> for DepVisitor<'_> {
        fn on_expr(&mut self, acc: s_map::T<Vec<String>>, e: &nast::Expr) -> s_map::T<Vec<String>> {
            let aast::Expr(_, _, e_) = e;
            match e_ {
                aast::Expr_::Lvar(lid) => add(self.local, &lid.1, acc),
                aast::Expr_::ObjGet(og) => match &**og {
                    (
                        x @ aast::Expr(_, _, aast::Expr_::This | aast::Expr_::Lvar(_)),
                        aast::Expr(_, _, aast::Expr_::Id(y)),
                        _,
                        _,
                    ) => add(self.local, &fake::make_id(x, &y.1), acc),
                    _ => visitor_deprecated::on_expr(self, acc, e),
                },
                aast::Expr_::ClassGet(cg) => {
                    let (aast::ClassId(_, _, x), (_, y), _) = &**cg;
                    add(self.local, &fake::make_static_id(x, y), acc)
                }
                _ => visitor_deprecated::on_expr(self, acc, e),
            }
        }
    }

    pub fn expr(
        local: &str,
        acc: s_map::T<Vec<String>>,
        e: &nast::Expr,
    ) -> s_map::T<Vec<String>> {
        visitor(local).on_expr(acc, e)
    }
}

mod alias_map {
    use super::*;

    pub type T = s_map::T<Vec<String>>;

    pub fn get(key: &str, acc: &T) -> Vec<String> {
        dep::get(key, acc)
    }

    fn local_to_string(e_: &nast::Expr_) -> Option<String> {
        match e_ {
            aast::Expr_::Lvar(lid) => Some(local_id::to_string(&lid.1)),
            aast::Expr_::ObjGet(og) => match &**og {
                (
                    x @ aast::Expr(_, _, aast::Expr_::This | aast::Expr_::Lvar(_)),
                    aast::Expr(_, _, aast::Expr_::Id(y)),
                    _,
                    _,
                ) => Some(local_id::to_string(&fake::make_id(x, &y.1))),
                _ => None,
            },
            aast::Expr_::ClassGet(cg) => {
                let (aast::ClassId(_, _, x), (_, y), _) = &**cg;
                Some(local_id::to_string(&fake::make_static_id(x, y)))
            }
            _ => None,
        }
    }

    /// `visitor`
    struct AliasVisitor;

    impl AliasVisitor {
        fn on_assign_(&mut self, acc: T, e1: &nast::Expr, e2: &nast::Expr) -> T {
            let aast::Expr(_, _, e1) = e1;
            match local_to_string(e1) {
                Some(s) => dep::expr(&s, acc, e2),
                None => acc,
            }
        }
    }

    impl Visitor<T> for AliasVisitor {
        fn on_expr(&mut self, acc: T, e: &nast::Expr) -> T {
            let aast::Expr(_, _, e_) = e;
            match e_ {
                aast::Expr_::Assign(a) => match &**a {
                    (aast::Expr(_, p, aast::Expr_::List(el)), _, x2) => {
                        let mut acc = acc;
                        for e in el {
                            acc = self.on_expr(
                                acc,
                                &aast::Expr(
                                    (),
                                    p.clone(),
                                    aast::Expr_::Assign(Box::new((e.clone(), None, x2.clone()))),
                                ),
                            );
                        }
                        acc
                    }
                    (lhs, _, rhs) => self.on_assign_(acc, lhs, rhs),
                },
                _ => visitor_deprecated::on_expr(self, acc, e),
            }
        }

        fn on_efun(&mut self, acc: T, _ef: &nast::Efun) -> T {
            acc
        }

        fn on_lfun(&mut self, acc: T, _f: &nast::Fun_, _idl: &[nast::CaptureLid]) -> T {
            acc
        }
    }

    pub fn make(st: &nast::Stmt) -> T {
        AliasVisitor.on_stmt(s_map::T::new(), st)
    }
}

/// Given an alias map, returns the length of the longest possible
/// 'aliasing chain'.
///
/// Example:
/// ```text
///   $x = $y;
///   $y = $z;
///   $z = 'hello';
/// ```
///
/// RESULT=3 because of the chain $x => $y => $z
mod depth {
    use super::*;

    /// `fold` returns `(visited, current_max)`; the map is threaded through
    /// `key`.
    fn fold(aliases: &alias_map::T) -> (s_map::T<isize>, isize) {
        let mut visited: s_map::T<isize> = s_map::T::new();
        let mut current_max = 0;
        for (k, _) in aliases.iter() {
            let n = key(aliases, &mut visited, k);
            current_max = std::cmp::max(n, current_max);
        }
        (visited, current_max)
    }

    fn key(aliases: &alias_map::T, visited: &mut s_map::T<isize>, k: &str) -> isize {
        if let Some(depth) = visited.get(k) {
            *depth
        } else {
            visited.insert(k.to_string(), 0);
            let kl = alias_map::get(k, aliases);
            let depth_l: Vec<isize> = kl.iter().map(|k| key(aliases, visited, k)).collect();
            let my_depth = 1 + depth_l.iter().fold(0, |acc, d| std::cmp::max(acc, *d));
            visited.insert(k.to_string(), my_depth);
            my_depth
        }
    }

    pub fn get(aliases: &alias_map::T) -> isize {
        fold(aliases).1
    }
}

// Entry point.

pub fn get_depth(st: &nast::Stmt) -> isize {
    let aliases = alias_map::make(st);
    let result = depth::get(&aliases);
    // Needs to be at least 2 because of back edges.
    std::cmp::max(2, result)
}

#[cfg(test)]
mod tests {
    use oxidized::pos::Pos;

    use super::*;

    fn lvar(name: &str) -> nast::Expr {
        aast::Expr(
            (),
            Pos::NONE,
            aast::Expr_::Lvar(Box::new(aast::Lid(
                Pos::NONE,
                local_id::make_unscoped(name),
            ))),
        )
    }

    fn assign(lhs: nast::Expr, rhs: nast::Expr) -> nast::Stmt {
        aast::Stmt(
            Pos::NONE,
            aast::Stmt_::Expr(Box::new(aast::Expr(
                (),
                Pos::NONE,
                aast::Expr_::Assign(Box::new((lhs, None, rhs))),
            ))),
        )
    }

    fn block(stmts: Vec<nast::Stmt>) -> nast::Stmt {
        aast::Stmt(
            Pos::NONE,
            aast::Stmt_::Block(Box::new((None, aast::Block(stmts)))),
        )
    }

    #[test]
    fn chain_of_three() {
        let st = block(vec![
            assign(lvar("$x"), lvar("$y")),
            assign(lvar("$y"), lvar("$z")),
            assign(
                lvar("$z"),
                aast::Expr((), Pos::NONE, aast::Expr_::Int("1".to_string())),
            ),
        ]);
        assert_eq!(get_depth(&st), 3);
        // One more link in the chain.
        let st = block(vec![
            assign(lvar("$x"), lvar("$y")),
            assign(lvar("$y"), lvar("$z")),
            assign(lvar("$z"), lvar("$w")),
        ]);
        assert_eq!(get_depth(&st), 4);
    }

    #[test]
    fn at_least_two() {
        let st = block(vec![assign(lvar("$x"), lvar("$y"))]);
        assert_eq!(get_depth(&st), 2);
    }

    #[test]
    fn cycles_terminate() {
        let st = block(vec![
            assign(lvar("$x"), lvar("$y")),
            assign(lvar("$y"), lvar("$x")),
        ]);
        assert_eq!(get_depth(&st), 2);
    }
}
