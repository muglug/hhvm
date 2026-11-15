// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_find_locals.ml`. See `hh/PORTING.md`.
//!
//! Find references in the current file to the local variable at the given
//! position.
//!
//! Representation:
//!
//! - The OCaml threads a persistent `LocalMap.t` through the visitor; every
//!   old value is dropped as soon as the new one is made, so here one
//!   [`local_map::T`] is moved through the visitor and changed in place.
//! - A scope chain (`scope list`, head first) is a `Vec` whose head is its
//!   *last* element; so is the stack of scope chains.
//! - `Ident.make` is a global counter, as in OCaml (the numbers are never
//!   printed: only which positions share one matters).
//! - The `failwith`s of the scope chains are panics with the same message;
//!   [`go`] catches a panic whose payload is a message (`Failure error`) and
//!   raises the OCaml's longer message.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::atomic::AtomicIsize;
use std::sync::atomic::Ordering;

use oxidized::nast;
use oxidized::pos::Pos;

use crate::ast_provider;
use crate::file_content::position as fc_position;
use crate::local_id;
use crate::nast::visitor_deprecated;
use crate::nast::visitor_deprecated::Visitor;
use crate::pos;
use crate::provider_context;

/// `Ident.t`
type Ident = isize;

static IDENT_CTR: AtomicIsize = AtomicIsize::new(1);

/// `Ident.make`: a fresh identifier (the name is not kept).
fn ident_make(_name: &str) -> Ident {
    IDENT_CTR.fetch_add(1, Ordering::Relaxed) + 1
}

/// An element of `PosSet` (`Stdlib.Set.Make (Pos)`): ordered by `Pos.compare`.
#[derive(Clone, Debug)]
struct PosElt(Pos);

impl PartialEq for PosElt {
    fn eq(&self, other: &Self) -> bool {
        pos::compare(&self.0, &other.0) == std::cmp::Ordering::Equal
    }
}

impl Eq for PosElt {}

impl PartialOrd for PosElt {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PosElt {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        pos::compare(&self.0, &other.0)
    }
}

type PosSet = BTreeSet<PosElt>;

pub mod local_positions {
    //! Local positions is a map from an identifier -- a unique integer that
    //! identifies a local "symbol" -- to a set of all known positions where
    //! that local is used.
    //!
    //! Identifiers that identify no known local produce an empty set of
    //! positions.

    use super::*;

    pub(super) type T = BTreeMap<Ident, PosSet>;

    pub(super) fn empty() -> T {
        BTreeMap::new()
    }

    pub(super) fn get(ident: Ident, locals: &T) -> PosSet {
        locals.get(&ident).cloned().unwrap_or_default()
    }

    pub(super) fn add(ident: Ident, pos: &Pos, locals: &mut T) {
        locals
            .entry(ident)
            .or_default()
            .insert(PosElt(pos.clone()));
    }
}

pub mod scope_chain {
    //! A scope maps from a string (the text of the use of a local) to an
    //! ident (a unique integer associated with this local symbol).
    //!
    //! A scope chain is a stack of scopes. If there is a match at the head
    //! of the stack, that match shadows any matches in the tail. Otherwise,
    //! the tail is checked.

    use super::*;

    pub(super) type Scope = BTreeMap<String, Ident>;

    /// The head of the chain is the last element.
    pub(super) type T = Vec<Scope>;

    /// In correct code locals are always found inside a function, method or
    /// lambda, and so there is always a scope already pushed on the scope chain
    /// when the local is added. However, suppose we are in erroneous code, such
    /// that the parser has parsed a local expression that is not inside a
    /// function. In that case we might attempt to add a local to the current
    /// scope with an empty scope chain.
    ///
    /// Therefore we head every scope chain with a "dummy" scope that can be
    /// used for these error cases.
    pub(super) fn empty() -> T {
        vec![Scope::new()]
    }

    pub(super) fn push(scopechain: &mut T) {
        scopechain.push(Scope::new())
    }

    pub(super) fn pop(scopechain: &mut T) {
        match scopechain.pop() {
            Some(_) => {}
            None => panic!("popping empty scope chain"),
        }
    }

    pub(super) fn add(name: &str, ident: Ident, scopechain: &mut T) {
        match scopechain.last_mut() {
            Some(h) => {
                h.insert(name.to_string(), ident);
            }
            None => panic!("adding name to empty scope chain"),
        }
    }

    pub(super) fn get(name: &str, scopechain: &T) -> Option<Ident> {
        scopechain.iter().rev().find_map(|h| h.get(name).copied())
    }
}

pub mod scope_chains {
    //! A "scope chain" is a stack of maps from names to idents. You might
    //! think that would be sufficient, but unfortunately it is not.
    //!
    //! When we have a nested function (not a lambda), then the scope chain
    //! from outside the nested function is not accessible inside the nested
    //! function. Rather, a new scope chain is created which has on it the
    //! formal parameters and the variables inherited from the outer scope chain
    //! by the "use" clause. We therefore have a stack of scope chains.

    use super::*;

    /// The head of the stack is the last element.
    pub(super) type T = Vec<scope_chain::T>;

    pub(super) fn head(scopechains: &mut T) -> &mut scope_chain::T {
        match scopechains.last_mut() {
            Some(h) => h,
            None => panic!("Scope chain stack is empty"),
        }
    }

    pub(super) fn previous(scopechains: &T) -> &scope_chain::T {
        if scopechains.len() >= 2 {
            &scopechains[scopechains.len() - 2]
        } else {
            panic!("Scope chain stack is too small")
        }
    }

    pub(super) fn pop(scopechains: &mut T) {
        match scopechains.pop() {
            Some(_) => {}
            None => panic!("Scope chain stack is empty"),
        }
    }

    pub(super) fn push(scopechain: scope_chain::T, scopechains: &mut T) {
        scopechains.push(scopechain)
    }
}

pub mod local_map {
    //! A "local map" is a scope chain stack and a local positions map.
    //! When a usage of a local is encountered, there are several possibilities
    //! for what has to happen next.
    //!
    //! (1) The most common scenario is: we've seen this local before. We look
    //! it up in the current scope chain, get a hit, and move on.
    //!
    //! (2) If this is the first time we've seen this perfectly ordinary local
    //! then we make a new identifier and add it to the scope chain.
    //!
    //! (3) There are some situations where we know we must introduce a new ident
    //! even if the name is in scope. Those situations include: a local is
    //! introduced by a formal parameter, a local is introduced by a catch
    //! clause, a function static shadows an existing local.
    //!
    //! (4) Finally, we need to do a lot of work to correctly handle a nested
    //! anonymous function with a "use" clause. See below for the details.
    //!
    //! Regardless, we add the position to the local positions map.
    //!
    //! We have a particular target local in mind but we only know its position.
    //! When we encounter a local at that position, we'll make a note of the
    //! ident so that we can look up the associated positions later.

    use super::*;

    pub struct T {
        pub(super) scopechains: scope_chains::T,
        pub(super) locals: local_positions::T,
        pub(super) target_pos: fc_position::T,
        pub(super) target_ident: Option<Ident>,
    }

    pub fn make(target_pos: fc_position::T) -> T {
        T {
            scopechains: vec![scope_chain::empty()],
            locals: local_positions::empty(),
            target_pos,
            target_ident: None,
        }
    }

    fn current_scopechain(localmap: &mut T) -> &mut scope_chain::T {
        scope_chains::head(&mut localmap.scopechains)
    }

    pub(super) fn push(mut localmap: T) -> T {
        scope_chain::push(current_scopechain(&mut localmap));
        localmap
    }

    pub(super) fn pop(mut localmap: T) -> T {
        scope_chain::pop(current_scopechain(&mut localmap));
        localmap
    }

    pub(super) fn push_scopechain(mut localmap: T) -> T {
        scope_chains::push(scope_chain::empty(), &mut localmap.scopechains);
        localmap
    }

    pub(super) fn pop_scopechain(mut localmap: T) -> T {
        scope_chains::pop(&mut localmap.scopechains);
        localmap
    }

    fn overlaps(pos: &Pos, localmap: &T) -> bool {
        let (target_line, target_char) = fc_position::line_column_one_based(&localmap.target_pos);
        let (pos_line, pos_start, pos_end) = pos::info_pos(pos);
        // Pos.t uses zero-indexed offsets, whereas the IDE target char is one-indexed.
        let target_end_offset = target_char - 1;

        pos_line == target_line && pos_start <= target_char && target_end_offset <= pos_end
    }

    fn get_target_ident(ident: Ident, pos: &Pos, localmap: &T) -> Option<Ident> {
        if localmap.target_ident.is_none() && overlaps(pos, localmap) {
            Some(ident)
        } else {
            localmap.target_ident
        }
    }

    /// This version of add always overwrites the existing scope entry, even
    /// if there's a local of this name already in scope. We need this for:
    ///
    /// ```text
    /// function ($x) {
    ///   $y = $x;
    ///   static $x = 123;
    ///   $z = $x;
    /// }
    /// ```
    ///
    /// We have two variables both named $x, one formal and one static. The
    /// later comes into scope at the point of its declaration, and is in
    /// scope for the rest of the body. The easiest way to model this is to
    /// simply replace the existing scope entry, if there is one.
    pub(super) fn force_add(name: &str, pos: &Pos, mut localmap: T) -> T {
        let ident = ident_make(name);
        scope_chain::add(name, ident, current_scopechain(&mut localmap));
        local_positions::add(ident, pos, &mut localmap.locals);
        localmap.target_ident = get_target_ident(ident, pos, &localmap);
        localmap
    }

    /// When we encounter a |> operator, we need to push a scope on the right
    /// side and add a brand-new $$ to that scope, but we do not yet have a
    /// position for it!
    pub(super) fn add_dollardollar(mut localmap: T) -> T {
        let name = "$$";
        let ident = ident_make(name);
        scope_chain::add(name, ident, current_scopechain(&mut localmap));
        localmap
    }

    /// Returns an (ident, bool) where the bool is true if the ident was found.
    fn find_or_create_ident(name: &str, localmap: &mut T) -> (Ident, bool) {
        let current = current_scopechain(localmap);
        let result = scope_chain::get(name, current);
        match result {
            None => (ident_make(name), false),
            Some(ident) => (ident, true),
        }
    }

    /// This version of add only adds an entry to the current scope if we haven't
    /// got a binding for this name.
    pub(super) fn add(name: &str, pos: &Pos, mut localmap: T) -> T {
        let (ident, found) = find_or_create_ident(name, &mut localmap);
        if !found {
            scope_chain::add(name, ident, current_scopechain(&mut localmap));
        }
        local_positions::add(ident, pos, &mut localmap.locals);
        localmap.target_ident = get_target_ident(ident, pos, &localmap);
        localmap
    }

    pub(super) fn add_from_use(name: &str, pos: &Pos, mut localmap: T) -> T {
        // When adding an item from a use clause we've got to do a couple
        // things. First, the variables mentioned in the use clause are
        // mentions of those variables, so they need to go in the list of
        // positions. Second, the binding from the name to its id from the
        // _previous_ scopechain needs to be copied into the _current_
        // scopechain.
        let previous = scope_chains::previous(&localmap.scopechains);
        let canonical = scope_chain::get(name, previous);
        // The user may have given a variable in the use clause which does not
        // exist. In that case, just make up a new ident.
        let ident = match canonical {
            None => ident_make(name),
            Some(ident) => ident,
        };
        // Regardless, this is a mention of that local.
        local_positions::add(ident, pos, &mut localmap.locals);
        scope_chain::add(name, ident, current_scopechain(&mut localmap));
        localmap.target_ident = get_target_ident(ident, pos, &localmap);
        localmap
    }

    pub(super) fn results(localmap: &T) -> Vec<Pos> {
        let results_set = match localmap.target_ident {
            Some(ident) => local_positions::get(ident, &localmap.locals),
            _ => PosSet::new(),
        };
        results_set.into_iter().map(|PosElt(p)| p).collect()
    }
}

// Here begins the code which walks the AST and accumulates the positions
// of every local in this file.

/// `class local_finding_visitor`
struct LocalFindingVisitor;

impl LocalFindingVisitor {
    fn on_fun_param(&mut self, localmap: local_map::T, p: &nast::FunParam) -> local_map::T {
        // A formal parameter always introduces a new local into the current
        // scope; we never want to unify a formal with a local seen previously.
        local_map::force_add(&p.name, &p.pos, localmap)
    }
}

impl Visitor<local_map::T> for LocalFindingVisitor {
    fn on_lvar(&mut self, localmap: local_map::T, nast::Lid(pos, name): &visitor_deprecated::Id) -> local_map::T {
        if local_id::is_user_denotable(name) {
            local_map::add(local_id::get_name(name), pos, localmap)
        } else {
            localmap
        }
    }

    fn on_pipe(
        &mut self,
        localmap: local_map::T,
        _id: &visitor_deprecated::Id,
        left: &nast::Expr,
        right: &nast::Expr,
        _null_flavor: &nast::OperatorNullFlavor,
    ) -> local_map::T {
        // A pipe expression has a left side and a right side. It introduces a
        // new scope on the right side only which defines a new magic local
        // called $$, which is equal to the value of the left side.
        //
        // Consider for example:
        //
        // ( a |> b($$) ) |> ( c((d($$) |> e($$)), $$) )
        //     1    1     2         2   3    3     2
        //
        // Here I have numbered all the pipe operators and $$s, indicating which
        // $$ is in scope at each usage.
        //
        // TODO: ericlippert
        // TODO: What is the interaction between the pipe operator and nested
        // TODO: anonymous functions? Does the $$ automatically end up in scope
        // TODO: inside the body, or does it have to go in a use($$) clause?
        // TODO: If the former, then we'll need to explicitly copy the active $$
        // TODO: binding into the scope chain introduced; if the latter then
        // TODO: the existing mechanisms should be sufficient.  Either way,
        // TODO: this should be tested.
        let localmap = self.on_expr(localmap, left);
        let localmap = local_map::push(localmap);
        let localmap = local_map::add_dollardollar(localmap);
        let localmap = self.on_expr(localmap, right);
        local_map::pop(localmap)
    }

    fn on_method_(&mut self, localmap: local_map::T, m: &nast::Method_) -> local_map::T {
        let mut localmap = local_map::push(localmap);
        for p in &m.params {
            localmap = self.on_fun_param(localmap, p);
        }
        let localmap = self.on_block(localmap, &m.body.fb_ast);
        local_map::pop(localmap)
    }

    /// This is called for both top-level functions and lambdas, but not
    /// anonymous functions.
    fn on_fun_(&mut self, localmap: local_map::T, f: &nast::Fun_) -> local_map::T {
        let mut localmap = local_map::push(localmap);
        for p in &f.params {
            localmap = self.on_fun_param(localmap, p);
        }
        let localmap = self.on_block(localmap, &f.body.fb_ast);
        local_map::pop(localmap)
    }

    fn on_lfun(
        &mut self,
        localmap: local_map::T,
        f: &nast::Fun_,
        _idl: &[nast::CaptureLid],
    ) -> local_map::T {
        self.on_fun_(localmap, f)
    }

    fn on_efun(&mut self, localmap: local_map::T, efun: &nast::Efun) -> local_map::T {
        // This is a traditional PHP nested function, and this is a bit tricky.
        // Consider first a normal case:
        //
        // function test1($x, $y) {
        //   $f = function ($z) use($x) {
        //     $y = 100;
        //     return $x + $y + $z;
        //   };
        //   return $f(10);
        // }
        //
        // We must detect every use of $x as a use of the formal parameter,
        // including the usage inside the "use". We must *not* detect use of
        // $y as a use of the formal parameter $y, since it was not mentioned
        // in the use clause.
        //
        // Now consider a corner case:
        //
        // function test2() {
        //   $x = 20;
        //   $f = function ($x) use ($x) {
        //     return $x;
        //   };
        //   return $f(10);
        // }
        //
        // Which $x is returned by the nested function? We have both a formal
        // and a closed-over local to choose from. In this case the
        // formal wins.
        //
        // So we push a new scopechain so that the outer locals come out of
        // scope, then push *two* scopes, one for the using, and one for the
        // formals (`on_fun_` pushes the second). A lookup in the body goes to
        // the head of the current scope chain, then to the scope of the use
        // clause; the previous scope chain is never searched.
        let localmap = local_map::push_scopechain(localmap);
        let mut localmap = local_map::push(localmap);
        // No need to pop; we're going to pop the whole scopechain.
        for nast::CaptureLid(_, nast::Lid(p, n)) in &efun.use_ {
            localmap = local_map::add_from_use(local_id::get_name(n), p, localmap);
        }
        let localmap = self.on_fun_(localmap, &efun.fun);
        local_map::pop_scopechain(localmap)
    }

    fn on_catch(&mut self, localmap: local_map::T, c: &nast::Catch) -> local_map::T {
        let nast::Catch(_, nast::Lid(pos, name), body) = c;
        // A catch block creates a local which is only in scope for the
        // body of the catch.
        //
        // The type name should never reasonably contain a local; we'll ignore it.
        let localmap = local_map::push(localmap);
        let localmap = local_map::force_add(local_id::get_name(name), pos, localmap);
        let localmap = self.on_block(localmap, body);
        local_map::pop(localmap)
    }
}

/// Same as [`go`], but with an AST provided explicitly. Prefer [`go`] when
/// possible to make use of caching.
pub fn go_from_ast(ast: &nast::Program, pos: &fc_position::T) -> Vec<Pos> {
    let empty = local_map::make(*pos);
    let mut visitor = LocalFindingVisitor;
    let localmap = visitor.on_program(empty, &ast.0);
    local_map::results(&localmap)
}

/// This is the entrypoint to this module. The relative path of a file,
/// the contents of a file, and a position within it, identifying a local, are given.
/// The result is a list of the positions of other uses of that local in the file.
pub fn go(
    ctx: &provider_context::T,
    entry: &provider_context::Entry,
    pos: &fc_position::T,
) -> Vec<Pos> {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let ast = ast_provider::compute_ast(provider_context::get_popt(ctx), entry);
        let results_list = go_from_ast(&ast, pos);
        results_list
            .iter()
            .map(|pos| pos::set_file(entry.path.clone(), pos))
            .collect::<Vec<_>>()
    }));
    match result {
        Ok(r) => r,
        Err(payload) => {
            // `| Failure error ->`: a panic with a message.
            let error = match payload.downcast_ref::<String>() {
                Some(s) => s.clone(),
                None => match payload.downcast_ref::<&str>() {
                    Some(s) => s.to_string(),
                    None => std::panic::resume_unwind(payload),
                },
            };
            let contents = provider_context::read_file_contents_exn(entry);
            let (line, char) = fc_position::line_column_one_based(pos);
            panic!(
                "{}{}",
                format!("Find locals service failed with error {}:\n", error),
                format!(
                    "line {} char {}\ncontent: \n{}\n",
                    line,
                    char,
                    String::from_utf8_lossy(&contents)
                )
            )
        }
    }
}
