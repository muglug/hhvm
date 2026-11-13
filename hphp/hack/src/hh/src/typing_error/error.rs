// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Typing_error.Error`, which `typing_error.ml` includes at its top level:
//! everything here is re-exported from `crate::typing_error`.

use std::rc::Rc;

use oxidized::error_codes::Typing;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::Ctx;

use super::callback;
// The module `primary`, as opposed to the function `primary` below.
use super::primary as prim;
use super::reasons_callback;
use super::secondary;

/// In OCaml a value of this type is a pointer to an immutable block, so
/// copying one is free; the payloads here are behind an `Rc` for the same
/// reason (the errors that subtyping would report are built, copied and
/// moved around for every subtype check, and most of them are dropped).
#[derive(Clone)]
pub enum T {
    Primary(Rc<prim::T>),
    Apply(Rc<callback::T>, Rc<T>),
    Apply_reasons(reasons_callback::T, Rc<secondary::T>),
    Assert_in_current_decl(Rc<secondary::T>, Rc<Ctx>),
    Multiple(Vec<T>),
    Union(Vec<T>),
    Intersection(Vec<T>),
    With_code(Rc<T>, Typing),
    With_pos(Rc<T>, Pos),
    /// Not in OCaml: an error that is not built yet, and stands for the one
    /// [`Deferred::force`] gives (built once, the first time it is needed).
    /// Subtyping makes millions of errors and almost all are dropped unseen
    /// (in OCaml each is a few small blocks; here several allocations): the
    /// error of a failing step is made this way, from immutable values only
    /// (see `typing_subtype::prelude::subtype_env::Fail`), so building it
    /// later gives the same error. Whatever inspects the structure of an
    /// error looks through this node ([`forced`]); printing it with `Debug`
    /// prints the error it stands for.
    Deferred(Rc<dyn Deferred>),
}

/// The computation behind [`T::Deferred`]: `force` gives the same value
/// every time (computed at most once).
pub trait Deferred {
    fn force(&self) -> &T;
}

/// The error itself, through any [`T::Deferred`] nodes at its root (which it
/// builds).
pub fn forced(t: &T) -> &T {
    match t {
        T::Deferred(d) => forced(d.force()),
        t => t,
    }
}

/// As `#[derive(Debug)]` (what OCaml's `[@@deriving show]` prints), with a
/// [`T::Deferred`] node printed as the error it stands for.
impl std::fmt::Debug for T {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            T::Primary(a) => f.debug_tuple("Primary").field(a).finish(),
            T::Apply(a, b) => f.debug_tuple("Apply").field(a).field(b).finish(),
            T::Apply_reasons(a, b) => f.debug_tuple("Apply_reasons").field(a).field(b).finish(),
            T::Assert_in_current_decl(a, b) => f
                .debug_tuple("Assert_in_current_decl")
                .field(a)
                .field(b)
                .finish(),
            T::Multiple(a) => f.debug_tuple("Multiple").field(a).finish(),
            T::Union(a) => f.debug_tuple("Union").field(a).finish(),
            T::Intersection(a) => f.debug_tuple("Intersection").field(a).finish(),
            T::With_code(a, b) => f.debug_tuple("With_code").field(a).field(b).finish(),
            T::With_pos(a, b) => f.debug_tuple("With_pos").field(a).field(b).finish(),
            T::Deferred(d) => d.force().fmt(f),
        }
    }
}

// -- Constructors -------------------------------------------------------------

/// Lift a `Primary.t` error to a `Typing_error.t`
pub fn primary(prim_err: prim::T) -> T {
    T::Primary(Rc::new(prim_err))
}

/// Lift a `Primary.Coeffect.t` error to a `Typing_error.t`
pub fn coeffect(err: prim::coeffect::T) -> T {
    primary(prim::T::Coeffect(err))
}

/// Lift a `Primary.Enum.t` error to a `Typing_error.t`
pub fn enum_(err: prim::enum_::T) -> T {
    primary(prim::T::Enum(err))
}

pub use self::enum_ as r#enum;

/// Lift a `Primary.Expr_tree.t` error to a `Typing_error.t`
pub fn expr_tree(err: prim::expr_tree::T) -> T {
    primary(prim::T::Expr_tree(err))
}

/// Lift a `Primary.Modules.t` error to a `Typing_error.t`
pub fn modules(err: prim::modules::T) -> T {
    primary(prim::T::Modules(err))
}

/// Lift a `Primary.Package.t` error to a `Typing_error.t`
pub fn package(err: prim::package::T) -> T {
    primary(prim::T::Package(err))
}

/// Lift a `Primary.Readonly.t` error to a `Typing_error.t`
pub fn readonly(err: prim::readonly::T) -> T {
    primary(prim::T::Readonly(err))
}

/// Lift a `Primary.Shape.t` error to a `Typing_error.t`
pub fn shape(err: prim::shape::T) -> T {
    primary(prim::T::Shape(err))
}

/// Lift a `Primary.Switch.t` error to a `Typing_error.t`
pub fn switch(err: prim::switch::T) -> T {
    primary(prim::T::Switch(err))
}

/// Lift a `Primary.Wellformedness.t` error to a `Typing_error.t`
pub fn wellformedness(err: prim::wellformedness::T) -> T {
    primary(prim::T::Wellformedness(err))
}

/// Lift a `Primary.Xhp.t` error to a `Typing_error.t`
pub fn xhp(err: prim::xhp::T) -> T {
    primary(prim::T::Xhp(err))
}

/// Lift a `Primary.CaseType.t` error to a `Typing_error.t`
pub fn casetype(err: prim::casetype::T) -> T {
    primary(prim::T::CaseType(err))
}

/// Lift a `Primary.SimpliHack.t` error to a `Typing_error.t`
pub fn simplihack(err: prim::simplihack::T) -> T {
    primary(prim::T::SimpliHack(err))
}

/// Apply a the `Reasons_callback.t` to the supplied `Secondary.t` error, using
/// the reasons and error code associated with that error
pub fn apply_reasons(t: secondary::T, on_error: reasons_callback::T) -> T {
    T::Apply_reasons(on_error, Rc::new(t))
}

/// Apply a the `Callback.t` to the supplied `Secondary.t` error, using
/// the claim, reasons, quickfixes and error code associated with that error
pub fn apply(t: T, on_error: callback::T) -> T {
    T::Apply(Rc::new(on_error), Rc::new(t))
}

/// Lift a `Secondary.t` error to a `Typing_error.t` by asserting that the
/// position of the first reason is in the current decl and treating it as a
/// claim
pub fn assert_in_current_decl(snd: secondary::T, ctx: Ctx) -> T {
    T::Assert_in_current_decl(Rc::new(snd), Rc::new(ctx))
}

fn group_opt(f: impl Fn(Vec<T>) -> T, ts: Vec<T>) -> Option<T> {
    if ts.is_empty() { None } else { Some(f(ts)) }
}

/// Report a list of errors at each type of an intersection
pub fn intersect(mut ts: Vec<T>) -> T {
    match ts.len() {
        0 => panic!("called on empty list"),
        1 => ts.pop().unwrap(),
        _ => T::Intersection(ts),
    }
}

/// Calling `intersect_opt xs` returns `None` if the list is empty and
/// `intersect xs` otherwise
pub fn intersect_opt(ts: Vec<T>) -> Option<T> {
    group_opt(intersect, ts)
}

/// Report a list of errors at each type of a union
pub fn union(mut ts: Vec<T>) -> T {
    match ts.len() {
        0 => panic!("called on empty list"),
        1 => ts.pop().unwrap(),
        _ => T::Union(ts),
    }
}

/// Calling `union_opt xs` returns `None` if the list is empty and `union xs`
/// otherwise
pub fn union_opt(ts: Vec<T>) -> Option<T> {
    group_opt(union, ts)
}

/// Report multiple errors at a single type
pub fn multiple(mut ts: Vec<T>) -> T {
    match ts.len() {
        0 => panic!("called on empty list"),
        1 => ts.pop().unwrap(),
        _ => T::Multiple(ts),
    }
}

/// Calling `multiple_opt xs` returns `None` if the list is empty and
/// `multiple xs` otherwise
pub fn multiple_opt(ts: Vec<T>) -> Option<T> {
    group_opt(multiple, ts)
}

/// Report two errors at a single type; `both t1 t2` is the same as
/// `multiple [t1;t2]`
pub fn both(t1: T, t2: T) -> T {
    T::Multiple(vec![t1, t2])
}

/// Modify the code that will be reported when evaluated to a
/// `User_diagnostic.t`
pub fn with_code(t: T, code: Typing) -> T {
    T::With_code(Rc::new(t), code)
}

pub fn count(t: &T) -> isize {
    match t {
        T::Primary(_) | T::Apply_reasons(_, _) | T::Assert_in_current_decl(_, _) => 1,
        T::Apply(_, t) | T::With_code(t, _) | T::With_pos(t, _) => count(t),
        T::Multiple(ts) | T::Union(ts) | T::Intersection(ts) => {
            ts.iter().fold(0, |acc, t| acc + count(t))
        }
        T::Deferred(d) => count(d.force()),
    }
}
