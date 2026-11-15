// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_error.ml`. See `hh/PORTING.md`.
//!
//! This module is the *data* of typing errors; `crate::typing_error_utils`
//! turns it into diagnostics.
//!
//! # Layout
//!
//! | OCaml | Rust |
//! |---|---|
//! | `Typing_error.t` (= `Error.t`) | [`T`] (also `error::T`) |
//! | `Typing_error.Primary.t` | [`primary::T`] |
//! | `Typing_error.Primary.Shape.t`, `.Enum.t`, ... | `primary::shape::T`, `primary::enum_::T`, ... |
//! | `Typing_error.Secondary.t` | [`secondary::T`] |
//! | `Typing_error.Callback.t` | [`callback::T`] |
//! | `Typing_error.Reasons_callback.t` | [`reasons_callback::T`] |
//! | `Typing_error.Error_code` (`= Error_codes.Typing`) | [`error_code`] |
//!
//! # Conventions
//!
//! - Every constructor is the UpperCamelCase of its OCaml name
//!   (`Unify_error` is `UnifyError`); every inline record field keeps its
//!   OCaml name. The hand-written `Debug` implementations (`error::T`,
//!   `callback::T`, `reasons_callback::T`) print the OCaml spellings
//!   (`With_code`), as `[@@deriving show]` does. Constructors with an
//!   inline record are struct-like variants, constructors with tuple
//!   arguments are tuple variants with the arguments in the same order.
//! - Names that are Rust keywords get a trailing underscore: the modules
//!   `primary::enum_` and `primary::enum_::const_` (also reachable as
//!   `r#enum` and `r#const`), the function `enum_` (also `r#enum`), and the
//!   fields `fn_` (`IllegalTypeStructure`) and `const_`
//!   (`enum_::const_::T::Label`).
//! - `Primary.CaseType` and `Primary.SimpliHack` are `primary::case_type` and
//!   `primary::simpli_hack` (the functions are `casetype` and `simplihack`).
//! - `'a Lazy.t` is [`Lazy<T>`].
//! - `Pos.t Message.t` is `oxidized::message::Message<Pos>`, whose text is a
//!   `bstr::BString` (as `Message.t` is declared); plain `string` fields are
//!   `String`; `int` is `isize`.
//! - The four mutually recursive types (`Error.t`, `Secondary.t`,
//!   `Callback.t`, `Reasons_callback.t`) are boxed exactly where a
//!   constructor mentions *its own* type, and where `Secondary.t` or
//!   `Reasons_callback.t` mention `Error.t` (`secondary::T::OfError`,
//!   `reasons_callback::T::{Always, OfError}`). Everything else is inline;
//!   lists are `Vec<T>`.
//! - Values of type `Callback.t` (`Callback.unify_error`, ...) are functions
//!   without arguments (`callback::unify_error()`).
//!
//! # Polymorphic variants
//!
//! OCaml gives the type of a field such as ``ctxt: [ `read | `write ]`` no
//! name. Here:
//!
//! - The tags are the variants of an enum, in UpperCamelCase:
//!   `` `read `` is `Read`, `` `method_ `` is `Method`, `` `static `` is
//!   `Static`, `` `Nothing `` is `Nothing`; `` `Self `` is `Self_` (`Self`
//!   is a Rust keyword).
//! - Fields with the same set of tags have the same type, as in OCaml. Such
//!   a type can have several names, which are aliases of one enum, all in
//!   the module of the type the constructor belongs to (`primary`,
//!   `primary::shape`, `primary::readonly`, `secondary`):
//!   - for field `some_field` of constructor `Some_constructor`, always
//!     `SomeConstructorSomeField`: `primary::NullMemberCtxt`,
//!     `primary::readonly::ReadonlyMismatchWhat`,
//!     `secondary::ReadonlyMismatchKind`. (When the polymorphic variant is
//!     inside a tuple, as for `hint` and `cstr`, this names the polymorphic
//!     variant alone.)
//!   - for a set of two tags, also `<Tag1>Or<Tag2>`: `primary::ReadOrWrite`,
//!     `primary::MethodOrProperty`, `primary::InstanceOrStatic`,
//!     `primary::MethOrProp`, `primary::IsOrAs`, `primary::CoOrContra`,
//!     `primary::ConstantOrParam`, `primary::PropertyOrMethod`,
//!     `primary::NonStringOrEmbeddedExpr`, `primary::VoidOrNoreturn`,
//!     `primary::StaticOrClassname`, `primary::ClassOrThisAs`,
//!     `primary::shape::NothingOrUndefined`, `secondary::AsOrSuper`. The
//!     ones that several constructors use are defined in this module and
//!     re-exported from `primary` and `secondary`.
//!   - the short names `primary::ClassMemberKind` (`SmemberNotFoundKind`),
//!     `primary::AbstractMemberKind`
//!     (`AbstractMemberInConcreteClassMemberKind`),
//!     `primary::SealedParentKind` (`ExtendSealedParentKind`),
//!     `primary::ReqConstraintKind`, `primary::shape::Reason`,
//!     `primary::readonly::What`, `primary::readonly::Kind` and
//!     `secondary::RefinementConstraintKind`
//!     (`ViolatedRefinementConstraintCstr`), which `typing_error_utils`
//!     uses.

use std::cell::Cell;
use std::cell::OnceCell;
use std::fmt;
use std::rc::Rc;

use oxidized::message::Message;
use oxidized::pos_or_decl::PosOrDecl;

pub mod callback;
pub mod error;
pub mod primary;
pub mod reasons_callback;
pub mod secondary;

// `include Error`
pub use error::*;

/// `module Error_code = Error_codes.Typing`
pub mod error_code {
    pub use oxidized::error_codes::Typing as T;
}

// -- Lazy values --------------------------------------------------------------

/// `'a Lazy.t`: a value computed at most once, the first time it is forced.
///
/// Typing errors carry the expensive parts of their messages (printed types,
/// reasons) lazily, because most errors built during subtyping are discarded
/// without being reported.
///
/// - `lazy e` is `Lazy::new(move || e)`; `Lazy.from_val v` is
///   `Lazy::from_val(v)` (or `v.into()`).
/// - `Lazy.force l` is `l.force()`, which gives a reference to the value.
/// - Cloning is cheap and shares the suspension, as copying an OCaml lazy
///   value does: forcing one clone forces all of them.
///
/// A `Lazy` is neither `Send` nor `Sync`: like the OCaml value it stays on the
/// thread that checks the file, and the suspended computation may capture
/// anything that lives there.
pub struct Lazy<T>(Rc<LazyInner<T>>);

struct LazyInner<T> {
    value: OnceCell<T>,
    thunk: Cell<Option<Box<dyn FnOnce() -> T>>>,
}

impl<T> Lazy<T> {
    /// `lazy (f ())`
    pub fn new(f: impl FnOnce() -> T + 'static) -> Self {
        Lazy(Rc::new(LazyInner {
            value: OnceCell::new(),
            thunk: Cell::new(Some(Box::new(f))),
        }))
    }

    /// `Lazy.from_val`
    pub fn from_val(v: T) -> Self {
        Lazy(Rc::new(LazyInner {
            value: OnceCell::from(v),
            thunk: Cell::new(None),
        }))
    }

    /// `Lazy.force`
    pub fn force(&self) -> &T {
        self.0.value.get_or_init(|| {
            let thunk = self
                .0
                .thunk
                .take()
                // OCaml raises `CamlinternalLazy.Undefined` in the first case
                // and the suspension's own exception again in the second.
                .expect("Lazy.force: forced recursively, or forced again after its computation panicked");
            thunk()
        })
    }

    /// `Lazy.is_val`
    pub fn is_val(&self) -> bool {
        self.0.value.get().is_some()
    }

    /// `Lazy.map`: the result is itself lazy and forces `self` when forced.
    pub fn map<U>(&self, f: impl FnOnce(&T) -> U + 'static) -> Lazy<U>
    where
        T: 'static,
    {
        let this = self.clone();
        Lazy::new(move || f(this.force()))
    }

    /// `Lazy.bind`
    pub fn bind<U: Clone>(&self, f: impl FnOnce(&T) -> Lazy<U> + 'static) -> Lazy<U>
    where
        T: 'static,
    {
        let this = self.clone();
        Lazy::new(move || f(this.force()).force().clone())
    }
}

impl<T> Clone for Lazy<T> {
    fn clone(&self) -> Self {
        Lazy(Rc::clone(&self.0))
    }
}

impl<T> From<T> for Lazy<T> {
    fn from(v: T) -> Self {
        Lazy::from_val(v)
    }
}

/// As `[@@deriving show]` does for `Lazy.t`: the value if it has been forced,
/// `<not evaluated>` otherwise. Printing never forces.
impl<T: fmt::Debug> fmt::Debug for Lazy<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.value.get() {
            Some(v) => v.fmt(f),
            None => f.write_str("<not evaluated>"),
        }
    }
}

// -- Polymorphic variants used by several constructors ------------------------

/// ``[ `read | `write ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReadOrWrite {
    Read,
    Write,
}

/// ``[ `method_ | `property ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MethodOrProperty {
    Method,
    Property,
}

/// ``[ `instance | `static ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstanceOrStatic {
    Instance,
    /// `` `static ``
    Static,
}

/// ``[ `meth | `prop ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MethOrProp {
    Meth,
    Prop,
}

/// ``[ `Nothing of Pos_or_decl.t Message.t list Lazy.t | `Undefined ]``
#[derive(Clone, Debug)]
pub enum NothingOrUndefined {
    Nothing(Lazy<Vec<Message<PosOrDecl>>>),
    Undefined,
}

// -- Printing -----------------------------------------------------------------

/// `Typing_error.show`. (`Typing_error.pp` is the `Debug` implementation.)
///
/// This is `Debug` output, for logs: it has the same content as what
/// `[@@deriving show]` prints, not the same layout.
pub fn show(t: &T) -> String {
    format!("{:?}", t)
}

#[cfg(test)]
mod tests;
