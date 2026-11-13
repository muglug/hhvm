// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Typing_error.Reasons_callback`

use std::fmt;
use std::rc::Rc;

use oxidized::error_codes::Typing;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::Ctx;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::quickfix::Quickfix;

use super::Lazy;
use super::callback;
use super::error;
use super::primary;
use super::secondary;

#[derive(Clone, Copy, Debug)]
pub enum Op {
    Append,
    Prepend,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Component {
    Code,
    Reasons,
    Quickfixes,
}

/// A mechanism to apply transformations to secondary errors
///
/// In OCaml a value of this type is a pointer to an immutable block, so
/// copying one is free; every payload here is behind an `Rc` for the same
/// reason (a callback is copied into every subtyping environment and every
/// error built from it).
#[derive(Clone)]
pub enum T {
    Always(Rc<error::T>),
    Of_error(Rc<error::T>),
    Prefix(Rc<primary::T>),
    Of_callback(Rc<callback::T>, Lazy<Message<Pos>>),
    Retain(Rc<T>, Component),
    Incoming_reasons(Rc<T>, Op),
    With_code(Rc<T>, Typing),
    With_claim(Rc<T>, Lazy<Message<Pos>>),
    With_reasons(Rc<T>, Lazy<Vec<Message<PosOrDecl>>>),
    Add_quickfixes(Rc<T>, Rc<Vec<Quickfix<Pos>>>),
    Add_reason(Rc<T>, Op, Lazy<Message<PosOrDecl>>),
    /// `From_on_error of (?code:int -> ?quickfixes:Pos.t Quickfix.t list ->
    /// Pos_or_decl.t Message.t list -> unit)`
    ///
    /// Deprecated in OCaml: "This constructor will be removed. Please use the
    /// provided combinators for constructing error callbacks."
    From_on_error(Rc<dyn Fn(Option<isize>, Option<Vec<Quickfix<Pos>>>, Vec<Message<PosOrDecl>>)>),
    Prepend_on_apply(Rc<T>, Rc<secondary::T>),
    Assert_in_current_decl(Typing, Rc<Ctx>),
    Drop_reasons_on_apply(Rc<T>),
    Choose(Lazy<bool>, Rc<T>, Rc<T>),
}

/// As `[@@deriving show]`: the function of `From_on_error` is opaque.
impl fmt::Debug for T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            T::Always(err) => f.debug_tuple("Always").field(err).finish(),
            T::Of_error(err) => f.debug_tuple("Of_error").field(err).finish(),
            T::Prefix(prim) => f.debug_tuple("Prefix").field(prim).finish(),
            T::Of_callback(cb, claim) => {
                f.debug_tuple("Of_callback").field(cb).field(claim).finish()
            }
            T::Retain(t, comp) => f.debug_tuple("Retain").field(t).field(comp).finish(),
            T::Incoming_reasons(t, op) => f
                .debug_tuple("Incoming_reasons")
                .field(t)
                .field(op)
                .finish(),
            T::With_code(t, code) => f.debug_tuple("With_code").field(t).field(code).finish(),
            T::With_claim(t, claim) => f.debug_tuple("With_claim").field(t).field(claim).finish(),
            T::With_reasons(t, reasons) => f
                .debug_tuple("With_reasons")
                .field(t)
                .field(reasons)
                .finish(),
            T::Add_quickfixes(t, qfxs) => f
                .debug_tuple("Add_quickfixes")
                .field(t)
                .field(qfxs)
                .finish(),
            T::Add_reason(t, op, reason) => f
                .debug_tuple("Add_reason")
                .field(t)
                .field(op)
                .field(reason)
                .finish(),
            T::From_on_error(_) => f
                .debug_tuple("From_on_error")
                .field(&format_args!("<opaque>"))
                .finish(),
            T::Prepend_on_apply(t, snd_err) => f
                .debug_tuple("Prepend_on_apply")
                .field(t)
                .field(snd_err)
                .finish(),
            T::Assert_in_current_decl(code, ctx) => f
                .debug_tuple("Assert_in_current_decl")
                .field(code)
                .field(ctx)
                .finish(),
            T::Drop_reasons_on_apply(t) => f.debug_tuple("Drop_reasons_on_apply").field(t).finish(),
            T::Choose(condition, if_true, if_false) => f
                .debug_tuple("Choose")
                .field(condition)
                .field(if_true)
                .field(if_false)
                .finish(),
        }
    }
}

// -- Constructors -------------------------------------------------------------

/// Construct a `Reasons_callback.t` from a side-effecting function. This is
/// included to support legacy code only and will be removed once that code is
/// migrated
///
/// Deprecated in OCaml: "This function will be removed. Please use the
/// provided combinators for constructing error callbacks."
pub fn from_on_error(
    f: impl Fn(Option<isize>, Option<Vec<Quickfix<Pos>>>, Vec<Message<PosOrDecl>>) + 'static,
) -> T {
    T::From_on_error(Rc::new(f))
}

/// Create a constant `Reasons_callback.t` which defaults to the value of the
/// supplied `Error.t` when applied. Each component of that error may be
/// subsequently overridden if a value for that component is supplied during
/// evaluation
pub fn of_error(err: error::T) -> T {
    T::Of_error(Rc::new(err))
}

/// Create a `Reasons_callback.t` which defaults to the value of the supplied
/// `Primary.t` error when applied; this is equivalent to
/// `of_error @@ primary err`
pub fn of_primary_error(prim_err: primary::T) -> T {
    T::Of_error(Rc::new(error::primary(prim_err)))
}

/// Select a callback when the error is evaluated.
pub fn choose(condition: Lazy<bool>, if_true: T, if_false: T) -> T {
    T::Choose(condition, Rc::new(if_true), Rc::new(if_false))
}

/// [`choose`] between callbacks that are already shared (a callback is
/// immutable: sharing it is invisible).
pub fn choose_shared(condition: Lazy<bool>, if_true: Rc<T>, if_false: Rc<T>) -> T {
    T::Choose(condition, if_true, if_false)
}

/// Replace the current default claim with the claim from the supplied
/// `Pos.t Message.t`
pub fn with_claim(no_claim: callback::T, claim: Lazy<Message<Pos>>) -> T {
    T::Of_callback(Rc::new(no_claim), claim)
}

/// Replace the current default error code with the supplied one
pub fn with_code(t: T, code: Typing) -> T {
    T::With_code(Rc::new(t), code)
}

/// Replace the current list of reasons with those supplied. This is typically
/// used in combination with `retain_reasons` to fix the `reasons` of the
/// `User_diagnostic.t` that is obtained when the callback is applied
pub fn with_reasons(t: T, reasons: Lazy<Vec<Message<PosOrDecl>>>) -> T {
    T::With_reasons(Rc::new(t), reasons)
}

/// Add a `quickfix` to the `User_diagnostic.t` generated when the callback is
/// applied
pub fn add_quickfixes(t: T, qfxs: Vec<Quickfix<Pos>>) -> T {
    T::Add_quickfixes(Rc::new(t), Rc::new(qfxs))
}

/// Add the `reason` to the start of current list of reasons
pub fn prepend_reason(t: T, reason: Lazy<Message<PosOrDecl>>) -> T {
    T::Add_reason(Rc::new(t), Op::Prepend, reason)
}

/// Add the `reason` to the end of current list of reasons
pub fn append_reason(t: T, reason: Lazy<Message<PosOrDecl>>) -> T {
    T::Add_reason(Rc::new(t), Op::Append, reason)
}

/// When applied, append the supplied reasons to the current list of reasons
pub fn append_incoming_reasons(t: T) -> T {
    T::Incoming_reasons(Rc::new(t), Op::Append)
}

/// When applied, prepend the supplied reasons to the current list of reasons
pub fn prepend_incoming_reasons(t: T) -> T {
    T::Incoming_reasons(Rc::new(t), Op::Prepend)
}

/// Ignore the incoming error code argument when evaluating to a
/// `User_diagnostic.t`.
///
/// This is equivalent to the following function, given some callback
/// `on_error`:
/// `(fun ?code:_ ?quickfixes reasons -> on_error ?quickfixes reasons)`
pub fn retain_code(t: T) -> T {
    T::Retain(Rc::new(t), Component::Code)
}

/// Ignore the incoming reasons argument when evaluating to a
/// `User_diagnostic.t`.
///
/// This is equivalent to the following function, given some callback
/// `on_error`:
/// `(fun ?code ?quickfixes _ -> on_error ?code ?quickfixes)`
pub fn retain_reasons(t: T) -> T {
    T::Retain(Rc::new(t), Component::Reasons)
}

/// Ignore the incoming quickfixes component when evaluating to a
/// `User_diagnostic.t`.
///
/// This is equivalent to the following function, given some callback
/// `on_error`:
/// `(fun ?code ?quickfixes:_ reasons -> on_error ?code reasons)`
pub fn retain_quickfixes(t: T) -> T {
    T::Retain(Rc::new(t), Component::Quickfixes)
}

/// Create a constant `Reasons_callback.t` which always evaluates to the
/// supplied `Error.t` when applied
///
/// This is equivalent to the following function, for some `error` of type
/// `Error.t`:
/// `(fun ?code:_ ?quickfixes:_ _ -> error)`
///
/// This is also the same as:
/// `retain_code @@ retain_reasons @@ reatain_quickfixes @@ of_error error`
pub fn always(err: error::T) -> T {
    T::Always(Rc::new(err))
}

/// Applying the `Reasons_callback.t` `(prepend_on_apply err snd_err1) snd_err2`
/// is the same as applying `err` the secondary error created by prepending
/// `snd_err1` to `snd_err2`.
///
/// The `Secondary.t` error created by the prepending operation has the same
/// code of `snd_err1` and the reasons from `snd_err1` prepended to those of
/// `snd_err2`.
pub fn prepend_on_apply(t: T, snd_err: secondary::T) -> T {
    T::Prepend_on_apply(Rc::new(t), Rc::new(snd_err))
}

/// Creates a callback that ignores the secondary reasons that are passed
/// when it is applied and then proceeds with the callback it wraps. This
/// construct is only helpful if the wrapped callback contains enough
/// context to generate a usable error message.
pub fn drop_reasons_on_apply(t: T) -> T {
    T::Drop_reasons_on_apply(Rc::new(t))
}

/// Applying the `Reasons_callback.t` `(assert_in_current_decl code ctx) err`
/// will evaluate the `Secondary.t` `err` then use the head of the list of
/// reasons as claim in the resulting error, given the position for that
/// reason is in the current decl.
pub fn assert_in_current_decl(code: Typing, ctx: Ctx) -> T {
    T::Assert_in_current_decl(code, Rc::new(ctx))
}

// -- Specific callbacks -------------------------------------------------------

pub fn unify_error_at(pos: Pos) -> T {
    of_error(error::primary(primary::T::Unify_error {
        pos,
        msg_opt: None,
        reasons_opt: None,
    }))
}

pub fn expr_tree_splice_error(
    pos: Pos,
    expr_pos: PosOrDecl,
    contextual_reasons: Option<Lazy<Vec<Message<PosOrDecl>>>>,
    dsl_opt: Option<&str>,
    docs_url: Lazy<Option<String>>,
) -> T {
    let msg = match dsl_opt {
        Some(dsl_name) => format!(
            "This value cannot be inserted (spliced) into a `{}` expression tree",
            crate::utils::strip_ns(dsl_name)
        ),
        None => "This value cannot be inserted (spliced) into an expression tree".to_string(),
    };
    let reason = Lazy::new(move || {
        let docs_url = docs_url.force();
        let docs_url = docs_url
            .as_deref()
            .unwrap_or("https://docs.hhvm.com/hack/expression-trees/splicing");
        let msg = "Hack values need to be converted (lifted) to compatible types before splicing. "
            .to_string()
            + &format!("For more information see: {}", docs_url);

        Message(expr_pos, msg.into())
    });
    let error = append_reason(
        of_error(error::primary(primary::T::Unify_error {
            pos,
            msg_opt: Some(msg),
            reasons_opt: None,
        })),
        reason,
    );
    match contextual_reasons {
        None => error,
        Some(reasons) => with_reasons(error, reasons),
    }
}

pub fn bad_enum_decl(pos: Pos) -> T {
    retain_code(retain_quickfixes(of_error(error::primary(
        primary::T::Bad_enum_decl(pos),
    ))))
}

pub fn bad_conditional_support_dynamic(
    pos: Pos,
    child: String,
    parent: String,
    ty_name: Lazy<String>,
    self_ty_name: Lazy<String>,
) -> T {
    retain_code(retain_quickfixes(of_primary_error(
        primary::T::Bad_conditional_support_dynamic {
            pos,
            child,
            parent,
            ty_name,
            self_ty_name,
        },
    )))
}

pub fn bad_decl_override(name: String, parent_pos: Pos, parent_name: String) -> T {
    append_incoming_reasons(retain_quickfixes(of_primary_error(
        primary::T::Bad_decl_override {
            name,
            pos: parent_pos,
            parent_name,
        },
    )))
}

pub fn invalid_class_refinement(pos: Pos) -> T {
    append_incoming_reasons(retain_code(retain_quickfixes(of_primary_error(
        primary::T::Wellformedness(primary::wellformedness::T::Invalid_class_refinement { pos }),
    ))))
}

pub fn explain_where_constraint(pos: Pos, in_class: bool, decl_pos: PosOrDecl) -> T {
    append_incoming_reasons(retain_code(retain_quickfixes(of_primary_error(
        primary::T::Explain_where_constraint {
            pos,
            in_class,
            decl_pos,
        },
    ))))
}

pub fn explain_constraint(pos: Pos) -> T {
    retain_code(of_primary_error(primary::T::Explain_constraint(pos)))
}

pub fn rigid_tvar_escape_at(pos: Pos, what: String) -> T {
    retain_quickfixes(retain_code(of_primary_error(
        primary::T::Rigid_tvar_escape { pos, what },
    )))
}

pub fn invalid_type_hint(pos: Pos) -> T {
    of_primary_error(primary::T::Invalid_type_hint(pos))
}

pub fn type_constant_mismatch(t: T) -> T {
    retain_quickfixes(with_code(t, Typing::TypeConstantMismatch))
}

pub fn class_constant_type_mismatch(t: T) -> T {
    retain_quickfixes(with_code(t, Typing::ClassConstantTypeMismatch))
}

pub fn unsatisfied_req_callback(
    class_pos: Pos,
    trait_pos: PosOrDecl,
    req_pos: PosOrDecl,
    req_name: String,
) -> T {
    append_incoming_reasons(retain_code(of_primary_error(primary::T::Unsatisfied_req {
        pos: class_pos,
        trait_pos,
        req_pos,
        req_name,
    })))
}

pub fn invalid_echo_argument_at(pos: Pos) -> T {
    of_primary_error(primary::T::Invalid_echo_argument(pos))
}

pub fn index_type_mismatch_at(pos: Pos) -> T {
    of_primary_error(primary::T::Index_type_mismatch {
        pos,
        msg_opt: None,
        reasons_opt: None,
        is_covariant_container: false,
    })
}

pub fn unify_error_assert_primary_pos_in_current_decl(ctx: Ctx) -> T {
    assert_in_current_decl(Typing::UnifyError, ctx)
}

pub fn invalid_type_hint_assert_primary_pos_in_current_decl(ctx: Ctx) -> T {
    assert_in_current_decl(Typing::InvalidTypeHint, ctx)
}
