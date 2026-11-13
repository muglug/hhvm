// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Typing_error.Callback`

use std::fmt;
use std::rc::Rc;

use oxidized::error_codes::Typing;
use oxidized::pos::Pos;
use oxidized::quickfix::Quickfix;

use super::primary;

/// A mechanism to apply transformations to primary errors
#[derive(Clone)]
pub enum T {
    Always(primary::T),
    Of_primary(primary::T),
    With_claim_as_reason(Box<T>, primary::T),
    With_code(Typing, Vec<Quickfix<Pos>>),
    Retain_code(Box<T>),
    /// `With_side_effect of t * (unit -> unit)`
    With_side_effect(Box<T>, Rc<dyn Fn()>),
}

/// As `[@@deriving show]`: the function of `With_side_effect` prints as
/// `<fun>`.
impl fmt::Debug for T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            T::Always(err) => f.debug_tuple("Always").field(err).finish(),
            T::Of_primary(err) => f.debug_tuple("Of_primary").field(err).finish(),
            T::With_claim_as_reason(t, new_claim) => f
                .debug_tuple("With_claim_as_reason")
                .field(t)
                .field(new_claim)
                .finish(),
            T::With_code(code, qfxs) => f.debug_tuple("With_code").field(code).field(qfxs).finish(),
            T::Retain_code(t) => f.debug_tuple("Retain_code").field(t).finish(),
            T::With_side_effect(t, _) => f
                .debug_tuple("With_side_effect")
                .field(t)
                .field(&format_args!("<fun>"))
                .finish(),
        }
    }
}

// -- Constructors -------------------------------------------------------------

/// Ignore any arguments and always return the given base error
pub fn always(err: primary::T) -> T {
    T::Always(err)
}

/// Perform an aribrary side-effects when the error is evaluated
///
/// Deprecated in OCaml: "This function will be removed. Please avoid adding
/// side effects to error callbacks."
pub fn with_side_effect(t: T, eff: impl Fn() + 'static) -> T {
    T::With_side_effect(Box::new(t), Rc::new(eff))
}

/// Provide default code, claim, reasons and quickfixes from the supplied
/// `Primary.t` error
pub fn of_primary_error(err: primary::T) -> T {
    T::Of_primary(err)
}

/// Provide a default error code
pub fn with_code(code: Typing) -> T {
    T::With_code(code, vec![])
}

/// Ignore any incoming error code argument and use the existing one
pub fn retain_code(t: T) -> T {
    T::Retain_code(Box::new(t))
}

/// Fix the claim of the callback to `new_claim` and add the received claim
/// argument to the list of reasons
pub fn with_claim_as_reason(t: T, new_claim: primary::T) -> T {
    T::With_claim_as_reason(Box::new(t), new_claim)
}

// -- Specific callbacks -------------------------------------------------------
//
// These are values in OCaml (`val unify_error : t`); here each is a function
// without arguments that builds the value.

pub fn unify_error() -> T {
    with_code(Typing::UnifyError)
}

pub fn index_type_mismatch() -> T {
    with_code(Typing::IndexTypeMismatch)
}

pub fn covariant_index_type_mismatch() -> T {
    with_code(Typing::CovariantIndexTypeMismatch)
}

pub fn expected_stringlike() -> T {
    with_code(Typing::ExpectedStringlike)
}

pub fn constant_does_not_match_enum_type() -> T {
    with_code(Typing::ConstantDoesNotMatchEnumType)
}

pub fn enum_underlying_type_must_be_arraykey() -> T {
    with_code(Typing::EnumUnderlyingTypeMustBeArraykey)
}

pub fn enum_constraint_must_be_arraykey() -> T {
    with_code(Typing::EnumConstraintMustBeArraykey)
}

pub fn enum_subtype_must_have_compatible_constraint() -> T {
    with_code(Typing::EnumSubtypeMustHaveCompatibleConstraint)
}

pub fn parameter_default_value_wrong_type() -> T {
    with_code(Typing::ParameterDefaultValueWrongType)
}

pub fn newtype_alias_must_satisfy_constraint() -> T {
    with_code(Typing::NewtypeAliasMustSatisfyConstraint)
}

pub fn missing_return() -> T {
    with_code(Typing::MissingReturnInNonVoidFunction)
}

pub fn inout_return_type_mismatch() -> T {
    with_code(Typing::InoutReturnTypeMismatch)
}

pub fn class_constant_value_does_not_match_hint() -> T {
    with_code(Typing::ClassConstantValueDoesNotMatchHint)
}

pub fn class_property_initializer_type_does_not_match_hint() -> T {
    with_code(Typing::ClassPropertyInitializerTypeDoesNotMatchHint)
}

pub fn xhp_attribute_does_not_match_hint() -> T {
    with_code(Typing::XhpAttributeValueDoesNotMatchHint)
}

pub fn strict_str_concat_type_mismatch() -> T {
    with_code(Typing::StrictStrConcatTypeMismatch)
}

pub fn strict_str_interp_type_mismatch() -> T {
    with_code(Typing::StrictStrInterpTypeMismatch)
}

pub fn bitwise_math_invalid_argument() -> T {
    with_code(Typing::BitwiseMathInvalidArgument)
}

pub fn inc_dec_invalid_argument() -> T {
    with_code(Typing::IncDecInvalidArgument)
}

pub fn math_invalid_argument() -> T {
    with_code(Typing::MathInvalidArgument)
}

pub fn expect_bool_for_condition() -> T {
    with_code(Typing::ExpectBoolForCondition)
}

pub fn using_error(pos: Pos, has_await: bool) -> T {
    let new_claim = primary::T::Using_error { pos, has_await };
    with_claim_as_reason(retain_code(unify_error()), new_claim)
}
