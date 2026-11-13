// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/lint/lint_codes.ml`. See `hh/PORTING.md`.
//!
//! `[@@deriving enum]` gives `to_enum`, `of_enum`, `min` and `max`.

/// Values 5501 - 5999 are reserved for FB-internal use
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(isize)]
pub enum T {
    LowercaseConstant = 5001,
    UseCollectionLiteral = 5002,
    StaticString = 5003,
    ShapeIdxRequiredField = 5005,
    OptClosedShapeIdxMissingField = 5006,
    SealedNotSubtype = 5007,
    OptionMixed = 5008,
    OptionNull = 5009,
    ClassPointerToString = 5010,
    // EXTEND HERE WITH NEW VALUES IF NEEDED
}

pub fn to_enum(t: T) -> isize {
    t as isize
}

pub fn of_enum(i: isize) -> Option<T> {
    match i {
        5001 => Some(T::LowercaseConstant),
        5002 => Some(T::UseCollectionLiteral),
        5003 => Some(T::StaticString),
        5005 => Some(T::ShapeIdxRequiredField),
        5006 => Some(T::OptClosedShapeIdxMissingField),
        5007 => Some(T::SealedNotSubtype),
        5008 => Some(T::OptionMixed),
        5009 => Some(T::OptionNull),
        5010 => Some(T::ClassPointerToString),
        _ => None,
    }
}

#[allow(non_upper_case_globals)]
pub const min: isize = 5001;

#[allow(non_upper_case_globals)]
pub const max: isize = 5010;

pub fn err_code(t: T) -> isize {
    to_enum(t)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values() {
        assert_eq!(to_enum(T::LowercaseConstant), 5001);
        assert_eq!(to_enum(T::StaticString), 5003);
        assert_eq!(to_enum(T::ShapeIdxRequiredField), 5005);
        assert_eq!(err_code(T::ClassPointerToString), 5010);
        for i in min..=max {
            if let Some(t) = of_enum(i) {
                assert_eq!(to_enum(t), i);
            }
        }
        assert_eq!(of_enum(5004), None);
    }
}
