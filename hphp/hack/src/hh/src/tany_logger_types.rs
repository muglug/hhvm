// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/tany_logger/tany_logger_types.ml`. See
//! `hh/PORTING.md`.

use oxidized::pos::Pos;

/// A masking scheme indicating logging mode.
///
/// For example, both the log levels 1 (0x1) and 3 (0x11) enable logging to a
/// file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogMask {
    File = 1,
    Scuba = 2,
}

/// `log_mask_to_enum`
pub fn log_mask_to_enum(m: LogMask) -> isize {
    m as isize
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpressionInfo {
    /// Notes that a bad type appears in the expression type as a direct
    /// consequence of a declaration having a bad type in it.
    pub declaration_usage: bool,
    /// Marks a point where a bad type is introduced, e.g., as a result of a
    /// function call. When statically available, it indicates what produced
    /// the bad type, e.g., a function name.
    pub producer: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParameterInfo {
    pub is_inout: bool,
    pub is_variadic: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Position {
    Return,
    Parameter(ParameterInfo),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationInfo {
    /// Where in a declaration a bad type appears?
    pub position: Position,
}

/// A context is either a function name or a method name qualified by the
/// enclosing class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContextId {
    Function(String),
    Method(String, String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommonInfo {
    /// Is it in a generated file (based on path)?
    pub is_generated: bool,
    /// Is it in a test file (based on path)?
    pub is_test: bool,
    /// Position of a bad type
    pub pos: Pos,
    /// Identifier for where bad types appear either of the form
    /// `function_name` or `class_name::method_name`
    pub context_id: ContextId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Context {
    Expression(ExpressionInfo),
    Declaration(DeclarationInfo),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Info {
    /// Information that is depended on being a decl or an expression
    pub context: Context,
    /// Information common to different contexts bad types appear in.
    pub common_info: CommonInfo,
}
