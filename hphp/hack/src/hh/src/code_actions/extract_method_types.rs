// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactors/extract_method/extract_method_types/extract_method_types.ml`.
//! See `hh/PORTING.md`.

use std::collections::BTreeMap;
use std::rc::Rc;

use super::code_action_types::type_string;
use crate::pos::Pos;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IteratorKind {
    Iterator,
    KeyedIterator,
}

/// `Code_action_types.Type_string.t String.Map.t`
pub type VarTys = BTreeMap<String, Rc<type_string::T>>;

#[derive(Clone)]
pub enum SelectionKind {
    SelectionKindExpression(Rc<type_string::T>),
    SelectionKindStatement,
}

#[derive(Clone)]
pub struct Candidate {
    /// Position for selected statement(s) or expression
    pub pos: Pos,
    pub placeholder_name: String,
    pub selection_kind: SelectionKind,
    pub params: VarTys,
    pub return_: VarTys,
    pub iterator_kind: Option<IteratorKind>,
    pub is_async: bool,
    pub method_pos: Pos,
    pub method_is_static: bool,
}
