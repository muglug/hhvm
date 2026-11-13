// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactors/inline_method/inline_method_types.ml`. See
//! `hh/PORTING.md`.

use crate::pos::Pos;
use crate::tast;

#[derive(Clone, Debug)]
pub struct ParamInfo {
    pub name: String,
    pub named: bool,
    pub default: Option<Pos>,
    pub variadic: bool,
}

#[derive(Clone)]
pub struct MethodInfo {
    pub method_pos: Pos,
    pub block: tast::Block,
    pub params: Vec<ParamInfo>,
    pub var_names: Vec<String>,
    pub has_void_return: bool,
    pub is_private: bool,
    pub return_cnt: isize,
    pub last_stmt_is_return: bool,
    pub all_params_are_supported: bool,
}

#[derive(Clone, Debug)]
pub enum CallArg {
    Positional(Pos),
    Named(String, Pos),
}

#[derive(Clone, Debug)]
pub struct CallInfo {
    pub callee_name: String,
    pub caller_name: String,
    pub call_stmt_pos: Pos,
    pub call_pos: Pos,
    pub call_args: Vec<CallArg>,
    pub arg_evaluation_order: Vec<isize>,
}

#[derive(Clone)]
pub struct Candidate {
    pub call: CallInfo,
    pub callee: MethodInfo,
    pub caller: MethodInfo,
}
