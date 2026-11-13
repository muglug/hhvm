// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Typing_error_utils.Eval_primary`. See `../mod.rs`.

use oxidized::error_codes::Typing;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::quickfix::Quickfix;

use super::common::Lazy;

/// `Eval_primary.t`
#[derive(Clone, Debug)]
pub struct T {
    pub code: Typing,
    pub claim: Lazy<Message<Pos>>,
    pub reasons: Lazy<Vec<Message<PosOrDecl>>>,
    pub quickfixes: Vec<Quickfix<Pos>>,
}

/// `create ~code ~claim ?(reasons = lazy []) ?(quickfixes = []) ()`
pub fn create(
    code: Typing,
    claim: Lazy<Message<Pos>>,
    reasons: Option<Lazy<Vec<Message<PosOrDecl>>>>,
    quickfixes: Option<Vec<Quickfix<Pos>>>,
) -> T {
    let reasons = reasons.unwrap_or_else(|| Lazy::new(Vec::new));
    let quickfixes = quickfixes.unwrap_or_default();
    T {
        code,
        claim,
        reasons,
        quickfixes,
    }
}

// The nested modules of `Eval_primary`.
pub mod nested;
pub use nested::*;

// The functions of `Eval_primary`, in the order of the OCaml file: the first
// half (up to and including `unresolved_tyvar_projection`'s predecessors), then
// the rest including `to_error`.
mod functions_a;
mod functions_b;
pub use functions_a::*;
pub use functions_b::*;
