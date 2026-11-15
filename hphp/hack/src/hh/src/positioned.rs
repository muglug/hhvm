// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/pos/positioned.ml`. See `hh/PORTING.md`.
//!
//! A positioned value is a pair `(pos, x)`, as in OCaml (`Pos.t * 'a`). The
//! hackrs decls use `pos::Positioned<S, BPos>` instead; these functions are
//! for the pairs of the AST and of the typechecker's own types.

use oxidized::decl_reference::DeclReference;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

/// Compress the position of a positioned value to be stored in the decl heap.
pub fn make_for_decl<A>((p, x): (Pos, A), decl: DeclReference) -> (PosOrDecl, A) {
    (crate::pos_or_decl::make_decl_pos(&p, decl), x)
}

/// Compress the position of a positioned value to be stored in the decl heap.
/// If no decl reference is given, the position is not compressed but
/// simply converted.
pub fn make_for_decl_of_option<A>((p, x): (Pos, A), decl: Option<DeclReference>) -> (PosOrDecl, A) {
    (crate::pos_or_decl::make_decl_pos_of_option(&p, decl), x)
}

/// This may become unsafe in the future as we change the implementation
/// of positions in the decl heap. Avoid using in new code.
/// Use an id from an AST instead of from a decl or type,
/// or resolve decl position to a raw position using a provider context.
pub fn unsafe_to_raw_positioned<A>((p, x): (PosOrDecl, A)) -> (Pos, A) {
    (crate::pos_or_decl::unsafe_to_raw_pos(p), x)
}

/// This is essentially an upcast.
pub fn of_raw_positioned<A>((p, x): (Pos, A)) -> (PosOrDecl, A) {
    (crate::pos_or_decl::of_raw_pos(p), x)
}
