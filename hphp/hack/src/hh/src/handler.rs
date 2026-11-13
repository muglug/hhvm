// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `handler.ml`. See `hh/PORTING.md`.
//!
//! `handler.ml` has only the two signatures that the TAST checks implement
//! (their `.mli` is `include Handler.S` or `include Handler.Warning.S`).
//! `Tast_check` uses them as first-class modules (`(module Is_check :
//! Handler.Warning.S)`), so a signature is a record of the functions it
//! declares, and a module of that signature is the record of its functions:
//! `handler::warning::S { error_codes: is_check::error_codes, handler:
//! is_check::handler }`.
//!
//! A check module has these as plain functions: `handler` (a value in OCaml,
//! the handler object) is
//! `pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a>`, or
//! `pub fn handler<'a>(as_lint: bool) -> ...` for a warning check, and
//! `error_codes` (a value) is `pub fn error_codes() -> Vec<..>`. `'a` is the
//! lifetime of the TAST the handler is given.

use crate::error_codes;
use crate::tast_visitor;

/// `module type S`
#[derive(Clone, Copy)]
pub struct S<'a> {
    /// `val handler : Tast_visitor.handler`
    pub handler: fn() -> Box<dyn tast_visitor::Handler<'a> + 'a>,
}

/// `module Warning`
pub mod warning {
    use super::error_codes;
    use super::tast_visitor;

    /// `module type S`
    #[derive(Clone, Copy)]
    pub struct S<'a> {
        /// `val error_codes : Error_codes.Warning.t list`
        pub error_codes: fn() -> Vec<error_codes::warning::T>,
        /// `val handler : as_lint:bool -> Tast_visitor.handler`
        pub handler: fn(bool) -> Box<dyn tast_visitor::Handler<'a> + 'a>,
    }
}
