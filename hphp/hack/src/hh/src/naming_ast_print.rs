// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming_ast_print.ml`. See `hh/PORTING.md`.
//!
//! The printing is `Aast.pp_program` ([`crate::ast_show`]), followed by
//! `Format.pp_print_newline`. `print_nast_without_position` prints the
//! positions as `Pos.none` (`P::pos_none`) instead of mapping the AST first.

use crate::ast_show;
use crate::format;
use crate::format::Formatter;

fn pp_unit(fmt: &mut Formatter, _: &()) {
    format::pp_print_string(fmt, "()")
}

fn print_nast_internal(nast: &oxidized::nast::Program, pos_none: bool) {
    let mut formatter = format::formatter_of_out_channel(Box::new(std::io::stdout()));
    format::pp_set_margin(&mut formatter, 200);
    {
        let mut p = ast_show::P::new(&mut formatter, &pp_unit, &pp_unit);
        p.pos_none = pos_none;
        ast_show::aast_defs::pp_program(&mut p, nast);
    }
    format::pp_print_newline(&mut formatter)
}

pub fn print_nast(nast: &oxidized::nast::Program) {
    print_nast_internal(nast, false)
}

/// (`on_'ex` returns `()`: the annotations of a NAST are `()` already.)
pub fn print_nast_without_position(nast: &oxidized::nast::Program) {
    print_nast_internal(nast, true)
}
