// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_ast_print.ml`. See `hh/PORTING.md`.
//!
//! The printing itself is `Aast.pp_program` ([`crate::ast_show`]: the
//! `[@@deriving show]` of the whole AST, OCaml's `Format` boxes in a margin
//! of 200). As in the OCaml, the formatter is never flushed: what is still in
//! its queue at the end (the closing `]` of the program) is not printed.
//!
//! `print_tast_without_position` prints the positions as `Pos.none` instead
//! of mapping the AST first (the OCaml's `Aast.map` whose `on_pos` returns
//! `Pos.none`): the printer of positions is told to (`P::pos_none`).

use std::sync::Arc;

use crate::ast_show;
use crate::ctx::Ctx;
use crate::format;
use crate::format::Formatter;
use crate::tast;
use crate::typing_env;
use crate::typing_env_types;
use crate::typing_print;

fn print_tast_internal<A>(
    apply_to_ex_ty: impl Fn(&dyn Fn(&tast::Ty) -> String, &tast::Ty) -> A,
    print_ex: impl Fn(A) -> String,
    ctx: Arc<Ctx>,
    tast: &tast::Program,
    pos_none: bool,
) {
    let dummy_filename = crate::relative_path::default;
    let mut env = typing_env_types::empty(None, None, ctx, Arc::new(dummy_filename), None);
    // Set a dummy position to satisfy the invariant check in typing_inference_env
    let dummy_file = crate::relative_path::from_root("tast_print.php");
    // `Pos.make dummy_file (Lexing.from_string "")`: both ends of the lexeme
    // of a fresh lexer are line 1, offset 0.
    let dummy_pos = crate::pos::make_from_lnum_bol_offset(dummy_file, (1, 0, 0), (1, 0, 0));
    let _restore = typing_env::set_inference_env_pos(&mut env, Some(dummy_pos));
    let env = env;
    let print_ex = |ex: &tast::Ty| {
        print_ex(apply_to_ex_ty(
            &|ty| typing_print::full_strip_ns(false, &env, ty),
            ex,
        ))
    };
    let pp_en = |fmt: &mut Formatter, _: &tast::SavedEnv| format::pp_print_string(fmt, "()");
    let pp_ex = |fmt: &mut Formatter, ex: &tast::Ty| format::pp_print_string(fmt, &print_ex(ex));
    let mut formatter = format::formatter_of_out_channel(Box::new(std::io::stdout()));
    format::pp_set_margin(&mut formatter, 200);
    let mut p = ast_show::P::new(&mut formatter, &pp_ex, &pp_en);
    p.pos_none = pos_none;
    ast_show::aast_defs::pp_program(&mut p, tast)
}

pub fn print_tast(ctx: Arc<Ctx>, tast: &tast::Program) {
    let apply_to_ex_ty = |f: &dyn Fn(&tast::Ty) -> String, ty: &tast::Ty| f(ty);
    let print_pos_and_ty = |ty: String| format!("({})", ty);
    print_tast_internal(apply_to_ex_ty, print_pos_and_ty, ctx, tast, false)
}

pub fn print_tast_without_position(ctx: Arc<Ctx>, tast: &tast::Program) {
    let apply_to_ex_ty = |f: &dyn Fn(&tast::Ty) -> String, ty: &tast::Ty| f(ty);
    // `Format.asprintf "%s" ty`
    let print_pos_and_ty = |ty: String| ty;
    print_tast_internal(apply_to_ex_ty, print_pos_and_ty, ctx, tast, true)
}
