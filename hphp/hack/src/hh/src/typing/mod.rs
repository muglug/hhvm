// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing.ml` (14.3k lines): the typing of expressions, statements
//! and function bodies. See `hh/PORTING.md`.
//!
//! `typing.ml` is one recursive group of OCaml modules (`module rec Expr ...
//! and Function_pointer ... and Tparam`), preceded by helpers and followed by
//! the entry points. Each OCaml module of the group is the Rust module of the
//! same name, in its own file, and the modules call each other by path, as in
//! OCaml (`Stmt.stmt env s` is `stmt::stmt(env, s)`, written
//! `crate::typing::stmt::stmt` or `super::stmt::stmt`).
//!
//! | OCaml (`typing.ml` lines) | Rust (`typing/`) |
//! |---|---|
//! | 1-2514: module aliases, `Log`, `Env_help`, `Fun_id`, `TraitMostConcreteParent`, `Valkind`, helper functions | `prelude.rs` (re-exported here) |
//! | 2515-9032: `Expr` | `expr/`: `part_a.rs` (2515-5016), `part_b.rs` (5017-6892), `part_c.rs` (6893-9032) |
//! | 9034-9486: `Function_pointer` | `function_pointer.rs` |
//! | 9488-9774: `Method_caller` | `method_caller.rs` |
//! | 9776-10649: `Stmt` | `stmt.rs` |
//! | 10651-11787: `Lambda` | `lambda.rs` |
//! | 11789-11869: `User_attribute` | `user_attribute.rs` |
//! | 11871-12507: `Class_id` | `class_id.rs` |
//! | 12509-12799: `Binop` | `binop.rs` |
//! | 12801-12823: `Expression_tree` | `expression_tree.rs` |
//! | 12825-12848: `Afield` | `afield.rs` |
//! | 12850-12966: `Xhp_attribute` | `xhp_attribute.rs` |
//! | 12968-12998: `As_expr` | `as_expr.rs` |
//! | 13000-13099: `Using_stmt` | `using_stmt.rs` |
//! | 13101-13573: `Assign` | `assign.rs` |
//! | 13575-14187: `Class_get_expr` | `class_get_expr.rs` |
//! | 14189-14211: `File_attribute` | `file_attribute.rs` |
//! | 14213-14232: `Tparam` | `tparam.rs` |
//! | 14234-14294: the entry points (`bind_params`, `fun_`, `call`, `expr`, `stmt`, ...) | `toplevel.rs` (re-exported here) |
//!
//! Conventions for every file of this directory:
//!
//! - `use crate::typing::prelude::*;` gives the helpers of the prelude, which
//!   OCaml sees unqualified. Do not glob-import `crate::typing::*`: it also
//!   brings the entry points of `toplevel.rs`, whose names (`expr`,
//!   `stmt`, `call`, ...) collide with the functions of the modules.
//! - The module aliases at the top of `typing.ml` (`module Env = Typing_env`,
//!   `module SubType = Typing_subtype`, ...) become `use` lines in each file
//!   that needs them (`use crate::typing_env as env;`).
//! - Every function is at least `pub(crate)`, including the ones the OCaml
//!   signature of the module hides: the modules of the group are split between
//!   files and people.
//! - In `expr/part_*.rs`, `use super::*;` gives the other functions of
//!   `Expr`, which the parts call unqualified, as in OCaml.

pub(crate) mod prelude;
pub use prelude::*;

pub mod afield;
pub mod as_expr;
pub mod assign;
pub mod binop;
pub mod class_get_expr;
pub mod class_id;
pub mod expr;
pub mod expression_tree;
pub mod file_attribute;
pub mod function_pointer;
pub mod lambda;
pub mod method_caller;
pub mod stmt;
pub mod tparam;
pub mod user_attribute;
pub mod using_stmt;
pub mod xhp_attribute;

mod toplevel;
pub use toplevel::*;
