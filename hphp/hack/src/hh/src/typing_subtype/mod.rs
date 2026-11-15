// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_subtype.ml` (13.6k lines): subtyping, constraint
//! simplification and the propagation of constraints to type variables. See
//! `hh/PORTING.md`.
//!
//! `typing_subtype.ml` is one recursive group of OCaml modules (`module rec
//! Subtype ... and Destructure ... and Instantiate`), preceded by helper
//! modules and followed by the entry points. Each OCaml module of the group is
//! the Rust module of the same name, in its own file, and the modules call
//! each other by path, as in OCaml (`Subtype_ask.is_sub_type` is
//! `subtype_ask::is_sub_type`).
//!
//! | OCaml (`typing_subtype.ml` lines) | Rust (`typing_subtype/`) |
//! |---|---|
//! | 1-801: `VisitedGoals`, `Pretty`, `Subtype_env`, `Logging`, `Subtype_negation`, `Sd`, helper functions | `prelude.rs` (re-exported here) |
//! | 802-7656: `Subtype` | `subtype/`: `part_a.rs` (802-2522), `part_b.rs` (2523-4772), `part_c.rs` (4773-7656, `simplify_`) |
//! | 7659-8124: `Destructure` | `destructure.rs` |
//! | 8126-8855: `Can_index` | `can_index.rs` |
//! | 8857-9374: `Can_index_assign` | `can_index_assign.rs` |
//! | 9376-9612: `Can_traverse` | `can_traverse.rs` |
//! | 9614-9857: `Has_type_member` | `has_type_member.rs` |
//! | 9859-10165: `Has_member` | `has_member.rs` |
//! | 10167-10413: `Has_const` | `has_const.rs` |
//! | 10415-10515: `Type_switch` | `type_switch.rs` |
//! | 10517-11226: `Common` | `common.rs` |
//! | 11229-11318: `Subtype_ask` | `subtype_ask.rs` |
//! | 11320-11450: `Subtype_simplify` | `subtype_simplify.rs` |
//! | 11452-12235: `Subtype_trans` | `subtype_trans.rs` |
//! | 12237-12468: `Subtype_tell` | `subtype_tell.rs` |
//! | 12470-12680: `Instantiate` | `instantiate.rs` |
//! | 12682-13559: the entry points (`sub_type`, `is_sub_type`, `add_constraint`, ...) | `toplevel.rs` (re-exported here) |
//!
//! Conventions for every file of this directory:
//!
//! - `use crate::typing_subtype::prelude::*;` gives the helper modules and
//!   functions of the prelude, which OCaml sees unqualified. Do not glob-import
//!   `crate::typing_subtype::*` (the entry points of `toplevel.rs` would
//!   collide with functions of the modules).
//! - The module aliases at the top of `typing_subtype.ml` become `use` lines
//!   in each file that needs them (`use crate::typing_env as env;`).
//! - Every function is at least `pub(crate)`, including the ones the OCaml
//!   signature of the module hides: the modules of the group are split between
//!   files and people.
//! - In `subtype/part_*.rs`, `use super::*;` gives the other functions of
//!   `Subtype`, which the parts call unqualified, as in OCaml.

pub(crate) mod prelude;
pub use prelude::*;

pub mod can_index;
pub mod can_index_assign;
pub mod can_traverse;
pub mod common;
pub mod destructure;
pub mod dynamic_memo;
pub mod has_const;
pub mod has_member;
pub mod has_type_member;
pub mod instantiate;
pub mod subtype;
pub mod subtype_ask;
pub mod subtype_simplify;
pub mod subtype_tell;
pub mod subtype_trans;
pub mod type_switch;

mod toplevel;
pub use toplevel::*;
