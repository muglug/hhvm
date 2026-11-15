// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactor_sd/refactor_sd_pretty_printer.ml`.

use super::refactor_sd_types::*;

fn pp(pos: &crate::pos::Pos) -> String {
    crate::ast_show::show_pos(pos)
}

pub fn show_entity(e: &Entity_) -> String {
    match e {
        Entity_::Literal(pos) => pp(pos),
        Entity_::Variable(var) => format!("?{}", var),
    }
}

pub fn show_constraint_(c: &Constraint_) -> String {
    match c {
        Constraint_::Introduction(pos) => format!("Introduction at {}", pp(pos)),
        Constraint_::Upcast(ent, _) => format!("Upcast at {}", show_entity(ent)),
        Constraint_::Subset(sub, sup) => format!("{} ⊆ {}", show_entity(sub), show_entity(sup)),
        Constraint_::Called(pos) => format!("Function call at {}", pp(pos)),
    }
}

/// Relationship with shape_analysis: show_shape_result
pub fn show_refactor_sd_result(r: &RefactorSdResult) -> String {
    match r {
        RefactorSdResult::ExistsUpcast(pos) => format!("Upcast exists at {}", pp(pos)),
        RefactorSdResult::NoUpcast => "No upcast".to_string(),
    }
}
