// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactor_sd/refactor_sd.ml`; its submodules are the other modules
//! of `refactor_sd/`. See `hh/PORTING.md`.
//!
//! A `constraint_ list` is a `Vec` in the order of the OCaml list (its head
//! first). `Refactor_sd_exn` is a panic.

pub mod refactor_sd_env;
pub mod refactor_sd_options;
pub mod refactor_sd_pretty_printer;
pub mod refactor_sd_solver;
pub mod refactor_sd_types;
pub mod refactor_sd_walker;

use refactor_sd_types::*;

fn add_ns(name: &str) -> String {
    if name.starts_with('\\') {
        name.to_string()
    } else {
        format!("\\{}", name)
    }
}

/// `do_ upcasted_id options ctx tast`
pub fn do_(upcasted_id: &str, options: &Options, ctx: &crate::provider_context::T, tast: &[crate::tast::Def]) {
    let upcasted_id = add_ns(upcasted_id);
    let upcasted_info = ElementInfo {
        element_name: upcasted_id,
    };
    match options.analysis_mode {
        AnalysisMode::FlagTargets => {}
        AnalysisMode::DumpConstraints => {
            for (id, constraints) in refactor_sd_walker::program(&upcasted_info, ctx, tast) {
                println!("Constraints for {}:", id);
                let mut shown: Vec<String> = constraints.iter().map(refactor_sd_pretty_printer::show_constraint_).collect();
                shown.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
                for s in shown {
                    println!("{}", s)
                }
                println!()
            }
        }
        AnalysisMode::SimplifyConstraints => {
            for (id, constraints) in refactor_sd_walker::program(&upcasted_info, ctx, tast) {
                let results = refactor_sd_solver::simplify(&constraints);
                println!("Summary for {}:", id);
                for result in &results {
                    println!("{}", refactor_sd_pretty_printer::show_refactor_sd_result(result))
                }
            }
        }
        AnalysisMode::SolveConstraints => {}
    }
}

/// Relationship with shape_analysis: is_shape_like_dict
pub fn contains_upcast(r: &RefactorSdResult) -> bool {
    matches!(r, RefactorSdResult::ExistsUpcast(_))
}
