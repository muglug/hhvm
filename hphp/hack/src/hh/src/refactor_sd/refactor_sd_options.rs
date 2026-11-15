// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactor_sd/refactor_sd_options.ml`.

use super::refactor_sd_types::*;

pub fn parse_analysis_mode(s: &str) -> Option<AnalysisMode> {
    match s {
        "flag" => Some(AnalysisMode::FlagTargets),
        "dump" => Some(AnalysisMode::DumpConstraints),
        "simplify" => Some(AnalysisMode::SimplifyConstraints),
        "solve" => Some(AnalysisMode::SolveConstraints),
        _ => None,
    }
}

pub fn parse_refactor_mode(s: &str) -> Option<RefactorMode> {
    match s {
        "Class" => Some(RefactorMode::Class),
        "Function" => Some(RefactorMode::Function),
        _ => None,
    }
}

pub fn mk(analysis_mode: AnalysisMode, refactor_mode: RefactorMode) -> Options {
    Options {
        analysis_mode,
        refactor_mode,
    }
}
