// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tany_logger_common.ml`. See `hh/PORTING.md`.

use oxidized::pos::Pos;

use crate::relative_path;
use crate::tany_logger_types::ContextId;
use crate::tany_logger_types::LogMask;
use crate::tany_logger_types::log_mask_to_enum;

pub fn should_log(log_level: isize, log_mask: LogMask) -> bool {
    log_level & log_mask_to_enum(log_mask) > 0
}

pub fn string_of_pos(pos: &Pos) -> String {
    let path = relative_path::suffix(pos.filename());
    // `String.rsplit2 ~on:'/'`
    let filename = match path.rsplit_once('/') {
        Some((_, filename)) => filename.to_string(),
        None => path.clone(),
    };
    let (line, col) = crate::pos::line_column(pos);
    format!("{}:{}:{}", filename, line, col + 1)
}

pub fn string_of_context_id(c: &ContextId) -> String {
    match c {
        ContextId::Function(fx_name) => fx_name.clone(),
        ContextId::Method(class_name, method_name) => format!("{}::{}", class_name, method_name),
    }
}
