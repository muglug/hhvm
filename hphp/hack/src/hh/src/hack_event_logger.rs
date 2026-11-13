// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Hack_event_logger` (`stubs/logging/hack_event_logger.ml`). See
//! `hh/PORTING.md`.
//!
//! The module that is in the tree is the stub: every function does nothing.
//! These are the ones the typechecker calls.

use crate::exception;
use crate::relative_path::RelativePath;
use crate::telemetry;

pub fn flush() {}

/// (Added for the file watchers.)
pub fn set_file_watcher_watchman() {}

/// (Added for the file watchers.)
pub fn set_file_watcher_dfind() {}

pub fn type_check_primary_position_bug(
    _current_file: &RelativePath,
    _message: &[String],
    _stack: &str,
) {
}

pub fn type_check_exn_bug(_path: &RelativePath, _pos: &str, _e: &exception::T) {}

pub fn invariant_violation_bug(
    _path: Option<&RelativePath>,
    _pos: Option<&str>,
    _data: Option<&str>,
    _data_int: Option<isize>,
    _telemetry: Option<&telemetry::T>,
    _desc: &str,
) {
}

/// (Added by F4, for `Symbol_index_core.log_symbol_index_search`.)
#[allow(clippy::too_many_arguments)]
pub fn search_symbol_index(
    _query_text: &str,
    _max_results: isize,
    _results: isize,
    _kind_filter: &str,
    _duration: f64,
    _caller: &str,
    _search_provider: &str,
) {
}

pub fn decl_consistency_bug(
    _path: Option<&RelativePath>,
    _pos: Option<&str>,
    _data: Option<&str>,
    _desc: &str,
) {
}

/// `Hack_event_logger.Fanouts`
pub mod fanouts {
    use crate::yojson::safe::T as Json;

    #[allow(clippy::too_many_arguments)]
    pub fn log_class(
        _class_name: &str,
        _class_diff: &str,
        _class_diff_category: &Json,
        _fanout_cardinal: isize,
        _direct_references_cardinal: isize,
        _descendants_cardinal: isize,
        _children_cardinal: isize,
    ) {
    }

    pub fn log(
        _changes_cardinal: isize,
        _fanout_cardinal: isize,
        _max_class_fanout_cardinal: isize,
    ) {
    }
}
