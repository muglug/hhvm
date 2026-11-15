// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lint.ml`. See `hh/PORTING.md`.

use crate::diagnostics::Format;
use crate::server_lint_types;

pub fn go(results: &server_lint_types::Result, output_json: bool, error_format: Format) {
    let stdout = std::io::stdout();
    let mut oc = stdout.lock();
    if output_json {
        server_lint_types::output_json(None, None, &mut oc, results)
    } else {
        if !results.is_empty() {
            crate::server_local_config_qe::log_agent_error_format_exposure();
        }
        server_lint_types::output_text(&mut oc, results, error_format)
    }
}
