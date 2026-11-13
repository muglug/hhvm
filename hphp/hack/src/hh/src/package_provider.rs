// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/package_provider.ml` (not yet
//! `get_package_with_override_for_file_no_env`, which needs
//! `Package_info.extract_package_override`).

use std::sync::Arc;

use oxidized::package::Package;

use crate::ctx::Ctx;
use crate::package_info;

/// `Package_provider.normalize_path`: reduces a multifile-test path
/// `<container>--<simulated/path.php>` to the path it simulates.
pub fn normalize_path(ctx: &Arc<Ctx>, path: &str) -> String {
    // `Provider_context.get_popt ctx`
    let popt = &ctx.tco.po;
    if popt.package_support_multifile_tests {
        crate::multifile::strip_multifile_prefix(path)
    } else {
        path.to_string()
    }
}

/// `Package_provider.get_package_for_file`
pub fn get_package_for_file(ctx: &Arc<Ctx>, path: &str) -> Option<Package> {
    // `Provider_context.get_package_info ctx` is `ctx.popt.package_info`.
    package_info::get_package_for_file(&ctx.tco.po.package_info, &normalize_path(ctx, path))
}
