// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/package_provider.ml`.

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

/// Every override spells out the attribute, so a file without it needs no
/// parse. The decl parser stamps the override on each definition.
pub fn get_package_override(ctx: &Arc<Ctx>, path: &str, content: &str) -> Option<String> {
    use oxidized::aast_defs::PackageMembership;
    use oxidized::shallow_decl_defs::Decl;
    if !content.contains(naming_special_names_rust::user_attributes::PACKAGE_OVERRIDE) {
        None
    } else {
        // Callers index arbitrary content, so a parse failure resolves by path.
        // (`try ... with _ -> None`)
        let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let file = crate::relative_path::from_root(path);
            ctx.decl_parser
                .parse_impl((&file).into(), content.as_bytes())
        }))
        .ok()?;
        parsed.iter().find_map(|(_, decl, _)| {
            let package = match decl {
                Decl::Class(c) => &c.package,
                Decl::Fun(f) => &f.package,
                Decl::Typedef(t) => &t.package,
                Decl::Const(c) => &c.package,
                Decl::Module(_) => &None,
            };
            match package {
                Some(PackageMembership::PackageOverride(_, package)) => Some(package.clone()),
                Some(PackageMembership::PackageConfigAssignment(_)) | None => None,
            }
        })
    }
}

/// `Package_provider.get_package_with_override_for_file_no_env`
pub fn get_package_with_override_for_file_no_env(
    ctx: &Arc<Ctx>,
    path: &str,
    content: &str,
) -> (Option<Package>, bool) {
    let path = normalize_path(ctx, path);
    let info = &ctx.tco.po.package_info;
    match get_package_override(ctx, &path, content) {
        Some(package) => (package_info::get_package(info, &package), true),
        None => (package_info::get_package_for_file(info, &path), false),
    }
}
