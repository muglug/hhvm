// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/package_expression_check.ml`.

use std::borrow::Cow;

use oxidized::aast_defs::PackageMembership;
use oxidized::name_context::NameContext;
use oxidized::naming_error::NamingError;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::nast_check_error::PackageConstruct;
use oxidized::package::Package;
use oxidized::package::PackageRelationship;
use oxidized::package::PosId;
use oxidized::pos::Pos;

use super::Errors;
use super::attrs;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;
use crate::ctx::Ctx;

/// `Package_info.synthesize_member`: the member package `F.D` of an implicit
/// family.
fn synthesize_member(family: &Package, member_dir: &str) -> Option<Package> {
    let PosId(fpos, fname) = &family.name;
    let PosId(path_pos, path) = family.include_paths.first()?;
    Some(Package {
        name: PosId(fpos.clone(), format!("{}.{}", fname, member_dir)),
        includes: family.includes.clone(),
        soft_includes: family.soft_includes.clone(),
        include_paths: vec![PosId(path_pos.clone(), format!("{}{}/", path, member_dir))],
        // Members inherit the family's observability settings.
        enable_strict_isolation: family.enable_strict_isolation,
        allow_deployed_packages_checking: family.allow_deployed_packages_checking,
        is_implicit: true,
    })
}

/// `Package_info.get_package`
pub(super) fn get_package<'a>(ctx: &'a Ctx, pkg: &str) -> Option<Cow<'a, Package>> {
    let info = &ctx.tco.po.package_info;
    if let Some(p) = info.existing_packages.get(pkg) {
        return Some(Cow::Borrowed(p));
    }
    // Not declared directly -- it may be a member `F.D` of a declared family.
    // (`split_member_name`)
    let (family, member) = pkg.split_once('.')?;
    if family.is_empty() || member.is_empty() {
        return None;
    }
    match info.existing_packages.get(family) {
        Some(f) if f.is_implicit => synthesize_member(f, member).map(Cow::Owned),
        _ => None,
    }
}

/// `Package.matches_package_reference`
fn matches_package_reference(PosId(_, referenced_name): &PosId, target: &Package) -> bool {
    let target_name = &target.name.1;
    referenced_name == target_name
        || target.is_implicit
            && match target_name.split_once('.') {
                Some((family_name, member_name)) => {
                    !family_name.is_empty()
                        && !member_name.is_empty()
                        && referenced_name == family_name
                }
                None => false,
            }
}

/// `Package.relationship`
fn relationship(pkg1: &Package, pkg2: &Package) -> PackageRelationship {
    if pkg1 == pkg2 {
        PackageRelationship::Equal
    } else if pkg1
        .includes
        .iter()
        .any(|package| matches_package_reference(package, pkg2))
    {
        PackageRelationship::Includes
    } else if pkg1
        .soft_includes
        .iter()
        .any(|package| matches_package_reference(package, pkg2))
    {
        PackageRelationship::SoftIncludes
    } else {
        PackageRelationship::Unrelated
    }
}

/// The current package information from the environment:
/// `(package, package_name, package_pos, assignment_kind)`.
fn get_current_package_info<'a>(
    env: &Env<'a>,
    current_pkg_membership: &'a PackageMembership,
) -> (Option<Cow<'a, Package>>, &'a str, Pos, &'static str) {
    match current_pkg_membership {
        PackageMembership::PackageConfigAssignment(pkg_name) => {
            let pkg = get_package(env.ctx, pkg_name);
            let pos = match &pkg {
                Some(p) => p.name.0.clone(),
                None => Pos::NONE,
            };
            (pkg, pkg_name, pos, "entry in the package config")
        }
        PackageMembership::PackageOverride(pkg_pos, pkg_name) => {
            let pkg = get_package(env.ctx, pkg_name);
            (pkg, pkg_name, pkg_pos.clone(), "package override")
        }
    }
}

/// `check_package_strict_inclusion`: the position of the declaration of the
/// required package, when the current package does not include it.
fn strict_inclusion_failure(required_package: &Package, current_package: &Package) -> Option<Pos> {
    match relationship(required_package, current_package) {
        PackageRelationship::Includes => None,
        PackageRelationship::Equal
        | PackageRelationship::Unrelated
        | PackageRelationship::SoftIncludes => Some(required_package.name.0.clone()),
    }
}

fn override_not_allowed(pos: &Pos, pkg_name: &str, attr: &str, p: &Package, errors: &mut Errors) {
    errors.add(NastCheckError::OverrideNotAllowedForPackage {
        pos: pos.clone(),
        pkg: pkg_name.to_string(),
        def_pos: p.name.0.clone(),
        attr: attr.to_string(),
    });
}

/// Emits an error and returns `true` if `required_pkg` has not opted in to
/// being checked for, so the caller skips the ordinary strict-inclusion
/// check. Keyed on the checked package, so no `__PackageOverride` on the
/// caller reaches around it. `construct` selects the message.
fn error_if_not_checkable(
    pos: &Pos,
    pkg_name: &str,
    construct: PackageConstruct,
    required_pkg: Option<&Package>,
    errors: &mut Errors,
) -> bool {
    match required_pkg {
        Some(p) if !p.allow_deployed_packages_checking => {
            // `unsupported_construct`
            errors.add(NastCheckError::ObservationNotAllowedForPackage {
                pos: pos.clone(),
                pkg: pkg_name.to_string(),
                def_pos: p.name.0.clone(),
                construct,
            });
            true
        }
        _ => false,
    }
}

/// `Package_provider.get_package_for_file`, for the file of a position.
fn get_path_package<'a>(env: &Env<'a>, pos: &Pos) -> Option<Cow<'a, Package>> {
    let po = &env.ctx.tco.po;
    po.package_info.get_package_for_file(
        po.package_support_multifile_tests,
        pos.filename().path_str(),
    )
}

fn require_package_strict_inclusion(
    env: &Env<'_>,
    attr: &nast::UserAttributes,
    errors: &mut Errors,
) {
    let Some(attr) = attrs::find2(
        sn::user_attributes::REQUIRE_PACKAGE,
        sn::user_attributes::SOFT_REQUIRE_PACKAGE,
        attr,
    ) else {
        return;
    };
    // Match the leading package-name argument and ignore any trailing
    // arguments, e.g. __SoftRequirePackage's optional integer sampling rate,
    // so those forms don't slip past the check.
    let Some(nast::Expr(_, _, nast::Expr_::String(required_pkg_name))) = attr.params.first() else {
        return;
    };
    let required_pkg_name = required_pkg_name.to_string();
    let nast::Id(name_pos, name) = &attr.name;
    let required_pkg = get_package(env.ctx, &required_pkg_name);
    if error_if_not_checkable(
        name_pos,
        &required_pkg_name,
        PackageConstruct::RequirePackageAttribute(name.clone()),
        required_pkg.as_deref(),
        errors,
    ) {
        return;
    }
    match (required_pkg, env.package) {
        (None, _) if name == sn::user_attributes::SOFT_REQUIRE_PACKAGE => {
            // Emit naming error for unbound package
            errors.add(NamingError::UnboundName {
                pos: name_pos.clone(),
                name: required_pkg_name,
                kind: NameContext::PackageNamespace,
            });
        }
        (Some(required_package), Some(current_pkg_membership)) => {
            let (current_pkg, current_pkg_name, current_pkg_pos, current_package_assignment_kind) =
                get_current_package_info(env, current_pkg_membership);
            if let Some(current_package) = current_pkg {
                if let Some(def_pos) = strict_inclusion_failure(&required_package, &current_package)
                {
                    errors.add(NastCheckError::RequirePackageStrictInclusion {
                        required_pos: name_pos.clone(),
                        required: required_pkg_name,
                        def_pos,
                        current: current_pkg_name.to_string(),
                        current_pos: current_pkg_pos,
                        attribute_name: name.clone(),
                        current_package_assignment_kind: current_package_assignment_kind
                            .to_string(),
                    });
                }
            }
        }
        _ => {}
    }
}

fn package_expression_strict_inclusion(
    env: &Env<'_>,
    nast::Id(pkg_pos, pkg_name): &nast::Id,
    errors: &mut Errors,
) {
    let required_pkg = get_package(env.ctx, pkg_name);
    if error_if_not_checkable(
        pkg_pos,
        pkg_name,
        PackageConstruct::PackageExpression,
        required_pkg.as_deref(),
        errors,
    ) {
        return;
    }
    if let (Some(required_package), Some(current_pkg_membership)) = (required_pkg, env.package) {
        let (current_pkg, current_pkg_name, current_pkg_pos, current_package_assignment_kind) =
            get_current_package_info(env, current_pkg_membership);
        if let Some(current_package) = current_pkg {
            if let Some(def_pos) = strict_inclusion_failure(&required_package, &current_package) {
                errors.add(NastCheckError::PackageExpressionStrictInclusion {
                    pkg_pos: pkg_pos.clone(),
                    pkg: pkg_name.clone(),
                    def_pos,
                    current: current_pkg_name.to_string(),
                    current_pos: current_pkg_pos,
                    current_package_assignment_kind: current_package_assignment_kind.to_string(),
                });
            }
        }
    }
}

/// The `__PackageOverride` file attribute relocates every symbol in the file
/// into `target`. An override is only meaningful when the file's path-derived
/// package `P` includes `target`: i.e. you may only override a file down into
/// a package that its own package already depends on (e.g. an `intern` file
/// overriding into `prod`, where `intern` includes `prod`). Every other
/// target is rejected:
/// - Equal: the override targets the file's own package (a no-op).
/// - otherwise (`target` includes `P`, or the two are unrelated): `P` does
///   not depend on `target`, so the override cannot be meaningful (e.g. a
///   `prod` file overriding into `intern`, or into some unrelated package).
///
/// A soft-include is treated like an include (still a dependency of `P`).
fn package_override_check(env: &Env<'_>, ua: &nast::UserAttribute, errors: &mut Errors) {
    let Some(nast::Expr(_, _, nast::Expr_::String(target_name))) = ua.params.first() else {
        return;
    };
    let target_name = target_name.to_string();
    // An unbound override target is reported by the naming pass.
    let Some(target_package) = get_package(env.ctx, &target_name) else {
        return;
    };
    // A file with no path-derived package uses the override to opt into one,
    // so there is no inclusion relationship to enforce.
    let Some(path_package) = get_path_package(env, &ua.name.0) else {
        return;
    };
    // The file-level isolation check reports this once.
    if path_package.is_implicit {
        return;
    }
    match relationship(&path_package, &target_package) {
        // `path_package` includes (or soft-includes) `target`: a valid demote
        // into a package the file's own package depends on.
        PackageRelationship::Includes | PackageRelationship::SoftIncludes => {}
        PackageRelationship::Equal => errors.add(NastCheckError::RedundantPackageOverride {
            pos: ua.name.0.clone(),
            pkg: path_package.name.1.clone(),
            def_pos: path_package.name.0.clone(),
        }),
        PackageRelationship::Unrelated => {
            errors.add(NastCheckError::PackageOverrideTargetNotIncluded {
                override_pos: ua.name.0.clone(),
                target: target_name,
                path_package: path_package.name.1.clone(),
                path_package_pos: path_package.name.0.clone(),
            })
        }
    }
}

/// Refuses `__PackageOverride` when either the file's path-derived package or
/// the override target has strict isolation. Deliberately keyed on strict
/// isolation alone: a package that merely omits
/// `allow_deployed_packages_checking` must stay joinable by attribute, since
/// that is the only way into one declaring no `include_paths`.
fn package_override_strict_isolation(
    env: &Env<'_>,
    attr: &nast::UserAttribute,
    errors: &mut Errors,
) {
    let nast::Id(name_pos, name) = &attr.name;
    if name != sn::user_attributes::PACKAGE_OVERRIDE {
        return;
    }
    let Some(nast::Expr(_, _, nast::Expr_::String(pkg_name))) = attr.params.first() else {
        return;
    };
    let pkg_name = pkg_name.to_string();
    match get_path_package(env, name_pos) {
        Some(path_package) if path_package.enable_strict_isolation => {
            override_not_allowed(name_pos, &path_package.name.1, name, &path_package, errors);
        }
        _ => match get_package(env.ctx, &pkg_name) {
            Some(p) if p.enable_strict_isolation => {
                override_not_allowed(name_pos, &pkg_name, name, &p, errors);
            }
            _ => {}
        },
    }
}

pub struct PackageExpressionCheck;

impl<'a> Handler<'a> for PackageExpressionCheck {
    // A file attribute, so this hook rather than a per-definition one: the
    // latter reports once per definition, and misses files whose only
    // definitions are typedefs or constants.
    fn at_user_attribute(
        &mut self,
        env: &Env<'a>,
        attr: &'a nast::UserAttribute,
        errors: &mut Errors,
    ) {
        package_override_strict_isolation(env, attr, errors);
    }

    fn at_fun_def(&mut self, env: &Env<'a>, fd: &'a nast::FunDef, errors: &mut Errors) {
        require_package_strict_inclusion(env, &fd.fun.user_attributes, errors);
    }

    fn at_method_(&mut self, env: &Env<'a>, m: &'a nast::Method_, errors: &mut Errors) {
        require_package_strict_inclusion(env, &m.user_attributes, errors);
    }

    fn at_expr(&mut self, env: &Env<'a>, e: &'a nast::Expr, errors: &mut Errors) {
        if let nast::Expr_::Package(id) = &e.2 {
            package_expression_strict_inclusion(env, id, errors);
        }
    }

    // Driven once per definition by `Nast_visitor`'s `on_file_attribute`; the
    // identical diagnostics are deduplicated when the errors are sorted. A
    // file whose only definitions are constants or top-level statements
    // carries no file-attribute copy and is therefore not checked -- the same
    // limitation as the existing __PackageOverride handling in
    // unbound_name_check.
    fn at_file_attribute(
        &mut self,
        env: &Env<'a>,
        fa: &'a nast::FileAttribute,
        errors: &mut Errors,
    ) {
        if let Some(ua) = attrs::find(sn::user_attributes::PACKAGE_OVERRIDE, &fa.user_attributes) {
            package_override_check(env, ua, errors);
        }
    }
}
