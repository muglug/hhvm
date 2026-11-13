// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_packages.ml`. See `hh/PORTING.md`.
//!
//! The polymorphic variants of the `.mli` are enums with the OCaml tags:
//! [`CheckReason`] (`check_reason`), [`CanAccessIgnoringPackageOverrideResult`]
//! (the result of `can_access_ignoring_package_override`) and
//! [`CanAccessByPackageRulesResult`] (the result of
//! `can_access_by_package_rules`).
//!
//! `is_excluded` matches the `package_exclude_patterns` of the options as
//! `Str` regular expressions (`Str.string_match (Str.regexp p) filename 0`):
//! they are translated by `crate::files::ignored_path_regexes`, which
//! anchors them at the start of the string, and the compiled patterns are
//! kept per thread (OCaml compiles them at every call; compiling them once
//! has no visible effect).

use std::cell::RefCell;
use std::collections::HashMap;

use oxidized::aast_defs::PackageMembership;
use oxidized::package::Package;
use oxidized::package::PackageRelationship;
use oxidized::package::PosId;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use relative_path::RelativePath;

use crate::package;
use crate::package_provider;
use crate::pos_or_decl;
use crate::relative_path as rp;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error::primary::package::TargetSymbolSpec;
use crate::utils;

#[derive(Clone, Debug)]
pub struct PackageWarningInfo {
    pub current_package: Option<PosId>,
    pub current_package_before_override: Option<String>,
    pub caller_has_package_override: bool,
    pub target_package: Option<PosId>,
    pub target_package_before_override: Option<String>,
    pub callee_has_package_override: bool,
    pub classptr_reference_warning: bool,
}

#[derive(Clone, Debug)]
pub struct PackageErrorInfo {
    pub current_package: Option<PosId>,
    pub current_package_assignment_kind: String,
    pub target_package: Option<PosId>,
    pub target_package_assignment_kind: String,
    pub target_id: String,
}

/// `check_reason`
#[derive(Clone, Debug)]
pub enum CheckReason {
    Yes(TargetSymbolSpec),
    LintOnly,
    ClassPtrLinterOnly,
    No,
}

/// ``[ `Yes | `YesWarning of package_warning_info ]``
#[derive(Clone, Debug)]
pub enum CanAccessIgnoringPackageOverrideResult {
    Yes,
    YesWarning(PackageWarningInfo),
}

/// The result of [`can_access_by_package_rules`].
#[derive(Clone, Debug)]
pub enum CanAccessByPackageRulesResult {
    Yes,
    YesWarning(PackageWarningInfo),
    PackageNotSatisfied(PackageErrorInfo),
    PackageSoftIncludes(PackageErrorInfo),
    ExcludedPathAccess(PackageErrorInfo),
}

fn is_package_loaded_for_access(env: &Env, package: &Package) -> bool {
    (!package.enable_strict_isolation)
        && env::is_package_loaded(env, &package::get_package_name(package))
}

pub fn get_package_violation(
    env: &Env,
    current_pkg: Option<&Package>,
    target_pkg: Option<&Package>,
) -> Option<PackageRelationship> {
    match (current_pkg, target_pkg) {
        (_, None) => None,
        (None, Some(target_pkg_info)) => {
            if is_package_loaded_for_access(env, target_pkg_info) {
                None
            } else {
                Some(PackageRelationship::Unrelated)
            }
        }
        // Anyone can call code outside of a package
        (Some(current_pkg_info), Some(target_pkg_info)) => {
            match package::relationship(current_pkg_info, target_pkg_info) {
                PackageRelationship::Equal | PackageRelationship::Includes => None,
                r @ (PackageRelationship::SoftIncludes | PackageRelationship::Unrelated) => {
                    if is_package_loaded_for_access(env, target_pkg_info) {
                        None
                    } else {
                        Some(r)
                    }
                }
            }
        }
    }
}

thread_local! {
    /// The compiled `package_exclude_patterns`, by source.
    static EXCLUDE_REGEXES: RefCell<HashMap<String, regex::Regex>> =
        RefCell::new(HashMap::new());
}

/// `Str.(string_match (regexp pattern) filename 0)`
fn str_string_match(pattern: &str, filename: &str) -> bool {
    EXCLUDE_REGEXES.with(|cache| {
        let mut cache = cache.borrow_mut();
        if !cache.contains_key(pattern) {
            // `Str.regexp` raises `Failure` on a malformed pattern, which
            // nothing catches.
            let re = match crate::files::ignored_path_regexes(&[pattern.to_string()]) {
                Ok(mut res) => res.remove(0),
                Err(e) => panic!("{}", e),
            };
            cache.insert(pattern.to_string(), re);
        }
        cache[pattern].is_match(filename)
    })
}

thread_local! {
    /// See [`is_excluded`]: the patterns the answers are for, and the
    /// answers by file.
    static EXCLUDED: RefCell<(Vec<String>, hash::HashMap<RelativePath, bool>)> =
        RefCell::new((vec![], hash::HashMap::default()));
}

pub fn is_excluded(env: &Env, file: &RelativePath) -> bool {
    // Not in the OCaml: the answer depends only on the file and on the
    // patterns of the options, and is asked at each access to a symbol of
    // another file (with the current file each time): it is kept per thread,
    // for the patterns it was found with (compared by value: each file is
    // checked with options of its own).
    let excluded_patterns = &env::get_tcopt(env).tco_package_exclude_patterns;
    if let Some(b) = EXCLUDED.with_borrow_mut(|(patterns, m)| {
        if patterns != excluded_patterns {
            *patterns = excluded_patterns.clone();
            m.clear();
        }
        m.get(file).copied()
    }) {
        return b;
    }
    let filename = rp::to_absolute(file);
    let b = excluded_patterns
        .iter()
        .any(|pattern| str_string_match(pattern, &filename));
    EXCLUDED.with_borrow_mut(|(_, m)| {
        if m.len() >= 16384 {
            m.clear()
        }
        m.insert(file.clone(), b)
    });
    b
}

/// package, package info (name * pos), package membership kind
pub fn get_package_profile(
    env: &Env,
    pkg_membership: Option<&PackageMembership>,
) -> (Option<Package>, Option<PosId>, String) {
    match pkg_membership {
        Some(PackageMembership::PackageConfigAssignment(pkg_name)) => {
            let pkg = env::get_package_by_name(env, pkg_name);
            let pos = match &pkg {
                Some(p) => package::get_package_pos(p),
                None => Pos::NONE,
            };
            (
                pkg,
                Some(PosId(pos, pkg_name.clone())),
                "entry in the package config".to_string(),
            )
        }
        Some(PackageMembership::PackageOverride(pkg_pos, pkg_name)) => (
            env::get_package_by_name(env, pkg_name),
            Some(PosId(pkg_pos.clone(), pkg_name.clone())),
            "package override".to_string(),
        ),
        _ => (None, None, "".to_string()),
    }
}

/// True when [membership] resolves to a package with strict isolation enabled.
/// Positions that are exempt from package checks by default (attributes, type
/// references, ::class, nameof) consult this to opt strict-isolation targets back
/// into enforcement.
pub fn is_strict_isolation_target(env: &Env, pkg_membership: Option<&PackageMembership>) -> bool {
    let (target_pkg, _, _) = get_package_profile(env, pkg_membership);
    match target_pkg {
        Some(p) => p.enable_strict_isolation,
        None => false,
    }
}

fn package_includes(current_pkg: Option<&Package>, target_pkg: Option<&Package>) -> bool {
    match (current_pkg, target_pkg) {
        (Some(current_pkg), Some(target_pkg)) => {
            match package::relationship(current_pkg, target_pkg) {
                PackageRelationship::Equal | PackageRelationship::Includes => true,
                PackageRelationship::SoftIncludes | PackageRelationship::Unrelated => false,
            }
        }
        _ => false,
    }
}

pub fn has_package_override(membership: Option<&PackageMembership>) -> bool {
    match membership {
        Some(PackageMembership::PackageOverride(..)) => true,
        Some(PackageMembership::PackageConfigAssignment(_)) | None => false,
    }
}

fn package_before_override(env: &Env, file: &RelativePath) -> Option<String> {
    package_provider::get_package_for_file(&env::get_ctx(env), &rp::suffix(file))
        .map(|p| package::get_package_name(&p))
}

pub fn can_access_ignoring_package_override(
    env: &Env,
    current_package: Option<PosId>,
    current_package_before_override: Option<String>,
    caller_has_package_override: bool,
    target_package: Option<PosId>,
    callee_has_package_override: bool,
    target_file: &RelativePath,
    classptr_reference_warning: bool,
) -> CanAccessIgnoringPackageOverrideResult {
    let target_package_before_override = package_before_override(env, target_file);
    let is_target_package_before_override_included = match (
        &current_package_before_override,
        &target_package_before_override,
    ) {
        (Some(current_package_before_override_name), Some(target_package_before_override_name)) => {
            package_includes(
                env::get_package_by_name(env, current_package_before_override_name).as_ref(),
                env::get_package_by_name(env, target_package_before_override_name).as_ref(),
            )
        }
        _ => true,
    };
    let is_target_package_before_override_loaded = match &target_package_before_override {
        Some(pkg_name) => env::is_package_loaded(env, pkg_name),
        None => true,
    };
    if is_target_package_before_override_included || is_target_package_before_override_loaded {
        CanAccessIgnoringPackageOverrideResult::Yes
    } else {
        let warn_info = PackageWarningInfo {
            current_package,
            current_package_before_override,
            caller_has_package_override,
            target_package,
            target_package_before_override,
            callee_has_package_override,
            classptr_reference_warning,
        };
        CanAccessIgnoringPackageOverrideResult::YesWarning(warn_info)
    }
}

pub fn can_access_by_package_rules(
    env: &Env,
    target_package_membership: Option<&PackageMembership>,
    target_pos: &PosOrDecl,
    target_id: String,
) -> CanAccessByPackageRulesResult {
    let current_file = env::get_file(env);
    let target_file = pos_or_decl::filename(target_pos);
    // invariant: if two symbols are in the same file they must be in the same package
    let in_same_file = rp::suffix(&current_file) == rp::suffix(&target_file);
    let accessing_hhi = pos_or_decl::is_hhi(target_pos);
    // Fast path: same-file and hhi accesses are always allowed. Keep this check
    // ahead of the package-profile and is_excluded lookups below, which are
    // comparatively expensive (env lookups and regex matching) and run on every
    // symbol access -- the same-file case is very common.
    if in_same_file || accessing_hhi {
        CanAccessByPackageRulesResult::Yes
    } else {
        let current_package_membership = env::get_current_package_membership(env);
        let (current_pkg, current_package, current_package_assignment_kind) =
            get_package_profile(env, current_package_membership.as_ref());
        let (target_pkg, target_package, target_package_assignment_kind) =
            get_package_profile(env, target_package_membership);
        let target_is_strict_isolation = match &target_pkg {
            Some(p) => p.enable_strict_isolation,
            None => false,
        };
        let current_excluded = is_excluded(env, &current_file);
        let target_excluded = is_excluded(env, &target_file);
        let mk_err_info = || PackageErrorInfo {
            current_package: current_package.clone(),
            current_package_assignment_kind: current_package_assignment_kind.clone(),
            target_package: target_package.clone(),
            target_package_assignment_kind: target_package_assignment_kind.clone(),
            target_id: target_id.clone(),
        };
        if (current_excluded || target_excluded) && !target_is_strict_isolation {
            // Packages without strict isolation: package_exclude_patterns (e.g.
            // __tests__) fully exempts the access from package enforcement, in either
            // direction.
            CanAccessByPackageRulesResult::Yes
        } else {
            // Run the ordinary cross-package rules first.
            let standard_result =
                match get_package_violation(env, current_pkg.as_ref(), target_pkg.as_ref()) {
                    None => {
                        // No package error, but the edge may be legal only because of a
                        // __PackageOverride on one of its endpoints, in which case it is what
                        // keeps that override -- and the package bloat it causes -- in
                        // place.
                        let caller_has_package_override =
                            has_package_override(current_package_membership.as_ref());
                        let callee_has_package_override =
                            has_package_override(target_package_membership);
                        if !(caller_has_package_override || callee_has_package_override) {
                            CanAccessByPackageRulesResult::Yes
                        } else {
                            // Without an override the path-derived package is the one already
                            // resolved, so skip the lookup.
                            let current_package_before_override = if caller_has_package_override {
                                package_before_override(env, &current_file)
                            } else {
                                current_package.as_ref().map(|PosId(_, name)| name.clone())
                            };
                            match can_access_ignoring_package_override(
                                env,
                                current_package.clone(),
                                current_package_before_override,
                                caller_has_package_override,
                                target_package.clone(),
                                callee_has_package_override,
                                &target_file,
                                false,
                            ) {
                                CanAccessIgnoringPackageOverrideResult::Yes => {
                                    CanAccessByPackageRulesResult::Yes
                                }
                                CanAccessIgnoringPackageOverrideResult::YesWarning(w) => {
                                    CanAccessByPackageRulesResult::YesWarning(w)
                                }
                            }
                        }
                    }
                    Some(pkg_relationship) => match pkg_relationship {
                        PackageRelationship::SoftIncludes => {
                            CanAccessByPackageRulesResult::PackageSoftIncludes(mk_err_info())
                        }
                        PackageRelationship::Unrelated => {
                            CanAccessByPackageRulesResult::PackageNotSatisfied(mk_err_info())
                        }
                        PackageRelationship::Equal | PackageRelationship::Includes => {
                            utils::assert_false_log_backtrace(Some(
                                "Package constraints are satisfied with equal and includes",
                            ))
                        }
                    },
                };
            // Strict isolation adds one boundary the ordinary cross-package rules
            // cannot express: within a strict-isolation package, non-excluded code may
            // not reference the package's own excluded-path (e.g. __tests__) code. The
            // ordinary rules see both files as the same package (an Equal
            // relationship) and allow it, so upgrade that -- and only that --
            // otherwise-allowed case to an error. A genuine cross-package reference
            // keeps its standard violation.
            match standard_result {
                CanAccessByPackageRulesResult::Yes
                    if target_is_strict_isolation && target_excluded && !current_excluded =>
                {
                    CanAccessByPackageRulesResult::ExcludedPathAccess(mk_err_info())
                }
                _ => standard_result,
            }
        }
    }
}
