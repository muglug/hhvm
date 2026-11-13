// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_local_packages.ml`. See `hh/PORTING.md`.
//!
//! The constructors of `local_package_requirement` keep their OCaml spelling
//! (`Exists_in_deployment`, ...), as the modules that already use them
//! (`typing_env`, `typing_lenv`, `typing_per_cont_env`) spell them. `t` is a
//! persistent map ([`T`], an `S_map`).

#![allow(non_camel_case_types)]

use oxidized::package_info::PackageInfo;
use oxidized::pos::Pos;

use crate::package_info;
use crate::s_map;
use crate::typing_log_value;

/// Packages locally asserted by RequirePackage and if package
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalPackageRequirement {
    Exists_in_deployment,
    Not_exists_in_deployment,
    Unsatisfiable_package_constraints,
}

/// `equal_local_package_requirement` (`[@@deriving eq]`)
pub fn equal_local_package_requirement(
    r1: &LocalPackageRequirement,
    r2: &LocalPackageRequirement,
) -> bool {
    r1 == r2
}

/// `show_local_package_requirement` (`[@@deriving show]`, which qualifies
/// the constructors with the module path).
pub fn show_local_package_requirement(r: &LocalPackageRequirement) -> String {
    match r {
        LocalPackageRequirement::Exists_in_deployment => {
            "Typing_local_packages.Exists_in_deployment".to_string()
        }
        LocalPackageRequirement::Not_exists_in_deployment => {
            "Typing_local_packages.Not_exists_in_deployment".to_string()
        }
        LocalPackageRequirement::Unsatisfiable_package_constraints => {
            "Typing_local_packages.Unsatisfiable_package_constraints".to_string()
        }
    }
}

/// Information about a loaded package in the current environment
#[derive(Clone, Debug)]
pub struct LoadedPackageInfo {
    pub pos: Pos,
    pub status: LocalPackageRequirement,
    pub from_includes: bool,
}

/// Each package maps to its loaded package info
pub type T = s_map::T<LoadedPackageInfo>;

// logging and pretty-printing
pub fn show(lp: &T) -> String {
    let mut acc = String::new();
    for (key, info) in lp.iter() {
        let LoadedPackageInfo {
            pos: _,
            status,
            from_includes,
        } = info;
        acc = format!(
            "{}{}: {}{}; ",
            acc,
            key,
            show_local_package_requirement(status),
            if *from_includes {
                " (from includes)"
            } else {
                ""
            }
        );
    }
    acc
}

pub fn as_log_value(lp: &T) -> typing_log_value::Value {
    typing_log_value::make_map(
        lp.iter()
            .map(|(key, info)| {
                let LoadedPackageInfo {
                    pos: _,
                    status,
                    from_includes,
                } = info;
                (
                    key.clone(),
                    typing_log_value::string_as_value(format!(
                        "{}{}",
                        show_local_package_requirement(status),
                        if *from_includes {
                            " (from includes)"
                        } else {
                            ""
                        }
                    )),
                )
            })
            .collect(),
    )
}

// typing_local_packages.t algebra
pub fn empty() -> T {
    // `SMap.empty`, a constant (see `crate::im_empty`).
    crate::im_empty::ord_map()
}

/// `S_map.merge`: only the packages known on both sides, with the same
/// status, are kept.
pub fn join(lp1: &T, lp2: &T) -> T {
    let mut result = empty();
    for (key, info1) in lp1.iter() {
        match lp2.get(key) {
            Some(info2) => {
                if equal_local_package_requirement(&info1.status, &info2.status) {
                    // attempt to preserve the position of an explicit requirepackage/if package over includes
                    let info = match (info1.from_includes, info2.from_includes) {
                        (true, true) | (false, true) | (false, false) => info1.clone(),
                        (true, false) => info2.clone(),
                    };
                    result.insert(key.clone(), info);
                }
            }
            // (Some _, None) -> None
            None => {}
        }
    }
    // (None, Some _) -> None; (None, None) -> None
    result
}

/// Helper function for add: if pkg is updated with status Unsatisfiable_package_constraints,
/// then all the packages that include pkg must also be updated to status Unsatisfiable_package_constraints.
/// Uses the package_info from the parsed PACKAGES.toml to find which packages include pkg.
fn update_unsatisfiable_packages(package_info: &PackageInfo, pkg: &str, pos: &Pos, lp: T) -> T {
    let mut result = empty();
    for (pkg_name, info) in lp.into_iter() {
        let info = match package_info::get_package(package_info, &pkg_name) {
            None => info,
            Some(package) => {
                let includes: Vec<String> = package.includes.iter().map(|p| p.1.clone()).collect();
                if includes.iter().any(|i| i == pkg) {
                    LoadedPackageInfo {
                        pos: pos.clone(),
                        status: LocalPackageRequirement::Unsatisfiable_package_constraints,
                        ..info
                    }
                } else {
                    info
                }
            }
        };
        result.insert(pkg_name, info);
    }
    result
}

/// The loaded_package algebra is complicated by the fact that packages can include
/// other packages: if A includes B and A is deployed, then B is guaranteed to be
/// deployed too.  This impacts the semantics of adding `pkg` with `status` to loaded_packages:
/// - if the status of pkg is Exists_in_deployment,
///   then the status of all the included packages of pkg is first checked:
///   - if all of them are either assumed to already exists, or have no assumptions made,
///     then pkg and all its included packages are added to the loaded_packages with status
///     Exists_in_deployment;
///   - if any of them as status Not_exists_in_deployment or Unsatisfiable_in_deployment,
///     then the pkg is assumed to be Unsatisfiable_in_deployment and no other assumptions
///     are made on its included packages.
/// - if the status of pkg is Not_exists_in_deployment,
///   then the only mapping pkg -> Not_exists_in_deployment is added to loaded_packages,
///   as no assumptions can be made about the packages included by pkg.
/// - whenever conflicting assumptions are made on a package, then the status of the
///   package, and of _all_ the packages that include it, is set to Unsatisfiable_package_constraints
///
/// Whenever package A includes package B, this code maintains two invariants on the local_package environment:
/// - if A -> Exists_in_deployment then B -> Exists_in_deployment;
/// - if B -> Unsatisfiable_package_constraints then A -> Unsatisfiable_package_constraints
pub fn add(
    package_info: &PackageInfo,
    pos: Pos,
    pkg: String,
    status: LocalPackageRequirement,
    lp: T,
) -> T {
    use LocalPackageRequirement::*;
    match status {
        Exists_in_deployment => {
            let pkgs_included_by_pkg: Vec<String> =
                match package_info::get_package(package_info, &pkg) {
                    None => vec![],
                    Some(pkg) => pkg.includes.iter().map(|p| p.1.clone()).collect(),
                };
            let has_conflict = std::iter::once(&pkg)
                .chain(pkgs_included_by_pkg.iter())
                .any(|pkg_name| match lp.get(pkg_name) {
                    Some(LoadedPackageInfo {
                        status: Not_exists_in_deployment,
                        ..
                    }) => true,
                    Some(LoadedPackageInfo {
                        status: Unsatisfiable_package_constraints,
                        ..
                    }) => true,
                    Some(LoadedPackageInfo {
                        status: Exists_in_deployment,
                        ..
                    }) => false,
                    None => false,
                });
            if has_conflict {
                // If one is not_exists or unsatisfiable, pkg -> Unsatisfiable
                // (no assumption on any of the other included packages)
                let mut lp = update_unsatisfiable_packages(package_info, &pkg, &pos, lp);
                lp.insert(
                    pkg,
                    LoadedPackageInfo {
                        pos,
                        status: Unsatisfiable_package_constraints,
                        from_includes: false,
                    },
                );
                lp
            } else {
                // If all are exists or not found, map includes ∪ pkg to Exists
                let mut lp = lp;
                lp.insert(
                    pkg,
                    LoadedPackageInfo {
                        pos: pos.clone(),
                        status: Exists_in_deployment,
                        from_includes: false,
                    },
                );
                for pkg_name in pkgs_included_by_pkg {
                    // `S_map.add ~combine:(fun old_value _new_value -> old_value)`:
                    // The old_value.status can only be Exists_in_deployment, otherwise
                    // a conflict would have been detected.  For error reporting, preserve
                    // the old_value from_includes and pos fields
                    if !lp.contains_key(&pkg_name) {
                        lp.insert(
                            pkg_name,
                            LoadedPackageInfo {
                                pos: pos.clone(),
                                status: Exists_in_deployment,
                                from_includes: true,
                            },
                        );
                    }
                }
                lp
            }
        }
        Not_exists_in_deployment => match lp.get(&pkg).map(|info| info.status) {
            None | Some(Not_exists_in_deployment) => {
                let mut lp = lp;
                lp.insert(
                    pkg,
                    LoadedPackageInfo {
                        pos,
                        status: Not_exists_in_deployment,
                        from_includes: false,
                    },
                );
                lp
            }
            Some(Exists_in_deployment) | Some(Unsatisfiable_package_constraints) => {
                let mut lp = update_unsatisfiable_packages(package_info, &pkg, &pos, lp);
                lp.insert(
                    pkg,
                    LoadedPackageInfo {
                        pos,
                        status: Unsatisfiable_package_constraints,
                        from_includes: false,
                    },
                );
                lp
            }
        },
        Unsatisfiable_package_constraints => {
            let mut lp = update_unsatisfiable_packages(package_info, &pkg, &pos, lp);
            lp.insert(
                pkg,
                LoadedPackageInfo {
                    pos,
                    status: Unsatisfiable_package_constraints,
                    from_includes: false,
                },
            );
            lp
        }
    }
}

/// Assuming a conservative entailement of package requirements
/// (`S_map.equal`: the same packages, with equal statuses).
pub fn sub(lp1: &T, lp2: &T) -> bool {
    lp1.len() == lp2.len()
        && lp1
            .iter()
            .zip(lp2.iter())
            .all(|((k1, info1), (k2, info2))| {
                k1 == k2 && equal_local_package_requirement(&info1.status, &info2.status)
            })
}

#[cfg(test)]
mod tests {
    use LocalPackageRequirement::*;

    use super::*;

    fn info(status: LocalPackageRequirement, from_includes: bool) -> LoadedPackageInfo {
        LoadedPackageInfo {
            pos: Pos::NONE,
            status,
            from_includes,
        }
    }

    #[test]
    fn join_keeps_common_equal_statuses() {
        let mut lp1 = empty();
        lp1.insert("a".to_string(), info(Exists_in_deployment, true));
        lp1.insert("b".to_string(), info(Exists_in_deployment, false));
        lp1.insert("c".to_string(), info(Exists_in_deployment, false));
        let mut lp2 = empty();
        lp2.insert("a".to_string(), info(Exists_in_deployment, false));
        lp2.insert("b".to_string(), info(Not_exists_in_deployment, false));
        let j = join(&lp1, &lp2);
        assert_eq!(j.len(), 1);
        assert!(!j.get("a").unwrap().from_includes);
    }

    #[test]
    fn sub_is_equality_of_statuses() {
        let mut lp1 = empty();
        lp1.insert("a".to_string(), info(Exists_in_deployment, true));
        let mut lp2 = empty();
        lp2.insert("a".to_string(), info(Exists_in_deployment, false));
        assert!(sub(&lp1, &lp2));
        lp2.insert("b".to_string(), info(Exists_in_deployment, false));
        assert!(!sub(&lp1, &lp2));
    }

    #[test]
    fn show_in_key_order() {
        let mut lp = empty();
        lp.insert("b".to_string(), info(Not_exists_in_deployment, false));
        lp.insert("a".to_string(), info(Exists_in_deployment, true));
        assert_eq!(
            show(&lp),
            "a: Typing_local_packages.Exists_in_deployment (from includes); \
             b: Typing_local_packages.Not_exists_in_deployment; "
        );
    }
}
