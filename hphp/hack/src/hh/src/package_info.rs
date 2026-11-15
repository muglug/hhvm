// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `packages/package_info.ml`. See `hh/PORTING.md`.
//!
//! The type is `oxidized::package_info::PackageInfo`, re-exported here.
//! `oxidized` has `get_package_for_file` (a method, which also knows about
//! the paths of multifile tests); this module has the functions of
//! `package_info.ml` that look a package up by its name.
//!

use oxidized::package::Package;
use oxidized::package::PosId;
pub use oxidized::package_info::*;

pub type T = PackageInfo;

/// `empty`
pub fn empty() -> T {
    T {
        existing_packages: Default::default(),
        include_path_to_package_map: vec![],
    }
}

/// `log_package_info`: the packages in decreasing order of their names
/// (`S_map.fold` puts each one before those it has seen).
pub fn log_package_info(info: &T) {
    let package_info: String = info
        .existing_packages
        .values()
        .rev()
        .map(crate::package::show_package)
        .collect();
    crate::hh_logger::log(&format!(
        "*** Package info: {}\n{}",
        if info.existing_packages.is_empty() {
            "empty"
        } else {
            ""
        },
        package_info
    ))
}

/// Synthesize the member package [F.D] of an implicit family. [family] is the
/// flagged family entry (its single include_path is the family path);
/// [member_dir] is the first path segment [D] below that path. Pure function
/// of the family declaration and [D] -- it touches no filesystem.
///
/// (`oxidized::package_info_impl` has the same function, which is private.)
pub fn synthesize_member(family: &Package, member_dir: &str) -> Package {
    let PosId(fpos, fname) = &family.name;
    let member_name = format!("{}.{}", fname, member_dir);
    let member_path = match family.include_paths.first() {
        Some(PosId(pos, path)) => PosId(pos.clone(), format!("{}{}/", path, member_dir)),
        // Without the family path the member would get the root-relative
        // include_path [D/], matching unrelated files anywhere in the repo.
        None => panic!("implicit package family {} carries no include_path", fname),
    };
    Package {
        name: PosId(fpos.clone(), member_name),
        includes: family.includes.clone(),
        soft_includes: family.soft_includes.clone(),
        include_paths: vec![member_path],
        // Members inherit the family's observability settings.
        enable_strict_isolation: family.enable_strict_isolation,
        allow_deployed_packages_checking: family.allow_deployed_packages_checking,
        is_implicit: true,
    }
}

/// Splits a (possibly synthesized) name [F.D] into family [F] and member [D].
/// Returns None unless both sides are non-empty.
pub fn split_member_name(pkg: &str) -> Option<(String, String)> {
    match pkg.split_once('.') {
        Some((family, member)) if !family.is_empty() && !member.is_empty() => {
            Some((family.to_string(), member.to_string()))
        }
        _ => None,
    }
}

pub fn get_package(info: &T, pkg: &str) -> Option<Package> {
    match info.existing_packages.get(pkg) {
        Some(p) => Some(p.clone()),
        None => {
            // Not declared directly -- it may be a member [F.D] of a declared
            // family.
            match split_member_name(pkg) {
                Some((family, member)) => match info.existing_packages.get(&family) {
                    Some(f) if f.is_implicit => Some(synthesize_member(f, &member)),
                    _ => None,
                },
                None => None,
            }
        }
    }
}

pub fn package_exists(info: &T, pkg: &str) -> bool {
    get_package(info, pkg).is_some()
}

pub fn add_package(info: &T, pkg: Package) -> T {
    let name = crate::package::get_package_name(&pkg);
    // Replacing a configured package would drop it from resolution for as long as
    // the caller holds this [t], which is never what adding one is meant to do.
    if info.existing_packages.contains_key(&name) {
        panic!("package {} is already configured", name);
    }
    let pkg_entries: Vec<(String, Package)> = pkg
        .include_paths
        .iter()
        .map(|PosId(_, path)| (path.clone(), pkg.clone()))
        .collect();
    let mut existing_packages = info.existing_packages.clone();
    existing_packages.insert(name, pkg);
    T {
        existing_packages,
        // Order is precedence: [get_package_for_file] returns the first entry whose
        // include path prefixes the path, and looks no further. So [pkg] goes at
        // the head — a configured package whose include path is a directory would
        // otherwise match first for a path [pkg] names, and [pkg] would never be
        // reached.
        include_path_to_package_map: pkg_entries
            .into_iter()
            .chain(info.include_path_to_package_map.iter().cloned())
            .collect(),
    }
}

/// The get_package_for_file returns the package a file path belongs to;
/// it ignores PackageOverride annotations.
pub fn get_package_for_file(info: &T, path: &str) -> Option<Package> {
    info.get_package_for_file(false, path)
        .map(|package| package.into_owned())
}

#[cfg(test)]
mod tests {
    use oxidized::pos::Pos;

    use super::*;

    fn pos_id(s: &str) -> PosId {
        PosId(Pos::NONE, s.to_string())
    }

    fn package(name: &str, path: &str, is_implicit: bool) -> Package {
        Package {
            name: pos_id(name),
            includes: vec![pos_id("intern")],
            soft_includes: vec![],
            include_paths: vec![pos_id(path)],
            enable_strict_isolation: true,
            allow_deployed_packages_checking: false,
            is_implicit,
        }
    }

    fn info() -> T {
        let plain = package("plain", "www/plain/", false);
        let family = package("prototypes", "www/prototypes/", true);
        PackageInfo {
            existing_packages: [
                ("plain".to_string(), plain.clone()),
                ("prototypes".to_string(), family.clone()),
            ]
            .into_iter()
            .collect(),
            include_path_to_package_map: vec![
                ("www/plain/".to_string(), plain),
                ("www/prototypes/".to_string(), family),
            ],
        }
    }

    #[test]
    fn by_name() {
        let info = info();
        assert_eq!(get_package(&info, "plain").unwrap().name.1, "plain");
        assert!(get_package(&info, "other").is_none());
        // A member of an implicit family.
        let member = get_package(&info, "prototypes.foo").unwrap();
        assert_eq!(member.name.1, "prototypes.foo");
        assert_eq!(member.include_paths, vec![pos_id("www/prototypes/foo/")]);
        assert_eq!(member.includes, vec![pos_id("intern")]);
        assert!(member.is_implicit && member.enable_strict_isolation);
        // Only the first `.` splits.
        assert_eq!(
            get_package(&info, "prototypes.foo.bar").unwrap().name.1,
            "prototypes.foo.bar"
        );
        // Not a member: the family is not implicit, or a side is empty.
        assert!(get_package(&info, "plain.foo").is_none());
        assert!(get_package(&info, "prototypes.").is_none());
        assert!(get_package(&info, ".foo").is_none());
        assert!(package_exists(&info, "prototypes"));
        assert!(package_exists(&info, "prototypes.x"));
        assert!(!package_exists(&info, "x.prototypes"));
        assert_eq!(
            split_member_name("a.b.c"),
            Some(("a".to_string(), "b.c".to_string()))
        );
        assert_eq!(split_member_name("a"), None);
    }

    #[test]
    fn by_file() {
        let info = info();
        assert_eq!(
            get_package_for_file(&info, "www/plain/a/b.php").unwrap().name.1,
            "plain"
        );
        assert_eq!(
            get_package_for_file(&info, "www/prototypes/foo/b.php")
                .unwrap()
                .name
                .1,
            "prototypes.foo"
        );
        // Directly in the directory of the family: no package.
        assert!(get_package_for_file(&info, "www/prototypes/b.php").is_none());
        assert!(get_package_for_file(&info, "www/prototypes//b.php").is_none());
        assert!(get_package_for_file(&info, "elsewhere/b.php").is_none());
    }

    #[test]
    fn adding_a_package() {
        let info = info();
        let extra = package("extra", "www/plain/extra/", false);
        let info = add_package(&info, extra);
        // The new package comes first, so it wins over the directory of `plain`.
        assert_eq!(
            get_package_for_file(&info, "www/plain/extra/a.php").unwrap().name.1,
            "extra"
        );
        assert_eq!(
            get_package_for_file(&info, "www/plain/a.php").unwrap().name.1,
            "plain"
        );
        assert!(package_exists(&info, "extra"));
        let res = std::panic::catch_unwind(|| add_package(&info, package("plain", "x/", false)));
        assert!(res.is_err());
    }

}
