// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Package` (`packages/package.ml`). See `hh/PORTING.md`.
//!
//! The types are those of `oxidized::package`, re-exported here: `Package`
//! is `Package.t`, `PosId` is `Package.pos_id` and `PackageRelationship` is
//! `Package.package_relationship`.

pub use oxidized::package::*;
use oxidized::pos::Pos;

pub type T = Package;

pub fn show_package(p: &T) -> String {
    let names = |l: &[PosId]| {
        l.iter()
            .map(|PosId(_, name)| name.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "Package: {}\n  | includes: {}\n  | soft_includes: {}\n  | include_paths: {}\n",
        p.name.1,
        names(&p.includes),
        names(&p.soft_includes),
        p.include_paths
            .iter()
            .map(|PosId(_, p)| format!("//{}", p))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub fn get_package_pos(pkg: &T) -> Pos {
    pkg.name.0.clone()
}

pub fn get_package_name(pkg: &T) -> String {
    pkg.name.1.clone()
}

pub fn matches_package_reference(reference: &PosId, target: &T) -> bool {
    let PosId(_, referenced_name) = reference;
    let target_name = get_package_name(target);
    *referenced_name == target_name
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

pub fn includes(pkg1: &T, pkg2: &T) -> bool {
    pkg1.includes
        .iter()
        .any(|package| matches_package_reference(package, pkg2))
}

pub fn soft_includes(pkg1: &T, pkg2: &T) -> bool {
    pkg1.soft_includes
        .iter()
        .any(|package| matches_package_reference(package, pkg2))
}

pub fn relationship(pkg1: &T, pkg2: &T) -> PackageRelationship {
    if pkg1 == pkg2 {
        PackageRelationship::Equal
    } else if includes(pkg1, pkg2) {
        PackageRelationship::Includes
    } else if soft_includes(pkg1, pkg2) {
        PackageRelationship::SoftIncludes
    } else {
        PackageRelationship::Unrelated
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pos_id(s: &str) -> PosId {
        PosId(Pos::NONE, s.to_string())
    }

    fn package(name: &str, includes: &[&str], soft_includes: &[&str]) -> T {
        Package {
            name: pos_id(name),
            includes: includes.iter().map(|s| pos_id(s)).collect(),
            soft_includes: soft_includes.iter().map(|s| pos_id(s)).collect(),
            include_paths: vec![],
            enable_strict_isolation: false,
            allow_deployed_packages_checking: false,
            is_implicit: false,
        }
    }

    #[test]
    fn relationships() {
        let a = package("a", &["b"], &["c"]);
        let b = package("b", &[], &[]);
        let c = package("c", &[], &[]);
        let d = package("d", &[], &[]);
        assert_eq!(relationship(&a, &a), PackageRelationship::Equal);
        assert_eq!(relationship(&a, &b), PackageRelationship::Includes);
        assert_eq!(relationship(&a, &c), PackageRelationship::SoftIncludes);
        assert_eq!(relationship(&a, &d), PackageRelationship::Unrelated);
        assert_eq!(relationship(&b, &a), PackageRelationship::Unrelated);
        // Included and soft-included: included.
        let both = package("both", &["b"], &["b"]);
        assert_eq!(relationship(&both, &b), PackageRelationship::Includes);
    }

    #[test]
    fn implicit_members() {
        // A reference to a family is a reference to its members.
        let a = package("a", &["fam"], &[]);
        let mut member = package("fam.d", &[], &[]);
        assert!(!includes(&a, &member));
        member.is_implicit = true;
        assert!(includes(&a, &member));
        assert!(matches_package_reference(&pos_id("fam.d"), &member));
        assert!(!matches_package_reference(&pos_id("fa"), &member));
        // Both sides of the first `.` have to be there.
        let mut odd = package(".d", &[], &[]);
        odd.is_implicit = true;
        assert!(!matches_package_reference(&pos_id(""), &odd));
        let mut nested = package("fam.d.e", &[], &[]);
        nested.is_implicit = true;
        assert!(matches_package_reference(&pos_id("fam"), &nested));
        assert!(!matches_package_reference(&pos_id("fam.d"), &nested));
    }

    #[test]
    fn show() {
        let mut p = package("a", &["b", "c"], &[]);
        p.include_paths = vec![pos_id("x/"), pos_id("y/")];
        assert_eq!(
            show_package(&p),
            "Package: a\n  | includes: b, c\n  | soft_includes: \n  | include_paths: //x/, //y/\n"
        );
        assert_eq!(get_package_name(&p), "a");
        assert_eq!(get_package_pos(&p), Pos::NONE);
    }
}
