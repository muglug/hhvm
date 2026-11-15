// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/fanout.ml`. See `hh/PORTING.md`.
//!
//! The "fanout" of a change: the cached information that must be invalidated
//! and the files that must be typechecked again for the errors of the
//! repository to reflect the change.

use crate::relative_path::RelativePath;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;
use crate::typing_deps_mode;

/// Represents the "fanout" of a change, representing the cached
/// information we must invalidate and the files we must re-typecheck if we want
/// to produce a correct list of all errors in the repository which reflects
/// those changes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct T {
    /// The subset of classes in changed files whose decls changed (excluding
    /// classes whose decls experienced a positions-only change).
    pub changed: dep_set::T,
    /// This set represents the dependents of the declarations which were
    /// changed. In order to detect all errors which may have resulted from
    /// the changes, we must re-typecheck all files containing these
    /// dependents. Because DepSet.t is lossy--it is only a set of symbol
    /// hashes--we cannot precisely reproduce the set of symbols which need
    /// rechecking. Instead, Typing_deps maintains a mapping from symbol hash
    /// to filename (exposed via Typing_deps.get_files).
    pub to_recheck: dep_set::T,
    /// Additional deps to recheck if their files previously had errors.
    pub to_recheck_if_errors: dep_set::T,
}

/// `empty` (a value in OCaml; a function here, as the sets are built anew)
pub fn empty() -> T {
    T {
        changed: dep_set::make(),
        to_recheck: dep_set::make(),
        to_recheck_if_errors: dep_set::make(),
    }
}

pub fn union(t1: &T, t2: &T) -> T {
    let T {
        changed: changed1,
        to_recheck: to_recheck1,
        to_recheck_if_errors: to_recheck_if_errors1,
    } = t1;
    let T {
        changed: changed2,
        to_recheck: to_recheck2,
        to_recheck_if_errors: to_recheck_if_errors2,
    } = t2;
    // Record fields are evaluated from right to left.
    let to_recheck_if_errors = dep_set::union(to_recheck_if_errors1, to_recheck_if_errors2);
    let to_recheck = dep_set::union(to_recheck1, to_recheck2);
    let changed = dep_set::union(changed1, changed2);
    T {
        changed,
        to_recheck,
        to_recheck_if_errors,
    }
}

pub fn add_fanout_of(mode: &typing_deps_mode::T, dep: &dep::Variant, t: T) -> T {
    let T {
        changed,
        to_recheck,
        to_recheck_if_errors,
    } = t;
    // Record fields are evaluated from right to left.
    let to_recheck = dep_set::union(&typing_deps::get_ideps(mode, dep), &to_recheck);
    let changed = dep_set::add(&changed, dep::make(dep));
    T {
        changed,
        to_recheck,
        to_recheck_if_errors,
    }
}

/// Cardinal of deps to recheck. Ignore deps to recheck if they had errors
pub fn cardinal(t: &T) -> isize {
    let T {
        changed: _,
        to_recheck,
        to_recheck_if_errors: _,
    } = t;
    dep_set::cardinal(to_recheck)
}

pub fn add_fanout_of_file(mode: &typing_deps_mode::T, file: &RelativePath, t: T) -> T {
    let T {
        changed,
        to_recheck,
        to_recheck_if_errors,
    } = t;
    let file_dep = dep::Variant::File(file.clone());
    let recheck = typing_deps::get_ideps(mode, &file_dep);
    if dep_set::is_empty(&recheck) {
        T {
            changed,
            to_recheck,
            to_recheck_if_errors,
        }
    } else {
        // Record fields are evaluated from right to left.
        let to_recheck = dep_set::union(&to_recheck, &recheck);
        let changed = dep_set::add(&changed, dep::make(&file_dep));
        T {
            changed,
            to_recheck,
            to_recheck_if_errors,
        }
    }
}

/// Dependency edges for the tests of the modules that compute fanouts.
#[cfg(test)]
pub(crate) mod testing {
    use std::process::Command;
    use std::process::Stdio;
    use std::sync::atomic::Ordering;

    use crate::typing_deps;
    use crate::typing_deps::dep;
    use crate::typing_deps_mode::T::InMemoryMode;

    /// Set in the child process that [`with_edges`] runs.
    const CHILD_VAR: &str = "HH_FANOUT_TEST_WITH_EDGES";

    /// Runs `body` once the edges `(dependent, dependency)` are in the
    /// dependency graph of the process, registered as a typecheck registers
    /// the edges it discovers: `Typing_deps.add_idep` while
    /// `Typing_deps.trace` is on, then `flush_deps` (a `DepEdge` cannot be
    /// built outside `typing_deps`).
    ///
    /// `trace` is global to the process, and the tests of `typing_deps` need
    /// it off, so this happens in a child process: this test binary, running
    /// only the test `test` of the module `module_path` (`module_path!()` of
    /// the test module). In the parent, `with_edges` returns once the child
    /// has passed, and fails otherwise.
    pub(crate) fn with_edges(
        module_path: &str,
        test: &str,
        edges: &[(dep::Variant, dep::Variant)],
        body: impl FnOnce(),
    ) {
        if std::env::var_os(CHILD_VAR).is_some() {
            let mode = InMemoryMode(None);
            typing_deps::TRACE.store(true, Ordering::SeqCst);
            for (dependent, dependency) in edges {
                typing_deps::add_idep(&mode, dependent, dependency);
            }
            typing_deps::flush_deps(&mode);
            typing_deps::TRACE.store(false, Ordering::SeqCst);
            body();
            return;
        }
        // libtest names a test by its path without the crate.
        let module_path = match module_path.split_once("::") {
            Some((_crate, path)) => path,
            None => module_path,
        };
        let name = format!("{module_path}::{test}");
        let out = Command::new(std::env::current_exe().unwrap())
            // (`--include-ignored`: the parent may be an `#[ignore]`d test that
            // was asked for.)
            .args([
                name.as_str(),
                "--exact",
                "--nocapture",
                "--test-threads=1",
                "--include-ignored",
            ])
            .env(CHILD_VAR, "1")
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success() && stdout.contains("1 passed"),
            "the test {name} failed in its child process:\n{stdout}\n{stderr}"
        );
    }
}

#[cfg(test)]
mod tests {
    use relative_path::Prefix;

    use super::*;
    use crate::typing_deps_mode::T::InMemoryMode;

    fn set(deps: &[&dep::Variant]) -> dep_set::T {
        dep_set::of_list(&deps.iter().map(|d| dep::make(d)).collect::<Vec<_>>())
    }

    #[test]
    fn fanout_of_a_dependency_and_of_a_file() {
        use dep::Variant::*;
        let f = |name: &str| Fun(format!("\\test_fanout_rs_{}", name));
        let file = RelativePath::make(Prefix::Root, "test_fanout_rs/a.php".into());
        let edges = [
            (f("user1"), f("used")),
            (f("user2"), f("used")),
            (f("user3"), File(file.clone())),
        ];
        testing::with_edges(
            module_path!(),
            "fanout_of_a_dependency_and_of_a_file",
            &edges,
            || fanout_of_a_dependency_and_of_a_file_body(file),
        );
    }

    fn fanout_of_a_dependency_and_of_a_file_body(file: RelativePath) {
        use dep::Variant::*;
        let mode = InMemoryMode(None);
        let f = |name: &str| Fun(format!("\\test_fanout_rs_{}", name));
        let lonely = RelativePath::make(Prefix::Root, "test_fanout_rs/b.php".into());

        let t = add_fanout_of(&mode, &f("used"), empty());
        assert_eq!(t.changed, set(&[&f("used")]));
        assert_eq!(t.to_recheck, set(&[&f("user1"), &f("user2")]));
        assert_eq!(t.to_recheck_if_errors, dep_set::make());
        assert_eq!(cardinal(&t), 2);

        // A dependency nobody depends on is still changed.
        let t = add_fanout_of(&mode, &f("unused"), t);
        assert_eq!(t.changed, set(&[&f("used"), &f("unused")]));
        assert_eq!(cardinal(&t), 2);

        // A file without dependents changes nothing.
        let t2 = add_fanout_of_file(&mode, &lonely, t.clone());
        assert_eq!(t2, t);
        let t3 = add_fanout_of_file(&mode, &file, t.clone());
        assert_eq!(
            t3.changed,
            set(&[&f("used"), &f("unused"), &File(file.clone())])
        );
        assert_eq!(t3.to_recheck, set(&[&f("user1"), &f("user2"), &f("user3")]));

        let u = union(
            &T {
                changed: set(&[&f("a")]),
                to_recheck: set(&[&f("b")]),
                to_recheck_if_errors: set(&[&f("c")]),
            },
            &T {
                changed: set(&[&f("d")]),
                to_recheck: set(&[&f("b"), &f("e")]),
                to_recheck_if_errors: dep_set::make(),
            },
        );
        assert_eq!(u.changed, set(&[&f("a"), &f("d")]));
        assert_eq!(u.to_recheck, set(&[&f("b"), &f("e")]));
        assert_eq!(u.to_recheck_if_errors, set(&[&f("c")]));
        assert_eq!(cardinal(&u), 2);
        assert_eq!(cardinal(&empty()), 0);
    }
}
