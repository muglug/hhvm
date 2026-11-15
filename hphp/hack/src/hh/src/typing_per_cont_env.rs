// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_per_cont_env.ml`. See `hh/PORTING.md`.
//!
//! Functions dealing with continuation based flow typing of local variables.
//!
//! The functions that return an updated `t` in OCaml take the map by value
//! and return it: the map is persistent, so callers that go on using the old
//! map clone it (cheaply) before the call.

use oxidized::local_id::LocalId;
use oxidized::package_info::PackageInfo;
use oxidized::pos::Pos;

use crate::type_parameter_env;
use crate::typing_continuations as c;
use crate::typing_fake_members;
use crate::typing_local_packages;
use crate::typing_local_types;

#[derive(Clone)]
pub struct PerContEntry {
    /// Local types per continuation. For example, the local types of the
    /// break continuation correspond to the local types that there were at the
    /// last encountered break in the current scope. These are kept to be merged
    /// at the appropriate merge points.
    pub local_types: typing_local_types::T,
    /// Fake members are used when we want member variables to be treated like
    /// locals. We want to handle the following:
    /// if($this->x) {
    ///   ... $this->x ...
    /// }
    /// The trick consists in replacing $this->x with a "fake" local. So that
    /// all the logic that normally applies to locals is applied in cases like
    /// this. Hence the name: FakeMembers.
    /// All the fake members are thrown away at the first call.
    /// We keep the invalidated fake members for better error messages.
    pub fake_members: typing_fake_members::T,
    /// Type parameter environment
    /// Lower and upper bounds on generic type parameters and abstract types
    /// For constraints of the form Tu <: Tv where both Tu and Tv are type
    /// parameters, we store an upper bound for Tu and a lower bound for Tv.
    /// Contrasting with tenv and subst, bounds are *assumptions* for type
    /// inference, not conclusions.
    pub tpenv: type_parameter_env::T,
    /// Information about packages that have been tested at runtime for inclusion
    /// in the current deployment.  These include the packages asserted with
    /// RequirePackage and if (package).
    /// Remark: the package the file belongs to is _not included although it can
    /// be safely assumed to be part of the current deployment.
    pub loaded_packages: typing_local_packages::T,
}

/// `per_cont_entry C.Map.t`
pub type T = c::map::T<PerContEntry>;

pub fn empty_entry() -> PerContEntry {
    PerContEntry {
        local_types: typing_local_types::empty(),
        fake_members: typing_fake_members::empty(),
        tpenv: type_parameter_env::empty(),
        loaded_packages: typing_local_packages::empty(),
    }
}

pub fn initial_locals(entry: PerContEntry) -> T {
    T::unit(c::T::Next, entry)
}

/// Get a continuation wrapped in Some, or None if not found
pub fn get_cont_option(name: c::T, m: &T) -> Option<PerContEntry> {
    m.get(&name).cloned()
}

/// Get all continuations present in an environment
pub fn all_continuations(m: &T) -> Vec<c::T> {
    // `C.Map.keys` is `fold (fun k _ acc -> k :: acc) m []`: the keys in
    // decreasing order.
    m.keys().rev().copied().collect()
}

/// Continuations used to typecheck the `finally` block.
pub fn continuations_for_finally() -> Vec<c::T> {
    vec![
        c::T::Break,
        c::T::Continue,
        c::T::Catch,
        c::T::Exit,
        c::T::Finally,
    ]
}

/// Update an entry if it exists
pub fn update_cont_entry(
    name: c::T,
    mut m: T,
    f: impl FnOnce(PerContEntry) -> PerContEntry,
) -> T {
    match m.remove(&name) {
        None => m,
        Some(entry) => {
            m.insert(name, f(entry));
            m
        }
    }
}

/// Add the key, value pair to the continuation named 'name'.
/// If the continuation doesn't exist, the map is unchanged.
pub fn add_to_cont(name: c::T, key: LocalId, value: typing_local_types::Local, mut m: T) -> T {
    match m.get_mut(&name) {
        None => m,
        Some(cont) => {
            cont.local_types.insert(key, value);
            m
        }
    }
}

/// remove a local from a continuation if it exists. Otherwise do nothing.
pub fn remove_from_cont(name: c::T, key: &LocalId, mut m: T) -> T {
    match m.get_mut(&name) {
        None => m,
        Some(c) => {
            c.local_types.remove(key);
            m
        }
    }
}

/// Drop a continuation. If the continuation is absent, the map remains
/// unchanged.
pub fn drop_cont(name: c::T, mut m: T) -> T {
    m.remove(&name);
    m
}

pub fn drop_conts(conts: &[c::T], map: T) -> T {
    conts
        .iter()
        .fold(map, |map, cont| drop_cont(*cont, map))
}

pub fn replace_cont(key: c::T, valueopt: Option<PerContEntry>, mut map: T) -> T {
    match valueopt {
        None => drop_cont(key, map),
        Some(value) => {
            map.insert(key, value);
            map
        }
    }
}

pub fn assert_package_loaded_in_cont(
    package_info: &PackageInfo,
    name: c::T,
    pos: Pos,
    pkg: String,
    status: typing_local_packages::LocalPackageRequirement,
    mut m: T,
) -> T {
    match m.get_mut(&name) {
        None => m,
        Some(cont) => {
            let loaded_packages = typing_local_packages::add(
                package_info,
                pos,
                pkg,
                status,
                cont.loaded_packages.clone(),
            );
            cont.loaded_packages = loaded_packages;
            m
        }
    }
}

#[cfg(test)]
mod tests {
    use oxidized::local_id;

    use super::*;
    use crate::typing_defs_core::Ty;

    fn local(ty: Ty) -> typing_local_types::Local {
        typing_local_types::Local {
            ty,
            pos: Pos::NONE,
            eid: crate::expression_id::make(&crate::expression_id::make_provider()),
            macro_splice_vars: None,
        }
    }

    fn some_ty() -> Ty {
        crate::typing_make_type::nothing(crate::typing_reason::none())
    }

    fn lid(name: &str) -> LocalId {
        local_id::make_unscoped(name)
    }

    fn locals_of(name: c::T, m: &T) -> Vec<String> {
        get_cont_option(name, m)
            .map(|entry| entry.local_types.keys().map(|lid| lid.1.clone()).collect())
            .unwrap_or_default()
    }

    #[test]
    fn initial_locals_has_only_next() {
        let m = initial_locals(empty_entry());
        assert_eq!(all_continuations(&m), vec![c::T::Next]);
        assert!(get_cont_option(c::T::Next, &m).is_some());
        assert!(get_cont_option(c::T::Break, &m).is_none());
    }

    #[test]
    fn all_continuations_is_in_decreasing_order() {
        let m = initial_locals(empty_entry());
        let m = replace_cont(c::T::Finally, Some(empty_entry()), m);
        let m = replace_cont(c::T::Catch, Some(empty_entry()), m);
        assert_eq!(
            all_continuations(&m),
            vec![c::T::Finally, c::T::Catch, c::T::Next]
        );
    }

    #[test]
    fn add_and_remove_locals() {
        let m = initial_locals(empty_entry());
        let m = add_to_cont(c::T::Next, lid("$x"), local(some_ty()), m);
        let m = add_to_cont(c::T::Next, lid("$y"), local(some_ty()), m);
        assert_eq!(locals_of(c::T::Next, &m), vec!["$x", "$y"]);

        // The continuation does not exist: nothing is added, and it is not
        // created.
        let m = add_to_cont(c::T::Break, lid("$z"), local(some_ty()), m);
        assert_eq!(all_continuations(&m), vec![c::T::Next]);

        // The map is persistent: an older version is not affected.
        let older = m.clone();
        let m = remove_from_cont(c::T::Next, &lid("$x"), m);
        assert_eq!(locals_of(c::T::Next, &m), vec!["$y"]);
        assert_eq!(locals_of(c::T::Next, &older), vec!["$x", "$y"]);

        let m = remove_from_cont(c::T::Next, &lid("$absent"), m);
        let m = remove_from_cont(c::T::Catch, &lid("$y"), m);
        assert_eq!(locals_of(c::T::Next, &m), vec!["$y"]);
    }

    #[test]
    fn update_cont_entry_only_updates_an_existing_entry() {
        let m = initial_locals(empty_entry());
        let m = update_cont_entry(c::T::Next, m, |mut entry| {
            entry.local_types.insert(lid("$x"), local(some_ty()));
            entry
        });
        assert_eq!(locals_of(c::T::Next, &m), vec!["$x"]);
        let m = update_cont_entry(c::T::Do, m, |_| panic!("no such continuation"));
        assert_eq!(all_continuations(&m), vec![c::T::Next]);
    }

    #[test]
    fn drop_and_replace() {
        let m = initial_locals(empty_entry());
        let m = replace_cont(c::T::Break, Some(empty_entry()), m);
        let m = replace_cont(c::T::Continue, Some(empty_entry()), m);
        assert_eq!(
            all_continuations(&m),
            vec![c::T::Break, c::T::Continue, c::T::Next]
        );
        let m = replace_cont(c::T::Continue, None, m);
        assert_eq!(all_continuations(&m), vec![c::T::Break, c::T::Next]);
        let m = drop_conts(&[c::T::Break, c::T::Exit, c::T::Next], m);
        assert!(all_continuations(&m).is_empty());
        // Dropping what is absent leaves the map unchanged.
        let m = drop_cont(c::T::Next, m);
        assert!(m.is_empty());
        assert_eq!(continuations_for_finally().len(), 5);
    }
}
