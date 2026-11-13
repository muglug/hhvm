// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Empty persistent maps and sets (`im`) that cost nothing to make.
//!
//! In OCaml, `SMap.empty` and friends are a constant. `im::OrdMap::new()`
//! allocates a whole tree node and fills it (a node has room for 64
//! entries), which is costly where the typechecker makes an empty map or set
//! that usually stays empty (a substitution for a class without type
//! arguments, a visited set that is only read...). These return a copy of
//! one empty map or set per thread and type, which is a reference count
//! bump. A copy is an ordinary map: adding to it copies the node first, as
//! adding to any shared map does.

use std::any::Any;
use std::any::TypeId;
use std::cell::RefCell;

thread_local! {
    static EMPTIES: RefCell<hash::HashMap<TypeId, Box<dyn Any>>> = Default::default();
}

fn empty<C: Any + Clone>(make: impl FnOnce() -> C) -> C {
    EMPTIES.with_borrow_mut(|empties| {
        empties
            .entry(TypeId::of::<C>())
            .or_insert_with(|| Box::new(make()))
            .downcast_ref::<C>()
            .expect("an empty collection of another type")
            .clone()
    })
}

/// `im::OrdMap::new()`
pub fn ord_map<K: Ord + Clone + 'static, V: Clone + 'static>() -> im::OrdMap<K, V> {
    empty(im::OrdMap::new)
}

/// `im::OrdSet::new()`
pub fn ord_set<A: Ord + Clone + 'static>() -> im::OrdSet<A> {
    empty(im::OrdSet::new)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn copies_are_independent() {
        let mut a: im::OrdMap<String, usize> = ord_map();
        a.insert("x".to_string(), 1);
        let b: im::OrdMap<String, usize> = ord_map();
        assert!(b.is_empty());
        assert_eq!(a.len(), 1);
        let mut s: im::OrdSet<String> = ord_set();
        s.insert("y".to_string());
        assert!(ord_set::<String>().is_empty());
        // Another type has its own.
        assert!(ord_map::<String, String>().is_empty());
    }
}
