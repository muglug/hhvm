// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `recursion_tracker.ml`. See `hh/PORTING.md`.
//!
//! The functor `Make (Op : Operation)` is the module [`make`], whose type and
//! functions are generic over the operation (a type that implements
//! [`Operation`]). A module that applies the functor (`include
//! Recursion_tracker.Make (Op)`) re-exports them at its operation type, as
//! `crate::subtype_recursion_tracker` does.

/// `module type Operation = sig type t [@@deriving eq] end`
pub trait Operation: Clone {
    /// `Op.equal`
    fn equal(a: &Self, b: &Self) -> bool;
}

/// `module Make (Op : Operation)`
pub mod make {
    use std::rc::Rc;

    use super::Operation;

    /// `type t = Op.t list`.
    ///
    /// A persistent list, whose tails are shared as OCaml shares them: adding
    /// an operation and copying a tracker are cheap, and the tracker a caller
    /// keeps is not changed by what is added to the one it passes on.
    pub struct T<Op>(Option<Rc<(Op, T<Op>)>>);

    impl<Op> Clone for T<Op> {
        fn clone(&self) -> Self {
            T(self.0.clone())
        }
    }

    impl<Op: std::fmt::Debug> std::fmt::Debug for T<Op> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let mut list = f.debug_list();
            let mut t = self;
            while let Some(cell) = &t.0 {
                let (op, tail) = &**cell;
                list.entry(op);
                t = tail;
            }
            list.finish()
        }
    }

    impl<Op> Default for T<Op> {
        fn default() -> Self {
            empty()
        }
    }

    pub fn empty<Op>() -> T<Op> {
        T(None)
    }

    /// No operation recorded (not in the OCaml).
    pub fn is_empty<Op>(t: &T<Op>) -> bool {
        t.0.is_none()
    }

    /// The operation is added in front of the others (`op :: t`), unless one
    /// of them is equal to it: the first such one, from the most recently
    /// added (`List.find`), is the error.
    pub fn add_op_and_check_infinite_recursion<Op: Operation>(t: T<Op>, op: Op) -> Result<T<Op>, Op> {
        let mut l = &t;
        while let Some(cell) = &l.0 {
            let (t_, tail) = &**cell;
            if Op::equal(&op, t_) {
                return Err(t_.clone());
            }
            l = tail;
        }
        Ok(T(Some(Rc::new((op, t)))))
    }
}

#[cfg(test)]
mod tests {
    use super::make;
    use super::Operation;

    /// An operation whose equality ignores its second component, as the
    /// equality of types ignores reasons.
    #[derive(Clone, Debug, PartialEq)]
    struct Op(isize, &'static str);

    impl Operation for Op {
        fn equal(a: &Self, b: &Self) -> bool {
            a.0 == b.0
        }
    }

    #[test]
    fn adds_new_operations_and_finds_the_most_recent_equal_one() {
        let t = make::empty();
        let t = make::add_op_and_check_infinite_recursion(t, Op(1, "a")).unwrap();
        let t = make::add_op_and_check_infinite_recursion(t, Op(2, "b")).unwrap();
        let kept = t.clone();
        let t = make::add_op_and_check_infinite_recursion(t, Op(3, "c")).unwrap();
        // The error is the operation already in the list, not the new one.
        assert_eq!(
            make::add_op_and_check_infinite_recursion(t.clone(), Op(2, "z")).unwrap_err(),
            Op(2, "b")
        );
        assert_eq!(
            make::add_op_and_check_infinite_recursion(t, Op(1, "z")).unwrap_err(),
            Op(1, "a")
        );
        // A tracker that was copied before an operation was added does not
        // see it.
        assert!(make::add_op_and_check_infinite_recursion(kept, Op(3, "z")).is_ok());
    }

    #[test]
    fn the_empty_tracker_accepts_anything() {
        assert!(make::add_op_and_check_infinite_recursion(make::empty(), Op(0, "a")).is_ok());
        assert_eq!(format!("{:?}", make::empty::<Op>()), "[]");
    }
}
