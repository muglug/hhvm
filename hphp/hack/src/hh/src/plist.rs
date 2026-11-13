// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! An immutable singly linked list, as OCaml's `list`: adding to the front
//! and copying the list are O(1) and share the tail.
//!
//! Use it where the OCaml keeps a short list in a record that is copied all
//! the time. (`im::Vector` stores up to 64 elements inline, and copies them
//! all when a shared vector is modified.)

use std::rc::Rc;

struct Node<T> {
    elem: T,
    next: Option<Rc<Node<T>>>,
}

pub struct List<T> {
    head: Option<Rc<Node<T>>>,
}

impl<T> List<T> {
    pub fn new() -> Self {
        List { head: None }
    }

    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    pub fn len(&self) -> usize {
        self.iter().count()
    }

    /// `x :: l`
    pub fn push_front(&mut self, elem: T) {
        let next = self.head.take();
        self.head = Some(Rc::new(Node { elem, next }));
    }

    /// `List.hd` (as an option)
    pub fn front(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            next: self.head.as_deref(),
        }
    }
}

impl<T: Clone> List<T> {
    /// Removes and returns the first element.
    pub fn pop_front(&mut self) -> Option<T> {
        let node = self.head.take()?;
        match Rc::try_unwrap(node) {
            Ok(Node { elem, next }) => {
                self.head = next;
                Some(elem)
            }
            Err(node) => {
                self.head = node.next.clone();
                Some(node.elem.clone())
            }
        }
    }

    /// The first element, to modify in place: the first cell is copied if it
    /// is shared with another list (the tail stays shared).
    pub fn front_mut(&mut self) -> Option<&mut T> {
        let node = self.head.as_mut()?;
        if Rc::get_mut(node).is_none() {
            *node = Rc::new(Node {
                elem: node.elem.clone(),
                next: node.next.clone(),
            });
        }
        Rc::get_mut(node).map(|node| &mut node.elem)
    }
}

impl<T> Default for List<T> {
    fn default() -> Self {
        List::new()
    }
}

impl<T> Clone for List<T> {
    fn clone(&self) -> Self {
        List {
            head: self.head.clone(),
        }
    }
}

impl<T> Drop for List<T> {
    /// Not recursive, so that a long list does not overflow the stack.
    fn drop(&mut self) {
        let mut next = self.head.take();
        while let Some(node) = next {
            match Rc::try_unwrap(node) {
                Ok(mut node) => next = node.next.take(),
                Err(_) => break,
            }
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for List<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// In the order of the iterator: its first element is the head of the list.
impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let elems: Vec<T> = iter.into_iter().collect();
        let mut list = List::new();
        for elem in elems.into_iter().rev() {
            list.push_front(elem);
        }
        list
    }
}

pub struct Iter<'a, T> {
    next: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let node = self.next?;
        self.next = node.next.as_deref();
        Some(&node.elem)
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shares_tails() {
        let mut l: List<i32> = [2, 3].into_iter().collect();
        let old = l.clone();
        l.push_front(1);
        assert_eq!(l.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3]);
        assert_eq!(old.iter().copied().collect::<Vec<_>>(), vec![2, 3]);
        assert_eq!(l.len(), 3);
        assert_eq!(l.front(), Some(&1));

        // Modifying the head of a list does not show in its copies.
        let copy = l.clone();
        *l.front_mut().unwrap() = 10;
        assert_eq!(l.iter().copied().collect::<Vec<_>>(), vec![10, 2, 3]);
        assert_eq!(copy.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3]);

        assert_eq!(l.pop_front(), Some(10));
        assert_eq!(l.iter().copied().collect::<Vec<_>>(), vec![2, 3]);
        assert_eq!(copy.len(), 3);
        let mut empty: List<i32> = List::new();
        assert!(empty.is_empty());
        assert_eq!(empty.pop_front(), None);
        assert!(empty.front_mut().is_none());
    }

    #[test]
    fn long_lists_drop() {
        let l: List<usize> = (0..1_000_000).collect();
        assert_eq!(l.len(), 1_000_000);
    }
}
