// Copyright (c) 2019, Facebook, Inc.
// All rights reserved.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use super::syntax::*;
use super::syntax_variant_generated::SyntaxVariant;
pub struct SyntaxChildrenIterator<'a, T, V> {
    pub syntax: &'a SyntaxVariant<'a, T, V>,
    pub index: usize,
    pub index_back: usize,
}

impl<'a, T, V> Iterator for SyntaxChildrenIterator<'a, T, V> {
    type Item = &'a Syntax<'a, T, V>;
    fn next(&mut self) -> Option<Self::Item> {
        // The commonest nodes (tokens, missing nodes, lists) without a call of
        // `next_impl`, a match on every kind; same result.
        match self.syntax {
            SyntaxVariant::Missing | SyntaxVariant::Token(_) => None,
            SyntaxVariant::SyntaxList(elems) => {
                if elems.len() - self.index_back <= self.index {
                    return None;
                }
                let res = elems.get(self.index);
                if res.is_some() {
                    self.index += 1
                }
                res
            }
            _ => self.next_impl(true),
        }
    }
}

impl<'a, T, V> DoubleEndedIterator for SyntaxChildrenIterator<'a, T, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_impl(false)
    }
}
