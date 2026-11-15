// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `parser/full_fidelity_positioned_syntax.ml`, as far as the ported
//! modules use it beyond what `parser_core_types::positioned_syntax` has.

use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax_trait::SyntaxTrait;

/// Takes a node and an offset; produces the descent through the parse tree
/// to that position (`parentage node position`: the nodes that contain the
/// offset, innermost first).
pub fn parentage(node: &PositionedSyntax, position: isize) -> Vec<&PositionedSyntax> {
    fn aux<'a>(
        nodes: impl Iterator<Item = &'a PositionedSyntax>,
        mut position: isize,
        acc: &mut Vec<&'a PositionedSyntax>,
    ) {
        for h in nodes {
            let width = h.full_width() as isize;
            if position < width {
                acc.push(h);
                return aux(h.iter_children(), position, acc);
            } else {
                position -= width
            }
        }
    }
    let mut acc = vec![];
    aux(std::iter::once(node), position, &mut acc);
    acc.reverse();
    acc
}