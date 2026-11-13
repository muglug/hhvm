// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming_attributes.ml`. See `hh/PORTING.md`.
//!
//! The attribute lists are `('a, 'b) Aast.user_attribute list`: slices of
//! `aast::UserAttribute<Ex, En>` (the `.0` of an `aast::UserAttributes`).

use oxidized::aast::UserAttribute;
use oxidized::ast_defs::Pos;

pub fn mem<Ex, En>(x: &str, xs: &[UserAttribute<Ex, En>]) -> bool {
    xs.iter().any(|UserAttribute { name, .. }| x == name.1)
}

pub fn mem2<Ex, En>(x1: &str, x2: &str, xs: &[UserAttribute<Ex, En>]) -> bool {
    xs.iter().any(|UserAttribute { name, .. }| {
        let n = name.1.as_str();
        x1 == n || x2 == n
    })
}

pub fn find<'a, Ex, En>(
    x: &str,
    xs: &'a [UserAttribute<Ex, En>],
) -> Option<&'a UserAttribute<Ex, En>> {
    xs.iter().find(|UserAttribute { name, .. }| x == name.1)
}

pub fn find2<'a, Ex, En>(
    x1: &str,
    x2: &str,
    xs: &'a [UserAttribute<Ex, En>],
) -> Option<&'a UserAttribute<Ex, En>> {
    xs.iter().find(|UserAttribute { name, .. }| {
        let n = name.1.as_str();
        x1 == n || x2 == n
    })
}

pub fn mem_pos<Ex, En>(x: &str, xs: &[UserAttribute<Ex, En>]) -> Option<Pos> {
    let attr = find(x, xs);
    match attr {
        Some(UserAttribute { name, .. }) => Some(name.0.clone()),
        None => None,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use oxidized::ast_defs::Id;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn attr(name: &str, line: usize) -> UserAttribute<(), ()> {
        let file = Arc::new(RelativePath::make(Prefix::Root, "a.php".into()));
        let pos = Pos::from_lnum_bol_offset(file, (line, 0, 0), (line, 0, 4));
        UserAttribute {
            name: Id(pos, name.to_string()),
            params: vec![],
        }
    }

    #[test]
    fn finds_the_first() {
        let attrs = vec![attr("__A", 1), attr("__B", 2), attr("__A", 3)];
        assert!(mem("__A", &attrs));
        assert!(!mem("__C", &attrs));
        assert!(mem2("__C", "__B", &attrs));
        assert!(!mem2("__C", "__D", &attrs));
        assert_eq!(find("__A", &attrs).unwrap().name.0.line(), 1);
        assert_eq!(find2("__B", "__A", &attrs).unwrap().name.0.line(), 1);
        assert_eq!(mem_pos("__A", &attrs).unwrap().line(), 1);
        assert_eq!(mem_pos("__C", &attrs), None);
    }
}
