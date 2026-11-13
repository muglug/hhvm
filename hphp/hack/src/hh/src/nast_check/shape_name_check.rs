// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/shape_name_check.ml`.

use oxidized::ast_defs::ShapeFieldName;
use oxidized::naming_error::NamingError;
use oxidized::nast;
use oxidized::pos::Pos;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

fn get_pos(name: &ShapeFieldName) -> &Pos {
    match name {
        ShapeFieldName::SFlitStr((pos, _))
        | ShapeFieldName::SFclassname(nast::Id(pos, _))
        | ShapeFieldName::SFclassConst(_, (pos, _)) => pos,
    }
}

/// What `Ast_defs.ShapeField.compare` compares: the names, not the positions.
#[derive(PartialEq, Eq, Hash)]
enum Key<'a> {
    LitStr(&'a [u8]),
    Classname(&'a str),
    ClassConst(&'a str, &'a str),
}

fn key(name: &ShapeFieldName) -> Key<'_> {
    match name {
        ShapeFieldName::SFlitStr((_, s)) => Key::LitStr(s),
        ShapeFieldName::SFclassname(nast::Id(_, s)) => Key::Classname(s),
        ShapeFieldName::SFclassConst(nast::Id(_, s1), (_, s2)) => Key::ClassConst(s1, s2),
    }
}

fn error_if_duplicate_names(fdl: &[nast::ShapeExprField], errors: &mut Errors) {
    // The names seen so far: a scan of a vector for the usual small shapes,
    // a hash set for big ones (only membership is asked, so the order of
    // the errors is the order of the fields either way).
    const SMALL: usize = 16;
    let mut seen_small: Vec<Key<'_>> = Vec::new();
    let mut seen = hash::HashSet::default();
    for field in fdl {
        let name = match field {
            nast::ShapeExprField::SFField(name, _) => name,
            nast::ShapeExprField::SFSplat(_) => continue,
        };
        let k = key(name);
        let fresh = if fdl.len() <= SMALL {
            if seen_small.contains(&k) {
                false
            } else {
                seen_small.push(k);
                true
            }
        } else {
            seen.insert(k)
        };
        if !fresh {
            errors.add(NamingError::FieldNameAlreadyBound(get_pos(name).clone()));
        }
    }
}

pub struct ShapeNameCheck;

impl<'a> Handler<'a> for ShapeNameCheck {
    fn at_expr(&mut self, _env: &Env<'a>, e: &'a nast::Expr, errors: &mut Errors) {
        if let nast::Expr_::Shape(fdl) = &e.2 {
            error_if_duplicate_names(fdl, errors);
        }
    }
}
