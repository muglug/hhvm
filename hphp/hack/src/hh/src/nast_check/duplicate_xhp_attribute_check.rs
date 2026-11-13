// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/duplicate_xhp_attribute_check.ml`.
//!
//! Produce a syntax error on XHP expressions of the form
//! `<foo x={1} x={2} />`.
//!
//! This is not enforced in the parser because syntax errors cannot be
//! `HH_FIXME`'d.

use std::collections::BTreeSet;

use oxidized::nast;
use oxidized::parsing_error::ParsingError;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

fn error_if_repeated_attribute(attribs: &[nast::XhpAttribute], errors: &mut Errors) {
    let mut seen = BTreeSet::new();
    for attrib in attribs {
        match attrib {
            nast::XhpAttribute::XhpSimple(nast::XhpSimple {
                name: (pos, name), ..
            }) => {
                if seen.contains(name.as_str()) {
                    errors.add(ParsingError::XhpParsingError {
                        pos: pos.clone(),
                        msg: format!("Cannot redeclare {}", name),
                    });
                    // Only the first repeated attribute is reported.
                    return;
                }
                seen.insert(name.as_str());
            }
            nast::XhpAttribute::XhpSpread(_) => {}
        }
    }
}

pub struct DuplicateXhpAttributeCheck;

impl<'a> Handler<'a> for DuplicateXhpAttributeCheck {
    fn at_expr(&mut self, _env: &Env<'a>, e: &'a nast::Expr, errors: &mut Errors) {
        if let nast::Expr_::Xml(xml) = &e.2 {
            error_if_repeated_attribute(&xml.1, errors);
        }
    }
}
