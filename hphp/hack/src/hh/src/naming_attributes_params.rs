// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/naming_attributes_params.ml`. See `hh/PORTING.md`.
//!
//! The message is bytes (`bstr::BString`), as an OCaml string is: it is made
//! of the parameter of the attribute, which `Nast_eval.static_string` gives
//! as bytes.

use bstr::BString;
use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::nast;

use crate::naming_attributes;
use crate::nast_eval;
use crate::utils;

/// TODO: generalize the arity check / argument check here to handle
/// attributes in general, not just __Deprecated
pub fn deprecated<P>(
    kind: &str,
    (_, name): &(P, String),
    attrs: &[nast::UserAttribute],
) -> Option<BString> {
    let attr = naming_attributes::find(sn::user_attributes::DEPRECATED, attrs);
    match attr {
        Some(aast::UserAttribute { name: _, params }) => match params.as_slice() {
            [msg, ..] => match nast_eval::static_string(msg) {
                Ok(msg) => {
                    let name = utils::strip_ns(name);
                    let deprecated_prefix = format!("The {} {} is deprecated: ", kind, name);
                    let mut res = BString::from(deprecated_prefix);
                    res.extend_from_slice(&msg);
                    Some(res)
                }
                Err(_) => None,
            },
            [] => None,
        },
        None => None,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use oxidized::ast_defs::Bop;
    use oxidized::ast_defs::Id;
    use oxidized::pos::Pos;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn pos(line: usize) -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, "a.php".into()));
        Pos::from_lnum_bol_offset(file, (line, 0, 0), (line, 0, 4))
    }

    fn string(s: &str) -> nast::Expr {
        aast::Expr((), pos(1), aast::Expr_::String(s.into()))
    }

    fn attr(name: &str, params: Vec<nast::Expr>) -> nast::UserAttribute {
        aast::UserAttribute {
            name: Id(pos(1), name.to_string()),
            params,
        }
    }

    #[test]
    fn deprecated_messages() {
        let id = (pos(1), "\\NS\\f".to_string());
        let msg = binop_dot(string("use "), string("g"));
        let attrs = vec![
            attr("__Memoize", vec![]),
            attr(
                sn::user_attributes::DEPRECATED,
                vec![msg, string("ignored")],
            ),
        ];
        assert_eq!(
            deprecated("function", &id, &attrs),
            Some("The function NS\\f is deprecated: use g".into())
        );
        // No message, or one that is not a static string.
        let attrs = vec![attr(sn::user_attributes::DEPRECATED, vec![])];
        assert_eq!(deprecated("function", &id, &attrs), None);
        let var = aast::Expr(
            (),
            pos(2),
            aast::Expr_::Lvar(Box::new(aast::Lid(
                pos(2),
                oxidized::local_id::make_unscoped("$x"),
            ))),
        );
        let attrs = vec![attr(sn::user_attributes::DEPRECATED, vec![var])];
        assert_eq!(deprecated("function", &id, &attrs), None);
        // No attribute.
        assert_eq!(deprecated("function", &id, &[]), None);
    }

    fn binop_dot(lhs: nast::Expr, rhs: nast::Expr) -> nast::Expr {
        aast::Expr(
            (),
            pos(1),
            aast::Expr_::Binop(Box::new(aast::Binop {
                bop: Bop::Dot,
                lhs,
                rhs,
            })),
        )
    }
}
