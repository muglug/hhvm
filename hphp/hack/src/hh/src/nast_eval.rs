// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/nast_eval.ml`. See `hh/PORTING.md`.
//!
//! The string of an expression is bytes (`bstr::BString`), as an OCaml
//! string is.

use bstr::BString;
use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::nast;
use oxidized::pos::Pos;

/// `exception Not_static_exn of Pos.t`: this should never be exposed /
/// thrown outside of this module; translate it into a result type first.
struct NotStaticExn(Pos);

fn static_string_exn(expr: &nast::Expr) -> Result<BString, NotStaticExn> {
    match expr {
        aast::Expr(_, _, aast::Expr_::Binop(binop)) if matches!(binop.bop, Bop::Dot) => {
            let aast::Binop { bop: _, lhs, rhs } = &**binop;
            let s1 = static_string_exn(lhs)?;
            let s2 = static_string_exn(rhs)?;
            let mut s = s1;
            s.extend_from_slice(&s2);
            Ok(s)
        }
        aast::Expr(_, _, aast::Expr_::String(s)) => Ok(s.clone()),
        aast::Expr(_, p, _) => Err(NotStaticExn(p.clone())),
    }
}

pub fn static_string(expr: &nast::Expr) -> Result<BString, Pos> {
    match static_string_exn(expr) {
        Ok(s) => Ok(s),
        Err(NotStaticExn(p)) => Err(p),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn pos(start: usize) -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, "a.php".into()));
        Pos::from_lnum_bol_offset(file, (1, 0, start), (1, 0, start + 1))
    }

    fn string(start: usize, s: &str) -> nast::Expr {
        aast::Expr((), pos(start), aast::Expr_::String(s.into()))
    }

    fn binop(bop: Bop, lhs: nast::Expr, rhs: nast::Expr) -> nast::Expr {
        aast::Expr(
            (),
            pos(0),
            aast::Expr_::Binop(Box::new(aast::Binop { bop, lhs, rhs })),
        )
    }

    #[test]
    fn concatenations() {
        assert_eq!(static_string(&string(1, "a")), Ok("a".into()));
        let e = binop(
            Bop::Dot,
            string(1, "a"),
            binop(Bop::Dot, string(2, "b"), string(3, "c")),
        );
        assert_eq!(static_string(&e), Ok("abc".into()));
        // The first expression that is not a string, from the left.
        let int = |start| aast::Expr((), pos(start), aast::Expr_::Int("1".to_string()));
        let e = binop(Bop::Dot, int(4), int(5));
        assert_eq!(static_string(&e), Err(pos(4)));
        // Another operator is not a static string.
        let e = binop(Bop::Plus, string(1, "a"), string(2, "b"));
        assert_eq!(static_string(&e), Err(pos(0)));
    }
}
