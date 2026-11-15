// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_logic_helpers.ml`. See `hh/PORTING.md`.
//!
//! The OCaml functions thread a pair `(env, prop)`: here the environment is
//! `&mut Env` and the proposition is passed and returned by value, so
//! `(env, p) &&& f` is `and(env, p, f)`, and a continuation
//! `env -> env * TL.subtype_prop` is an `FnOnce(&mut Env) -> SubtypeProp`.
//!
//! The two infix operators have no Rust spelling:
//!
//! | OCaml | Rust |
//! |---|---|
//! | `(env, p1) &&& f` | [`and`]`(env, p1, f)` |
//! | `(env, p1) \|\|\| f` with `( \|\|\| ) ~fail` | [`or`]`(fail, env, p1, f)` |
//!
//! A chain `valid env &&& f &&& g` is
//! `let p = valid(env); let p = and(env, p, f); and(env, p, g)`.
//!
//! [`valid`] and [`invalid`] do not use the environment (the OCaml returns
//! it as it is): they take it by shared reference, and a `&mut Env` can be
//! passed as it is. `if_unsat (invalid ~fail) (env, p)` is
//! `if_unsat(|env| invalid(fail, env), env, p)`.

use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_logic as tl;

pub fn valid(_env: &Env) -> tl::SubtypeProp {
    tl::valid()
}

/// `( &&& )`
pub fn and(
    env: &mut Env,
    p1: tl::SubtypeProp,
    f: impl FnOnce(&mut Env) -> tl::SubtypeProp,
) -> tl::SubtypeProp {
    // `valid env &&& f` is `f env` (not in the OCaml, typing_logic_helpers.ml
    // `( &&& )`, which calls `get_error_if_unsat` and `TL.conj`: they give
    // `f env` too). Most subtyping chains start with `valid env`; this skips
    // the walks of both propositions.
    if tl::is_conj_nil(&p1) {
        return f(env);
    }
    match tl::get_error_if_unsat(&p1) {
        Some(ty_err_opt1) => {
            let p2 = f(env);
            match tl::get_error_if_unsat(&p2) {
                Some(ty_err_opt2) => {
                    // `Typing_error.multiple_opt (List.filter_opt [..])`
                    let ty_err_opt = match (ty_err_opt1, ty_err_opt2) {
                        (None, None) => None,
                        (Some(e), None) | (None, Some(e)) => Some(e),
                        (Some(e1), Some(e2)) => Some(typing_error::multiple(vec![e1, e2])),
                    };
                    tl::SubtypeProp::Disj(ty_err_opt, vec![])
                }
                None => p1,
            }
        }
        None => {
            let p2 = f(env);
            tl::conj(p1, p2)
        }
    }
}

pub fn if_unsat(
    f: impl FnOnce(&mut Env) -> tl::SubtypeProp,
    env: &mut Env,
    p: tl::SubtypeProp,
) -> tl::SubtypeProp {
    if tl::is_unsat(&p) { f(env) } else { p }
}

/// `( ||| )`. `fail` is anything that gives the error (an error built only
/// when it is needed, `crate::typing_subtype::prelude::subtype_env::Fail`):
/// it is not needed when `p1` is valid. The OCaml's `~fail` is an error that
/// every caller has already built; most of them are dropped (on the benchmark
/// sample 2.8M subtype errors were built and 212 reported), so building it
/// only here keeps the result and saves that work.
pub fn or(
    fail: impl Into<Option<typing_error::T>>,
    env: &mut Env,
    p1: tl::SubtypeProp,
    f: impl FnOnce(&mut Env) -> tl::SubtypeProp,
) -> tl::SubtypeProp {
    if tl::is_valid(&p1) {
        p1
    } else {
        let p2 = f(env);
        tl::disj(fail.into(), p1, p2)
    }
}

/// We *know* that the assertion is unsatisfiable
///
/// The OCaml is polymorphic in the environment (`'a -> 'a * subtype_prop`).
pub fn invalid<A: ?Sized>(fail: impl Into<Option<typing_error::T>>, _env: &A) -> tl::SubtypeProp {
    tl::invalid(fail.into())
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::path::Path;
    use std::sync::Arc;

    use oxidized::ast_defs::Tprim;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;
    use crate::typing_defs_constraints::InternalType;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::mk;
    use crate::typing_reason;

    fn env() -> Env {
        let ctx = crate::ctx::Ctx::new(Path::new("/"), Default::default()).unwrap();
        let file = Arc::new(RelativePath::make(Prefix::Root, "f.php".into()));
        crate::typing_env_types::empty(None, None, Arc::new(ctx), file, None)
    }

    /// `#n <: int`
    fn sub(n: isize) -> tl::SubtypeProp {
        tl::SubtypeProp::IsSubtype(
            false,
            InternalType::LoclType(mk((typing_reason::none(), Ty_::Tvar(n)))),
            InternalType::LoclType(mk((typing_reason::none(), Ty_::Tprim(Tprim::Tint)))),
        )
    }

    fn err() -> typing_error::T {
        typing_error::T::Multiple(vec![])
    }

    fn show(p: &tl::SubtypeProp) -> String {
        match p {
            tl::SubtypeProp::IsSubtype(_, InternalType::LoclType(ty), _) => {
                match crate::typing_defs_core::get_node(ty) {
                    Ty_::Tvar(n) => format!("#{}", n),
                    _ => "?".to_string(),
                }
            }
            tl::SubtypeProp::IsSubtype(..) | tl::SubtypeProp::AmbiguousShapeSplat(_) => {
                "?".to_string()
            }
            tl::SubtypeProp::Conj(ps) => format!(
                "Conj[{}]",
                ps.iter().map(show).collect::<Vec<_>>().join("; ")
            ),
            tl::SubtypeProp::Disj(e, ps) => format!(
                "Disj{}[{}]",
                match e {
                    None => "",
                    Some(typing_error::T::Multiple(es)) if es.len() == 2 => "!!",
                    Some(_) => "!",
                },
                ps.iter().map(show).collect::<Vec<_>>().join("; ")
            ),
        }
    }

    #[test]
    fn valid_and_invalid() {
        let mut env = env();
        assert!(tl::is_valid(&valid(&env)));
        // A `&mut Env` can be passed to both.
        let env_ = &mut env;
        assert!(tl::is_valid(&valid(env_)));
        assert!(matches!(
            tl::get_error_if_unsat(&invalid(Some(err()), env_)),
            Some(Some(_))
        ));
        assert!(matches!(
            tl::get_error_if_unsat(&invalid(None, &())),
            Some(None)
        ));
    }

    #[test]
    fn and_() {
        let mut env = env();
        let calls = Cell::new(0);
        let f = |p: tl::SubtypeProp| {
            let calls = &calls;
            move |_env: &mut Env| {
                calls.set(calls.get() + 1);
                p
            }
        };
        // Satisfiable: the conjunction.
        let p = and(&mut env, sub(1), f(sub(2)));
        assert_eq!(show(&p), "Conj[#1; #2]");
        let p = and(&mut env, tl::valid(), f(sub(2)));
        assert_eq!(show(&p), "#2");
        // Unsatisfiable, and the continuation is satisfiable: the first one
        // (the continuation is still called).
        let p = and(&mut env, invalid(Some(err()), &()), f(sub(2)));
        assert_eq!(show(&p), "Disj![]");
        // Both unsatisfiable: the errors of both, together.
        let p = and(
            &mut env,
            tl::conj(sub(1), invalid(Some(err()), &())),
            f(invalid(Some(err()), &())),
        );
        assert_eq!(show(&p), "Disj!![]");
        let p = and(&mut env, invalid(None, &()), f(invalid(Some(err()), &())));
        assert_eq!(show(&p), "Disj![]");
        let p = and(&mut env, invalid(None, &()), f(invalid(None, &())));
        assert_eq!(show(&p), "Disj[]");
        assert_eq!(calls.get(), 6);
    }

    #[test]
    fn or_() {
        let mut env = env();
        let calls = Cell::new(0);
        let f = |p: tl::SubtypeProp| {
            let calls = &calls;
            move |_env: &mut Env| {
                calls.set(calls.get() + 1);
                p
            }
        };
        // Valid: the continuation is not called.
        let p = or(Some(err()), &mut env, tl::valid(), f(sub(2)));
        assert!(tl::is_valid(&p));
        assert_eq!(calls.get(), 0);
        // Otherwise the disjunction, with `fail`.
        let p = or(Some(err()), &mut env, sub(1), f(sub(2)));
        assert_eq!(show(&p), "Disj![#1; #2]");
        let p = or(None, &mut env, invalid(None, &()), f(sub(2)));
        assert_eq!(show(&p), "Disj[#2]");
        let p = or(None, &mut env, sub(1), f(tl::valid()));
        assert!(tl::is_valid(&p));
        assert_eq!(calls.get(), 3);
    }

    #[test]
    fn if_unsat_() {
        let mut env = env();
        let calls = Cell::new(0);
        let fallback = |env: &mut Env| {
            calls.set(calls.get() + 1);
            invalid(Some(err()), env)
        };
        let p = if_unsat(fallback, &mut env, sub(1));
        assert_eq!(show(&p), "#1");
        assert_eq!(calls.get(), 0);
        let p = if_unsat(fallback, &mut env, invalid(None, &()));
        assert_eq!(show(&p), "Disj![]");
        assert_eq!(calls.get(), 1);
    }
}
