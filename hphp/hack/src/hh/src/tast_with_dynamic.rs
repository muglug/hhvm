// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tast_with_dynamic.ml`. See `hh/PORTING.md`.
//!
//! `[@@deriving eq, hash, show]`: [`equal`] (and `PartialEq`/`Eq`), `Hash`,
//! and the printers [`pp`] and [`show`] of `ppx_deriving.show` (laid out by
//! `crate::format`, as OCaml's `Format`; `Debug` is only for Rust).
//!
//! OCaml evaluates the fields of a record from the last one to the first:
//! the functions below apply `f` to `under_dynamic_assumptions` before
//! `under_normal_assumptions`, as OCaml does (it matters when `f` has an
//! effect).

use crate::format;
use crate::format::Formatter;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct T<A> {
    pub under_normal_assumptions: A,
    pub under_dynamic_assumptions: Option<A>,
}

/// `[@@deriving show]`: `pp poly_a fmt x`. The record is `"@[<2>{ "`, the
/// fields separated by `";@ "`, `"@ }@]"`; a field is `"@[%s =@ "`, its
/// value, `"@]"`, and the first one is qualified by the module
/// (`with_path`). An option is `None` or `(Some x)`.
pub fn pp<A>(mut poly_a: impl FnMut(&mut Formatter, &A), fmt: &mut Formatter, x: &T<A>) {
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "{ ");
    format::pp_open_box(fmt, 0);
    format::pp_print_string(fmt, "Tast_with_dynamic.under_normal_assumptions");
    format::pp_print_string(fmt, " =");
    format::pp_print_space(fmt);
    poly_a(fmt, &x.under_normal_assumptions);
    format::pp_close_box(fmt);
    format::pp_print_string(fmt, ";");
    format::pp_print_space(fmt);
    format::pp_open_box(fmt, 0);
    format::pp_print_string(fmt, "under_dynamic_assumptions");
    format::pp_print_string(fmt, " =");
    format::pp_print_space(fmt);
    match &x.under_dynamic_assumptions {
        None => format::pp_print_string(fmt, "None"),
        Some(x) => {
            format::pp_print_string(fmt, "(Some ");
            poly_a(fmt, x);
            format::pp_print_string(fmt, ")");
        }
    }
    format::pp_close_box(fmt);
    format::pp_print_space(fmt);
    format::pp_print_string(fmt, "}");
    format::pp_close_box(fmt);
}

/// `[@@deriving show]`: `Format.asprintf "%a" (pp poly_a) x`
pub fn show<A>(poly_a: impl FnMut(&mut Formatter, &A), x: &T<A>) -> String {
    format::asprintf(|fmt| pp(poly_a, fmt, x))
}

/// `[@@deriving eq]`
pub fn equal<A>(mut equal_a: impl FnMut(&A, &A) -> bool, x: &T<A>, y: &T<A>) -> bool {
    equal_a(&x.under_normal_assumptions, &y.under_normal_assumptions)
        && match (&x.under_dynamic_assumptions, &y.under_dynamic_assumptions) {
            (None, None) => true,
            (Some(x), Some(y)) => equal_a(x, y),
            (None, Some(_)) | (Some(_), None) => false,
        }
}

pub fn mk_without_dynamic<A>(under_normal_assumptions: A) -> T<A> {
    T {
        under_normal_assumptions,
        under_dynamic_assumptions: None,
    }
}

pub fn map<A, B>(mut f: impl FnMut(A) -> B, x: T<A>) -> T<B> {
    let T {
        under_normal_assumptions,
        under_dynamic_assumptions,
    } = x;
    let under_dynamic_assumptions = under_dynamic_assumptions.map(&mut f);
    let under_normal_assumptions = f(under_normal_assumptions);
    T {
        under_normal_assumptions,
        under_dynamic_assumptions,
    }
}

pub fn combine<A>(mut f: impl FnMut(A, A) -> A, x: T<A>, y: T<A>) -> T<A> {
    let under_dynamic_assumptions = match (x.under_dynamic_assumptions, y.under_dynamic_assumptions)
    {
        (None, None) => None,
        (Some(x), None) => Some(x),
        (None, Some(y)) => Some(y),
        (Some(x), Some(y)) => Some(f(x, y)),
    };
    let under_normal_assumptions = f(x.under_normal_assumptions, y.under_normal_assumptions);
    T {
        under_normal_assumptions,
        under_dynamic_assumptions,
    }
}

pub fn all<A>(x: T<A>) -> Vec<A> {
    let T {
        under_normal_assumptions,
        under_dynamic_assumptions,
    } = x;
    match under_dynamic_assumptions {
        None => vec![under_normal_assumptions],
        Some(under_dynamic_assumptions) => {
            vec![under_normal_assumptions, under_dynamic_assumptions]
        }
    }
}

/// `combine ~f:( @ ) xs ys`
pub fn append<A>(xs: T<Vec<A>>, ys: T<Vec<A>>) -> T<Vec<A>> {
    combine(
        |mut xs, ys| {
            xs.extend(ys);
            xs
        },
        xs,
        ys,
    )
}

pub fn cons<A>(x: T<A>, xs: T<Vec<A>>) -> T<Vec<A>> {
    append(map(|x| vec![x], x), xs)
}

/// `List.fold_right ~f:cons ~init:(mk_without_dynamic []) xs`: the normal
/// TASTs in order, and the dynamic ones that exist in order (`None` if there
/// are none). Built in one pass (consing in front of a `Vec` would move the
/// whole accumulator for each element).
pub fn collect<A>(xs: Vec<T<A>>) -> T<Vec<A>> {
    let mut under_normal_assumptions = Vec::with_capacity(xs.len());
    let mut under_dynamic_assumptions: Option<Vec<A>> = None;
    for x in xs {
        under_normal_assumptions.push(x.under_normal_assumptions);
        if let Some(d) = x.under_dynamic_assumptions {
            under_dynamic_assumptions.get_or_insert_with(Vec::new).push(d)
        }
    }
    T {
        under_normal_assumptions,
        under_dynamic_assumptions,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn both(n: isize, d: isize) -> T<isize> {
        T {
            under_normal_assumptions: n,
            under_dynamic_assumptions: Some(d),
        }
    }

    #[test]
    fn map_applies_to_dynamic_first() {
        let mut seen = vec![];
        let x = map(
            |n| {
                seen.push(n);
                n * 10
            },
            both(1, 2),
        );
        assert_eq!(seen, vec![2, 1]);
        assert_eq!(x, both(10, 20));
        assert_eq!(map(|n: isize| n + 1, mk_without_dynamic(1)), mk_without_dynamic(2));
    }

    #[test]
    fn combine_and_all() {
        let c = combine(|a, b| a - b, both(5, 7), mk_without_dynamic(2));
        assert_eq!(c, both(3, 7));
        let c = combine(|a, b| a - b, mk_without_dynamic(5), both(2, 1));
        assert_eq!(c, both(3, 1));
        let c = combine(|a, b| a - b, both(5, 7), both(2, 1));
        assert_eq!(c, both(3, 6));
        assert_eq!(all(both(1, 2)), vec![1, 2]);
        assert_eq!(all(mk_without_dynamic(1)), vec![1]);
        assert!(equal(|a, b| a == b, &both(1, 2), &both(1, 2)));
        assert!(!equal(|a, b| a == b, &both(1, 2), &mk_without_dynamic(1)));
    }

    #[test]
    fn collect_keeps_order() {
        let c = collect(vec![both(1, 10), mk_without_dynamic(2), both(3, 30)]);
        assert_eq!(c.under_normal_assumptions, vec![1, 2, 3]);
        assert_eq!(c.under_dynamic_assumptions, Some(vec![10, 30]));
        let c = collect(vec![mk_without_dynamic(1), mk_without_dynamic(2)]);
        assert_eq!(c.under_dynamic_assumptions, None);
        let c: T<Vec<isize>> = collect(vec![]);
        assert_eq!(c, mk_without_dynamic(vec![]));
    }

    fn pp_int(fmt: &mut Formatter, n: &isize) {
        format::pp_print_string(fmt, &n.to_string())
    }

    #[test]
    fn show_as_ppx_deriving() {
        assert_eq!(
            show(pp_int, &mk_without_dynamic(1)),
            "{ Tast_with_dynamic.under_normal_assumptions = 1;\n  under_dynamic_assumptions = None }"
        );
        assert_eq!(
            show(pp_int, &both(1, 2)),
            "{ Tast_with_dynamic.under_normal_assumptions = 1;\n  under_dynamic_assumptions = (Some 2) }"
        );
    }
}
