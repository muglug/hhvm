// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `common/common.ml` (Hack's extensions of `Core`'s modules), as far
//! as the ported modules use it.

/// `Common.List`
pub mod list {
    /// `List.map_env_ty_err_opt`: `f` is applied to the
    /// elements from left to right, and `combine_ty_errs` gets the errors in the
    /// order the OCaml builds them: the elements are taken five at a time, the
    /// errors of each group in order and the groups from the last to the first
    /// (after 1001 groups, the errors of the rest of the elements from the last
    /// to the first, before the groups).
    pub fn map_env_ty_err_opt<E: ?Sized, X, Y, Err, Errs>(
        env: &mut E,
        xs: &[X],
        mut f: impl FnMut(&mut E, &X) -> (Option<Err>, Y),
        combine_ty_errs: impl FnOnce(Vec<Err>) -> Errs,
    ) -> (Errs, Vec<Y>) {
        // The OCaml list of errors, last element first.
        let mut rev_errs: Vec<Err> = Vec::new();
        let mut ys = Vec::with_capacity(xs.len());
        let mut rest = xs;
        let mut counter = 0;
        loop {
            if rest.is_empty() {
                break;
            }
            let (group, tail) = rest.split_at(std::cmp::min(5, rest.len()));
            let errs: Vec<Option<Err>> = group
                .iter()
                .map(|x| {
                    let (err, y) = f(env, x);
                    ys.push(y);
                    err
                })
                .collect();
            // `ty_err_opt1 :: ... :: ty_err_opt5 :: ty_err_opts`
            rev_errs.extend(errs.into_iter().rev().flatten());
            if tail.is_empty() {
                break;
            }
            if counter > 1000 {
                // `rev_map_env_ty_err_opt env ys ~f ~err:(...)`
                for x in tail {
                    let (err, y) = f(env, x);
                    ys.push(y);
                    rev_errs.extend(err);
                }
                break;
            }
            counter += 1;
            rest = tail;
        }
        rev_errs.reverse();
        (combine_ty_errs(rev_errs), ys)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `List.map_env_ty_err_opt` applies `f` from left to right and gives
    /// `combine_ty_errs` the errors of the last group of five first (as the
    /// OCaml's `aux` conses each group onto the accumulator).
    #[test]
    fn map_env_ty_err_opt_order() {
        let mut calls: Vec<i32> = vec![];
        let xs: Vec<i32> = (1..=7).collect();
        let (errs, ys) = list::map_env_ty_err_opt(
            &mut calls,
            &xs,
            |calls, x| {
                calls.push(*x);
                (Some(*x * 10), *x + 100)
            },
            |errs: Vec<i32>| errs,
        );
        assert_eq!(calls, vec![1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(ys, vec![101, 102, 103, 104, 105, 106, 107]);
        assert_eq!(errs, vec![60, 70, 10, 20, 30, 40, 50]);
    }

    #[test]
    fn map_env_ty_err_opt_orders_errors_as_ocaml() {
        // Seven elements: the errors of the second group of five first, then
        // those of the first, each group in order.
        let xs: Vec<isize> = (1..=7).collect();
        let mut seen = vec![];
        let (errs, ys) = list::map_env_ty_err_opt(
            &mut (),
            &xs,
            |_, x| {
                seen.push(*x);
                (if *x == 3 { None } else { Some(*x) }, *x * 10)
            },
            |errs| errs,
        );
        assert_eq!(seen, vec![1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(ys, vec![10, 20, 30, 40, 50, 60, 70]);
        assert_eq!(errs, vec![6, 7, 1, 2, 4, 5]);
    }

    #[test]
    fn map_env_ty_err_opt_error_order() {
        // Elements 0..=11: groups [0..4], [5..9], [10, 11]; the errors of a
        // group in order, the last group first.
        let xs: Vec<isize> = (0..12).collect();
        let mut env = ();
        let (errs, ys) = list::map_env_ty_err_opt(
            &mut env,
            &xs,
            |_, x| (if x % 2 == 0 { Some(*x) } else { None }, *x * 10),
            |errs| errs,
        );
        assert_eq!(ys, (0..12).map(|x| x * 10).collect::<Vec<_>>());
        assert_eq!(errs, vec![10, 6, 8, 0, 2, 4]);
        let (errs, ys) = list::map_env_ty_err_opt(&mut env, &[] as &[isize], |_, x| (Some(*x), *x), |e| e);
        assert!(errs.is_empty() && ys.is_empty());
        // Five elements: one group.
        let (errs, _) = list::map_env_ty_err_opt(&mut env, &[1, 2, 3, 4, 5], |_, x| (Some(*x), ()), |e| e);
        assert_eq!(errs, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn map_env_ty_err_opt_long_lists() {
        // After 1001 groups of five (and the 1002nd), the errors of the rest
        // of the elements come first, from the last to the first.
        let n = 5 * 1002 + 3;
        let xs: Vec<usize> = (0..n).collect();
        let mut env = ();
        let (errs, ys) = list::map_env_ty_err_opt(&mut env, &xs, |_, x| (Some(*x), *x), |e| e);
        assert_eq!(ys, xs);
        assert_eq!(&errs[..3], &[n - 1, n - 2, n - 3]);
        // then the groups from the last to the first
        assert_eq!(&errs[3..8], &[5 * 1001, 5 * 1001 + 1, 5 * 1001 + 2, 5 * 1001 + 3, 5 * 1001 + 4]);
        assert_eq!(&errs[errs.len() - 5..], &[0, 1, 2, 3, 4]);
    }
}
