// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the `Eval_result` module of `typing/typing_error_utils.ml`.
//! See `mod.rs`.
//!
//! The OCaml signature keeps the type abstract (only `empty`, `single`,
//! `multiple`, `union`, `intersect` and `of_option` build values), so the
//! constructors are private here too.

/// `'a Eval_result.t`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct T<A>(Repr<A>);

#[derive(Clone, Debug, Eq, PartialEq)]
enum Repr<A> {
    Empty,
    Single(A),
    Multiple(Vec<Repr<A>>),
    Union(Vec<Repr<A>>),
    Intersect(Vec<Repr<A>>),
}

fn reprs<A>(xs: Vec<T<A>>) -> Vec<Repr<A>> {
    xs.into_iter().map(|T(x)| x).collect()
}

fn multiple_repr<A>(xs: Vec<Repr<A>>) -> Repr<A> {
    if xs.is_empty() {
        Repr::Empty
    } else {
        Repr::Multiple(xs)
    }
}

fn union_repr<A>(xs: Vec<Repr<A>>) -> Repr<A> {
    if xs.is_empty() {
        Repr::Empty
    } else {
        Repr::Union(xs)
    }
}

fn intersect_repr<A>(xs: Vec<Repr<A>>) -> Repr<A> {
    if xs.is_empty() {
        Repr::Empty
    } else {
        Repr::Intersect(xs)
    }
}

pub fn empty<A>() -> T<A> {
    T(Repr::Empty)
}

pub fn single<A>(a: A) -> T<A> {
    T(Repr::Single(a))
}

pub fn multiple<A>(xs: Vec<T<A>>) -> T<A> {
    T(multiple_repr(reprs(xs)))
}

pub fn union<A>(xs: Vec<T<A>>) -> T<A> {
    T(union_repr(reprs(xs)))
}

pub fn intersect<A>(xs: Vec<T<A>>) -> T<A> {
    T(intersect_repr(reprs(xs)))
}

pub fn of_option<A>(x: Option<A>) -> T<A> {
    match x {
        Some(x) => T(Repr::Single(x)),
        None => T(Repr::Empty),
    }
}

pub fn map<A, B>(t: T<A>, mut f: impl FnMut(A) -> B) -> T<B> {
    fn aux<A, B>(t: Repr<A>, f: &mut dyn FnMut(A) -> B) -> Repr<B> {
        match t {
            Repr::Empty => Repr::Empty,
            Repr::Single(x) => Repr::Single(f(x)),
            Repr::Multiple(xs) => Repr::Multiple(xs.into_iter().map(|x| aux(x, f)).collect()),
            Repr::Union(xs) => Repr::Union(xs.into_iter().map(|x| aux(x, f)).collect()),
            Repr::Intersect(xs) => Repr::Intersect(xs.into_iter().map(|x| aux(x, f)).collect()),
        }
    }
    T(aux(t.0, &mut f))
}

pub fn bind<A, B>(t: T<A>, mut f: impl FnMut(A) -> T<B>) -> T<B> {
    fn aux<A, B>(t: Repr<A>, f: &mut dyn FnMut(A) -> T<B>) -> Repr<B> {
        match t {
            Repr::Empty => Repr::Empty,
            Repr::Single(x) => f(x).0,
            Repr::Multiple(xs) => Repr::Multiple(xs.into_iter().map(|x| aux(x, f)).collect()),
            Repr::Union(xs) => Repr::Union(xs.into_iter().map(|x| aux(x, f)).collect()),
            Repr::Intersect(xs) => Repr::Intersect(xs.into_iter().map(|x| aux(x, f)).collect()),
        }
    }
    T(aux(t.0, &mut f))
}

/// `f` is given each element by value (the OCaml callers pass
/// `Diagnostics.add_diagnostic`, which keeps it).
pub fn iter<A>(t: T<A>, mut f: impl FnMut(A)) {
    fn aux<A>(t: Repr<A>, f: &mut dyn FnMut(A)) {
        match t {
            Repr::Empty => {}
            Repr::Single(x) => f(x),
            Repr::Multiple(xs) | Repr::Union(xs) | Repr::Intersect(xs) => {
                for x in xs {
                    aux(x, f)
                }
            }
        }
    }
    aux(t.0, &mut f)
}

fn is_suppressed<A>(t: &Repr<A>, p: &dyn Fn(&A) -> bool) -> bool {
    match t {
        Repr::Intersect(xs) => xs.iter().any(|x| is_suppressed(x, p)),
        Repr::Multiple(xs) | Repr::Union(xs) => xs.iter().all(|x| is_suppressed(x, p)),
        Repr::Empty => false,
        Repr::Single(x) => p(x),
    }
}

pub fn suppress_intersection<A>(t: T<A>, is_suppressed_: impl Fn(&A) -> bool) -> T<A> {
    fn aux<A>(t: Repr<A>, p: &dyn Fn(&A) -> bool) -> Repr<A> {
        match t {
            Repr::Intersect(xs) => auxs(xs, p),
            Repr::Multiple(xs) => multiple_repr(xs.into_iter().map(|x| aux(x, p)).collect()),
            Repr::Union(xs) => union_repr(xs.into_iter().map(|x| aux(x, p)).collect()),
            Repr::Empty | Repr::Single(_) => t,
        }
    }
    // `auxs acc xs`: the first suppressed member replaces the intersection;
    // if there is none, the members are kept as they are.
    fn auxs<A>(xs: Vec<Repr<A>>, p: &dyn Fn(&A) -> bool) -> Repr<A> {
        let mut acc = Vec::with_capacity(xs.len());
        for next in xs {
            if is_suppressed(&next, p) {
                return aux(next, p);
            } else {
                acc.push(next)
            }
        }
        intersect_repr(acc)
    }
    T(aux(t.0, &is_suppressed_))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn collect<A: Clone>(t: &T<A>) -> Vec<A> {
        let mut out = vec![];
        iter(t.clone(), |x| out.push(x));
        out
    }

    #[test]
    fn smart_constructors() {
        assert_eq!(multiple::<i32>(vec![]), empty());
        assert_eq!(union::<i32>(vec![]), empty());
        assert_eq!(intersect::<i32>(vec![]), empty());
        assert_eq!(of_option(Some(1)), single(1));
        assert_eq!(of_option::<i32>(None), empty());
        assert_ne!(multiple(vec![single(1)]), union(vec![single(1)]));
        assert_ne!(multiple(vec![single(1)]), single(1));
    }

    #[test]
    fn map_bind_iter() {
        let t = multiple(vec![
            single(1),
            union(vec![single(2), empty(), intersect(vec![single(3), single(4)])]),
        ]);
        assert_eq!(collect(&t), vec![1, 2, 3, 4]);
        // `map` keeps the shape and applies `f` from left to right.
        let mut seen = vec![];
        let mapped = map(t.clone(), |x| {
            seen.push(x);
            x * 10
        });
        assert_eq!(seen, vec![1, 2, 3, 4]);
        assert_eq!(
            mapped,
            multiple(vec![
                single(10),
                union(vec![
                    single(20),
                    empty(),
                    intersect(vec![single(30), single(40)])
                ]),
            ])
        );
        // `bind` does not flatten or drop the empty results.
        let bound = bind(t, |x| {
            if x % 2 == 0 {
                empty()
            } else {
                multiple(vec![single(x), single(-x)])
            }
        });
        assert_eq!(
            bound,
            multiple(vec![
                multiple(vec![single(1), single(-1)]),
                union(vec![
                    empty(),
                    empty(),
                    intersect(vec![multiple(vec![single(3), single(-3)]), empty()])
                ]),
            ])
        );
        assert_eq!(collect(&bound), vec![1, -1, 3, -3]);
    }

    #[test]
    fn suppress_intersection_picks_first_suppressed() {
        let odd = |x: &i32| x % 2 == 1;
        // No member suppressed: unchanged.
        let t = intersect(vec![single(2), single(4)]);
        assert_eq!(suppress_intersection(t.clone(), odd), t);
        // The first suppressed member replaces the intersection.
        let t = intersect(vec![single(2), single(3), single(5)]);
        assert_eq!(suppress_intersection(t, odd), single(3));
        // A union is suppressed only if all its members are; a nested
        // intersection if any is.
        let t = intersect(vec![
            union(vec![single(1), single(2)]),
            multiple(vec![single(1), intersect(vec![single(6), single(7)])]),
            single(9),
        ]);
        assert_eq!(
            suppress_intersection(t, odd),
            multiple(vec![single(1), single(7)])
        );
        // Outside an intersection nothing is removed, suppressed or not.
        let t = union(vec![single(1), multiple(vec![single(3), single(2)])]);
        assert_eq!(suppress_intersection(t.clone(), odd), t);
        // The members before a suppressed one are not rewritten themselves
        // when none is suppressed (`auxs` keeps them as they are).
        let t = intersect(vec![
            single(2),
            union(vec![intersect(vec![single(1), single(8)]), single(4)]),
        ]);
        assert_eq!(suppress_intersection(t.clone(), odd), t);
    }
}
