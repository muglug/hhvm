// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Utils` (`utils/core/utils.ml`). See `hh/PORTING.md`.
//!
//! The functions of `utils.ml` that the typechecker uses. The namespace
//! helpers that the `core_utils_rust` crate (`utils/core/utils.rs`) already
//! has are the ones of that crate.
//!
//! The functions that strip a prefix return a slice of their argument (as
//! every caller in this crate expects: the result usually goes straight into
//! `md_codify`); the others return owned values.

/// Callstack is simply a typed way to indicate that a string is a callstack
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Callstack(pub String);

/// `sl`: the concatenation of the strings of a list.
pub fn sl<S: AsRef<str>>(l: &[S]) -> String {
    let mut res = String::new();
    for s in l {
        res.push_str(s.as_ref());
    }
    res
}

/// Same as `fold_left2`, except that it only goes as far as the shortest of
/// both lists.
pub fn wfold_left2<Env, A, B>(
    mut f: impl FnMut(Env, &A, &B) -> Env,
    env: Env,
    l1: &[A],
    l2: &[B],
) -> Env {
    let mut env = env;
    for (x1, x2) in l1.iter().zip(l2.iter()) {
        env = f(env, x1, x2);
    }
    env
}

/// Since OCaml usually runs w/o backtraces enabled, the note makes errors
/// easier to debug.
///
/// (`raise (Invalid_argument note)`: nothing catches it.)
pub fn unsafe_opt_note<A>(note: &str, x: Option<A>) -> A {
    match x {
        None => panic!("Invalid_argument: {}", note),
        Some(x) => x,
    }
}

pub fn unsafe_opt<A>(x: Option<A>) -> A {
    unsafe_opt_note("unsafe_opt got None", x)
}

/// `\A\B\C` -> `A\B\C`
pub fn strip_ns(s: &str) -> &str {
    core_utils_rust::strip_ns(s)
}

/// A:B:C -> :A:B:C
pub fn add_xhp_ns(s: &str) -> String {
    if s.starts_with(':') {
        s.to_string()
    } else {
        format!(":{}", s)
    }
}

pub fn strip_xhp_ns(s: &str) -> &str {
    s.strip_prefix(':').unwrap_or(s)
}

/// `A\B\C` -> `\A\B\C`
pub fn add_ns(s: &str) -> String {
    core_utils_rust::add_ns(s).into_owned()
}

/// `split_ns_from_name`: the namespace part (with its trailing backslash)
/// and the name part of a name; `("\\", s)` when `s` has no backslash.
/// (Added by F4.)
pub fn split_ns_from_name(s: &str) -> (&str, &str) {
    match s.rfind('\\') {
        Some(pos) => {
            let base_name_start = pos + 1;
            (&s[..base_name_start], &s[base_name_start..])
        }
        None => ("\\", s),
    }
}

/// `\A\B\C` -> `C`
pub fn strip_all_ns(s: &str) -> &str {
    core_utils_rust::strip_all_ns(s)
}

/// `\HH\C` -> `C`, `\HH\Lib\C` -> `C`, `\A\B\C` -> `A\B\C` (added by F2)
pub fn strip_hh_lib_ns(s: &str) -> &str {
    let s = s.strip_prefix("\\HH\\Lib\\").unwrap_or(s);
    let s = s.strip_prefix("\\HH\\").unwrap_or(s);
    strip_ns(s)
}

/// `expand_namespace ns_map s` (added by F2)
pub fn expand_namespace(ns_map: &[(String, String)], s: &str) -> String {
    let (raw_ns, name) = split_ns_from_name(s);
    // Might need left backslash
    let ns = add_ns(raw_ns);
    let matching_alias = ns_map.iter().find(|(alias, _)| {
        let fixup = add_ns(alias) + "\\";
        fixup == ns
    });
    match matching_alias {
        None => add_ns(s),
        Some((_, expanded)) => add_ns(&format!("{}\\{}", expanded, name)),
    }
}

pub fn compose<A, B, C>(f: impl Fn(B) -> C, g: impl Fn(A) -> B) -> impl Fn(A) -> C {
    move |x| f(g(x))
}

/// Runs `f`, then `finally`, whether `f` returns or raises.
///
/// An exception that propagates is a panic here (`Exception.wrap`,
/// `Exception.reraise`): `finally` runs while it unwinds, and the panic then
/// goes on. An `f` that reports failure through its result (`Result`)
/// returns normally, and `finally` runs after it, as in OCaml.
pub fn try_finally<A>(f: impl FnOnce() -> A, finally: impl FnOnce()) -> A {
    let res = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(res) => res,
        Err(exn) => {
            let e = crate::exception::wrap(exn);
            finally();
            crate::exception::reraise(e)
        }
    };
    finally();
    res
}

/// We run with exception backtraces turned off for performance reasons. But
/// for some kinds of catastrophic exceptions, which we never recover from (so
/// the performance doesn't matter) we do want the backtrace. "assert false"
/// is one of such conditions.
pub fn assert_false_log_backtrace(msg: Option<&str>) -> ! {
    eprintln!("assert false with backtrace:");
    if let Some(msg) = msg {
        eprintln!("{}", msg);
    }
    eprint!("{}", crate::exception::get_current_callstack_string(100));
    panic!("Assertion failed")
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;

    #[test]
    fn namespaces() {
        // `String.chop_prefix_if_exists ~prefix:"\\"`: one backslash only.
        assert_eq!(strip_ns("\\A\\B\\C"), "A\\B\\C");
        assert_eq!(strip_ns("A\\B\\C"), "A\\B\\C");
        assert_eq!(strip_ns("\\\\A"), "\\A");
        assert_eq!(strip_ns("\\"), "");
        assert_eq!(strip_ns(""), "");
        assert_eq!(strip_xhp_ns(":foo:bar"), "foo:bar");
        assert_eq!(strip_xhp_ns("foo:bar"), "foo:bar");
        assert_eq!(strip_xhp_ns("::foo"), ":foo");
        assert_eq!(strip_xhp_ns(""), "");
        assert_eq!(add_ns("A\\B"), "\\A\\B");
        assert_eq!(add_ns("\\A\\B"), "\\A\\B");
        assert_eq!(add_ns(""), "\\");
        // `String.rindex s '\\'`: what follows the last backslash.
        assert_eq!(strip_all_ns("\\A\\B\\C"), "C");
        assert_eq!(strip_all_ns("C"), "C");
        assert_eq!(strip_all_ns("\\A\\"), "");
        assert_eq!(strip_all_ns(""), "");
    }

    #[test]
    fn lists() {
        assert_eq!(sl(&["a", "bc", "", "d"]), "abcd");
        assert_eq!(sl::<&str>(&[]), "");
        // Stops at the end of the shortest list.
        let sum = wfold_left2(|acc, x, y| acc + x * y, 0, &[1, 2, 3], &[10, 20]);
        assert_eq!(sum, 50);
        assert_eq!(unsafe_opt(Some(3)), 3);
        assert_eq!(compose(|x: i32| x + 1, |x: i32| x * 2)(5), 11);
    }

    #[test]
    #[should_panic(expected = "Invalid_argument: unsafe_opt got None")]
    fn unsafe_opt_none() {
        unsafe_opt::<()>(None)
    }

    #[test]
    fn finally_runs_once() {
        let log = RefCell::new(vec![]);
        let res = try_finally(
            || {
                log.borrow_mut().push("f");
                1
            },
            || log.borrow_mut().push("finally"),
        );
        assert_eq!(res, 1);
        assert_eq!(*log.borrow(), ["f", "finally"]);

        // When `f` raises, `finally` runs and the exception goes on.
        let log = RefCell::new(vec![]);
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            try_finally(
                || -> i32 { std::panic::panic_any("Not_found") },
                || log.borrow_mut().push("finally"),
            )
        }));
        assert_eq!(res.unwrap_err().downcast_ref::<&str>(), Some(&"Not_found"));
        assert_eq!(*log.borrow(), ["finally"]);
    }
}

/// `Utils.timestring`: `[YYYY-MM-DD HH:MM:SS.mmm]` in local time.
pub fn timestring(time: f64) -> String {
    let secs = time.floor() as libc::time_t;
    // `Unix.localtime`
    let mut tm: libc::tm = unsafe { std::mem::zeroed() };
    unsafe {
        libc::localtime_r(&secs, &mut tm);
    }
    // `Int.of_float (time *. 1000.) % 1000`: Base's `%` is never negative.
    let millis = ((time * 1000.) as i64).rem_euclid(1000);
    format!(
        "[{}-{:02}-{:02} {:02}:{:02}:{:02}.{:03}]",
        tm.tm_year + 1900,
        tm.tm_mon + 1,
        tm.tm_mday,
        tm.tm_hour,
        tm.tm_min,
        tm.tm_sec,
        millis
    )
}

/// `Utils.infimum`: binary search for the index of the last element of `arr`
/// that is smaller than `bound` (`compare elt bound < 0`). As in OCaml, a
/// one-element range is returned without testing its element (so the index
/// 0 comes back even when no element is smaller), and an empty array gives
/// `None`.
pub fn infimum<A, B>(arr: &[A], bound: &B, compare: impl Fn(&A, &B) -> isize) -> Option<usize> {
    fn binary_search<A, B>(
        arr: &[A],
        bound: &B,
        compare: &impl Fn(&A, &B) -> isize,
        low: isize,
        high: isize,
    ) -> Option<usize> {
        if low == high {
            Some(low as usize)
        } else if low > high {
            None
        } else {
            let mid = (low + high + 1) / 2;
            let test = &arr[mid as usize];
            if compare(test, bound) < 0 {
                binary_search(arr, bound, compare, mid, high)
            } else {
                binary_search(arr, bound, compare, low, mid - 1)
            }
        }
    }
    binary_search(arr, bound, &compare, 0, arr.len() as isize - 1)
}

/// `Utils.With_complete_flag` (added by F3).
pub mod with_complete_flag {
    /// `'a With_complete_flag.t`
    #[derive(Clone, Debug)]
    pub struct T<A> {
        pub is_complete: bool,
        pub value: A,
    }
}
