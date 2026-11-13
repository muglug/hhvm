// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Counters` (`utils/counters.ml`). See `hh/PORTING.md`.
//!
//! The counters are global state in OCaml, where a worker is a process. Here
//! they are kept for each thread, like the errors of
//! `crate::diagnostics_state`: a file is checked on one thread.

use std::cell::RefCell;

use crate::telemetry;

pub mod category {
    /// Care: each of these entries adds up to telemetry in
    /// [HackEventLogger.ProfileTypeCheck.get_stats], and we should keep the
    /// number small... 5 to 10 items here are fine, but more will be a
    /// problem.
    #[allow(non_camel_case_types)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum T {
        /// This is counted every use of [Disk.cat]
        Disk_cat,
        /// This is counted every use of
        /// [Direct_decl_utils.direct_decl_parse{_and_cache}].
        /// It often includes some [Disk_cat] time.
        Direct_decl_parse,
        /// This measures every [Decl_provider.get_*] function.
        Decl_provider_get,
        /// This measures every [Ast_provider.get_ast_with_error] call, for
        /// fetching the full ASTs of the files we're typechecking.
        Ast_provider_get,
        /// This measures every [Typing_top_level] call.
        Typing_toplevel,
    }

    pub fn to_enum(category: T) -> isize {
        category as isize
    }

    pub fn of_enum(i: isize) -> Option<T> {
        match i {
            0 => Some(T::Disk_cat),
            1 => Some(T::Direct_decl_parse),
            2 => Some(T::Decl_provider_get),
            3 => Some(T::Ast_provider_get),
            4 => Some(T::Typing_toplevel),
            _ => None,
        }
    }

    pub fn show(category: T) -> String {
        match category {
            T::Disk_cat => "Disk_cat",
            T::Direct_decl_parse => "Direct_decl_parse",
            T::Decl_provider_get => "Decl_provider_get",
            T::Ast_provider_get => "Ast_provider_get",
            T::Typing_toplevel => "Typing_toplevel",
        }
        .to_string()
    }

    #[allow(non_upper_case_globals)]
    pub const count: isize = 5;
}

pub type TimeInSec = f64;

#[derive(Clone, Copy, Debug, PartialEq)]
struct Counter {
    /// how many times did 'count' get called?
    count: isize,
    /// cumulative duration of all calls to 'count'
    time: TimeInSec,
}

const EMPTY: Counter = Counter { count: 0, time: 0. };

/// here we store each individual counter.
#[derive(Clone, Debug, PartialEq)]
pub struct T(Vec<Counter>);

fn create() -> T {
    T(vec![EMPTY; category::count as usize])
}

thread_local! {
    static COUNTERS: RefCell<T> = RefCell::new(create());
}

pub fn restore_state(new_state: T) {
    COUNTERS.with(|counters| *counters.borrow_mut() = new_state)
}

/// state is global and mutable. This function resets it, and returns the
/// previous state. You should 'restore_state' when done, in case your caller
/// had been doing their own count.
pub fn reset() -> T {
    COUNTERS.with(|counters| std::mem::replace(&mut *counters.borrow_mut(), create()))
}

fn get_counter(category: category::T) -> Counter {
    COUNTERS.with(|counters| counters.borrow().0[category::to_enum(category) as usize])
}

fn set_counter(category: category::T, counts: Counter) {
    COUNTERS.with(|counters| {
        counters.borrow_mut().0[category::to_enum(category) as usize] = counts
    })
}

/// `Unix.gettimeofday ()`
fn gettimeofday() -> f64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_secs_f64(),
        Err(e) => -e.duration().as_secs_f64(),
    }
}

/// Increment the counter for the category by one, time the function and add
/// the duration to the total duration for the category.
pub fn count<A>(category: category::T, f: impl FnOnce() -> A) -> A {
    let tally = get_counter(category);
    let start_time = gettimeofday();
    crate::utils::try_finally(f, || {
        set_counter(
            category,
            Counter {
                count: tally.count + 1,
                time: tally.time + gettimeofday() - start_time,
            },
        )
    })
}

pub fn read_time(category: category::T) -> TimeInSec {
    get_counter(category).time
}

pub fn get_counters() -> telemetry::T {
    let telemetry_of_counter = |counter: Counter| {
        let t = telemetry::create();
        let t = telemetry::int_("count", counter.count, t);
        telemetry::duration(None, 0., Some(counter.time), t)
    };
    let counters = COUNTERS.with(|counters| counters.borrow().clone());
    let mut telemetry = telemetry::create();
    for (i, counter) in counters.0.iter().enumerate() {
        let category = match category::of_enum(i as isize) {
            Some(cat) => cat,
            None => panic!("WrongEnum"),
        };
        telemetry = telemetry::object_(
            &category::show(category),
            telemetry_of_counter(*counter),
            telemetry,
        );
    }
    telemetry
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counting() {
        let saved = reset();
        assert_eq!(count(category::T::Typing_toplevel, || 1 + 1), 2);
        count(category::T::Typing_toplevel, || ());
        count(category::T::Disk_cat, || ());
        assert_eq!(get_counter(category::T::Typing_toplevel).count, 2);
        assert_eq!(get_counter(category::T::Disk_cat).count, 1);
        assert_eq!(get_counter(category::T::Ast_provider_get), EMPTY);
        assert!(read_time(category::T::Typing_toplevel) >= 0.);

        // The count of the outer call replaces what the inner call counted
        // for the same category: the tally is read before `f` runs.
        let before = reset();
        count(category::T::Disk_cat, || count(category::T::Disk_cat, || ()));
        assert_eq!(get_counter(category::T::Disk_cat).count, 1);
        restore_state(before);
        assert_eq!(get_counter(category::T::Typing_toplevel).count, 2);

        // The counter is updated when `f` raises, too.
        let res = std::panic::catch_unwind(|| {
            count(category::T::Ast_provider_get, || -> () { std::panic::panic_any(1) })
        });
        assert!(res.is_err());
        assert_eq!(get_counter(category::T::Ast_provider_get).count, 1);
        restore_state(saved);
    }

    #[test]
    fn telemetry_of_counters() {
        let saved = reset();
        restore_state(T(vec![
            Counter { count: 1, time: 0.5 },
            EMPTY,
            EMPTY,
            EMPTY,
            Counter { count: 3, time: 2.0019 },
        ]));
        assert_eq!(
            telemetry::to_string(None, &get_counters()),
            concat!(
                r#"{"Disk_cat":{"count":1,"duration":500},"#,
                r#""Direct_decl_parse":{"count":0,"duration":0},"#,
                r#""Decl_provider_get":{"count":0,"duration":0},"#,
                r#""Ast_provider_get":{"count":0,"duration":0},"#,
                r#""Typing_toplevel":{"count":3,"duration":2001}}"#
            )
        );
        restore_state(saved);
    }
}
