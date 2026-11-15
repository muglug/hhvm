// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: panics that stand for OCaml exceptions which the
//! code catches and
//! reports itself (`try ... with Failure s -> print ...`): [`catch_reported`]
//! runs a function under `catch_unwind` and keeps the panic hook from
//! writing its "thread ... panicked at ..." message to stderr for the panics
//! whose payload the caller says it reports (the OCaml writes nothing
//! there). Any other panic (a bug: it is resumed, or not caught) is printed
//! by the hook as before.

use std::any::Any;
use std::cell::RefCell;
use std::sync::Once;

type Reported = fn(&(dyn Any + Send)) -> bool;

thread_local! {
    /// The predicates of the [`catch_reported`] calls in progress on this
    /// thread, innermost last.
    static REPORTED: RefCell<Vec<Reported>> = const { RefCell::new(Vec::new()) };

    /// Where the last panic that was not printed was raised (see
    /// [`take_raise_site`]).
    static RAISE_SITE: RefCell<Option<RaiseSite>> = const { RefCell::new(None) };
}

/// Where a panic was raised: its location (`file:line:column`), and the
/// backtrace of the panicking thread there when backtraces are enabled
/// (`RUST_BACKTRACE`: `Backtrace::capture`).
pub struct RaiseSite {
    pub location: Option<String>,
    pub backtrace: std::backtrace::Backtrace,
}

/// Where the last panic of this thread was raised, if a [`catch_reported`]
/// kept it from the panic hook: what the hook would have printed, for the
/// code that reports the exception (as an OCaml backtrace is read right
/// after the exception is caught). `None` once taken, or when the last panic
/// was printed by the hook.
pub fn take_raise_site() -> Option<RaiseSite> {
    RAISE_SITE.with(|r| r.borrow_mut().take())
}

static INSTALL: Once = Once::new();

/// Wraps the current panic hook (once): a panic whose payload one of the
/// predicates in progress on this thread accepts is not printed.
fn install() {
    INSTALL.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            let payload = info.payload();
            let quiet = REPORTED
                .try_with(|r| r.borrow().iter().any(|reported| reported(payload)))
                .unwrap_or(false);
            if !quiet {
                // (No raise site: the hook prints this one.)
                let _ = RAISE_SITE.try_with(|r| *r.borrow_mut() = None);
                previous(info)
            } else {
                let site = RaiseSite {
                    location: info
                        .location()
                        .map(|l| format!("{}:{}:{}", l.file(), l.line(), l.column())),
                    backtrace: std::backtrace::Backtrace::capture(),
                };
                let _ = RAISE_SITE.try_with(|r| *r.borrow_mut() = Some(site));
            }
        }));
    })
}

/// `catch_unwind(f)`, where the panics whose payload `reported` accepts
/// (those the caller turns into the OCaml's output) are not printed by the
/// panic hook.
pub fn catch_reported<A>(reported: Reported, f: impl FnOnce() -> A) -> std::thread::Result<A> {
    install();
    REPORTED.with(|r| r.borrow_mut().push(reported));
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    REPORTED.with(|r| {
        r.borrow_mut().pop();
    });
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug)]
    struct Reported;

    #[test]
    fn a_reported_panic_is_caught_and_the_scope_ends() {
        let r = catch_reported(|p| p.is::<Reported>(), || std::panic::panic_any(Reported));
        assert!(r.unwrap_err().is::<Reported>());
        // Another payload is caught too (and printed by the hook).
        let r = catch_reported(|p| p.is::<Reported>(), || panic!("other"));
        assert_eq!(r.unwrap_err().downcast_ref::<&str>(), Some(&"other"));
        assert!(REPORTED.with(|r| r.borrow().is_empty()));
        assert_eq!(catch_reported(|_| true, || 3).unwrap(), 3);
    }

    #[test]
    fn the_raise_site_of_a_reported_panic_is_kept() {
        let _ = take_raise_site();
        let r = catch_reported(|p| p.is::<Reported>(), || std::panic::panic_any(Reported));
        assert!(r.is_err());
        let site = take_raise_site().unwrap();
        assert!(site.location.unwrap().contains("quiet_panic.rs:"));
        assert!(take_raise_site().is_none());
        // The exception, then where it was raised (as the OCaml logs an
        // exception and its backtrace: `HANDLE_CONNECTION_EXCEPTION`).
        let payload =
            catch_reported(|_| true, || std::panic::panic_any("Failure")).unwrap_err();
        let e = crate::exception::wrap_with_raise_site(payload, take_raise_site());
        let s = crate::exception::to_string(&e);
        assert!(s.starts_with("Failure\npanicked at "), "{s}");
        assert!(s.contains("quiet_panic.rs:"), "{s}");
    }
}
