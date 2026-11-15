// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/sys/timeout.ml`, as far as the typechecker uses it
//! (`with_timeout`, for `Typing_helpers.with_timeout`).

/// The exception `Timeout` of `with_timeout`, raised (unwound with)
/// when its deadline has passed: the `exn_id` of the call it belongs to.
pub struct Timeout(u64);

thread_local! {
    /// The deadline of the innermost `with_timeout` running on this thread,
    /// and its id (`mk_id`).
    static DEADLINE: std::cell::Cell<Option<(u64, std::time::Instant)>> =
        const { std::cell::Cell::new(None) };
    static NEXT_ID: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Where OCaml's `Timer` (`SIGALRM`) would interrupt the computation: the
/// signal handler raises `Timeout` in whatever code runs when the deadline
/// passes. Rust cannot raise from a signal handler, so the typechecker
/// checks the deadline at points it reaches regularly (each statement,
/// `Typing_debug.log_env_if_too_big`, which runs only when there is a
/// timeout) and unwinds from there.
pub fn check_timeout() {
    if let Some((id, deadline)) = DEADLINE.get() {
        if std::time::Instant::now() >= deadline {
            std::panic::resume_unwind(Box::new(Timeout(id)))
        }
    }
}

/// `with_timeout ~timeout ~on_timeout ~do_` (`on_timeout` does not get the
/// times: no caller reads them).
///
/// The function `with_timeout` executes 'do_' for at most 'timeout'
/// seconds. If the `timeout` is reached, the `on_timeout` is executed.
/// The OCaml is based on an interval timer (`SIGALRM`); here the deadline is
/// polled by [`check_timeout`], which the computation must call on a regular
/// basis.
pub fn with_timeout<B>(
    timeout: isize,
    on_timeout: impl FnOnce() -> B,
    do_: impl FnOnce() -> B,
) -> B {
    let start_time = std::time::Instant::now();
    let id = NEXT_ID.get();
    NEXT_ID.set(id + 1);
    let outer = DEADLINE.get();
    let deadline = start_time + std::time::Duration::from_secs(timeout.max(0) as u64);
    // An outer deadline that comes first still applies (OCaml's `Timer`
    // keeps every timer and fires the earliest).
    DEADLINE.set(Some(match outer {
        Some((outer_id, outer_deadline)) if outer_deadline < deadline => (outer_id, outer_deadline),
        _ => (id, deadline),
    }));
    let ret = std::panic::catch_unwind(std::panic::AssertUnwindSafe(do_));
    // Any uncaught exception will cancel the timeout
    DEADLINE.set(outer);
    match ret {
        Ok(ret) => ret,
        Err(payload) => match payload.downcast_ref::<Timeout>() {
            Some(Timeout(exn_id)) if *exn_id == id => on_timeout(),
            _ => std::panic::resume_unwind(payload),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn with_timeout_interrupts_at_a_check() {
        // `do_` runs to its end within the deadline.
        assert_eq!(with_timeout(5, || 0, || 1), 1);
        // A `do_` that does not end is interrupted at a check.
        let r = with_timeout(
            1,
            || "timeout",
            || loop {
                check_timeout();
                std::thread::sleep(std::time::Duration::from_millis(10));
            },
        );
        assert_eq!(r, "timeout");
        // The deadline is gone after.
        check_timeout();
        // Another panic goes through.
        let e = std::panic::catch_unwind(|| with_timeout(5, || 0, || panic!("boom")));
        assert!(e.is_err());
        // Nested: the outer deadline, which comes first, is the outer's.
        let r = with_timeout(
            1,
            || "outer",
            || {
                with_timeout(
                    100,
                    || "inner",
                    || loop {
                        check_timeout();
                        std::thread::sleep(std::time::Duration::from_millis(10));
                    },
                )
            },
        );
        assert_eq!(r, "outer");
    }
}
