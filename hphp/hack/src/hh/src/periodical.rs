// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the `Periodical` module of `server/server_idle.ml` (`:20-78`):
//! callbacks run every so many seconds by the idle loop, and its clock
//! (`Unix.time`), which tests can set.
//!
//! Owned by **SRV** (plan §3.1).

#![allow(non_upper_case_globals)]

use std::sync::Mutex;

use crate::server_env::Env;

pub const always: f64 = 0.0;
pub const one_second: f64 = 1.0;
pub const one_minute: f64 = 60.0;
pub const one_hour: f64 = 3600.0;
pub const one_day: f64 = 86400.0;
pub const one_week: f64 = 604800.0;

/// A job: `env:Server_env.env -> Server_env.env`.
pub type Job = Box<dyn FnMut(Env) -> Env + Send>;

/// `callback`: the seconds left before the job runs (and its period).
pub enum Callback {
    Periodic(f64, f64, Job),
    Once(f64, Job),
}

/// The time tests set instead of the system's (see [`set_time_for_test`]).
static FAKE_TIME: Mutex<Option<f64>> = Mutex::new(None);

/// `Unix.time ()`: the seconds since the epoch, a whole number.
pub fn time() -> f64 {
    match *FAKE_TIME.lock().unwrap_or_else(|e| e.into_inner()) {
        Some(t) => t,
        None => crate::rt::ocaml_unix::gettimeofday().floor(),
    }
}

/// Makes [`time`] return `t` (or the system's time again with `None`).
pub fn set_time_for_test(t: Option<f64>) {
    *FAKE_TIME.lock().unwrap_or_else(|e| e.into_inner()) = t
}

struct State {
    /// `callback_list`: the one registered last first.
    callback_list: Vec<Callback>,
    /// `last_call`
    last_call: Option<f64>,
}

static STATE: Mutex<State> = Mutex::new(State {
    callback_list: vec![],
    last_call: None,
});

fn lock() -> std::sync::MutexGuard<'static, State> {
    STATE.lock().unwrap_or_else(|e| e.into_inner())
}

/// `last_call = ref (Unix.time ())`, evaluated when the OCaml module is
/// initialised, at the start of the program: the server calls this when it
/// starts.
pub fn init_last_call() {
    let mut state = lock();
    if state.last_call.is_none() {
        state.last_call = Some(time());
    }
}

/// Check if any callback is due and run those.
pub fn check(env: Env) -> Env {
    let current = time();
    // The callbacks are taken out while they run (a job may register
    // another).
    let (delta, callbacks) = {
        let mut state = lock();
        let last_call = state.last_call.unwrap_or(current);
        state.last_call = Some(current);
        (current - last_call, std::mem::take(&mut state.callback_list))
    };
    let mut env = env;
    let mut kept = Vec::with_capacity(callbacks.len());
    for callback in callbacks {
        match callback {
            Callback::Periodic(mut seconds_left, period, mut job) => {
                seconds_left -= delta;
                if seconds_left < 0.0 {
                    env = job(env);
                }
                if seconds_left < 0.0 {
                    seconds_left = period;
                }
                kept.push(Callback::Periodic(seconds_left, period, job));
            }
            Callback::Once(mut seconds_left, mut job) => {
                seconds_left -= delta;
                if seconds_left < 0.0 {
                    env = job(env);
                }
            }
        }
    }
    let mut state = lock();
    // Callbacks registered while the jobs ran go first.
    let mut registered = std::mem::take(&mut state.callback_list);
    registered.extend(kept);
    state.callback_list = registered;
    env
}

/// `register_callback X Y`: registers a new callback Y called every X
/// seconds. The time is an approximation, don't expect it to be supper
/// accurate. More or less 1 sec is a more or less what you can expect.
/// More or less 30 secs if the server is busy.
pub fn register_callback(cb: Callback) {
    init_last_call();
    lock().callback_list.insert(0, cb)
}

/// Removes every callback (tests).
pub fn clear_for_test() {
    let mut state = lock();
    state.callback_list.clear();
    state.last_call = None;
}
