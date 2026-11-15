// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/lwt_message_queue.ml`. See `hh/PORTING.md`.
//!
//! The OCaml queue is awaited by Lwt promises of one thread; here it is
//! shared by threads (`Arc`) and [`pop`] blocks the calling thread. The
//! semantics are the OCaml's: [`push`] on a closed queue returns `false`,
//! [`pop`] returns `None` as soon as the queue is closed (even if it held
//! messages: [`close`] empties it), and the waiters of [`pop`] are served in
//! the order they started waiting (`Lwt_condition`'s queue of waiters: here
//! a ticket order).

use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::Condvar;
use std::sync::Mutex;
use std::time::Duration;
use std::time::Instant;

struct State<A> {
    messages: VecDeque<A>,
    is_open: bool,
    /// The next ticket to give a waiter of `pop`, and the ticket served next.
    next_ticket: u64,
    serving: u64,
    /// The tickets of the waiters that left before their turn.
    left: std::collections::BTreeSet<u64>,
}

pub struct Inner<A> {
    state: Mutex<State<A>>,
    /// Broadcasted whenever any of the above state changes.
    cv: Condvar,
}

/// A mutable queue containing messages of type ['a]. (`'a t`)
pub type T<A> = Arc<Inner<A>>;

/// Create a new [Lwt_message_queue.t].
pub fn create<A>() -> T<A> {
    Arc::new(Inner {
        state: Mutex::new(State {
            messages: VecDeque::new(),
            is_open: true,
            next_ticket: 0,
            serving: 0,
            left: Default::default(),
        }),
        cv: Condvar::new(),
    })
}

/// Push a message into the queue. Wakes up the task waiting to [pop] from it,
/// if any.
pub fn push<A>(queue: &T<A>, message: A) -> bool {
    let mut state = queue.state.lock().unwrap();
    if state.is_open {
        state.messages.push_back(message);
        drop(state);
        queue.cv.notify_all();
        true
    } else {
        false
    }
}

/// The result of [`pop_timeout`] when the time ran out first.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Timeout;

/// Get and remove the next message in the queue. If there are currently no
/// messages in the queue, wait until one becomes available. If the queue is or
/// becomes closed, returns [None]; otherwise returns [Some message].
///
/// `pop`: the next message, waiting for one; `None` once the queue is closed.
pub fn pop<A>(queue: &T<A>) -> Option<A> {
    match pop_until(queue, None) {
        Ok(message) => message,
        Err(Timeout) => unreachable!(),
    }
}

/// [`pop`], giving up after `timeout` (what `Lwt.pick` with a sleep, or the
/// cancellation of a pending `pop`, does in the OCaml): the waiter leaves
/// its place in the line.
pub fn pop_timeout<A>(queue: &T<A>, timeout: Duration) -> Result<Option<A>, Timeout> {
    pop_until(queue, Some(Instant::now() + timeout))
}

fn pop_until<A>(queue: &T<A>, deadline: Option<Instant>) -> Result<Option<A>, Timeout> {
    let mut state = queue.state.lock().unwrap();
    let ticket = state.next_ticket;
    state.next_ticket += 1;
    loop {
        if !state.is_open {
            leave(&mut state, ticket);
            drop(state);
            queue.cv.notify_all();
            return Ok(None);
        }
        if state.serving == ticket {
            if let Some(message) = state.messages.pop_front() {
                leave(&mut state, ticket);
                drop(state);
                queue.cv.notify_all();
                return Ok(Some(message));
            }
        }
        match deadline {
            None => state = queue.cv.wait(state).unwrap(),
            Some(deadline) => {
                let now = Instant::now();
                if now >= deadline {
                    // Leave the line: the waiters behind move up.
                    leave(&mut state, ticket);
                    drop(state);
                    queue.cv.notify_all();
                    return Err(Timeout);
                }
                state = queue.cv.wait_timeout(state, deadline - now).unwrap().0;
            }
        }
    }
}

/// The waiter with `ticket` leaves the line (served, or gone): the line
/// moves past it, and past the waiters behind it that left before their turn.
fn leave<A>(state: &mut State<A>, ticket: u64) {
    if state.serving == ticket {
        state.serving += 1;
        while state.left.remove(&state.serving) {
            state.serving += 1;
        }
    } else {
        state.left.insert(ticket);
    }
}

/// Close the message queue for further reads and writes. All messages
/// currently in the queue will be dropped. Future calls to [push] will return
/// [false], and future calls to [pop] will return [None].
///
/// Either the producer or consumer end of the queue may close it.
pub fn close<A>(queue: &T<A>) {
    let mut state = queue.state.lock().unwrap();
    state.messages.clear();
    state.is_open = false;
    drop(state);
    queue.cv.notify_all();
}

/// Whether or not the queue has any pending messages at this moment.
pub fn is_empty<A>(queue: &T<A>) -> bool {
    queue.state.lock().unwrap().messages.is_empty()
}

/// Returns the number of messages currently in the queue. If the queue is
/// closed, returns [0].
pub fn length<A>(queue: &T<A>) -> usize {
    queue.state.lock().unwrap().messages.len()
}

/// Returns whether or not a message satisfying predicate [f] exists in the
/// current queue.
pub fn exists<A>(queue: &T<A>, f: impl Fn(&A) -> bool) -> bool {
    queue.state.lock().unwrap().messages.iter().any(f)
}
