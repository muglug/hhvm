// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_spinner.ml`. See `hh/PORTING.md`.
//!
//! The spinner is global state, as in OCaml (`state`, `animator`). OCaml's
//! never-ending Lwt loops (`animate`, the heartbeat) are threads here; the
//! state and the writes to stderr are under one lock, so the invariant holds
//! for them too ("whatever this current state implies is reflected in
//! stderr"), and a [`report`] of `None` hides the spinner before its caller
//! prints anything.
//!
//! `Tty.print_clear_line stderr` and `Tty.eprintf` (write only when stderr is
//! a terminal) are not in `crate::tty` yet: they are transliterated below,
//! private, and should move there. `Hack_event_logger.spinner_heartbeat` and
//! `spinner_change` are no-ops in the OSS build
//! (`stubs/logging/hack_event_logger.ml`); `Hh_logger.log` is
//! `crate::hh_logger::log`.

use std::sync::LazyLock;
use std::sync::Mutex;
use std::sync::MutexGuard;

use crate::hh_logger;
use crate::rt::ocaml_unix;

const ASCII_CHARS: [&str; 4] = ["-", "\\", "|", "/"];

/// Some terminals display the emoji using only one column, even though they
/// may take up two columns, and put the cursor immediately after it in an
/// illegible manner. We append an extra space to separate the cursor from the emoji.
const EMOJI_CHARS: [&str; 4] = [
    "\u{1F621} ", // Angry Face
    "\u{1F602} ", // Face With Tears of Joy
    "\u{1F914} ", // Thinking Face
    "\u{1F4AF} ", // Hundred Points
];

#[derive(Clone, Debug, PartialEq)]
enum Message {
    /// There has not yet been a call to [report (Some s)], so there's nothing to show
    Init,
    Message {
        /// This reflects the most recent call to [report (Some text)].
        /// It is displayed as "hh_server is busy: [<s>] <spinner>".
        text: String,
        /// This is true when [report None] has been called more recently than [report Some].
        /// It means that the text won't be displayed on stderr.
        /// (However, the text is still used for heartbeat and logging).
        is_hidden: bool,
        /// the time of the oldest [report (Some text)] with no other [report (Some other_text)] since then.
        start_time: f64,
    },
}

#[derive(Clone, Debug, PartialEq)]
struct State {
    message: Message,
    /// should this be displayed on stderr?
    to_stderr: bool,
    /// do we use emoji_chars or ascii_chars?
    angery_reaccs_only: bool,
    /// which of the four chars is used as spinner
    index: usize,
}

/// The current state of the spinner. Invariant: whatever this current state implies
/// is reflected in stderr -- either some message, or nothing.
fn state() -> MutexGuard<'static, State> {
    static STATE: Mutex<State> = Mutex::new(State {
        message: Message::Init,
        to_stderr: false,
        angery_reaccs_only: false,
        index: 0,
    });
    STATE.lock().unwrap_or_else(|e| e.into_inner())
}

/// For telemetry purposes, this is the most recent non-None report,
/// and how long since it was first reported.
pub fn get_latest_report() -> Option<(String, f64)> {
    let now = ocaml_unix::gettimeofday();
    match &state().message {
        Message::Message {
            text,
            is_hidden: false,
            start_time,
        } => Some((text.clone(), now - start_time)),
        Message::Message {
            text,
            is_hidden: true,
            start_time,
        } => Some((format!("[hidden] {}", text), now - start_time)),
        Message::Init => None,
    }
}

/// Used so that when we Hh_logger.log a spinner change, we can show wall-time.
/// (OCaml computes it when the program starts; here when it is first read.)
fn start_time() -> f64 {
    static START_TIME: LazyLock<f64> = LazyLock::new(ocaml_unix::gettimeofday);
    *START_TIME
}

/// Whether spinner changes are written to Hh_logger: not when
/// [HH_DISABLE_SPINNER_LOGGING=1]. (OCaml reads the variable when the program
/// starts; here when it is first needed.)
fn log_spinner() -> bool {
    static LOG_SPINNER: LazyLock<bool> = LazyLock::new(|| {
        let var = std::env::var("HH_DISABLE_SPINNER_LOGGING").ok();
        match var.as_deref() {
            Some("1") => false,
            _ => true,
        }
    });
    *LOG_SPINNER
}

/// The caller should invoke [start_heartbeat_telemetry ()] once, as close as possible
/// to process start. From this point until process termination, it will log once
/// a second to HackEventLogger what the latest non-None report is.
/// (It's not called automatically because sometimes the startup path might determine
/// that it doesn't want heartbeats.
pub fn start_heartbeat_telemetry() {
    let _future = std::thread::Builder::new()
        .name("spinner heartbeat".to_string())
        .spawn(|| {
            let mut n: isize = 1;
            loop {
                std::thread::sleep(std::time::Duration::from_secs(1));
                // `Hack_event_logger.spinner_heartbeat n ~spinner:(get_latest_report ())`:
                // a no-op in the OSS build.
                let _heartbeat = (n, get_latest_report());
                n += 1;
            }
        });
}

/// This updates stderr to reflect new_state. This might involve clearing
/// the old stderr (if there was anything on it), and displaying a new thing
/// on stderr (if needed).
fn update_stderr(old_state: &State, new_state: &State) {
    let was_present = match &old_state.message {
        Message::Message {
            is_hidden: false, ..
        } if old_state.to_stderr => true,
        _ => false,
    };
    if was_present {
        crate::tty::print_clear_line();
    }
    match &new_state.message {
        Message::Message {
            is_hidden: false,
            text,
            ..
        } if new_state.to_stderr => {
            let chars = if new_state.angery_reaccs_only {
                EMOJI_CHARS
            } else {
                ASCII_CHARS
            };
            let spinner = chars[new_state.index];
            crate::tty::eprintf(&format!("hh_server is busy: [{}] {}", text, spinner));
        }
        _ => {}
    }
}

/// Never-ending background process to update the spinner on stderr once a second.
/// This is kicked off by the first time someone calls [report].
fn animate() {
    loop {
        std::thread::sleep(std::time::Duration::from_secs(1));
        let mut state = state();
        let new_state = State {
            index: (state.index + 1) % 4,
            ..state.clone()
        };
        update_stderr(&state, &new_state);
        *state = new_state;
    }
}

/// Mutable field so that [report] knows whether it needs to kick off [animate] in the background.
fn animator() -> MutexGuard<'static, Option<std::thread::JoinHandle<()>>> {
    static ANIMATOR: Mutex<Option<std::thread::JoinHandle<()>>> = Mutex::new(None);
    ANIMATOR.lock().unwrap_or_else(|e| e.into_inner())
}

/// [report ~to_stderr ~angery_reaccs_only message_opt] is used to report progress:
/// * Heartbeat: if [message_opt] is [Some] then all subsequent heartbeats will report
///   this [message_opt] to telemetry, at least until the next time [report] is invoked
/// * Hh_logger: if [message_opt] is [Some], and differs from what was previously reported,
///   then it will be written to Hh_logger i.e. to `$(hh --client-logname)`, unless
///   [HH_DISABLE_SPINNER_LOGGING=1] is set at process start.
/// * Stderr: if [to_stderr] is true and [message_opt] is [Some] then it will be displayed
///   on stderr with an animated spinner (which continues to animate automatically, even if
///   you don't call [report] again).
/// * Use [message_opt=None] to erase the spinner from stderr. This won't be written to the log.
///   It won't affect future heartbeats, nor [get_latest_report]. The assumption is that
///   if someone erases the spinner, they do so only temporarily.
pub fn report(to_stderr: bool, angery_reaccs_only: bool, next: Option<String>) {
    {
        let mut animator = animator();
        if animator.is_none() {
            *animator = std::thread::Builder::new()
                .name("spinner".to_string())
                .spawn(animate)
                .ok();
        }
    }
    let mut state = state();
    let message = match (&state.message, next) {
        (
            Message::Message {
                text: prev,
                start_time,
                ..
            },
            Some(next),
        ) if *prev == next => {
            // text is unchanged. But if it was hidden before, now let it be shown
            Message::Message {
                text: next,
                is_hidden: false,
                start_time: *start_time,
            }
        }
        (_, Some(next)) => {
            // text has changed
            if log_spinner() {
                hh_logger::log(&format!(
                    "spinner {:.1}s: [{}]",
                    ocaml_unix::gettimeofday() - start_time(),
                    next
                ));
            }
            // `Hack_event_logger.spinner_change ~spinner:(get_latest_report ())
            // ~next`: a no-op in the OSS build.
            Message::Message {
                text: next,
                is_hidden: false,
                start_time: ocaml_unix::gettimeofday(),
            }
        }
        (
            Message::Message {
                text, start_time, ..
            },
            None,
        ) => {
            // pre-existing text gets hidden
            Message::Message {
                text: text.clone(),
                start_time: *start_time,
                is_hidden: true,
            }
        }
        (Message::Init, None) => {
            // no-op, because we're hiding when no text has yet been reported
            Message::Init
        }
    };
    let new_state = State {
        message,
        to_stderr,
        angery_reaccs_only,
        ..state.clone()
    };
    update_stderr(&state, &new_state);
    *state = new_state;
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// The spinner is global: the tests that use it take turns, and see
    /// what it writes as if stderr were a terminal.
    pub(crate) fn with_captured_stderr<A>(f: impl FnOnce() -> A) -> (A, String) {
        static SERIAL: Mutex<()> = Mutex::new(());
        let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
        *state() = State {
            message: Message::Init,
            to_stderr: false,
            angery_reaccs_only: false,
            index: 0,
        };
        *crate::tty::CAPTURE.lock().unwrap() = Some(String::new());
        let a = f();
        let captured = crate::tty::CAPTURE.lock().unwrap().take().unwrap();
        (a, captured)
    }

    #[test]
    fn spinner_text() {
        let (latest, out) = with_captured_stderr(|| {
            report(true, false, None);
            report(true, false, Some("connecting".to_string()));
            report(true, false, Some("connecting".to_string()));
            report(true, false, None);
            report(true, true, Some("typechecking".to_string()));
            report(false, false, Some("typechecking".to_string()));
            let (shown, _) = get_latest_report().unwrap();
            report(false, false, None);
            let (hidden, _) = get_latest_report().unwrap();
            (shown, hidden)
        });
        // Nothing for the first `None`; the text; cleared and shown again;
        // cleared (hidden); the new text with an emoji; cleared, and not
        // shown again without `to_stderr`. (The animation may add a tick in
        // between: a clear and the text with the next character.)
        assert!(
            ASCII_CHARS
                .iter()
                .any(|c| out.starts_with(&format!("hh_server is busy: [connecting] {}", c))),
            "{:?}",
            out
        );
        assert!(out.contains(&format!(
            "{}hh_server is busy: [connecting] ",
            crate::tty::CLEAR_LINE_SEQ
        )));
        assert!(out.contains(&format!(
            "{}hh_server is busy: [typechecking] \u{1F621} ",
            crate::tty::CLEAR_LINE_SEQ
        )) || EMOJI_CHARS.iter().any(|c| out.contains(&format!("hh_server is busy: [typechecking] {}", c))));
        assert!(out.ends_with(crate::tty::CLEAR_LINE_SEQ), "{:?}", out);
        assert_eq!(latest.0, "typechecking");
        assert_eq!(latest.1, "[hidden] typechecking");
    }

    #[test]
    fn spinner_animates() {
        let ((), out) = with_captured_stderr(|| {
            report(true, false, Some("waiting".to_string()));
            std::thread::sleep(std::time::Duration::from_millis(2300));
            report(true, false, None);
        });
        // At least two ticks of the animation, each clearing the line and
        // showing the next character.
        let shown: Vec<&str> = out
            .split(crate::tty::CLEAR_LINE_SEQ)
            .filter(|s| !s.is_empty())
            .collect();
        assert!(shown.len() >= 3, "{:?}", out);
        let chars: Vec<&str> = shown
            .iter()
            .map(|s| s.strip_prefix("hh_server is busy: [waiting] ").unwrap())
            .collect();
        let first = ASCII_CHARS.iter().position(|c| *c == chars[0]).unwrap();
        assert_eq!(chars[1], ASCII_CHARS[(first + 1) % 4]);
        assert_eq!(chars[2], ASCII_CHARS[(first + 2) % 4]);
    }
}
