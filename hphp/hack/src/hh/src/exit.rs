// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/exit.ml`. See `hh/PORTING.md`.

use std::sync::Mutex;

use crate::exception;
use crate::exit_status;
use crate::telemetry;
use crate::utils;

type Hook = Box<dyn Fn(&exit_status::FinaleData) + Send>;

/// The hooks, the one added last first (OCaml conses them onto its list).
static HOOK_UPON_CLEAN_EXIT: Mutex<Vec<Hook>> = Mutex::new(Vec::new());

pub fn add_hook_upon_clean_exit(hook: impl Fn(&exit_status::FinaleData) + Send + 'static) {
    HOOK_UPON_CLEAN_EXIT
        .lock()
        .unwrap()
        .insert(0, Box::new(hook));
}

// ~~ The world gate ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// In OCaml a signal handler runs on the main thread (at an allocation
// point), so when the SIGUSR2 handler of `Server_main.Program.set_signals`
// calls `Exit.exit`, the typecheck it interrupted never resumes: nothing the
// main thread would have done next (report errors to the errors file, write
// the progress file, log, answer a client) happens after the exit hooks
// unlink the errors file and write the finale. Here signal handlers run on a
// thread of their own (`rt::ocaml_sys`) and the main ("world") thread keeps
// going, so [`exit`] first stops the world: it takes the gate, waiting for
// the side effect in flight (a write of the errors file or of the progress
// file: see [`with_world`]) to finish, and keeps it for good; from then on
// every other thread that comes to such a side effect, a log line or a
// write to a socket ([`check_world`]) stops there until the process is gone.
// Only the thread that exits goes on, so exactly one exit happens, after
// everything the world did before the signal and nothing it did after.

struct Gate {
    owner: Option<std::thread::ThreadId>,
    depth: usize,
}

static GATE: Mutex<Gate> = Mutex::new(Gate {
    owner: None,
    depth: 0,
});
static GATE_FREE: std::sync::Condvar = std::sync::Condvar::new();
/// Set (for good) once a thread has stopped the world to exit.
static EXITING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn lock_gate() -> std::sync::MutexGuard<'static, Gate> {
    GATE.lock().unwrap_or_else(|e| e.into_inner())
}

/// Takes the gate (re-entrantly): waits while another thread holds it.
/// Another thread that has stopped the world holds it forever.
fn enter_gate() {
    let me = std::thread::current().id();
    let mut gate = lock_gate();
    while gate.owner.is_some_and(|owner| owner != me) {
        gate = GATE_FREE.wait(gate).unwrap_or_else(|e| e.into_inner());
    }
    gate.owner = Some(me);
    gate.depth += 1;
}

fn leave_gate() {
    let mut gate = lock_gate();
    gate.depth -= 1;
    if gate.depth == 0 && !EXITING.load(std::sync::atomic::Ordering::SeqCst) {
        gate.owner = None;
        GATE_FREE.notify_all();
    }
}

/// Runs `f`, a side effect of the server that the exit hooks undo or
/// overwrite (writing the errors file, the progress file), so that it
/// happens wholly before an exit or not at all: an exit waits until `f` is
/// done, and once a thread is exiting `f` of any other thread never runs.
pub fn with_world<A>(f: impl FnOnce() -> A) -> A {
    struct Leave;
    impl Drop for Leave {
        fn drop(&mut self) {
            leave_gate()
        }
    }
    enter_gate();
    let _leave = Leave;
    f()
}

/// For a side effect that must not happen once another thread is exiting
/// but that may take long (a write to a client, which an exit must not wait
/// for) or that is done under locks of its own (a log line): when a thread
/// other than this one has stopped the world, never returns.
pub fn check_world() {
    if EXITING.load(std::sync::atomic::Ordering::Relaxed) {
        let me = std::thread::current().id();
        if lock_gate().owner != Some(me) {
            loop {
                std::thread::park();
            }
        }
    }
}

/// Stops the world for this thread, which is going to exit (see the notes
/// above): waits for the side effect in flight on another thread, then
/// keeps the gate. Idempotent; a second thread that wants to exit stops here
/// for good.
pub fn stop_the_world() {
    enter_gate();
    EXITING.store(true, std::sync::atomic::Ordering::SeqCst);
}

/// Runs the hooks registered with [`add_hook_upon_clean_exit`] with the
/// finale data of `exit_status` (a hook that raises is ignored), then exits.
/// The process exits with `exit_code_override` if given, ignoring the exit
/// code that `exit_status::exit_code(exit_status)` would give. The world is
/// stopped first (see [`stop_the_world`]).
pub fn exit(
    msg: Option<String>,
    telemetry: Option<telemetry::T>,
    stack: Option<String>,
    exit_code_override: Option<isize>,
    exit_status: exit_status::T,
) -> ! {
    stop_the_world();
    // is there additional inforamtion in exit_status to pick up?
    let (emsg, estack) = match &exit_status {
        exit_status::T::UncaughtException(e) => (
            Some(exception::get_ctor_string(e)),
            Some(exception::clean_stack(&exception::get_backtrace_string(e))),
        ),
        exit_status::T::ServerHungUpShouldAbort(Some(finale_data))
        | exit_status::T::ServerHungUpShouldRetry(Some(finale_data)) => {
            let exit_status::FinaleData {
                exit_status,
                stack: utils::Callstack(stack),
                ..
            } = &**finale_data;
            (Some(exit_status::show(exit_status)), Some(stack.clone()))
        }
        _ => (None, None),
    };
    let stack = stack
        .unwrap_or_else(|| exception::clean_stack(&exception::get_current_callstack_string(99)));
    let stack = match estack {
        None => stack,
        Some(estack) => format!("{}\n\n{}", stack, estack),
    };
    // `Option.first_some msg emsg`
    let msg = msg.or(emsg);
    let server_finale_data = exit_status::FinaleData {
        exit_status,
        msg,
        stack: utils::Callstack(stack),
        telemetry,
    };
    for hook in HOOK_UPON_CLEAN_EXIT.lock().unwrap().iter() {
        let _ =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| hook(&server_finale_data)));
    }
    let exit_code = exit_code_override
        .unwrap_or_else(|| exit_status::exit_code(&server_finale_data.exit_status));
    // `Stdlib.exit` flushes the standard channels first (and then exits even
    // if that fails).
    {
        use std::io::Write;
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
    }
    std::process::exit(exit_code as i32)
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    use super::*;

    /// The scenario runs in a child process (a stopped world stays stopped):
    /// a "world" thread keeps doing side effects under the gate and logging;
    /// once the main thread has stopped the world, none happens any more,
    /// the gated side effect in flight is finished first, and a second exit
    /// from another thread never gets past the gate.
    #[test]
    fn stop_the_world_stops_the_others_for_good() {
        if std::env::var("HH_EXIT_GATE_CHILD").is_ok() {
            static EFFECTS: AtomicUsize = AtomicUsize::new(0);
            static LOGS: AtomicUsize = AtomicUsize::new(0);
            static IN_FLIGHT: AtomicUsize = AtomicUsize::new(0);
            std::thread::spawn(|| {
                loop {
                    with_world(|| {
                        IN_FLIGHT.store(1, Ordering::SeqCst);
                        std::thread::sleep(std::time::Duration::from_millis(2));
                        EFFECTS.fetch_add(1, Ordering::SeqCst);
                        IN_FLIGHT.store(0, Ordering::SeqCst);
                    });
                    check_world();
                    LOGS.fetch_add(1, Ordering::SeqCst);
                }
            });
            std::thread::sleep(std::time::Duration::from_millis(50));
            stop_the_world();
            // Re-entrant for the thread that stopped the world.
            with_world(|| ());
            check_world();
            assert_eq!(IN_FLIGHT.load(Ordering::SeqCst), 0);
            let (effects, logs) = (EFFECTS.load(Ordering::SeqCst), LOGS.load(Ordering::SeqCst));
            assert!(effects > 0);
            let second_exit = std::thread::spawn(|| {
                stop_the_world();
                std::process::exit(3)
            });
            std::thread::sleep(std::time::Duration::from_millis(100));
            assert!(!second_exit.is_finished());
            assert_eq!(EFFECTS.load(Ordering::SeqCst), effects);
            // (At most the one log line that had passed its check.)
            assert!(LOGS.load(Ordering::SeqCst) <= logs + 1);
            std::process::exit(0)
        } else {
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "exit::tests::stop_the_world_stops_the_others_for_good",
                    "--nocapture",
                ])
                .env("HH_EXIT_GATE_CHILD", "1")
                .status()
                .unwrap();
            assert_eq!(status.code(), Some(0));
        }
    }
}
