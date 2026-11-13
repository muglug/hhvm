// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/client_ide_service.ml` (the handle of plan
//! §7.4).
//!
//! Owned by **G1** (plan §7.3).
//!
//! Provides IDE services in the client, without an instance of hh_server
//! running.
//!
//! Basic approach: we load the naming table to give us just enough symbol
//! information to provide IDE services for just the files you're looking at. When
//! we need to look up declarations to service an IDE query, we parse and typecheck
//! the files containing those declarations on-demand, then answer your IDE query.
//!
//! # Threads instead of a process and Lwt (plan §6 #35)
//!
//! The OCaml spawns `clientIdeDaemon` as a process (`Daemon.spawn`, its
//! stdout and stderr the LSP log file) and talks to it over two pipes of
//! marshalled messages, from Lwt promises of `hh_client lsp`'s one thread.
//! Here the daemon is a thread ([`make`] starts it), the pipes are channels,
//! and the functions that return an Lwt promise in the OCaml block the
//! calling thread until the promise would be resolved:
//!
//! - [`serve`] is the loop that `Client_lsp` runs with `Lwt.async`: run it on
//!   a thread of its own (it returns once the service has stopped). It moves
//!   the messages of [`rpc`] to the daemon and the daemon's messages to the
//!   response and notification queues, as the OCaml's does.
//! - [`rpc`] blocks until its response (which [`serve`] delivers); `progress`
//!   is called after 0.2 s if the response has not come, and once it has.
//! - [`initialize_from_saved_state`] talks to the daemon directly (before
//!   [`serve`] runs), as the OCaml does.
//! - [`get_notifications`] is the queue of notifications ([`lwt_message_queue`],
//!   popped with blocking `pop`).
//!
//! `Daemon.force_quit` (kill the daemon process) has no counterpart for a
//! thread: [`stop`] closes the daemon's input instead (what the OCaml
//! daemon treats as the other "proper way to close clientIdeDaemon"), and
//! the thread ends once it has finished the request it is on, if any.
//! `Hack_event_logger` calls are no-ops in the open-source build: omitted.

use std::sync::Arc;
use std::sync::Mutex;
use std::sync::mpsc;
use std::time::Duration;

use crate::client_ide_daemon;
use crate::client_ide_message;
use crate::client_ide_message::IdeResult;
use crate::client_ide_message::MessageFromDaemon;
use crate::client_ide_message::Notification;
use crate::client_ide_message::RichError;
use crate::client_ide_message::TrackedT;
use crate::client_ide_utils;
use crate::exception;
use crate::hh_logger;
use crate::i_map;
use crate::lsp;
use crate::lwt_message_queue;
use crate::path;
use crate::telemetry;

pub mod status {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum T {
        /// The IDE services are still initializing (e.g. loading saved-state or
        /// building indexes.)
        Initializing,
        /// The IDE services will be available once they're done handling
        /// one or more existing requests. The telemetry items are information
        /// about each received request currently being performed.
        Rpc(Vec<telemetry::T>),
        /// The IDE services are available.
        Ready,
        /// The IDE services are not available.
        Stopped(RichError),
    }

    pub fn is_ready(t: &T) -> bool {
        matches!(t, T::Ready)
    }

    pub fn to_log_string(t: &T) -> String {
        match t {
            T::Initializing => "Initializing".to_string(),
            T::Rpc(requests) => format!(
                "Rpc [{}]",
                requests
                    .iter()
                    .map(|r| telemetry::to_string(None, r))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            T::Ready => "Ready".to_string(),
            T::Stopped(RichError {
                short_user_message, ..
            }) => format!("Stopped({})", short_user_message),
        }
    }
}

pub mod stop_reason {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum T {
        /// clientIdeService encountered an unexpected bug
        Crashed,
        /// clientIdeService shut down normally, although we've failed to record why
        Closed,
        /// clientLsp decided to close in response to shutdown
        EditorExited,
        /// clientLsp decided to close this clientIdeService and start a new one
        Restarting,
        /// test harnesses can tell clientLsp to shut down clientIdeService
        Testing,
    }

    pub fn to_log_string(t: T) -> String {
        match t {
            T::Crashed => "crashed",
            T::Closed => "closed",
            T::EditorExited => "editor exited",
            T::Restarting => "restarting",
            T::Testing => "testing-only, you should not see this",
        }
        .to_string()
    }
}

#[derive(Clone, Debug)]
enum State {
    /// The ide_service is created. We may or may not have yet sent an
    /// initialize message to the daemon.
    Uninitialized,
    /// The response to our initialize message was a failure. This is
    /// a terminal state.
    FailedToInitialize(RichError),
    /// We have received an initialize response from the daemon and all
    /// is well. The only thing that can take us out of this state is if
    /// someone invokes [stop], or if the daemon connection gets EOF.
    Initialized { status: status::T },
    /// Someone called [stop] or the daemon connection got EOF.
    /// This is a terminal state. This is the only state that arose
    /// from actions on our side; all the other states arose from
    /// responses from clientIdeDaemon.
    Stopped(RichError),
}

fn state_to_log_string(state: &State) -> String {
    match state {
        State::Uninitialized => "Uninitialized".to_string(),
        State::FailedToInitialize(RichError { category, .. }) => {
            format!("Failed_to_initialize({})", category)
        }
        State::Initialized { status } => {
            format!("Initialized({})", status::to_log_string(status))
        }
        State::Stopped(RichError { category, .. }) => format!("Stopped({})", category),
    }
}

/// `response_wrapper`: the responses of the daemon, in the order of the
/// requests.
type ResponseEmitter = lwt_message_queue::T<client_ide_message::TimedResponse>;

type NotificationEmitter = lwt_message_queue::T<Notification>;

mod active_rpc_requests {
    use super::*;

    #[derive(Clone, Debug, Default)]
    pub struct T {
        /// These are requests which have been sent to the daemon but we haven't yet had
        /// a response, e.g. if we sent requests #3 and #4 and #5 and a response #5 has come
        /// back, then active would be #3 and #4.
        pub requests: i_map::T<telemetry::T>,
        /// Monotonically increasing counter, used as indices in [requests]. E.g. we might
        /// at one moment have requests #3 and #4 active, while the counter is at #6.
        pub counter: isize,
    }

    pub fn new_() -> T {
        T::default()
    }

    pub fn add(telemetry: telemetry::T, t: &T) -> (T, isize) {
        let id = t.counter;
        (
            T {
                requests: t.requests.update(id, telemetry),
                counter: id + 1,
            },
            id,
        )
    }

    pub fn remove(id: isize, t: &T) -> T {
        T {
            requests: t.requests.without(&id),
            ..t.clone()
        }
    }

    pub fn is_empty(t: &T) -> bool {
        t.requests.is_empty()
    }

    pub fn values(t: &T) -> Vec<telemetry::T> {
        t.requests.values().cloned().collect()
    }
}

struct Inner {
    state: Mutex<State>,
    active_rpc_requests: Mutex<active_rpc_requests::T>,
    /// The daemon's input ("out_fd": we write to it). `None` once it is
    /// closed (`Daemon.force_quit`).
    out_fd: Mutex<Option<mpsc::Sender<TrackedT>>>,
    /// The daemon's output ("in_fd": we read from it).
    in_fd: Mutex<mpsc::Receiver<MessageFromDaemon>>,
    /// The queue of messages that we have yet to send to the daemon.
    messages_to_send: lwt_message_queue::T<TrackedT>,
    /// The queue of responses that we received from RPC calls to the daemon. We
    /// assume that we receive the responses in the same order that we sent their
    /// requests.
    response_emitter: ResponseEmitter,
    /// The queue of notifications that the daemon emitted. Notifications can be
    /// emitted at any time, not just in response to an RPC call.
    notification_emitter: NotificationEmitter,
}

/// `t`: a handle on the IDE service (clones share it).
#[derive(Clone)]
pub struct T(Arc<Inner>);

fn log(s: &str) {
    hh_logger::log(&format!("[ide-service] {}", s))
}

fn log_debug(s: &str) {
    hh_logger::debug(None, None, &format!("[ide-service] {}", s))
}

fn set_state(t: &T, new_state: State) {
    let mut state = t.0.state.lock().unwrap();
    log(&format!(
        "ClientIdeService.set_state {} -> {}",
        state_to_log_string(&state),
        state_to_log_string(&new_state)
    ));
    *state = new_state;
    // (`Lwt_condition.broadcast t.state_changed_cv ()`: nothing waits on it.)
}

fn get_state(t: &T) -> State {
    t.0.state.lock().unwrap().clone()
}

/// Create an uninitialized IDE service. All queries made to this service will
/// fail immediately, unless otherwise requested in the initialization procedure.
pub fn make(args: client_ide_message::DaemonArgs) -> T {
    // `Daemon.fd_of_path args.client_lsp_log_fn`: the daemon's stdout and
    // stderr.
    let log_fd = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&args.client_lsp_log_fn)
        .ok();
    let (to_daemon, daemon_in) = mpsc::channel::<TrackedT>();
    let (daemon_out, from_daemon) = mpsc::channel::<MessageFromDaemon>();
    let _daemon_handle = std::thread::Builder::new()
        .name("ClientIdeService".to_string())
        .spawn(move || {
            hh_logger::set_thread_instance(Some(hh_logger::Instance::new(log_fd)));
            client_ide_daemon::daemon_main(args, (daemon_in, daemon_out))
        })
        .expect("ClientIdeService: cannot start the daemon thread");
    T(Arc::new(Inner {
        state: Mutex::new(State::Uninitialized),
        active_rpc_requests: Mutex::new(active_rpc_requests::new_()),
        out_fd: Mutex::new(Some(to_daemon)),
        in_fd: Mutex::new(from_daemon),
        messages_to_send: lwt_message_queue::create(),
        response_emitter: lwt_message_queue::create(),
        notification_emitter: lwt_message_queue::create(),
    }))
}

/// `Marshal_tools_lwt.to_fd_with_preamble t.out_fd message`
fn write_to_daemon(t: &T, message: TrackedT) -> Result<(), String> {
    match &*t.0.out_fd.lock().unwrap() {
        Some(out_fd) => out_fd
            .send(message)
            .map_err(|_| "Unix.Unix_error(Unix.EPIPE, \"write\", \"\")".to_string()),
        None => Err("Unix.Unix_error(Unix.EBADF, \"write\", \"\")".to_string()),
    }
}

/// `Marshal_tools_lwt.from_fd_with_preamble t.in_fd`: `End_of_file` when the
/// daemon has gone.
fn read_from_daemon(t: &T) -> Result<MessageFromDaemon, String> {
    t.0.in_fd
        .lock()
        .unwrap()
        .recv()
        .map_err(|_| "End_of_file".to_string())
}

/// This function does an rpc to the daemon: it pushes a message
/// onto the daemon's stdin queue, then awaits until [serve] has stuck
/// the stdout response from the daemon response onto our [response_emitter].
/// The daemon updates [ref_unblocked_time], the time at which the
/// daemon starting handling the rpc.
///
/// Our only caller of this function is [ClientLsp.ide_rpc], which aims
/// to uphold the invariant that it never makes two concurrent calls
/// to this function. We support that invariant here by logging an
/// invariant_violation_bug should it occur, but that's only to help
/// our caller; this function supports being called while an existing
/// rpc is outstanding, and guarantees that its results will be
/// delivered in order.
///
/// The progress callback will be invoked during this call to rpc, at times
/// when the result of [get_status t] might have changed. It's designed
/// so the caller of rpc can, in their callback, invoke get_status and display
/// some kind of progress message.
///
/// Note: If we're in Stopped state (due to someone calling [stop]) then
/// we'll refrain from sending the rpc. Stopped is the only state we enter
/// due to our own volition; all other states are just a reflection
/// of what state the daemon is in, and so it's fine for the daemon
/// to respond as it see fits while in the other states.
pub fn rpc<A: IdeResult>(
    t: &T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    progress: &mut dyn FnMut(),
    message: client_ide_message::Request<A>,
) -> Result<A, lsp::error::T> {
    rpc_(t, tracking_id, ref_unblocked_time, progress, message.message, None)
        .and_then(|response| match A::of_response(response) {
            Some(a) => Ok(a),
            None => Err(client_ide_utils::to_lsp_error(&client_ide_utils::make_rich_error(
                None,
                Some(&exception::wrap("Failure(\"ClientIdeService desync\")".to_string())),
                "rpc",
            ))),
        })
}

/// [`rpc`] on an untyped message; with `timeout`, gives up waiting then
/// (the `Lwt.pick` of `destroy`), with `Err(None)`.
fn rpc_(
    t: &T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    progress: &mut dyn FnMut(),
    message: client_ide_message::T,
    timeout: Option<Duration>,
) -> Result<client_ide_message::Response, lsp::error::T> {
    let tracked_message = TrackedT {
        tracking_id: tracking_id.to_string(),
        message,
    };
    let result: Result<Result<client_ide_message::Response, lsp::error::T>, String> = (|| {
        match get_state(t) {
            State::Stopped(reason) => return Ok(Err(client_ide_utils::to_lsp_error(&reason))),
            State::Uninitialized | State::Initialized { .. } | State::FailedToInitialize(_) => {}
        }
        let message_string = client_ide_message::t_to_string(&tracked_message.message);
        let success = lwt_message_queue::push(&t.0.messages_to_send, tracked_message.clone());
        if !success {
            // queue closure is normal part of shutdown
            return Err("Failure(\"Could not send message (queue was closed)\")".to_string());
        }
        // If any rpc takes too long, we'll ask clientLsp to refresh status
        // a short time in, and then again when it's done.
        let telemetry = telemetry::create();
        let telemetry = telemetry::string_(None, "tracking_id", tracking_id, telemetry);
        let telemetry = telemetry::string_(None, "message", &message_string, telemetry);
        let id = {
            let mut active = t.0.active_rpc_requests.lock().unwrap();
            // (`if not (Active_rpc_requests.is_empty ...) then
            // Hack_event_logger.invariant_violation_bug "Multiple concurrent
            // ide_rpc requests"`: telemetry only.)
            let (new_active, id) = active_rpc_requests::add(telemetry, &active);
            *active = new_active;
            id
        };
        // `let pingPromise = Lwt_unix.sleep 0.2 |> Lwt.map progress`
        let response = match lwt_message_queue::pop_timeout(&t.0.response_emitter, Duration::from_millis(200)) {
            Ok(response) => Ok(response),
            Err(lwt_message_queue::Timeout) => {
                progress();
                match timeout {
                    None => Ok(lwt_message_queue::pop(&t.0.response_emitter)),
                    Some(timeout) => lwt_message_queue::pop_timeout(
                        &t.0.response_emitter,
                        timeout.saturating_sub(Duration::from_millis(200)),
                    ),
                }
            }
        };
        {
            let mut active = t.0.active_rpc_requests.lock().unwrap();
            *active = active_rpc_requests::remove(id, &active);
        }
        progress();
        match response {
            Err(lwt_message_queue::Timeout) => Ok(Err(lsp::error::T {
                code: lsp::error::InternalError,
                message: "timeout".to_string(),
                data: None,
            })),
            Ok(Some(timed_response)) if timed_response.tracking_id == tracked_message.tracking_id => {
                *ref_unblocked_time = timed_response.unblocked_time;
                Ok(timed_response.response)
            }
            // as discussed above, this case will never be hit.
            Ok(Some(_)) => Err("Failure(\"ClientIdeService desync\")".to_string()),
            // queue closure is part of normal shutdown
            Ok(None) => Err("Failure(\"Could not read response: queue was closed\")".to_string()),
        }
    })();
    match result {
        Ok(response) => response,
        Err(e) => {
            let e = exception::wrap(e);
            Err(client_ide_utils::to_lsp_error(&client_ide_utils::make_rich_error(
                None,
                Some(&e),
                "rpc",
            )))
        }
    }
}

/// Request that the IDE service initialize from the saved state. Queries made
/// to the service will fail until it is done initializing, unless
/// [wait_for_initialization] is [true], in which case queries made to the service
/// will block until the initializing is complete.
pub fn initialize_from_saved_state(
    t: &T,
    root: path::T,
    naming_table_load_info: Option<client_ide_message::initialize_from_saved_state::NamingTableLoadInfo>,
    warnings_saved_state_path: Option<path::T>,
    config: Vec<(String, String)>,
    ignore_hh_version: bool,
    open_files: Vec<path::T>,
) -> Result<(), RichError> {
    set_state(t, State::Uninitialized);
    let result: Result<Result<(), RichError>, String> = (|| {
        let message = TrackedT {
            tracking_id: "init".to_string(),
            message: client_ide_message::T::InitializeFromSavedState(
                client_ide_message::initialize_from_saved_state::T {
                    root,
                    naming_table_load_info,
                    warnings_saved_state_path,
                    config,
                    ignore_hh_version,
                    open_files,
                },
            ),
        };
        // Can't use [rpc] here, since that depends on the [serve] event loop,
        // which is called only after we return. We rely on the invariant
        // that daemon will send us no messages until after it has responded
        // to this first message.
        log_debug(&format!(
            "-> {} [init]",
            client_ide_message::tracked_t_to_string(&message)
        ));
        write_to_daemon(t, message)?;
        let response = read_from_daemon(t)?;
        log_debug(&format!(
            "<- {} [init]",
            client_ide_message::message_from_daemon_to_string(&response)
        ));
        match response {
            MessageFromDaemon::Response(client_ide_message::TimedResponse {
                response: Ok(_),
                tracking_id,
                ..
            }) if tracking_id == "init" => Ok(Ok(())),
            MessageFromDaemon::Response(client_ide_message::TimedResponse {
                response: Err(e),
                tracking_id,
                ..
            }) if tracking_id == "init" => {
                // that error has structure, which we wish to preserve in our error_data.
                Ok(Err(client_ide_utils::make_rich_error(e.data, None, &e.message)))
            }
            response => {
                // What we got back wasn't the 'init' response we expected:
                // the clientIdeDaemon has violated its contract.
                Err(format!(
                    "Failure(\"desync: {}\")",
                    client_ide_message::message_from_daemon_to_string(&response)
                ))
            }
        }
    })();
    match result {
        Ok(result) => result,
        Err(e) => {
            let e = exception::wrap(e);
            let reason = client_ide_utils::make_rich_error(None, Some(&e), "init_failed");
            set_state(t, State::FailedToInitialize(reason.clone()));
            Err(reason)
        }
    }
}

fn process_status_notification(t: &T, notification: &Notification) {
    match (get_state(t), notification) {
        (State::FailedToInitialize(_), _) | (State::Stopped(_), _) => {
            // terminal states, which don't change with notifications
        }
        (State::Uninitialized, Notification::DoneInit(Ok(()))) => set_state(
            t,
            State::Initialized {
                status: status::T::Ready,
            },
        ),
        (State::Uninitialized, Notification::DoneInit(Err(edata))) => {
            set_state(t, State::FailedToInitialize(edata.clone()))
        }
        (state, _) => {
            let message = format!(
                "Unexpected notification '{}' in state '{}'",
                client_ide_message::notification_to_string(notification),
                state_to_log_string(&state)
            );
            client_ide_utils::log_bug(None, None, true, &message);
        }
    }
}

fn destroy(t: &T, tracking_id: &str) {
    match get_state(t) {
        State::Uninitialized | State::FailedToInitialize(_) | State::Stopped(_) => {}
        State::Initialized { .. } => {
            let mut ref_unblocked_time = 0.;
            let result = rpc_(
                t,
                tracking_id,
                &mut ref_unblocked_time,
                &mut || {},
                client_ide_message::T::Shutdown,
                Some(Duration::from_secs(5)),
            );
            match result {
                // `Hack_event_logger.serverless_ide_destroy_ok`
                Ok(_) => {}
                Err(lsp::error::T { message, .. }) => {
                    log(&format!("ClientIdeService.destroy {}", message))
                }
            }
            // `Daemon.force_quit t.daemon_handle`: see the module doc.
            *t.0.out_fd.lock().unwrap() = None;
        }
    }
    lwt_message_queue::close(&t.0.messages_to_send);
    lwt_message_queue::close(&t.0.notification_emitter);
    lwt_message_queue::close(&t.0.response_emitter);
}

/// Clean up any resources held by the IDE service (such as the message loop
/// and background processes). Mark the service's status as "shut down" for the
/// given [reason].
pub fn stop(t: &T, tracking_id: &str, stop_reason: stop_reason::T, e: Option<&exception::T>) {
    // we store both a user-facing reason here, and a programmatic error
    // for use in subsequent telemetry
    let reason = client_ide_utils::make_rich_error(None, e, "stop");
    // We'll stick the stop_reason into that programmatic error, so that subsequent
    // telemetry can pick it up. (It never affects the user-facing message.)
    use crate::yojson::safe as yojson;
    let mut items = match &reason.data {
        None => vec![],
        Some(yojson::T::Assoc(items)) => items.clone(),
        Some(json) => vec![("data".to_string(), json.clone())],
    };
    items.insert(
        0,
        (
            "stop_reason".to_string(),
            yojson::T::String(stop_reason::to_log_string(stop_reason)),
        ),
    );
    let reason = RichError {
        data: Some(yojson::T::Assoc(items)),
        ..reason
    };
    destroy(t, tracking_id);
    // Correctness here is very subtle... During the course of that call to
    // 'destroy', we do let%lwt on an rpc call to shutdown the daemon.
    // Either that will return in 5s, or it won't; either way, we will
    // synchronously force quit the daemon handle and close the message queue.
    // (The OCaml's comment goes on: clientLsp never makes rpc requests to
    // us after it has called 'stop'.)
    set_state(t, State::Stopped(reason));
}

fn cleanup_upon_shutdown_or_exn(t: &T, e: Option<&exception::T>) {
    // We are invoked with e=None when one of the message-queues has said that
    // it's closed. This indicates an orderly shutdown has been performed by 'stop'.
    // We are invoked with e=Some when we had an exception in our main serve loop.
    let stop_reason = match e {
        None => {
            log("Normal shutdown due to message-queue closure");
            stop_reason::T::Closed
        }
        Some(e) => {
            client_ide_utils::log_bug(None, Some(e), true, "shutdown");
            stop_reason::T::Crashed
        }
    };
    // We might as well call 'stop' in both cases; there'll be no harm.
    match get_state(t) {
        State::Stopped(_) => {}
        _ => {
            log("Shutting down...");
            stop(t, "cleanup_or_shutdown", stop_reason, e)
        }
    }
}

/// Pump the message loop for the IDE service. Exits once the IDE service has
/// been [destroy]ed.
///
/// Behavior of 'serve' is (1) take items from `messages_to_send` and send
/// then over the wire to the daemon, (2) take items from the wire from the
/// daemon and put them onto `notification_emitter` or `response_emitter` queues,
/// (3) keep doing this until we discover that a queue has been closed, which
/// is the "cancellation" signal for us to stop our loop.
///
/// Blocks: run it on a thread of its own. The two directions, which the
/// OCaml interleaves with `Lwt.pick`, are two threads here (this one reads
/// from the daemon; a helper sends to it).
pub fn serve(t: &T) {
    // The cleanup is done once, by whichever direction finds the end first.
    let done = Arc::new(std::sync::Once::new());
    let outgoing = {
        let t = t.clone();
        let done = Arc::clone(&done);
        let id = hh_logger::thread_instance();
        std::thread::Builder::new()
            .name("ClientIdeService.serve".to_string())
            .spawn(move || {
                hh_logger::set_thread_instance(id);
                loop {
                    match lwt_message_queue::pop(&t.0.messages_to_send) {
                        None => {
                            done.call_once(|| cleanup_upon_shutdown_or_exn(&t, None));
                            return;
                        }
                        Some(next_message) => {
                            log_debug(&format!(
                                "-> {}",
                                client_ide_message::tracked_t_to_string(&next_message)
                            ));
                            if let Err(e) = write_to_daemon(&t, next_message) {
                                let e = exception::wrap(e);
                                // cleanup function below will log the exception
                                done.call_once(|| cleanup_upon_shutdown_or_exn(&t, Some(&e)));
                                return;
                            }
                        }
                    }
                }
            })
    };
    loop {
        let message = match read_from_daemon(t) {
            Ok(message) => message,
            Err(e) => {
                let e = exception::wrap(e);
                done.call_once(|| cleanup_upon_shutdown_or_exn(t, Some(&e)));
                break;
            }
        };
        log_debug(&format!(
            "<- {}",
            client_ide_message::message_from_daemon_to_string(&message)
        ));
        let queue_is_open = match message {
            MessageFromDaemon::Notification(notification) => {
                process_status_notification(t, &notification);
                lwt_message_queue::push(&t.0.notification_emitter, notification)
            }
            MessageFromDaemon::Response(response) => {
                lwt_message_queue::push(&t.0.response_emitter, response)
            }
        };
        if !queue_is_open {
            done.call_once(|| cleanup_upon_shutdown_or_exn(t, None));
            break;
        }
    }
    // The outgoing direction ends when `messages_to_send` is closed, which
    // the cleanup does.
    if let Ok(outgoing) = outgoing {
        let _ = outgoing.join();
    }
}

/// Get a handle to the stream of notifications sent by the IDE service. These
/// notifications may be sent even during RPC requests, and so should be processed
/// asynchronously.
pub fn get_notifications(t: &T) -> lwt_message_queue::T<Notification> {
    Arc::clone(&t.0.notification_emitter)
}

/// Get the status of the IDE services, based on the internal state and any
/// notifications that the IDE service process has sent to us.
pub fn get_status(t: &T) -> status::T {
    match get_state(t) {
        State::Uninitialized => status::T::Initializing,
        State::FailedToInitialize(error_data) => status::T::Stopped(error_data),
        State::Stopped(reason) => status::T::Stopped(reason),
        State::Initialized { status } => {
            let active = t.0.active_rpc_requests.lock().unwrap();
            if status::is_ready(&status) && !active_rpc_requests::is_empty(&active) {
                status::T::Rpc(active_rpc_requests::values(&active))
            } else {
                status
            }
        }
    }
}
