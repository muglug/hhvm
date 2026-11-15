// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/jsonrpc/jsonrpc.ml`. See `hh/PORTING.md`.
//!
//! Wrapper for handling JSON-RPC.
//! Spec: http://www.jsonrpc.org/specification
//! Practical readbable guide: https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md#base-protocol-json-structures
//!
//! # How this all works
//!
//! GOAL 1: is to always be ready to read on stdin so we can timestamp
//! accurately the moment that a request was delivered to us. If our
//! stdin pipe gets so full that a client can't write requests to us,
//! or if we're busy doing something else before we read on stdin,
//! both things would result in incorrect timestamps.
//! GOAL 2: when we process a message, then all subsequent messages that
//! have already been presented to our stdin should already be in our own
//! queue data-structure (rather than an OS pipe buffer) in case any
//! of the messages involved cancellation.
//!
//! The OCaml kicks off a background *process*, the "daemon", which reads
//! stdin and writes the messages over a pipe to the main process. Here the
//! daemon is a *thread* running [`internal_run_daemon`], and the pipe is a
//! channel (`crossbeam_channel`, unbounded, so that the daemon never waits to
//! write: its own queue of messages to send is the channel's). The rest is as
//! in OCaml: the daemon reads a message as soon as it arrives, timestamps it
//! and sends it; the main side ([`T`]) keeps its own queue of what it has
//! received from the channel so far.
//!
//! Callers of this library invoke [`get_message`]. When the queue is empty it
//! blocks until at least one message has come over the channel, and it slurps
//! up any further messages that have come too. This way, if the client calls
//! [`find_already_queued_message`] then they have a better chance of success.
//!
//! The Lwt functions are blocking functions here. In place of the file
//! descriptor of the pipe, [`await_until_message`] gives the receiving end
//! of the channel, which a caller can wait on together with other channels
//! (`crossbeam_channel::Select::ready`, which does not receive). The
//! cancellation token of [`await_until_found`] is a channel too: it is
//! "resolved" once its sender is dropped (or has sent a value).
//!
//! CARE!!! Jsonrpc is vulnerable to incomplete requests and malformed
//! Content-length headers... If the Content-length header is one byte
//! short, then Jsonrpc will read a json string that lacks the final }, and
//! will report this as a recoverable error (malformed json). Next, Jsonrpc
//! will block until a header+body has been read on stdin -- but nothing
//! further will come beyond that }, so it blocks indefinitely.
//! The only solution is to take care that Content-length is exact!
//!
//! Errors: the message of a [`marshal_tools::RemoteExceptionData`] is what
//! `Printexc.to_string` gives in OCaml (`End_of_file`,
//! `Http_lite.Malformed("Missing Content-Length")`,
//! `Yojson.Json_error("Line 1, ...")`...). A body that is not UTF-8 is read
//! with U+FFFD in place of the bytes that are not (a Rust `String` cannot
//! hold them).

use std::collections::VecDeque;
use std::io::Read;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicIsize;
use std::sync::atomic::Ordering;

use crossbeam_channel::Receiver;
use crossbeam_channel::Select;
use crossbeam_channel::Sender;

use crate::buffered_line_reader;
use crate::exception;
use crate::http_lite;
use crate::marshal_tools;
use crate::marshal_tools::RemoteExceptionData;
use crate::yojson::safe as yojson;

/// `Yojson.Safe.t -> unit`
pub type Writer<'a> = dyn Fn(yojson::T) + 'a;

#[derive(Clone, Debug, PartialEq)]
pub struct TimestampedJson {
    pub json: yojson::T,
    pub timestamp: f64,
}

/// These messages are the ones stored in the daemon's internal queue,
/// that are sent between daemon and main thread, that are stored
/// in the main queue, and that are handed to callers.
#[derive(Clone, Debug, PartialEq)]
pub enum QueueMessage {
    TimestampedJson(TimestampedJson),
    FatalException(RemoteExceptionData),
    RecoverableException(RemoteExceptionData),
}

/// This is the abstraction that callers use to get messages. The channel is
/// where we read from the daemon, and the queue holds all messages that
/// we've read from the daemon's channel so far.
///
/// (`T` is `Sync`: a caller can wait in [`await_until_found`] on one thread
/// while another uses the queue.)
pub struct T {
    /// The channel used by the main thread to read messages from the daemon.
    daemon_in_fd: Receiver<QueueMessage>,
    /// Whether the daemon has ended and dropped its end of the channel: the
    /// channel then reads as a pipe at its end of file (readable).
    daemon_done: Arc<AtomicBool>,
    messages: Mutex<VecDeque<QueueMessage>>,
}

/// The daemon has to deal with stdin of messages from client that it has to
/// read whenever available, and with its queue of messages which it wants to
/// send to the main thread. This type says which option it will chose.
///
/// (The OCaml decides with a `select` on stdin and the pipe. Here the
/// channel is never full, so a message to send is sent at once, and the
/// daemon blocks on stdin only when it has nothing to send; what it read
/// and has not parsed yet is read first, as in OCaml.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DaemonNextAction {
    /// We received an EOF on stdin, and our queue is empty, so the daemon has nothing left to do.
    DaemonEndDueToStdinEofAndEmptyQueue,
    /// There is no data to be read from stdin,
    /// and there are items in the daemon queue,
    /// and the channel to the main thread is open enough for us to write them without blocking.
    DaemonWriteToMainProcessPipe,
    /// EITHER there is data to be read from stdin so we prioritize that above all else,
    /// OR there are no items in the daemon queue so we might as well block on stdin until
    /// something arrives.
    DaemonReadFromStdin,
}

/// `Yojson.Json_error`, as `Printexc.to_string` prints it.
struct JsonErrorExn(crate::yojson::JsonError);

impl std::fmt::Debug for JsonErrorExn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Yojson.Json_error({})", crate::rt::ocaml_printf::sprintf_s(&(self.0).0))
    }
}

/// What `internal_read_message` raises: what the reader raises, or the
/// error of the JSON parser.
enum ReadError {
    Reader(http_lite::Error),
    JsonError(crate::yojson::JsonError),
}

/// Try to read a message from the daemon's stdin, which is where all of the
/// editor messages can be read from. May throw if the message is malformed.
fn internal_read_message<R: Read>(
    reader: &mut buffered_line_reader::T<R>,
) -> Result<TimestampedJson, ReadError> {
    let message = http_lite::read_message_utf8(reader).map_err(ReadError::Reader)?;
    let message = match String::from_utf8(message) {
        Ok(s) => s,
        Err(e) => String::from_utf8_lossy(e.as_bytes()).into_owned(),
    };
    let json = yojson::from_string(&message).map_err(ReadError::JsonError)?;
    let timestamp = crate::rt::ocaml_unix::gettimeofday();
    Ok(TimestampedJson { json, timestamp })
}

/// Reads messages from the editor on stdin, parses them, and sends them to the
/// main thread.
/// This runs in a different thread because we also timestamp the messages, so
/// we need to read them as soon as they come in. That is, we can't wait for any
/// server computation to finish if we want to get an accurate timestamp.
///
/// Returns when the main thread no longer receives (`Err`) or when there is
/// nothing left to do (`Ok`).
fn internal_run_daemon_<R: Read>(
    reader: R,
    oc: &Sender<QueueMessage>,
) -> Result<(), crossbeam_channel::SendError<QueueMessage>> {
    let mut reader = buffered_line_reader::create(reader);
    let mut messages_to_send: VecDeque<QueueMessage> = VecDeque::new();
    let mut allowed_to_read = true;
    loop {
        let daemon_next_action = if buffered_line_reader::has_buffered_content(&reader) {
            DaemonNextAction::DaemonReadFromStdin
        } else if !messages_to_send.is_empty() {
            DaemonNextAction::DaemonWriteToMainProcessPipe
        } else if allowed_to_read {
            // An indefinite wait until we're able to read.
            DaemonNextAction::DaemonReadFromStdin
        } else {
            DaemonNextAction::DaemonEndDueToStdinEofAndEmptyQueue
        };
        let (should_continue, allowed_to_read_) = match daemon_next_action {
            DaemonNextAction::DaemonReadFromStdin => match internal_read_message(&mut reader) {
                Ok(timestamped_json) => {
                    messages_to_send.push_back(QueueMessage::TimestampedJson(timestamped_json));
                    (true, allowed_to_read)
                }
                Err(exn) => {
                    let (allowed_to_read, message) = match exn {
                        ReadError::JsonError(e) => {
                            let e = exception::wrap(JsonErrorExn(e));
                            let edata = marshal_tools::of_exception(&e);
                            (true, QueueMessage::RecoverableException(edata))
                        }
                        // End_of_file | _
                        ReadError::Reader(e) => {
                            let e = exception::wrap(e);
                            let edata = marshal_tools::of_exception(&e);
                            (false, QueueMessage::FatalException(edata))
                        }
                    };
                    messages_to_send.push_back(message);
                    (true, allowed_to_read)
                }
            },
            DaemonNextAction::DaemonWriteToMainProcessPipe => {
                assert!(!messages_to_send.is_empty());
                let message = messages_to_send.pop_front().unwrap();
                oc.send(message)?;
                (true, allowed_to_read)
            }
            DaemonNextAction::DaemonEndDueToStdinEofAndEmptyQueue => (false, false),
        };
        allowed_to_read = allowed_to_read_;
        if !should_continue {
            return Ok(());
        }
    }
}

/// Main function for the daemon thread.
fn internal_run_daemon<R: Read>(reader: R, oc: Sender<QueueMessage>, done: Arc<AtomicBool>) {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        internal_run_daemon_(reader, &oc)
    })) {
        Ok(_) => {}
        Err(exn) => {
            let e = exception::wrap(exn);
            // An exception that's gotten here is not simply a parse error, but
            // something else, so we should terminate the daemon at this point.
            // (If the main thread no longer receives, we just give up on
            // reporting the error.)
            let _ = oc.send(QueueMessage::FatalException(marshal_tools::of_exception(&e)));
        }
    }
    // The end of the pipe: the main thread reads an end of file.
    drop(oc);
    done.store(true, Ordering::SeqCst);
}

/// `Daemon.register_entry_point "Jsonrpc" internal_run_daemon`, and
/// `Daemon.spawn` of it: the daemon thread, reading `reader`.
fn internal_entry_point<R: Read + Send + 'static>(reader: R) -> T {
    let (oc, ic) = crossbeam_channel::unbounded();
    let done = Arc::new(AtomicBool::new(false));
    let done_ = Arc::clone(&done);
    std::thread::Builder::new()
        .name("Jsonrpc".to_string())
        .spawn(move || internal_run_daemon(reader, oc, done_))
        .expect("could not start the Jsonrpc thread");
    T {
        daemon_in_fd: ic,
        daemon_done: done,
        messages: Mutex::new(VecDeque::new()),
    }
}

// ~~ Queue functions that run in the main thread ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Make the JsonRPC daemon responsible for parsing and transmitting LSP
/// messages: a thread that reads stdin.
pub fn make_t() -> T {
    internal_entry_point(std::io::stdin())
}

/// [`make_t`], reading the messages from `reader` instead of stdin.
pub fn make_t_from_reader<R: Read + Send + 'static>(reader: R) -> T {
    internal_entry_point(reader)
}

fn lock_messages(t: &T) -> std::sync::MutexGuard<'_, VecDeque<QueueMessage>> {
    t.messages.lock().unwrap_or_else(|e| e.into_inner())
}

/// Whether receiving on `rx` would not block: a value is waiting, or every
/// sender has been dropped. (`Select::try_ready` does not receive.)
fn is_ready<A>(rx: &Receiver<A>) -> bool {
    let mut sel = Select::new();
    sel.recv(rx);
    sel.try_ready().is_ok()
}

/// `Lwt_unix.readable` on the pipe: a message is waiting in the channel, or
/// the daemon has ended (an end of file is readable). (The channel is
/// disconnected a moment before `daemon_done` is set: `is_ready` sees it.)
fn is_readable(t: &T) -> bool {
    t.daemon_done.load(Ordering::SeqCst) || is_ready(&t.daemon_in_fd)
}

/// Read a message into the queue, and return the just-read message.
fn read_single_message_into_queue_wait(t: &T) -> QueueMessage {
    let message = match t.daemon_in_fd.recv() {
        Ok(message) => message,
        Err(crossbeam_channel::RecvError) => {
            let e = exception::wrap(buffered_line_reader::Error::EndOfFile);
            // This is different from when the client hangs up. It handles the case
            // that the daemon exited: for example, if it was killed.
            QueueMessage::FatalException(marshal_tools::of_exception(&e))
        }
    };
    lock_messages(t).push_back(message.clone());
    message
}

fn read_messages_into_queue_no_wait(t: &T) {
    loop {
        if is_readable(t) {
            // We're expecting this not to block because we just checked
            // to make sure that there's something there.
            let message = read_single_message_into_queue_wait(t);
            // Now read any more messages that might be queued up. Only try to read more
            // messages if the daemon is still available to read from. Otherwise, we may
            // infinite loop as a result of the channel always being readable at its end.
            match message {
                QueueMessage::FatalException(_) => return,
                _ => {}
            }
        } else {
            return;
        }
    }
}

/// says whether there's already an item on the queue, or stdin is readable meaning that there's something pending on it
pub fn has_message(t: &T) -> bool {
    let is_readable = is_readable(t);
    is_readable || !lock_messages(t).is_empty()
}

/// What [`await_until_message`] gives: `` `Already_has_message `` or
/// `` `Wait_for_data_here fd ``.
pub enum AwaitUntilMessage<'a> {
    AlreadyHasMessage,
    /// Ready (`crossbeam_channel::Select::ready`) when there is a message to
    /// read. Waiting does not receive it.
    WaitForDataHere(&'a Receiver<QueueMessage>),
}

/// similar to [`has_message`], but can be used to power a 'select' syscall
/// which will fire when a message is available.
pub fn await_until_message(t: &T) -> AwaitUntilMessage<'_> {
    // The next message will come either from the queue or (if it's empty) then
    // from some data coming in from [daemon_in_fd].
    if lock_messages(t).is_empty() {
        AwaitUntilMessage::WaitForDataHere(&t.daemon_in_fd)
    } else {
        AwaitUntilMessage::AlreadyHasMessage
    }
}

/// says whether the things we've already enqueued from stdin contain a message that matches the predicate
pub fn find_already_queued_message(
    f: impl Fn(&TimestampedJson) -> bool,
    t: &T,
) -> Option<TimestampedJson> {
    let messages = lock_messages(t);
    let mut found: Option<TimestampedJson> = None;
    for message in messages.iter() {
        found = match (found, message) {
            (Some(found), _) => Some(found),
            (None, QueueMessage::TimestampedJson(message)) if f(message) => Some(message.clone()),
            _ => None,
        }
    }
    found
}

/// A cancellation token (`unit Lwt.t`): resolved once its sender has been
/// dropped, or has sent `()`. As a promise, once resolved it stays resolved:
/// nothing here receives from it.
pub type CancellationToken = Receiver<()>;

/// `not (Lwt.is_sleeping cancellation_token)`. (It does not receive the
/// `()`, so that the token stays resolved, as a resolved promise does.)
fn is_resolved(cancellation_token: &CancellationToken) -> bool {
    is_ready(cancellation_token)
}

/// This awaits until a message is found which satisfies the predicate,
/// and returns it as [Some].
/// If the message was already in the queue at the time this function was called,
/// then it returns at once.
/// If [cancellation_token] is fired before a message is found, then
/// it returns [None].
/// If there's a fault with the incoming channel like EOF, it also returns
/// [None].
pub fn await_until_found(
    t: &T,
    predicate: impl Fn(&TimestampedJson) -> bool,
    cancellation_token: &CancellationToken,
) -> Option<TimestampedJson> {
    match find_already_queued_message(&predicate, t) {
        Some(message) => Some(message),
        None => loop {
            // `Lwt.pick [Lwt_unix.wait_read daemon_in_fd; cancellation_token]`
            loop {
                let mut sel = Select::new();
                sel.recv(&t.daemon_in_fd);
                sel.recv(cancellation_token);
                sel.ready();
                // (`ready` may return spuriously.)
                if is_readable(t) || is_resolved(cancellation_token) {
                    break;
                }
            }
            let was_cancelled = is_resolved(cancellation_token);
            if was_cancelled {
                return None;
            } else {
                match read_single_message_into_queue_wait(t) {
                    QueueMessage::TimestampedJson(message) if predicate(&message) => {
                        return Some(message);
                    }
                    QueueMessage::TimestampedJson(_) => {}
                    QueueMessage::FatalException(_) | QueueMessage::RecoverableException(_) => {
                        return None;
                    }
                }
            }
        },
    }
}

/// What [`get_message`] gives.
#[derive(Clone, Debug, PartialEq)]
pub enum GetMessage {
    Message(TimestampedJson),
    FatalException(RemoteExceptionData),
    RecoverableException(RemoteExceptionData),
}

pub fn get_message(t: &T) -> GetMessage {
    // Read one in a blocking manner to ensure that we have one.
    let is_empty = lock_messages(t).is_empty();
    if is_empty {
        let _message: QueueMessage = read_single_message_into_queue_wait(t);
    }
    // Then read any others that got queued up so that we can see the maximum
    // number of messages at once for invalidation purposes.
    read_messages_into_queue_no_wait(t);
    // `Queue.dequeue_exn`
    let item = lock_messages(t)
        .pop_front()
        .expect("Jsonrpc.get_message: the queue has a message");
    match item {
        QueueMessage::TimestampedJson(timestamped_json) => GetMessage::Message(timestamped_json),
        QueueMessage::FatalException(data) => GetMessage::FatalException(data),
        QueueMessage::RecoverableException(data) => GetMessage::RecoverableException(data),
    }
}

// ~~ Output functions for request ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

static REQUESTS_COUNTER: AtomicIsize = AtomicIsize::new(0);

/// `requests_counter` (an `I_map.key ref`)
pub fn requests_counter() -> &'static AtomicIsize {
    &REQUESTS_COUNTER
}

pub fn get_next_request_id() -> isize {
    requests_counter().fetch_add(1, Ordering::SeqCst) + 1
}

#[cfg(test)]
mod tests {
    use std::io::Write;
    use std::os::unix::net::UnixStream;
    use std::time::Duration;

    use super::*;

    fn frame(body: &str) -> String {
        format!("Content-Length: {}\r\n\r\n{}", body.len(), body)
    }

    fn json_of(m: &GetMessage) -> String {
        match m {
            GetMessage::Message(TimestampedJson { json, .. }) => yojson::to_string(json),
            _ => panic!("not a message: {:?}", m),
        }
    }

    /// Waits until the daemon has sent everything it read (the end of file
    /// included).
    fn wait_until_done(t: &T) {
        while !t.daemon_done.load(Ordering::SeqCst) {
            std::thread::sleep(Duration::from_millis(1));
        }
    }

    #[test]
    fn messages_in_order_with_malformed_input() {
        let input = [
            frame(r#"{"id":1,"method":"a"}"#),
            frame(r#"{"method":"b"}"#),
            frame("{not json"),
            frame(r#"{"method":"c"}"#),
        ]
        .concat();
        let t = make_t_from_reader(std::io::Cursor::new(input.into_bytes()));
        wait_until_done(&t);
        assert!(has_message(&t));
        let before = crate::rt::ocaml_unix::gettimeofday();
        let m1 = get_message(&t);
        assert_eq!(json_of(&m1), r#"{"id":1,"method":"a"}"#);
        match &m1 {
            GetMessage::Message(m) => assert!(m.timestamp <= before && m.timestamp > 0.0),
            _ => unreachable!(),
        }
        // Everything the daemon sent is in the queue now.
        assert!(
            find_already_queued_message(
                |m| m.json == yojson::T::Assoc(vec![("method".to_string(), yojson::T::String("c".to_string()))]),
                &t
            )
            .is_some()
        );
        assert_eq!(json_of(&get_message(&t)), r#"{"method":"b"}"#);
        match get_message(&t) {
            GetMessage::RecoverableException(e) => {
                assert!(e.message.starts_with("Yojson.Json_error(\"Line 1"), "{}", e.message)
            }
            m => panic!("{:?}", m),
        }
        assert_eq!(json_of(&get_message(&t)), r#"{"method":"c"}"#);
        // The end of stdin is fatal, and so is every read after it.
        assert_eq!(
            get_message(&t),
            GetMessage::FatalException(RemoteExceptionData {
                message: "End_of_file".to_string(),
                stack: String::new()
            })
        );
        match get_message(&t) {
            GetMessage::FatalException(e) => assert_eq!(e.message, "End_of_file"),
            m => panic!("{:?}", m),
        }
        assert!(has_message(&t));
    }

    #[test]
    fn malformed_headers_are_fatal() {
        let t = make_t_from_reader(std::io::Cursor::new(
            b"Content-Type: text\r\n\r\n{}".to_vec(),
        ));
        match get_message(&t) {
            GetMessage::FatalException(e) => assert_eq!(
                e.message,
                "Http_lite.Malformed(\"Missing Content-Length\")"
            ),
            m => panic!("{:?}", m),
        }
        // The daemon stops reading after a fatal error.
        match get_message(&t) {
            GetMessage::FatalException(e) => assert_eq!(e.message, "End_of_file"),
            m => panic!("{:?}", m),
        }
    }

    #[test]
    fn await_and_cancel() {
        let (mut client, server) = UnixStream::pair().unwrap();
        let t = make_t_from_reader(server);
        assert!(!has_message(&t));
        assert!(matches!(
            await_until_message(&t),
            AwaitUntilMessage::WaitForDataHere(_)
        ));
        client
            .write_all(frame(r#"{"method":"x"}"#).as_bytes())
            .unwrap();
        // The daemon reads it on its own.
        match await_until_message(&t) {
            AwaitUntilMessage::WaitForDataHere(rx) => {
                let mut sel = Select::new();
                sel.recv(rx);
                sel.ready();
            }
            AwaitUntilMessage::AlreadyHasMessage => panic!("nothing was read yet"),
        }
        assert!(has_message(&t));
        let is_cancel = |m: &TimestampedJson| {
            crate::hh_json_helpers::jget::string_opt(Some(&m.json), "method").as_deref()
                == Some("$/cancelRequest")
        };
        // A cancellation that comes while waiting.
        let (_cancel_tx, cancel_rx) = crossbeam_channel::bounded::<()>(1);
        std::thread::scope(|scope| {
            let waiter = scope.spawn(|| await_until_found(&t, is_cancel, &cancel_rx));
            std::thread::sleep(Duration::from_millis(20));
            client
                .write_all(frame(r#"{"method":"$/cancelRequest","params":{"id":1}}"#).as_bytes())
                .unwrap();
            let found = waiter.join().unwrap();
            assert!(found.is_some());
        });
        // It is in the queue, and so is the first message.
        assert!(find_already_queued_message(is_cancel, &t).is_some());
        assert!(matches!(
            await_until_message(&t),
            AwaitUntilMessage::AlreadyHasMessage
        ));
        // A token that fires first.
        let (cancel_tx, cancel_rx) = crossbeam_channel::bounded::<()>(1);
        std::thread::scope(|scope| {
            let waiter = scope.spawn(|| {
                await_until_found(&t, |m| m.json == yojson::T::Null, &cancel_rx)
            });
            std::thread::sleep(Duration::from_millis(20));
            drop(cancel_tx);
            assert_eq!(waiter.join().unwrap(), None);
        });
        assert_eq!(json_of(&get_message(&t)), r#"{"method":"x"}"#);
        assert_eq!(
            json_of(&get_message(&t)),
            r#"{"method":"$/cancelRequest","params":{"id":1}}"#
        );
        drop(client);
        match get_message(&t) {
            GetMessage::FatalException(e) => assert_eq!(e.message, "End_of_file"),
            m => panic!("{:?}", m),
        }
    }

    #[test]
    fn buffered_input_is_read_after_a_fatal_error() {
        // One read gives the reader all of it: after the fatal error of the
        // first message, the second is still in the reader's buffer, and the
        // daemon reads what is buffered before it looks at
        // `allowed_to_read`, as the OCaml does.
        let input = ["X: y\r\n\r\n".to_string(), frame(r#"{"method":"m"}"#)].concat();
        let t = make_t_from_reader(std::io::Cursor::new(input.into_bytes()));
        match get_message(&t) {
            GetMessage::FatalException(e) => assert_eq!(
                e.message,
                "Http_lite.Malformed(\"Missing Content-Length\")"
            ),
            m => panic!("{:?}", m),
        }
        assert_eq!(json_of(&get_message(&t)), r#"{"method":"m"}"#);
        match get_message(&t) {
            GetMessage::FatalException(e) => assert_eq!(e.message, "End_of_file"),
            m => panic!("{:?}", m),
        }
    }

    #[test]
    fn a_resolved_token_stays_resolved() {
        // The client stays connected and sends nothing: only the token can
        // end the waits.
        let (client, server) = UnixStream::pair().unwrap();
        let t = Arc::new(make_t_from_reader(server));
        let (cancel_tx, cancel_rx) = crossbeam_channel::bounded::<()>(1);
        // `Lwt.wakeup`: the promise is resolved, and stays resolved.
        cancel_tx.send(()).unwrap();
        let (done_tx, done_rx) = crossbeam_channel::bounded(1);
        let t_ = Arc::clone(&t);
        std::thread::spawn(move || {
            let first = await_until_found(&t_, |_| true, &cancel_rx);
            let second = await_until_found(&t_, |_| true, &cancel_rx);
            done_tx.send((first, second, is_resolved(&cancel_rx))).unwrap();
        });
        let (first, second, still_resolved) = done_rx
            .recv_timeout(Duration::from_secs(10))
            .expect("await_until_found returns at once on a resolved token");
        assert_eq!(first, None);
        assert_eq!(second, None);
        assert!(still_resolved);
        assert!(!has_message(&t));
        drop(client);
    }

    #[test]
    fn request_ids() {
        let a = get_next_request_id();
        let b = get_next_request_id();
        assert!(b > a);
    }
}
