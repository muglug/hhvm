// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart for the frames: the client-server protocol, the
//! conversation between `hh_client`, the monitor and `hh_server` over
//! `Server_files.socket_file` and the pipes from the monitor to the server,
//! which stands in for `Marshal_tools`. The messages are those of
//! `crate::monitor_rpc`, `crate::monitor_utils` and `crate::prehandoff`;
//! `crate::monitor_connection` is the client's end of the handshake, and
//! [`server_end`] the server's half of
//! `client_and_server/server_client_provider.ml`; the decisions of the
//! client's end (`Client_connect`, `Client_start`, `Client_stop`) are
//! transliterated.
//!
//! As in OCaml, the monitor (`crate::monitor_main`) accepts the
//! connection, checks the client's version, and hands the file descriptor
//! to the server (`SCM_RIGHTS`, `libancillary`), which then talks to the
//! client. OCaml `Marshal`s every value after a preamble; here every value is
//! a frame: a `u32` (little-endian) length, then that many bytes (only these
//! binaries talk to each other on these frames). The handshake keeps OCaml's
//! messages, in OCaml's order:
//!
//! | # | direction | frame | OCaml |
//! |---|---|---|---|
//! | 1 | C → M | the JSON of `crate::monitor_utils::version_payload` | the version string (and a newline, not sent here) |
//! | 2 | M → C | `crate::monitor_utils::ConnectionState` | `connection_state` |
//! | 3 | C → M | `crate::monitor_rpc::Command` (`HandoffToServer` or `ShutDown`) | `Monitor_rpc.command` |
//! | 4 | M → C | `crate::prehandoff::Msg`s, the last a `Sentinel` | `Prehandoff.msg` |
//! | | M → S | `crate::monitor_rpc::MonitorToServerHandoffMsg`, then the fd, on the pipe of the request | the same |
//! | 5 | S → C | `MessageType::Hello` (or `Monitor_failed_to_handoff` from M) | `Hello` |
//! | 6 | C → S | `ConnectionType::NonPersistent` | `connection_type` |
//! | 7 | C → S | the command, `(CmdMetadata, T)` | `'a command` |
//! | 8 | S → C | `MessageType::Ping`s, then `Response (result, tracker)`; the server closes | `'a message_type` |
//!
//! Frame 1 is JSON (it must stay readable by any version); the others are
//! `bincode` of `serde` values ([`wire`]).
//!
//! Not kept, because there is nothing for them to do: the
//! `pgrep monitor_daemon_main` and the "busy and overloaded" timer of
//! `connect_to_monitor` (only with `~log_on_slow_connect:true`, which no
//! caller passes); `Hack_event_logger` calls (a stub in the OSS build).

// ~~ Frames ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

use std::io;
use std::io::Read;
use std::io::Write;
use std::os::fd::AsRawFd;
use std::os::unix::net::UnixStream;
use std::time::Duration;

use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::rt::ocaml_unix;

/// What reading a value from the other end can fail with: OCaml's
/// `Marshal_tools.from_fd_with_preamble`, whose exceptions the callers treat
/// differently (an `End_of_file` is a hang-up; the others are not caught).
#[derive(Debug)]
pub enum ReadError {
    /// `End_of_file`: nothing at all could be read (the other end closed).
    EndOfFile,
    /// `Marshal_tools.Reading_Preamble_Exception`: the length was cut short.
    ReadingPreamble,
    /// `Marshal_tools.Reading_Payload_Exception`: the payload was cut short.
    ReadingPayload,
    /// `Failure "input_value: truncated object"`: `Stdlib.input_value`
    /// ([`input_value`]) met the end of the stream inside a value.
    Truncated,
    /// `Unix.Unix_error (_, "read", "")`. A read that times out (a socket
    /// timeout) is one of these, with kind `WouldBlock` or `TimedOut`.
    Unix(io::Error),
    /// `Failure "input_value: bad object"`: the bytes are not a value of the
    /// expected type.
    Malformed(String),
}

impl ReadError {
    /// Whether this is a socket timeout.
    pub fn is_timeout(&self) -> bool {
        matches!(self, ReadError::Unix(e) if is_timeout(e))
    }
}

/// The exception OCaml raises, as `Printexc.to_string` shows it: what a
/// [`ReadError`] that nothing catches until the catch-all handler of the
/// program is returned as ([`uncaught_read_error`]), with `?` up to that
/// handler.
pub struct UncaughtReadError(pub String);

impl std::fmt::Debug for UncaughtReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// `Printexc.to_string` of the exception of a [`ReadError`].
pub fn read_error_to_string(e: &ReadError, fun_name: &str) -> String {
    match e {
        ReadError::EndOfFile => "End_of_file".to_string(),
        ReadError::ReadingPreamble => "Marshal_tools.Reading_Preamble_Exception".to_string(),
        ReadError::ReadingPayload => "Marshal_tools.Reading_Payload_Exception".to_string(),
        ReadError::Unix(e) => ocaml_unix::unix_error_to_string(e, fun_name, ""),
        ReadError::Truncated => "Failure(\"input_value: truncated object\")".to_string(),
        ReadError::Malformed(_) => "Failure(\"input_value: bad object\")".to_string(),
    }
}

/// The exception of a [`ReadError`] that the OCaml does not catch where it
/// is raised.
pub fn uncaught_read_error(e: ReadError) -> UncaughtReadError {
    UncaughtReadError(read_error_to_string(&e, "read"))
}

/// What writing a value can fail with: `Unix.Unix_error (_, "write", "")`
/// (`EPIPE` when the other end is gone, which `hh_client` sees because it
/// ignores `SIGPIPE`).
pub type WriteError = io::Error;

/// The exception of a write error that nothing catches.
pub fn uncaught_write_error(e: WriteError) -> UncaughtReadError {
    UncaughtReadError(ocaml_unix::unix_error_to_string(&e, "write", ""))
}

pub fn is_timeout(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
    )
}

/// The largest payload: what a `u32` length can say.
pub const MAXIMUM_PAYLOAD_SIZE: usize = u32::MAX as usize;

/// Writes one frame: the length (`u32`, little-endian), then the payload,
/// as `Marshal_tools.to_fd_with_preamble` writes (see [`write_with_preamble`]).
pub fn write_frame(w: &mut impl FrameSink, payload: &[u8]) -> Result<(), WriteError> {
    if payload.len() > MAXIMUM_PAYLOAD_SIZE {
        return Err(ocaml_unix::RaisedException(
            "Marshal_tools.Payload_Size_Too_Large_Exception",
        )
        .into_io_error());
    }
    w.write_with_preamble(&(payload.len() as u32).to_le_bytes(), payload)
}

/// `Marshal_tools.RegularWriterReader.write fd ~buffer ~offset ~size`: waits
/// until the descriptor is writable (`Poll.wait_fd_write_non_interrupted
/// ~timeout_ms:None`), then writes once; 0 bytes are written when the poll
/// says the descriptor is not writable (a peer that hung up: `POLLHUP`
/// alone), and the poll's error flags (`POLLPRI`, `POLLNVAL`) are
/// `Poll.Poll_exception`.
fn poll_write(fd: std::os::fd::RawFd, buf: &[u8]) -> io::Result<usize> {
    let mut pfd = libc::pollfd {
        fd,
        events: libc::POLLOUT,
        revents: 0,
    };
    let nready = loop {
        // SAFETY: `pfd` is one valid `pollfd`.
        let n = unsafe { libc::poll(&mut pfd, 1, -1) };
        if n >= 0 {
            break n;
        }
        let e = io::Error::last_os_error();
        if e.kind() != io::ErrorKind::Interrupted {
            return Err(e);
        }
    };
    if nready == 0 {
        // `Ok Poll.Timeout -> 0`
        return Ok(0);
    }
    // (`POLLERR` on a descriptor polled for writing is a hang-up, not an
    // error.)
    if pfd.revents & (libc::POLLPRI | libc::POLLNVAL) != 0 {
        return Err(ocaml_unix::RaisedException("Poll.Poll_exception(_)").into_io_error());
    }
    if pfd.revents & libc::POLLOUT == 0 {
        return Ok(0);
    }
    loop {
        // SAFETY: writes from `buf`, which lives during the call.
        let n = unsafe { libc::write(fd, buf.as_ptr() as *const libc::c_void, buf.len()) };
        if n >= 0 {
            return Ok(n as usize);
        }
        let e = io::Error::last_os_error();
        if e.kind() != io::ErrorKind::Interrupted {
            return Err(e);
        }
    }
}

/// Where `Marshal_tools.to_fd_with_preamble` writes: a descriptor (written
/// as the OCaml writes, [`write_with_preamble`]), or a buffer (a test
/// comparing bytes).
pub trait FrameSink: Write {
    fn write_with_preamble(&mut self, preamble: &[u8], payload: &[u8]) -> Result<(), WriteError>;
}

macro_rules! fd_frame_sink {
    ($($t:ty),*) => {
        $(impl FrameSink for $t {
            fn write_with_preamble(&mut self, preamble: &[u8], payload: &[u8]) -> Result<(), WriteError> {
                write_with_preamble(self.as_raw_fd(), preamble, payload)
            }
        })*
    };
}

fd_frame_sink!(UnixStream, &UnixStream, std::fs::File);

impl FrameSink for Vec<u8> {
    fn write_with_preamble(&mut self, preamble: &[u8], payload: &[u8]) -> Result<(), WriteError> {
        self.extend_from_slice(preamble);
        self.extend_from_slice(payload);
        Ok(())
    }
}

/// `write_payload fd buffer offset to_write`: the count written, less than
/// the length of `buf` when a write wrote nothing.
fn write_payload(fd: std::os::fd::RawFd, buf: &[u8]) -> io::Result<usize> {
    let mut offset = 0;
    while offset < buf.len() {
        let n = poll_write(fd, &buf[offset..])?;
        if n == 0 {
            break;
        }
        offset += n;
    }
    Ok(offset)
}

/// The writing half of `Marshal_tools.to_fd_with_preamble`: the preamble,
/// then the payload, each as [`write_payload`]; a short preamble is
/// `Writing_Preamble_Exception`, a short payload `Writing_Payload_Exception`.
fn write_with_preamble(
    fd: std::os::fd::RawFd,
    preamble: &[u8],
    payload: &[u8],
) -> Result<(), WriteError> {
    // (No write once another thread is exiting, as in OCaml where the exit
    // happens on the thread that would write: see `exit::check_world`.)
    crate::exit::check_world();
    if write_payload(fd, preamble)? != preamble.len() {
        return Err(
            ocaml_unix::RaisedException("Marshal_tools.Writing_Preamble_Exception").into_io_error(),
        );
    }
    if write_payload(fd, payload)? != payload.len() {
        return Err(
            ocaml_unix::RaisedException("Marshal_tools.Writing_Payload_Exception").into_io_error(),
        );
    }
    Ok(())
}

/// Reads as much of `buf` as the other end sends: the count read (less than
/// the length of `buf` only at the end of the stream).
fn read_fully(r: &mut impl Read, buf: &mut [u8]) -> io::Result<usize> {
    let mut offset = 0;
    while offset < buf.len() {
        match r.read(&mut buf[offset..]) {
            Ok(0) => break,
            Ok(n) => offset += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(offset)
}

/// Reads one frame (as `Marshal_tools.from_fd_with_preamble` reads one
/// value).
pub fn read_frame(r: &mut impl Read) -> Result<Vec<u8>, ReadError> {
    let mut preamble = [0u8; 4];
    let bytes_read = read_fully(r, &mut preamble).map_err(ReadError::Unix)?;
    if bytes_read == 0 {
        // Unix manpage for read says 0 bytes read indicates end of file.
        return Err(ReadError::EndOfFile);
    } else if bytes_read != preamble.len() {
        crate::hh_logger::log(&format!(
            "Error, only read {} bytes for preamble.",
            bytes_read
        ));
        return Err(ReadError::ReadingPreamble);
    }
    let payload_size = u32::from_le_bytes(preamble) as usize;
    let mut payload = vec![0u8; payload_size];
    let payload_size_read = read_fully(r, &mut payload).map_err(ReadError::Unix)?;
    if payload_size_read != payload_size {
        return Err(ReadError::ReadingPayload);
    }
    Ok(payload)
}

/// Reads a value of type `V` from a frame as `Stdlib.input_value` reads
/// one from a channel (where the OCaml reads a value that the other end
/// wrote with `Marshal.to_channel`): nothing at all is `End_of_file`, a
/// frame cut short `Failure "input_value: truncated object"`
/// ([`ReadError::Truncated`]); nothing is logged.
pub fn input_value<V: DeserializeOwned>(r: &mut impl Read) -> Result<V, ReadError> {
    let mut preamble = [0u8; 4];
    let bytes_read = read_fully(r, &mut preamble).map_err(ReadError::Unix)?;
    if bytes_read == 0 {
        return Err(ReadError::EndOfFile);
    } else if bytes_read != preamble.len() {
        return Err(ReadError::Truncated);
    }
    let payload_size = u32::from_le_bytes(preamble) as usize;
    let mut payload = vec![0u8; payload_size];
    if read_fully(r, &mut payload).map_err(ReadError::Unix)? != payload_size {
        return Err(ReadError::Truncated);
    }
    wire::decode(&payload).map_err(ReadError::Malformed)
}

/// Writes a value as a frame (`Marshal_tools.to_fd_with_preamble`).
pub fn write_value<V: Serialize>(w: &mut impl FrameSink, v: &V) -> Result<(), WriteError> {
    write_frame(w, &wire::encode(v))
}

/// Reads a value of type `V` from a frame
/// (`Marshal_tools.from_fd_with_preamble`).
pub fn read_value<V: DeserializeOwned>(r: &mut impl Read) -> Result<V, ReadError> {
    let payload = read_frame(r)?;
    wire::decode(&payload).map_err(ReadError::Malformed)
}

// ~~ OCaml frames (the handshake) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The first two messages of the handshake (the client's version, the
/// monitor's `connection_state`) are exactly the OCaml's, so that a client
/// and a monitor of the two implementations understand each other's
/// version mismatch: `Marshal_tools.to_fd_with_preamble` (a preamble of
/// `'\142'` and the size, 4 bytes big-endian, then OCaml `Marshal` bytes).
pub mod ocaml_frame {
    use std::io;
    use std::io::Read;

    use super::FrameSink;
    use super::ReadError;
    use crate::rt::ocaml_marshal;
    use crate::rt::ocaml_marshal::Value;

    use crate::marshal_tools::EXPECTED_PREAMBLE_SIZE;
    use crate::marshal_tools::PREAMBLE_START_SENTINEL;

    /// `Marshal_tools.to_fd_with_preamble fd v` (no flags).
    pub fn write_value(w: &mut impl FrameSink, v: &Value) -> io::Result<()> {
        let payload = ocaml_marshal::to_bytes(v, &[])
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e.0))?;
        if payload.len() >= u32::MAX as usize {
            return Err(crate::rt::ocaml_unix::RaisedException(
                "Marshal_tools.Payload_Size_Too_Large_Exception",
            )
            .into_io_error());
        }
        let preamble = crate::marshal_tools::make_preamble(payload.len());
        w.write_with_preamble(&preamble, &payload)
    }

    /// `Marshal_tools.from_fd_with_preamble fd`: the preamble is one read
    /// (as the OCaml's), the payload as many as it takes.
    pub fn read_value(r: &mut impl Read) -> Result<Value, ReadError> {
        let mut preamble = [0u8; EXPECTED_PREAMBLE_SIZE];
        let bytes_read = loop {
            match r.read(&mut preamble) {
                Ok(n) => break n,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(ReadError::Unix(e)),
            }
        };
        if bytes_read == 0 {
            // Unix manpage for read says 0 bytes read indicates end of file.
            return Err(ReadError::EndOfFile);
        } else if bytes_read != EXPECTED_PREAMBLE_SIZE {
            crate::hh_logger::log(&format!(
                "Error, only read {} bytes for preamble.",
                bytes_read
            ));
            return Err(ReadError::ReadingPreamble);
        }
        if preamble[0] != PREAMBLE_START_SENTINEL {
            return Err(ReadError::Malformed(
                "Marshal_tools.Malformed_Preamble_Exception".to_string(),
            ));
        }
        let payload_size = u32::from_be_bytes([preamble[1], preamble[2], preamble[3], preamble[4]]) as usize;
        let mut payload = vec![0u8; payload_size];
        let mut offset = 0;
        while offset < payload_size {
            match r.read(&mut payload[offset..]) {
                Ok(0) => break,
                Ok(n) => offset += n,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(ReadError::Unix(e)),
            }
        }
        if offset != payload_size {
            return Err(ReadError::ReadingPayload);
        }
        ocaml_marshal::from_bytes(&payload, 0).map_err(|e| ReadError::Malformed(e.0))
    }

    /// The client's version message: the string, then a newline.
    pub fn write_version(w: &mut impl FrameSink, version: &str) -> io::Result<()> {
        write_value(w, &Value::string(version.as_bytes()))?;
        w.write_all(b"\n")?;
        w.flush()
    }

    /// `read_version_string_then_newline`: the string, or the exception of
    /// reading it; then `Error "missing newline after version"` when the
    /// next byte is not a newline (the inner `Err`).
    pub fn read_version(r: &mut impl Read) -> Result<Result<String, String>, ReadError> {
        let v = read_value(r)?;
        let s = match v.as_bytes() {
            Ok(b) => String::from_utf8_lossy(b).into_owned(),
            Err(e) => return Err(ReadError::Malformed(e.0)),
        };
        let mut newline_byte = [0u8; 1];
        let _ = r.read(&mut newline_byte);
        if &newline_byte == b"\n" {
            Ok(Ok(s))
        } else {
            Ok(Err("missing newline after version".to_string()))
        }
    }

    /// The monitor's `connection_state`.
    pub fn write_connection_state(
        w: &mut impl FrameSink,
        c: &crate::monitor_utils::ConnectionState,
    ) -> io::Result<()> {
        write_value(w, &crate::monitor_utils::connection_state_to_ocaml(c))
    }

    pub fn read_connection_state(
        r: &mut impl Read,
    ) -> Result<crate::monitor_utils::ConnectionState, ReadError> {
        let v = read_value(r)?;
        crate::monitor_utils::connection_state_of_ocaml(&v).map_err(ReadError::Malformed)
    }
}

/// Waits until `stream` has something to read (or the other end closed it),
/// at most `timeout` seconds: `Unix.select [fd] [] [fd] timeout`. True if it
/// is readable.
pub fn select_readable(stream: &UnixStream, timeout: f64) -> io::Result<bool> {
    let mut pfd = libc::pollfd {
        fd: stream.as_raw_fd(),
        events: libc::POLLIN,
        revents: 0,
    };
    let ms = (timeout * 1000.).max(0.) as libc::c_int;
    loop {
        // SAFETY: one valid `pollfd`.
        let ret = unsafe { libc::poll(&mut pfd, 1, ms) };
        if ret < 0 {
            let e = io::Error::last_os_error();
            if e.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(e);
        }
        return Ok(ret > 0);
    }
}

/// A point in time by which an operation must be done
/// (`Timeout.with_timeout ~timeout`).
#[derive(Clone, Copy, Debug)]
pub struct Deadline(f64);

impl Deadline {
    pub fn in_seconds(timeout: f64) -> Deadline {
        Deadline(ocaml_unix::gettimeofday() + timeout)
    }

    /// What is left, `None` once it has passed.
    pub fn remaining(&self) -> Option<Duration> {
        let left = self.0 - ocaml_unix::gettimeofday();
        if left <= 0. {
            None
        } else {
            Some(Duration::from_secs_f64(left))
        }
    }

    /// Makes the reads and writes of `stream` time out at the deadline (an
    /// error with kind `WouldBlock`/`TimedOut`). A deadline that has passed
    /// is a timeout at once (the only `Err`).
    ///
    /// (Setting the timeouts of a socket whose other end has gone fails on
    /// macOS, `EINVAL`: that is ignored, as the next read or write on it
    /// reports the hang-up, which is what OCaml sees.)
    pub fn apply(&self, stream: &UnixStream) -> io::Result<()> {
        let left = self
            .remaining()
            .ok_or_else(|| io::Error::new(io::ErrorKind::TimedOut, "timeout"))?;
        let _ = stream.set_read_timeout(Some(left));
        let _ = stream.set_write_timeout(Some(left));
        Ok(())
    }
}

/// Removes the timeouts of `stream` (after the parts of the protocol that
/// have one). An error is ignored, as in [`Deadline::apply`].
pub fn clear_timeouts(stream: &UnixStream) {
    let _ = stream.set_read_timeout(None);
    let _ = stream.set_write_timeout(None);
}

/// `Unix.open_connection (ADDR_UNIX sock_name)`, where connecting may take
/// until `deadline` (a full backlog). The error is `Unix_error (_,
/// "connect", "")`.
pub fn open_connection(sock_name: &str, deadline: &Deadline) -> io::Result<UnixStream> {
    use std::os::fd::FromRawFd;
    let _addr = std::os::unix::net::SocketAddr::from_pathname(sock_name)?;
    let c_path = std::ffi::CString::new(sock_name)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e))?;
    let left = deadline
        .remaining()
        .ok_or_else(|| io::Error::new(io::ErrorKind::TimedOut, "timeout"))?;
    // SAFETY: plain socket calls on a descriptor we own; `sockaddr_un` is
    // zeroed and filled within its bounds (`from_pathname` checked the
    // length).
    unsafe {
        let fd = libc::socket(libc::AF_UNIX, libc::SOCK_STREAM, 0);
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        let stream = UnixStream::from_raw_fd(fd);
        libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
        // A connect that blocks gives up at the send timeout.
        stream.set_write_timeout(Some(left))?;
        let mut sun: libc::sockaddr_un = std::mem::zeroed();
        sun.sun_family = libc::AF_UNIX as libc::sa_family_t;
        let bytes = c_path.as_bytes_with_nul();
        for (i, b) in bytes.iter().enumerate() {
            sun.sun_path[i] = *b as libc::c_char;
        }
        let len = (std::mem::size_of::<libc::sa_family_t>() + bytes.len()) as libc::socklen_t;
        loop {
            if libc::connect(fd, &sun as *const _ as *const libc::sockaddr, len) == 0 {
                break;
            }
            let e = io::Error::last_os_error();
            match e.raw_os_error() {
                Some(libc::EINTR) => continue,
                Some(libc::EAGAIN) | Some(libc::EINPROGRESS) => {
                    return Err(io::Error::new(io::ErrorKind::TimedOut, e));
                }
                _ => return Err(e),
            }
        }
        Ok(stream)
    }
}

// ~~ Values on the wire ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The encoding of the values in the frames (`bincode` of their `serde`),
/// and the `serde` of the types of other modules that have none.
pub mod wire {
    use serde::Deserialize;
    use serde::Deserializer;
    use serde::Serialize;
    use serde::Serializer;
    use serde::de::DeserializeOwned;

    use crate::file_content;
    use crate::find_refs_wire_format::cli_args;
    use crate::pos::APos;
    use crate::pos::Absolute;
    use crate::relative_path::RelativePath;
    use crate::search_types::find_refs;
    use crate::server_notifier_types::Clock;
    use crate::telemetry;
    use crate::yojson::safe as yojson;

    pub fn encode<V: Serialize>(v: &V) -> Vec<u8> {
        match bincode::serde::encode_to_vec(v, bincode::config::standard()) {
            Ok(bytes) => bytes,
            // A value that cannot be encoded is a bug of this program (the
            // `todo!`s below are raised from inside the encoder).
            Err(e) => panic!("cannot encode a value for the socket: {}", e),
        }
    }

    pub fn decode<V: DeserializeOwned>(bytes: &[u8]) -> Result<V, String> {
        match bincode::serde::decode_from_slice(bytes, bincode::config::standard()) {
            Ok((v, read)) if read == bytes.len() => Ok(v),
            Ok((_, read)) => Err(format!(
                "{} bytes left after the value",
                bytes.len() - read
            )),
            Err(e) => Err(e.to_string()),
        }
    }

    // `Pos.absolute`: its file and its span (`Pos.to_absolute` of a `Pos`
    // in a `Dummy` path, whose absolute path is its suffix, gives it back).

    #[derive(Serialize, Deserialize)]
    struct AbsoluteWire {
        file: String,
        start: oxidized::file_pos_large::FilePosLarge,
        end: oxidized::file_pos_large::FilePosLarge,
    }

    impl Serialize for Absolute {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            let span = self.raw_span();
            AbsoluteWire {
                file: self.pos_file(),
                start: span.start,
                end: span.end,
            }
            .serialize(s)
        }
    }

    impl<'de> Deserialize<'de> for Absolute {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let AbsoluteWire { file, start, end } = AbsoluteWire::deserialize(d)?;
            let file = std::sync::Arc::new(RelativePath::make(
                relative_path::Prefix::Dummy,
                std::path::PathBuf::from(file),
            ));
            let pos = oxidized::pos::Pos::from_raw_span(
                file,
                oxidized::pos_span_raw::PosSpanRaw { start, end },
            );
            Ok(crate::pos::to_absolute(&pos))
        }
    }

    // `File_content.Position.t`: its one-based line and column.

    impl Serialize for file_content::position::T {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            file_content::position::line_column_one_based(self).serialize(s)
        }
    }

    impl<'de> Deserialize<'de> for file_content::position::T {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let (line, column) = <(isize, isize)>::deserialize(d)?;
            Ok(file_content::position::from_one_based(line, column))
        }
    }

    // `Telemetry.t`: its JSON.

    impl Serialize for telemetry::T {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            yojson::to_string(&telemetry::to_yojson(self)).serialize(s)
        }
    }

    impl<'de> Deserialize<'de> for telemetry::T {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let s = String::deserialize(d)?;
            match yojson::from_string(&s) {
                Ok(yojson::T::Assoc(pairs)) => {
                    // `telemetry::json` adds a pair as it is: the pairs come
                    // back in the order `to_yojson` gave them.
                    let mut t = telemetry::create();
                    for (key, value) in pairs {
                        t = telemetry::json(&key, value, t);
                    }
                    Ok(t)
                }
                _ => Err(serde::de::Error::custom("telemetry: a JSON object expected")),
            }
        }
    }

    // `Yojson.Safe.t`: its text.

    impl Serialize for yojson::T {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            yojson::to_string(self).serialize(s)
        }
    }

    impl<'de> Deserialize<'de> for yojson::T {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let s = String::deserialize(d)?;
            yojson::from_string(&s).map_err(|e| serde::de::Error::custom(e.0))
        }
    }

    // `Server_notifier_types.clock`

    #[derive(Serialize, Deserialize)]
    enum ClockWire {
        Watchman(String),
        Eden(String),
    }

    impl Serialize for Clock {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            match self {
                Clock::Watchman(c) => ClockWire::Watchman(c.clone()),
                Clock::Eden(c) => ClockWire::Eden(c.clone()),
            }
            .serialize(s)
        }
    }

    impl<'de> Deserialize<'de> for Clock {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            Ok(match ClockWire::deserialize(d)? {
                ClockWire::Watchman(c) => Clock::Watchman(c),
                ClockWire::Eden(c) => Clock::Eden(c),
            })
        }
    }

    // `Search_types.Find_refs.member` and `action`

    #[derive(Serialize, Deserialize)]
    enum MemberWire {
        Method(String),
        Property(String),
        ClassConst(String),
        Typeconst(String),
    }

    impl Serialize for find_refs::Member {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            match self {
                find_refs::Member::Method(x) => MemberWire::Method(x.clone()),
                find_refs::Member::Property(x) => MemberWire::Property(x.clone()),
                find_refs::Member::ClassConst(x) => MemberWire::ClassConst(x.clone()),
                find_refs::Member::Typeconst(x) => MemberWire::Typeconst(x.clone()),
            }
            .serialize(s)
        }
    }

    impl<'de> Deserialize<'de> for find_refs::Member {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            Ok(match MemberWire::deserialize(d)? {
                MemberWire::Method(x) => find_refs::Member::Method(x),
                MemberWire::Property(x) => find_refs::Member::Property(x),
                MemberWire::ClassConst(x) => find_refs::Member::ClassConst(x),
                MemberWire::Typeconst(x) => find_refs::Member::Typeconst(x),
            })
        }
    }

    #[derive(Serialize, Deserialize)]
    enum ActionWire {
        Class(String),
        ExplicitClass(String),
        Member(String, find_refs::Member),
        Function(String),
        GConst(String),
        LocalVar {
            filename: RelativePath,
            file_content: String,
            pos: file_content::position::T,
        },
    }

    impl Serialize for find_refs::Action {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            match self.clone() {
                find_refs::Action::Class(x) => ActionWire::Class(x),
                find_refs::Action::ExplicitClass(x) => ActionWire::ExplicitClass(x),
                find_refs::Action::Member(x, m) => ActionWire::Member(x, m),
                find_refs::Action::Function(x) => ActionWire::Function(x),
                find_refs::Action::GConst(x) => ActionWire::GConst(x),
                find_refs::Action::LocalVar {
                    filename,
                    file_content,
                    pos,
                } => ActionWire::LocalVar {
                    filename,
                    file_content,
                    pos,
                },
            }
            .serialize(s)
        }
    }

    impl<'de> Deserialize<'de> for find_refs::Action {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            Ok(match ActionWire::deserialize(d)? {
                ActionWire::Class(x) => find_refs::Action::Class(x),
                ActionWire::ExplicitClass(x) => find_refs::Action::ExplicitClass(x),
                ActionWire::Member(x, m) => find_refs::Action::Member(x, m),
                ActionWire::Function(x) => find_refs::Action::Function(x),
                ActionWire::GConst(x) => find_refs::Action::GConst(x),
                ActionWire::LocalVar {
                    filename,
                    file_content,
                    pos,
                } => find_refs::Action::LocalVar {
                    filename,
                    file_content,
                    pos,
                },
            })
        }
    }

    // `Find_refs_wire_format.CliArgs.t`

    #[derive(Serialize, Deserialize)]
    struct CliArgsWire {
        symbol_name: String,
        action: find_refs::Action,
        stream_file: Option<String>,
        hint_suffixes: Vec<String>,
    }

    impl Serialize for cli_args::T {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            CliArgsWire {
                symbol_name: self.symbol_name.clone(),
                action: self.action.clone(),
                stream_file: self.stream_file.clone(),
                hint_suffixes: self.hint_suffixes.clone(),
            }
            .serialize(s)
        }
    }

    impl<'de> Deserialize<'de> for cli_args::T {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let CliArgsWire {
                symbol_name,
                action,
                stream_file,
                hint_suffixes,
            } = CliArgsWire::deserialize(d)?;
            Ok(cli_args::T {
                symbol_name,
                action,
                stream_file,
                hint_suffixes,
            })
        }
    }

    /// `Relative_path.Set.t` (an `im::OrdSet`, whose `serde` needs a
    /// feature of `im` that is not on): its elements, in order.
    pub mod ord_set {
        use super::*;

        pub fn serialize<S: Serializer>(
            set: &crate::relative_path::set::T,
            s: S,
        ) -> Result<S::Ok, S::Error> {
            s.collect_seq(set.iter())
        }

        pub fn deserialize<'de, D: Deserializer<'de>>(
            d: D,
        ) -> Result<crate::relative_path::set::T, D::Error> {
            let v = Vec::<RelativePath>::deserialize(d)?;
            Ok(v.into_iter().collect())
        }
    }

    /// The result of `STATUS_SINGLE`: the TASTs (behind the feature `port`,
    /// with no `serde`) cannot cross the socket yet; the diagnostics can.
    pub mod status_single_result {
        use super::*;
        use crate::diagnostics::FinalizedDiagnostic;

        pub fn serialize<S: Serializer, X>(
            ((errors, dropped_count), tasts): &((Vec<FinalizedDiagnostic>, isize), Option<X>),
            s: S,
        ) -> Result<S::Ok, S::Error> {
            match tasts {
                None => (errors, dropped_count).serialize(s),
                Some(_) => todo!(
                    "STATUS_SINGLE's TASTs over the socket: Tast.program Tast_with_dynamic.t (behind the feature port) has no serde"
                ),
            }
        }

        pub fn deserialize<'de, D: Deserializer<'de>, X>(
            d: D,
        ) -> Result<((Vec<FinalizedDiagnostic>, isize), Option<X>), D::Error> {
            let (errors, dropped_count) = <(Vec<FinalizedDiagnostic>, isize)>::deserialize(d)?;
            Ok(((errors, dropped_count), None))
        }
    }

    use crate::relative_path;
}

// ~~ Monitor_rpc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

// ~~ Monitor_utils ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

// ~~ Prehandoff ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

// ~~ Monitor_connection: the client's end of the handshake ~~~~~~~~~~~~~~~~~~

// ~~ The server's end ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monitor_utils;

    #[test]
    fn frames() {
        let (mut w, mut r) = UnixStream::pair().unwrap();
        write_frame(&mut w, b"hello").unwrap();
        drop(w);
        let mut buf = vec![];
        r.read_to_end(&mut buf).unwrap();
        assert_eq!(&buf[..4], &5u32.to_le_bytes());
        let mut r = &buf[..];
        assert_eq!(read_frame(&mut r).unwrap(), b"hello");
        assert!(matches!(read_frame(&mut r), Err(ReadError::EndOfFile)));
        let mut r = &buf[..2];
        assert!(matches!(read_frame(&mut r), Err(ReadError::ReadingPreamble)));
        let mut r = &buf[..6];
        assert!(matches!(read_frame(&mut r), Err(ReadError::ReadingPayload)));
    }

    /// `Marshal_tools.to_fd_with_preamble` to a peer that hung up: the poll
    /// says the socket is not writable (macOS: `POLLHUP` alone), so nothing
    /// is written and it is `Writing_Preamble_Exception`; where the poll says
    /// it is writable (Linux), the write fails with `EPIPE`.
    #[test]
    fn writes_to_a_peer_that_hung_up() {
        let (mut w, r) = UnixStream::pair().unwrap();
        drop(r);
        let e = write_value(&mut w, &5u32).unwrap_err();
        let shown = ocaml_unix::unix_error_to_string(&e, "write", "");
        if cfg!(target_os = "macos") {
            assert_eq!(shown, "Marshal_tools.Writing_Preamble_Exception");
        } else {
            assert_eq!(shown, "Unix.Unix_error(Unix.EPIPE, \"write\", \"\")");
        }
        let (mut w, r) = UnixStream::pair().unwrap();
        drop(r);
        let e = ocaml_frame::write_value(&mut w, &crate::rt::ocaml_marshal::Value::int(1)).unwrap_err();
        if cfg!(target_os = "macos") {
            assert_eq!(
                ocaml_unix::unix_error_to_string(&e, "write", ""),
                "Marshal_tools.Writing_Preamble_Exception"
            );
        }
    }

    /// `Stdlib.input_value` (the connection type and the command the server
    /// reads): nothing is `End_of_file`, a value cut short
    /// `Failure "input_value: truncated object"`, at the length or after it.
    #[test]
    fn input_value_of_a_frame_cut_short() {
        let (mut w, mut r) = UnixStream::pair().unwrap();
        write_value(&mut w, &(1u32, "abcdef".to_string())).unwrap();
        drop(w);
        let mut buf = vec![];
        r.read_to_end(&mut buf).unwrap();
        assert_eq!(input_value::<(u32, String)>(&mut &buf[..]).unwrap(), (1, "abcdef".to_string()));
        assert!(matches!(input_value::<(u32, String)>(&mut &buf[..0]), Err(ReadError::EndOfFile)));
        for cut in [2, 4, buf.len() - 1] {
            let e = input_value::<(u32, String)>(&mut &buf[..cut]).unwrap_err();
            assert!(matches!(e, ReadError::Truncated));
            assert_eq!(read_error_to_string(&e, "read"), "Failure(\"input_value: truncated object\")");
        }
    }

    #[test]
    fn version_payload() {
        use monitor_utils::version_payload::*;
        let tracker = crate::connection_tracker::create();
        let s = serialize(&tracker, false, false);
        assert!(s.starts_with(r#"{"client_version":""#));
        let t = deserialize(&s).unwrap();
        assert_eq!(t.client_version, crate::build_id::build_revision());
        assert_eq!(t.tracker_id, crate::connection_tracker::log_id(&tracker));
        assert!(!t.terminate_monitor_on_version_mismatch);
        // Older clients sent just a client_version string
        let t = deserialize("abc").unwrap();
        assert_eq!(t.client_version, "abc");
        assert_eq!(t.tracker_id, "t#?");
        assert!(t.terminate_monitor_on_version_mismatch);
        assert_eq!(
            deserialize(r#"{"tracker_id":"x"}"#),
            Err(DeserializeError::Error("Missing client_version".to_string()))
        );
        assert!(matches!(deserialize("{nope"), Err(DeserializeError::Error(_))));
        // The accessors of `Yojson.Safe.Util` raise on a value of another
        // type (`to_string_option`, `to_bool_option`), and on a non-object.
        assert_eq!(
            deserialize(r#"{"client_version":3}"#),
            Err(DeserializeError::TypeError(
                r#"Yojson.Safe.Util.Type_error("Expected string or null, got int", _)"#.to_string()
            ))
        );
        assert_eq!(
            deserialize(r#"{"client_version":"v","terminate_monitor_on_version_mismatch":"no"}"#),
            Err(DeserializeError::TypeError(
                r#"Yojson.Safe.Util.Type_error("Expected bool or null, got string", _)"#
                    .to_string()
            ))
        );
        let t = deserialize(r#"{"client_version":"v","tracker_id":null}"#).unwrap();
        assert_eq!(t.tracker_id, "t#?");
        use monitor_utils::mismatch_payload;
        assert_eq!(
            mismatch_payload::serialize(false),
            r#"{"monitor_will_terminate":false}"#
        );
        assert!(!mismatch_payload::deserialize(r#"{"monitor_will_terminate":false}"#)
            .unwrap()
            .unwrap()
            .monitor_will_terminate);
        assert!(mismatch_payload::deserialize("{}").unwrap().unwrap().monitor_will_terminate);
        assert!(mismatch_payload::deserialize("x").unwrap().is_err());
        match mismatch_payload::deserialize("[1]") {
            Err(e) => assert_eq!(
                e.0,
                r#"Yojson.Safe.Util.Type_error("Can't get member 'monitor_will_terminate' of non-object type array", _)"#
            ),
            Ok(_) => panic!("expected Type_error"),
        }
    }

    #[test]
    fn values_round_trip() {
        use crate::server_command_types::*;
        let pos = crate::rt::diagnostic_fixtures::chars("a.php", 3, 2, 5);
        let back: crate::pos::Absolute = wire::decode(&wire::encode(&pos)).unwrap();
        assert_eq!(crate::pos::string(&back), crate::pos::string(&pos));
        let diag = crate::rt::diagnostic_fixtures::err(
            4110,
            crate::rt::diagnostic_fixtures::msg(pos, "boom"),
            vec![],
        );
        let status = server_status::T {
            liveness: StatusLiveness::LiveStatus,
            error_list: vec![diag],
            dropped_count: 2,
            last_recheck_stats: Some(crate::telemetry::int_(
                "n",
                3,
                crate::telemetry::create(),
            )),
            file_watcher_clock: Some(crate::server_notifier_types::Clock::Watchman("c:1".into())),
        };
        let r = MessageType::Response(
            CommandResult::Status(status.clone()),
            crate::connection_tracker::create(),
        );
        let back: MessageType<CommandResult> = wire::decode(&wire::encode(&r)).unwrap();
        match back {
            MessageType::Response(CommandResult::Status(s), _) => assert_eq!(s, status),
            _ => panic!("expected STATUS"),
        }
        let cmd: Command = (
            CmdMetadata {
                from: "f".into(),
                desc: "d".into(),
            },
            T::IdeFindRefsBySymbol(crate::find_refs_wire_format::cli_args::T {
                symbol_name: "C::m".into(),
                action: find_refs::Action::Member(
                    "\\C".into(),
                    find_refs::Member::Method("m".into()),
                ),
                stream_file: None,
                hint_suffixes: vec!["x".into()],
            }),
        );
        let back: Command = wire::decode(&wire::encode(&cmd)).unwrap();
        match back {
            (meta, T::IdeFindRefsBySymbol(args)) => {
                assert_eq!(meta, cmd.0);
                assert_eq!(args.symbol_name, "C::m");
                assert_eq!(
                    crate::find_refs_wire_format::cli_args::to_string(&args).unwrap(),
                    "C::m|Member,\\C,Method,m"
                );
            }
            _ => panic!("expected IDE_FIND_REFS_BY_SYMBOL"),
        }
        let p = crate::file_content::position::from_one_based(3, 4);
        let back: crate::file_content::position::T = wire::decode(&wire::encode(&p)).unwrap();
        assert_eq!(back, p);
        let set: crate::relative_path::set::T = [relative_path::RelativePath::make(
            relative_path::Prefix::Root,
            std::path::PathBuf::from("b.php"),
        )]
        .into_iter()
        .collect();
        let r = CommandResult::PackageLint(set.clone());
        match wire::decode::<CommandResult>(&wire::encode(&r)).unwrap() {
            CommandResult::PackageLint(s) => assert_eq!(s, set),
            _ => panic!("expected PACKAGE_LINT"),
        }
        let r = CommandResult::StatusSingle(((vec![], 0), None));
        match wire::decode::<CommandResult>(&wire::encode(&r)).unwrap() {
            CommandResult::StatusSingle(((errors, 0), None)) => assert!(errors.is_empty()),
            _ => panic!("expected STATUS_SINGLE"),
        }
        assert!(wire::decode::<Command>(b"garbage").is_err());
    }

    #[test]
    fn connection_error_telemetry() {
        use monitor_utils::*;
        let e = ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
            server_exists: false,
            failure_phase: ConnectFailurePhase::ConnectOpenSocket,
            failure_reason: ConnectFailureReason::ConnectException(crate::exception::wrap(
                UnixError(std::io::Error::from_raw_os_error(libc::ENOENT), "connect"),
            )),
        });
        assert_eq!(
            connection_error_to_telemetry(&e).0,
            "Connect_open_socket:ENOENT [absent]"
        );
        assert_eq!(
            connection_error_to_telemetry(&ConnectionError::ServerDormantOutOfRetries).0,
            "Server_dormant_out_of_retries"
        );
    }
}
