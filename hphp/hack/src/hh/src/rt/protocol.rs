// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The client-server protocol: the conversation between `hh_client`, the
//! monitor and `hh_server` over `Server_files.socket_file` and the pipes from
//! the monitor to the server.
//!
//! Owned by **MON** (plan §3.1) for the monitor's end; the client's end
//! (`Client_connect`, `Client_start`, `Client_stop`) and the server's end
//! are transliterated with their decisions.
//!
//! As in OCaml, the monitor (`crate::monitor_main`) accepts the
//! connection, checks the client's version, and hands the file descriptor
//! to the server (`SCM_RIGHTS`, `rt::fd_passing`), which then talks to the
//! client. OCaml `Marshal`s every value after a preamble; here every value is
//! a frame: a `u32` (little-endian) length, then that many bytes (plan §6
//! #34: only our binaries talk to each other). The handshake keeps OCaml's
//! messages, in OCaml's order:
//!
//! | # | direction | frame | OCaml |
//! |---|---|---|---|
//! | 1 | C → M | the JSON of [`monitor_utils::version_payload`] | the version string (and a newline, not sent here) |
//! | 2 | M → C | [`monitor_utils::ConnectionState`] | `connection_state` |
//! | 3 | C → M | [`monitor_rpc::Command`] (`HANDOFF_TO_SERVER` or `SHUT_DOWN`) | `Monitor_rpc.command` |
//! | 4 | M → C | [`prehandoff::Msg`]s, the last a `Sentinel` | `Prehandoff.msg` |
//! | | M → S | [`monitor_rpc::MonitorToServerHandoffMsg`], then the fd, on the pipe of the request | the same |
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

#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

use std::io;
use std::io::Read;
use std::io::Write;
use std::os::fd::AsRawFd;
use std::os::unix::net::UnixStream;
use std::time::Duration;

use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::rt::ocaml_unix;

// ~~ Frames ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
pub const maximum_payload_size: usize = u32::MAX as usize;

/// Writes one frame: the length (`u32`, little-endian), then the payload.
pub fn write_frame(w: &mut impl Write, payload: &[u8]) -> Result<(), WriteError> {
    if payload.len() > maximum_payload_size {
        // `Marshal_tools.Payload_Size_Too_Large_Exception`
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Marshal_tools.Payload_Size_Too_Large_Exception",
        ));
    }
    let mut buf = Vec::with_capacity(4 + payload.len());
    buf.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    buf.extend_from_slice(payload);
    w.write_all(&buf)?;
    w.flush()
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

/// Writes a value as a frame (`Marshal_tools.to_fd_with_preamble`).
pub fn write_value<V: Serialize>(w: &mut impl Write, v: &V) -> Result<(), WriteError> {
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
    use std::io::Write;

    use super::ReadError;
    use crate::rt::ocaml_marshal;
    use crate::rt::ocaml_marshal::Value;

    /// `Marshal_tools.preamble_start_sentinel`
    const PREAMBLE_START_SENTINEL: u8 = 142;
    /// `Marshal_tools.expected_preamble_size`
    const EXPECTED_PREAMBLE_SIZE: usize = 5;

    /// `Marshal_tools.to_fd_with_preamble fd v` (no flags).
    pub fn write_value(w: &mut impl Write, v: &Value) -> io::Result<()> {
        let payload = ocaml_marshal::to_bytes(v, &[])
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e.0))?;
        if payload.len() >= u32::MAX as usize {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Marshal_tools.Payload_Size_Too_Large_Exception",
            ));
        }
        let mut buf = Vec::with_capacity(EXPECTED_PREAMBLE_SIZE + payload.len());
        buf.push(PREAMBLE_START_SENTINEL);
        buf.extend_from_slice(&(payload.len() as u32).to_be_bytes());
        buf.extend_from_slice(&payload);
        w.write_all(&buf)?;
        w.flush()
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
    pub fn write_version(w: &mut impl Write, version: &str) -> io::Result<()> {
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
        w: &mut impl Write,
        c: &super::monitor_utils::ConnectionState,
    ) -> io::Result<()> {
        write_value(w, &super::monitor_utils::connection_state_to_ocaml(c))
    }

    pub fn read_connection_state(
        r: &mut impl Read,
    ) -> Result<super::monitor_utils::ConnectionState, ReadError> {
        let v = read_value(r)?;
        super::monitor_utils::connection_state_of_ocaml(&v).map_err(ReadError::Malformed)
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

    /// A value of a type that needs the typing port (`Lints_core.t`), which
    /// has no `serde`: it cannot cross the socket yet.
    pub mod port_only {
        use super::*;

        pub fn serialize<S: Serializer, X>(_x: &X, _s: S) -> Result<S::Ok, S::Error> {
            todo!(
                "Server_lint_types.result over the socket: Lints_core.t (behind the feature port) has no serde"
            )
        }

        pub fn deserialize<'de, D: Deserializer<'de>, X>(_d: D) -> Result<X, D::Error> {
            todo!(
                "Server_lint_types.result over the socket: Lints_core.t (behind the feature port) has no serde"
            )
        }
    }

    /// The result of `STATUS_SINGLE`: the TASTs (behind the feature `port`,
    /// with no `serde`) cannot cross the socket yet; the diagnostics can.
    pub mod status_single_result {
        use super::*;
        use crate::server_progress::FinalizedDiagnostic;

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

/// `Monitor_rpc` (`client_and_server/monitor_rpc.ml`): what the client asks
/// for after the version check, what the monitor sends the server with each
/// client, and the server's receipt file.
pub mod monitor_rpc {
    use serde::Deserialize;
    use serde::Serialize;

    use crate::connection_tracker;
    use crate::hh_logger;
    use crate::rt::ocaml_unix;
    use crate::yojson::safe as yojson;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
    pub enum PipeType {
        Default,
        Priority,
        ForceDormantStartOnly,
    }

    pub fn pipe_type_to_string(p: PipeType) -> &'static str {
        match p {
            PipeType::Default => "default",
            PipeType::Priority => "priority",
            PipeType::ForceDormantStartOnly => "force_dormant_start_only",
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct HandoffOptions {
        /// If server is dormant because it is waiting for Informant to start one,
        /// set this to true to start a server anyway.
        pub force_dormant_start: bool,
        /// There can be multiple channels between server and monitor in order
        /// to prioritize some requests over others. Connecting code needs to specify
        /// which channel it wants to use.
        pub pipe_type: PipeType,
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub enum Command {
        HANDOFF_TO_SERVER(connection_tracker::T, HandoffOptions),
        /// Shut down all servers and then the monitor.
        SHUT_DOWN(connection_tracker::T),
    }

    /// Sent by monitor in ServerMonitor, received by server in ServerClientProvider
    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct MonitorToServerHandoffMsg {
        pub m2s_tracker: connection_tracker::T,
        /// A unique number incremented for each client socket handoff from monitor to server.
        /// Useful to correlate monitor and server logs.
        pub m2s_sequence_number: isize,
    }

    const RECEIPT_KEY: &str = "sequence_number_high_water_mark";

    /// `receipt_serialize`
    pub fn receipt_serialize(i: isize) -> yojson::T {
        yojson::T::Assoc(vec![(RECEIPT_KEY.to_string(), yojson::T::Int(i))])
    }

    /// `receipt_deserialize`: `Err` is the `Failure` it raises.
    pub fn receipt_deserialize(json: &yojson::T) -> Result<isize, String> {
        match json {
            yojson::T::Assoc(pairs) => match pairs.iter().find(|(k, _)| k == RECEIPT_KEY) {
                Some((_, yojson::T::Int(i))) => Ok(*i),
                _ => Err(format!("{} not found or not an int", RECEIPT_KEY)),
            },
            _ => Err("expected JSON object".to_string()),
        }
    }

    /// `Sys_utils.protected_write_exn filename content`: under a write
    /// lock (`lockf F_LOCK`), writes `content` at the start of the file and
    /// truncates it there; the file is made with mode 0o666 (umask 0).
    pub fn protected_write_exn(filename: &str, content: &str) -> std::io::Result<()> {
        use std::io::Write;
        use std::os::fd::AsRawFd;
        if content.is_empty() {
            return Err(std::io::Error::other("Failure(\"Empty content not supported.\")"));
        }
        let mut f = ocaml_unix::openfile_with_umask(
            filename,
            &[ocaml_unix::OpenFlag::ORdwr, ocaml_unix::OpenFlag::OCreat],
            0o666,
            0o000,
        )?;
        ocaml_unix::lockf(f.as_raw_fd(), ocaml_unix::LockCommand::FLock, 0)?;
        // (`Unix.write_substring` at the current position, which is the
        // start of the file just opened.)
        f.write_all(content.as_bytes())?;
        f.set_len(content.len() as u64)?;
        Ok(())
    }

    /// `Sys_utils.protected_read_exn filename`: the content under a read
    /// lock, retried (after 1 ms) while the file is empty.
    pub fn protected_read_exn(filename: &str) -> std::io::Result<String> {
        use std::io::Read;
        use std::io::Seek;
        use std::os::fd::AsRawFd;
        loop {
            let mut f = std::fs::File::open(filename)?;
            ocaml_unix::lockf(f.as_raw_fd(), ocaml_unix::LockCommand::FRlock, 0)?;
            let total = f.seek(std::io::SeekFrom::End(0))?;
            f.seek(std::io::SeekFrom::Start(0))?;
            let mut buf = vec![0u8; total as usize];
            let mut offset = 0;
            while offset < buf.len() {
                let n = f.read(&mut buf[offset..])?;
                if n == 0 {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::UnexpectedEof,
                        "End_of_file",
                    ));
                }
                offset += n;
            }
            drop(f);
            if buf.is_empty() {
                std::thread::sleep(std::time::Duration::from_millis(1));
                continue;
            }
            return Ok(String::from_utf8_lossy(&buf).into_owned());
        }
    }

    /// This writes to the specified file. Invariants maintained by callers:
    /// (1) the file is deleted shortly after the server launches, if it already existed,
    /// (2) after the server has first received a handoff then it writes to the file,
    /// (3) after each successive handoff the server overwrites the file,
    /// (4) each write is protected by a unix writer lock.
    /// In case of failure, we log but don't raise exceptions, in the hope that a
    /// future write will succeed.
    pub fn write_server_receipt_to_monitor_file(
        server_receipt_to_monitor_file: &str,
        sequence_number_high_water_mark: isize,
    ) {
        let json = crate::rt::yojson_ext::pretty_to_string(&receipt_serialize(
            sequence_number_high_water_mark,
        ));
        if let Err(e) = protected_write_exn(server_receipt_to_monitor_file, &json) {
            hh_logger::log(&format!(
                "SERVER_RECEIPT_TO_MONITOR(write) {}\n{}",
                ocaml_unix::unix_error_to_string(&e, "open", server_receipt_to_monitor_file),
                ""
            ));
            // `Hack_event_logger.server_receipt_to_monitor_write_exn`: a
            // no-op in the OSS build.
        }
    }

    /// This reads the specified file, under a unix reader lock.
    /// There are legitimate scenarios where the file might not exist,
    /// e.g. if the server has only recently started up and hasn't yet
    /// written any receipts. In this case we return None.
    /// If there are failures e.g. a malformed file content, then we write
    /// a log and return None.
    pub fn read_server_receipt_to_monitor_file(server_receipt_to_monitor_file: &str) -> Option<isize> {
        let content = match protected_read_exn(server_receipt_to_monitor_file) {
            Ok(content) => content,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return None,
            Err(e) => {
                hh_logger::log(&format!(
                    "SERVER_RECEIPT_TO_MONITOR(read) {}\n{}\n{}",
                    ocaml_unix::unix_error_to_string(&e, "open", server_receipt_to_monitor_file),
                    "",
                    "[not yet read content]"
                ));
                return None;
            }
        };
        let res = match crate::rt::yojson_ext::from_string(&content) {
            Ok(json) => receipt_deserialize(&json),
            Err(e) => Err(format!("Yojson.Json_error({})", crate::rt::ocaml_printf::sprintf_S(&e.0))),
        };
        match res {
            Ok(i) => Some(i),
            Err(msg) => {
                // `Hack_event_logger.server_receipt_to_monitor_read_exn`: a
                // no-op in the OSS build.
                hh_logger::log(&format!(
                    "SERVER_RECEIPT_TO_MONITOR(read) {}\n{}\n{}",
                    msg, "", content
                ));
                None
            }
        }
    }
}

// ~~ Monitor_utils ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Monitor_utils` (`monitor/monitor_client_api/monitor_utils.ml`).
pub mod monitor_utils {
    use std::sync::LazyLock;

    use serde::Deserialize;
    use serde::Serialize;

    use crate::build_id;
    use crate::connection_tracker;
    use crate::exception;
    use crate::rt::ocaml_sys;
    use crate::rt::ocaml_unix;
    use crate::telemetry;
    use crate::yojson::safe as yojson;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct MonitorConfig {
        /// The socket file on which the monitor is listening for connections.
        pub socket_file: String,
        /// This lock is held when a monitor is alive.
        pub lock_file: String,
        /// The path to the server log file
        pub server_log_file: String,
        /// The path to the monitor log file
        pub monitor_log_file: String,
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct BuildMismatchInfo {
        pub existing_version: String,
        pub existing_build_commit_time: String,
        pub existing_argv: Vec<String>,
        pub existing_launch_time: f64,
    }

    /// `current_build_info`: OCaml computes it when the program starts (its
    /// launch time is then); here when it is first used. The server calls
    /// it as it starts ([`crate::rt::protocol::server_end`] does, when it
    /// binds), so that the launch time is the server's.
    pub fn current_build_info() -> BuildMismatchInfo {
        static CURRENT_BUILD_INFO: LazyLock<BuildMismatchInfo> =
            LazyLock::new(|| BuildMismatchInfo {
                existing_version: build_id::build_revision(),
                existing_build_commit_time: build_id::build_commit_time_string(),
                existing_argv: ocaml_sys::argv(),
                existing_launch_time: ocaml_unix::gettimeofday(),
            });
        CURRENT_BUILD_INFO.clone()
    }

    #[derive(Debug)]
    pub enum ConnectFailureReason {
        ConnectTimeout,
        ConnectException(exception::T),
    }

    /// `show_connect_failure_reason` (`[@@deriving show { with_path = false }]`,
    /// with its printer for the exception).
    pub fn show_connect_failure_reason(r: &ConnectFailureReason) -> String {
        match r {
            ConnectFailureReason::ConnectTimeout => "Connect_timeout".to_string(),
            ConnectFailureReason::ConnectException(e) => {
                format!("Connect_exception({})", exception::get_ctor_string(e))
            }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ConnectFailurePhase {
        ConnectOpenSocket,
        ConnectSendVersion,
        ConnectSendNewline,
        ConnectReceiveConnectionOk,
        ConnectSendShutdown,
    }

    /// `show_connect_failure_phase` (`[@@deriving show { with_path = false }]`)
    pub fn show_connect_failure_phase(p: ConnectFailurePhase) -> &'static str {
        match p {
            ConnectFailurePhase::ConnectOpenSocket => "Connect_open_socket",
            ConnectFailurePhase::ConnectSendVersion => "Connect_send_version",
            ConnectFailurePhase::ConnectSendNewline => "Connect_send_newline",
            ConnectFailurePhase::ConnectReceiveConnectionOk => "Connect_receive_connection_ok",
            ConnectFailurePhase::ConnectSendShutdown => "Connect_send_shutdown",
        }
    }

    #[derive(Debug)]
    pub struct ConnectToMonitorFailure {
        /// This reflects the state of the lock file shortly after the failure happened.
        pub server_exists: bool,
        pub failure_phase: ConnectFailurePhase,
        pub failure_reason: ConnectFailureReason,
    }

    #[derive(Debug)]
    pub enum ConnectionError {
        ConnectToMonitorFailure(ConnectToMonitorFailure),
        ServerDied,
        /// Server dormant, i.e. waiting for a rebase to settle, and monitor's queue
        /// of pending connections in the now-full queue of connections waiting for the next server.
        ServerDormant,
        ServerDormantOutOfRetries,
        /// hh_client binary is a different version from hh_server binary,
        /// so hh_server will terminate.
        BuildIdMismatchedMonitorWillTerminate(Option<BuildMismatchInfo>),
        /// hh_client binary is a different version and must abandon its connection attempt
        BuildIdMismatchedClientMustTerminate(BuildMismatchInfo),
    }

    /// `pp_build_mismatch_info` (`[@@deriving show]`), on one line (OCaml's
    /// `Format` boxes may break it; only the logs show it).
    fn show_build_mismatch_info(info: &BuildMismatchInfo) -> String {
        use crate::rt::ocaml_printf::sprintf_S;
        format!(
            "{{ Monitor_utils.existing_version = {}; existing_build_commit_time = {}; existing_argv = [{}]; existing_launch_time = {} }}",
            sprintf_S(&info.existing_version),
            sprintf_S(&info.existing_build_commit_time),
            info.existing_argv
                .iter()
                .map(|s| sprintf_S(s))
                .collect::<Vec<_>>()
                .join("; "),
            info.existing_launch_time,
        )
    }

    /// `show_connection_error` (`[@@deriving show { with_path = false }]`),
    /// on one line (OCaml's `Format` boxes may break the records; only the
    /// logs show them).
    pub fn show_connection_error(e: &ConnectionError) -> String {
        match e {
            ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
                server_exists,
                failure_phase,
                failure_reason,
            }) => format!(
                "(Connect_to_monitor_failure {{ server_exists = {}; failure_phase = {}; failure_reason = {} }})",
                server_exists,
                show_connect_failure_phase(*failure_phase),
                show_connect_failure_reason(failure_reason)
            ),
            ConnectionError::ServerDied => "Server_died".to_string(),
            ConnectionError::ServerDormant => "Server_dormant".to_string(),
            ConnectionError::ServerDormantOutOfRetries => "Server_dormant_out_of_retries".to_string(),
            ConnectionError::BuildIdMismatchedMonitorWillTerminate(None) => {
                "(Build_id_mismatched_monitor_will_terminate None)".to_string()
            }
            ConnectionError::BuildIdMismatchedMonitorWillTerminate(Some(info)) => format!(
                "(Build_id_mismatched_monitor_will_terminate (Some {}))",
                show_build_mismatch_info(info)
            ),
            ConnectionError::BuildIdMismatchedClientMustTerminate(info) => format!(
                "(Build_id_mismatched_client_must_terminate {})",
                show_build_mismatch_info(info)
            ),
        }
    }

    /// The telemetry we get from this ends up appearing in our telemetry a HUGE number of times.
    /// I guess [HackEventLogger.client_connect_once_failure] is just called a lot.
    /// We therefore take pains to make this as minimal as we can.
    pub fn connection_error_to_telemetry(e: &ConnectionError) -> (String, Option<telemetry::T>) {
        match e {
            ConnectionError::ServerDied
            | ConnectionError::ServerDormant
            | ConnectionError::ServerDormantOutOfRetries
            | ConnectionError::BuildIdMismatchedMonitorWillTerminate(_)
            | ConnectionError::BuildIdMismatchedClientMustTerminate(_) => {
                // these errors come from MonitorConnection.connect_to_monitor [match cstate]
                (show_connection_error(e), None)
            }
            ConnectionError::ConnectToMonitorFailure(ConnectToMonitorFailure {
                server_exists,
                failure_phase,
                failure_reason,
            }) => {
                let (reason, stack) = match failure_reason {
                    ConnectFailureReason::ConnectTimeout => {
                        // comes from MonitorConnection.connect_to_monitor [Unix.open_connection]
                        ("Connect_timeout".to_string(), None)
                    }
                    ConnectFailureReason::ConnectException(e) => {
                        // comes from MonitorConnection.connect_to_monitor and [phase] says what part
                        let ctor = exception::get_ctor_string(e);
                        let errno = exception::unwrap(e)
                            .downcast_ref::<UnixError>()
                            .and_then(|u| u.0.raw_os_error().map(|c| (c, u.1)));
                        match errno {
                            Some((libc::ECONNREFUSED, "connect")) => {
                                // Generally comes from [Unix.open_connection]
                                ("ECONNREFUSED".to_string(), None)
                            }
                            Some((libc::ENOENT, "connect")) => {
                                // Generally comes from [Unix.open_connection]
                                ("ENOENT".to_string(), None)
                            }
                            Some((libc::EMFILE, "pipe")) => {
                                // Usually comes from [Process.exec Exec_command.Pgrep]
                                ("EMFILE".to_string(), None)
                            }
                            Some((libc::ECONNRESET, "read")) => {
                                // Usually from [let cstate : ... = from_channel_without_buffering ic]
                                ("ECONNRESET".to_string(), None)
                            }
                            _ => (
                                ctor,
                                Some(exception::clean_stack(&exception::get_backtrace_string(e))),
                            ),
                        }
                    }
                };
                let exists = if *server_exists { "exists" } else { "absent" };
                let reason = format!(
                    "{}:{} [{}]",
                    show_connect_failure_phase(*failure_phase),
                    reason,
                    exists
                );
                let telemetry =
                    stack.map(|value| telemetry::string_(None, "stack", &value, telemetry::create()));
                (reason, telemetry)
            }
        }
    }

    /// `Unix.Unix_error (err, fun_name, "")`, as an exception: what
    /// `ConnectException` wraps.
    pub struct UnixError(pub std::io::Error, pub &'static str);

    impl std::fmt::Debug for UnixError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(&ocaml_unix::unix_error_to_string(&self.0, self.1, ""))
        }
    }

    /// The first part of the client/monitor handshake is that client sends
    /// a [VersionPayload.serialized] over the socket, followed by a newline byte.
    /// Note that [VersionPayload.serialized] is just an ocaml string, and can
    /// never be anything else, because we have to maintain forwards and backwards
    /// compatibility between different version of hh_client and hh_server.
    pub mod version_payload {
        use super::*;

        pub type Serialized = String;

        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct T {
            pub client_version: String,
            pub tracker_id: String,
            pub terminate_monitor_on_version_mismatch: bool,
            /// What a Rust client asks a Rust monitor (the field
            /// [`RUST_TERMINATE_KEY`], which only Rust clients send and only
            /// Rust monitors read): `terminate_monitor_on_version_mismatch`
            /// is then what it asks a monitor of the other implementation
            /// (see [`super::cross_implementation_policy`]).
            pub rust_terminate_monitor_on_version_mismatch: Option<bool>,
        }

        /// The field of the payload that only the Rust implementation reads.
        pub const RUST_TERMINATE_KEY: &str = "rust_terminate_monitor_on_version_mismatch";

        /// `serialize ~tracker ~terminate_monitor_on_version_mismatch`, by a
        /// Rust client: `terminate_monitor_on_version_mismatch` is what it
        /// asks a Rust monitor, `terminate_other_implementation` what it asks
        /// an OCaml monitor (the OCaml's field).
        pub fn serialize(
            tracker: &connection_tracker::T,
            terminate_monitor_on_version_mismatch: bool,
            terminate_other_implementation: bool,
        ) -> Serialized {
            yojson::to_string(&yojson::T::Assoc(vec![
                (
                    "client_version".to_string(),
                    yojson::T::String(build_id::build_revision()),
                ),
                (
                    "tracker_id".to_string(),
                    yojson::T::String(connection_tracker::log_id(tracker)),
                ),
                (
                    "terminate_monitor_on_version_mismatch".to_string(),
                    yojson::T::Bool(terminate_other_implementation),
                ),
                (
                    RUST_TERMINATE_KEY.to_string(),
                    yojson::T::Bool(terminate_monitor_on_version_mismatch),
                ),
            ]))
        }

        /// How `deserialize` fails: its `Error`, or the exception that the
        /// `Yojson.Safe.Util` accessors raise (`Type_error`, as
        /// `Printexc.to_string` shows it), which OCaml does not catch there.
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum DeserializeError {
            Error(String),
            Type_error(String),
        }

        pub fn deserialize(s: &str) -> Result<T, DeserializeError> {
            // Newer clients send version in a json object; older clients sent just a client_version string
            let json = if s.starts_with('{') {
                match yojson::from_string(s) {
                    Ok(json) => json,
                    Err(exn) => return Err(DeserializeError::Error(exn.to_string())),
                }
            } else {
                yojson::T::Assoc(vec![(
                    "client_version".to_string(),
                    yojson::T::String(s.to_string()),
                )])
            };
            let raised = DeserializeError::Type_error;
            let client_version =
                match util::to_string_option(util::member("client_version", &json).map_err(raised)?)
                    .map_err(raised)?
                {
                    Some(s) => s,
                    None => return Err(DeserializeError::Error("Missing client_version".to_string())),
                };
            let tracker_id =
                util::to_string_option(util::member("tracker_id", &json).map_err(raised)?)
                    .map_err(raised)?
                    .unwrap_or_else(|| "t#?".to_string());
            let terminate_monitor_on_version_mismatch = util::to_bool_option(
                util::member("terminate_monitor_on_version_mismatch", &json).map_err(raised)?,
            )
            .map_err(raised)?
            .unwrap_or(true);
            let rust_terminate_monitor_on_version_mismatch =
                util::to_bool_option(util::member(RUST_TERMINATE_KEY, &json).map_err(raised)?)
                    .map_err(raised)?;
            Ok(T {
                client_version,
                tracker_id,
                terminate_monitor_on_version_mismatch,
                rust_terminate_monitor_on_version_mismatch,
            })
        }
    }

    /// The accessors of `Yojson.Safe.Util` that the payloads use. They raise
    /// `Type_error (msg, json)`: here an `Err` of what `Printexc.to_string`
    /// shows of it.
    mod util {
        use super::yojson;

        /// `Yojson.Safe.Util.typeof`
        fn typeof_(json: &yojson::T) -> &'static str {
            match json {
                yojson::T::Assoc(_) => "object",
                yojson::T::Bool(_) => "bool",
                yojson::T::Float(_) => "float",
                yojson::T::Int(_) => "int",
                yojson::T::List(_) => "array",
                yojson::T::Null => "null",
                yojson::T::String(_) => "string",
                yojson::T::Intlit(_) => "intlit",
            }
        }

        /// `typerr msg js`
        fn typerr(msg: &str, json: &yojson::T) -> String {
            format!(
                "Yojson.Safe.Util.Type_error({}, _)",
                crate::rt::ocaml_printf::sprintf_S(&format!("{}{}", msg, typeof_(json)))
            )
        }

        /// `member name json`: the field `name` of an object, `Null` if
        /// there is none.
        pub fn member<'a>(name: &str, json: &'a yojson::T) -> Result<&'a yojson::T, String> {
            match json {
                yojson::T::Assoc(fields) => Ok(fields
                    .iter()
                    .find(|(k, _)| k == name)
                    .map_or(&yojson::T::Null, |(_, v)| v)),
                js => Err(typerr(
                    &format!("Can't get member '{}' of non-object type ", name),
                    js,
                )),
            }
        }

        pub fn to_string_option(json: &yojson::T) -> Result<Option<String>, String> {
            match json {
                yojson::T::String(s) => Ok(Some(s.clone())),
                yojson::T::Null => Ok(None),
                js => Err(typerr("Expected string or null, got ", js)),
            }
        }

        pub fn to_bool_option(json: &yojson::T) -> Result<Option<bool>, String> {
            match json {
                yojson::T::Bool(b) => Ok(Some(*b)),
                yojson::T::Null => Ok(None),
                js => Err(typerr("Expected bool or null, got ", js)),
            }
        }
    }

    /// The second part of the client/monitor handshake is that monitor sends
    /// [connection_state] over the socket. In case of version mismatch it sends
    /// [Build_id_mismatch_v3], which includes a [MismatchPayload.serialized].
    /// Note that this is just an ocaml string, and can never be anything else,
    /// because we have to maintain forwards and backwards compatibility between
    /// different versions of hh_client and hh_server. (However, every version
    /// in existince understands the binary format of Build_id_mismatch_v3...)
    pub mod mismatch_payload {
        use super::*;

        pub type Serialized = String;

        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct T {
            pub monitor_will_terminate: bool,
        }

        pub fn serialize(monitor_will_terminate: bool) -> Serialized {
            yojson::to_string(&yojson::T::Assoc(vec![(
                "monitor_will_terminate".to_string(),
                yojson::T::Bool(monitor_will_terminate),
            )]))
        }

        /// `Yojson.Safe.Util.(json |> member .. |> to_bool_option)` is
        /// outside the `try`: its `Type_error` is not caught, here or by the
        /// callers (until the catch-all of the program). It is the outer
        /// error.
        pub fn deserialize(
            s: &str,
        ) -> Result<Result<T, String>, super::super::UncaughtReadError> {
            let json = match yojson::from_string(s) {
                Ok(json) => json,
                Err(exn) => return Ok(Err(exn.to_string())),
            };
            let monitor_will_terminate = match util::member("monitor_will_terminate", &json)
                .and_then(util::to_bool_option)
            {
                Ok(b) => b.unwrap_or(true),
                Err(exn) => return Err(super::super::UncaughtReadError(exn)),
            };
            Ok(Ok(T {
                monitor_will_terminate,
            }))
        }
    }

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub enum ConnectionState {
        ConnectionOk,
        /// Build_is_mismatch is never used, but it can't be removed, because
        /// the sequence of constructors here is part of the binary protocol
        /// we want to support between mismatched versions of client_server.
        BuildIdMismatch,
        /// Build_id_mismatch_ex also isn't used.
        BuildIdMismatchEx(BuildMismatchInfo),
        /// Build_id_mismatch_v3 is used!
        BuildIdMismatchV3(BuildMismatchInfo, mismatch_payload::Serialized),
        /// Connection_ok_v2 isn't used yet, but might be
        ConnectionOkV2(String),
    }

    /// `show_connection_state` (`[@@deriving show]`), for the constructors the
    /// server sends; the logs only.
    pub fn show_connection_state(c: &ConnectionState) -> String {
        match c {
            ConnectionState::ConnectionOk => "Monitor_utils.Connection_ok".to_string(),
            ConnectionState::BuildIdMismatch => "Monitor_utils.Build_id_mismatch".to_string(),
            ConnectionState::BuildIdMismatchEx(info) => format!(
                "(Monitor_utils.Build_id_mismatch_ex {})",
                show_build_mismatch_info(info)
            ),
            ConnectionState::BuildIdMismatchV3(info, payload) => format!(
                "(Monitor_utils.Build_id_mismatch_v3 ({}, {}))",
                show_build_mismatch_info(info),
                crate::rt::ocaml_printf::sprintf_S(payload)
            ),
            ConnectionState::ConnectionOkV2(s) => format!(
                "(Monitor_utils.Connection_ok_v2 {})",
                crate::rt::ocaml_printf::sprintf_S(s)
            ),
        }
    }

    /// Result of a shutdown monitor RPC.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ShutdownResult {
        /// Request sent and channel hung up, indicating the process has exited.
        SHUTDOWN_VERIFIED,
        /// Request sent, but channel hasn't hung up.
        SHUTDOWN_UNVERIFIED,
    }

    /// Message we send to the --waiting-client
    pub const ready: &str = "ready";

    // ~~ The two implementations ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    /// What a client and a monitor of different implementations (Rust and
    /// OCaml, installed side by side and sharing the files of a root) do on
    /// their version mismatch.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum CrossImplementationPolicy {
        /// Neither replaces the other's server: the Rust monitor answers an
        /// OCaml client `monitor_will_terminate = false` (the OCaml client
        /// says "Error: version mismatch" and exits `Build_id_mismatch`); a
        /// Rust client asks an OCaml monitor not to terminate, says which
        /// server runs and how to stop it, and exits `Build_id_mismatch`.
        /// An explicit `stop` still stops the other's server.
        Refuse,
        /// As between two versions of one implementation (the OCaml's
        /// `terminate_monitor_on_version_mismatch`).
        TakeOver,
    }

    /// The policy between the two implementations: the one place to change
    /// it.
    pub fn cross_implementation_policy() -> CrossImplementationPolicy {
        CrossImplementationPolicy::Refuse
    }

    /// What a Rust client asks a monitor of the other implementation, when
    /// it would ask a Rust one `terminate` (a `stop` asks both to terminate,
    /// whatever the policy).
    pub fn terminate_other_implementation(terminate: bool, is_stop: bool) -> bool {
        match cross_implementation_policy() {
            _ if is_stop => true,
            CrossImplementationPolicy::Refuse => false,
            CrossImplementationPolicy::TakeOver => terminate,
        }
    }

    /// Whether this (Rust) monitor terminates on a version mismatch with the
    /// client of `payload`.
    pub fn monitor_will_terminate(payload: &version_payload::T) -> bool {
        if build_id::is_rust_build_revision(&payload.client_version) {
            payload
                .rust_terminate_monitor_on_version_mismatch
                .unwrap_or(payload.terminate_monitor_on_version_mismatch)
        } else {
            match cross_implementation_policy() {
                CrossImplementationPolicy::Refuse => false,
                CrossImplementationPolicy::TakeOver => payload.terminate_monitor_on_version_mismatch,
            }
        }
    }

    /// Whether the monitor of a mismatch is of the other implementation.
    pub fn is_other_implementation(info: &BuildMismatchInfo) -> bool {
        !build_id::is_rust_build_revision(&info.existing_version)
    }

    /// What the Rust client says when it finds a monitor of the other
    /// implementation, which it does not replace.
    pub fn other_implementation_message(info: &BuildMismatchInfo, root: &str) -> String {
        format!(
            "Error: an OCaml hh_server is running for {}; this hh_client is the Rust one and does not replace it.\n  hh_server '{}', version '{}', launched {}\nStop it first (`hh_client stop {}`, with either hh_client), then retry.\n",
            root,
            info.existing_argv.join(" "),
            info.existing_version,
            crate::utils::timestring(info.existing_launch_time),
            root
        )
    }

    // ~~ The OCaml values of the handshake ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    use crate::rt::ocaml_marshal::Value;

    fn build_mismatch_info_to_ocaml(info: &BuildMismatchInfo) -> Value {
        Value::block(
            0,
            vec![
                Value::string(info.existing_version.as_bytes()),
                Value::string(info.existing_build_commit_time.as_bytes()),
                Value::list(info.existing_argv.iter().map(|a| Value::string(a.as_bytes()))),
                Value::double(info.existing_launch_time),
            ],
        )
    }

    fn string_of_ocaml(v: &Value) -> Result<String, String> {
        v.as_bytes()
            .map(|b| String::from_utf8_lossy(b).into_owned())
            .map_err(|e| e.0)
    }

    fn build_mismatch_info_of_ocaml(v: &Value) -> Result<BuildMismatchInfo, String> {
        let f = v.fields(0, 4).map_err(|e| e.0)?;
        Ok(BuildMismatchInfo {
            existing_version: string_of_ocaml(&f[0])?,
            existing_build_commit_time: string_of_ocaml(&f[1])?,
            existing_argv: f[2]
                .list_items()
                .map_err(|e| e.0)?
                .into_iter()
                .map(string_of_ocaml)
                .collect::<Result<_, _>>()?,
            existing_launch_time: f[3].as_double().map_err(|e| e.0)?,
        })
    }

    /// The OCaml value of a `connection_state`, as the OCaml monitor
    /// marshals it.
    pub fn connection_state_to_ocaml(c: &ConnectionState) -> Value {
        match c {
            ConnectionState::ConnectionOk => Value::int(0),
            ConnectionState::BuildIdMismatch => Value::int(1),
            ConnectionState::BuildIdMismatchEx(info) => {
                Value::block(0, vec![build_mismatch_info_to_ocaml(info)])
            }
            ConnectionState::BuildIdMismatchV3(info, payload) => Value::block(
                1,
                vec![
                    build_mismatch_info_to_ocaml(info),
                    Value::string(payload.as_bytes()),
                ],
            ),
            ConnectionState::ConnectionOkV2(s) => Value::block(2, vec![Value::string(s.as_bytes())]),
        }
    }

    /// A `connection_state` of its OCaml value; `Err` for a value of
    /// another type.
    pub fn connection_state_of_ocaml(v: &Value) -> Result<ConnectionState, String> {
        if let Ok(n) = v.as_int() {
            return match n {
                0 => Ok(ConnectionState::ConnectionOk),
                1 => Ok(ConnectionState::BuildIdMismatch),
                n => Err(format!("connection_state: constant {}", n)),
            };
        }
        let (tag, fields) = v.as_block().map_err(|e| e.0)?;
        match (tag, fields) {
            (0, [info]) => Ok(ConnectionState::BuildIdMismatchEx(
                build_mismatch_info_of_ocaml(info)?,
            )),
            (1, [info, payload]) => Ok(ConnectionState::BuildIdMismatchV3(
                build_mismatch_info_of_ocaml(info)?,
                string_of_ocaml(payload)?,
            )),
            (2, [s]) => Ok(ConnectionState::ConnectionOkV2(string_of_ocaml(s)?)),
            (tag, f) => Err(format!("connection_state: block {} of {}", tag, f.len())),
        }
    }
}

// ~~ Prehandoff ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Prehandoff` (`monitor/monitor_client_api/prehandoff.ml`): what the
/// monitor sends after `HANDOFF_TO_SERVER`, before the server's `Hello`.
pub mod prehandoff {
    use serde::Deserialize;
    use serde::Serialize;

    use crate::server_command_types::ServerSpecificFiles;

    /// `Unix.process_status`
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum ProcessStatus {
        WEXITED(isize),
        WSIGNALED(isize),
        WSTOPPED(isize),
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct ExitStatus {
        pub status: ProcessStatus,
        pub was_oom: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum Msg {
        /// Last of the prehandoff messages; includes finale_file_name of server.
        Sentinel(ServerSpecificFiles),
        /// The monitor keeps a queue of connections that will need to be passed
        /// onto the next server instance. This queue has a size limit that has been
        /// reached.
        ServerDormantConnectionsLimitReached,
        /// Monitor is running but has no server - i.e. dormant. Connection has been
        /// placed on a queue to be sent to the next started server.
        ServerNotAliveDormant(String),
        /// Server process died. Connect another client to start another one.
        ServerDied(ExitStatus),
        /// Server died from a config change, and the Monitor didn't automatically
        /// start a new one because a version change in the config file.
        ServerDiedConfigChange,
    }
}

// ~~ Monitor_connection: the client's end of the handshake ~~~~~~~~~~~~~~~~~~

/// `Monitor_connection` (`monitor/monitor_client_api/monitor_connection.ml`):
/// the client's end of frames 1 to 4.
pub mod monitor_connection {
    use std::io::Read;
    use std::os::unix::net::UnixStream;

    use super::Deadline;
    use super::ReadError;
    use super::monitor_rpc;
    use super::monitor_utils::ConnectFailurePhase;
    use super::monitor_utils::ConnectFailureReason;
    use super::monitor_utils::ConnectToMonitorFailure;
    use super::monitor_utils::ConnectionError;
    use super::monitor_utils::ConnectionState;
    use super::monitor_utils::MonitorConfig;
    use super::monitor_utils::ShutdownResult;
    use super::monitor_utils::UnixError;
    use super::monitor_utils::{self};
    use super::prehandoff;
    use super::UncaughtReadError;
    use super::read_value;
    use super::write_value;
    use crate::connection_tracker;
    use crate::connection_tracker::Key;
    use crate::exception;
    use crate::hh_logger;
    use crate::lock;
    use crate::path;
    use crate::rt::ocaml_unix;
    use crate::server_command_types::ServerSpecificFiles;
    use crate::server_files;
    use crate::socket;

    fn log(s: &str, tracker: &connection_tracker::T) {
        hh_logger::log(&format!("[{}] {}", connection_tracker::log_id(tracker), s))
    }

    pub fn server_exists(lock_file: &str) -> bool {
        !lock::check(lock_file)
    }

    pub fn hh_monitor_config(root: &path::T) -> MonitorConfig {
        MonitorConfig {
            lock_file: server_files::lock_file(root),
            socket_file: server_files::socket_file(root),
            server_log_file: server_files::log_link(root),
            monitor_log_file: server_files::monitor_log_link(root),
        }
    }

    /// The server is out of date and is going to exit. Subsequent calls
    /// to connect on the Unix Domain Socket might succeed, connecting to
    /// the server that is about to die, and eventually we will be hung
    /// up on while trying to read from our end.
    ///
    /// To avoid that fate, when we know the server is about to exit, we
    /// wait for the connection to be closed, signaling that the server
    /// has exited and the OS has cleaned up after it, then we try again.
    ///
    /// See also: MonitorMain.client_out_of_date
    ///
    /// (`Err` only for a timeout of the enclosing `Timeout.with_timeout`:
    /// the socket's timeout, which the caller set.)
    pub fn wait_on_server_restart(ic: &mut UnixStream) -> Result<(), ()> {
        let mut c = [0u8; 1];
        loop {
            match ic.read(&mut c) {
                Ok(0) => return Ok(()),
                Ok(_) => {}
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                // Server has exited and hung up on us (`End_of_file`,
                // `Sys_error _`)
                Err(e) if !super::is_timeout(&e) => return Ok(()),
                Err(_) => return Err(()),
            }
        }
    }

    pub fn get_sockaddr(config: &MonitorConfig) -> String {
        socket::make_valid_socket_path(&config.socket_file)
    }

    /// What interrupts the `do_` of a `Timeout.with_timeout`.
    enum Interrupt {
        /// The deadline passed.
        Timeout,
        /// `Unix.Unix_error`
        Unix(std::io::Error, &'static str),
        /// Another exception, which nothing here catches.
        Raise(UncaughtReadError),
    }

    fn of_read_error(e: ReadError) -> Interrupt {
        match e {
            ReadError::Unix(e) if super::is_timeout(&e) => Interrupt::Timeout,
            ReadError::Unix(e) => Interrupt::Unix(e, "read"),
            e => Interrupt::Raise(super::uncaught_read_error(e)),
        }
    }

    fn of_write_error(e: std::io::Error) -> Interrupt {
        if super::is_timeout(&e) {
            Interrupt::Timeout
        } else {
            Interrupt::Unix(e, "write")
        }
    }

    /// Consume sequence of Prehandoff messages.
    fn consume_prehandoff_messages(
        ic: &mut UnixStream,
    ) -> Result<Result<ServerSpecificFiles, ConnectionError>, Interrupt> {
        let m: prehandoff::Msg = read_value(ic).map_err(of_read_error)?;
        match m {
            prehandoff::Msg::Sentinel(server_specific_files) => Ok(Ok(server_specific_files)),
            prehandoff::Msg::ServerDormantConnectionsLimitReached => {
                eprint!(
                    "Connections limit on dormant server reached. Be patient waiting for a server to be started."
                );
                Ok(Err(ConnectionError::ServerDormant))
            }
            prehandoff::Msg::ServerNotAliveDormant(_) => {
                // `Client_messages.waiting_for_server_to_be_started_doc` is
                // `""` (`stubs/client_messages.ml`).
                eprint!("Waiting for a server to be started...{}\n", "");
                consume_prehandoff_messages(ic)
            }
            prehandoff::Msg::ServerDiedConfigChange => {
                eprint!(
                    "Last server exited due to config change. Please re-run client to force discovery of the correct version of the client."
                );
                Ok(Err(ConnectionError::ServerDied))
            }
            prehandoff::Msg::ServerDied(prehandoff::ExitStatus { status, was_oom }) => {
                match (was_oom, status) {
                    (true, _) => eprint!("Last server killed by OOM Manager.\n"),
                    (false, prehandoff::ProcessStatus::WEXITED(exit_code)) => {
                        eprint!("Last server exited with code: {}.\n", exit_code)
                    }
                    (false, prehandoff::ProcessStatus::WSIGNALED(signal)) => {
                        eprint!("Last server killed by signal: {}.\n", signal)
                    }
                    (false, prehandoff::ProcessStatus::WSTOPPED(signal)) => {
                        eprint!("Last server stopped by signal: {}.\n", signal)
                    }
                }
                // Monitor will exit now that it has provided a client with a reason
                // for the last server dying. Wait for the Monitor to exit.
                wait_on_server_restart(ic).map_err(|()| Interrupt::Timeout)?;
                Ok(Err(ConnectionError::ServerDied))
            }
        }
    }

    /// The `do_` of `connect_to_monitor`'s `Timeout.with_timeout`.
    fn connect_to_monitor_do(
        phase: &mut ConnectFailurePhase,
        deadline: &Deadline,
        tracker: connection_tracker::T,
        terminate_monitor_on_version_mismatch: bool,
        is_stop: bool,
        config: &MonitorConfig,
    ) -> Result<
        Result<(UnixStream, UnixStream, connection_tracker::T), ConnectionError>,
        Interrupt,
    > {
        // 1. open the socket
        *phase = ConnectFailurePhase::ConnectOpenSocket;
        let sockaddr = get_sockaddr(config);
        let mut ic = super::open_connection(&sockaddr, deadline).map_err(|e| {
            if super::is_timeout(&e) {
                Interrupt::Timeout
            } else {
                Interrupt::Unix(e, "connect")
            }
        })?;
        deadline.apply(&ic).map_err(|_| Interrupt::Timeout)?;
        let mut oc = ic.try_clone().map_err(|e| Interrupt::Unix(e, "dup"))?;
        let tracker = connection_tracker::track(Key::ClientOpenedSocket, None, None, None, None, tracker);

        // 2. send version, followed by newline
        *phase = ConnectFailurePhase::ConnectSendVersion;
        let version_str = monitor_utils::version_payload::serialize(
            &tracker,
            terminate_monitor_on_version_mismatch,
            monitor_utils::terminate_other_implementation(
                terminate_monitor_on_version_mismatch,
                is_stop,
            ),
        );
        super::ocaml_frame::write_value(
            &mut oc,
            &crate::rt::ocaml_marshal::Value::string(version_str.as_bytes()),
        )
        .map_err(of_write_error)?;
        *phase = ConnectFailurePhase::ConnectSendNewline;
        {
            use std::io::Write;
            oc.write_all(b"\n").map_err(of_write_error)?;
        }
        let tracker = connection_tracker::track(Key::ClientSentVersion, None, None, None, None, tracker);

        // 3. wait for Connection_ok
        // timeout/exn -> Server_missing_exn/Monitor_connection_misc_exception
        *phase = ConnectFailurePhase::ConnectReceiveConnectionOk;
        let cstate: ConnectionState =
            super::ocaml_frame::read_connection_state(&mut ic).map_err(of_read_error)?;
        let tracker = connection_tracker::track(Key::ClientGotCstate, None, None, None, None, tracker);

        // 4. return Ok
        match cstate {
            ConnectionState::ConnectionOk | ConnectionState::ConnectionOkV2(_) => {
                Ok(Ok((ic, oc, tracker)))
            }
            ConnectionState::BuildIdMismatch => {
                wait_on_server_restart(&mut ic).map_err(|()| Interrupt::Timeout)?;
                Ok(Err(ConnectionError::BuildIdMismatchedMonitorWillTerminate(None)))
            }
            ConnectionState::BuildIdMismatchEx(mismatch_info) => {
                wait_on_server_restart(&mut ic).map_err(|()| Interrupt::Timeout)?;
                Ok(Err(ConnectionError::BuildIdMismatchedMonitorWillTerminate(
                    Some(mismatch_info),
                )))
            }
            ConnectionState::BuildIdMismatchV3(mismatch_info, mismatch_payload) => {
                let monitor_will_terminate =
                    match monitor_utils::mismatch_payload::deserialize(&mismatch_payload)
                        .map_err(Interrupt::Raise)?
                    {
                        Err(msg) => {
                            hh_logger::log(&format!(
                                "Unparseable response from monitor - {}\n{}",
                                msg, mismatch_payload
                            ));
                            true
                        }
                        Ok(monitor_utils::mismatch_payload::T {
                            monitor_will_terminate,
                        }) => monitor_will_terminate,
                    };
                if monitor_will_terminate {
                    wait_on_server_restart(&mut ic).map_err(|()| Interrupt::Timeout)?;
                    Ok(Err(ConnectionError::BuildIdMismatchedMonitorWillTerminate(
                        Some(mismatch_info),
                    )))
                } else {
                    Ok(Err(ConnectionError::BuildIdMismatchedClientMustTerminate(
                        mismatch_info,
                    )))
                }
            }
        }
    }

    /// (`log_on_slow_connect` defaults to `false`, and nothing passes it:
    /// see the module documentation of `rt::protocol`.) On success the
    /// socket's timeouts are those of `timeout`; the caller changes them.
    ///
    /// The exceptions that OCaml does not catch here (a read error other
    /// than a `Unix_error`, such as `End_of_file` when the other end closes
    /// before it answers) are the outer `Err` (`UncaughtReadError`).
    pub fn connect_to_monitor(
        tracker: connection_tracker::T,
        timeout: isize,
        terminate_monitor_on_version_mismatch: bool,
        config: &MonitorConfig,
    ) -> Result<
        Result<(UnixStream, UnixStream, connection_tracker::T), ConnectionError>,
        UncaughtReadError,
    > {
        connect_to_monitor_(tracker, timeout, terminate_monitor_on_version_mismatch, false, config)
    }

    /// [`connect_to_monitor`]; `is_stop` for `connect_and_shut_down`, which
    /// asks a monitor of the other implementation to terminate too
    /// (`monitor_utils::terminate_other_implementation`).
    fn connect_to_monitor_(
        tracker: connection_tracker::T,
        timeout: isize,
        terminate_monitor_on_version_mismatch: bool,
        is_stop: bool,
        config: &MonitorConfig,
    ) -> Result<
        Result<(UnixStream, UnixStream, connection_tracker::T), ConnectionError>,
        UncaughtReadError,
    > {
        // There are some pathological scenarios concerned with high volumes of requests.
        // (See `monitor_connection.ml`.)
        let mut phase = ConnectFailurePhase::ConnectOpenSocket;
        let deadline = Deadline::in_seconds(timeout as f64);
        // Note: Timeout.with_timeout is accomplished internally by an exception;
        // hence, our "try/with exn ->" catch-all must be outside with_timeout.
        // (`finally`: the socket closes when it is dropped.)
        Ok(match connect_to_monitor_do(
            &mut phase,
            &deadline,
            tracker,
            terminate_monitor_on_version_mismatch,
            is_stop,
            config,
        ) {
            Ok(res) => res,
            Err(Interrupt::Timeout) => Err(ConnectionError::ConnectToMonitorFailure(
                ConnectToMonitorFailure {
                    server_exists: server_exists(&config.lock_file),
                    failure_phase: phase,
                    failure_reason: ConnectFailureReason::ConnectTimeout,
                },
            )),
            Err(Interrupt::Unix(e, fun_name)) => {
                let e = exception::wrap(UnixError(e, fun_name));
                Err(ConnectionError::ConnectToMonitorFailure(
                    ConnectToMonitorFailure {
                        server_exists: server_exists(&config.lock_file),
                        failure_phase: phase,
                        failure_reason: ConnectFailureReason::ConnectException(e),
                    },
                ))
            }
            Err(Interrupt::Raise(e)) => {
                return Err(e);
            }
        })
    }

    /// The outer `Err` is an exception that OCaml raises out of
    /// `connect_and_shut_down` (an uncaught read error of
    /// `connect_to_monitor`, or a failed write of `SHUT_DOWN`): its only
    /// caller, `Client_stop.nice_kill`, catches every exception.
    pub fn connect_and_shut_down(
        tracker: connection_tracker::T,
        root: &path::T,
    ) -> Result<Result<ShutdownResult, ConnectionError>, UncaughtReadError> {
        let config = hh_monitor_config(root);
        let (mut ic, mut oc, tracker) = match connect_to_monitor_(tracker, 3, true, true, &config)? {
            Ok(conn) => conn,
            Err(e) => return Ok(Err(e)),
        };
        log("send_shutdown", &tracker);
        if let Err(e) = write_value(&mut oc, &monitor_rpc::Command::SHUT_DOWN(tracker)) {
            return Err(UncaughtReadError(ocaml_unix::unix_error_to_string(
                &e, "write", "",
            )));
        }
        let on_timeout = || {
            if server_exists(&config.lock_file) {
                Ok(ShutdownResult::SHUTDOWN_UNVERIFIED)
            } else {
                Err(ConnectionError::ConnectToMonitorFailure(
                    ConnectToMonitorFailure {
                        server_exists: false,
                        failure_phase: ConnectFailurePhase::ConnectSendShutdown,
                        failure_reason: ConnectFailureReason::ConnectTimeout,
                    },
                ))
            }
        };
        // `Timeout.with_timeout ~timeout:3`
        let deadline = Deadline::in_seconds(3.);
        if deadline.apply(&ic).is_err() {
            return Ok(on_timeout());
        }
        Ok(match wait_on_server_restart(&mut ic) {
            Ok(()) => Ok(ShutdownResult::SHUTDOWN_VERIFIED),
            Err(()) => on_timeout(),
        })
    }

    /// The exceptions that OCaml does not catch here are the outer `Err`
    /// (`UncaughtReadError`): they skip the logging, as in OCaml.
    pub fn connect_once(
        tracker: connection_tracker::T,
        timeout: isize,
        terminate_monitor_on_version_mismatch: bool,
        root: &path::T,
        handoff_options: monitor_rpc::HandoffOptions,
    ) -> Result<
        Result<(UnixStream, UnixStream, ServerSpecificFiles), ConnectionError>,
        UncaughtReadError,
    > {
        let config = hh_monitor_config(root);
        let t_start = ocaml_unix::gettimeofday();
        let log_tracker = tracker.clone();
        let result = (|| {
            let tracker = connection_tracker::track(
                Key::ClientStartConnect,
                Some(t_start),
                None,
                None,
                None,
                tracker,
            );
            let (mut ic, mut oc, tracker) = match connect_to_monitor(
                tracker,
                timeout,
                terminate_monitor_on_version_mismatch,
                &config,
            )? {
                Ok(conn) => conn,
                Err(e) => return Ok(Err(e)),
            };
            let tracker =
                connection_tracker::track(Key::ClientReadyToSendHandoff, None, None, None, None, tracker);
            if let Err(e) = write_value(
                &mut oc,
                &monitor_rpc::Command::HANDOFF_TO_SERVER(tracker, handoff_options),
            ) {
                return Err(super::uncaught_write_error(e));
            }
            let elapsed_t = (ocaml_unix::gettimeofday() - t_start) as isize;
            let timeout = std::cmp::max(timeout - elapsed_t, 1);
            let deadline = Deadline::in_seconds(timeout as f64);
            let res = match deadline.apply(&ic) {
                Err(_) => Err(Interrupt::Timeout),
                Ok(()) => consume_prehandoff_messages(&mut ic),
            };
            Ok(match res {
                Ok(Ok(server_specific_files)) => {
                    super::clear_timeouts(&ic);
                    Ok((ic, oc, server_specific_files))
                }
                Ok(Err(e)) => Err(e),
                Err(Interrupt::Timeout) => Err(ConnectionError::ServerDormantOutOfRetries),
                // `Timeout.with_timeout` catches nothing else.
                Err(Interrupt::Unix(e, fun_name)) => {
                    return Err(super::UncaughtReadError(ocaml_unix::unix_error_to_string(
                        &e, fun_name, "",
                    )));
                }
                Err(Interrupt::Raise(e)) => return Err(e),
            })
        })()?;
        // oops too heavy
        match &result {
            Ok(_) => {
                log("CLIENT_CONNECT_ONCE", &log_tracker);
                // `Hack_event_logger.client_connect_once ~t_start`: a no-op
                // in the OSS build.
            }
            Err(e) => {
                let (reason, _telemetry) = monitor_utils::connection_error_to_telemetry(e);
                log(&format!("CLIENT_CONNECT_ONCE {}", reason), &log_tracker);
                // `Hack_event_logger.client_connect_once_failure ~t_start
                // reason telemetry`: a no-op in the OSS build.
            }
        }
        Ok(result)
    }
}

// ~~ The server's end ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The server's end of the protocol (`ServerClientProvider`'s
/// `say_hello`, `read_connection_type`, `read_client_msg`,
/// `send_response_to_client`, `ping`), on a client connection that the
/// monitor (`crate::monitor_main`) handed off. For the client's tests only
/// (`#[cfg(test)]`): a monitor and a server in one (`bind`,
/// [`ack_and_handoff_client`]), the monitor's half of the handshake as
/// `Monitor_main.ack_and_handoff_client` does it.
pub mod server_end {
    #[cfg(test)]
    use std::os::unix::net::UnixListener;
    use std::os::unix::net::UnixStream;

    use super::Deadline;
    use super::ReadError;
    use super::monitor_rpc;
    use super::monitor_utils;
    #[cfg(test)]
    use super::monitor_utils::ConnectionState;
    #[cfg(test)]
    use super::prehandoff;
    use super::read_value;
    use super::write_value;
    #[cfg(test)]
    use crate::build_id;
    use crate::connection_tracker;
    use crate::connection_tracker::Key;
    #[cfg(test)]
    use crate::hh_logger;
    #[cfg(test)]
    use crate::path;
    use crate::server_command_types::Command;
    use crate::server_command_types::CommandResult;
    use crate::server_command_types::ConnectionType;
    use crate::server_command_types::MessageType;
    #[cfg(test)]
    use crate::server_command_types::ServerSpecificFiles;
    #[cfg(test)]
    use crate::server_files;
    #[cfg(test)]
    use crate::socket;
    #[cfg(test)]
    use crate::utils;

    #[cfg(test)]
    /// The listening socket of a root (`Socket.init_unix_socket
    /// (Server_files.socket_file root)`). Binding it also fixes the launch
    /// time that a version mismatch reports
    /// (`Monitor_utils.current_build_info`).
    pub fn bind(root: &path::T) -> UnixListener {
        let _ = monitor_utils::current_build_info();
        let listener = socket::init_unix_socket(&server_files::socket_file(root));
        // `last_request_handoff = ref (Unix.time ())` when the server starts
        // (`Server_controller.start_server`).
        set_last_request_handoff();
        listener
    }

    #[cfg(test)]
    /// `server.last_request_handoff` (`Server_process.server_process`): the
    /// time (`Unix.time`) of the last handoff, which the monitor logs.
    static LAST_REQUEST_HANDOFF: std::sync::Mutex<Option<f64>> = std::sync::Mutex::new(None);

    #[cfg(test)]
    /// `server.last_request_handoff := Unix.time ()`
    fn set_last_request_handoff() {
        *LAST_REQUEST_HANDOFF
            .lock()
            .unwrap_or_else(|e| e.into_inner()) =
            Some(crate::rt::ocaml_unix::gettimeofday().floor());
    }

    #[cfg(test)]
    fn last_request_handoff() -> f64 {
        let last = *LAST_REQUEST_HANDOFF.lock().unwrap_or_else(|e| e.into_inner());
        match last {
            Some(t) => t,
            // A server that did not [`bind`] (the tests): as if it had just
            // started.
            None => {
                set_last_request_handoff();
                last_request_handoff()
            }
        }
    }

    /// `ServerClientProvider.Client_went_away`
    #[derive(Debug)]
    pub struct Client_went_away;

    /// `Server_command_types.Read_command_timeout` or `Client_went_away`.
    #[derive(Debug)]
    pub enum ReadClientError {
        ReadCommandTimeout,
        ClientWentAway,
        /// Any other exception (the OCaml does not catch it).
        Other(ReadError),
    }

    /// A client whose handshake is done: the server talks to it (`client`
    /// of `ServerClientProvider`).
    pub struct Client {
        pub ic: UnixStream,
        pub oc: UnixStream,
        pub tracker: connection_tracker::T,
        pub handoff_options: monitor_rpc::HandoffOptions,
    }

    #[cfg(test)]
    /// What the handshake of a connection came to.
    pub enum Handshake {
        /// `HANDOFF_TO_SERVER`: the `Sentinel` is sent; the server goes on
        /// with [`read_connection_type`].
        Handoff(Client),
        /// `SHUT_DOWN`: the server shuts down and exits with `No_error`
        /// (`kill_server_with_check_and_wait`, `Exit.exit No_error`); the
        /// client sees the connection close when it exits.
        ShutDown(connection_tracker::T, UnixStream),
        /// The client is another version, and was told
        /// `Build_id_mismatch_v3`. If `monitor_will_terminate`, the server
        /// exits with `Build_id_mismatch` (keeping the connection until it
        /// does, so that the client sees it close then); otherwise the
        /// connection was closed.
        VersionMismatch {
            monitor_will_terminate: bool,
            conn: Option<UnixStream>,
        },
    }

    #[cfg(test)]
    /// `read_version_string_then_newline` (there is no newline here). An
    /// OCaml string is any bytes: one that is not UTF-8 is read lossily (it
    /// is then a version that matches no build). The error is the exception
    /// that `Marshal_tools.from_fd_with_preamble` raises, which OCaml does
    /// not turn into `"Malformed Build ID"`: the monitor's handler logs it
    /// and closes the connection.
    fn read_version_string(fd: &mut UnixStream) -> Result<String, ReadError> {
        match super::ocaml_frame::read_version(fd)? {
            Ok(s) => Ok(s),
            Err(msg) => Err(ReadError::Malformed(msg)),
        }
    }

    #[cfg(test)]
    /// `Monitor_main.ack_and_handoff_client` for a server that is alive
    /// (frames 1 to 4), with the monitor's `ignore_hh_version`. `Err` is
    /// `"Malformed Build ID"` (a version payload that does not parse), or
    /// the exception of reading the version or the command (OCaml's
    /// `Printexc.to_string` of it), or of writing: the connection is dropped
    /// (the monitor logs `Ack_and_handoff failure; closing client FD: %s`).
    pub fn ack_and_handoff_client(
        client_fd: UnixStream,
        ignore_hh_version: bool,
        server_specific_files: &ServerSpecificFiles,
    ) -> Result<Handshake, String> {
        ack_and_handoff_client_as(
            client_fd,
            &build_id::build_revision(),
            ignore_hh_version,
            server_specific_files,
        )
    }

    #[cfg(test)]
    /// [`ack_and_handoff_client`] for a server whose version
    /// (`Build_id.build_revision`) is `monitor_version`: what the tests use
    /// to be another version than their client.
    pub fn ack_and_handoff_client_as(
        mut client_fd: UnixStream,
        monitor_version: &str,
        ignore_hh_version: bool,
        server_specific_files: &ServerSpecificFiles,
    ) -> Result<Handshake, String> {
        // OCaml's monitor reads the version and the monitor command with no
        // timeout. Here a connection that sends nothing for 30 seconds is
        // dropped (as a malformed one), so that it cannot hold its task.
        let _ = Deadline::in_seconds(30.).apply(&client_fd);
        let start_time = crate::rt::ocaml_unix::gettimeofday();
        let payload = match read_version_string(&mut client_fd) {
            Err(e) => return Err(super::read_error_to_string(&e, "read")),
            Ok(s) => match monitor_utils::version_payload::deserialize(&s) {
                Ok(payload) => payload,
                Err(monitor_utils::version_payload::DeserializeError::Error(_err)) => {
                    return Err("Malformed Build ID".to_string());
                }
                // `Yojson.Safe.Util.Type_error`, raised (not an `Error`).
                Err(monitor_utils::version_payload::DeserializeError::Type_error(exn)) => {
                    return Err(exn);
                }
            },
        };
        let monitor_will_terminate = monitor_utils::monitor_will_terminate(&payload);
        let monitor_utils::version_payload::T {
            client_version,
            tracker_id,
            terminate_monitor_on_version_mismatch,
            ..
        } = payload;
        hh_logger::log(&format!(
            "[{}] read_version: start_wait={}, client_version={}, monitor_version={}, monitor_ignore_hh_version={}, terminate_monitor_on_version_mismatch={}",
            tracker_id,
            utils::timestring(start_time),
            client_version,
            monitor_version,
            ignore_hh_version,
            terminate_monitor_on_version_mismatch
        ));
        // Version is okay if *monitor* was started with --ignore-hh-version, or versions match.
        let is_version_ok = ignore_hh_version || client_version == monitor_version;
        if is_version_ok {
            let connection_state = ConnectionState::ConnectionOk;
            hh_logger::log(&format!(
                "[{}] sending {}",
                tracker_id,
                monitor_utils::show_connection_state(&connection_state)
            ));
            super::ocaml_frame::write_connection_state(&mut client_fd, &connection_state)
                .map_err(|e| e.to_string())?;
            // following function returns [env msg_update] monad
            handle_monitor_rpc(client_fd, server_specific_files)
        } else {
            let _ = terminate_monitor_on_version_mismatch;
            let connection_state = ConnectionState::BuildIdMismatchV3(
                monitor_utils::BuildMismatchInfo {
                    existing_version: monitor_version.to_string(),
                    ..monitor_utils::current_build_info()
                },
                monitor_utils::mismatch_payload::serialize(monitor_will_terminate),
            );
            hh_logger::log(&format!(
                "[{}] sending {}",
                tracker_id,
                monitor_utils::show_connection_state(&connection_state)
            ));
            if let Err(exn) =
                super::ocaml_frame::write_connection_state(&mut client_fd, &connection_state)
            {
                hh_logger::log(&format!("while sending, exn: {}", exn));
            }
            if monitor_will_terminate {
                Ok(Handshake::VersionMismatch {
                    monitor_will_terminate,
                    conn: Some(client_fd),
                })
            } else {
                hh_logger::log("Closing client_fd");
                drop(client_fd);
                Ok(Handshake::VersionMismatch {
                    monitor_will_terminate,
                    conn: None,
                })
            }
        }
    }

    #[cfg(test)]
    /// `handle_monitor_rpc`, and `client_prehandoff` for a server that is
    /// alive: the `Sentinel`.
    fn handle_monitor_rpc(
        mut client_fd: UnixStream,
        server_specific_files: &ServerSpecificFiles,
    ) -> Result<Handshake, String> {
        let cmd: monitor_rpc::Command =
            read_value(&mut client_fd).map_err(|e| super::read_error_to_string(&e, "read"))?;
        match cmd {
            monitor_rpc::Command::HANDOFF_TO_SERVER(tracker, handoff_options) => {
                let tracker =
                    connection_tracker::track(Key::MonitorReceivedHandoff, None, None, None, None, tracker);
                let t_ready = crate::rt::ocaml_unix::gettimeofday();
                let tracker =
                    connection_tracker::track(Key::MonitorReady, Some(t_ready), None, None, None, tracker);
                // TODO: Send this to client so it is visible.
                hh_logger::log(&format!(
                    "[{}] Got {} request for typechecker. Prior request {:.1} seconds ago",
                    connection_tracker::log_id(&tracker),
                    monitor_rpc::pipe_type_to_string(handoff_options.pipe_type),
                    t_ready - last_request_handoff()
                ));
                write_value(
                    &mut client_fd,
                    &prehandoff::Msg::Sentinel(server_specific_files.clone()),
                )
                .map_err(|e| e.to_string())?;
                let tracker =
                    connection_tracker::track(Key::MonitorSentAckToClient, None, None, None, None, tracker);
                // (`hand_off_client_connection_wrapper`: the connection is
                // the server's from here.)
                set_last_request_handoff();
                super::clear_timeouts(&client_fd);
                let oc = client_fd.try_clone().map_err(|e| e.to_string())?;
                Ok(Handshake::Handoff(Client {
                    ic: client_fd,
                    oc,
                    tracker,
                    handoff_options,
                }))
            }
            monitor_rpc::Command::SHUT_DOWN(tracker) => {
                hh_logger::log(&format!(
                    "[{}] Got shutdown RPC. Shutting down.",
                    connection_tracker::log_id(&tracker)
                ));
                Ok(Handshake::ShutDown(tracker, client_fd))
            }
        }
    }

    pub fn say_hello(oc: &mut UnixStream) -> Result<(), std::io::Error> {
        write_value(oc, &MessageType::<CommandResult>::Hello)
    }

    /// `read_connection_type_from_channel`: sent by
    /// [ClientConnection.connect], within a second.
    fn read_connection_type_from_channel(
        ic: &mut UnixStream,
    ) -> Result<ConnectionType, ReadClientError> {
        let deadline = Deadline::in_seconds(1.);
        if deadline.apply(ic).is_err() {
            return Err(ReadClientError::ReadCommandTimeout);
        }
        let res = read_value(ic);
        super::clear_timeouts(ic);
        match res {
            Ok(connection_type) => Ok(connection_type),
            Err(e) if e.is_timeout() => Err(ReadClientError::ReadCommandTimeout),
            Err(e) => Err(ReadClientError::Other(e)),
        }
    }

    /// Says hello, then reads the connection type. A broken pipe while
    /// saying hello (`Unix_error (EPIPE, "write", _)`) or a reset connection
    /// while reading (`Sys_error "Connection reset by peer"`, from
    /// `input_value`) is `Client_went_away`; anything else is not caught.
    pub fn read_connection_type(client: &mut Client) -> Result<ConnectionType, ReadClientError> {
        if let Err(e) = say_hello(&mut client.oc) {
            return match e.raw_os_error() {
                Some(libc::EPIPE) => Err(ReadClientError::ClientWentAway),
                _ => Err(ReadClientError::Other(ReadError::Unix(e))),
            };
        }
        client.tracker = connection_tracker::track(
            Key::ServerSentHello,
            None,
            None,
            None,
            None,
            client.tracker.clone(),
        );
        let connection_type = match read_connection_type_from_channel(&mut client.ic) {
            Err(ReadClientError::Other(ReadError::Unix(e)))
                if e.raw_os_error() == Some(libc::ECONNRESET) =>
            {
                return Err(ReadClientError::ClientWentAway);
            }
            res => res?,
        };
        client.tracker = connection_tracker::track(
            Key::ServerGotConnectionType,
            None,
            None,
            None,
            None,
            client.tracker.clone(),
        );
        Ok(connection_type)
    }

    pub fn send_response_to_client(
        client: &mut Client,
        response: CommandResult,
    ) -> Result<(), std::io::Error> {
        write_value(
            &mut client.oc,
            &MessageType::Response(response, client.tracker.clone()),
        )
    }

    /// `read_client_msg`: the command, within a second. The end of the
    /// stream is `Client_went_away`.
    pub fn read_client_msg(client: &mut Client) -> Result<Command, ReadClientError> {
        let deadline = Deadline::in_seconds(1.);
        if deadline.apply(&client.ic).is_err() {
            return Err(ReadClientError::ReadCommandTimeout);
        }
        let res = read_value(&mut client.ic);
        super::clear_timeouts(&client.ic);
        match res {
            Ok(cmd) => Ok(cmd),
            Err(ReadError::EndOfFile) => Err(ReadClientError::ClientWentAway),
            Err(e) if e.is_timeout() => Err(ReadClientError::ReadCommandTimeout),
            Err(e) => Err(ReadClientError::Other(e)),
        }
    }

    pub fn ping(client: &mut Client) -> Result<(), Client_went_away> {
        write_value(&mut client.oc, &MessageType::<CommandResult>::Ping).map_err(|_| Client_went_away)
    }

    /// Tells the client waiting in `Client_start.start_server` (through the
    /// `--waiting-client` descriptor) that the server is ready:
    /// `Monitor_utils.ready` and a newline.
    pub fn send_ready_to_waiting_client(fd: std::os::fd::RawFd) -> std::io::Result<()> {
        use std::io::Write;
        use std::os::fd::FromRawFd;
        // SAFETY: the descriptor was given on the command line by the
        // client; it is used once and closed.
        let mut f = unsafe { std::fs::File::from_raw_fd(fd) };
        f.write_all(format!("{}\n", monitor_utils::ready).as_bytes())?;
        f.flush()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frames() {
        let mut buf = vec![];
        write_frame(&mut buf, b"hello").unwrap();
        assert_eq!(&buf[..4], &5u32.to_le_bytes());
        let mut r = &buf[..];
        assert_eq!(read_frame(&mut r).unwrap(), b"hello");
        assert!(matches!(read_frame(&mut r), Err(ReadError::EndOfFile)));
        let mut r = &buf[..2];
        assert!(matches!(read_frame(&mut r), Err(ReadError::ReadingPreamble)));
        let mut r = &buf[..6];
        assert!(matches!(read_frame(&mut r), Err(ReadError::ReadingPayload)));
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
            Err(DeserializeError::Type_error(
                r#"Yojson.Safe.Util.Type_error("Expected string or null, got int", _)"#.to_string()
            ))
        );
        assert_eq!(
            deserialize(r#"{"client_version":"v","terminate_monitor_on_version_mismatch":"no"}"#),
            Err(DeserializeError::Type_error(
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
            CommandResult::STATUS(status.clone()),
            crate::connection_tracker::create(),
        );
        let back: MessageType<CommandResult> = wire::decode(&wire::encode(&r)).unwrap();
        match back {
            MessageType::Response(CommandResult::STATUS(s), _) => assert_eq!(s, status),
            _ => panic!("expected STATUS"),
        }
        let cmd: Command = (
            CmdMetadata {
                from: "f".into(),
                desc: "d".into(),
            },
            T::IDEFINDREFSBYSYMBOL(crate::find_refs_wire_format::cli_args::T {
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
            (meta, T::IDEFINDREFSBYSYMBOL(args)) => {
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
        let r = CommandResult::PACKAGELINT(set.clone());
        match wire::decode::<CommandResult>(&wire::encode(&r)).unwrap() {
            CommandResult::PACKAGELINT(s) => assert_eq!(s, set),
            _ => panic!("expected PACKAGE_LINT"),
        }
        let r = CommandResult::STATUSSINGLE(((vec![], 0), None));
        match wire::decode::<CommandResult>(&wire::encode(&r)).unwrap() {
            CommandResult::STATUSSINGLE(((errors, 0), None)) => assert!(errors.is_empty()),
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
