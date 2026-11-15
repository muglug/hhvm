// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/buffered_line_reader/buffered_line_reader.ml` (`Functor`
//! applied to the `Regular_reader` instance). See `hh/PORTING.md`.
//!
//! This module is needed because Unix.select doesn't play well with
//! input_line on Ocaml channels.. i.e., when a buffered read into an
//! Ocaml channel consumes two complete lines from the file descriptor, the next
//! select will say there is nothing to read when in fact there is
//! something in the channel. This wouldn't be a problem if Ocaml channel's API
//! supported a "has buffered content" call, so you could check if the
//! buffer contains something as well as doing a Unix select to know for real if
//! there is content coming.
//!
//! Only what `Http_lite` reads LSP messages with: `create`, `get_next_line`,
//! `get_next_bytes`, `has_buffered_content`, `get_fd`. The file descriptor is
//! any [`std::io::Read`]. Not here: `is_readable` (a `select` on the file
//! descriptor) and `get_null_reader`.
//!
//! The exceptions (`End_of_file`, `Unix.Unix_error`, the `Assert_failure` of
//! `get_next_bytes`) are caught by the callers that read LSP messages: they
//! are the [`Error`] of a `Result`. A read interrupted by a signal is
//! restarted (the OCaml reads in a process of its own, which no signal
//! reaches; here any thread can take one).

use std::io::Read;

/// Our Unix systems only allow reading 64KB chunks at a time.
/// Trying to read more than 64KB results in only 64KB being read.
const CHUNK_SIZE: usize = 65536;

/// `chunk_size`
pub fn chunk_size() -> usize {
    CHUNK_SIZE
}

/// The exceptions of the readers. `Debug` gives what `Printexc.to_string`
/// gives in OCaml.
pub enum Error {
    /// `End_of_file`
    EndOfFile,
    /// `Unix.Unix_error`, raised by `Unix.read`.
    UnixError(std::io::Error),
    /// The `assert (size > 0)` of `get_next_bytes`.
    AssertFailure,
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::EndOfFile => f.write_str("End_of_file"),
            // The printer that `Unix` registers.
            Error::UnixError(e) => {
                f.write_str(&crate::rt::ocaml_unix::unix_error_to_string(e, "read", ""))
            }
            Error::AssertFailure => f.write_str(
                "File \"hack/src/utils/buffered_line_reader/buffered_line_reader.ml\", line 137, characters 4-10: Assertion failed",
            ),
        }
    }
}

pub struct T<R> {
    fd: R,
    /// The bytes left after the last content that haven't been consumed yet.
    unconsumed_buffer: Option<Vec<u8>>,
}

fn set_buffer<R>(r: &mut T<R>, b: Option<Vec<u8>>) {
    r.unconsumed_buffer = b
}

fn trim_trailing_cr(s: Vec<u8>) -> Vec<u8> {
    let mut s = s;
    if s.last() == Some(&b'\r') {
        s.pop();
    }
    s
}

fn merge_chunks(last_chunk: Vec<u8>, chunks_rev: Vec<Vec<u8>>) -> Vec<u8> {
    let mut chunks_rev = chunks_rev;
    chunks_rev.insert(0, last_chunk);
    let mut res = vec![];
    for chunk in chunks_rev.into_iter().rev() {
        res.extend(chunk)
    }
    res
}

/// `Unix.read fd buffer 0 size`
fn read<R: Read>(fd: &mut R, buffer: &mut [u8]) -> Result<usize, Error> {
    loop {
        match fd.read(buffer) {
            Ok(n) => return Ok(n),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(Error::UnixError(e)),
        }
    }
}

/// This function reads a line, delimited by LF (unix) or CRLF (internet)...
/// Recursively read a chunk from the file descriptor until we see a newline
/// character, building up the chunks accumulator along the way.
/// Any remaining bytes not consumed (bytes past the newline) are placed in the
/// reader's unconsumed_buffer which will be consumed on the next
/// call to get_next_line or get_next_bytes.
///
/// (`chunks` is in reverse order, as in OCaml.)
fn read_line<R: Read>(chunks: Vec<Vec<u8>>, r: &mut T<R>) -> Result<Vec<u8>, Error> {
    let mut chunks = chunks;
    loop {
        let mut b = vec![0; CHUNK_SIZE];
        let bytes_read = read(&mut r.fd, &mut b)?;
        if bytes_read == 0 {
            return Err(Error::EndOfFile);
        }
        b.truncate(bytes_read);
        match b.iter().position(|c| *c == b'\n') {
            None => chunks.insert(0, b),
            Some(i) => {
                let tail = b[0..i].to_vec();
                let result = merge_chunks(tail, chunks);
                if i + 1 < bytes_read {
                    // We read some bytes beyond the first newline character.
                    // We skip the newline character.
                    let remainder = b[i + 1..].to_vec();
                    set_buffer(r, Some(remainder))
                } else {
                    // We didn't read any bytes beyond the first newline character.
                    set_buffer(r, None)
                }
                return Ok(trim_trailing_cr(result));
            }
        }
    }
}

pub fn get_next_line<R: Read>(r: &mut T<R>) -> Result<Vec<u8>, Error> {
    match r.unconsumed_buffer.take() {
        None => read_line(vec![], r),
        Some(remainder) => match remainder.iter().position(|c| *c == b'\n') {
            None => {
                set_buffer(r, None);
                read_line(vec![remainder], r)
            }
            Some(i) => {
                let result = remainder[0..i].to_vec();
                if i + 1 < remainder.len() {
                    // There are some bytes left beyond the first newline character.
                    let remainder = remainder[i + 1..].to_vec();
                    set_buffer(r, Some(remainder))
                } else {
                    // No bytes beyond the first newline character.
                    set_buffer(r, None)
                }
                Ok(trim_trailing_cr(result))
            }
        },
    }
}

fn read_bytes<R: Read>(r: &mut T<R>, size: usize, chunks: Vec<Vec<u8>>) -> Result<Vec<u8>, Error> {
    let mut size = size;
    let mut chunks = chunks;
    loop {
        let bytes_desired = std::cmp::min(CHUNK_SIZE, size);
        let mut b = vec![0; bytes_desired];
        let bytes_read = read(&mut r.fd, &mut b)?;
        if bytes_read == 0 {
            return Err(Error::EndOfFile);
        }
        if bytes_read < size {
            b.truncate(bytes_read);
            size -= bytes_read;
            chunks.insert(0, b);
        } else {
            set_buffer(r, None);
            return Ok(merge_chunks(b, chunks));
        }
    }
}

/// The next `size` bytes (`size` must be positive).
pub fn get_next_bytes<R: Read>(r: &mut T<R>, size: isize) -> Result<Vec<u8>, Error> {
    if size <= 0 {
        return Err(Error::AssertFailure);
    }
    let size = size as usize;
    match r.unconsumed_buffer.take() {
        None => read_bytes(r, size, vec![]),
        Some(remainder) => {
            let remainder_length = remainder.len();
            if remainder_length < size {
                set_buffer(r, None);
                read_bytes(r, size - remainder_length, vec![remainder])
            } else if remainder_length == size {
                set_buffer(r, None);
                Ok(remainder)
            } else {
                let extra = remainder[size..].to_vec();
                set_buffer(r, Some(extra));
                Ok(remainder[0..size].to_vec())
            }
        }
    }
}

pub fn has_buffered_content<R>(r: &T<R>) -> bool {
    r.unconsumed_buffer.is_some()
}

pub fn create<R>(fd: R) -> T<R> {
    T {
        fd,
        unconsumed_buffer: None,
    }
}

pub fn get_fd<R>(r: &T<R>) -> &R {
    &r.fd
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A reader that gives its input in the given pieces, one per read.
    struct Pieces(Vec<Vec<u8>>);

    impl Read for Pieces {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.0.is_empty() {
                return Ok(0);
            }
            let piece = &mut self.0[0];
            let n = std::cmp::min(buf.len(), piece.len());
            buf[..n].copy_from_slice(&piece[..n]);
            piece.drain(..n);
            if piece.is_empty() {
                self.0.remove(0);
            }
            Ok(n)
        }
    }

    fn pieces(p: &[&str]) -> T<Pieces> {
        create(Pieces(p.iter().map(|s| s.as_bytes().to_vec()).collect()))
    }

    #[test]
    fn lines_and_bytes() {
        let mut r = pieces(&["ab", "c\r\nde\nfgh", "ij\n", "klm"]);
        assert_eq!(get_next_line(&mut r).unwrap(), b"abc");
        assert!(has_buffered_content(&r));
        assert_eq!(get_next_line(&mut r).unwrap(), b"de");
        assert_eq!(get_next_bytes(&mut r, 2).unwrap(), b"fg");
        assert_eq!(get_next_bytes(&mut r, 4).unwrap(), b"hij\n");
        assert!(!has_buffered_content(&r));
        assert_eq!(get_next_bytes(&mut r, 2).unwrap(), b"kl");
        assert!(matches!(get_next_bytes(&mut r, 0), Err(Error::AssertFailure)));
        assert!(matches!(get_next_line(&mut r), Err(Error::EndOfFile)));
        assert_eq!(format!("{:?}", Error::EndOfFile), "End_of_file");
    }

    #[test]
    fn exact_remainder() {
        let mut r = pieces(&["x\nyz"]);
        assert_eq!(get_next_line(&mut r).unwrap(), b"x");
        assert_eq!(get_next_bytes(&mut r, 2).unwrap(), b"yz");
        assert!(!has_buffered_content(&r));
        let mut r = pieces(&["x\n", "\n"]);
        assert_eq!(get_next_line(&mut r).unwrap(), b"x");
        assert_eq!(get_next_line(&mut r).unwrap(), b"");
        assert!(matches!(get_next_bytes(&mut r, 1), Err(Error::EndOfFile)));
    }
}
