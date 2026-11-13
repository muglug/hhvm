// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the fd passing of `Libancillary` (`libancillary/libancillary.ml`
//! over `third-party/libancillary/fd_send.c`, `fd_recv.c`) as
//! `Monitor_main` and `Server_client_provider` use it; no OCaml file of its
//! own.
//!
//! Owned by **MON** (plan §3.1).
//!
//! As libancillary, one descriptor is sent with one byte of data (`'!'`)
//! and an `SCM_RIGHTS` control message over a Unix-domain socket.

use std::os::fd::RawFd;

/// `Libancillary.Receiving_Fd_Exception`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReceivingFdException(pub String);

const CMSG_SPACE_ONE_FD: usize = 64;

fn errno() -> i32 {
    std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
}

/// `ancil_send_fd ~to_:dest_fd fd`: 0 on success, -1 on failure (with
/// `errno` set, as the C function).
pub fn ancil_send_fd(to: RawFd, fd: RawFd) -> i32 {
    // SAFETY: plain `sendmsg` with a buffer large enough for one fd's
    // control message (`CMSG_SPACE(sizeof(int))` is at most 24 bytes).
    unsafe {
        let mut nothing: u8 = b'!';
        let mut iov = libc::iovec {
            iov_base: &mut nothing as *mut u8 as *mut libc::c_void,
            iov_len: 1,
        };
        let mut buf = [0u64; CMSG_SPACE_ONE_FD / 8];
        let space = libc::CMSG_SPACE(std::mem::size_of::<libc::c_int>() as u32) as usize;
        let mut msghdr: libc::msghdr = std::mem::zeroed();
        msghdr.msg_iov = &mut iov;
        msghdr.msg_iovlen = 1;
        msghdr.msg_control = buf.as_mut_ptr() as *mut libc::c_void;
        msghdr.msg_controllen = space as _;
        let cmsg = libc::CMSG_FIRSTHDR(&msghdr);
        (*cmsg).cmsg_level = libc::SOL_SOCKET;
        (*cmsg).cmsg_type = libc::SCM_RIGHTS;
        (*cmsg).cmsg_len = libc::CMSG_LEN(std::mem::size_of::<libc::c_int>() as u32) as _;
        std::ptr::write_unaligned(libc::CMSG_DATA(cmsg) as *mut libc::c_int, fd);
        loop {
            let ret = libc::sendmsg(to, &msghdr, 0);
            if ret < 0 && errno() == libc::EINTR {
                continue;
            }
            return if ret < 0 { -1 } else { 0 };
        }
    }
}

/// `ancil_recv_fd socket_fd`: the descriptor received, or
/// `Receiving_Fd_Exception "(errno=%d) %s"`.
pub fn ancil_recv_fd(socket_fd: RawFd) -> Result<RawFd, ReceivingFdException> {
    // SAFETY: plain `recvmsg` into buffers of the right sizes.
    unsafe {
        let mut nothing: u8 = 0;
        let mut iov = libc::iovec {
            iov_base: &mut nothing as *mut u8 as *mut libc::c_void,
            iov_len: 1,
        };
        let mut buf = [0u64; CMSG_SPACE_ONE_FD / 8];
        let space = libc::CMSG_SPACE(std::mem::size_of::<libc::c_int>() as u32) as usize;
        let mut msghdr: libc::msghdr = std::mem::zeroed();
        msghdr.msg_iov = &mut iov;
        msghdr.msg_iovlen = 1;
        msghdr.msg_control = buf.as_mut_ptr() as *mut libc::c_void;
        msghdr.msg_controllen = space as _;
        let ret = loop {
            let ret = libc::recvmsg(socket_fd, &mut msghdr, 0);
            if ret < 0 && errno() == libc::EINTR {
                continue;
            }
            break ret;
        };
        let fail = |code: i32| {
            let msg = std::io::Error::from_raw_os_error(code).to_string();
            // `strerror` has no " (os error N)" suffix.
            let msg = match msg.rfind(" (os error ") {
                Some(i) => msg[..i].to_string(),
                None => msg,
            };
            Err(ReceivingFdException(format!("(errno={}) {}", code, msg)))
        };
        if ret < 0 {
            return fail(errno());
        }
        let cmsg = libc::CMSG_FIRSTHDR(&msghdr);
        if ret == 0
            || cmsg.is_null()
            || (*cmsg).cmsg_level != libc::SOL_SOCKET
            || (*cmsg).cmsg_type != libc::SCM_RIGHTS
        {
            // `ancil_recv_fds` returns -1 without setting errno when the
            // message carries no descriptor: errno is whatever it was.
            return fail(errno());
        }
        let fd = std::ptr::read_unaligned(libc::CMSG_DATA(cmsg) as *const libc::c_int);
        Ok(fd)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Read;
    use std::io::Write;
    use std::os::fd::AsRawFd;
    use std::os::fd::FromRawFd;
    use std::os::unix::net::UnixStream;

    use super::*;

    #[test]
    fn send_and_receive() {
        let (a, b) = UnixStream::pair().unwrap();
        let (mut c1, c2) = UnixStream::pair().unwrap();
        assert_eq!(ancil_send_fd(a.as_raw_fd(), c2.as_raw_fd()), 0);
        drop(c2);
        let fd = ancil_recv_fd(b.as_raw_fd()).unwrap();
        let mut c2 = unsafe { UnixStream::from_raw_fd(fd) };
        c1.write_all(b"hi").unwrap();
        let mut buf = [0u8; 2];
        c2.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"hi");
        drop(a);
        assert!(ancil_recv_fd(b.as_raw_fd()).is_err());
    }
}
