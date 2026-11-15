// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `heap/hh_shared.c`: the shared heap of the master and its worker
//! processes, with the hash table of Slack's settings
//! (`shm_use_sharded_hashtbl = false`: one open-addressing table, not
//! `shmffi`'s sharded one). With `shm_use_sharded_hashtbl = true` (which
//! `rust_provider_backend` takes) the table is this one too: `shmffi` is not
//! ported, and which table holds the entries is not something a client of
//! the server sees.
//!
//! The memory is one file mapping (`memfd_create` on Linux, `shm_open` on
//! macOS, as the OCaml) made by the master before it spawns the workers,
//! which map it again from the inherited file descriptor ([`connect`]). Its
//! layout is the OCaml's minus the parts nothing here uses (the global
//! storage of `hh_shared_store`, the per-worker counters): a page of global
//! counters, the hash table (`1 << hash_table_pow` slots of a 64-bit hash and
//! the address of the entry), then the heap, where entries are allocated by
//! bumping a pointer shared by every process (8-byte aligned; a 64-bit header
//! of the OCaml's layout, then the data). Workers add; only the master
//! removes, moves (oldifies) and collects (compacts), when no worker runs.
//!
//! What differs from the C, and why:
//! - An entry's address is its OFFSET from the start of the mapping. The OCaml
//!   maps the memory at the same fixed address in every process
//!   (`SHARED_MEM_INIT`) and stores pointers; offsets need no fixed address.
//! - The values are bytes: the caller serializes (`shared_mem`, with serde in
//!   place of `Marshal`); compression is here, as in `hh_store_ocaml`: lz4
//!   (the OCaml's `compression = 0`) when it makes the value smaller.
//! - Errors the OCaml raises as exceptions (`Hash_table_full`, `Heap_full`)
//!   are panics with the OCaml's exception names.

use std::os::fd::RawFd;
use std::sync::OnceLock;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;

/// What a worker needs to map the master's memory (`Shared_mem.handle`: the
/// fd and the sizes, `hh_get_handle`).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Handle {
    pub fd: RawFd,
    pub heap_size: u64,
    pub hash_table_pow: u64,
    pub num_workers: u64,
}

/// The global counters, at the start of the mapping (`define_globals`: the
/// "small objects page").
#[repr(C)]
struct Globals {
    /// `heap`: the top of the heap (an offset from the start of the mapping).
    heap_top: AtomicU64,
    /// `hcounter`: the slots whose hash is set.
    hcounter: AtomicU64,
    /// `hcounter_filled`: the slots that have a value.
    hcounter_filled: AtomicU64,
    /// `wasted_heap_size`
    wasted_heap_size: AtomicU64,
    /// `workers_should_exit`
    workers_should_exit: AtomicU64,
    /// `allow_removes`
    allow_removes: AtomicU64,
    /// `master_pid`
    master_pid: AtomicU64,
    /// `log_level`
    log_level: AtomicU64,
    /// `compression` (0: lz4; the zstd levels are not supported).
    compression: AtomicU64,
    /// `counter` (`hh_counter_next`).
    counter: AtomicU64,
}

/// A cell of the hash table (`helt_t`).
#[repr(C)]
struct Helt {
    hash: AtomicU64,
    /// 0: no value (`NULL`); [`WRITE_IN_PROGRESS`]; else the offset of the
    /// entry.
    addr: AtomicU64,
}

/// `HASHTBL_WRITE_IN_PROGRESS`
const WRITE_IN_PROGRESS: u64 = 1;

/// The page of the globals.
const GLOBALS_SIZE: usize = 4096;

/// `KIND_SERIALIZED`, `KIND_STRING` of an entry's header.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Serialized = 0,
    String = 1,
}

/// `hh_header_t`: `size << 33 | kind << 32 | uncompressed_size << 1 | 1`.
fn header(size: u64, kind: Kind, uncompressed_size: u64) -> u64 {
    size << 33 | (kind as u64) << 32 | uncompressed_size << 1 | 1
}

/// `Entry_size`
fn entry_size(header: u64) -> u64 {
    header >> 33
}

/// `Entry_kind`
fn entry_kind(header: u64) -> Kind {
    if (header >> 32) & 1 == 1 {
        Kind::String
    } else {
        Kind::Serialized
    }
}

/// `Entry_uncompressed_size`
fn entry_uncompressed_size(header: u64) -> u64 {
    (header >> 1) & 0x7FFF_FFFF
}

/// `HEAP_ALIGN(Heap_entry_total_size(header))`: the bytes an entry takes.
fn slot_size(header: u64) -> u64 {
    (8 + entry_size(header) + 7) & !7
}

struct Mem {
    base: *mut u8,
    size: usize,
    fd: RawFd,
    hashtbl_size: u64,
    /// The offsets of the start and the end of the heap.
    heap_init: u64,
    heap_max: u64,
    num_workers: u64,
    hash_table_pow: u64,
    heap_size: u64,
}

// The mapping is shared by design; every access goes through atomics or
// through entries that are immutable once published.
unsafe impl Send for Mem {}
unsafe impl Sync for Mem {}

static MEM: OnceLock<Mem> = OnceLock::new();

/// `my_pid` of the process that made the memory (`master_pid`).
fn my_pid() -> u64 {
    std::process::id() as u64
}

impl Mem {
    fn globals(&self) -> &Globals {
        unsafe { &*(self.base as *const Globals) }
    }

    fn helt(&self, slot: u64) -> &Helt {
        debug_assert!(slot < self.hashtbl_size);
        unsafe { &*((self.base.add(GLOBALS_SIZE) as *const Helt).add(slot as usize)) }
    }

    fn at(&self, offset: u64) -> *mut u8 {
        debug_assert!((offset as usize) < self.size);
        unsafe { self.base.add(offset as usize) }
    }

    fn entry_header(&self, offset: u64) -> u64 {
        unsafe { (self.at(offset) as *const u64).read() }
    }

    fn entry_data(&self, offset: u64) -> &[u8] {
        let size = entry_size(self.entry_header(offset)) as usize;
        unsafe { std::slice::from_raw_parts(self.at(offset + 8), size) }
    }
}

/// The memory of this process, if it made or connected to it.
fn mem() -> Option<&'static Mem> {
    MEM.get()
}

fn mem_or_panic() -> &'static Mem {
    MEM.get().expect("hh_shared: the shared heap is not initialised")
}

/// Whether this process has the shared heap (made it or connected to it).
pub fn is_initialized() -> bool {
    MEM.get().is_some()
}

/// `memfd_create_helper`: an anonymous file of `size` bytes whose fd the
/// workers inherit.
fn memfd_create_helper(name: &str, size: u64) -> std::io::Result<RawFd> {
    #[cfg(target_os = "linux")]
    {
        let cname = std::ffi::CString::new(name).unwrap();
        let fd = unsafe { libc::memfd_create(cname.as_ptr(), 0) };
        if fd < 0 {
            return Err(std::io::Error::last_os_error());
        }
        if unsafe { libc::ftruncate(fd, size as libc::off_t) } == -1 {
            return Err(std::io::Error::last_os_error());
        }
        Ok(fd)
    }
    #[cfg(not(target_os = "linux"))]
    {
        // As the OCaml on macOS: a POSIX shared memory object, unlinked at
        // once (it lives as long as a process maps it or holds the fd).
        let memname = std::ffi::CString::new(format!("/{}.{}", name, std::process::id())).unwrap();
        unsafe {
            libc::shm_unlink(memname.as_ptr());
            let fd = libc::shm_open(memname.as_ptr(), libc::O_CREAT | libc::O_RDWR, 0o666);
            if fd < 0 {
                return Err(std::io::Error::last_os_error());
            }
            libc::shm_unlink(memname.as_ptr());
            if libc::ftruncate(fd, size as libc::off_t) == -1 {
                let e = std::io::Error::last_os_error();
                libc::close(fd);
                return Err(e);
            }
            Ok(fd)
        }
    }
}

/// `memfd_map` (without `MAP_FIXED`: see the module documentation).
fn memfd_map(fd: RawFd, size: usize) -> std::io::Result<*mut u8> {
    let mem = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            size,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_SHARED | libc::MAP_NORESERVE,
            fd,
            0,
        )
    };
    if mem == libc::MAP_FAILED {
        return Err(std::io::Error::last_os_error());
    }
    Ok(mem as *mut u8)
}

fn sizes(heap_size: u64, hash_table_pow: u64) -> (u64, usize) {
    let hashtbl_size = 1u64 << hash_table_pow;
    let size = GLOBALS_SIZE + hashtbl_size as usize * std::mem::size_of::<Helt>() + heap_size as usize;
    (hashtbl_size, size)
}

/// `hh_shared_init`: makes the memory (the master, before it spawns its
/// workers) and returns the handle the workers connect with.
pub fn init(config: &crate::shared_mem::Config, num_workers: usize) -> std::io::Result<Handle> {
    let heap_size = config.heap_size.max(0) as u64;
    let hash_table_pow = config.hash_table_pow.max(0) as u64;
    let (hashtbl_size, size) = sizes(heap_size, hash_table_pow);
    let fd = memfd_create_helper("fb_heap", size as u64)?;
    let base = memfd_map(fd, size)?;
    let heap_init = (GLOBALS_SIZE + hashtbl_size as usize * std::mem::size_of::<Helt>()) as u64;
    let m = Mem {
        base,
        size,
        fd,
        hashtbl_size,
        heap_init,
        heap_max: size as u64,
        num_workers: num_workers as u64,
        hash_table_pow,
        heap_size,
    };
    // `init_shared_globals`
    let g = m.globals();
    g.heap_top.store(heap_init, Ordering::Relaxed);
    g.hcounter.store(0, Ordering::Relaxed);
    g.hcounter_filled.store(0, Ordering::Relaxed);
    g.wasted_heap_size.store(0, Ordering::Relaxed);
    g.workers_should_exit.store(0, Ordering::Relaxed);
    g.allow_removes.store(1, Ordering::Relaxed);
    g.master_pid.store(my_pid(), Ordering::Relaxed);
    g.log_level.store(config.log_level.max(0) as u64, Ordering::Relaxed);
    g.compression.store(config.compression.max(0) as u64, Ordering::Relaxed);
    g.counter.store(0, Ordering::Release);
    let handle = Handle {
        fd,
        heap_size,
        hash_table_pow,
        num_workers: num_workers as u64,
    };
    if MEM.set(m).is_err() {
        panic!("hh_shared: init called twice");
    }
    set_close_on_exec(true);
    Ok(handle)
}

/// `hh_connect`: a worker maps the master's memory.
pub fn connect(handle: &Handle) -> std::io::Result<()> {
    let (hashtbl_size, size) = sizes(handle.heap_size, handle.hash_table_pow);
    let base = memfd_map(handle.fd, size)?;
    let heap_init = (GLOBALS_SIZE + hashtbl_size as usize * std::mem::size_of::<Helt>()) as u64;
    let m = Mem {
        base,
        size,
        fd: handle.fd,
        hashtbl_size,
        heap_init,
        heap_max: size as u64,
        num_workers: handle.num_workers,
        hash_table_pow: handle.hash_table_pow,
        heap_size: handle.heap_size,
    };
    if MEM.set(m).is_err() {
        panic!("hh_shared: connect called twice");
    }
    set_close_on_exec(true);
    Ok(())
}

/// `hh_get_handle`
pub fn get_handle() -> Option<Handle> {
    mem().map(|m| Handle {
        fd: m.fd,
        heap_size: m.heap_size,
        hash_table_pow: m.hash_table_pow,
        num_workers: m.num_workers,
    })
}

/// `Shared_mem.set_close_on_exec` / `clear_close_on_exec` of the handle: the
/// fd is inherited only by the processes spawned while it is cleared (the
/// workers).
pub fn set_close_on_exec(on: bool) {
    if let Some(m) = mem() {
        unsafe {
            let flags = libc::fcntl(m.fd, libc::F_GETFD);
            if flags != -1 {
                let flags = if on { flags | libc::FD_CLOEXEC } else { flags & !libc::FD_CLOEXEC };
                libc::fcntl(m.fd, libc::F_SETFD, flags);
            }
        }
    }
}

/// `assert_master`
fn assert_master(m: &Mem) {
    assert_eq!(
        m.globals().master_pid.load(Ordering::Relaxed),
        my_pid(),
        "hh_shared: only the master may do this"
    );
}

/// `assert_allow_removes`
fn assert_allow_removes(m: &Mem) {
    assert!(m.globals().allow_removes.load(Ordering::Relaxed) != 0, "hh_shared: removes are not allowed");
}

/// Whether this process made the memory.
pub fn is_master() -> bool {
    mem().is_some_and(|m| m.globals().master_pid.load(Ordering::Relaxed) == my_pid())
}

// ~~ Cancellation ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `hh_stop_workers`
pub fn stop_workers() {
    let m = mem_or_panic();
    assert_master(m);
    m.globals().workers_should_exit.store(1, Ordering::SeqCst);
}

/// `hh_resume_workers`
pub fn resume_workers() {
    let m = mem_or_panic();
    assert_master(m);
    m.globals().workers_should_exit.store(0, Ordering::SeqCst);
}

/// The flag `workers_should_exit` (false before the memory exists).
#[inline]
pub fn workers_should_exit() -> bool {
    mem().is_some_and(|m| m.globals().workers_should_exit.load(Ordering::Relaxed) != 0)
}

/// `should_exit` (with `worker_can_exit`, which `crate::worker_cancel`
/// keeps).
pub fn should_exit() -> bool {
    crate::worker_cancel::is_stop_requested()
}

/// `raise_if_should_exit`: `Worker_should_exit` (the panic payload of
/// `worker_cancel`).
pub fn raise_if_should_exit() {
    crate::worker_cancel::raise_if_stop_requested()
}

// ~~ Allocation and the table ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `hh_alloc`: a chunk of the heap for an entry of this header.
fn hh_alloc(m: &Mem, header: u64) -> u64 {
    let size = slot_size(header);
    let offset = m.globals().heap_top.fetch_add(size, Ordering::Relaxed);
    if offset + size > m.heap_max {
        // `raise_heap_full`
        panic!("Shared_mem.Heap_full");
    }
    offset
}

/// What [`add`] stored: `(compressed_size, original_size, total_size)` of
/// `hh_add` (`None`: nothing new was added, the OCaml's negative sizes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Added {
    pub compressed_size: u64,
    pub original_size: u64,
    pub total_size: u64,
}

/// `hh_store_ocaml` of bytes already serialized: compressed with lz4 when
/// that makes them smaller.
fn hh_store(m: &Mem, data: &[u8], kind: Kind) -> (u64, Added) {
    assert!(data.len() < 0x8000_0000, "hh_shared: an entry of 2GB or more");
    let orig_size = data.len() as u64;
    let compressed = if data.is_empty() {
        None
    } else {
        lz4::block::compress(data, None, false).ok().filter(|c| !c.is_empty() && c.len() < data.len())
    };
    let (bytes, uncompressed_size): (&[u8], u64) = match &compressed {
        Some(c) => (c, orig_size),
        None => (data, 0),
    };
    let h = header(bytes.len() as u64, kind, uncompressed_size);
    let offset = hh_alloc(m, h);
    unsafe {
        (m.at(offset) as *mut u64).write(h);
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), m.at(offset + 8), bytes.len());
    }
    (
        offset,
        Added {
            compressed_size: bytes.len() as u64,
            original_size: orig_size,
            total_size: slot_size(h),
        },
    )
}

/// `write_at`: the first writer of a slot wins.
fn write_at(m: &Mem, slot: u64, data: &[u8], kind: Kind) -> Option<Added> {
    let helt = m.helt(slot);
    if helt
        .addr
        .compare_exchange(0, WRITE_IN_PROGRESS, Ordering::AcqRel, Ordering::Relaxed)
        .is_ok()
    {
        let (offset, added) = hh_store(m, data, kind);
        helt.addr.store(offset, Ordering::Release);
        m.globals().hcounter_filled.fetch_add(1, Ordering::Relaxed);
        Some(added)
    } else {
        None
    }
}

/// `raise_hash_table_full`
fn hash_table_full() -> ! {
    panic!("Shared_mem.Hash_table_full")
}

/// `hh_add`: adds the value of a key; a key that has a value keeps it (the
/// first writer wins).
pub fn add(hash: u64, data: &[u8], kind: Kind) -> Option<Added> {
    let m = mem_or_panic();
    raise_if_should_exit();
    let mask = m.hashtbl_size - 1;
    let mut slot = hash & mask;
    let init_slot = slot;
    loop {
        let helt = m.helt(slot);
        let slot_hash = helt.hash.load(Ordering::Acquire);
        if slot_hash == hash {
            return write_at(m, slot, data, kind);
        }
        if m.globals().hcounter.load(Ordering::Relaxed) >= m.hashtbl_size {
            hash_table_full()
        }
        if slot_hash == 0 {
            match helt.hash.compare_exchange(0, hash, Ordering::AcqRel, Ordering::Acquire) {
                Ok(_) => {
                    let size = m.globals().hcounter.fetch_add(1, Ordering::Relaxed);
                    assert!(size < m.hashtbl_size);
                    return write_at(m, slot, data, kind);
                }
                Err(now) if now == hash => return write_at(m, slot, data, kind),
                Err(_) => {}
            }
        }
        slot = (slot + 1) & mask;
        if slot == init_slot {
            hash_table_full()
        }
    }
}

/// `find_slot`: the slot of the key, or the free slot where it would go.
fn find_slot(m: &Mem, hash: u64) -> u64 {
    let mask = m.hashtbl_size - 1;
    let mut slot = hash & mask;
    let init_slot = slot;
    loop {
        let h = m.helt(slot).hash.load(Ordering::Acquire);
        if h == hash || h == 0 {
            return slot;
        }
        slot = (slot + 1) & mask;
        if slot == init_slot {
            hash_table_full()
        }
    }
}

/// `hh_is_slot_taken_for_key`: the offset of the key's entry, once written.
fn taken(m: &Mem, slot: u64, hash: u64) -> Option<u64> {
    let helt = m.helt(slot);
    if helt.hash.load(Ordering::Acquire) != hash {
        return None;
    }
    let mut addr = helt.addr.load(Ordering::Acquire);
    if addr == 0 {
        return None;
    }
    let start = std::time::Instant::now();
    while addr == WRITE_IN_PROGRESS {
        std::hint::spin_loop();
        // If the worker writing the data dies, we can get stuck.
        if start.elapsed().as_secs() > 60 {
            panic!("hh_mem busy-wait loop stuck for 60s");
        }
        addr = helt.addr.load(Ordering::Acquire);
    }
    Some(addr)
}

/// `hh_mem`
pub fn mem_(hash: u64) -> bool {
    let m = mem_or_panic();
    raise_if_should_exit();
    let slot = find_slot(m, hash);
    taken(m, slot, hash).is_some()
}

/// `hh_get_and_deserialize` up to the deserialization: `f` is given the
/// bytes of the key's value (decompressed) and its kind.
pub fn get<T>(hash: u64, f: impl FnOnce(&[u8], Kind) -> T) -> Option<T> {
    if GET_TIMING.load(Ordering::Relaxed) {
        let start = std::time::Instant::now();
        let r = get_(hash, f);
        GET_NANOS.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        GET_COUNT.fetch_add(1, Ordering::Relaxed);
        return r;
    }
    get_(hash, f)
}

/// The time and number of [`get`]s of this process (with their
/// decompression and the caller's decoding), when `GET_TIMING` is set
/// (instrumentation: `HH_MEM_WORKER_FP`).
pub static GET_TIMING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
pub static GET_NANOS: AtomicU64 = AtomicU64::new(0);
pub static GET_COUNT: AtomicU64 = AtomicU64::new(0);

fn get_<T>(hash: u64, f: impl FnOnce(&[u8], Kind) -> T) -> Option<T> {
    let m = mem_or_panic();
    raise_if_should_exit();
    let slot = find_slot(m, hash);
    let offset = taken(m, slot, hash)?;
    let h = m.entry_header(offset);
    let data = m.entry_data(offset);
    let uncompressed = entry_uncompressed_size(h);
    if uncompressed != 0 {
        let bytes = lz4::block::decompress(data, Some(uncompressed as i32))
            .expect("hh_shared: a corrupt compressed entry");
        assert_eq!(bytes.len() as u64, uncompressed);
        Some(f(&bytes, entry_kind(h)))
    } else {
        Some(f(data, entry_kind(h)))
    }
}

/// `hh_get_size`: the stored (compressed) size of the key's value.
pub fn get_size(hash: u64) -> Option<u64> {
    let m = mem_or_panic();
    let slot = find_slot(m, hash);
    taken(m, slot, hash).map(|offset| entry_size(m.entry_header(offset)))
}

/// The sizes of the key's entry: (stored, before compression, slot), as the
/// MEM census of the OCaml (`hh_census_entry`, instrumentation).
pub fn census_entry(hash: u64) -> Option<(u64, u64, u64)> {
    let m = mem_or_panic();
    let slot = find_slot(m, hash);
    let offset = taken(m, slot, hash)?;
    let h = m.entry_header(offset);
    let stored = entry_size(h);
    let orig = match entry_uncompressed_size(h) {
        0 => stored,
        u => u,
    };
    Some((stored, orig, slot_size(h)))
}

/// `hh_move`: moves the value of `hash1` to `hash2` (free). Master only.
pub fn move_(hash1: u64, hash2: u64) {
    let m = mem_or_panic();
    let slot1 = find_slot(m, hash1);
    let slot2 = find_slot(m, hash2);
    assert_master(m);
    assert_allow_removes(m);
    let h1 = m.helt(slot1);
    let h2 = m.helt(slot2);
    assert_eq!(h1.hash.load(Ordering::Relaxed), hash1);
    assert_eq!(h2.addr.load(Ordering::Relaxed), 0);
    if h2.hash.load(Ordering::Relaxed) == 0 {
        m.globals().hcounter.fetch_add(1, Ordering::Relaxed);
    }
    h2.hash.store(hash2, Ordering::Release);
    h2.addr.store(h1.addr.load(Ordering::Acquire), Ordering::Release);
    h1.addr.store(0, Ordering::Release);
}

/// `hh_remove`: removes the key's value (which must exist) and returns its
/// stored size. Master only.
pub fn remove(hash: u64) -> u64 {
    remove_if_present(hash).expect("hh_remove of a key without a value")
}

/// [`remove`] if the key has a value: its stored size. Master only.
///
/// (The value is taken with a compare-and-swap of its address, where
/// `hh_remove` stores NULL: the OCaml's master is one thread, the Rust's
/// has several (RPC requests, the threads' typing without workers), and two
/// of them may replace the same decl at once (`ctx::DeclMap::insert`); only
/// one of them removes it.)
pub fn remove_if_present(hash: u64) -> Option<u64> {
    let m = mem_or_panic();
    let slot = find_slot(m, hash);
    assert_master(m);
    assert_allow_removes(m);
    let helt = m.helt(slot);
    if helt.hash.load(Ordering::Acquire) != hash {
        return None;
    }
    let offset = helt.addr.load(Ordering::Acquire);
    if offset <= WRITE_IN_PROGRESS
        || helt.addr.compare_exchange(offset, 0, Ordering::AcqRel, Ordering::Relaxed).is_err()
    {
        return None;
    }
    let h = m.entry_header(offset);
    m.globals().wasted_heap_size.fetch_add(slot_size(h), Ordering::Relaxed);
    REMOVED_COUNT.fetch_add(1, Ordering::Relaxed);
    m.globals().hcounter_filled.fetch_sub(1, Ordering::Relaxed);
    Some(entry_size(h))
}

/// `removed_count` (of this process).
static REMOVED_COUNT: AtomicU64 = AtomicU64::new(0);

/// `hh_removed_count`
pub fn removed_count() -> u64 {
    REMOVED_COUNT.load(Ordering::Relaxed)
}

/// `hh_set_allow_removes`
pub fn set_allow_removes(allow: bool) {
    if let Some(m) = mem() {
        m.globals().allow_removes.store(allow as u64, Ordering::Relaxed);
    }
}

/// `hh_collect`: compacts the heap: the live entries slide to the bottom
/// (in heap order), the table is updated, the dead ones are dropped. Master
/// only, with no worker running.
///
/// As the C, the space freed at the top is not given back to the system
/// ("will almost certainly become used again soon").
pub fn collect() {
    let m = mem_or_panic();
    assert_master(m);
    assert_allow_removes(m);
    // Step 1: mark. The header of every live entry moves to its slot's addr
    // field, and the entry's first word gets the slot's index (shifted, so
    // that its low bit, 1 in a header, is 0).
    for i in 0..m.hashtbl_size {
        let helt = m.helt(i);
        let addr = helt.addr.load(Ordering::Acquire);
        if addr == 0 {
            continue;
        }
        assert_ne!(addr, WRITE_IN_PROGRESS, "hh_collect while a worker writes");
        let h = m.entry_header(addr);
        helt.addr.store(h, Ordering::Relaxed);
        unsafe { (m.at(addr) as *mut u64).write(i << 1) };
    }
    // Step 2: walk the heap and move the live entries down.
    let top = m.globals().heap_top.load(Ordering::Acquire);
    let mut dest = m.heap_init;
    let mut src = m.heap_init;
    while src < top {
        let word = unsafe { (m.at(src) as *const u64).read() };
        let size;
        if word & 1 == 1 {
            // A header: the entry is dead.
            size = slot_size(word);
        } else {
            let slot = word >> 1;
            let helt = m.helt(slot);
            let h = helt.addr.load(Ordering::Relaxed);
            size = slot_size(h);
            helt.addr.store(dest, Ordering::Relaxed);
            unsafe {
                (m.at(src) as *mut u64).write(h);
                std::ptr::copy(m.at(src), m.at(dest), size as usize);
            }
            dest += size;
        }
        src += size;
    }
    m.globals().heap_top.store(dest, Ordering::Release);
    m.globals().wasted_heap_size.store(0, Ordering::Relaxed);
}

// ~~ Telemetry ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `hh_used_heap_size`
pub fn used_heap_size() -> u64 {
    mem().map_or(0, |m| m.globals().heap_top.load(Ordering::Relaxed) - m.heap_init)
}

/// `hh_wasted_heap_size`
pub fn wasted_heap_size() -> u64 {
    mem().map_or(0, |m| m.globals().wasted_heap_size.load(Ordering::Relaxed))
}

/// `hh_hash_used_slots`: (slots with a hash, slots with a value).
pub fn hash_used_slots() -> (u64, u64) {
    mem().map_or((0, 0), |m| {
        (
            m.globals().hcounter.load(Ordering::Relaxed),
            m.globals().hcounter_filled.load(Ordering::Relaxed),
        )
    })
}

/// `hh_hash_slots`
pub fn hash_slots() -> u64 {
    mem().map_or(0, |m| m.hashtbl_size)
}

/// `hh_log_level`
pub fn log_level() -> u64 {
    mem().map_or(0, |m| m.globals().log_level.load(Ordering::Relaxed))
}

/// `hh_check_heap_overflow`
pub fn check_heap_overflow() -> bool {
    mem().is_some_and(|m| m.globals().heap_top.load(Ordering::Relaxed) >= m.heap_max)
}

/// `hh_counter_next`: a counter that increases over the life of the master
/// and all its workers (the OCaml reserves ranges per worker; one atomic
/// here).
pub fn counter_next() -> u64 {
    match mem() {
        Some(m) => m.globals().counter.fetch_add(1, Ordering::Relaxed) + 1,
        None => {
            static EARLY: AtomicU64 = AtomicU64::new(0);
            EARLY.fetch_add(1, Ordering::Relaxed) + 1
        }
    }
}

/// The key hash of the OCaml's `KeyHasher.hash`: the first 8 bytes of
/// `Stdlib.Digest.string (prefix ^ key)` (MD5), read as the C reads them
/// (`*((uint64_t*)String_val(key))`, little-endian here).
pub fn hash_key(prefix: &[u8], key: &[u8]) -> u64 {
    use md5::Digest;
    let mut h = md5::Md5::new();
    h.update(prefix);
    h.update(key);
    let d = h.finalize();
    let mut b = [0u8; 8];
    b.copy_from_slice(&d[..8]);
    u64::from_le_bytes(b)
}

#[cfg(test)]
mod tests;
