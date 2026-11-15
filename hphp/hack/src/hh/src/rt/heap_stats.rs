// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Heap accounting for the daemon's memory work (no OCaml counterpart).
//!
//! - [`Counting`]: a global allocator around another one that counts the
//!   bytes live (allocated and not freed). The lib test binary uses it (the
//!   recheck-cycle tests assert on [`live_bytes`]); `hh_server` uses it when
//!   built with `RUSTFLAGS="--cfg hh_heap_stats"` (never in a release
//!   build: it costs a few percent of allocation-heavy work).
//! - [`process_info`]: what mimalloc holds (committed bytes, RSS), whichever
//!   global allocator counts.
//! - [`log_line`]: one `HEAP_STATS` line for the server log.

// (Links mimalloc, whose `mi_*` functions are called below, even when it
// is not the global allocator.)
extern crate mimalloc;

use std::alloc::GlobalAlloc;
use std::alloc::Layout;
use std::cell::Cell;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicI64;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

// One counter per shard, each thread taking a shard once: a single atomic
// would be contended by every allocating thread. (No OCaml counterpart: the
// OCaml has no allocator to wrap.)
const SHARDS: usize = 64;

#[repr(align(128))]
struct Shard(AtomicI64);

#[allow(clippy::declare_interior_mutable_const)]
const ZERO: Shard = Shard(AtomicI64::new(0));
static LIVE: [Shard; SHARDS] = [ZERO; SHARDS];
static COUNTING: AtomicBool = AtomicBool::new(false);
static NEXT_SHARD: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    static SHARD: Cell<usize> = const { Cell::new(usize::MAX) };
}

#[inline]
fn shard() -> &'static AtomicI64 {
    // `try_with`: a thread being torn down still frees.
    let i = SHARD
        .try_with(|s| {
            let mut i = s.get();
            if i == usize::MAX {
                i = NEXT_SHARD.fetch_add(1, Ordering::Relaxed) % SHARDS;
                s.set(i);
            }
            i
        })
        .unwrap_or(0);
    &LIVE[i].0
}

/// A global allocator that counts the bytes live in `A`.
pub struct Counting<A>(pub A);

unsafe impl<A: GlobalAlloc> GlobalAlloc for Counting<A> {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if SAMPLE_EVERY.load(Ordering::Relaxed) != 0 {
            if let Some(p) = sampler::maybe_sample(layout, false) {
                shard().fetch_add(layout.size() as i64, Ordering::Relaxed);
                return p;
            }
        }
        let p = unsafe { self.0.alloc(layout) };
        if !p.is_null() {
            shard().fetch_add(layout.size() as i64, Ordering::Relaxed);
        }
        p
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if SAMPLE_EVERY.load(Ordering::Relaxed) != 0 {
            if let Some(p) = sampler::maybe_sample(layout, true) {
                shard().fetch_add(layout.size() as i64, Ordering::Relaxed);
                return p;
            }
        }
        let p = unsafe { self.0.alloc_zeroed(layout) };
        if !p.is_null() {
            shard().fetch_add(layout.size() as i64, Ordering::Relaxed);
        }
        p
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if SAMPLED.load(Ordering::Relaxed) {
            sampler::forget(ptr);
        }
        unsafe { self.0.dealloc(ptr, layout) };
        shard().fetch_sub(layout.size() as i64, Ordering::Relaxed);
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if SAMPLED.load(Ordering::Relaxed) {
            if let Some(p) = sampler::realloc(ptr, layout, new_size) {
                shard().fetch_add(new_size as i64 - layout.size() as i64, Ordering::Relaxed);
                return p;
            }
        }
        let p = unsafe { self.0.realloc(ptr, layout, new_size) };
        if !p.is_null() {
            shard().fetch_add(new_size as i64 - layout.size() as i64, Ordering::Relaxed);
        }
        p
    }
}

impl<A> Counting<A> {
    /// Call once at startup from the binary that installs this allocator,
    /// so that [`live_bytes`] answers.
    pub fn enable(&self) {
        COUNTING.store(true, Ordering::Relaxed);
    }
}

/// Sampling of the live allocations of a [`Counting`] allocator by call
/// stack (for the memory breakdown; no cost unless enabled): about one
/// allocation per `every` bytes allocated by a thread is made in a heap of
/// its own and its stack recorded (frame pointers: always kept on Apple
/// arm64); [`sampler::report`] writes the live samples by stack.
static SAMPLE_EVERY: AtomicUsize = AtomicUsize::new(0);
/// Sampling was ever on (frees look up their block from then on).
static SAMPLED: AtomicBool = AtomicBool::new(false);

pub mod sampler {
    use std::alloc::Layout;
    use std::cell::Cell;
    use std::ffi::c_void;
    use std::sync::Mutex;
    use std::sync::atomic::AtomicPtr;
    use std::sync::atomic::Ordering;

    const FRAMES: usize = 28;

    struct Sample {
        weight: usize,
        frames: [usize; FRAMES],
    }

    unsafe extern "C" {
        fn mi_heap_new() -> *mut c_void;
        fn mi_heap_contains(heap: *const c_void, p: *const c_void) -> bool;
        fn mi_heap_malloc_aligned(heap: *mut c_void, size: usize, align: usize) -> *mut c_void;
        fn mi_heap_zalloc_aligned(heap: *mut c_void, size: usize, align: usize) -> *mut c_void;
        fn mi_free(p: *mut c_void);
    }

    #[cfg(target_os = "macos")]
    unsafe extern "C" {
        fn _dyld_get_image_vmaddr_slide(image_index: u32) -> isize;
    }

    /// The offset the main executable is loaded at, taken off the recorded
    /// return addresses so that they can be looked up in the binary. Stacks
    /// are only recorded on Apple arm64 (see `stack`): 0 elsewhere.
    fn image_slide() -> isize {
        #[cfg(target_os = "macos")]
        {
            // SAFETY: image 0 is the main executable.
            unsafe { _dyld_get_image_vmaddr_slide(0) }
        }
        #[cfg(not(target_os = "macos"))]
        {
            0
        }
    }

    static HEAP: AtomicPtr<c_void> = AtomicPtr::new(std::ptr::null_mut());
    static SAMPLES: Mutex<Option<std::collections::HashMap<usize, Sample>>> = Mutex::new(None);

    thread_local! {
        static SINCE: Cell<usize> = const { Cell::new(0) };
        static INSIDE: Cell<bool> = const { Cell::new(false) };
    }

    /// Starts sampling about one allocation per `every` bytes.
    pub fn enable(every: usize) {
        // SAFETY: no preconditions.
        HEAP.store(unsafe { mi_heap_new() }, Ordering::SeqCst);
        *SAMPLES.lock().unwrap() = Some(Default::default());
        super::SAMPLED.store(true, Ordering::SeqCst);
        super::SAMPLE_EVERY.store(every, Ordering::SeqCst);
    }

    #[inline(never)]
    fn stack() -> [usize; FRAMES] {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        let mut frames = [0usize; FRAMES];
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        let frames = [0usize; FRAMES];
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            let mut fp: usize;
            // SAFETY: reads the frame pointer register.
            unsafe { std::arch::asm!("mov {}, x29", out(reg) fp) };
            let mut i = 0;
            while i < FRAMES && fp != 0 && fp % 8 == 0 {
                // SAFETY: Apple arm64 keeps the frame chain: [fp] is the
                // caller's frame pointer, [fp + 8] the return address; the
                // chain goes up the stack and ends with 0.
                let (next, ret) = unsafe { (*(fp as *const usize), *((fp + 8) as *const usize)) };
                if ret == 0 {
                    break;
                }
                frames[i] = ret;
                i += 1;
                if next <= fp || next - fp > (64 << 20) {
                    break;
                }
                fp = next;
            }
        }
        frames
    }

    #[inline(never)]
    pub(super) fn maybe_sample(layout: Layout, zeroed: bool) -> Option<*mut u8> {
        let every = super::SAMPLE_EVERY.load(Ordering::Relaxed);
        let since = SINCE.try_with(|s| {
            let n = s.get() + layout.size();
            s.set(if n >= every { 0 } else { n });
            n
        });
        let Ok(since) = since else { return None };
        if since < every || INSIDE.try_with(|i| i.replace(true)).unwrap_or(true) {
            return None;
        }
        let heap = HEAP.load(Ordering::Relaxed);
        // SAFETY: a heap of `mi_heap_new`.
        let p = unsafe {
            if zeroed {
                mi_heap_zalloc_aligned(heap, layout.size(), layout.align())
            } else {
                mi_heap_malloc_aligned(heap, layout.size(), layout.align())
            }
        };
        if !p.is_null() {
            let frames = stack();
            if let Some(map) = SAMPLES.lock().unwrap().as_mut() {
                map.insert(p as usize, Sample { weight: since, frames });
            }
        }
        INSIDE.with(|i| i.set(false));
        (!p.is_null()).then_some(p.cast())
    }

    #[inline]
    pub(super) fn forget(p: *mut u8) {
        let heap = HEAP.load(Ordering::Relaxed);
        // SAFETY: `p` is a block of mimalloc.
        if !heap.is_null() && unsafe { mi_heap_contains(heap, p.cast()) } {
            let inside = INSIDE.try_with(|i| i.replace(true)).unwrap_or(true);
            if let Some(map) = SAMPLES.lock().unwrap().as_mut() {
                map.remove(&(p as usize));
            }
            if !inside {
                INSIDE.with(|i| i.set(false));
            }
        }
    }

    /// The realloc of a sampled block: a new block in the sampling heap,
    /// which keeps the sample (its stack, its weight plus the growth).
    /// `None` for a block that is not sampled.
    pub(super) fn realloc(p: *mut u8, layout: Layout, new_size: usize) -> Option<*mut u8> {
        let heap = HEAP.load(Ordering::Relaxed);
        // SAFETY: `p` is a block of mimalloc.
        if heap.is_null() || !unsafe { mi_heap_contains(heap, p.cast()) } {
            return None;
        }
        let inside = INSIDE.try_with(|i| i.replace(true)).unwrap_or(true);
        // SAFETY: a heap of `mi_heap_new`; `p` holds `layout.size()` bytes.
        let q = unsafe { mi_heap_malloc_aligned(heap, new_size, layout.align()) } as *mut u8;
        if !q.is_null() {
            unsafe {
                std::ptr::copy_nonoverlapping(p, q, layout.size().min(new_size));
                mi_free(p.cast());
            }
            if let Some(map) = SAMPLES.lock().unwrap().as_mut() {
                if let Some(mut s) = map.remove(&(p as usize)) {
                    s.weight = (s.weight as isize + new_size as isize - layout.size() as isize).max(0) as usize;
                    map.insert(q as usize, s);
                }
            }
        }
        if !inside {
            INSIDE.with(|i| i.set(false));
        }
        Some(q)
    }

    /// Writes the live samples to `path`, aggregated by stack: a header
    /// line `binary <path> slide <hex>`, then per stack `bytes count
    /// addr...` (addresses without the slide, for `atos -o binary`),
    /// largest first. Returns the bytes the samples stand for.
    pub fn report(path: &std::path::Path) -> usize {
        use std::io::Write;
        // (No sample is taken on this thread meanwhile: the allocations
        // below happen with the table locked.)
        let was_inside = INSIDE.with(|i| i.replace(true));
        let mut by_stack: std::collections::HashMap<[usize; FRAMES], (usize, usize)> = Default::default();
        {
            let samples = SAMPLES.lock().unwrap();
            for s in samples.as_ref().into_iter().flat_map(|m| m.values()) {
                let e = by_stack.entry(s.frames).or_default();
                e.0 += s.weight;
                e.1 += 1;
            }
        }
        INSIDE.with(|i| i.set(was_inside));
        let mut v: Vec<_> = by_stack.into_iter().collect();
        v.sort_by(|a, b| b.1.0.cmp(&a.1.0));
        let slide = image_slide();
        let mut f = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
        let exe = std::env::current_exe().unwrap();
        writeln!(f, "binary {} slide {:x}", exe.display(), slide).unwrap();
        let mut total = 0;
        for (frames, (bytes, n)) in v {
            total += bytes;
            write!(f, "{bytes} {n}").unwrap();
            for a in frames.iter().take_while(|a| **a != 0) {
                write!(f, " {:x}", (*a as isize - slide) as usize).unwrap();
            }
            writeln!(f).unwrap();
        }
        total
    }
}

/// The bytes live in the global allocator, when it is a [`Counting`] one
/// (enabled).
pub fn live_bytes() -> Option<i64> {
    if !COUNTING.load(Ordering::Relaxed) {
        return None;
    }
    Some(LIVE.iter().map(|s| s.0.load(Ordering::Relaxed)).sum())
}

unsafe extern "C" {
    fn mi_process_info(
        elapsed_msecs: *mut usize,
        user_msecs: *mut usize,
        system_msecs: *mut usize,
        current_rss: *mut usize,
        peak_rss: *mut usize,
        current_commit: *mut usize,
        peak_commit: *mut usize,
        page_faults: *mut usize,
    );
    fn mi_collect(force: bool);
}

/// mimalloc's view of the process: `(current_rss, peak_rss,
/// current_commit, peak_commit)` in bytes.
pub fn process_info() -> (usize, usize, usize, usize) {
    let mut v = [0usize; 8];
    let [a, b, c, d, e, f, g, h] = &mut v;
    // SAFETY: every out-pointer is valid.
    unsafe { mi_process_info(a, b, c, d, e, f, g, h) };
    (v[3], v[4], v[5], v[6])
}

/// The physical footprint of this process (what `footprint` and Activity
/// Monitor report; macOS only, else 0).
pub fn phys_footprint() -> u64 {
    #[cfg(target_os = "macos")]
    {
        let mut ri: libc::rusage_info_v2 = unsafe { std::mem::zeroed() };
        // SAFETY: `ri` is a `rusage_info_v2`, the flavor asked for.
        let r = unsafe {
            libc::proc_pid_rusage(
                libc::getpid(),
                libc::RUSAGE_INFO_V2,
                (&mut ri as *mut libc::rusage_info_v2).cast(),
            )
        };
        if r == 0 {
            return ri.ri_phys_footprint;
        }
    }
    0
}

/// `mi_collect(force)`: mimalloc returns the free memory of the calling
/// thread's heap (and with `force`, abandoned pages) to the OS.
pub fn collect(force: bool) {
    // SAFETY: no preconditions.
    unsafe { mi_collect(force) }
}

/// A switch of the memory work read from the environment once per name:
/// `NAME=1` on, `NAME=0` off, unset: `default`.
pub fn switch(name: &'static str, default: bool) -> bool {
    static SWITCHES: std::sync::Mutex<Vec<(&'static str, bool)>> = std::sync::Mutex::new(Vec::new());
    let mut switches = SWITCHES.lock().unwrap();
    if let Some((_, on)) = switches.iter().find(|(n, _)| *n == name) {
        return *on;
    }
    let on = std::env::var_os(name).map_or(default, |v| v != "0");
    switches.push((name, on));
    on
}

#[repr(C)]
struct MiHeapArea {
    blocks: *mut std::ffi::c_void,
    reserved: usize,
    committed: usize,
    used: usize,
    block_size: usize,
    full_block_size: usize,
    reserved1: *mut std::ffi::c_void,
}

type MiBlockVisit = unsafe extern "C" fn(
    heap: *const std::ffi::c_void,
    area: *const MiHeapArea,
    block: *mut std::ffi::c_void,
    block_size: usize,
    arg: *mut std::ffi::c_void,
) -> bool;

unsafe extern "C" {
    fn mi_heap_visit_blocks(heap: *mut std::ffi::c_void, visit_blocks: bool, f: MiBlockVisit, arg: *mut std::ffi::c_void) -> bool;
    fn mi_heap_visit_abandoned_blocks(heap: *mut std::ffi::c_void, visit_blocks: bool, f: MiBlockVisit, arg: *mut std::ffi::c_void) -> bool;
    fn mi_stats_print_out(out: unsafe extern "C" fn(msg: *const std::ffi::c_char, arg: *mut std::ffi::c_void), arg: *mut std::ffi::c_void);
}

/// The pages of mimalloc's main heap (all threads): per class of block
/// size, `(pages, committed bytes, bytes in use)`, and the committed bytes
/// of the pages by how full they are.
#[derive(Default, Debug)]
struct Pages {
    by_class: [(usize, usize, usize); 6],
    by_fill: [usize; 5],
}

unsafe extern "C" fn visit_page(
    _heap: *const std::ffi::c_void,
    area: *const MiHeapArea,
    block: *mut std::ffi::c_void,
    _block_size: usize,
    arg: *mut std::ffi::c_void,
) -> bool {
    if !block.is_null() {
        return true;
    }
    // SAFETY: mimalloc passes its area and our `Pages`.
    let (area, pages) = unsafe { (&*area, &mut *(arg as *mut Pages)) };
    let class = match area.block_size {
        0..=1024 => 0,
        1025..=8192 => 1,
        8193..=65536 => 2,
        65537..=524288 => 3,
        524289..=8388608 => 4,
        _ => 5,
    };
    let used = area.used * area.block_size;
    let c = &mut pages.by_class[class];
    c.0 += 1;
    c.1 += area.committed;
    c.2 += used;
    let fill = if area.committed == 0 { 0 } else { used * 100 / area.committed };
    pages.by_fill[match fill {
        0..=9 => 0,
        10..=24 => 1,
        25..=49 => 2,
        50..=74 => 3,
        _ => 4,
    }] += area.committed;
    true
}

/// What mimalloc holds, page by page (for the memory breakdown: the
/// committed memory that is not in use, and where): the pages of all the
/// threads, by size class and by how full they are; the abandoned ones
/// (of threads that ended); and mimalloc's own statistics (of all the
/// threads) when `stats`.
pub fn mi_report(stats: bool) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    let mut pages = Pages::default();
    let mut abandoned = Pages::default();
    // SAFETY: the visitor and its argument match; NULL is the main heap.
    unsafe {
        mi_heap_visit_blocks(std::ptr::null_mut(), false, visit_page, (&mut pages as *mut Pages).cast());
        mi_heap_visit_abandoned_blocks(std::ptr::null_mut(), false, visit_page, (&mut abandoned as *mut Pages).cast());
    }
    let names = ["<=1K", "<=8K", "<=64K", "<=512K", "<=8M", "huge"];
    let total: (usize, usize, usize) = pages.by_class.iter().fold((0, 0, 0), |a, c| (a.0 + c.0, a.1 + c.1, a.2 + c.2));
    let (_, _, commit, _) = process_info();
    writeln!(
        out,
        "    mimalloc pages: {} pages, committed {:.1} MB, in use {:.1} MB (free in pages {:.1} MB); committed outside pages {:.1} MB (of {:.1} MB)",
        total.0,
        total.1 as f64 / 1e6,
        total.2 as f64 / 1e6,
        (total.1 - total.2) as f64 / 1e6,
        (commit as f64 - total.1 as f64) / 1e6,
        commit as f64 / 1e6
    )
    .unwrap();
    for (n, c) in names.iter().zip(pages.by_class.iter()) {
        if c.0 > 0 {
            writeln!(out, "      blocks {n:>6}: {:>7} pages, committed {:>8.1} MB, in use {:>8.1} MB", c.0, c.1 as f64 / 1e6, c.2 as f64 / 1e6).unwrap();
        }
    }
    let fills = ["<10%", "10-25%", "25-50%", "50-75%", ">=75%"];
    let f: Vec<String> = fills.iter().zip(pages.by_fill.iter()).map(|(n, b)| format!("{n} {:.1}", *b as f64 / 1e6)).collect();
    writeln!(out, "      committed MB of pages by fill: {}", f.join(", ")).unwrap();
    let ab: (usize, usize, usize) = abandoned.by_class.iter().fold((0, 0, 0), |a, c| (a.0 + c.0, a.1 + c.1, a.2 + c.2));
    writeln!(out, "      abandoned: {} pages, committed {:.1} MB, in use {:.1} MB", ab.0, ab.1 as f64 / 1e6, ab.2 as f64 / 1e6).unwrap();
    if stats {
        unsafe extern "C" fn push(msg: *const std::ffi::c_char, arg: *mut std::ffi::c_void) {
            // SAFETY: mimalloc passes a C string and our `String`.
            let (msg, out) = unsafe { (std::ffi::CStr::from_ptr(msg), &mut *(arg as *mut String)) };
            out.push_str(&msg.to_string_lossy());
        }
        let mut text = String::new();
        // SAFETY: `push` and its argument match.
        unsafe { mi_stats_print_out(push, (&mut text as *mut String).cast()) };
        for l in text.lines() {
            writeln!(out, "      | {l}").unwrap();
        }
    }
    out
}

fn mb(x: f64) -> String {
    format!("{:.1}", x / 1e6)
}

/// `HEAP_STATS live=<MB> commit=<MB> rss=<MB> peak_rss=<MB>` (live is
/// `-` when the allocator does not count).
pub fn log_line(what: &str) -> String {
    let (rss, peak_rss, commit, _) = process_info();
    let live = live_bytes().map_or("-".to_string(), |b| mb(b as f64));
    format!(
        "HEAP_STATS {} live={} commit={} rss={} peak_rss={} footprint={}",
        what,
        live,
        mb(commit as f64),
        mb(rss as f64),
        mb(peak_rss as f64),
        mb(phys_footprint() as f64)
    )
}

#[cfg(feature = "port")]
/// After each check of the daemon (the end of `Server_type_check.type_check`):
/// with a counting allocator or `HH_HEAP_STATS=1`, a `HEAP_STATS` line in
/// the server log.
pub fn after_recheck() {
    static STATS: std::sync::LazyLock<bool> =
        std::sync::LazyLock::new(|| std::env::var_os("HH_HEAP_STATS").is_some_and(|v| v != "0"));
    if *STATS || live_bytes().is_some() {
        crate::hh_logger::log(&log_line("recheck_end"));
    }
    // A counting `hh_server` with `HH_HEAP_SAMPLE=<bytes>` (see
    // `bin/hh_server.rs`) and `HH_HEAP_SAMPLE_OUT=<dir>`: the live samples
    // after each check, in `<dir>/check<N>.txt`.
    if SAMPLED.load(Ordering::Relaxed) {
        if let Some(dir) = std::env::var_os("HH_HEAP_SAMPLE_OUT") {
            static N: AtomicUsize = AtomicUsize::new(0);
            let n = N.fetch_add(1, Ordering::Relaxed);
            let path = std::path::Path::new(&dir).join(format!("check{n}.txt"));
            let bytes = sampler::report(&path);
            crate::hh_logger::log(&format!("HEAP_SAMPLES {:.1} MB in {}", bytes as f64 / 1e6, path.display()));
        }
    }
}

#[cfg(all(test, feature = "server"))]
pub(crate) mod tests;
