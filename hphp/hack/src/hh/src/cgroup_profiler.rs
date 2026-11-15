// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/cgroup/cgroup_profiler.ml`, with the background thread of
//! `cgroupWatcher.c` (`cgroup_watcher_start`, `cgroup_watcher_get`).
//!
//! The Cgroup_profiler module is to help us keep track of how cgroup memory
//! usage evolves during the various steps of work done by hh_server.
//!
//! It helps to group steps into groups. An example step-group is "init",
//! which is made up of steps "update naming table" then "update depgraph".
//!
//! Where there is no cgroup v2 (macOS), every reading fails: nothing is
//! logged and no thread is started, as in the OCaml.

use std::sync::LazyLock;
use std::sync::Mutex;

use crate::c_group;
use crate::hh_logger;
use crate::rt::ocaml_unix::gettimeofday;
use crate::telemetry;

/// `initial_reading`: the cgroup name, and what initial values it had upon
/// process startup. (The OCaml pairs it with
/// `Hack_event_logger.ProfileTypeCheck.stats`, which are `()` in the
/// open-source build.)
pub type InitialReading = Result<c_group::Stats, String>;

/// `initial_reading_capture`: the [`InitialReading`] that we capture upon
/// module load, i.e. process startup (here: on first use, which
/// `Monitor_start.start` makes at once).
static INITIAL_READING_CAPTURE: LazyLock<InitialReading> = LazyLock::new(c_group::get_stats);

/// `initial_reading`: the [`InitialReading`] that we'll actually use, i.e.
/// we'll record data relative to this. None means we won't use anything.
static INITIAL_READING: Mutex<Option<InitialReading>> = Mutex::new(None);

/// `get_initial_reading ()`: upon module load, this module takes an
/// [`InitialReading`] and stores it in mutable state. This function lets us
/// retrieve it. Except: if someone has subsequently called
/// [`use_initial_reading`], then the captured value will be irretrievable,
/// and we'll return the [`use_initial_reading`] instead.
pub fn get_initial_reading() -> InitialReading {
    match &*INITIAL_READING.lock().unwrap_or_else(|e| e.into_inner()) {
        None => INITIAL_READING_CAPTURE.clone(),
        Some(initial_reading) => initial_reading.clone(),
    }
}

/// `use_initial_reading new_initial_reading`: this module doesn't actually
/// respect the [`InitialReading`] it took upon program startup; it only uses
/// a reading that was passed to it by this function. Why? imagine if after
/// some heavy allocation, server_main used Daemon.spawn to spawn a child
/// process; we'd usually prefer that child process to record numbers
/// relative to the intial_reading that was captured by the initial process
/// upon its initial startup, not the one captured by the child upon child
/// process startup.
pub fn use_initial_reading(new_initial_reading: InitialReading) {
    *INITIAL_READING.lock().unwrap_or_else(|e| e.into_inner()) = Some(new_initial_reading);
}

/// `initial_value_map current_cgroup ~f ~default`: a small helper: returns
/// either (initial_reading, f initial_reading) if (1) someone has previously
/// called [`use_initial_reading`] and provided an Ok one, (2) the
/// `current_cgroup` parameter is Ok, (3) the `current_cgroup` has the same
/// cgroup name as the initial one. Otherwise, it returns ({0...}, default).
fn initial_value_map<T>(
    initial_reading: &Option<InitialReading>,
    current_cgroup: &Result<c_group::Stats, String>,
    f: impl FnOnce(&c_group::Stats) -> T,
    default: T,
) -> (c_group::Stats, T) {
    match (initial_reading, current_cgroup) {
        (Some(Ok(initial_cgroup)), Ok(current_cgroup))
            if initial_cgroup.cgroup_name == current_cgroup.cgroup_name =>
        {
            let value = f(initial_cgroup);
            (initial_cgroup.clone(), value)
        }
        _ => (c_group::Stats::default(), default),
    }
}

/// `!initial_reading`
fn initial_reading() -> Option<InitialReading> {
    INITIAL_READING.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

/// `step_summary`
#[derive(Clone, Debug)]
struct StepSummary {
    time: f64,
    log_label_and_suffix: String,
    step_total: i64,
}

/// `step_group`: represents a step-group that's underway; created by
/// [`step_group`].
pub struct StepGroup {
    /// e.g. "lazy_init"
    name: String,
    /// should it be logged to Hh_logger?
    log: bool,
    state: Mutex<StepGroupState>,
}

/// The mutable fields of a [`StepGroup`].
#[derive(Default)]
struct StepGroupState {
    /// used to prefix the step-names for telemetry+logging
    step_count: usize,
    /// we only print to Hh_logger if it's markedly changed since last we
    /// printed.
    last_printed_total: i64,
    /// in case we print, we might want to include something about the
    /// previous one, if it hasn't already been printed
    prev_step_to_show: Option<StepSummary>,
}

impl StepGroup {
    fn state(&self) -> std::sync::MutexGuard<'_, StepGroupState> {
        self.state.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// `step_group.step_count := !(step_group.step_count) + 1`, and the
    /// step's name with it (`"%02d_%s"`).
    fn next_step(&self, name: &str) -> String {
        let mut state = self.state();
        state.step_count += 1;
        format!("{:02}_{}", state.step_count, name)
    }
}

/// We'll only bother writing to the log if the total has changed by at least
/// this many bytes
const THRESHOLD_FOR_LOGGING: i64 = 100 * 1024 * 1024;

/// `pretty_num i`: prints bytes in gb
fn pretty_num(i: i64) -> String {
    format!("{}GiB", crate::rt::ocaml_printf::sprintf_f(2, i as f64 / 1073741824.0))
}

/// `log_cgroup_total cgroup ~step_group ~step ~suffix ~total_hwm`: records
/// to Hh_logger if it differs from the previous total, and update total
fn log_cgroup_total(
    cgroup: &Result<c_group::Stats, String>,
    step_group: &StepGroup,
    step: &str,
    suffix: &str,
    total_hwm: i64,
) {
    if let Some(message) = cgroup_total_message(
        &initial_reading(),
        cgroup,
        step_group,
        step,
        suffix,
        total_hwm,
        gettimeofday(),
    ) {
        hh_logger::log(&message)
    }
}

/// What [`log_cgroup_total`] logs, if anything, with the readings and the
/// time given (the state of `step_group` is updated as the OCaml's).
fn cgroup_total_message(
    initial_reading: &Option<InitialReading>,
    cgroup: &Result<c_group::Stats, String>,
    step_group: &StepGroup,
    step: &str,
    suffix: &str,
    total_hwm: i64,
    now: f64,
) -> Option<String> {
    let (initial, initial_msg) = initial_value_map(
        initial_reading,
        cgroup,
        |i| format!(" (relative to initial {})", pretty_num(i.total)),
        String::new(),
    );
    let cgroup = cgroup.as_ref().ok()?;
    let log_label_and_suffix = format!("{}/{}{}", step_group.name, step, suffix);
    let mut state = step_group.state();
    let prev = state.prev_step_to_show.clone();
    let current = StepSummary {
        time: now,
        log_label_and_suffix,
        step_total: cgroup.total,
    };
    if (cgroup.total - state.last_printed_total).abs() < THRESHOLD_FOR_LOGGING {
        // We didn't print this current step. But if the *next* step proves
        // to have a big increase in memory, then when we print the next
        // step, we'll also print this one.
        state.prev_step_to_show = Some(current);
        None
    } else {
        // This step is being shown right now. So if the next step proves to
        // have a big increase in memory, we won't need to show this one
        // again!
        state.prev_step_to_show = None;
        state.last_printed_total = cgroup.total;
        let hwm = if cgroup.total >= total_hwm {
            String::new()
        } else {
            format!(" (hwm {})", pretty_num(total_hwm - initial.total))
        };
        let prev = match prev {
            None => String::new(),
            Some(prev) => format!(
                "\n   >{} {}  [@{}]  previous measurement",
                crate::utils::timestring(prev.time),
                pretty_num(prev.step_total - initial.total),
                prev.log_label_and_suffix
            ),
        };
        Some(format!(
            "Cgroup: {}{}  [@{}]{}{}",
            pretty_num(cgroup.total - initial.total),
            hwm,
            current.log_label_and_suffix,
            initial_msg,
            prev
        ))
    }
}

/// `secs_above_gb_summary secs_at_gb`: given a float array `secs_at_gb`
/// where secs_at_gb[0] says how many secs were spent at cgroup memory 0gb,
/// secs_at_gb[1] says how many secs were spent at cgroup memory 1gb, and so
/// on, produces an S_map where keys are some arbitrary thresholds
/// "secs_above_20gb" and values are (int) number of seconds spent at that
/// memory or higher. We pick just a few arbitrary thresholds that we think
/// are useful for telemetry, and their sole purpose is telemetry.
fn secs_above_gb_summary(secs_at_gb: &[f64]) -> std::collections::BTreeMap<String, isize> {
    if secs_at_gb.is_empty() {
        return Default::default();
    }
    // 0gb, 5gb, ..., 70gb
    (0..15)
        .map(|i| i * 5)
        .filter_map(|threshold| {
            let title = format!("secs_above_{:02}gb", threshold);
            let secs: f64 = secs_at_gb
                .iter()
                .enumerate()
                .fold(0., |acc, (i, s)| acc + if i < threshold { 0. } else { *s });
            // `Float.round` (ties up; the seconds are not negative, so the same).
            let secs = secs.round() as isize;
            (secs > 0).then_some((title, secs))
        })
        .collect()
}

/// `log_telemetry ~step_group ~step ~start_time ~total_hwm ~start_cgroup
/// ~cgroup ~telemetry_ref ~secs_at_total_gb`: records to HackEventLogger
/// (`Hack_event_logger.CGroup.error` and `.step` are no-ops in the
/// open-source build, so `has_logged_error`, which only spares the logger
/// repeated errors, has no counterpart), and to `telemetry_ref`.
fn log_telemetry(
    total_hwm: i64,
    start_cgroup: Option<&Result<c_group::Stats, String>>,
    cgroup: &Result<c_group::Stats, String>,
    telemetry_ref: Option<&mut Option<telemetry::T>>,
    secs_at_total_gb: &[f64],
) {
    let Some(telemetry_ref) = telemetry_ref else {
        return;
    };
    let (initial, initial_opt) = initial_value_map(&initial_reading(), cgroup, |_| true, false);
    let some_if = |b: bool, v: i64| b.then_some(v as isize);
    match (start_cgroup, cgroup) {
        (Some(Err(e)), _) | (_, Err(e)) => {
            *telemetry_ref = Some(telemetry::error(e, telemetry::create()));
        }
        (Some(Ok(start_cgroup)), Ok(cgroup)) => {
            let total_hwm = start_cgroup.total.max(cgroup.total).max(total_hwm);
            let secs_above_total_gb_summary = secs_above_gb_summary(secs_at_total_gb);
            let sysinfo = crate::sys_utils::sysinfo();
            let mut t = telemetry::create();
            for (key, value) in &secs_above_total_gb_summary {
                t = telemetry::int_(key, *value, t);
            }
            let t = telemetry::int_("start_bytes", (start_cgroup.total - initial.total) as isize, t);
            let t = telemetry::int_("end_bytes", (cgroup.total - initial.total) as isize, t);
            let t = telemetry::int_("hwm_bytes", (total_hwm - initial.total) as isize, t);
            let t = telemetry::int_opt("relative_to_initial", some_if(initial_opt, initial.total), t);
            let t = telemetry::int_opt("sysinfo_freeram", sysinfo.map(|si| si.freeram), t);
            let t = telemetry::int_opt("sysinfo_freeswap", sysinfo.map(|si| si.freeswap), t);
            let t = telemetry::int_opt("sysinfo_totalswap", sysinfo.map(|si| si.totalswap), t);
            *telemetry_ref = Some(t);
        }
        (None, Ok(cgroup)) => {
            *telemetry_ref = Some(telemetry::int_("end", cgroup.total as isize, telemetry::create()));
        }
    }
}

/// `step_group name ~log f`: indicates that group `name` will span all the
/// steps created within callback. If `log` is true then each step will be
/// logged to Hh_logger and HackEventLogger.
pub fn step_group<R>(name: &str, log: bool, f: impl FnOnce(&StepGroup) -> R) -> R {
    let profiling = StepGroup {
        name: name.to_string(),
        log,
        state: Mutex::new(StepGroupState::default()),
    };
    f(&profiling)
}

/// `step step_group ?telemetry_ref name`: record cgroup stats at a point in
/// time. Write to logs and to telemetry.
pub fn step(step_group: &StepGroup, telemetry_ref: Option<&mut Option<telemetry::T>>, name: &str) {
    if !step_group.log {
        return;
    }
    let step = step_group.next_step(name);
    let cgroup = c_group::get_stats();
    log_cgroup_total(&cgroup, step_group, &step, "", 0);
    log_telemetry(0, None, &cgroup, telemetry_ref, &[]);
}

/// `step_start_end phase ?telemetry_ref name f`: records cgroup stats
/// immediately, then executes the callback, then records cgroup a second
/// time. Write to logs and telemetry.
pub fn step_start_end<R>(
    step_group: &StepGroup,
    telemetry_ref: Option<&mut Option<telemetry::T>>,
    name: &str,
    f: impl FnOnce() -> R,
) -> R {
    if !step_group.log {
        return f();
    }
    let step = step_group.next_step(name);
    let start_cgroup = c_group::get_stats();
    log_cgroup_total(&start_cgroup, step_group, &step, " start", 0);
    let (initial, ()) = initial_value_map(&initial_reading(), &start_cgroup, |_| (), ());
    if let Ok(c_group::Stats { cgroup_name, .. }) = &start_cgroup {
        let path1 = format!("{}/{}/memory.current", c_group::CGROUP_DIR, cgroup_name);
        let path2 = format!("{}/{}/memory.swap.current", c_group::CGROUP_DIR, cgroup_name);
        cgroup_watcher_start(path1, path2, initial.total / 1024);
    }
    // `Utils.try_finally ~f ~finally`: the end is recorded when `f` returns
    // or unwinds. (The OCaml catches an exception of the recording and logs
    // "cgroup - failed to log."; nothing here raises.)
    struct Finally<'a> {
        step_group: &'a StepGroup,
        step: String,
        start_cgroup: Result<c_group::Stats, String>,
        telemetry_ref: Option<&'a mut Option<telemetry::T>>,
    }
    impl Drop for Finally<'_> {
        fn drop(&mut self) {
            let cgroup = c_group::get_stats();
            let (hwm_kb, _num_readings, secs_at_total_gb) = cgroup_watcher_get();
            let total_hwm = hwm_kb * 1024;
            log_cgroup_total(&cgroup, self.step_group, &self.step, " end", total_hwm);
            log_telemetry(
                total_hwm,
                Some(&self.start_cgroup),
                &cgroup,
                self.telemetry_ref.take(),
                &secs_at_total_gb,
            );
        }
    }
    let _finally = Finally {
        step_group,
        step,
        start_cgroup,
        telemetry_ref,
    };
    f()
}

// ~~ cgroupWatcher.c ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Highest expected peak cgroup memory. We only write to scuba as many
/// entries as there actually are, so it's fine for this to be large. If it
/// were too small then we'd "clip", i.e, anything bigger than GB_MAX would
/// be ascribed to GB_MAX.
const GB_MAX: usize = 1024;

/// We'll have a background thread which reads cgroup this frequently. I
/// don't know if there'll be adverse perf impact of having it more frequent.
/// If it's too infrequent, then we'll fail to capture short-lived peaks.
const INTERVAL_MS: u64 = 20;

/// The static data of `cgroupWatcher.c`, which its lock protects.
struct Watcher {
    /// Accumulates how many seconds have been spent at each total cgroup
    /// size. This is reset by [`cgroup_watcher_start`], and read by
    /// [`cgroup_watcher_get`]. The final entry in the array accumulates time
    /// spent at GB_MAX or higher.
    seconds_at_gb: [f64; GB_MAX],
    /// Records the high-water-mark
    hwm_kb: i64,
    /// How many cgroup readings have we taken since the last reset
    num_readings: i64,
    /// These are the cgroup memory.current and memory.swap.current file
    /// we'll read for the current value. We'll add them together. The paths
    /// include the leading "/sys/fs/group/" and the trailing
    /// "/memory.current"
    path1: Option<String>,
    path2: Option<String>,
    /// The seconds_at_gb array will be relative to this, e.g. a reading of
    /// Xgb would increment the tally kept at
    /// seconds_at_gb[X-subtract_kb_for_array/1GiB].
    subtract_kb_for_array: i64,
    /// Whether the thread has been launched
    thread_is_running: bool,
}

static WATCHER: Mutex<Watcher> = Mutex::new(Watcher {
    seconds_at_gb: [0.0; GB_MAX],
    hwm_kb: 0,
    num_readings: 0,
    path1: None,
    path2: None,
    subtract_kb_for_array: 0,
    thread_is_running: false,
});

/// `fscanf(file, "%llu", ..)` of the file at `path`.
fn read_llu(path: &str) -> Result<Option<u64>, ()> {
    let contents = std::fs::read(path).map_err(|_| ())?;
    let s = String::from_utf8_lossy(&contents);
    let digits: String = s.trim_start().chars().take_while(char::is_ascii_digit).collect();
    Ok(digits.parse().ok())
}

/// `get_mem_kb ()`: reads the current unsigned long long from the contents
/// of 'path1+path2', and returns it /1024. If it fails to open the file, -1.
/// If it fails to parse the contents, -2.
fn get_mem_kb(path1: &str, path2: &str) -> i64 {
    match (read_llu(path1), read_llu(path2)) {
        (Ok(Some(mem1)), Ok(Some(mem2))) => ((mem1 + mem2) / 1024) as i64,
        (Ok(_), Ok(_)) => -2,
        _ => -1,
    }
}

impl Watcher {
    /// One reading of `threadfunc`, `seconds` after the previous one:
    /// updates the counters [hwm_kb, seconds_at_gb, num_readings]. If there
    /// are any errors, then the counters simply won't be updated.
    fn tick(&mut self, seconds: f64) {
        let (Some(path1), Some(path2)) = (&self.path1, &self.path2) else {
            return;
        };
        let mut kb = get_mem_kb(path1, path2);
        if kb >= 0 {
            self.hwm_kb = self.hwm_kb.max(kb);
            kb -= self.subtract_kb_for_array;
            if kb < 0 {
                // Underflow, because the value dropped below what it was
                // initially. We'll "clip" it, tallying it under
                // seconds_at_gb[0]
                kb = 0;
            }
            let mut gb = (kb / 1024 / 1024) as usize;
            if gb >= GB_MAX {
                // Overflow, because the value was higher than we ever
                // dreamt. We'll "clip" it, tallying it under
                // seconds_at_gb[GB_MAX-1]
                gb = GB_MAX - 1;
            }
            self.seconds_at_gb[gb] += seconds;
            self.num_readings += 1;
        }
    }

    /// The reset of [`cgroup_watcher_start`].
    fn reset(&mut self, path1: String, path2: String, subtract_kb_for_array: i64) {
        self.path1 = Some(path1);
        self.path2 = Some(path2);
        self.subtract_kb_for_array = subtract_kb_for_array;
        self.hwm_kb = 0;
        self.num_readings = 0;
        self.seconds_at_gb = [0.0; GB_MAX];
    }

    /// What [`cgroup_watcher_get`] returns.
    fn get(&self) -> (i64, i64, Vec<f64>) {
        let max = self
            .seconds_at_gb
            .iter()
            .rposition(|s| *s > 0.0)
            .map_or(0, |i| i + 1);
        (self.hwm_kb, self.num_readings, self.seconds_at_gb[..max].to_vec())
    }
}

/// `threadfunc`: the background thread. Every INTERVAL_MS, it reads the
/// cgroup memory.current from [path], and updates the counters.
fn threadfunc() {
    let mut tprev = std::time::Instant::now();
    loop {
        {
            let mut watcher = WATCHER.lock().unwrap_or_else(|e| e.into_inner());
            let t = std::time::Instant::now();
            let seconds = t.duration_since(tprev).as_secs_f64();
            tprev = t;
            watcher.tick(seconds);
        }
        std::thread::sleep(std::time::Duration::from_millis(INTERVAL_MS));
    }
}

/// `cgroup_watcher_start filename subtract_kb_for_array` will reset
/// cgroup_watcher counters, and have it start monitoring the two filenames
/// (e.g. "/sys/fs/.../memory.current" and ".../memory.swap.current") and
/// adds them together. See [`cgroup_watcher_get`] for the meaning of
/// `subtract_kb_for_array`. The thread is started if it's not already
/// running. Any failures aren't reported here; they're manifest in
/// [`cgroup_watcher_get`].
fn cgroup_watcher_start(path1: String, path2: String, subtract_kb_for_array: i64) {
    let mut watcher = WATCHER.lock().unwrap_or_else(|e| e.into_inner());
    watcher.reset(path1, path2, subtract_kb_for_array);
    if !watcher.thread_is_running {
        let started = std::thread::Builder::new()
            .name("cgroup_watcher".to_string())
            .spawn(threadfunc);
        watcher.thread_is_running = started.is_ok();
    }
}

/// `cgroup_watcher_get ()`: this returns (hwm_kb, num_readings,
/// seconds_at_gb[||]) that have been tallied since [`cgroup_watcher_start`].
/// Hwm_kb is the high water mark of the cgroup. Num_readings is the number
/// of readings that succeeded. The meaning of seconds_at_gb.(i) is that we
/// spent this many seconds with the value between (subtract_kb_for_array+i)
/// and (subtract_kb_for_array+i+1) gb. If there had been failures along the
/// way, e.g. the path was invalid or cgroups don't exist, then it will
/// return (0,0,[||]).
fn cgroup_watcher_get() -> (i64, i64, Vec<f64>) {
    WATCHER.lock().unwrap_or_else(|e| e.into_inner()).get()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c_group::tests::ScratchDir;
    use crate::c_group::tests::write_cgroup;

    const GIB: f64 = 1073741824.0;

    /// The bytes that `pretty_num` prints as `gib` (rounded down).
    fn bytes(gib: f64) -> i64 {
        (gib * GIB) as i64
    }

    fn stat() -> String {
        "anon 1\nfile 2\nshmem 1\n".to_string()
    }

    /// The reading of a fixture cgroup directory with this `memory.current`.
    fn reading(dir: &ScratchDir, name: &str, memory_current: i64) -> Result<c_group::Stats, String> {
        write_cgroup(dir.path(), name, Some(&format!("{}\n", memory_current)), Some("0\n"), Some(&stat()));
        c_group::get_stats_for_cgroup_in(dir.path(), name)
    }

    #[test]
    fn pretty_num_is_the_ocaml_s() {
        assert_eq!(pretty_num(0), "0.00GiB");
        assert_eq!(pretty_num(bytes(16.70)), "16.70GiB");
        assert_eq!(pretty_num(bytes(1.77) + 1), "1.77GiB");
        // `%0.2f` of C: an exact half is rounded to even.
        assert_eq!(pretty_num((0.125 * GIB) as i64), "0.12GiB");
        assert_eq!(pretty_num(-bytes(0.5)), "-0.50GiB");
    }

    /// The lines of the OCaml's full init in a CI job, from the readings of a
    /// fixture directory.
    #[test]
    fn the_full_init_s_lines() {
        let dir = ScratchDir::new("profiler");
        let initial = bytes(0.02) + 1;
        let initial_reading = Some(reading(&dir, "/job", initial));
        let group = StepGroup {
            name: "full_init".to_string(),
            log: true,
            state: Default::default(),
        };
        let message = |memory_current: i64, step: &str, suffix: &str, total_hwm: i64, now: f64| {
            cgroup_total_message(
                &initial_reading,
                &reading(&dir, "/job", memory_current),
                &group,
                step,
                suffix,
                total_hwm,
                now,
            )
        };
        assert_eq!(
            message(initial + bytes(1.01) + 1, "01_lazy.nt.parsing", " start", 0, 1.0).as_deref(),
            Some("Cgroup: 1.01GiB  [@full_init/01_lazy.nt.parsing start] (relative to initial 0.02GiB)")
        );
        assert_eq!(
            message(
                initial + bytes(1.77) + 1,
                "01_lazy.nt.parsing",
                " end",
                initial + bytes(2.66) + 1,
                2.0
            )
            .as_deref(),
            Some("Cgroup: 1.77GiB (hwm 2.66GiB)  [@full_init/01_lazy.nt.parsing end] (relative to initial 0.02GiB)")
        );
        // Less than 100 MiB from the last line: not logged, but kept.
        assert_eq!(message(initial + bytes(1.80), "02_lazy.nt.do_naming.naming", " start", 0, 3.0), None);
        assert_eq!(message(initial + bytes(1.75), "02_lazy.nt.do_naming.naming", " end", 0, 4.0), None);
        let start_time = 1763130000.25;
        assert_eq!(
            message(initial + bytes(1.74) + 1, "03_lazy.full.type_check", " start", 0, start_time),
            None
        );
        // The hwm is not printed when the reading is the highest.
        let line = message(
            initial + bytes(2.97) + 1,
            "03_lazy.full.type_check",
            " end",
            initial + bytes(16.70) + 1,
            start_time + 110.0,
        )
        .unwrap();
        assert_eq!(
            line,
            format!(
                "Cgroup: 2.97GiB (hwm 16.70GiB)  [@full_init/03_lazy.full.type_check end] (relative to initial 0.02GiB)\n   >{} 1.74GiB  [@full_init/03_lazy.full.type_check start]  previous measurement",
                crate::utils::timestring(start_time)
            )
        );
        assert!(crate::utils::timestring(start_time).ends_with(".250]"));
        assert_eq!(
            message(initial + bytes(3.5), "04_x", "", initial + bytes(3.0), 5.0).as_deref(),
            Some("Cgroup: 3.50GiB  [@full_init/04_x] (relative to initial 0.02GiB)")
        );
    }

    #[test]
    fn without_an_initial_reading_of_the_same_cgroup() {
        let dir = ScratchDir::new("profiler_other");
        let group = StepGroup {
            name: "Full_check".to_string(),
            log: true,
            state: Default::default(),
        };
        let other = Some(reading(&dir, "/other", bytes(1.0)));
        let current = reading(&dir, "/job", bytes(2.0));
        assert_eq!(
            cgroup_total_message(&other, &current, &group, "01_parsing", " start", 0, 1.0).as_deref(),
            Some("Cgroup: 2.00GiB  [@Full_check/01_parsing start]")
        );
        assert_eq!(
            cgroup_total_message(&None, &Err("no".to_string()), &group, "01_parsing", " end", 0, 1.0),
            None
        );
    }

    #[test]
    fn steps_without_cgroups_log_nothing_and_run_the_callback() {
        if std::path::Path::new(c_group::CGROUP_DIR).exists() {
            return;
        }
        let r = step_group("full_init", true, |group| {
            let mut telemetry = None;
            let r = step_start_end(group, Some(&mut telemetry), "lazy.nt.parsing", || 42);
            assert_eq!(
                telemetry.map(|t| telemetry::to_string(None, &t)).as_deref(),
                Some(r#"{"error":{"message":"/sys/fs/cgroup doesn't exist"}}"#)
            );
            step(group, None, "x");
            assert_eq!(group.state().step_count, 2);
            r
        });
        assert_eq!(r, 42);
        assert!(!WATCHER.lock().unwrap().thread_is_running);
        step_group("off", false, |group| {
            assert_eq!(step_start_end(group, None, "a", || 1), 1);
            assert_eq!(group.state().step_count, 0);
        });
    }

    #[test]
    fn the_watcher_tallies_the_readings() {
        let dir = ScratchDir::new("watcher");
        let p1 = dir.path().join("memory.current");
        let p2 = dir.path().join("memory.swap.current");
        let mut w = Watcher {
            seconds_at_gb: [0.0; GB_MAX],
            hwm_kb: 0,
            num_readings: 0,
            path1: None,
            path2: None,
            subtract_kb_for_array: 0,
            thread_is_running: false,
        };
        let (s1, s2) = (p1.display().to_string(), p2.display().to_string());
        assert_eq!(get_mem_kb(&s1, &s2), -1);
        w.reset(s1.clone(), s2.clone(), 1024 * 1024);
        w.tick(1.0);
        assert_eq!(w.get(), (0, 0, vec![]));
        std::fs::write(&p1, "x\n").unwrap();
        std::fs::write(&p2, "0\n").unwrap();
        assert_eq!(get_mem_kb(&s1, &s2), -2);
        std::fs::write(&p1, "3221225472\n").unwrap();
        std::fs::write(&p2, "1024\n").unwrap();
        w.tick(0.5);
        std::fs::write(&p1, "1048576\n").unwrap();
        w.tick(0.25);
        // 3 GiB + 1 KiB less the 1 GiB subtracted, then a clipped reading.
        assert_eq!(w.get(), (3 * 1024 * 1024 + 1, 2, vec![0.25, 0.0, 0.5]));
        assert_eq!(
            secs_above_gb_summary(&[0.25, 0.0, 0.5, 3.0, 0.0, 2.6]),
            [("secs_above_00gb".to_string(), 6), ("secs_above_05gb".to_string(), 3)]
                .into_iter()
                .collect()
        );
        assert!(secs_above_gb_summary(&[]).is_empty());
    }
}
