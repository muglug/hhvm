// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/memory_stats.ml`: the readers of `/proc` that the port
//! uses. See `hh/PORTING.md`.

/// `colon_file_to_pairs ~fn`: some interesting files are made of lines like
/// "a  : b". This function reads the file and splits it into [(a,b),...] pairs.
fn colon_file_to_pairs(path: &str) -> Vec<(String, String)> {
    match std::fs::read_to_string(path) {
        Err(_) => vec![],
        Ok(text) => text
            .split('\n')
            .filter_map(|line| {
                let mut parts = line.split(':').filter(|s| !s.is_empty());
                match (parts.next(), parts.next(), parts.next()) {
                    (Some(k), Some(v), None) => Some((k.trim().to_string(), v.trim().to_string())),
                    _ => None,
                }
            })
            .collect(),
    }
}

/// Convert the human-readable format of /proc/[pid]/status back to bytes
/// Because the machine-readable /proc/[pid]/stat,statm files do not have the
/// VmHWM we need
fn to_bytes_opt(s: &str) -> Option<isize> {
    let parts: Vec<&str> = s.split(' ').filter(|s| !s.is_empty()).collect();
    match parts.as_slice() {
        [amount, "kB"] => Some(amount.parse::<isize>().ok()? * 1024),
        _ => None,
    }
}

fn get_status_entry(status: &[(String, String)], key: &str) -> Option<isize> {
    status
        .iter()
        .find(|(k, _)| k == key)
        .and_then(|(_, v)| to_bytes_opt(v))
}

pub fn get_vm_rss() -> Option<isize> {
    get_status_entry(&colon_file_to_pairs("/proc/self/status"), "VmRSS")
}

pub fn get_vm_hwm() -> Option<isize> {
    get_status_entry(&colon_file_to_pairs("/proc/self/status"), "VmHWM")
}

/// Bytes of memory the machine could give a new process without swapping
/// (`MemAvailable`). [None] where the host does not say.
pub fn get_mem_available() -> Option<isize> {
    get_status_entry(&colon_file_to_pairs("/proc/meminfo"), "MemAvailable")
}

/// [get_mem_available_and_total ()] is [get_mem_available] and the machine's
/// total (`MemTotal`), read together.
pub fn get_mem_available_and_total() -> Option<(isize, isize)> {
    let pairs = colon_file_to_pairs("/proc/meminfo");
    match (
        get_status_entry(&pairs, "MemAvailable"),
        get_status_entry(&pairs, "MemTotal"),
    ) {
        (Some(available), Some(total)) => Some((available, total)),
        _ => None,
    }
}
