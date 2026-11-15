// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use super::*;

/// The shared heap of the test process (made once; the tests use keys of
/// their own).
pub(crate) fn init_for_tests() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        if !is_initialized() {
            let mut config = crate::shared_mem::default_config();
            config.heap_size = 1 << 30;
            config.hash_table_pow = 16;
            init(&config, 0).unwrap();
        }
    });
}

/// `collect` moves every entry: the tests that remove or add while it runs
/// take this first (`Shared_mem.GC.collect` runs when the workers are idle).
static COLLECT: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[test]
fn add_get_remove() {
    init_for_tests();
    let k = hash_key(b"test-add-get-remove:", b"a");
    assert!(!mem_(k));
    let data = vec![7u8; 10_000];
    let added = add(k, &data, Kind::Serialized).unwrap();
    // Compressible: stored compressed.
    assert!(added.compressed_size < added.original_size);
    assert_eq!(added.original_size, 10_000);
    assert!(mem_(k));
    assert_eq!(get(k, |b, _| b.to_vec()).unwrap(), data);
    // The first writer wins.
    assert!(add(k, b"other", Kind::Serialized).is_none());
    assert_eq!(get(k, |b, _| b.len()).unwrap(), 10_000);
    let k2 = hash_key(b"test-add-get-remove:", b"b");
    add(k2, b"xy", Kind::String).unwrap();
    assert_eq!(get(k2, |b, kind| (b.to_vec(), kind)).unwrap(), (b"xy".to_vec(), Kind::String));
    remove(k);
    assert!(!mem_(k));
    assert!(get(k, |_, _| ()).is_none());
    // A removed key can be added again.
    add(k, b"again", Kind::Serialized).unwrap();
    assert_eq!(get(k, |b, _| b.to_vec()).unwrap(), b"again");
    let old = hash_key(b"old_test-add-get-remove:", b"a");
    move_(k, old);
    assert!(!mem_(k));
    assert_eq!(get(old, |b, _| b.to_vec()).unwrap(), b"again");
}

#[test]
fn collect_compacts() {
    // (Alone in its own heap would be better; the other tests only add keys
    // of their own, and nothing removes theirs while this runs but this.)
    let _serial = COLLECT.lock().unwrap_or_else(|e| e.into_inner());
    init_for_tests();
    let keys: Vec<u64> = (0..200).map(|i| hash_key(b"test-collect:", format!("{i}").as_bytes())).collect();
    for (i, k) in keys.iter().enumerate() {
        add(*k, format!("value {i} {}", "x".repeat(i)).as_bytes(), Kind::Serialized);
    }
    for k in keys.iter().step_by(2) {
        remove(*k);
    }
    assert!(wasted_heap_size() > 0);
    let before = used_heap_size();
    collect();
    assert!(used_heap_size() < before);
    assert_eq!(wasted_heap_size(), 0);
    for (i, k) in keys.iter().enumerate() {
        let v = get(*k, |b, _| String::from_utf8(b.to_vec()).unwrap());
        if i % 2 == 0 {
            assert!(v.is_none());
        } else {
            assert_eq!(v.unwrap(), format!("value {i} {}", "x".repeat(i)));
        }
    }
}

/// Threads of the master replacing the same key at once (two folds of a
/// class, `ctx::DeclMap::insert`): one of them removes each value, none
/// panics, and the key ends with a value.
#[test]
fn concurrent_replace_in_the_master() {
    let _serial = COLLECT.lock().unwrap_or_else(|e| e.into_inner());
    init_for_tests();
    let k = hash_key(b"test-concurrent-replace:", b"a");
    std::thread::scope(|scope| {
        for t in 0..8u8 {
            scope.spawn(move || {
                for _ in 0..2_000 {
                    if mem_(k) {
                        remove_if_present(k);
                    }
                    add(k, &[t; 64], Kind::Serialized);
                }
            });
        }
    });
    if !mem_(k) {
        add(k, b"last", Kind::Serialized);
    }
    assert!(get(k, |b, _| b.len()).is_some());
    assert!(remove_if_present(k).is_some());
    assert!(remove_if_present(k).is_none());
}
