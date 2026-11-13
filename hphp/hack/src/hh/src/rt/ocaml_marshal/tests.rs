// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The fixtures are bytes written by OCaml 5:
//!
//! - `ocaml5_values.bin`: the values of `gen_ocaml5_values.ml` (compiled
//!   with OCaml 5.1.1's `ocamlopt`, run as `./gen ocaml5_values.bin`), one
//!   `Marshal.to_string` after the other.
//! - `*.errors.bin`: errors files written by the OCaml `hh_server` (the
//!   oracle build), on the tiny roots of the ERR notes: `r1` (errors and a
//!   warning, completed), `r2` (23 diagnostics in 15 files, a fixme,
//!   quickfixes), `r3_stopped` (read through a descriptor kept open while
//!   the server was stopped mid-check), `r4_restarted` (the first file of a
//!   check restarted by an interrupt) and `r4_second` (the file that
//!   replaced it).

use super::*;

const VALUES: &[u8] = include_bytes!("fixtures/ocaml5_values.bin");

pub(crate) const GOLDEN_ERRORS_FILES: &[(&str, &[u8])] = &[
    ("r1", include_bytes!("fixtures/r1.errors.bin")),
    ("r2", include_bytes!("fixtures/r2.errors.bin")),
    ("r3_stopped", include_bytes!("fixtures/r3_stopped.errors.bin")),
    ("r4_restarted", include_bytes!("fixtures/r4_restarted.errors.bin")),
    ("r4_second", include_bytes!("fixtures/r4_second.errors.bin")),
];

/// The marshalled payloads of an errors file (each after its 5-byte
/// preamble).
pub(crate) fn errors_file_payloads(file: &[u8]) -> Vec<&[u8]> {
    let mut out = vec![];
    let mut i = 0;
    while i < file.len() {
        assert_eq!(file[i], 0x8e);
        let size = u32::from_be_bytes(file[i + 1..i + 5].try_into().unwrap()) as usize;
        out.push(&file[i + 5..i + 5 + size]);
        i += 5 + size;
    }
    out
}

/// The values of a file of `Marshal.to_string` outputs.
fn values(file: &[u8]) -> Vec<&[u8]> {
    let mut out = vec![];
    let mut i = 0;
    while i < file.len() {
        let n = total_size(file, i).unwrap();
        out.push(&file[i..i + n]);
        i += n;
    }
    out
}

#[test]
fn ocaml_values_round_trip() {
    let vs = values(VALUES);
    assert_eq!(vs.len(), 281);
    for (i, bytes) in vs.iter().enumerate() {
        let v = from_bytes(bytes, 0).unwrap_or_else(|e| panic!("value {}: {}", i, e));
        // Value 117 was written with [No_sharing].
        let flags: &[ExternFlag] = if i == 117 { &[ExternFlag::NoSharing] } else { &[] };
        let again = to_bytes(&v, flags).unwrap();
        assert!(again == *bytes, "value {} differs: {:?}", i, v);
    }
}

#[test]
fn ocaml_values_decode() {
    let vs = values(VALUES);
    let v = |i: usize| from_bytes(vs[i], 0).unwrap();
    let ints: Vec<i64> = Vec::from_ocaml(&v(0)).unwrap();
    assert_eq!(
        ints,
        vec![
            0,
            1,
            63,
            64,
            -1,
            -64,
            -128,
            127,
            128,
            -129,
            255,
            256,
            32767,
            32768,
            -32768,
            -32769,
            (1 << 30) - 1,
            1 << 30,
            -(1 << 30),
            -(1 << 30) - 1,
            1 << 31,
            (1 << 62) - 1,
            -(1 << 62)
        ]
    );
    let strings: Vec<String> = Vec::from_ocaml(&v(1)).unwrap();
    assert_eq!(strings.len(), 300);
    assert!(strings.iter().enumerate().all(|(n, s)| s.len() == n));
    assert_eq!(String::from_ocaml(&v(2)).unwrap(), "y".repeat(300));
    let floats: Vec<f64> = Vec::from_ocaml(&v(3)).unwrap();
    assert_eq!(floats[2], 1.5);
    assert!(floats[3].is_nan());
    assert_eq!(floats[7], 5e-324);
    match &v(4) {
        Value::Ptr(o) => assert_eq!(**o, Obj::DoubleArray(vec![1., 2., 3.])),
        _ => panic!(),
    }
    // Sharing: [s; s; s] is one string, written once.
    let shared = v(113);
    let items = shared.list_items().unwrap();
    assert!(items[0].phys_equal(items[1]) && items[1].phys_equal(items[2]));
    // The same, written without sharing: three strings.
    let unshared = v(117);
    let items = unshared.list_items().unwrap();
    assert!(!items[0].phys_equal(items[1]));
    assert_eq!(items[0], items[1]);
    assert_eq!(to_bytes(&shared.unshare(), &[ExternFlag::NoSharing]).unwrap(), vs[117]);
    // A shared reference more than 65536 objects back (CODE_SHARED32).
    let far = v(115);
    let f = far.fields(0, 3).unwrap();
    assert!(f[0].phys_equal(&f[2]));
    // Polymorphic variants.
    let pv = v(118);
    let items = pv.list_items().unwrap();
    assert_eq!(items[0].as_int().unwrap(), hash_variant("Null"));
    for (i, name) in [(1, "Bool"), (2, "Int"), (3, "Intlit"), (4, "Float"), (5, "String"), (6, "Assoc"), (7, "List"), (8, "Tuple"), (9, "Variant")] {
        assert_eq!(items[i].fields(0, 2).unwrap()[0].as_int().unwrap(), hash_variant(name), "{}", name);
    }
    assert_eq!(hash_variant("Assoc"), 963043957);
    assert_eq!(hash_variant("Float"), 365180284);
    assert_eq!(hash_variant("String"), -976970511);
}

/// `Map.Make(Int)` and `Set.Make(String)` built by `add` in the order of a
/// key list, and a `filter` of the map: the same shapes, so the same bytes.
#[test]
fn ocaml_maps_and_sets() {
    let vs = values(VALUES);
    let cmp = |a: &i64, b: &i64| a.cmp(b);
    for o in 0..4 {
        let base = 119 + 3 * o;
        let int = |n: &i64| Value::int(*n);
        // (keys, m)
        let v = from_bytes(vs[base], 0).unwrap();
        let f = v.fields(0, 2).unwrap();
        let keys: Vec<i64> = Vec::from_ocaml(&f[0]).unwrap();
        let m = ocaml_map::of_iter(keys.iter().map(|k| (*k, k * 2)), &cmp);
        let built = Value::block(0, vec![f[0].clone(), ocaml_map::to_ocaml(&m, &mut |k| int(k), &mut |d| int(d))]);
        assert!(to_bytes(&built, &[]).unwrap() == vs[base], "map {}", o);
        let bindings: Vec<(i64, i64)> = ocaml_map::bindings_of_ocaml(&f[1])
            .unwrap()
            .into_iter()
            .map(|(k, d)| (k.as_int().unwrap(), d.as_int().unwrap()))
            .collect();
        assert_eq!(bindings, ocaml_map::bindings(&m));
        // (keys, filter (fun k _ -> k mod 3 <> 0) m)
        let filtered = ocaml_map::filter(&mut |k: &i64, _| k % 3 != 0, &m);
        let v = from_bytes(vs[base + 1], 0).unwrap();
        let f = v.fields(0, 2).unwrap();
        let built = Value::block(0, vec![f[0].clone(), ocaml_map::to_ocaml(&filtered, &mut |k| int(k), &mut |d| int(d))]);
        assert!(to_bytes(&built, &[]).unwrap() == vs[base + 1], "filtered map {}", o);
        // (keys, set of string_of_int keys)
        let v = from_bytes(vs[base + 2], 0).unwrap();
        let f = v.fields(0, 2).unwrap();
        let s = ocaml_set::of_iter(keys.iter().map(|k| k.to_string()), &|a: &String, b: &String| a.as_bytes().cmp(b.as_bytes()));
        let built = Value::block(0, vec![f[0].clone(), ocaml_set::to_ocaml(&s, &mut |k| k.to_ocaml())]);
        assert!(to_bytes(&built, &[]).unwrap() == vs[base + 2], "set {}", o);
        let elements: Vec<String> = ocaml_set::elements_of_ocaml(&f[1])
            .unwrap()
            .into_iter()
            .map(|e| String::from_ocaml(e).unwrap())
            .collect();
        let mut sorted: Vec<String> = keys.iter().map(|k| k.to_string()).collect();
        sorted.sort();
        sorted.dedup();
        assert_eq!(elements, sorted);
    }
}

/// Every message of the errors files written by the OCaml server decodes,
/// and encodes back to the same bytes (shared references included).
#[test]
fn golden_errors_files_round_trip() {
    for (name, file) in GOLDEN_ERRORS_FILES {
        for (i, m) in errors_file_payloads(file).into_iter().enumerate() {
            let v = from_bytes(m, 0).unwrap_or_else(|e| panic!("{} message {}: {}", name, i, e));
            assert!(to_bytes(&v, &[]).unwrap() == m, "{} message {}", name, i);
        }
    }
}

/// A small deterministic generator (no external crate).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn random_value(rng: &mut Rng, pool: &mut Vec<Value>, depth: usize) -> Value {
    let r = rng.below(100);
    if r < 15 && !pool.is_empty() {
        return pool[rng.below(pool.len() as u64) as usize].clone();
    }
    let v = if depth > 4 || r < 40 {
        match rng.below(8) {
            0 => Value::int(rng.below(64) as i64),
            1 => Value::int(rng.next() as i64 >> 1),
            2 => Value::int(rng.below(1 << 20) as i64 - (1 << 19)),
            3 => Value::string(vec![b'z'; rng.below(300) as usize]),
            4 => Value::double(rng.next() as f64 / 7.0),
            5 => Value::Ptr(Rc::new(Obj::DoubleArray(
                (0..rng.below(5) + 1).map(|i| i as f64).collect(),
            ))),
            6 => Value::block(rng.below(250) as u8, vec![]),
            _ => Value::string(vec![]),
        }
    } else {
        let size = rng.below(12) as usize + 1;
        let tag = if rng.below(4) == 0 { rng.below(250) as u8 } else { rng.below(3) as u8 };
        let fields = (0..size).map(|_| random_value(rng, pool, depth + 1)).collect();
        Value::block(tag, fields)
    };
    pool.push(v.clone());
    v
}

/// Random values with sharing: decoding what is encoded gives an equal
/// value with the same sharing (so the same bytes again); without sharing,
/// the decoded value shares nothing.
#[test]
fn random_values_round_trip() {
    let mut rng = Rng(0x9E3779B97F4A7C15);
    for _ in 0..500 {
        let mut pool = vec![];
        let v = random_value(&mut rng, &mut pool, 0);
        let bytes = to_bytes(&v, &[]).unwrap();
        assert_eq!(total_size(&bytes, 0).unwrap(), bytes.len());
        let w = from_bytes(&bytes, 0).unwrap();
        assert_eq!(v, w);
        assert!(to_bytes(&w, &[]).unwrap() == bytes);
        let unshared = to_bytes(&v, &[ExternFlag::NoSharing]).unwrap();
        let w = from_bytes(&unshared, 0).unwrap();
        assert_eq!(v, w);
        assert!(to_bytes(&w.unshare(), &[]).unwrap() == to_bytes(&v.unshare(), &[]).unwrap());
    }
}

#[test]
fn long_lists_and_errors() {
    // A list longer than any recursion would allow.
    let l = Value::list((0..1_000_000).map(Value::int).collect::<Vec<_>>());
    let bytes = to_bytes(&l, &[]).unwrap();
    let back = from_bytes(&bytes, 0).unwrap();
    assert_eq!(back.list_items().unwrap().len(), 1_000_000);
    // Truncated or garbled input is an error, not a crash.
    assert!(from_bytes(&bytes[..bytes.len() - 1], 0).is_err());
    assert!(from_bytes(&bytes[..10], 0).is_err());
    let mut bad = bytes.clone();
    bad[0] = 0;
    assert!(from_bytes(&bad, 0).is_err());
    // A shared reference to nothing.
    let mut v = to_bytes(&Value::block(0, vec![Value::int(1)]), &[]).unwrap();
    let n = v.len();
    v[n - 1] = CODE_SHARED8;
    v.push(5);
    v[7] += 1; // the data length
    assert!(from_bytes(&v, 0).is_err());
    // Compat_32 refuses what a 32-bit OCaml could not read.
    assert!(to_bytes(&Value::int(1 << 40), &[ExternFlag::Compat32]).is_err());
}
