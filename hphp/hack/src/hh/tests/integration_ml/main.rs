// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The `integration_ml` tests of `hphp/hack/test/integration_ml`, ported
//! (plan §4.2). One binary (`harness = false`): without arguments it runs
//! itself once per test (`main --run <test>`), because a process can only
//! initialise one server (process globals: the dep graph, the path
//! prefixes, `decl_store`), as in the OCaml.
//!
//! Owned by **T1** (plan §3.1). Created by W0 with no test yet.

// (Used by the tests T1 ports.)
#[allow(dead_code)]
mod base;

/// The tests: name and body.
const TESTS: &[(&str, fn())] = &[];

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if let [_, flag, name] = args.as_slice() {
        if flag == "--run" {
            match TESTS.iter().find(|(n, _)| n == name) {
                Some((_, test)) => test(),
                None => {
                    eprintln!("integration_ml: no test {}", name);
                    std::process::exit(2)
                }
            }
            return;
        }
    }
    // `cargo test` passes its own flags (`--nocapture`, a filter...): a
    // filter is any argument that does not start with `-`.
    let filter: Option<&String> = args.iter().skip(1).find(|a| !a.starts_with('-'));
    let exe = std::env::current_exe().expect("integration_ml: current_exe");
    let mut failed = Vec::new();
    for (name, _) in TESTS {
        if filter.is_some_and(|f| !name.contains(f.as_str())) {
            continue;
        }
        let status = std::process::Command::new(&exe)
            .args(["--run", name])
            .status()
            .expect("integration_ml: spawn");
        println!("test {} ... {}", name, if status.success() { "ok" } else { "FAILED" });
        if !status.success() {
            failed.push(*name);
        }
    }
    if !failed.is_empty() {
        println!("failures: {:?}", failed);
        std::process::exit(101)
    }
}
