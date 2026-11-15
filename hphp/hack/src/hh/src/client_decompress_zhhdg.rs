// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_decompress_zhhdg.ml`. See `hh/PORTING.md`.
//!
//! The open-source build links `stubs/depgraph_decompress_ffi.ml`, whose
//! `decompress` fails ("decompress not implemented"): so does this one
//! (`crate::depgraph_decompress_ffi::decompress`).

/// `Client_decompress_zhhdg.env`
use crate::depgraph_decompress_ffi;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Env {
    pub path: String,
    pub from: String,
}

/// `Failure s`, as `Printexc.to_string` prints it.
pub struct Failure(pub String);

impl std::fmt::Debug for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failure({})", crate::rt::ocaml_printf::sprintf_s(&self.0))
    }
}

/// `main env` (`Err`: the `Failure` it raises)
pub fn main(env: &Env) -> Result<crate::exit_status::T, Failure> {
    let deptable_result = depgraph_decompress_ffi::decompress(&env.path)?;
    match deptable_result {
        Ok(decompressed_path) => {
            println!("Decompressed depgraph to {}", decompressed_path);
            Ok(crate::exit_status::T::NoError)
        }
        Err(err) => Err(Failure(format!("Failed to decompress dep graph: {}", err))),
    }
}
