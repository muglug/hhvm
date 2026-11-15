// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/service/map_reduce.ml` and `map_reduce_ffi.ml`. See
//! `hh/PORTING.md`.
//!
//! A map-reducer maps a TAST into intermediate data, and then reduces a
//! bunch of intermediate data to a single value.
//!
//! The map-reducers are the fields of [`T`] (the OCaml keeps them in a map
//! with a GADT of their types). Of the five, `Tast_hashes`, `Type_counter`
//! and `Refinement_counter` are ported; `Tast_collector` and
//! `Reason_collector` are not: [`not_ported`] names the one that the
//! options enable.

use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::typechecker_options::TypecheckerOptions;
use crate::yojson::safe as yojson;

/// The result of an analysis (`map_reducer_result MRMap.t`).
#[derive(Default)]
pub struct T {
    tast_hashes: Option<crate::tast_hashes::T>,
    type_counter: Option<crate::type_counter::T>,
    refinement_counter: Option<crate::refinement_counter::T>,
}

/// The empty analysis.
pub fn empty() -> T {
    T::default()
}

/// The enabled map-reducer that is not ported, if there is one.
pub fn not_ported(tcopt: &TypecheckerOptions) -> Option<&'static str> {
    if !tcopt.dump_tasts.is_empty() {
        Some("Tast_collector")
    } else if tcopt.log_levels.get("reason_collector").map(|level| *level == 1).unwrap_or(false) {
        Some("Reason_collector")
    } else {
        None
    }
}

/// Take in a TAST and analyze it.
pub fn map(
    ctx: &provider_context::T,
    path: &RelativePath,
    tasts: &tast::ByNames,
    errors: &crate::diagnostics::T,
) -> T {
    let tcopt = provider_context::get_tcopt(ctx);
    T {
        tast_hashes: if crate::tast_hashes::is_enabled(&tcopt) {
            Some(crate::tast_hashes::map(ctx, path, tasts, errors))
        } else {
            None
        },
        type_counter: if crate::type_counter::is_enabled(&tcopt) {
            Some(crate::type_counter::map(ctx, path, tasts.clone()))
        } else {
            None
        },
        refinement_counter: if crate::refinement_counter::is_enabled(&tcopt) {
            Some(crate::refinement_counter::map(ctx, path, tasts.clone()))
        } else {
            None
        },
    }
}

/// `MRMap.union ~combine xs ys`
fn union<A>(x: Option<A>, y: Option<A>, reduce: impl FnOnce(A, A) -> A) -> Option<A> {
    match (x, y) {
        (Some(x), Some(y)) => Some(reduce(x, y)),
        (x, None) => x,
        (None, y) => y,
    }
}

/// Reduce two analysis into one.
pub fn reduce(xs: T, ys: T) -> T {
    T {
        tast_hashes: union(xs.tast_hashes, ys.tast_hashes, crate::tast_hashes::reduce),
        type_counter: union(xs.type_counter, ys.type_counter, crate::type_counter::reduce),
        refinement_counter: union(
            xs.refinement_counter,
            ys.refinement_counter,
            crate::refinement_counter::reduce,
        ),
    }
}

/// `Map_reduce_ffi.yojson_of_t (to_ffi xs)`: the fields that are `Some`.
pub fn yojson_of_t(xs: &T) -> yojson::T {
    let mut fields = vec![];
    if let Some(tast_hashes) = &xs.tast_hashes {
        fields.push(("tast_hashes".to_string(), crate::tast_hashes::yojson_of_t(tast_hashes)))
    }
    if let Some(type_counter) = &xs.type_counter {
        fields.push(("type_counter".to_string(), crate::type_counter::yojson_of_t(type_counter)))
    }
    if let Some(refinement_counter) = &xs.refinement_counter {
        fields.push((
            "refinement_counter".to_string(),
            crate::refinement_counter::yojson_of_t(refinement_counter),
        ))
    }
    yojson::T::Assoc(fields)
}
