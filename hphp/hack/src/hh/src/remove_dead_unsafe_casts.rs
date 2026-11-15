// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `remove_dead_unsafe_casts/remove_dead_unsafe_casts.ml`. See
//! `hh/PORTING.md`.
//!
//! A patch is the position to replace and its new text (the OCaml
//! `Server_rename_types.Replace` of the absolute position, which has the
//! same offsets).

use std::collections::BTreeMap;
use std::sync::Mutex;

use oxidized::aast;

use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;

/// `Replace { pos; text }`
pub type Patch = (Pos, String);

pub type Patches = Vec<Patch>;

type CanBeCaptured = bool;

/// Positions needed to generate dead unsafe cast removal patches
///
/// `PatchHeap` (a `SharedMem.Heap`, description `Patch_heap`) on the shared
/// heap when the server has one (see `ctx::use_shared_memory_stores`: every
/// thread, and the workers' clones with `HH_RUST_WORKERS=1`, records there
/// and the master reads the patches); otherwise a map of the process.
mod patch_heap {
    use super::*;

    type V = (CanBeCaptured, Pos, Pos);

    static HEAP: Mutex<BTreeMap<RelativePath, V>> = Mutex::new(BTreeMap::new());

    #[cfg(feature = "port")]
    #[derive(serde::Serialize, serde::Deserialize)]
    struct PatchValue(V);

    #[cfg(feature = "port")]
    impl crate::shared_mem::Value for PatchValue {
        const DESCRIPTION: &'static str = "Patch_heap";
    }

    #[cfg(feature = "port")]
    fn shared_heap() -> Option<&'static crate::shared_mem::Heap<PatchValue>> {
        static HEAP: std::sync::OnceLock<crate::shared_mem::Heap<PatchValue>> = std::sync::OnceLock::new();
        crate::ctx::shared_memory_stores().then(|| HEAP.get_or_init(|| crate::shared_mem::Heap::new(0)))
    }

    /// `Relative_path.S.to_string`: the key of a file in the heap.
    #[cfg(feature = "port")]
    fn key(path: &RelativePath) -> Vec<u8> {
        path.to_string().into_bytes()
    }

    /// (A write only works when the entry is empty.)
    pub fn add(path: RelativePath, v: V) {
        #[cfg(feature = "port")]
        if let Some(heap) = shared_heap() {
            return heap.add(&key(&path), &PatchValue(v));
        }
        HEAP.lock().unwrap().entry(path).or_insert(v);
    }

    pub fn get(path: &RelativePath) -> Option<V> {
        #[cfg(feature = "port")]
        if let Some(heap) = shared_heap() {
            return heap.get(&key(path)).map(|v| v.0);
        }
        HEAP.lock().unwrap().get(path).cloned()
    }

    pub fn remove(path: &RelativePath) {
        #[cfg(feature = "port")]
        if let Some(heap) = shared_heap() {
            return heap.remove(&key(path));
        }
        HEAP.lock().unwrap().remove(path);
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, expr: &'a tast::Expr) {
        let aast::Expr(_, hole_pos, e) = expr;
        if let aast::Expr_::Hole(hole) = e {
            let (aast::Expr(expr_ty, expr_pos, expr), _, dest_ty, source) = &**hole;
            if matches!(source, aast::HoleSource::UnsafeCast(_) | aast::HoleSource::UnsafeNonnullCast)
                && !crate::typing_defs::is_any(expr_ty)
                && crate::typing_subtype::is_sub_type(
                    env,
                    expr_ty,
                    &crate::typing_make_type::locl_like(crate::typing_reason::none(), dest_ty.clone()),
                )
            {
                let path = tast_env::get_file(env);
                // The following shared memory write will only work when the entry for
                // `path` is empty. Later updates will be dropped on the floor. This is
                // the desired behaviour as patches don't compose and we want to apply
                // them one at a time per file.
                patch_heap::add(
                    RelativePath::clone(&path),
                    (crate::aast_utils::can_be_captured(expr), hole_pos.clone(), expr_pos.clone()),
                )
            }
        }
    }
}

pub fn patch_location_collection_handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}

fn generate_patch(content: &str, (can_be_captured, hole_pos, expr_pos): (CanBeCaptured, Pos, Pos)) -> Patch {
    let text = crate::pos::get_text_from_pos(content, &expr_pos);
    // Enclose with parantheses to prevent accidental capture of the expression
    // if the expression inside the UNSAFE_CAST can be captured.
    let text = if can_be_captured { format!("({})", text) } else { text };
    (hole_pos, text)
}

/// `get_patches ?is_test ~files_info ~fold`: `files_info` are the keys of
/// the map, in the order of the fold.
///
/// (`File_provider.get_contents ~force_read_disk:(not is_test)`: the files
/// are those of the context, which is where the test's replacements are.)
pub fn get_patches(ctx: &provider_context::T, _is_test: Option<bool>, files_info: &[RelativePath]) -> Patches {
    let mut patches = vec![];
    for path in files_info {
        match patch_heap::get(path) {
            None => {}
            Some(patch_info) => {
                let contents = crate::file_provider::rust_provider_backend::file::get_contents(ctx, path)
                    .expect("Option.value_exn");
                let new_patch = generate_patch(&String::from_utf8_lossy(&contents), patch_info);
                patch_heap::remove(path);
                // `new_patch :: patches`
                patches.insert(0, new_patch)
            }
        }
    }
    patches
}
