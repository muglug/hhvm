// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl.ml`. See `hh/PORTING.md`.
//!
//! `make_env` is split in its two steps, because its two callers need them
//! at different times:
//!
//! - `Direct_decl_utils.direct_decl_parse_and_cache ctx fn` (the Rust backend
//!   branch: `Rust_provider_backend.Decl.direct_decl_parse_and_cache`, which
//!   parses the file and caches its decls with
//!   `remove_naming_conflict_losers`): [`direct_decl_parse`], then
//!   [`cache_decls`] (`Ctx::add_shallow_decls`);
//! - the fold of each class of the file
//!   (`Rust_provider_backend.Decl.declare_folded_class`):
//!   [`declare_folded_classes`].
//!
//! [`make_env`] itself (used by `hh single`) parses and folds without the
//! cache step: the decl stores of `hh single` are filled by
//! `Ctx::declare_file` for all the files before (with the same winners), so
//! caching them again would change nothing. `Decl_redecl_service` (the
//! daemon) does all three steps, see `decl_redecl_service::redeclare_files`.

use std::sync::Arc;

use ::file_provider::FileProvider as _;
use pos::TypeName;
use ty::decl::shallow::NamedDecl;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::relative_path;

/// `make_env ~sh ctx fn`: declares (folds) every class of the file, in the
/// order of `pfh_decls` (the reverse of the lexical order), through the
/// Rust provider backend (`Rust_provider_backend.Decl.declare_folded_class`).
/// The errors of a fold (a cycle, ...) are kept in the folded class, so the
/// first class of a cycle to be folded decides on which class it is
/// reported.
pub fn make_env(ctx: &Arc<Ctx>, fn_: &relative_path::T) {
    // Direct_decl_utils.direct_decl_parse_and_cache ctx fn (without the
    // cache: see the module documentation)
    let Some(decls) = direct_decl_parse(ctx, fn_) else {
        return;
    };
    declare_folded_classes(ctx, &classes_of_decls(&decls));
}

/// The parse of `direct_decl_parse_and_cache`: the decls of the file in
/// lexical order, `None` when it cannot be read (`get_file_contents` gives
/// `None`).
pub fn direct_decl_parse(ctx: &Arc<Ctx>, fn_: &relative_path::T) -> Option<Vec<NamedDecl<R>>> {
    let path = pos::RelativePath::from(fn_);
    let text = ctx.files.get(path).ok()?;
    ctx.decl_parser.parse_with_text(path, &text).ok()
}

/// The cache of `direct_decl_parse_and_cache`
/// (`Rust_provider_backend.Decl.direct_decl_parse_and_cache`, then
/// `dedup_and_add_decls`): the decls of the names bound to the file.
pub fn cache_decls(ctx: &Arc<Ctx>, fn_: &relative_path::T, decls: Vec<NamedDecl<R>>) {
    ctx.add_shallow_decls(pos::RelativePath::from(fn_), decls)
}

/// The classes of `decls` (in lexical order), in the order of `pfh_decls`
/// (the reverse).
pub fn classes_of_decls(decls: &[NamedDecl<R>]) -> Vec<TypeName> {
    decls
        .iter()
        .rev()
        .filter_map(|decl| match decl {
            NamedDecl::Class(name, _) => Some(*name),
            _ => None,
        })
        .collect()
}

/// The `List.iter parsed_file.pfh_decls` of `make_env`: folds the classes
/// (in the order [`classes_of_decls`] gives them).
pub fn declare_folded_classes(ctx: &Arc<Ctx>, classes: &[TypeName]) {
    for name in classes {
        let _ = ctx.folded_decls.get_class(*name);
    }
}
