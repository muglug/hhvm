// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `parser/ide_parser_cache.ml`. See `hh/PORTING.md`.
//!
//! The two `Shared_mem.FreqCache`s (`IdeAstCache`, `IdeCstCache`, capacity
//! 10) are `lfu_cache` caches, one per thread: like a `FreqCache`, which is
//! a cache of the process that is not in the shared heap, they are local to
//! the worker that fills them. The CST is the root of the parser's
//! positioned syntax tree (`SyntaxTree.t`), shared (`Arc`).

use std::sync::atomic::AtomicU8;
use std::sync::atomic::Ordering;

use std::cell::RefCell;
use std::sync::Arc;

use oxidized::parser_options::ParserOptions;
use parser_core_types::positioned_syntax::PositionedSyntax;
use relative_path::RelativePath;

use crate::diagnostics as diagnostics;
use crate::full_fidelity_ast;
use crate::hh_logger;
use crate::parser_return;

const DISABLED: u8 = 0;
const ACTIVE: u8 = 1;
const INACTIVE: u8 = 2;

/// `is_active_ref : [ `Disabled | `Active | `Inactive ] ref`
static IS_ACTIVE_REF: AtomicU8 = AtomicU8::new(DISABLED);

pub fn enable() {
    hh_logger::log("Enabling Ide_parser_cache");
    IS_ACTIVE_REF.store(INACTIVE, Ordering::Relaxed)
}

pub fn is_enabled() -> bool {
    !matches!(IS_ACTIVE_REF.load(Ordering::Relaxed), DISABLED)
}

pub fn is_active() -> bool {
    matches!(IS_ACTIVE_REF.load(Ordering::Relaxed), ACTIVE)
}

pub fn activate() {
    if is_enabled() {
        IS_ACTIVE_REF.store(ACTIVE, Ordering::Relaxed)
    }
}

pub fn deactivate() {
    if is_enabled() {
        IS_ACTIVE_REF.store(INACTIVE, Ordering::Relaxed)
    }
}

pub fn with_ide_cache<A>(f: impl FnOnce() -> A) -> A {
    crate::utils::try_finally(
        || {
            activate();
            f()
        },
        deactivate,
    )
}

/// `IdeAstCache`: `Parser_return.t * Fixme_provider.FixmeMap.t * Diagnostics.t`
type IdeAstCacheValue = Arc<(
    parser_return::T,
    crate::fixme_provider::fixme_map::T,
    diagnostics::T,
)>;

/// The `capacity` of both caches.
const CAPACITY: usize = 10;

thread_local! {
    static IDE_AST_CACHE: RefCell<crate::lfu_cache::Cache<Vec<u8>, IdeAstCacheValue>> =
        RefCell::new(crate::lfu_cache::Cache::make(CAPACITY));
    static IDE_CST_CACHE: RefCell<crate::lfu_cache::Cache<Vec<u8>, Arc<PositionedSyntax>>> =
        RefCell::new(crate::lfu_cache::Cache::make(CAPACITY));
}

fn get_digest(path: &RelativePath, content: &[u8]) -> Vec<u8> {
    use md5::Digest;
    let string_path = crate::relative_path::to_absolute(path);
    let mut hasher = md5::Md5::new();
    hasher.update(string_path.as_bytes());
    hasher.update(content);
    hasher.finalize().to_vec()
}

pub fn get_cst(source_text: &crate::full_fidelity_source_text::T) -> Arc<PositionedSyntax> {
    assert!(is_active());
    let digest = get_digest(
        crate::full_fidelity_source_text::file_path(source_text),
        crate::full_fidelity_source_text::text(source_text),
    );
    match IDE_CST_CACHE.with_borrow_mut(|cache| cache.find_and_count(&digest)) {
        Some(cst) => cst,
        None => {
            // `Full_fidelity_parser_env.default`
            let (root, _errors, _state) = positioned_parser::parse_script(
                &crate::full_fidelity_source_text::source_text(source_text),
                parser_core_types::parser_env::ParserEnv::default(),
            );
            let cst = Arc::new(root);
            IDE_CST_CACHE.with_borrow_mut(|cache| cache.add(digest, Arc::clone(&cst)));
            cst
        }
    }
}

pub fn get_ast(tcopt: &ParserOptions, path: &RelativePath, content: &[u8]) -> parser_return::T {
    assert!(is_active());
    let digest = get_digest(path, content);
    match IDE_AST_CACHE.with_borrow_mut(|cache| cache.find_and_count(&digest)) {
        Some(cached) => {
            let (ast, fixmes, errors) = &*cached;
            diagnostics::merge_into_current(errors.clone());
            crate::fixme_provider::provide_hh_fixmes(path.clone(), fixmes.clone());
            ast.clone()
        }
        None => {
            let (errors, ast) = diagnostics::do_(None, || {
                full_fidelity_ast::defensive_program(
                    Some(false),
                    None,
                    None,
                    Some(true),
                    tcopt.clone(),
                    path,
                    content,
                )
            });
            diagnostics::merge_into_current(errors.clone());
            let fixmes = crate::fixme_provider::get_hh_fixmes(path).unwrap_or_default();
            IDE_AST_CACHE.with_borrow_mut(|cache| cache.add(digest, Arc::new((ast.clone(), fixmes, errors))));
            ast
        }
    }
}

pub fn get_ast_if_active(
    tcopt: &ParserOptions,
    path: &RelativePath,
    content: &[u8],
) -> Option<parser_return::T> {
    if !is_active() {
        None
    } else {
        Some(get_ast(tcopt, path, content))
    }
}
