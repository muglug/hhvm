// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/ide_parser_cache.ml`. See `hh/PORTING.md`.
//!
//! Ported by F5 (for `File_outline.outline`): the activation state
//! (`is_active_ref`, `enable`, `is_enabled`, `is_active`, `activate`,
//! `deactivate`, `with_ide_cache`) and `get_ast`, `get_ast_if_active`.
//!
//! Not ported: `get_cst` (the positioned syntax tree has no type of its own
//! in this crate) and the two `Shared_mem.FreqCache`s (`IdeAstCache`,
//! `IdeCstCache`): `get_ast` parses every time. A hit of the OCaml cache
//! gives the same AST, merges the same errors and provides the same fixmes
//! as the miss that filled it, so only the time differs.

use std::sync::atomic::AtomicU8;
use std::sync::atomic::Ordering;

use oxidized::parser_options::ParserOptions;
use relative_path::RelativePath;

use crate::diagnostics_state as diagnostics;
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

pub fn get_ast(tcopt: &ParserOptions, path: &RelativePath, content: &[u8]) -> parser_return::T {
    assert!(is_active());
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
    diagnostics::merge_into_current(errors);
    ast
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
