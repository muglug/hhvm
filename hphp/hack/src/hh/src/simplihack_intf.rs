// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `simplihack/simplihack_intf.ml`. See `hh/PORTING.md`.
//!
//! The module types become traits. The functions of a
//! `LanguageServiceProvider` raise (`Simplihack_interpreter.EvalError`) when
//! what they look up is not there: here they return a `Result` with the
//! provider's `Error`. `PromptCtxProvider` (a signature nothing is checked
//! against) has no counterpart: the functions of
//! `Simplihack_prompt_context_provider.Make` are generic over the provider.

use oxidized::aast;
use oxidized::nast;

use crate::folded_class::ClassElt;
use crate::tast_env;

/// `module type Value`
#[derive(Clone, Debug)]
pub enum Value {
    /// String values
    Str(bstr::BString),
    /// Represents the unit value
    Unit,
}

/// `module type LanguageServiceProvider`: `Class.t` is `Class`; the
/// functions of `Class` are those prefixed with `class_`.
pub trait LanguageServiceProvider: Sized {
    /// What the functions raise.
    type Error;

    /// `Class.t`
    type Class;

    fn env(&self) -> &tast_env::Env;

    fn find_class(&self, name: &aast::ClassName) -> Result<nast::Class_, Self::Error>;

    fn find_static_method<'c>(
        &self,
        class_: &'c nast::Class_,
        name: &oxidized::ast_defs::Pstring,
    ) -> Result<&'c nast::Method_, Self::Error>;

    fn find_function(&self, name: &aast::Sid) -> Result<nast::FunDef, Self::Error>;

    /// `Class.find`
    fn class_find(&self, name: &aast::ClassName) -> Result<Self::Class, Self::Error>;

    /// `Class.constructor`
    fn class_constructor(cls: &Self::Class) -> Option<ClassElt>;

    /// `Class.methods`
    fn class_methods(cls: &Self::Class) -> Vec<(String, ClassElt)>;

    /// `Class.static_methods`
    fn class_static_methods(cls: &Self::Class) -> Vec<(String, ClassElt)>;

    /// `Class.fields`
    fn class_fields(cls: &Self::Class) -> Vec<(String, ClassElt)>;

    /// `Class.static_fields`
    fn class_static_fields(cls: &Self::Class) -> Vec<(String, ClassElt)>;
}
