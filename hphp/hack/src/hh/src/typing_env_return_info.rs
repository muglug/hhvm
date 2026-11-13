// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_env_return_info.ml`. See `hh/PORTING.md`.

use crate::typing_defs_core::Ty;

/// Return type information as gathered from explicit hints or inferred
#[derive(Clone)]
pub struct T {
    /// Return type itself. Awaitable<t> is represented explicitly, not stripped.
    /// In the case of lambdas without an explicit return type hint, the return
    /// type is determined by context or is a type variable that may get resolved
    /// when checking the body of the lambda.
    pub return_type: Ty,
    /// Does the function or function type have the <<__ReturnDisposable>> attribute?
    pub return_disposable: bool,
    /// Should we ignore readonly errors when checking return types?
    /// This is set when the parameter has <<__IgnoreReadonlyError>> attribute.
    pub return_ignore_readonly: bool,
}
