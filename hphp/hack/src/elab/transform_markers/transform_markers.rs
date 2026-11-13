// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use proc_macro::TokenStream;

/// Registers the inert `#[transform(..)]` attribute on a type, its fields and
/// its variants.
///
/// The attribute is read by `hh_codegen elab-transform` when it generates
/// `elab/pass.rs` and `elab/transform.rs`:
///
/// - `#[transform(opaque)]`: the generated traversal does not descend into
///   this type, field or variant.
/// - `#[transform(explicit)]`: the generated `Pass` trait gets a dedicated
///   method for this field or variant.
///
/// The derive itself generates no code.
#[proc_macro_derive(TransformMarkers, attributes(transform))]
pub fn derive_transform_markers(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}
