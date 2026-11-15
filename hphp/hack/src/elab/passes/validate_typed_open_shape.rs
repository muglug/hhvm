// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Hint;
use nast::Hint_;
use nast::Id;
use nast::NastShapeInfo;

use crate::prelude::*;

/// Port of `Naming_validate_typed_open_shape`: reject `shape(..., T...)` typed
/// open shapes unless `tco_typed_open_shapes` is enabled.
#[derive(Clone, Copy, Default)]
pub struct ValidateTypedOpenShapePass;

/// `mixed...` is accepted regardless of the flag because it is semantically
/// equivalent to plain `...` (the implicit unknown-fields type). Detect bare
/// `Hmixed`, `Happly` forms produced before/around `Happly`-hint elaboration,
/// and `supportdyn(mixed)` (introduced by implicit-sdt elaboration).
fn is_mixed_hint(Hint(_, hint_): &Hint) -> bool {
    match &**hint_ {
        Hint_::Hmixed => true,
        Hint_::Happly(Id(_, name), hints) if hints.is_empty() => {
            name == sn::typehints::MIXED
                || name.strip_prefix('\\') == Some(sn::typehints::MIXED)
                || name.strip_prefix("\\HH\\") == Some(sn::typehints::MIXED)
        }
        Hint_::Happly(Id(_, name), hints)
            if hints.len() == 1 && name == sn::classes::SUPPORT_DYN =>
        {
            is_mixed_hint(&hints[0])
        }
        _ => false,
    }
}

impl Pass for ValidateTypedOpenShapePass {
    fn on_ty_hint_top_down(&mut self, env: &Env, elem: &mut Hint) -> ControlFlow<()> {
        if !env.typed_open_shapes() {
            if let Hint(
                _,
                box Hint_::Hshape(NastShapeInfo {
                    unknown_fields_type: Some(h),
                    ..
                }),
            ) = elem
            {
                if !is_mixed_hint(h) {
                    env.emit_error(NamingError::TypedOpenShapeDisallowed(h.0.clone()))
                }
            }
        }
        Continue(())
    }
}
