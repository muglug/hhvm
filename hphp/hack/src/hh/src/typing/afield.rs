// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing.ml` (lines 12825-12848): module `Afield`.
//! See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::nast;

use crate::tast;
use crate::typing::expr;
use crate::typing_defs::Ty;
use crate::typing_env_types::Env;

/// `(locl_ty, saved_env) afield * locl_phase ty option * locl_ty`, without
/// the environment.
pub fn array_field(
    env: &mut Env,
    afield: &nast::Afield,
) -> (aast::Afield<Ty, tast::SavedEnv>, Option<Ty>, Ty) {
    match afield {
        aast::Afield::AFvalue(ve) => {
            let (tve, tv) = expr::expr(None, &expr::context::default(), env, ve);
            (aast::Afield::AFvalue(tve), None, tv)
        }
        aast::Afield::AFkvalue(ke, ve) => {
            let (tke, tk) = expr::expr(None, &expr::context::default(), env, ke);
            let (tve, tv) = expr::expr(None, &expr::context::default(), env, ve);
            (aast::Afield::AFkvalue(tke, tve), Some(tk), tv)
        }
    }
}
