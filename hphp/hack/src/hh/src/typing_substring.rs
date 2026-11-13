// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_substring.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::pos::Pos;

use crate::typing_defs_core::Ty;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error_utils;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_solver;
use crate::typing_subtype;

pub fn sub_string_err(p: Pos, env: &mut Env, ty: Ty) -> Option<(Ty, Ty)> {
    // Under constraint-based inference, we implement sub_string as a subtype test.
    // All the cases in the legacy implementation just fall out from subtyping rules.
    // We test against ?(arraykey | bool | float | resource | dynamic).
    let r = reason::witness(p.clone());
    let tyl = vec![
        make_type::arraykey(r.clone()),
        make_type::bool(r.clone()),
        make_type::float(r.clone()),
        make_type::resource(r.clone()),
        make_type::dynamic(r.clone()),
    ];
    let stringish = make_type::class_type(r.clone(), sn::classes::STRINGISH.to_string(), vec![]);
    let stringlike = make_type::nullable(r.clone(), make_type::union(r, tyl));
    let (is_sub_stringish, e1) = typing_solver::is_sub_type(env, &ty, &stringish);
    let err = typing_error::primary(if is_sub_stringish {
        typing_error::primary::T::Object_string_deprecated(p)
    } else {
        // `lazy (Typing_print.error env ty)`, with the environment as it is now.
        let env = env.clone();
        let ty = ty.clone();
        typing_error::primary::T::Invalid_substring {
            pos: p,
            ty_name: Lazy::new(move || typing_print::error(None, &env, &ty)),
        }
    });
    let e2 = typing_subtype::sub_type_or_fail(env, ty.clone(), stringlike.clone(), Some(err));
    let ty_mismatch = e2.as_ref().map(|_| (ty, stringlike));
    let ty_err_opt = match (e1, e2) {
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    };
    if let Some(ty_err) = &ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    ty_mismatch
}

pub fn sub_string(p: Pos, env: &mut Env, ty: Ty) {
    sub_string_err(p, env, ty);
}
