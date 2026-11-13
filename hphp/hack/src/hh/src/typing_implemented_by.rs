// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_implemented_by.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::nast;

use crate::typing;
use crate::typing_env_types::Env;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_subtype;

/// `Naming_special_names.UserAttributes.uaImplementedBy`
/// (`naming_special_names_rust` does not have it).
const UA_IMPLEMENTED_BY: &str = "__ImplementedBy";

/// Validation for the __ImplementedBy attribute.
/// - the referenced function exists
/// - The method and function signatures are compatible
pub fn check_method(env: &mut Env, cls_id: &aast::Sid, m: &nast::Method_) {
    match m
        .user_attributes
        .iter()
        .find(|ua| ua.name.1 == UA_IMPLEMENTED_BY)
    {
        Some(aast::UserAttribute { params, .. }) => match params.as_slice() {
            [aast::Expr(_, p, aast::Expr_::String(impl_name))] => {
                // The name is a byte string in the AST.
                let impl_name = String::from_utf8_lossy(impl_name.as_slice()).into_owned();
                let (_, fun_type) = typing::function_pointer::synth_top_level(
                    p,
                    &oxidized::ast_defs::Id(p.clone(), impl_name),
                    &[],
                    aast::FunctionPointerSource::Code,
                    env,
                );
                let (_, meth_type) = typing::method_caller::synth_function_type(
                    &m.span,
                    &(cls_id.clone(), (m.name.0.clone(), m.name.1.clone())),
                    env,
                );
                let ty_err_opt = typing_subtype::sub_type(
                    env,
                    None,
                    None,
                    None,
                    None,
                    fun_type,
                    meth_type,
                    Some(reasons_callback::of_primary_error(
                        primary::T::Unify_error {
                            pos: p.clone(),
                            msg_opt: Some(
                                "The method must be implemented by a function with a compatible type."
                                    .to_string(),
                            ),
                            reasons_opt: None,
                        },
                    )),
                );
                if let Some(err) = &ty_err_opt {
                    typing_error_utils::add_typing_error(err, env)
                }
            }
            _ => {}
        },
        _ => {}
    }
}
