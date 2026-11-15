// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_attributes.ml`. See `hh/PORTING.md`.
//!
//! The tables of `Naming_special_names` that this module reads
//! (`AttributeKinds.plain_english_map`, and the `contexts` of
//! `UserAttributes.as_map` and `UserAttributes.systemlib_map`) are in
//! `crate::naming_special_names`.

use oxidized::aast;
use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
use crate::diagnostics;
use crate::folded_class as cls;
use crate::naming_special_names as sn;
use crate::string_utils;
use crate::typechecker_options;
use crate::typing_coeffects;
use crate::typing_defs_core::PosString;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_lenv;
use crate::typing_make_type as make_type;

pub type AttributeInterfaceName = String;

/// `new_object_checker`: `Pos.t -> env -> Typing_defs.pos_string ->
/// Nast.argument list -> env`.
pub type NewObjectChecker<'a> = dyn Fn(&Pos, &mut Env, &PosString, &[nast::Argument]) + 'a;

/// `Diagnostics.add_diagnostic (Nast_check_error.to_user_diagnostic err)`
fn add_naming_phase_error(error: NamingPhaseError) {
    let diagnostic = crate::naming_phase_error::to_user_diagnostic(error);
    diagnostics::add_diagnostic(diagnostic);
}

/// `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic err
/// custom_err_config)`: the diagnostic of `crate::naming_phase_error`, with the
/// messages of the custom error config (which that renderer does not add).
pub(crate) fn add_naming_error(
    err: NamingError,
    custom_err_config: &crate::custom_error_config::T,
) {
    let custom_msgs: Vec<String> =
        crate::custom_error_eval::eval_naming_error(custom_err_config, &err)
            .iter()
            .map(|t| crate::naming_error_utils::render_custom_error(t))
            .collect();
    let mut diagnostic = crate::naming_phase_error::to_user_diagnostic(NamingPhaseError::Naming(err));
    diagnostic.custom_msgs = custom_msgs;
    diagnostics::add_diagnostic(diagnostic);
}

fn check_implements(
    check_new_object: &NewObjectChecker<'_>,
    attr_interface: &str,
    ua: &nast::UserAttribute,
    env: &mut Env,
) {
    let aast::UserAttribute {
        name: oxidized::ast_defs::Id(attr_pos, attr_name),
        params,
    } = ua;
    let expr_kind = match sn::attribute_kinds::plain_english_map_find_opt(attr_interface) {
        Some(ek) => ek,
        None => "this expression",
        // this case should never execute
    };
    let is_systemlib = typing_env::get_tcopt(env).po.is_systemlib;
    if attr_name.starts_with("__") {
        // Check against builtins
        let check_attr = |map: &'static [(&'static str, &'static [&'static str])]| {
            match sn::user_attributes::find_opt(attr_name, map) {
                Some(contexts) => {
                    if !contexts.iter().any(|c| *c == attr_interface) {
                        add_naming_phase_error(NamingPhaseError::NastCheck(
                            NastCheckError::WrongExpressionKindBuiltinAttribute {
                                expr_kind: expr_kind.to_string(),
                                pos: attr_pos.clone(),
                                attr_name: attr_name.clone(),
                            },
                        ))
                    }
                    true
                }
                None => false,
            }
        };
        if check_attr(sn::user_attributes::AS_MAP)
            || (is_systemlib && check_attr(sn::user_attributes::SYSTEMLIB_MAP))
        {
        } else {
            let all_valid_user_attributes: Vec<String> = sn::user_attributes::AS_MAP
                .iter()
                .filter(|(_, contexts)| contexts.iter().any(|c| *c == attr_interface))
                .map(|(name, _)| name.to_string())
                .collect();

            let closest_attr_name = string_utils::most_similar(
                None,
                attr_name,
                &all_valid_user_attributes,
                |x: &String| x.clone(),
            );

            let custom_err_config =
                typechecker_options::custom_error_config(&typing_env::get_tcopt(env));
            add_naming_error(
                NamingError::UnboundAttributeName {
                    pos: attr_pos.clone(),
                    attr_name: attr_name.clone(),
                    closest_attr_name,
                },
                &custom_err_config,
            )
        }
    } else {
        match typing_env::get_class(env, attr_name) {
            decl_entry::T::Found(attr_class) => {
                // Found matching class
                let attr_cid = PosString(cls::pos(&attr_class), cls::name(&attr_class));
                // Package-boundary enforcement for attribute classes (strict-isolation
                // targets) is handled uniformly with other class references in
                // `class_id_`'s `should_check_package_boundary`; nothing to do here.
                if !cls::has_ancestor(&attr_class, attr_interface) {
                    let attr_class_pos: PosOrDecl = cls::pos(&attr_class);
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::WrongExpressionKindAttribute {
                            expr_kind: expr_kind.to_string(),
                            pos: attr_pos.clone(),
                            attr_name: attr_name.clone(),
                            attr_class_pos,
                            attr_class_name: cls::name(&attr_class),
                            intf_name: attr_interface.to_string(),
                        }),
                        env,
                    )
                } else {
                    let args: Vec<nast::Argument> = params
                        .iter()
                        .map(|e| aast::Argument::Anormal(e.clone()))
                        .collect();
                    check_new_object(attr_pos, env, &attr_cid, &args)
                }
            }
            decl_entry::T::NotYetAvailable => {
                // A retry will happen. Don't emit error to avoid error-based backtracking
            }
            _ => {
                let custom_err_config =
                    typechecker_options::custom_error_config(&typing_env::get_tcopt(env));
                add_naming_error(
                    NamingError::UnboundAttributeName {
                        pos: attr_pos.clone(),
                        attr_name: attr_name.clone(),
                        closest_attr_name: None,
                    },
                    &custom_err_config,
                )
            }
        }
    }
}

/// `check_def` of typing_attributes.ml:135, shadowed at :143 (the second one
/// calls it). `List.fold_right`: from the last attribute to the
/// first.
fn check_def_shadowed(
    env: &mut Env,
    check_new_object: &NewObjectChecker<'_>,
    kind: &str,
    attributes: &[nast::UserAttribute],
) {
    for attr in attributes.iter().rev() {
        check_implements(check_new_object, kind, attr, env)
    }
}

/// Checks a list of user attributes:
/// - checks that the attributes are on the proper kind of element,
///   by checking subtyping of the attribute class with the provided attribute interface
///   (e.g. FileAttribute, MethodAttribute, see Naming_special_names for a full list)
/// - checks for unbound attribute names
/// - runs the provided new_object_checker, which checks creating an instance of the attribute class.
///
/// TODO(coeffects) change to mixed after changing those constructors to pure
pub fn check_def(
    env: &mut Env,
    check_new_object: &NewObjectChecker<'_>,
    kind: &str,
    attributes: &[nast::UserAttribute],
) {
    let defaults = make_type::default_capability(PosOrDecl::NONE);
    let conts = typing_env::all_continuations(env);
    typing_lenv::stash_and_do(env, &conts, |env| {
        let _ = typing_coeffects::register_capabilities(env, defaults.clone(), defaults);
        check_def_shadowed(env, check_new_object, kind, attributes)
    })
}

#[cfg(test)]
mod tests {
    use super::sn::user_attributes;

    #[test]
    fn tables_are_sorted() {
        for map in [user_attributes::AS_MAP, user_attributes::SYSTEMLIB_MAP] {
            assert!(map.windows(2).all(|w| w[0].0 < w[1].0));
        }
        assert_eq!(user_attributes::AS_MAP.len(), 61);
        assert_eq!(user_attributes::SYSTEMLIB_MAP.len(), 7);
    }
}
