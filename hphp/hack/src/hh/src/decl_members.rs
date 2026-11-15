// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_members.ml`:
//! `Decl_members.Make (Decl_enforceability_shallow.Provider)`.
//!
//! This modules transforms member types from Shallow_decl_defs like
//! `shallow_method` into member types from Typing_defs like `fun_elt`.
//! It may perform pessimization along the way.

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::ast_defs::ClassishKind;
use ty::decl::ShallowClass;
use ty::decl::ShallowMethod;
use ty::decl::ShallowProp;
use ty::decl::Ty;
use ty::decl::ty::FunElt;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_enforceability::FunKind;
// module Pessimize = Decl_enforceability.Pessimize (Provider)
use crate::decl_enforceability::pessimize;
use crate::decl_enforceability_shallow::Provider;
use crate::decl_utils;

/// May pessimize the property.
pub fn build_property(
    ctx: &Arc<Ctx>,
    this_class: Option<&Arc<ShallowClass<R>>>,
    sp: &ShallowProp<R>,
) -> Ty<R> {
    let ShallowProp {
        name: _,
        xhp_attr: sp_xhp_attr,
        ty: sp_type,
        visibility: _,
        flags: sp_flags,
    } = sp;
    let is_xhp_attr = sp_xhp_attr.is_some();
    let no_auto_likes = sp_flags.no_auto_likes();
    pessimize::pessimise_prop_type::<Provider>(
        is_xhp_attr,
        this_class,
        no_auto_likes,
        ctx,
        &decl_utils::get_pos(sp_type),
        sp_type,
    )
}

pub fn build_constructor(sm: &ShallowMethod<R>) -> FunElt<R> {
    let ShallowMethod {
        name: sm_name,
        ty: sm_type,
        visibility: _,
        deprecated: sm_deprecated,
        flags: _,
        attributes: _,
        package_requirement: sm_package_requirement,
    } = sm;
    let fe_pos = sm_name.pos();
    FunElt {
        module: None,
        package: None,
        pos: fe_pos.clone(),
        internal: false,
        deprecated: *sm_deprecated,
        ty: sm_type.clone(),
        php_std_lib: false,
        support_dynamic_type: false,
        no_auto_dynamic: false,
        no_auto_likes: false,
        gated_by_feature_flag: None,
        package_requirement: sm_package_requirement.clone(),
    }
}

/// May pessimize the method.
pub fn build_method(
    ctx: &Arc<Ctx>,
    this_class: Option<&Arc<ShallowClass<R>>>,
    no_auto_likes: bool,
    sm: &ShallowMethod<R>,
) -> FunElt<R> {
    let ShallowMethod {
        name: sm_name,
        ty: sm_type,
        visibility: sm_visibility,
        deprecated: _,
        flags: sm_flags,
        attributes: sm_attributes,
        package_requirement: sm_package_requirement,
    } = sm;
    let pos = sm_name.pos();
    let support_dynamic_type = sm_flags.supports_dynamic_type();
    let fe_no_auto_dynamic =
        decl_utils::attributes_mem(sn::user_attributes::NO_AUTO_DYNAMIC, sm_attributes);
    let fe_no_auto_likes = no_auto_likes
        || decl_utils::attributes_mem(sn::user_attributes::NO_AUTO_LIKES, sm_attributes);
    let cannot_override = match this_class {
        Some(c) => {
            c.is_final
                || sm_flags.is_final()
                || *sm_visibility == oxidized::ast_defs::Visibility::Private
                    && !(c.kind == ClassishKind::Ctrait)
        }
        None => true,
    };
    FunElt {
        module: None,
        package: None,
        pos: pos.clone(),
        internal: false,
        deprecated: None,
        ty: if !fe_no_auto_dynamic
            && pessimize::implicit_sdt_for_class::<Provider>(ctx, this_class)
        {
            pessimize::pessimise_fun_type::<Provider>(
                if sm_flags.is_abstract() {
                    FunKind::AbstractMethod
                } else {
                    FunKind::ConcreteMethod
                },
                this_class,
                fe_no_auto_likes,
                cannot_override,
                ctx,
                pos,
                sm_type,
            )
        } else {
            sm_type.clone()
        },
        php_std_lib: false,
        support_dynamic_type,
        no_auto_dynamic: fe_no_auto_dynamic,
        no_auto_likes: fe_no_auto_likes,
        gated_by_feature_flag: None,
        package_requirement: sm_package_requirement.clone(),
    }
}
