// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_kinding_defs.ml`. See `hh/PORTING.md`.
//!
//! `oxidized::typing_kinding_defs::Kind` is not re-exported: its bounds are
//! `oxidized::typing_set::TySet`, a `BTreeSet` of `oxidized::typing_defs::Ty`,
//! and that `Ty` has the constructors of declared types only (no `Tvar`,
//! `Tclass`, `Tnewtype`, ...), whereas the OCaml bounds are `locl_ty`. `Kind`
//! is therefore defined here, field for field, over `Typing_set.t`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::typing_defs::attributes;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::PosId;
use crate::typing_set as ty_set;

pub type TparamBounds = ty_set::T;

/// The kind of a type, used to collect information about type paramters.
#[derive(Clone, Debug, Hash)]
pub struct Kind {
    pub lower_bounds: TparamBounds,
    pub upper_bounds: TparamBounds,
    /// = Reified if generic parameter is marked `reify`, = Erased otherwise
    pub reified: aast::ReifyKind,
    /// Set if generic parameter has attribute <<__Enforceable>>
    pub enforceable: bool,
    /// Set if generic parameter has attribute <<__Newable>>
    pub newable: bool,
    /// Set if class is marked <<__SupportDynamicType>> and
    /// generic parameter does *not* have attribute <<__NoRequireDynamic>>
    pub require_dynamic: bool,
    pub rank: isize,
}

pub type NamedKind = (PosId, Kind);

/// This can be used in situations where we don't have a name for a type
/// parameter at hand. All error functions must be aware of this and not print the dummy name.
pub fn dummy_name() -> PosId {
    (PosOrDecl::NONE, String::new())
}

/// Turns a decl_tparam into a kind, throwing away all bounds in the process
pub fn kind_of_decl_tparam_no_bounds(
    rank: Option<isize>,
    require_dynamic: Option<bool>,
    decl_tparam: &DeclTparam,
) -> Kind {
    let rank = rank.unwrap_or(0);
    let require_dynamic = require_dynamic.unwrap_or(false);
    let DeclTparam {
        reified,
        user_attributes: tp_user_attributes,
        ..
    } = decl_tparam;
    // `Attributes.mem` is over `Typing_defs.user_attribute`: the attributes
    // of a declared type parameter are converted to that form.
    let tp_user_attributes = tp_user_attributes.clone().to_oxidized();
    let enforceable = attributes::mem(sn::user_attributes::ENFORCEABLE, &tp_user_attributes);
    let newable = attributes::mem(sn::user_attributes::NEWABLE, &tp_user_attributes);

    Kind {
        lower_bounds: ty_set::T::default(),
        upper_bounds: ty_set::T::default(),
        reified: *reified,
        enforceable,
        newable,
        require_dynamic,
        rank,
    }
}

pub fn force_lazy_values(kind: Kind) -> Kind {
    let Kind {
        lower_bounds,
        upper_bounds,
        reified,
        enforceable,
        newable,
        require_dynamic,
        rank,
    } = kind;
    Kind {
        lower_bounds: ty_set::force_lazy_values(lower_bounds),
        upper_bounds: ty_set::force_lazy_values(upper_bounds),
        reified,
        enforceable,
        newable,
        require_dynamic,
        rank,
    }
}
