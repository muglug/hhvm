// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `type_force_lazy_values.ml`. See `hh/PORTING.md`.

use crate::type_mapper_generic::DeepTypeMapper;
use crate::type_mapper_generic::InternalTypeMapper;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::Ty;
use crate::typing_reason;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;

pub fn locl_ty(ty: Ty) -> Ty {
    struct Visitor;
    impl DeepTypeMapper<()> for Visitor {
        fn on_reason(&mut self, _env: &mut (), r: Reason) -> Reason {
            typing_reason::force_lazy_values(&r)
        }
    }
    let mut visitor = Visitor;
    visitor.on_type(&mut (), ty)
}

pub fn internal_type(ty: InternalType) -> InternalType {
    struct Visitor;
    impl InternalTypeMapper<()> for Visitor {
        fn on_reason(&mut self, _env: &mut (), r: Reason) -> Reason {
            typing_reason::force_lazy_values(&r)
        }
    }
    let mut visitor = Visitor;
    visitor.on_internal_type(&mut (), ty)
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use oxidized::ast_defs::Tprim;

    use super::*;
    use crate::typing_defs_constraints::ConstraintType_;
    use crate::typing_defs_constraints::constraint_ty_compare;
    use crate::typing_defs_constraints::mk_constraint_type;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::compare_locl_ty;
    use crate::typing_defs_core::mk;

    fn sample() -> Ty {
        let int = mk((typing_reason::none(), Ty_::Tprim(Tprim::Tint)));
        let var = mk((typing_reason::none(), Ty_::Tvar(3)));
        mk((
            typing_reason::none(),
            Ty_::Tunion(vec![
                mk((typing_reason::none(), Ty_::Toption(int.clone()))),
                mk((typing_reason::none(), Ty_::TvecOrDict(int, var))),
            ]),
        ))
    }

    #[test]
    fn locl_ty_gives_the_same_type() {
        let ty = sample();
        let forced = locl_ty(ty.clone());
        assert_eq!(compare_locl_ty(None, &ty, &forced), Ordering::Equal);
    }

    #[test]
    fn internal_type_gives_the_same_type() {
        let ty = sample();
        match internal_type(InternalType::LoclType(ty.clone())) {
            InternalType::LoclType(forced) => {
                assert_eq!(compare_locl_ty(None, &ty, &forced), Ordering::Equal)
            }
            InternalType::ConstraintType(_) => panic!("expected a locl type"),
        }
        let cty = mk_constraint_type((
            typing_reason::none(),
            ConstraintType_::ThasConst {
                name: "C".to_string(),
                ty,
            },
        ));
        match internal_type(InternalType::ConstraintType(cty.clone())) {
            InternalType::ConstraintType(forced) => {
                assert_eq!(constraint_ty_compare(None, &cty, &forced), Ordering::Equal)
            }
            InternalType::LoclType(_) => panic!("expected a constraint type"),
        }
    }
}
