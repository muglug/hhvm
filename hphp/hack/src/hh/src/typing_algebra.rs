// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_algebra.ml`. See `hh/PORTING.md`.

use crate::typing_defs_core::Ty;
/// `module TySet = Typing_set`
use crate::typing_set as ty_set;

/// Factorize common types, for example
///   (A | B) & (A | C) = A | (B & C)
/// and
///   (A | B | C1 | D1) & (A | B | C2 | D2) = A | B | ((C1 | D1) & (C2 | D2))
///
/// return the common types, followed by the unique types from each input list
pub fn factorize_common_types(tyl1: &[Ty], tyl2: &[Ty]) -> (Vec<Ty>, Vec<Ty>, Vec<Ty>) {
    let tys1 = ty_set::of_list(tyl1.to_vec());
    let tys2 = ty_set::of_list(tyl2.to_vec());
    let common_tys = ty_set::inter(&tys1, &tys2);
    let tys1_ = ty_set::diff(&tys1, &common_tys);
    let tys2_ = ty_set::diff(&tys2, &common_tys);
    let tyl1_ = ty_set::elements(&tys1_);
    let tyl2_ = ty_set::elements(&tys2_);
    let common_tyl = ty_set::elements(&common_tys);
    (common_tyl, tyl1_, tyl2_)
}


#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::mk;
    use crate::typing_reason;

    fn prim(p: Tprim) -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(p)))
    }

    #[test]
    fn common_types_come_first_then_the_rest_of_each_list() {
        let (int, num, float, bool) = (
            prim(Tprim::Tint),
            prim(Tprim::Tnum),
            prim(Tprim::Tfloat),
            prim(Tprim::Tbool),
        );
        let (common, rest1, rest2) = factorize_common_types(
            &[num.clone(), int.clone(), float.clone()],
            &[int.clone(), bool.clone(), num.clone()],
        );
        // In the order of the sets (`compare_locl_ty`), not of the lists.
        assert_eq!(common, ty_set::elements(&ty_set::of_list(vec![int, num])));
        assert_eq!(rest1, vec![float]);
        assert_eq!(rest2, vec![bool]);
    }
}
