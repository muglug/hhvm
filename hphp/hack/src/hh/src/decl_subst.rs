// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_subst.ml`. See `hh/PORTING.md`.

use hash::IndexMap;
use pos::TypeName;
use ty::decl::Tparam;
use ty::decl::Ty;
use ty::decl::subst::Subst;
use ty::reason::Reason;

use crate::ctx::R;

/// `decl_ty SMap.t`. Decl data stays in the hackrs representation: this is the
/// type of `ty::decl::SubstContext::subst`, a map from the name of a type
/// parameter to the decl type that replaces it.
pub type DeclSubst = Subst<R>;

/// `'ty Typing_defs.tparam`, of which the functions below only read the name.
/// The type parameters of declarations are hackrs's (`ty::decl::Tparam`),
/// those of localized function types are oxidized's.
pub trait TpName {
    /// `snd t.tp_name`
    fn tp_name(&self) -> &str;
}

impl<TY> TpName for Tparam<R, TY> {
    fn tp_name(&self) -> &str {
        self.name.id_ref().as_str()
    }
}

impl TpName for oxidized::typing_defs_core::Tparam {
    fn tp_name(&self) -> &str {
        &self.name.1
    }
}

impl<TP: TpName> TpName for &TP {
    fn tp_name(&self) -> &str {
        (**self).tp_name()
    }
}

// Builds a substitution out of a list of type parameters and a list of types.
//
// Typical use-case:
//   class Y<T> { ... }
//   class X extends Y<int>
//
// To build the type of X, we need to replace all the occurrences of T in Y by
// int. The function make_subst, builds the substitution (the map associating
// types to a type parameter name), in this case, it would build the map(T =>
// int).

pub fn make_locl<TP: TpName>(
    tparams: &[TP],
    tyl: &[oxidized::typing_defs_core::Ty],
) -> im::OrdMap<String, oxidized::typing_defs_core::Ty> {
    let mut subst = im::OrdMap::new();
    let mut tyl = tyl;
    for t in tparams {
        match tyl {
            [] => {}
            [ty, rl @ ..] => {
                subst.insert(t.tp_name().to_string(), ty.clone());
                tyl = rl;
            }
        }
    }
    subst
}

pub fn make_decl<TP: TpName>(tparams: &[TP], tyl: &[Ty<R>]) -> DeclSubst {
    // We tolerate missing types in silent_mode. When that happens, we bind
    // all the parameters we can, and bind the remaining ones to "Tany".
    //
    // (`ty::decl::subst::Subst::new` does the same for hackrs's own type
    // parameters.)
    let mut subst: IndexMap<TypeName, Ty<R>> = IndexMap::default();
    let mut tyl = tyl;
    for t in tparams {
        let ty = match tyl {
            [] => Ty::any(R::none()),
            [ty, rl @ ..] => {
                tyl = rl;
                ty.clone()
            }
        };
        subst.insert(TypeName::new(t.tp_name()), ty);
    }
    Subst(subst)
}

#[cfg(test)]
mod tests {
    use pos::BPos;
    use pos::Positioned;
    use ty::decl::Prim;
    use ty::decl::Ty_;

    use super::*;

    fn tparam(name: &str) -> Tparam<R, Ty<R>> {
        Tparam {
            variance: oxidized::ast_defs::Variance::Invariant,
            name: Positioned::new(BPos::none(), TypeName::new(name)),
            constraints: Box::new([]),
            reified: oxidized::aast_defs::ReifyKind::Erased,
            user_attributes: Box::new([]),
        }
    }

    #[test]
    fn make_decl_binds_missing_arguments_to_any() {
        let tparams = [tparam("Ta"), tparam("Tb"), tparam("Tc")];
        let int = Ty::prim(R::none(), Prim::Tint);
        let string = Ty::prim(R::none(), Prim::Tfloat);
        let subst = make_decl(&tparams, &[int.clone(), string.clone()]);
        assert_eq!(subst.0.len(), 3);
        assert_eq!(subst.0.get(&TypeName::new("Ta")), Some(&int));
        assert_eq!(subst.0.get(&TypeName::new("Tb")), Some(&string));
        assert!(matches!(
            subst.0.get(&TypeName::new("Tc")).map(|ty| ty.node_ref()),
            Some(Ty_::Tany)
        ));
        // The same thing hackrs builds for its own type parameters.
        assert_eq!(subst, Subst::new(&tparams, &[int.clone(), string]));
        // Arguments in excess are dropped.
        let subst = make_decl(&tparams[..1], &[int.clone(), int.clone()]);
        assert_eq!(subst.0.len(), 1);
    }

    #[test]
    fn make_locl_drops_parameters_without_argument() {
        use oxidized::typing_defs_core as tdc;
        use oxidized::typing_reason::Reason as LoclReason;
        let tparams = [tparam("Ta"), tparam("Tb")];
        let int = tdc::Ty(
            LoclReason::NoReason,
            Box::new(tdc::Ty_::Tprim(oxidized::aast_defs::Tprim::Tint)),
        );
        let subst = make_locl(&tparams, &[int.clone()]);
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.get("Ta"), Some(&int));
        assert_eq!(subst.get("Tb"), None);
    }
}
