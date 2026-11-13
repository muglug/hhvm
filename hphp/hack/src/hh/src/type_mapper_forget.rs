// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `type_mapper_forget.ml`. See `hh/PORTING.md`.
//!
//! The class `forget_tyvar_mapper` inherits `deep_type_mapper`, then
//! `constraint_type_mapper` and `internal_type_mapper` (each of which
//! inherits the previous one): it is [`ForgetTyvarMapper`], which implements
//! [`InternalTypeMapper`] and overrides `on_tvar`, `on_tunion` and
//! `on_tintersection`. Its two extra public methods (`recurse_opt`,
//! `recurse_internal_type_opt`) and its private one (`result_opt`) are
//! inherent methods. The class type `forget_tyvar_mapper_type` is the list of
//! those methods (see `crate::type_mapper_generic`).
//!
//! As in OCaml, the environment of the mapper ([`Env`]) is threaded through
//! the traversal, except by `on_tunion` and `on_tintersection`, which map
//! every element in the environment they were given and return that
//! environment unchanged; `recurse_opt` and `recurse_internal_type_opt` do
//! not return the environment either.

use crate::tvid;
use crate::type_mapper_generic::InternalTypeMapper;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::mk;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;

#[derive(Clone, Debug)]
pub struct Env {
    /// the tyvar to be removed
    pub tyvar: tvid::T,
    /// why did we need to forget this type?
    pub forget_reason: Option<Reason>,
}

pub fn make_env(tyvar: tvid::T) -> Env {
    let forget_reason = None;
    Env {
        tyvar,
        forget_reason,
    }
}

/// Type mapper which forgets a type variable, i.e. removes all occurrences of a type variable
#[derive(Clone, Copy, Debug, Default)]
pub struct ForgetTyvarMapper;

impl ForgetTyvarMapper {
    /// `method private result_opt`
    fn result_opt<A>(&self, env: &Env, x: A) -> Option<A> {
        match env.forget_reason {
            Some(_) => None,
            None => Some(x),
        }
    }

    pub fn recurse_opt(&mut self, env: &Env, locl_ty: Ty) -> Option<Ty> {
        let mut env = env.clone();
        let locl_ty = self.on_type(&mut env, locl_ty);
        self.result_opt(&env, locl_ty)
    }

    pub fn recurse_internal_type_opt(
        &mut self,
        env: &Env,
        ity: InternalType,
    ) -> Option<InternalType> {
        let mut env = env.clone();
        let ity = self.on_internal_type(&mut env, ity);
        self.result_opt(&env, ity)
    }
}

impl InternalTypeMapper<Env> for ForgetTyvarMapper {
    fn on_tvar(&mut self, env: &mut Env, r: Reason, var: tvid::T) -> Ty {
        if tvid::equal(var, env.tyvar) {
            // `({ env with forget_reason = Some r }, mk (r, Tunion []))`
            env.forget_reason = Some(r.clone());
            mk((r, Ty_::Tunion(vec![])))
        } else {
            mk((r, Ty_::Tvar(var)))
        }
    }

    fn on_tunion(&mut self, env: &mut Env, r: Reason, tyl: Vec<Ty>) -> Ty {
        // Every element is mapped in `env`; the environments this gives are
        // dropped, and `env` is returned as it is.
        let tyl = tyl
            .into_iter()
            .filter_map(|x| {
                let mut env = env.clone();
                let ty = self.on_type(&mut env, x);
                self.recurse_opt(&env, ty)
            })
            .collect();
        mk((r, Ty_::Tunion(tyl)))
    }

    fn on_tintersection(&mut self, env: &mut Env, r: Reason, tyl: Vec<Ty>) -> Ty {
        let tyl = tyl
            .into_iter()
            .filter_map(|x| {
                let mut env = env.clone();
                let ty = self.on_type(&mut env, x);
                self.recurse_opt(&env, ty)
            })
            .collect();
        mk((r, Ty_::Tintersection(tyl)))
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;
    use oxidized::pos::Pos;

    use super::*;
    use crate::typing_defs_core::TupleExtra;
    use crate::typing_defs_core::TupleType;
    use crate::typing_defs_core::get_node;
    use crate::typing_defs_core::nonexact;

    fn r() -> Reason {
        crate::typing_reason::none()
    }

    fn var(n: isize) -> Ty {
        mk((r(), Ty_::Tvar(n)))
    }

    fn int() -> Ty {
        mk((r(), Ty_::Tprim(Tprim::Tint)))
    }

    fn union(tyl: Vec<Ty>) -> Ty {
        mk((r(), Ty_::Tunion(tyl)))
    }

    fn tuple(tyl: Vec<Ty>) -> Ty {
        mk((
            r(),
            Ty_::Ttuple(TupleType {
                required: tyl,
                optional: vec![],
                extra: TupleExtra::Tvariadic(union(vec![])),
            }),
        ))
    }

    fn class(tyl: Vec<Ty>) -> Ty {
        mk((
            r(),
            Ty_::Tclass((Pos::NONE, "\\C".to_string()), nonexact(), tyl),
        ))
    }

    fn union_elements(ty: &Ty) -> Vec<Ty> {
        match get_node(ty) {
            Ty_::Tunion(tyl) => tyl.clone(),
            _ => panic!("not a union"),
        }
    }

    #[test]
    fn the_variable_becomes_nothing_and_is_recorded() {
        let mut env = make_env(1);
        let ty = ForgetTyvarMapper.on_type(&mut env, var(1));
        assert!(union_elements(&ty).is_empty());
        assert!(env.forget_reason.is_some());
        let mut env = make_env(1);
        let ty = ForgetTyvarMapper.on_type(&mut env, var(2));
        assert!(matches!(get_node(&ty), Ty_::Tvar(2)));
        assert!(env.forget_reason.is_none());
    }

    #[test]
    fn union_elements_that_mention_the_variable_are_dropped() {
        // int | C<#1> | #2  ~>  int | #2, and the union does not report
        // that it forgot something
        let mut env = make_env(1);
        let ty = union(vec![int(), class(vec![var(1)]), var(2)]);
        let ty = ForgetTyvarMapper.on_type(&mut env, ty);
        let tyl = union_elements(&ty);
        assert_eq!(tyl.len(), 2);
        assert!(matches!(get_node(&tyl[0]), Ty_::Tprim(Tprim::Tint)));
        assert!(matches!(get_node(&tyl[1]), Ty_::Tvar(2)));
        assert!(env.forget_reason.is_none());
    }

    #[test]
    fn a_reason_found_before_a_union_empties_it() {
        // In (#1, int | string) the tuple threads the environment: when the
        // union is reached the variable has been forgotten already, and
        // `recurse_opt` drops every element of the union.
        let mut env = make_env(1);
        let ty = tuple(vec![var(1), union(vec![int(), int()])]);
        let ty = ForgetTyvarMapper.on_type(&mut env, ty);
        match get_node(&ty) {
            Ty_::Ttuple(TupleType { required, .. }) => {
                assert!(union_elements(&required[0]).is_empty());
                assert!(union_elements(&required[1]).is_empty());
            }
            _ => panic!("not a tuple"),
        }
        assert!(env.forget_reason.is_some());
    }

    #[test]
    fn recurse_opt_does_not_change_the_environment() {
        let mut mapper = ForgetTyvarMapper;
        let env = make_env(1);
        assert!(mapper.recurse_opt(&env, class(vec![var(1)])).is_none());
        assert!(env.forget_reason.is_none());
        assert!(mapper.recurse_opt(&env, class(vec![var(3)])).is_some());
        let ity = InternalType::LoclType(var(1));
        assert!(mapper.recurse_internal_type_opt(&env, ity).is_none());
        let ity = InternalType::LoclType(int());
        assert!(mapper.recurse_internal_type_opt(&env, ity).is_some());
    }
}
