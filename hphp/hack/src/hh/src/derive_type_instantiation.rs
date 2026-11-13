// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `derive_type_instantiation.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use ty::decl::ty as d;

use crate::typing_defs::*;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_make_type as make_type;
use crate::typing_phase;
use crate::typing_reason;

/// `module Instantiation`
pub mod instantiation {
    use crate::typing_defs::Ty;

    /// `type t = private { ... }`: the fields can be read, and the value is
    /// built by the functions of this module.
    #[derive(Clone, Debug)]
    pub struct T {
        pub this: Option<Ty>,
        pub subst: im::OrdMap<String, Ty>,
    }

    pub(super) fn empty() -> T {
        T {
            this: None,
            subst: im::OrdMap::new(),
        }
    }

    pub fn is_empty(t: &T) -> bool {
        let T { this, subst } = t;
        this.is_none() && subst.is_empty()
    }

    pub(super) fn add_this(ty: Ty, t: T) -> T {
        let T { subst, this: _ } = t;
        T {
            subst,
            this: Some(ty),
        }
    }

    pub(super) fn add(tparam: String, ty: Ty, t: T) -> T {
        let T { subst, this } = t;
        T {
            subst: subst.update(tparam, ty),
            this,
        }
    }
}

/// Given two types ty1 and ty2, assuming ty2 is an instantiation
/// of ty1, return the type substitution to apply to ty1 to obtain ty2.
/// This won't fail if ty2 is not an instantiation of ty1 but instead will return
/// a best effort substitution.
pub fn derive_instantiation(
    env: &mut Env,
    uninstantiated: &DeclTy,
    instantiated: &Ty,
) -> instantiation::T {
    fn derive_instantiation(
        uninstantiated: &DeclTy,
        instantiated: &Ty,
        env: &mut Env,
        subst_acc: instantiation::T,
    ) -> instantiation::T {
        let instantiated = env::expand_type(env, instantiated.clone());
        match (uninstantiated.node_ref(), get_node(&instantiated)) {
            // base cases: Tgeneric, Tthis
            (DeclTy_::Tgeneric(lname), Ty_::Tgeneric(rname)) if lname.as_str() == rname => {
                subst_acc
            }
            (DeclTy_::Tgeneric(name), _) => {
                instantiation::add(name.as_str().to_string(), instantiated.clone(), subst_acc)
            }
            (DeclTy_::Tthis, _) => instantiation::add_this(instantiated.clone(), subst_acc),
            // Strip all like types and supportdyn on both sides
            (DeclTy_::Tlike(ty), _) => derive_instantiation(ty, &instantiated, env, subst_acc),
            (_, Ty_::Tunion(tyl)) if tyl.iter().any(is_dynamic) => {
                let tyl: Vec<Ty> = tyl.iter().filter(|ty| !is_dynamic(ty)).cloned().collect();
                derive_instantiation(
                    uninstantiated,
                    &make_type::union(typing_reason::none(), tyl),
                    env,
                    subst_acc,
                )
            }
            (DeclTy_::Tapply(lname_args), _)
                if lname_args.1.len() == 1
                    && lname_args.0.id_ref().as_str() == sn::classes::SUPPORT_DYN =>
            {
                derive_instantiation(&lname_args.1[0], &instantiated, env, subst_acc)
            }
            (_, Ty_::Tnewtype(rname, rargs, _))
                if rargs.len() == 1 && rname == sn::classes::SUPPORT_DYN =>
            {
                derive_instantiation(uninstantiated, &rargs[0], env, subst_acc)
            }
            // All other recursive cases
            (DeclTy_::Tapply(lname_ltargs), Ty_::Tclass((_, rname), _, rtargs))
                if lname_ltargs.0.id_ref().as_str() == rname =>
            {
                derive_instantiation_list(&lname_ltargs.1, rtargs, env, subst_acc)
            }
            (DeclTy_::Tapply(lname_ltargs), Ty_::Tnewtype(rname, rtargs, _))
                if lname_ltargs.0.id_ref().as_str() == rname =>
            {
                derive_instantiation_list(&lname_ltargs.1, rtargs, env, subst_acc)
            }
            (DeclTy_::Trefinement(refinement), _) => {
                derive_instantiation(&refinement.ty, &instantiated, env, subst_acc)
            }
            (DeclTy_::Toption(lty), Ty_::Toption(rty))
            | (DeclTy_::TclassPtr(lty), Ty_::TclassPtr(rty)) => {
                derive_instantiation(lty, rty, env, subst_acc)
            }
            (
                DeclTy_::Ttuple(ltuple),
                Ty_::Ttuple(TupleType {
                    required: rtyl,
                    optional: ropt,
                    extra: rextra,
                }),
            ) => {
                let d::TupleType(ltyl, lopt, lextra) = &**ltuple;
                let subst_acc = derive_instantiation_list(ltyl, rtyl, env, subst_acc);
                let subst_acc = derive_instantiation_list(lopt, ropt, env, subst_acc);
                match (lextra, rextra) {
                    (d::TupleExtra::Tvariadic(lvar), TupleExtra::Tvariadic(rvar)) => {
                        derive_instantiation(lvar, rvar, env, subst_acc)
                    }
                    (d::TupleExtra::Tsplat(lty), TupleExtra::Tsplat(rty)) => {
                        derive_instantiation(lty, rty, env, subst_acc)
                    }
                    (_, TupleExtra::Tvariadic(_) | TupleExtra::Tsplat(_)) => subst_acc,
                }
            }
            (
                DeclTy_::Tshape(lshape),
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: _,
                    unknown_value: rty,
                    fields: rfields,
                })),
            ) if matches!(&**lshape, d::ShapeType::Simple(_)) => {
                let d::ShapeType::Simple(d::ShapeTypeSimple(lty, lfields)) = &**lshape else {
                    unreachable!()
                };
                let subst_acc = derive_instantiation(lty, rty, env, subst_acc);
                // `TShapeMap.fold`: the fields of the declared shape in the
                // order of their keys.
                let mut subst_acc = subst_acc;
                for (key, sft) in lfields {
                    let key = typing_phase::tshape_field_of_decl(key, sft);
                    match rfields.get(&key) {
                        None => {}
                        Some(ShapeFieldType { ty: rty, .. }) => {
                            subst_acc = derive_instantiation(&sft.ty, rty, env, subst_acc)
                        }
                    }
                }
                subst_acc
            }
            (
                DeclTy_::Tfun(lft),
                Ty_::Tfun(rft),
            ) => {
                let FunType {
                    params: rparams,
                    ret: rret,
                    ..
                } = &**rft;
                let lparams: Vec<DeclTy> = lft.params.iter().map(|p| p.ty.clone()).collect();
                let rparams: Vec<Ty> = rparams.iter().map(|p| p.type_.clone()).collect();
                let subst_acc = derive_instantiation_list(&lparams, &rparams, env, subst_acc);
                derive_instantiation(&lft.ret, rret, env, subst_acc)
            }
            (DeclTy_::Tunion(ltyl), Ty_::Tunion(rtyl))
            | (DeclTy_::Tintersection(ltyl), Ty_::Tintersection(rtyl)) => {
                derive_instantiation_list(ltyl, rtyl, env, subst_acc)
            }
            (DeclTy_::TvecOrDict(lty1_lty2), Ty_::TvecOrDict(rty1, rty2)) => {
                let (lty1, lty2) = &**lty1_lty2;
                let subst_acc = derive_instantiation(lty1, rty1, env, subst_acc);
                derive_instantiation(lty2, rty2, env, subst_acc)
            }
            (DeclTy_::Taccess(ltaccess), Ty_::Taccess(TaccessType(rty, (_, rname))))
                if ltaccess.type_const.id_ref().as_str() == rname =>
            {
                derive_instantiation(&ltaccess.ty, rty, env, subst_acc)
            }
            _ => subst_acc,
        }
    }
    fn derive_instantiation_list(
        utyl: &[DeclTy],
        ityl: &[Ty],
        env: &mut Env,
        subst_acc: instantiation::T,
    ) -> instantiation::T {
        let ulen = utyl.len();
        let ilen = ityl.len();
        let (utyl, ityl) = if ulen < ilen {
            (utyl, &ityl[..ulen])
        } else if ulen > ilen {
            (&utyl[..ilen], ityl)
        } else {
            (utyl, ityl)
        };
        let mut subst_acc = subst_acc;
        for (uninstantiated, instantiated) in utyl.iter().zip(ityl) {
            subst_acc = derive_instantiation(uninstantiated, instantiated, env, subst_acc)
        }
        subst_acc
    }
    derive_instantiation(uninstantiated, instantiated, env, instantiation::empty())
}
