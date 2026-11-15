// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_escape.ml`. See `hh/PORTING.md`.
//!
//! This module contains functions to clear rigid type variables from types
//! and from the inference environment. We say that a type variable is
//! "rigid" when it only unifies with itself. Examples of such type variables
//! include type parameters and expression-dependent types. Any such rigid
//! type variable needs to be cleared after type-checking lambdas & loops
//! for soundness.
//!
//! # The refresh environment
//!
//! The OCaml `refresh_env` record (the typing environment and the state of a
//! refresh) is threaded through every `refresh_*` function: here it is
//! [`RefreshEnv`], owned by [`refresh_env_and_type`] and passed as
//! `&mut RefreshEnv`; a function that returns `(renv, x, changed)` returns
//! `(x, changed)`. No OCaml function of this module goes on with an older
//! `renv` than the last one it got, except for the fields it saves and puts
//! back explicitly (`elim_bogus_taccess`, `eliminating`), which the port does
//! the same way.
//!
//! The mli makes `snapshot` and `escaping_rigid_tvars` abstract; the other
//! definitions are private.

use std::cmp::Ordering;
use std::rc::Rc;

use oxidized::ast_defs::Variance;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::ast_defs;
use crate::expression_id;
use crate::internal_type_set as ity_set;
use crate::local_id;
use crate::markdown_lite;
use crate::pos_or_decl;
use crate::rt::ocaml_option;
use crate::s_map;
use crate::tvid;
use crate::type_parameter_env;
use crate::typing_defs::dependent_kind;
use crate::typing_defs_constraints::CanIndex;
use crate::typing_defs_constraints::CanIndexAssign;
use crate::typing_defs_constraints::CanTraverse;
use crate::typing_defs_constraints::ConstraintType;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::Destructure;
use crate::typing_defs_constraints::HasMember;
use crate::typing_defs_constraints::HasTypeMember;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DependentType;
use crate::typing_defs_core::FunParam;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TaccessType;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::find_locl_ty;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::locl_subst;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::phys_equal;
use crate::typing_defs_core::t_shape_map;
use crate::typing_defs_core::with_reason;
use crate::typing_env as env_;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_error_utils;
use crate::typing_intersection;
use crate::typing_kinding_defs;
use crate::typing_lenv;
use crate::typing_local_types;
use crate::typing_log;
use crate::typing_reason as reason;
use crate::typing_set as ty_set;
use crate::typing_union;
use crate::typing_utils as t_utils;

/// `S_set.t`
type SSet = im::OrdSet<String>;
/// `'a S_map.t`
type SMap<V> = crate::type_parameter_env::SMap<V>;

// Here is an example program that would bogusly type check if we did not
// clear rigid type variables properly:
//
//    $f = (mixed $arg) ==> ($arg as Box<_>);
//    $bs = $f($str_box as mixed) : Box<T#1>
//    $bi = $f($int_box as mixed) : Box<T#1>  // unsound!
//    $bi->set($bs->get());  // should not work
//
// We do not want the type of the two calls to $f to unify; this module
// prevents unsoundness by clearing T#1 from the result of the lambda.
// In this particular case, an error is generated.

// TODO(T92111151): Adding existential types to Hack locl types might
// help in simplifying the logic below by harnessing Typing_subtype.
//
// Namely, elimination of a rigid type T#1 in a type C[T#1] would
// simply quantify T#1 away (preserving its constraints).

#[derive(Clone, Debug)]
pub enum RigidTvar {
    RtvTparam(String),
    RtvDependent(expression_id::T),
}

// ********************************************************************
// Eliminating rigid type variables
// ********************************************************************

// Many languages cannot "eliminate" escaping types and will simply raise
// an error when such an escape happens. In Hack, we can do a bit better
// using subtyping. For example, if a lambda returns [vec<T#1>] where
// T#1 must be eliminated, we can type the return value as [vec<mixed>]
// instead, or [vec<Foo>] if we happen to know that T#1 <: Foo. More
// generally, a type T to be eliminated can be replaced with the
// intersection of its upper bounds in covariant position, and with the
// union of its lower bounds in contravariant positions. This replacement
// is what the [eliminate] function performs.
//
// Because Hack is effectful, it is not sufficient to eliminate rigid type
// variables in the return type of lambdas, we must also make sure they
// do not escape in bounds of type variables that existed before typing
// a lambda. For example, consider:
//
//   $v = Vector{}
//   $f = (mixed $x) ==> {
//     invariant($x is Box<_>, "");
//     $v[] = $x->get();
//   }
//   // we do not want $v : Vector<T#1>; instead we want Vector<mixed>
//
// Improper rigid type variables handling would lead $v to have type
// Vector<T#1> leaving the door open to soundness holes. To prevent this
// problem we provide [refresh_*] functions that act on the inference
// environment. When doing so the question of the variance in constraints
// comes in.
//
// Inference can be understood as producing the following result: "under the
// constraints C on tyvars, the program P has type T"; which we will write
// more compactly as [C ==> P:T]. You can see that C stands on the LHS of an
// implication, i.e., it is in *contravariant* position.  This amounts to
// remarking that if C' is such that C'[tvs] ==> C[tvs] for all tvs then
// [C ==> P:T] implies [C' ==> P:T]. Consequently, it is always sound to
// make a constraints set stronger (harder to satisfy). Concretely, if we
// have a type variable #2021 with constraint #2021 <: arraykey, we can
// soundly replace the constraint with #2021 <: int; that is: upper bounds
// of type variables are *contravariant*. Dually, lower bounds are
// *covariant*. This remark underpins the implementation of [refresh_tvar].

#[derive(Clone, Debug)]
pub struct ElimInfo {
    pub pos: PosOrDecl,
    pub upper_bounds: ty_set::T,
    pub lower_bounds: ty_set::T,
}

/// `rigid_tvar -> elim_info option`
pub type RemoveMap = Rc<dyn Fn(&RigidTvar) -> Option<ElimInfo>>;

#[derive(Clone)]
struct RefreshEnv {
    /// the underlying typing env
    env: Env,
    /// an accumulator used to remember all the type variabes
    /// that appeared when refreshing a type; the map is used as a
    /// set, and error callbacks are merely used for reporting
    tvars: tvid::map::T<reasons_callback::T>,
    /// the list of all the type parameters to eliminate with their
    /// bounds
    remove: RemoveMap,
    /// sometimes eliminating a rigid type is not possible and we must
    /// surface an error to the user
    on_error: reasons_callback::T,
    /// a string and position describing the language construct for which
    /// we are preventing escapes (e.g., "lambda")
    scope_kind: (String, Pos),
    /// a boolean indicating whether or not the elimination procedure
    /// should eliminate bogus Tgenerics of the form A::T where T is
    /// an abstract const type in A
    /// TODO(T91765587): kill bogus type access generics
    elim_bogus_taccess: bool,
    /// set of generic names currently being eliminated; used to
    /// detect cycles in self-referential type constant bounds
    eliminating: SSet,
}

/// refresh_ functions will return [Elim ...] when they eliminated a rigid
/// type variable from their result. [Unchanged] is returned when nothing
/// has changed in the data to refresh.
#[derive(Clone, Debug)]
enum Changed {
    Elim(PosOrDecl, String),
    Unchanged,
}

/// Using [with_default], all the refresh_ functions take care of returning
/// *exactly* their argument if the refreshing did not change anything.
///
/// I conjecture that this plays nice with the GC: if nothing changes all the
/// temporary fresh objects will sit root-less in the minor heap and get
/// collected for very cheap. If we instead used the fresh results as
/// replacements of the originals we would create roots for them and may
/// eventually have to collect the original copies with a constly compaction
/// of the major heap
fn with_default<A>(default: A, (res, changed): (A, Changed)) -> (A, Changed) {
    match changed {
        Changed::Elim(..) => (res, changed),
        Changed::Unchanged => (default, Changed::Unchanged),
    }
}

/// `( || )`: the first change.
fn or(ch1: Changed, ch2: Changed) -> Changed {
    match ch1 {
        Changed::Elim(..) => ch1,
        Changed::Unchanged => ch2,
    }
}

fn is_bogus_taccess(tp: &str) -> bool {
    // In typing_taccess.ml some type parameters of the form I::T are
    // generated when T is abstract; these types are bogus and should
    // be eliminated from our internal data structures but, in the
    // meantime, we cope with them here by ignoring them.
    // TODO(T91765587): kill bogus type access generics
    tp.contains("::") && tp.as_bytes()[0] != b'<'
}

fn eliminate(
    ty_orig: &Ty,
    rtv_pos: PosOrDecl,
    name: &str,
    ubs: &ty_set::T,
    lbs: &ty_set::T,
    renv: &mut RefreshEnv,
    v: Variance,
) -> (Ty, Changed) {
    let r = {
        let (what, wpos) = &renv.scope_kind;
        reason::rigid_tvar_escape((
            wpos.clone(),
            what.clone(),
            name.to_string(),
            get_reason(ty_orig).clone(),
        ))
    };
    match v {
        Variance::Contravariant => {
            let lbs = ty_set::elements(lbs);
            let lbty: Ty = typing_union::union_list(&mut renv.env, None, r.clone(), &lbs);
            // a type that depends on type variables to be eliminated may be
            // generated by the union computation; so we recursively eliminate
            // them
            let elim_bogus_taccess = renv.elim_bogus_taccess;
            renv.elim_bogus_taccess = true;
            let (lbty, _) = refresh_type(renv, v, lbty);
            let lbty = with_reason(lbty, r);
            renv.elim_bogus_taccess = elim_bogus_taccess;
            (lbty, Changed::Elim(rtv_pos, name.to_string()))
        }
        Variance::Covariant => {
            let ubs = ty_set::elements(ubs);
            let ubty: Ty = typing_intersection::intersect_list(&mut renv.env, r.clone(), &ubs);
            let elim_bogus_taccess = renv.elim_bogus_taccess;
            renv.elim_bogus_taccess = true;
            // ditto
            let (ubty, _) = refresh_type(renv, v, ubty);
            let ubty = with_reason(ubty, r);
            renv.elim_bogus_taccess = elim_bogus_taccess;
            (ubty, Changed::Elim(rtv_pos, name.to_string()))
        }
        Variance::Invariant => {
            let name = markdown_lite::md_codify(name);
            let snd_err = secondary::T::RigidTvarEscape { pos: rtv_pos, name };
            typing_error_utils::add_typing_error(
                &typing_error::apply_reasons(
                    snd_err,
                    reasons_callback::retain_code(renv.on_error.clone()),
                ),
                &renv.env,
            );
            (ty_orig.clone(), Changed::Unchanged)
        }
    }
}

fn refresh_type(renv: &mut RefreshEnv, v: Variance, ty_orig: Ty) -> (Ty, Changed) {
    let ty = env_::expand_type(&mut renv.env, ty_orig.clone());
    let r = get_reason(&ty).clone();
    let res = match get_node(&ty) {
        Ty_::Tany(_)
        | Ty_::Tnonnull
        | Ty_::Tdynamic(_)
        | Ty_::Tprim(_)
        | Ty_::Tneg(_)
        | Ty_::Tlabel(_) => (ty_orig.clone(), Changed::Unchanged),
        Ty_::Toption(ty1) => {
            let (ty1, changed) = refresh_type(renv, v, ty1.clone());
            (mk((r, Ty_::Toption(ty1))), changed)
        }
        Ty_::Tfun(ft) => {
            let param_v = ast_defs::swap_variance(v);
            // `List.map_env (renv, Unchanged) ft.ft_params ~f:ft_param`
            let mut changed = Changed::Unchanged;
            let mut ft_params = Vec::with_capacity(ft.params.len());
            for fp in ft.params.iter() {
                let (fp_type, changed_) = refresh_type(renv, param_v, fp.type_.clone());
                changed = or(changed, changed_);
                ft_params.push(FunParam {
                    type_: fp_type,
                    ..fp.clone()
                });
            }
            let (ft_ret, changed_) = refresh_type(renv, v, ft.ret.clone());
            (
                mk((
                    r,
                    Ty_::Tfun(std::rc::Rc::new(FunType {
                        params: ft_params,
                        ret: ft_ret,
                        ..FunType::clone(&ft)
                    })),
                )),
                or(changed, changed_),
            )
        }
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        }) => {
            let (t_required, changed) = refresh_types(renv, v, t_required);
            let (t_optional, changed1) = refresh_types(renv, v, t_optional);
            let (t_extra, changed2) = match t_extra {
                TupleExtra::Tvariadic(t_variadic) => {
                    let (t_variadic, changed) = refresh_type(renv, v, t_variadic.clone());
                    (TupleExtra::Tvariadic(t_variadic), changed)
                }
                TupleExtra::Tsplat(t_splat) => {
                    let (t_splat, changed) = refresh_type(renv, v, t_splat.clone());
                    (TupleExtra::Tsplat(t_splat), changed)
                }
            };
            (
                mk((
                    r,
                    Ty_::Ttuple(TupleType {
                        required: t_required,
                        optional: t_optional,
                        extra: t_extra,
                    }),
                )),
                or(changed, or(changed1, changed2)),
            )
        }
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: _,
            unknown_value: sk,
            fields: sm,
        })) => {
            // `TShapeMap.fold ... sm (renv, TShapeMap.empty, Unchanged)`, in
            // the order of the fields
            let mut sm_ = t_shape_map::T::new();
            let mut ch = Changed::Unchanged;
            for (
                sfn,
                ShapeFieldType {
                    optional: sft_optional,
                    ty: sft_ty,
                },
            ) in sm.iter()
            {
                let (sft_ty, ch_) = refresh_type(renv, v, sft_ty.clone());
                sm_.insert(
                    sfn.clone(),
                    ShapeFieldType {
                        optional: *sft_optional,
                        ty: sft_ty,
                    },
                );
                ch = or(ch, ch_);
            }
            (
                mk((
                    r,
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: TypeOrigin::MissingOrigin,
                        // TODO(shapes) refresh_type s_unknown_value
                        unknown_value: sk.clone(),
                        fields: sm_,
                    })),
                )),
                ch,
            )
        }
        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
            let (ss_elems, ch) = refresh_types(renv, v, ss_elems);
            (
                mk((
                    r,
                    Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })),
                )),
                ch,
            )
        }
        Ty_::Tvar(var) => {
            renv.tvars.insert(*var, renv.on_error.clone());
            (ty_orig.clone(), Changed::Unchanged)
        }
        Ty_::Tgeneric(name) => {
            // look if the Tgeneric has to go away and kill it using its
            // bounds if the variance of the current occurrence permits it
            match (renv.remove)(&RigidTvar::RtvTparam(name.clone())) {
                None => (ty_orig.clone(), Changed::Unchanged),
                Some(_) if renv.eliminating.contains(name) => (ty_orig.clone(), Changed::Unchanged),
                Some(_) if is_bogus_taccess(name) && !renv.elim_bogus_taccess => {
                    (ty_orig.clone(), Changed::Unchanged)
                }
                Some(ElimInfo {
                    pos,
                    lower_bounds: lbs,
                    upper_bounds: ubs,
                }) => {
                    let rtv_pos = if pos_or_decl::equal(&pos, &pos_or_decl::NONE) {
                        reason::to_pos(&r)
                    } else {
                        pos
                    };
                    // Keep a copy of the set of type parameters we are eliminating so
                    // we can pop the current name after it's been eliminated
                    let eliminating = renv.eliminating.clone();
                    renv.eliminating = renv.eliminating.update(name.clone());
                    let (ty, ch) = eliminate(&ty_orig, rtv_pos, name, &ubs, &lbs, renv, v);
                    renv.eliminating = eliminating;
                    (ty, ch)
                }
            }
        }
        Ty_::Tdependent(dt @ DependentType::DTexpr(id), ty1) => {
            let name = dependent_kind::to_string(dt);
            match (renv.remove)(&RigidTvar::RtvDependent(*id)) {
                None => {
                    let (ty1, ch1) = refresh_type(renv, v, ty1.clone());
                    (mk((r, Ty_::Tdependent(*dt, ty1))), ch1)
                }
                Some(_) if renv.eliminating.contains(&name) => {
                    (ty_orig.clone(), Changed::Unchanged)
                }
                Some(_) => {
                    let lbs = ty_set::empty();
                    let ubs = ty_set::singleton(ty1.clone());
                    let rtv_pos = reason::to_pos(&r);
                    // Keep a copy of the set of type parameters we are eliminating so
                    // we can pop the current name after it's been eliminated
                    let eliminating = renv.eliminating.clone();
                    renv.eliminating = renv.eliminating.update(name.clone());
                    let (ty, ch) = eliminate(&ty_orig, rtv_pos, &name, &ubs, &lbs, renv, v);
                    renv.eliminating = eliminating;
                    (ty, ch)
                }
            }
        }
        Ty_::Tunion(l) => {
            let (l, changed) = refresh_types(renv, v, l);
            match changed {
                Changed::Elim(..) => {
                    let ty: Ty = typing_union::union_list(&mut renv.env, None, r, &l);
                    (ty, changed)
                }
                Changed::Unchanged => (ty_orig.clone(), Changed::Unchanged),
            }
        }
        Ty_::Tintersection(l) => {
            let (l, changed) = refresh_types(renv, v, l);
            match changed {
                Changed::Elim(..) => {
                    let ty: Ty = typing_intersection::intersect_list(&mut renv.env, r, &l);
                    (ty, changed)
                }
                Changed::Unchanged => (ty_orig.clone(), Changed::Unchanged),
            }
        }
        Ty_::TvecOrDict(ty1, ty2) => {
            let (ty1, ch1) = refresh_type(renv, v, ty1.clone());
            let (ty2, ch2) = refresh_type(renv, v, ty2.clone());
            (mk((r, Ty_::TvecOrDict(ty1, ty2))), or(ch1, ch2))
        }
        Ty_::Taccess(TaccessType(ty1, id)) => {
            let (ty1, ch1) = refresh_type(renv, Variance::Invariant, ty1.clone());
            (mk((r, Ty_::Taccess(TaccessType(ty1, id.clone())))), ch1)
        }
        Ty_::Tnewtype(name, l, bnd) => {
            let tparams = env_::get_class_or_typedef_tparams(&renv.env, name);
            let (l, ch) = refresh_types_w_variance(renv, v, &tparams, l);
            (mk((r, Ty_::Tnewtype(name.clone(), l, bnd.clone()))), ch)
        }
        Ty_::Tclass((p, cid), e, l) => {
            let tparams = env_::get_class_or_typedef_tparams(&renv.env, cid);
            let (l, ch) = refresh_types_w_variance(renv, v, &tparams, l);
            (
                mk((r, Ty_::Tclass((p.clone(), cid.clone()), e.clone(), l))),
                ch,
            )
        }
        Ty_::TclassPtr(ty1) => {
            let (ty1, changed) = refresh_type(renv, v, ty1.clone());
            (mk((r, Ty_::TclassPtr(ty1))), changed)
        }
    };
    with_default(ty_orig, res)
}

fn refresh_types(renv: &mut RefreshEnv, v: Variance, l: &[Ty]) -> (Vec<Ty>, Changed) {
    // `go renv Unchanged l []`
    let mut changed = Changed::Unchanged;
    let mut acc = Vec::with_capacity(l.len());
    for ty in l {
        let (ty, changed_) = refresh_type(renv, v, ty.clone());
        changed = or(changed, changed_);
        acc.push(ty);
    }
    with_default(l.to_vec(), (acc, changed))
}

fn refresh_types_w_variance(
    renv: &mut RefreshEnv,
    v: Variance,
    tpl: &[DeclTparam],
    tl: &[Ty],
) -> (Vec<Ty>, Changed) {
    // `go renv Unchanged tpl tl []`: once the type parameters run out, the
    // remaining types are invariant.
    let mut changed = Changed::Unchanged;
    let mut acc = Vec::with_capacity(tl.len());
    let mut tpl = tpl.iter();
    for ty in tl {
        let v = match tpl.next() {
            None => Variance::Invariant,
            Some(tp) => match tp.variance {
                Variance::Invariant => Variance::Invariant,
                Variance::Covariant => v,
                Variance::Contravariant => ast_defs::swap_variance(v),
            },
        };
        let (ty, changed_) = refresh_type(renv, v, ty.clone());
        changed = or(changed, changed_);
        acc.push(ty);
    }
    with_default(tl.to_vec(), (acc, changed))
}

fn refresh_type_opt(renv: &mut RefreshEnv, v: Variance, tyo: &Option<Ty>) -> (Option<Ty>, Changed) {
    match tyo {
        None => (None, Changed::Unchanged),
        Some(ty) => {
            let (ty, ch) = refresh_type(renv, v, ty.clone());
            (Some(ty), ch)
        }
    }
}

fn refresh_ctype(
    renv: &mut RefreshEnv,
    v: Variance,
    cty_orig: ConstraintType,
) -> (ConstraintType, Changed) {
    let inv = Variance::Invariant;
    let ConstraintType(r, cty_) = &cty_orig;
    let r = r.clone();
    let res = match &**cty_ {
        ConstraintType_::ThasMember(hm) => {
            let HasMember {
                type_: hm_type,
                name: _,
                class_id: _,
                method: _,
            } = hm;
            let (hm_type, changed) = refresh_type(renv, inv, hm_type.clone());
            (
                mk_constraint_type((
                    r,
                    ConstraintType_::ThasMember(HasMember {
                        type_: hm_type,
                        ..hm.clone()
                    }),
                )),
                changed,
            )
        }
        ConstraintType_::ThasTypeMember(htm) => {
            let HasTypeMember {
                id: htm_id,
                lower: htm_lower,
                upper: htm_upper,
            } = htm;
            let v_ = ast_defs::swap_variance(v);
            let (htm_upper, ch1) = refresh_type(renv, v, htm_upper.clone());
            let (htm_lower, ch2) = refresh_type(renv, v_, htm_lower.clone());
            let htm = HasTypeMember {
                id: htm_id.clone(),
                lower: htm_lower,
                upper: htm_upper,
            };
            (
                mk_constraint_type((r, ConstraintType_::ThasTypeMember(htm))),
                or(ch1, ch2),
            )
        }
        ConstraintType_::TcanIndex(ci) => {
            let (ci_val, ch1) = refresh_type(renv, inv, ci.val.clone());
            let (ci_key, ch2) = refresh_type(renv, inv, ci.key.clone());
            (
                mk_constraint_type((
                    r,
                    ConstraintType_::TcanIndex(CanIndex {
                        val: ci_val,
                        key: ci_key,
                        ..ci.clone()
                    }),
                )),
                or(ch1, ch2),
            )
        }
        ConstraintType_::TcanIndexAssign(cia) => {
            let (cia_key, ch1) = refresh_type(renv, inv, cia.key.clone());
            let (cia_write, ch2) = refresh_type(renv, inv, cia.write.clone());
            let (cia_val, ch3) = refresh_type(renv, inv, cia.val.clone());
            (
                mk_constraint_type((
                    r,
                    ConstraintType_::TcanIndexAssign(CanIndexAssign {
                        key: cia_key,
                        write: cia_write,
                        val: cia_val,
                        ..cia.clone()
                    }),
                )),
                or(ch1, or(ch2, ch3)),
            )
        }
        ConstraintType_::TcanTraverse(ct) => {
            let (ct_val, ch1) = refresh_type(renv, inv, ct.val.clone());
            let (ct_key, ch2) = match &ct.key {
                None => (None, Changed::Unchanged),
                Some(ct_key) => {
                    let (ct_key, ch2) = refresh_type(renv, inv, ct_key.clone());
                    (Some(ct_key), ch2)
                }
            };
            (
                mk_constraint_type((
                    r,
                    ConstraintType_::TcanTraverse(CanTraverse {
                        val: ct_val,
                        key: ct_key,
                        ..ct.clone()
                    }),
                )),
                or(ch1, ch2),
            )
        }
        ConstraintType_::Tdestructure(Destructure {
            required: d_required,
            optional: d_optional,
            variadic: d_variadic,
            kind: d_kind,
        }) => {
            let (d_required, ch1) = refresh_types(renv, inv, d_required);
            let (d_optional, ch2) = refresh_types(renv, inv, d_optional);
            let (d_variadic, ch3) = refresh_type_opt(renv, inv, d_variadic);
            let des = Destructure {
                required: d_required,
                optional: d_optional,
                variadic: d_variadic,
                kind: *d_kind,
            };
            (
                mk_constraint_type((r, ConstraintType_::Tdestructure(des))),
                or(ch1, or(ch2, ch3)),
            )
        }
        ConstraintType_::TtypeSwitch {
            predicate,
            ty_true,
            ty_false,
        } => {
            let (ty_true, ch1) = refresh_type(renv, v, ty_true.clone());
            let (ty_false, ch2) = refresh_type(renv, v, ty_false.clone());
            (
                mk_constraint_type((
                    r,
                    ConstraintType_::TtypeSwitch {
                        predicate: predicate.clone(),
                        ty_true,
                        ty_false,
                    },
                )),
                or(ch1, ch2),
            )
        }
        ConstraintType_::ThasConst { name, ty } => {
            let (ty, changed) = refresh_type(renv, inv, ty.clone());
            (
                mk_constraint_type((
                    r,
                    ConstraintType_::ThasConst {
                        name: name.clone(),
                        ty,
                    },
                )),
                changed,
            )
        }
    };
    with_default(cty_orig, res)
}

/// The bounds that changed (`del`), and their refreshed versions (`add`, in
/// the order of the OCaml list: the last bound refreshed first).
fn refresh_bounds(
    renv: &mut RefreshEnv,
    v: Variance,
    tys: &ity_set::T,
) -> (ity_set::T, Vec<(InternalType, PosOrDecl, String)>) {
    // `ITySet.fold ... tys (renv, ITySet.empty, [])`, in increasing order;
    // `add` is built by consing.
    let mut del = ity_set::empty();
    let mut add = vec![];
    for ity in tys.iter() {
        match ity {
            InternalType::LoclType(lty) => {
                let (lty, changed) = refresh_type(renv, v, lty.clone());
                match changed {
                    Changed::Unchanged => {}
                    Changed::Elim(pos, name) => {
                        del = ity_set::add(ity.clone(), &del);
                        add.push((InternalType::LoclType(lty), pos, name));
                    }
                }
            }
            InternalType::ConstraintType(cty) => {
                let (cty, changed) = refresh_ctype(renv, v, cty.clone());
                match changed {
                    Changed::Unchanged => {}
                    Changed::Elim(pos, name) => {
                        del = ity_set::add(ity.clone(), &del);
                        add.push((InternalType::ConstraintType(cty), pos, name));
                    }
                }
            }
        }
    }
    add.reverse();
    (del, add)
}

fn refresh_tvar(tv: tvid::T, on_error: &reasons_callback::T, renv: &mut RefreshEnv) {
    // restore the error context of one local variable causing us to visit
    // this tvar
    renv.on_error = on_error.clone();
    let tv_ity = InternalType::LoclType(mk((reason::none(), Ty_::Tvar(tv))));
    let elim_on_error = |pos: PosOrDecl, name: &str| {
        let name = markdown_lite::md_codify(name);
        Some(reasons_callback::with_reasons(
            reasons_callback::retain_code(reasons_callback::retain_quickfixes(on_error.clone())),
            Lazy::new(move || {
                vec![Message(
                    pos,
                    format!("Could not remove rigid type variable {}", name).into(),
                )]
            }),
        ))
    };
    let e1 = {
        let ubs = env_::get_tyvar_upper_bounds(&renv.env, tv);
        let var = Variance::Contravariant;
        let (del, add) = refresh_bounds(renv, var, &ubs);
        if ity_set::is_empty(&del) && add.is_empty() {
            None
        } else {
            let ubs = env_::get_tyvar_upper_bounds(&renv.env, tv);
            let ubs = ity_set::diff(&ubs, &del);
            env_::set_tyvar_upper_bounds(&mut renv.env, tv, ubs);
            // `List.fold ~init:(env, []) ~f:add_bound add`: `ty_errs` is built
            // by consing.
            let mut ty_errs = vec![];
            for (ity, pos, name) in add {
                let ty_err: Option<typing_error::T> = t_utils::sub_type_i(
                    &mut renv.env,
                    None,
                    None,
                    tv_ity.clone(),
                    ity,
                    elim_on_error(pos, &name),
                );
                if let Some(ty_err) = ty_err {
                    ty_errs.push(ty_err)
                }
            }
            ty_errs.reverse();
            typing_error::multiple_opt(ty_errs)
        }
    };
    let e2 = {
        let lbs = env_::get_tyvar_lower_bounds(&renv.env, tv);
        let var = Variance::Covariant;
        let (del, add) = refresh_bounds(renv, var, &lbs);
        if ity_set::is_empty(&del) && add.is_empty() {
            None
        } else {
            let lbs = env_::get_tyvar_lower_bounds(&renv.env, tv);
            let lbs = ity_set::diff(&lbs, &del);
            env_::set_tyvar_lower_bounds(&mut renv.env, tv, lbs);
            let mut ty_errs = vec![];
            for (ity, pos, name) in add {
                let ty_err: Option<typing_error::T> = t_utils::sub_type_i(
                    &mut renv.env,
                    None,
                    None,
                    ity,
                    tv_ity.clone(),
                    elim_on_error(pos, &name),
                );
                if let Some(ty_err) = ty_err {
                    ty_errs.push(ty_err)
                }
            }
            ty_errs.reverse();
            typing_error::multiple_opt(ty_errs)
        }
    };
    if let Some(e) = ocaml_option::merge(e1, e2, typing_error::both) {
        typing_error_utils::add_typing_error(&e, &renv.env)
    }
}

fn refresh_tvars(seen: tvid::set::T, renv: RefreshEnv) -> Env {
    // OCaml recurses (in tail position) until no new type variable is found.
    let mut seen = seen;
    let mut renv = renv;
    loop {
        if renv.tvars.is_empty() {
            return renv.env;
        }
        let tvars = std::mem::take(&mut renv.tvars);
        // `Tvid.Map.fold refresh_tvar tvars renv`, in increasing order
        for (tv, on_error) in tvars.iter() {
            refresh_tvar(*tv, on_error, &mut renv)
        }
        for v in tvars.keys() {
            seen.insert(*v);
        }
        for v in seen.iter() {
            renv.tvars.remove(v);
        }
    }
}

fn refresh_locals(renv: &mut RefreshEnv) {
    let locals = match env_::next_cont_opt(&renv.env) {
        None => typing_local_types::empty(),
        Some(entry) => entry.local_types,
    };
    // save the original error callback & use it to create one callback
    // per local in the fold below
    let on_error = renv.on_error.clone();
    // `Local_id.Map.fold`, in increasing order
    for (
        local,
        typing_local_types::Local {
            ty: lty,
            pos,
            eid: _,
            macro_splice_vars: _,
        },
    ) in locals.iter()
    {
        let on_error = {
            let pos = pos_or_decl::of_raw_pos(pos.clone());
            let name = markdown_lite::md_codify(&local_id::to_string(local));
            let reason =
                Lazy::new(move || Message(pos, format!("in the type of local {}", name).into()));
            reasons_callback::append_reason(on_error.clone(), reason)
        };
        renv.on_error = on_error;
        let (lty, changed) = refresh_type(renv, Variance::Covariant, lty.clone());
        match changed {
            Changed::Elim(..) => {
                env_::set_local(None, None, &mut renv.env, local.clone(), lty, pos.clone())
            }
            Changed::Unchanged => {}
        }
    }
}

/// Whether OCaml's `Typing_defs_core.Locl_subst.apply ty ~subst` gives `ty`
/// back itself (physically): it does for the types it does not rebuild (the
/// leaves, and the generics that are not substituted), and rebuilds all the
/// others. (`crate::typing_defs_core::locl_subst::apply` rebuilds them all.)
fn locl_subst_keeps(ty: &Ty, subst: &locl_subst::T) -> bool {
    subst.is_empty()
        || match get_node(ty) {
            Ty_::Tgeneric(nm) => !subst.contains_key(nm),
            Ty_::Tvar(_)
            | Ty_::Tany(_)
            | Ty_::Tnonnull
            | Ty_::Tdynamic(_)
            | Ty_::Tprim(_)
            | Ty_::Tlabel(_)
            | Ty_::Tneg(_) => true,
            Ty_::Toption(_)
            | Ty_::TclassPtr(_)
            | Ty_::Taccess(_)
            | Ty_::TvecOrDict(_, _)
            | Ty_::Ttuple(_)
            | Ty_::Tunion(_)
            | Ty_::Tintersection(_)
            | Ty_::Tfun(_)
            | Ty_::Tshape(_)
            | Ty_::Tnewtype(_, _, _)
            | Ty_::Tdependent(_, _)
            | Ty_::Tclass(_, _, _) => false,
        }
}

/// Remove escaping expression-dependent types from the global tpenv.
///     Without this cleanup, expression-dependent types introduced inside
///     one scope leak into subsequent scopes via the global tpenv.
///     typing_taccess expands type constants on a Tgeneric by iterating
///     over all its upper bounds and intersecting the results. With the
///     recursive `with` refinement pattern (e.g.,
///       abstract const type TCB as IRepBuilder
///         with { type TCB = this::TCB };
///     ), each scope adds a distinct `with` upper bound to the mangled
///     generic, so typing_taccess produces a growing intersection,
///     causing exponential blowup.
///
///     After the refresh steps above have replaced escaping types in
///     locals, the return type, and unsolved tyvar bounds, we:
///     1. Build a substitution mapping each deleted expr-dep generic
///        to its upper bound (read before deletion)
///     2. Delete the expr-dep entries from the tpenv
///     3. Apply the substitution to remaining tpenv entries' bounds
///        (cleaning stale `with` refinements that reference deleted types)
///     4. Apply the substitution to solved tyvar solutions (which the
///        refresh steps expanded inline but did not write back)
fn remove_expr_dep_types_from_tpenv(types: &[String], env: &mut Env) {
    let pre_deletion_tpenv = env_::get_global_tpenv(env);

    // Build substitution map: deleted name -> upper bound
    let mut subst: locl_subst::T = im::OrdMap::new();
    for name in types {
        if dependent_kind::is_expr_dep_ty(name) {
            match &ty_set::elements(&type_parameter_env::get_upper_bounds(
                &pre_deletion_tpenv,
                name,
            ))[..]
            {
                [ub] => {
                    subst.insert(name.clone(), ub.clone());
                }
                _ => {}
            }
        }
    }
    let combine_reasons = |src: reason::T, _dest: reason::T| src;
    // `subst_ty`, with what OCaml gives back physically given back.
    let subst_ty_opt = |ty: &Ty| -> Option<Ty> {
        if locl_subst_keeps(ty, &subst) {
            None
        } else {
            Some(locl_subst::apply(ty.clone(), &subst, &combine_reasons))
        }
    };
    let subst_ty = |ty: &Ty| -> Ty { subst_ty_opt(ty).unwrap_or_else(|| ty.clone()) };

    // Delete expr-dep entries from the tpenv
    let mut global_tpenv = pre_deletion_tpenv.clone();
    for name in types {
        if dependent_kind::is_expr_dep_ty(name) && type_parameter_env::mem(name, &global_tpenv) {
            type_parameter_env::remove(&mut global_tpenv, name)
        }
    }

    // Substitute in remaining entries bounds
    if !subst.is_empty() {
        for name in type_parameter_env::get_tparam_names(&global_tpenv) {
            match type_parameter_env::get_with_pos(&name, &global_tpenv) {
                None => {}
                Some((def_pos, tparam_info)) => {
                    // `TySet.map subst_ty`: the nodes in which nothing changed are
                    // kept, as in OCaml.
                    let ubs = ty_set::map_phys(subst_ty_opt, &tparam_info.upper_bounds);
                    let lbs = ty_set::map_phys(subst_ty_opt, &tparam_info.lower_bounds);
                    if ty_set::equal(&ubs, &tparam_info.upper_bounds)
                        && ty_set::equal(&lbs, &tparam_info.lower_bounds)
                    {
                    } else {
                        type_parameter_env::add(
                            def_pos,
                            name,
                            typing_kinding_defs::Kind {
                                upper_bounds: ubs,
                                lower_bounds: lbs,
                                ..tparam_info
                            },
                            &mut global_tpenv,
                        )
                    }
                }
            }
        }
    }
    env_::env_with_global_tpenv(env, global_tpenv);

    // Substitute in solved tyvar solutions
    if !subst.is_empty() {
        for tv in env_::get_all_tyvars(env) {
            if env_::tyvar_is_solved(env, tv) {
                let solution = env_::get_type(env, reason::none(), tv);
                let solution_ = subst_ty(&solution);
                if phys_equal(&solution, &solution_) {
                } else {
                    env_::add(env, None, tv, solution_)
                }
            }
        }
    }
}

pub fn refresh_env_and_type(remove: EscapingRigidTvars, pos: Pos, env: &mut Env, ty: Ty) -> Ty {
    let pos = &pos;
    let (types, remove) = remove;
    if types.is_empty() {
        // nothing to clear, just return the inputs
        ty
    } else {
        typing_log::log_escape(
            None,
            &pos_or_decl::of_raw_pos(pos.clone()),
            env,
            "Clearing escaping types:",
            &types,
        );
        let what = "lambda";
        let on_error = reasons_callback::rigid_tvar_escape_at(pos.clone(), what.to_string());
        let mut renv = RefreshEnv {
            env: env.clone(),
            tvars: tvid::map::T::new(),
            remove,
            on_error: on_error.clone(),
            scope_kind: (what.to_string(), pos.clone()),
            elim_bogus_taccess: false,
            eliminating: SSet::new(),
        };
        refresh_locals(&mut renv);
        let on_error = {
            let pos = pos_or_decl::of_raw_pos(pos.clone());
            reasons_callback::append_reason(
                on_error,
                Lazy::new(move || Message(pos, "in the return type of this lambda".into())),
            )
        };
        renv.on_error = on_error;
        let (ty, _) = refresh_type(&mut renv, Variance::Covariant, ty);
        let mut env_ = refresh_tvars(tvid::set::T::new(), renv);

        remove_expr_dep_types_from_tpenv(&types, &mut env_);
        *env = env_;
        ty
    }
}

// ********************************************************************
// Computing escaping types
// ********************************************************************

#[derive(Clone, Debug)]
pub struct Snapshot {
    tpmap: SMap<(PosOrDecl, typing_kinding_defs::Kind)>,
    /// nextid is used to detect if an expression-dependent type is fresh
    /// or not; we snapshot it at some time and all ids larger than the
    /// snapshot were allocated after the snapshot time
    nextid: expression_id::T,
}

/// `string list * remove_map`
pub type EscapingRigidTvars = (Vec<String>, RemoveMap);

/// Extract the Expression_id.t from a tpenv entry name like "<expr#3>::TFoo".
fn extract_expr_id(name: &str) -> expression_id::T {
    // `atoi name 6 0`
    let s = name.as_bytes();
    let mut i = 6;
    let mut acc: isize = 0;
    while s[i] != b'>' {
        acc = acc
            .wrapping_mul(10)
            .wrapping_add(s[i] as isize - b'0' as isize);
        i += 1;
    }
    expression_id::dodgy_from_int(acc)
}

fn has_tvar_or_expr_dep_types(env: &Env, result_ty: &Ty) -> bool {
    // `let (_env, result_ty) = Env.expand_type env result_ty`: only a type
    // variable is expanded, in a copy of the environment.
    let result_ty = match get_node(result_ty) {
        Ty_::Tvar(_) => env_::expand_type(&mut env.clone(), result_ty.clone()),
        _ => result_ty.clone(),
    };
    // Not in the OCaml, which searches it: a type whose flags tell that no
    // type variable, generic or dependent type occurs in it has none of the
    // types searched (see `typing_defs_core::ty_flags`).
    {
        use crate::typing_defs_core::ty_flags;
        if !result_ty.may_have(ty_flags::TVAR | ty_flags::TGENERIC | ty_flags::TDEPENDENT) {
            return false;
        }
    }
    find_locl_ty(&result_ty, &|ty| match get_node(ty) {
        Ty_::Tvar(_) | Ty_::Tdependent(DependentType::DTexpr(_), _) => true,
        Ty_::Tgeneric(name) => dependent_kind::is_expr_dep_ty(name),
        _ => false,
    })
    .is_some()
}

fn cleanup_expr_dep_types(snap: &Snapshot, env: &mut Env, result_ty: &Ty) {
    if has_tvar_or_expr_dep_types(env, result_ty) {
    } else {
        let Snapshot { nextid, .. } = snap;
        // `List.filter` of `get_tparam_names`, copying only the names kept.
        let new_expr_dep_types: Vec<String> =
            type_parameter_env::iter_tparam_names(&env.tpenv)
                .filter(|name| {
                    dependent_kind::is_expr_dep_ty(name)
                        && expression_id::compare(extract_expr_id(name), *nextid) != Ordering::Less
                })
                .cloned()
                .collect();
        if new_expr_dep_types.is_empty() {
        } else {
            remove_expr_dep_types_from_tpenv(&new_expr_dep_types, env)
        }
    }
}

pub fn snapshot_env(env: &Env) -> Snapshot {
    let gtp = type_parameter_env::get_tparams(&env_::get_global_tpenv(env));
    let ltp = type_parameter_env::get_tparams(&env_::get_tpenv(env));
    Snapshot {
        tpmap: s_map::union(None, &gtp, &ltp),
        nextid: env_::make_expression_id(env),
    }
}

pub fn with_expr_dep_cleanup<A>(env: &mut Env, f: impl FnOnce(&mut Env) -> (Ty, A)) -> (Ty, A) {
    let snap = snapshot_env(env);
    let (ty, x) = f(env);
    cleanup_expr_dep_types(&snap, env, &ty);
    (ty, x)
}

pub fn escaping_from_snapshot(snap: &Snapshot, env: &Env, quants: &[String]) -> EscapingRigidTvars {
    let is_global = |tp: &str| {
        // Oh, that's nice...
        tp.len() > 6 && &tp.as_bytes()[..6] == b"this::"
    };
    let Snapshot { nextid, .. } = snap;
    let nextid = *nextid;
    let is_old_dep_expr = |tp: &str| {
        tp.len() > 6
            && &tp.as_bytes()[..6] == b"<expr#"
            && expression_id::compare(extract_expr_id(tp), nextid) == Ordering::Less
    };
    let tpmap = {
        let mut tpmap = type_parameter_env::get_tparams(&env_::get_global_tpenv(env));
        // `Typing_continuations.Map.fold (fun _ c -> S_map.union (... c.tpenv))`,
        // in the order of the continuations
        for (_, c) in typing_lenv::get_all_locals(env).iter() {
            tpmap = s_map::union(None, &type_parameter_env::get_tparams(&c.tpenv), &tpmap);
        }
        for (key, _) in snap.tpmap.iter() {
            tpmap.remove_key(key);
        }
        tpmap
            .into_iter()
            .filter(|(tp, _)| !is_global(tp) && !is_old_dep_expr(tp))
            .collect::<SMap<_>>()
    };
    let mut tpmap = tpmap;
    for nm in quants {
        tpmap.remove_key(nm);
    }
    let keys = s_map::keys(&tpmap);
    let remove: RemoveMap = Rc::new(move |rtv: &RigidTvar| match rtv {
        RigidTvar::RtvTparam(name) => tpmap.get(name).map(|(pos, tpi)| ElimInfo {
            pos: pos.clone(),
            upper_bounds: tpi.upper_bounds.clone(),
            lower_bounds: tpi.lower_bounds.clone(),
        }),
        RigidTvar::RtvDependent(id) => {
            let empty_info = ElimInfo {
                pos: pos_or_decl::NONE,
                upper_bounds: ty_set::empty(),
                lower_bounds: ty_set::empty(),
            };
            if expression_id::compare(*id, nextid) == Ordering::Greater {
                Some(empty_info)
            } else {
                None
            }
        }
    });
    (keys, remove)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bogus_type_accesses() {
        assert!(is_bogus_taccess("C::T"));
        assert!(!is_bogus_taccess("<expr#1>::T"));
        assert!(!is_bogus_taccess("<cls#C>::T"));
        assert!(!is_bogus_taccess("T"));
    }

    #[test]
    fn the_first_change_wins() {
        let elim = |n: &str| Changed::Elim(pos_or_decl::NONE, n.to_string());
        assert!(matches!(
            or(Changed::Unchanged, Changed::Unchanged),
            Changed::Unchanged
        ));
        assert!(matches!(or(elim("a"), elim("b")), Changed::Elim(_, n) if n == "a"));
        assert!(matches!(
            or(Changed::Unchanged, elim("b")),
            Changed::Elim(_, n) if n == "b"
        ));
        // with_default gives back the original when nothing changed
        assert_eq!(with_default(1, (2, Changed::Unchanged)).0, 1);
        assert_eq!(with_default(1, (2, elim("a"))).0, 2);
    }

    #[test]
    fn expression_ids_of_names() {
        assert_eq!(extract_expr_id("<expr#3>::TFoo"), 3);
        assert_eq!(extract_expr_id("<expr#123>::T"), 123);
    }
}
