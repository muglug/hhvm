// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! c.f. `hphp/hack/src/decl/decl_requirements.ml`, which this follows
//! function by function.
//!
//! The ancestors that the OCaml finds in its `Decl_env.class_cache`
//! (`Decl_env.get_class_and_add_dep ~cache ~shmem_fallback:false
//! ~fallback:Decl_env.no_fallback`, which only looks in the cache and records
//! no dependency) are looked up in `parents`.
//!
//! The OCaml lists that are built by consing are `VecDeque`s here
//! (`x :: l` is `l.push_front(x)`), so that every list ends up in the order of
//! the OCaml list: `cr_req_ancestors` and `cr_req_constraints_ancestors` are
//! read in that order by the typechecker (`Cls.all_ancestor_reqs`, ...).

use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Arc;

use hash::IndexMap;
use hash::IndexSet;
use pos::TypeName;
use ty::decl::ClassishKind;
use ty::decl::FoldedClass;
use ty::decl::Requirement;
use ty::decl::ShallowClass;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::folded::ConstraintRequirement;
use ty::decl::subst::Subst;
use ty::decl::ty::DeclConstraintRequirement;
use ty::reason::Reason;

use super::subst::Substitution;

/// `Decl_defs.class_requirements`
#[derive(Clone, Debug)]
pub struct ClassRequirements<R: Reason> {
    /// `cr_req_ancestors`
    pub req_ancestors: Vec<Requirement<R>>,
    /// `cr_req_ancestors_extends`
    pub req_ancestors_extends: IndexSet<TypeName>,
    /// `cr_req_constraints_ancestors`
    pub req_constraints_ancestors: Vec<ConstraintRequirement<R>>,
}

/// The class entries the OCaml has in its `Decl_env.class_cache`.
pub type ClassCache<R> = IndexMap<TypeName, Arc<FoldedClass<R>>>;

pub fn make_substitution<R: Reason>(
    class_type: &FoldedClass<R>,
    class_parameters: &[Ty<R>],
) -> Subst<R> {
    // Inst.make_subst class_type.dc_tparams class_parameters
    Subst::new(&class_type.tparams, class_parameters)
}

/// `Decl_env.get_class_and_add_dep ~cache:class_cache ~shmem_fallback:false
/// ~fallback:Decl_env.no_fallback env name`
fn get_class_and_add_dep<R: Reason>(
    class_cache: &ClassCache<R>,
    name: TypeName,
) -> Option<&Arc<FoldedClass<R>>> {
    class_cache.get(&name)
}

/// `(req_ancestors, req_ancestors_extends)`
pub type Acc<R> = (VecDeque<Requirement<R>>, IndexSet<TypeName>);

/// Accumulate requirements so that we can successfully check the bodies
/// of trait methods / check that classes satisfy these requirements
pub fn flatten_parent_class_reqs<R: Reason>(
    class_cache: &ClassCache<R>,
    shallow_class: &ShallowClass<R>,
    acc: Acc<R>,
    parent_ty: &Ty<R>,
) -> Acc<R> {
    let (mut req_ancestors, req_ancestors_extends) = acc;
    let (_, parent_pos_id, parent_params) = parent_ty.unwrap_class_type();
    let parent_type = get_class_and_add_dep(class_cache, parent_pos_id.id());
    match parent_type {
        None => {
            // The class lives in PHP
            (req_ancestors, req_ancestors_extends)
        }
        Some(parent_type) => {
            let subst = make_substitution(parent_type, parent_params);
            let substitution = Substitution { subst: &subst };
            // List.rev_map_append parent_type.dc_req_ancestors req_ancestors
            for req in parent_type.req_ancestors.iter() {
                let ty = substitution.instantiate(&req.ty);
                req_ancestors.push_front(Requirement::new(parent_pos_id.pos().clone(), ty));
            }
            match shallow_class.kind {
                ClassishKind::Cclass(_) => {
                    // not necessary to accumulate req_ancestors_extends for classes --
                    // it's not used
                    (req_ancestors, IndexSet::default())
                }
                ClassishKind::Ctrait | ClassishKind::Cinterface => {
                    let mut req_ancestors_extends = req_ancestors_extends;
                    req_ancestors_extends.extend(parent_type.req_ancestors_extends.iter().copied());
                    (req_ancestors, req_ancestors_extends)
                }
                ClassishKind::Cenum | ClassishKind::CenumClass(_) => {
                    panic!("Assert_failure decl_requirements.ml: flatten_parent_class_reqs")
                }
            }
        }
    }
}

pub fn declared_class_req<R: Reason>(
    class_cache: &ClassCache<R>,
    acc: Acc<R>,
    req_ty: &Ty<R>,
) -> Acc<R> {
    let (mut requirements, mut req_extends) = acc;
    let (_, req_pos_id, _) = req_ty.unwrap_class_type();
    let req_name = req_pos_id.id();
    let req_type = get_class_and_add_dep(class_cache, req_name);
    req_extends.insert(req_name);
    // since the req is declared on this class, we should
    // emphatically *not* substitute: a require extends Foo<T> is
    // going to be this class's <T>
    requirements.push_front(Requirement::new(req_pos_id.pos().clone(), req_ty.clone()));
    match req_type {
        None => {
            // The class lives in PHP : error??
            (requirements, req_extends)
        }
        Some(parent_type) => {
            // The parent class lives in Hack
            req_extends.extend(parent_type.extends.iter().copied());
            req_extends.extend(parent_type.xhp_attr_deps.iter().copied());
            // the req may be of an interface that has reqs of its own; the
            // flattened ancestry required by *those* reqs need to be added
            // in to, e.g., interpret accesses to protected functions inside
            // traits
            req_extends.extend(parent_type.req_ancestors_extends.iter().copied());
            (requirements, req_extends)
        }
    }
}

pub fn declared_class_req_non_strict<R: Reason>(
    class_cache: &ClassCache<R>,
    mut required_classes: VecDeque<ConstraintRequirement<R>>,
    req: &DeclConstraintRequirement<R>,
) -> VecDeque<ConstraintRequirement<R>> {
    let elab = |req_ty: &Ty<R>| {
        let (_, req_pos_id, _) = req_ty.unwrap_class_type();
        // ensure we add a dependecy even if we don't need the class itself
        let _ = get_class_and_add_dep(class_cache, req_pos_id.id());
        Requirement::new(req_pos_id.pos().clone(), req_ty.clone())
    };
    match req {
        DeclConstraintRequirement::DCREqual(req_ty) => {
            required_classes.push_front(ConstraintRequirement::CREqual(elab(req_ty)))
        }
        DeclConstraintRequirement::DCRSubtype(req_ty) => {
            required_classes.push_front(ConstraintRequirement::CRSubtype(elab(req_ty)))
        }
    }
    required_classes
}

pub fn flatten_parent_class_reqs_non_strict<R: Reason>(
    class_cache: &ClassCache<R>,
    mut req_constraints_ancestors: VecDeque<ConstraintRequirement<R>>,
    parent_ty: &Ty<R>,
) -> VecDeque<ConstraintRequirement<R>> {
    let (_, parent_pos_id, parent_params) = parent_ty.unwrap_class_type();
    let parent_type = get_class_and_add_dep(class_cache, parent_pos_id.id());
    match parent_type {
        None => {
            // The class lives in PHP
            req_constraints_ancestors
        }
        Some(parent_type) => {
            let subst = make_substitution(parent_type, parent_params);
            let substitution = Substitution { subst: &subst };
            // List.rev_map_append
            //   parent_type.dc_req_constraints_ancestors
            //   req_constraints_ancestors
            for cr in parent_type.req_constraints_ancestors.iter() {
                let elab = |req: &Requirement<R>| {
                    let ty = substitution.instantiate(&req.ty);
                    Requirement::new(parent_pos_id.pos().clone(), ty)
                };
                req_constraints_ancestors.push_front(match cr {
                    ConstraintRequirement::CREqual(req_ty) => {
                        ConstraintRequirement::CREqual(elab(req_ty))
                    }
                    ConstraintRequirement::CRSubtype(req_ty) => {
                        ConstraintRequirement::CRSubtype(elab(req_ty))
                    }
                })
            }
            req_constraints_ancestors
        }
    }
}

/// Cheap hack: we cannot do unification / subtyping in the decl phase because
/// the type arguments of the types that we are trying to unify may not have
/// been declared yet. See the test iface_require_circular.php for details.
///
/// However, we don't want a super long req_extends list because of the perf
/// overhead. And while we can't do proper unification we can dedup types
/// that are syntactically equivalent.
///
/// A nicer solution might be to add a phase in between type-decl and type-check
/// that prunes the list via proper subtyping, but that's a little more work
/// than I'm willing to do now.
pub fn naive_dedup<R: Reason>(req_extends: VecDeque<Requirement<R>>) -> VecDeque<Requirement<R>> {
    // maps class names to type params
    let mut h: HashMap<TypeName, Vec<Ty<R>>> = HashMap::default();
    // List.rev_filter_map: [f] is applied from the head of the list, and the
    // results are in the reverse order.
    let mut result = VecDeque::new();
    for req in req_extends {
        let kept = match req.ty.node_ref() {
            Ty_::Tapply(id_and_args) => {
                let (name, hl) = &**id_and_args;
                let name = name.id();
                // `List.map hl ~f:Decl_pos_utils.NormalizeSig.ty`, then
                // `List.equal equal_decl_ty`: `equal_decl_ty` ignores the
                // positions that `NormalizeSig` erases.
                match h.get(&name) {
                    Some(hl_) if equal::equal_decl_tyl(hl, hl_) => None,
                    // `Exit`, `Not_found`
                    _ => {
                        h.insert(name, hl.to_vec());
                        Some(req)
                    }
                }
            }
            _ => Some(req),
        };
        if let Some(req) = kept {
            result.push_front(req);
        }
    }
    result
}

pub fn get_class_requirements<R: Reason>(
    class_cache: &ClassCache<R>,
    shallow_class: &ShallowClass<R>,
) -> ClassRequirements<R> {
    let acc: Acc<R> = (VecDeque::new(), IndexSet::default());
    let acc = (shallow_class.req_extends.iter()).fold(acc, |acc, req_ty| {
        declared_class_req(class_cache, acc, req_ty)
    });
    let acc = (shallow_class.req_implements.iter()).fold(acc, |acc, req_ty| {
        declared_class_req(class_cache, acc, req_ty)
    });
    let acc = (shallow_class.uses.iter()).fold(acc, |acc, parent_ty| {
        flatten_parent_class_reqs(class_cache, shallow_class, acc, parent_ty)
    });
    let acc = (if shallow_class.kind.is_cinterface() {
        shallow_class.extends.iter()
    } else {
        shallow_class.implements.iter()
    })
    .fold(acc, |acc, parent_ty| {
        flatten_parent_class_reqs(class_cache, shallow_class, acc, parent_ty)
    });
    let (req_extends, req_ancestors_extends) = acc;
    let req_extends = naive_dedup(req_extends);

    let req_constraints = (shallow_class.req_constraints.iter())
        .fold(VecDeque::new(), |acc, req| {
            declared_class_req_non_strict(class_cache, acc, req)
        });
    let req_constraints = (shallow_class.uses.iter()).fold(req_constraints, |acc, parent_ty| {
        flatten_parent_class_reqs_non_strict(class_cache, acc, parent_ty)
    });
    ClassRequirements {
        req_ancestors: req_extends.into(),
        req_ancestors_extends,
        req_constraints_ancestors: req_constraints.into(),
    }
}

/// `Typing_defs_core.equal_decl_ty`: `ty__compare` (without
/// `~normalize_lists`) returning 0. Reasons are ignored, and so are the
/// positions in types; the parts of a type that `ty__compare` does not look
/// at (the variance of type parameters, the names of parameters that are not
/// named, default values, ...) are ignored too.
pub mod equal {
    use ty::decl::ClassRefinement;
    use ty::decl::FunParam;
    use ty::decl::FunType;
    use ty::decl::RefinedConst;
    use ty::decl::RefinedConstBound;
    use ty::decl::Tparam;
    use ty::decl::Ty;
    use ty::decl::Ty_;
    use ty::decl::UserAttribute;
    use ty::decl::WhereConstraint;
    use ty::decl::ty::Capability;
    use ty::decl::ty::FunParamFlags;
    use ty::decl::ty::ShapeType;
    use ty::decl::ty::ShapeTypeSimple;
    use ty::decl::ty::TupleExtra;
    use ty::decl::ty::TupleType;
    use ty::decl::ty::UserAttributeParam;
    use ty::reason::Reason;

    /// `List.compare f l1 l2 = 0`
    fn list_equal<T>(f: impl Fn(&T, &T) -> bool, l1: &[T], l2: &[T]) -> bool {
        l1.len() == l2.len() && l1.iter().zip(l2.iter()).all(|(x, y)| f(x, y))
    }

    pub fn equal_decl_ty<R: Reason>(ty1: &Ty<R>, ty2: &Ty<R>) -> bool {
        equal_decl_ty_(ty1.node_ref(), ty2.node_ref())
    }

    pub fn equal_decl_tyl<R: Reason>(tyl1: &[Ty<R>], tyl2: &[Ty<R>]) -> bool {
        list_equal(equal_decl_ty, tyl1, tyl2)
    }

    /// `tyl_compare ~sort:true` returning 0: the lists are equal once sorted,
    /// i.e. they have the same elements, as many times each.
    fn sorted_tyl_equal<R: Reason>(tyl1: &[Ty<R>], tyl2: &[Ty<R>]) -> bool {
        if tyl1.len() != tyl2.len() {
            return false;
        }
        let mut used = vec![false; tyl2.len()];
        tyl1.iter().all(|ty1| {
            match (tyl2.iter().enumerate()).find(|(i, ty2)| !used[*i] && equal_decl_ty(ty1, ty2)) {
                Some((i, _)) => {
                    used[i] = true;
                    true
                }
                None => false,
            }
        })
    }

    pub fn equal_decl_ty_<R: Reason>(ty_1: &Ty_<R>, ty_2: &Ty_<R>) -> bool {
        use Ty_::*;
        match (ty_1, ty_2) {
            (Tthis, Tthis) => true,
            (Tapply(a1), Tapply(a2)) => {
                let (id1, tyl1) = &**a1;
                let (id2, tyl2) = &**a2;
                id1.id() == id2.id() && equal_decl_tyl(tyl1, tyl2)
            }
            (Trefinement(tr1), Trefinement(tr2)) => {
                equal_decl_ty(&tr1.ty, &tr2.ty)
                    && class_refinement_equal(&tr1.refinement, &tr2.refinement)
            }
            (Tmixed, Tmixed) => true,
            (Twildcard, Twildcard) => true,
            (Tlike(ty1), Tlike(ty2)) => equal_decl_ty(ty1, ty2),
            (Tprim(p1), Tprim(p2)) => p1 == p2,
            (Toption(ty1), Toption(ty2)) => equal_decl_ty(ty1, ty2),
            (TvecOrDict(kv1), TvecOrDict(kv2)) => {
                equal_decl_ty(&kv1.0, &kv2.0) && equal_decl_ty(&kv1.1, &kv2.1)
            }
            (Tfun(ft1), Tfun(ft2)) => tfun_equal(ft1, ft2),
            (Tunion(tyl1), Tunion(tyl2)) | (Tintersection(tyl1), Tintersection(tyl2)) => {
                equal_decl_tyl(tyl1, tyl2)
            }
            (Ttuple(t1), Ttuple(t2)) => tuple_type_equal(t1, t2),
            (Tgeneric(n1), Tgeneric(n2)) => n1 == n2,
            (Tshape(s1), Tshape(s2)) => shape_type_equal(s1, s2),
            (Taccess(ta1), Taccess(ta2)) => {
                equal_decl_ty(&ta1.ty, &ta2.ty) && ta1.type_const.id() == ta2.type_const.id()
            }
            (Tnonnull, Tnonnull) => true,
            (Tdynamic, Tdynamic) => true,
            (TclassPtr(ty1), TclassPtr(ty2)) => equal_decl_ty(ty1, ty2),
            // `ty_con_ordinal_ ty_1 - ty_con_ordinal_ ty_2`: 0 for two
            // `Tany`s, and for no two different constructors.
            (Tany, Tany) => true,
            (
                Tthis | Tapply(_) | Trefinement(_) | Tmixed | Twildcard | Tlike(_) | Tprim(_)
                | Toption(_) | TvecOrDict(_) | Tfun(_) | Tunion(_) | Tintersection(_) | Ttuple(_)
                | Tgeneric(_) | Tshape(_) | Taccess(_) | Tnonnull | Tdynamic | TclassPtr(_) | Tany,
                _,
            ) => false,
        }
    }

    fn shape_type_equal<R: Reason>(s1: &ShapeType<R>, s2: &ShapeType<R>) -> bool {
        match (s1, s2) {
            (ShapeType::Simple(_), ShapeType::Splat(_))
            | (ShapeType::Splat(_), ShapeType::Simple(_)) => false,
            (ShapeType::Splat(e1), ShapeType::Splat(e2)) => equal_decl_tyl(e1, e2),
            (
                ShapeType::Simple(ShapeTypeSimple(unknown_fields_type1, fields1)),
                ShapeType::Simple(ShapeTypeSimple(unknown_fields_type2, fields2)),
            ) => {
                // (decl shapes have no origin: they are all `Missing_origin`,
                // as `NormalizeSig` makes them.)
                equal_decl_ty(unknown_fields_type1, unknown_fields_type2)
                    && fields1.len() == fields2.len()
                    && (fields1.iter().zip(fields2.iter())).all(|((k1, sft1), (k2, sft2))| {
                        k1 == k2
                            && equal_decl_ty(&sft1.ty, &sft2.ty)
                            && sft1.optional == sft2.optional
                    })
            }
        }
    }

    fn tuple_type_equal<R: Reason>(t1: &TupleType<R>, t2: &TupleType<R>) -> bool {
        let TupleType(t_required1, t_optional1, t_extra1) = t1;
        let TupleType(t_required2, t_optional2, t_extra2) = t2;
        equal_decl_tyl(t_required1, t_required2)
            && equal_decl_tyl(t_optional1, t_optional2)
            && match (t_extra1, t_extra2) {
                (TupleExtra::Tsplat(t1), TupleExtra::Tsplat(t2))
                | (TupleExtra::Tvariadic(t1), TupleExtra::Tvariadic(t2)) => equal_decl_ty(t1, t2),
                (TupleExtra::Tsplat(_), TupleExtra::Tvariadic(_))
                | (TupleExtra::Tvariadic(_), TupleExtra::Tsplat(_)) => false,
            }
    }

    fn user_attribute_param_equal(p1: &UserAttributeParam, p2: &UserAttributeParam) -> bool {
        match (p1, p2) {
            (UserAttributeParam::Classname(s1), UserAttributeParam::Classname(s2)) => s1 == s2,
            (UserAttributeParam::EnumClassLabel(s1), UserAttributeParam::EnumClassLabel(s2)) => {
                s1 == s2
            }
            (UserAttributeParam::String(s1), UserAttributeParam::String(s2)) => s1 == s2,
            (UserAttributeParam::Int(s1), UserAttributeParam::Int(s2)) => s1 == s2,
            _ => false,
        }
    }

    fn user_attribute_equal<P>(ua1: &UserAttribute<P>, ua2: &UserAttribute<P>) -> bool {
        ua1.name.id() == ua2.name.id()
            && list_equal(user_attribute_param_equal, &ua1.params, &ua2.params)
    }

    fn tparam_equal<R: Reason>(tp1: &Tparam<R, Ty<R>>, tp2: &Tparam<R, Ty<R>>) -> bool {
        // Type parameters on functions are always marked invariant
        tp1.name.id() == tp2.name.id()
            && list_equal(
                |(ck1, ty1), (ck2, ty2)| ck1 == ck2 && equal_decl_ty(ty1, ty2),
                &tp1.constraints,
                &tp2.constraints,
            )
            && list_equal(
                user_attribute_equal,
                &tp1.user_attributes,
                &tp2.user_attributes,
            )
            && tp1.reified == tp2.reified
    }

    fn ft_param_equal<R: Reason>(param1: &FunParam<R, Ty<R>>, param2: &FunParam<R, Ty<R>>) -> bool {
        equal_decl_ty(&param1.ty, &param2.ty)
            && param1.flags == param2.flags
            && (!param1.flags.contains(FunParamFlags::NAMED) || param1.name == param2.name)
    }

    fn tfun_equal<R: Reason>(fty1: &FunType<R, Ty<R>>, fty2: &FunType<R, Ty<R>>) -> bool {
        equal_decl_ty(&fty1.ret, &fty2.ret)
            && list_equal(ft_param_equal, &fty1.params, &fty2.params)
            && list_equal(tparam_equal, &fty1.tparams, &fty2.tparams)
            && list_equal(
                |WhereConstraint(ty1a, ck1, ty1b), WhereConstraint(ty2a, ck2, ty2b)| {
                    ck1 == ck2 && equal_decl_ty(ty1a, ty2a) && equal_decl_ty(ty1b, ty2b)
                },
                &fty1.where_constraints,
                &fty2.where_constraints,
            )
            && fty1.flags == fty2.flags
            && match (
                &fty1.implicit_params.capability,
                &fty2.implicit_params.capability,
            ) {
                (Capability::CapDefaults(_), Capability::CapDefaults(_)) => true,
                (Capability::CapTy(ty1), Capability::CapTy(ty2)) => equal_decl_ty(ty1, ty2),
                (Capability::CapDefaults(_), Capability::CapTy(_))
                | (Capability::CapTy(_), Capability::CapDefaults(_)) => false,
            }
            && fty1.instantiated == fty2.instantiated
    }

    fn refined_const_equal<R: Reason>(a: &RefinedConst<Ty<R>>, b: &RefinedConst<Ty<R>>) -> bool {
        a.is_ctx == b.is_ctx
            && match (&a.bound, &b.bound) {
                (RefinedConstBound::Exact(_), RefinedConstBound::Loose(_))
                | (RefinedConstBound::Loose(_), RefinedConstBound::Exact(_)) => false,
                (RefinedConstBound::Loose(b1), RefinedConstBound::Loose(b2)) => {
                    sorted_tyl_equal(&b1.lower, &b2.lower) && sorted_tyl_equal(&b1.upper, &b2.upper)
                }
                (RefinedConstBound::Exact(ty1), RefinedConstBound::Exact(ty2)) => {
                    equal_decl_ty(ty1, ty2)
                }
            }
    }

    fn class_refinement_equal<R: Reason>(
        cr1: &ClassRefinement<Ty<R>>,
        cr2: &ClassRefinement<Ty<R>>,
    ) -> bool {
        // S_map.compare refined_const_compare
        cr1.consts.len() == cr2.consts.len()
            && (cr1.consts.iter()).all(|(k, rc1)| match cr2.consts.get(k) {
                Some(rc2) => refined_const_equal(rc1, rc2),
                None => false,
            })
    }
}
