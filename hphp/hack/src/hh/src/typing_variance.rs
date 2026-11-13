// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_variance.ml`. See `hh/PORTING.md`.
//!
//! Module checking the (co/contra)variance annotations (+/-).
//!
//! The algorithm works by tracking the variance of *uses* of a type parameter,
//! and checks that the variance *declaration* on that type parameter is
//! consistent with its uses.
//!
//! For every type parameter use, we keep a witness (a position in the source),
//! that tells us where the covariance (or contravariance) was deduced.
//! This way, when we find an error, we can point to the place that was
//! problematic (as usual).
//!
//! # Port notes
//!
//! - The reason stacks (`reason list`) are `Vec`s whose first element is the
//!   head of the OCaml list.
//! - `typing_variance.ml` defines `get_declared_variance` and `flip` twice. The
//!   first `get_declared_variance` (from a position and an annotation) is
//!   [`get_declared_variance_at`], the first `flip` (which swaps the positive
//!   and negative occurrences) is [`flip_typarams`]; the second definitions
//!   keep the names.
//! - The positive and negative occurrences (`Reason.decl_t list S_map.t`) are
//!   [`Occurrences`]. Building them records dependencies (the variances of the
//!   classes in `Tapply`), so the operands of `union` are computed in the
//!   order of the OCaml (from right to left).

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::ParamKind;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos::Pos;
use pos::ToOxidized;
use ty::decl::ty as d;

use crate::ast_defs;
use crate::ctx::R;
use crate::naming_attributes;
use crate::pos_or_decl;
use crate::typing_defs::*;
use crate::typing_env;
use crate::typing_env_types::Env as TEnv;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::utils;

/// Type describing the kind of position we are dealing with.
/// Pos.t gives us the position in the source, it doesn't tell us the kind
/// of position we are dealing with. This type keeps track of that.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PositionDescr {
    Rtypedef,
    /// Instance variable
    Rproperty,
    /// The declaration site of a type-parameter
    RtypeParameter,
    RfunParameter,
    RfunReturn,
    /// The argument of a parametric class or
    /// typedef:
    /// A<T1, ..>, T1 is (Rtype_argument "A")
    RtypeArgument(String),
    RconstraintAs,
    RconstraintEq,
    RconstraintSuper,
    RrefinementEq,
    RrefinementAs,
    RrefinementSuper,
    RwhereAs,
    RwhereSuper,
    RwhereEq,
    RcaseTypeWhereAs,
    RcaseTypeWhereSuper,
    RcaseTypeWhereEq,
    RfunInoutParameter,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PositionVariance {
    Pcovariant,
    Pcontravariant,
    Pinvariant,
}

/// `reason`
pub type Reason = (Pos, PositionDescr, PositionVariance);

/// The variance that we have inferred for a given use of a type-parameter. We keep
/// a stack of reasons that made us infer the variance of a position.
/// For example:
/// T appears in foo(...): (function(...): T)
/// T is inferred as covariant + a stack made of two elements:
/// -) The first one points to the position of T
/// -) The second one points to the position of (function(...): T)
/// We can, thanks to this stack, detail why we think something is covariant
/// in the error message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Variance {
    /// The type parameter appeared in covariant position.
    Vcovariant(Vec<Reason>),
    /// The type parameter appeared in contravariant position.
    Vcontravariant(Vec<Reason>),
    /// The type parameter appeared in both covariant and contravariant position.
    /// We keep a stack for each side: the left hand side is proof for covariance,
    /// while the right hand side is proof for contravariance.
    Vinvariant(Vec<Reason>, Vec<Reason>),
    /// The type parameter is not used, or is a method type parameter.
    Vboth,
}

/// `module Env`
pub mod env {
    use super::*;

    /// The set of type parameters which are in scope, with their variances.
    pub type TypeParameterEnv = im::OrdMap<String, Variance>;

    #[derive(Clone)]
    pub struct T<'a> {
        pub tpenv: TypeParameterEnv,
        pub enclosing_class: Option<&'a nast::Class_>,
        pub env: &'a TEnv,
    }

    pub fn remove_type_parameter<'a>(env: &T<'a>, name: &str) -> T<'a> {
        let mut tpenv = env.tpenv.clone();
        tpenv.remove(name);
        T {
            tpenv,
            ..env.clone()
        }
    }
}

/// `Reason.decl_t list S_map.t`: the reasons of the occurrences of each
/// tracked type parameter.
pub type Occurrences = im::OrdMap<String, Vec<R>>;

// ---------------------------------------------------------------------------
// Reason pretty-printing
// ---------------------------------------------------------------------------

fn variance_to_string(v: PositionVariance) -> &'static str {
    match v {
        PositionVariance::Pcovariant => "covariant (+)",
        PositionVariance::Pcontravariant => "contravariant (-)",
        PositionVariance::Pinvariant => "invariant",
    }
}

fn variance_to_sign(v: PositionVariance) -> &'static str {
    match v {
        PositionVariance::Pcovariant => "(+)",
        PositionVariance::Pcontravariant => "(-)",
        PositionVariance::Pinvariant => "(I)",
    }
}

fn reason_stack_to_string(variance: &str, reason_stack: &[Reason]) -> String {
    // List.fold_right ... (fun (_, _, pvariance) acc -> variance_to_sign pvariance ^ acc) ~init:""
    let signs: String = reason_stack
        .iter()
        .map(|(_, _, pvariance)| variance_to_sign(*pvariance))
        .collect();
    format!(
        "This position is {} because it is the composition of {}\nThe rest of the error messages decomposes the inference of the variance.\nCheck out this link if you don't understand what this is about:\nhttp://en.wikipedia.org/wiki/Covariance_and_contravariance_(computer_science)",
        variance, signs
    )
}

fn reason_to_string(sign: bool, (_, descr, variance): &Reason) -> String {
    let prefix = if sign {
        format!("{} ", variance_to_sign(*variance))
    } else {
        "".to_string()
    };
    let text = match descr {
        PositionDescr::Rtypedef => "Aliased types are covariant".to_string(),
        PositionDescr::Rproperty => "A non private class property is always invariant".to_string(),
        PositionDescr::RtypeParameter => format!(
            "The type parameter was declared as {}",
            variance_to_string(*variance)
        ),
        PositionDescr::RfunParameter => "Function parameters are contravariant".to_string(),
        PositionDescr::RfunReturn => "Function return types are covariant".to_string(),
        PositionDescr::RtypeArgument(name) => format!(
            "This type parameter was declared as {} (cf '{}')",
            variance_to_string(*variance),
            name
        ),
        PositionDescr::RconstraintSuper => {
            "`super` constraints on method type parameters are covariant".to_string()
        }
        PositionDescr::RconstraintAs => {
            "`as` constraints on method type parameters are contravariant".to_string()
        }
        PositionDescr::RconstraintEq => {
            "`=` constraints on method type parameters are invariant".to_string()
        }
        PositionDescr::RwhereAs => {
            "`where _ as _` constraints are covariant on the left, contravariant on the right"
                .to_string()
        }
        PositionDescr::RwhereEq => {
            "`where _ = _` constraints are invariant on the left and right".to_string()
        }
        PositionDescr::RwhereSuper => {
            "`where _ super _` constraints are contravariant on the left, covariant on the right"
                .to_string()
        }
        PositionDescr::RcaseTypeWhereAs => {
            "`case type where _ as _` constraints are covariant on the left, contravariant on the right"
                .to_string()
        }
        PositionDescr::RcaseTypeWhereEq => {
            "`case type where _ = _` constraints are invariant on the left and right".to_string()
        }
        PositionDescr::RcaseTypeWhereSuper => {
            "`case type where _ super _` constraints are contravariant on the left, covariant on the right"
                .to_string()
        }
        PositionDescr::RfunInoutParameter => {
            "Inout/ref function parameters are both covariant and contravariant".to_string()
        }
        PositionDescr::RrefinementEq => "exact refinements are invariant".to_string(),
        PositionDescr::RrefinementAs => "`as` refinement bounds are covariant".to_string(),
        PositionDescr::RrefinementSuper => {
            "`super` refinement bounds are contravariant".to_string()
        }
    };
    prefix + &text
}

fn detailed_message(variance: &str, pos: &Pos, stack: &[Reason]) -> Vec<Message<Pos>> {
    match stack {
        [] => vec![],
        [r] => {
            let (p, _, _) = r;
            vec![Message(p.clone(), reason_to_string(false, r).into())]
        }
        _ => {
            let mut msgs = vec![Message(
                pos.clone(),
                reason_stack_to_string(variance, stack).into(),
            )];
            msgs.extend(stack.iter().map(|r| {
                let (p, _, _) = r;
                Message(p.clone(), reason_to_string(true, r).into())
            }));
            msgs
        }
    }
}

// ---------------------------------------------------------------------------
// Converts an annotation (+/-) to a type.
// ---------------------------------------------------------------------------

fn make_variance(reason: PositionDescr, pos: Pos, v: ast_defs::Variance) -> Variance {
    match v {
        ast_defs::Variance::Covariant => {
            Variance::Vcovariant(vec![(pos, reason, PositionVariance::Pcovariant)])
        }
        ast_defs::Variance::Contravariant => {
            Variance::Vcontravariant(vec![(pos, reason, PositionVariance::Pcontravariant)])
        }
        ast_defs::Variance::Invariant => Variance::Vinvariant(
            vec![(pos.clone(), reason.clone(), PositionVariance::Pinvariant)],
            vec![(pos, reason, PositionVariance::Pinvariant)],
        ),
    }
}

// ---------------------------------------------------------------------------
// Used when we want to compose with the variance coming from another class.
// Let's assume: A<-T>
// public function foo(A<T> $x): void;
// A<T> is in contravariant position so we process -A<T>.
// because A is annotated with a minus: we deduce --T (which becomes T).
// ---------------------------------------------------------------------------

fn compose((pos, param_descr): (Pos, PositionDescr), from: &Variance, to_: &Variance) -> Variance {
    // We don't really care how we deduced the variance that we are composing
    // with (_stack_to). That's because the decomposition could be in a different
    // file and would be too hard to follow anyway.
    // Let's consider the following return type: A<T>.
    // Turns out A is declared as A<-T>.
    // It's not a good idea for us to point to what made us deduce that the
    // position was contravariant (the declaration side). Because the user will
    // wonder where it comes from.
    // It's better to point to the return type (more precisely, point to the T
    // in the return type) and explain that this position is contravariant.
    // Later on, the user can go and check the definition of A for herself.
    let cons = |reason: Reason, stack: &[Reason]| {
        let mut l = vec![reason];
        l.extend(stack.iter().cloned());
        l
    };
    match (from, to_) {
        (Variance::Vcovariant(stack_from), Variance::Vcovariant(_stack_to)) => {
            let reason = (pos, param_descr, PositionVariance::Pcovariant);
            Variance::Vcovariant(cons(reason, stack_from))
        }
        (Variance::Vcontravariant(stack_from), Variance::Vcontravariant(_stack_to)) => {
            let reason = (pos, param_descr, PositionVariance::Pcontravariant);
            Variance::Vcovariant(cons(reason, stack_from))
        }
        (Variance::Vcovariant(stack_from), Variance::Vcontravariant(_stack_to)) => {
            let reason = (pos, param_descr, PositionVariance::Pcontravariant);
            Variance::Vcontravariant(cons(reason, stack_from))
        }
        (Variance::Vcontravariant(stack_from), Variance::Vcovariant(_stack_to)) => {
            let reason = (pos, param_descr, PositionVariance::Pcovariant);
            Variance::Vcontravariant(cons(reason, stack_from))
        }
        (x @ Variance::Vinvariant(..), _) => x.clone(),
        (_, Variance::Vinvariant(_co, _contra)) => {
            let reason = (pos, param_descr, PositionVariance::Pinvariant);
            Variance::Vinvariant(vec![reason.clone()], vec![reason])
        }
        (Variance::Vboth, x) | (x, Variance::Vboth) => x.clone(),
    }
}

// ---------------------------------------------------------------------------
// Given a type parameter, returns the declared variance.
// ---------------------------------------------------------------------------

fn get_tparam_variance(env: &env::TypeParameterEnv, name: &str) -> Variance {
    match env.get(name) {
        None => Variance::Vboth,
        Some(x) => x.clone(),
    }
}

// ---------------------------------------------------------------------------
// Given a type parameter, returns the variance declared.
// ---------------------------------------------------------------------------

/// The first `get_declared_variance` of the OCaml (see the module
/// documentation).
fn get_declared_variance_at(pos: Pos, v: ast_defs::Variance) -> Variance {
    make_variance(PositionDescr::RtypeParameter, pos, v)
}

fn make_decl_tparam_variance(t: &DeclTparam) -> Variance {
    get_declared_variance_at(
        pos_or_decl::unsafe_to_raw_pos(t.name.pos().clone().to_oxidized()),
        t.variance,
    )
}

fn get_declared_variance(t: &nast::Tparam) -> Variance {
    get_declared_variance_at(t.name.0.clone(), t.variance)
}

// ---------------------------------------------------------------------------
// Checks that a 'this' type is correctly used at a given contravariant
// position in a final class.
// ---------------------------------------------------------------------------

fn check_final_this_pos_variance(
    env: &TEnv,
    env_variance: &Variance,
    rpos: &Pos,
    class_: &nast::Class_,
) {
    if class_.final_ {
        for t in &class_.tparams {
            match (env_variance, t.variance) {
                (
                    Variance::Vcontravariant(_),
                    ast_defs::Variance::Covariant | ast_defs::Variance::Contravariant,
                ) => typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Contravariant_this {
                        pos: rpos.clone(),
                        class_name: utils::strip_ns(&ast_defs::get_id(&class_.name)).to_string(),
                        typaram_name: t.name.1.clone(),
                    }),
                    env,
                ),
                _ => {}
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Returns the list of type parameter variance for a given class.
//
// N.B.: this function works both with classes and typedefs.
// ---------------------------------------------------------------------------

fn get_class_variance(env: &TEnv, class_name: &str) -> Vec<Variance> {
    let tparams = typing_env::get_class_or_typedef_tparams(env, class_name);
    tparams.iter().map(make_decl_tparam_variance).collect()
}

/// `S_map.union ~combine:(fun _ x y -> Some (x @ y))`
fn union_occurrences(m1: Occurrences, m2: Occurrences) -> Occurrences {
    // (With one side empty the union is the other side: no walk.)
    if m2.is_empty() {
        return m1;
    }
    if m1.is_empty() {
        return m2;
    }
    let mut res = m1;
    for (k, y) in m2 {
        match res.get_mut(&k) {
            Some(x) => x.extend(y),
            None => {
                res.insert(k, y);
            }
        }
    }
    res
}

fn union(
    (pos1, neg1): (Occurrences, Occurrences),
    (pos2, neg2): (Occurrences, Occurrences),
) -> (Occurrences, Occurrences) {
    // (The components of the tuple are computed without effects.)
    (union_occurrences(pos1, pos2), union_occurrences(neg1, neg2))
}

/// The first `flip` of the OCaml (see the module documentation).
fn flip_typarams((pos, neg): (Occurrences, Occurrences)) -> (Occurrences, Occurrences) {
    (neg, pos)
}

fn get_typarams_union(
    tracked: &im::OrdSet<String>,
    tenv: &TEnv,
    acc: (Occurrences, Occurrences),
    ty: &DeclTy,
) -> (Occurrences, Occurrences) {
    let tp = get_typarams(tracked, tenv, ty);
    union(acc, tp)
}

/// `Typing_defs.is_generic_equal_to`, on a declared type.
fn is_generic_equal_to(n: &str, t: &DeclTy) -> bool {
    match t.node_ref() {
        d::Ty_::Tgeneric(n_) if n == n_.as_str() => true,
        _ => false,
    }
}

/// `Typing_defs.get_fp_mode`, on a declared parameter.
fn get_fp_mode(fp: &DeclFunParam) -> ParamMode {
    if fp
        .flags
        .contains(oxidized::typing_defs_flags::FunParamFlags::INOUT)
    {
        ParamMode::FPinout
    } else {
        ParamMode::FPnormal
    }
}

fn get_typarams(
    tracked: &im::OrdSet<String>,
    tenv: &TEnv,
    ty: &DeclTy,
) -> (Occurrences, Occurrences) {
    let empty = || (Occurrences::new(), Occurrences::new());
    let get_typarams_union =
        |acc: (Occurrences, Occurrences), ty: &DeclTy| get_typarams_union(tracked, tenv, acc, ty);
    let get_typarams_list = |tyl: &[DeclTy]| {
        tyl.iter()
            .fold(empty(), |acc, ty| get_typarams_union(acc, ty))
    };
    let get_typarams = |ty: &DeclTy| get_typarams(tracked, tenv, ty);
    let single = |id: &str, pos: &R| {
        (
            Occurrences::unit(id.to_string(), vec![pos.clone()]),
            Occurrences::new(),
        )
    };
    let get_typarams_variance_list = |acc: (Occurrences, Occurrences),
                                      variancel: &[Variance],
                                      tyl: &[DeclTy]| {
        let mut acc = acc;
        for (variance, ty) in variancel.iter().zip(tyl.iter()) {
            let param = get_typarams(ty);
            let param = match variance {
                Variance::Vcovariant(_) => param,
                Variance::Vcontravariant(_) => flip_typarams(param),
                _ => union(param.clone(), flip_typarams(param)),
            };
            acc = union(acc, param)
        }
        acc
    };
    match ty.node_ref() {
        d::Ty_::Tgeneric(id) => {
            // Only count tracked generic parameters
            if tracked.contains(id.as_str()) {
                single(id.as_str(), ty.reason())
            } else {
                empty()
            }
        }
        d::Ty_::Tnonnull
        | d::Ty_::Tdynamic
        | d::Ty_::Tprim(_)
        | d::Ty_::Tany
        | d::Ty_::Tthis
        | d::Ty_::Tmixed
        | d::Ty_::Twildcard => empty(),
        d::Ty_::Toption(ty) | d::Ty_::Tlike(ty) => get_typarams(ty),
        d::Ty_::Taccess(ta) => get_typarams(&ta.ty),
        d::Ty_::Trefinement(tr) => {
            let init = get_typarams(&tr.ty);
            // S_map.fold: in the order of the names (the map of `hackrs` is
            // ordered by name too)
            tr.refinement.consts.iter().fold(init, |acc, (_, rc)| {
                let tp = match &rc.bound {
                    d::RefinedConstBound::Exact(bnd) => {
                        let tp = get_typarams(bnd);
                        union(flip_typarams(tp.clone()), tp)
                    }
                    d::RefinedConstBound::Loose(bnds) => {
                        // Lower bounds on type members are contravariant
                        // while upper bounds are covariant. Interestingly,
                        // this differs from where constraints because,
                        // logically, those sit on the LHS of an
                        // implication while refinements are on the RHS.
                        //   (A => B) |- (A' => B ) if A' |- A
                        //   (A => B) |- (A  => B') if B  |- B'
                        let upper = get_typarams_list(&bnds.upper);
                        let lower = get_typarams_list(&bnds.lower);
                        union(flip_typarams(lower), upper)
                    }
                };
                union(acc, tp)
            })
        }
        d::Ty_::Tunion(tyl) | d::Ty_::Tintersection(tyl) => get_typarams_list(tyl),
        d::Ty_::Ttuple(t) => {
            let d::TupleType(t_required, t_optional, t_extra) = &**t;
            let t_vs = match t_extra {
                d::TupleExtra::Tvariadic(t_vs) | d::TupleExtra::Tsplat(t_vs) => t_vs,
            };
            let vs = get_typarams(t_vs);
            let required = get_typarams_list(t_required);
            let optional = get_typarams_list(t_optional);
            union(optional, union(required, vs))
        }
        d::Ty_::Tshape(st) => match &**st {
            d::ShapeType::Simple(d::ShapeTypeSimple(s_unknown_value, m)) => {
                // TShapeMap.fold: in the order of the names of the fields
                let mut fields: Vec<_> = m.iter().collect();
                fields.sort_by(|a, b| decl_tshape_field_name_compare(a.0, b.0));
                fields
                    .into_iter()
                    .fold(get_typarams(s_unknown_value), |res, (_, sft)| {
                        get_typarams_union(res, &sft.ty)
                    })
            }
            d::ShapeType::Splat(ss_elems) => ss_elems
                .iter()
                .fold(empty(), |acc, ty| get_typarams_union(acc, ty)),
        },
        d::Ty_::Tfun(ft) => {
            let get_typarams_param = |acc: (Occurrences, Occurrences), fp: &DeclFunParam| {
                let tp = get_typarams(&fp.ty);
                let tp = match get_fp_mode(fp) {
                    // Parameters behave contravariantly
                    ParamMode::FPnormal => flip_typarams(tp),
                    // Inout parameters behave both co- and contra-variantly
                    ParamMode::FPinout => union(tp.clone(), flip_typarams(tp)),
                };
                union(acc, tp)
            };
            let params = ft
                .params
                .iter()
                .fold(empty(), |acc, fp| get_typarams_param(acc, fp));
            let implicit_params = {
                let d::FunImplicitParams { capability } = &ft.implicit_params;
                match capability {
                    d::Capability::CapDefaults(_) => empty(),
                    d::Capability::CapTy(ty) => get_typarams(ty),
                }
            };
            let ret = get_typarams(&ft.ret);
            let get_typarams_constraint =
                |acc: (Occurrences, Occurrences), (ck, ty): &(ConstraintKind, DeclTy)| {
                    let tp = match ck {
                        ConstraintKind::ConstraintAs => get_typarams(ty),
                        ConstraintKind::ConstraintEq => {
                            let tp = get_typarams(ty);
                            union(flip_typarams(tp.clone()), tp)
                        }
                        ConstraintKind::ConstraintSuper => flip_typarams(get_typarams(ty)),
                    };
                    union(acc, tp)
                };
            let get_typarams_tparam = |acc: (Occurrences, Occurrences), tp: &DeclTparam| {
                tp.constraints
                    .iter()
                    .fold(acc, |acc, c| get_typarams_constraint(acc, c))
            };
            let bounds = ft
                .tparams
                .iter()
                .fold(empty(), |acc, tp| get_typarams_tparam(acc, tp));
            let get_typarams_where_constraint =
                |acc: (Occurrences, Occurrences), d::WhereConstraint(ty1, ck, ty2): &DeclWhereConstraint| {
                    let tp = match ck {
                        ConstraintKind::ConstraintSuper => {
                            let tp2 = get_typarams(ty2);
                            let tp1 = get_typarams(ty1);
                            union(flip_typarams(tp1), tp2)
                        }
                        ConstraintKind::ConstraintAs => {
                            let tp2 = get_typarams(ty2);
                            let tp1 = get_typarams(ty1);
                            union(tp1, flip_typarams(tp2))
                        }
                        ConstraintKind::ConstraintEq => {
                            let tp2 = get_typarams(ty2);
                            let tp1 = get_typarams(ty1);
                            let tp = union(tp1, tp2);
                            union(tp.clone(), flip_typarams(tp))
                        }
                    };
                    union(acc, tp)
                };
            let constrs = ft
                .where_constraints
                .iter()
                .fold(empty(), |acc, wc| get_typarams_where_constraint(acc, wc));

            // Result so far: bounds, constraints, return, parameters
            // (params |> union implicit_params |> union ret |> union constrs |> union bounds)
            let result = union(bounds, union(constrs, union(ret, union(implicit_params, params))));

            // Get the lower bounds of a type parameter, including where constraints
            // of the form `where t as T` or `where T super t`
            let get_lower_bounds = |tp: &DeclTparam| -> Vec<DeclTy> {
                let name = tp.name.id_ref().as_str();
                let mut l: Vec<DeclTy> = tp
                    .constraints
                    .iter()
                    .filter_map(|(ck, ty)| match ck {
                        ConstraintKind::ConstraintSuper | ConstraintKind::ConstraintEq => {
                            Some(ty.clone())
                        }
                        _ => None,
                    })
                    .collect();
                l.extend(
                    ft.where_constraints
                        .iter()
                        .filter_map(|d::WhereConstraint(ty1, ck, ty2)| match ck {
                            ConstraintKind::ConstraintAs | ConstraintKind::ConstraintEq
                                if is_generic_equal_to(name, ty2) =>
                            {
                                Some(ty1.clone())
                            }
                            ConstraintKind::ConstraintSuper | ConstraintKind::ConstraintEq
                                if is_generic_equal_to(name, ty1) =>
                            {
                                Some(ty2.clone())
                            }
                            _ => None,
                        }),
                );
                l
            };

            // Get the upper bounds of a type parameter, including where constraints
            // of the form `where T as t` or `where t super T`
            let get_upper_bounds = |tp: &DeclTparam| -> Vec<DeclTy> {
                let name = tp.name.id_ref().as_str();
                let mut l: Vec<DeclTy> = tp
                    .constraints
                    .iter()
                    .filter_map(|(ck, ty)| match ck {
                        ConstraintKind::ConstraintAs | ConstraintKind::ConstraintEq => {
                            Some(ty.clone())
                        }
                        _ => None,
                    })
                    .collect();
                l.extend(
                    ft.where_constraints
                        .iter()
                        .filter_map(|d::WhereConstraint(ty1, ck, ty2)| match ck {
                            ConstraintKind::ConstraintAs | ConstraintKind::ConstraintEq
                                if is_generic_equal_to(name, ty1) =>
                            {
                                Some(ty2.clone())
                            }
                            ConstraintKind::ConstraintSuper | ConstraintKind::ConstraintEq
                                if is_generic_equal_to(name, ty2) =>
                            {
                                Some(ty1.clone())
                            }
                            _ => None,
                        }),
                );
                l
            };

            // If a type parameter appears covariantly, then treat its lower bounds as covariant
            let propagate_covariant_to_lower_bounds =
                |tp: &DeclTparam| get_typarams_list(&get_lower_bounds(tp));

            // If a type parameter appears contravariantly, then treat its upper bounds as contravariant
            let propagate_contravariant_to_upper_bounds =
                |tp: &DeclTparam| flip_typarams(get_typarams_list(&get_upper_bounds(tp)));

            // Given a type parameter, propagate its variance (co and/or contra) to lower and upper bounds
            // as appropriate. See Typing_env.set_tyvar_appears_covariantly_and_propagate etc for an
            // analagous calculation for type variables.
            let propagate_typarams_tparam = |acc: (Occurrences, Occurrences), tp: &DeclTparam| {
                let name = tp.name.id_ref().as_str();
                let acc = if result.0.contains_key(name) {
                    union(acc, propagate_covariant_to_lower_bounds(tp))
                } else {
                    acc
                };
                let acc = if result.1.contains_key(name) {
                    union(acc, propagate_contravariant_to_upper_bounds(tp))
                } else {
                    acc
                };
                acc
            };
            ft.tparams
                .iter()
                .fold(result.clone(), |acc, tp| propagate_typarams_tparam(acc, tp))
        }
        d::Ty_::Tapply(id_and_tyl) => {
            let (id, tyl) = &**id_and_tyl;
            let variancel = get_class_variance(tenv, id.id_ref().as_str());
            get_typarams_variance_list(empty(), &variancel, tyl)
        }
        d::Ty_::TvecOrDict(tys) => {
            let (ty1, ty2) = &**tys;
            let tp2 = get_typarams(ty2);
            let tp1 = get_typarams(ty1);
            union(tp1, tp2)
        }
        d::Ty_::TclassPtr(ty) => get_typarams(ty),
    }
}

/// Get (positive,negative) occurrences of generic parameters in a type.
/// Only collect those present in tracked. If is_mutable is true, treat the
/// type as invariant, i.e. all type parameters appear both positively and negatively.
pub fn get_positive_negative_generics(
    tracked: &im::OrdSet<String>,
    is_mutable: bool,
    env: &TEnv,
    acc: (Occurrences, Occurrences),
    ty: &DeclTy,
) -> (Occurrences, Occurrences) {
    let r = get_typarams(tracked, env, ty);
    if is_mutable {
        union(acc, union(r.clone(), flip_typarams(r)))
    } else {
        union(acc, r)
    }
}

fn generic_(tyenv: &TEnv, env: &env::TypeParameterEnv, variance: &Variance, name: &str) {
    let declared_variance = get_tparam_variance(env, name);
    let hd = |stack: &[Reason]| -> Pos {
        match stack.first() {
            Some((pos, _, _)) => pos.clone(),
            None => panic!("hd_exn"),
        }
    };
    match (&declared_variance, variance) {
        // Happens if type parameter isn't from class
        (Variance::Vboth, _) | (_, Variance::Vboth) => {}
        (Variance::Vinvariant(..), _)
        | (Variance::Vcovariant(_), Variance::Vcovariant(_))
        | (Variance::Vcontravariant(_), Variance::Vcontravariant(_)) => {}
        (
            Variance::Vcovariant(stack1),
            Variance::Vcontravariant(stack2) | Variance::Vinvariant(_, stack2),
        ) => {
            let pos1 = hd(stack1);
            let pos2 = hd(stack2);
            let emsg = {
                let pos2 = pos2.clone();
                let stack2 = stack2.clone();
                typing_error::Lazy::new(move || {
                    detailed_message("contravariant (-)", &pos2, &stack2)
                })
            };
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Declared_covariant {
                    param_pos: pos1,
                    pos: pos2,
                    msgs: emsg,
                }),
                tyenv,
            )
        }
        (
            Variance::Vcontravariant(stack1),
            Variance::Vcovariant(stack2) | Variance::Vinvariant(stack2, _),
        ) => {
            let pos1 = hd(stack1);
            let pos2 = hd(stack2);
            let emsg = {
                let pos2 = pos2.clone();
                let stack2 = stack2.clone();
                typing_error::Lazy::new(move || detailed_message("covariant (+)", &pos2, &stack2))
            };
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Declared_contravariant {
                    param_pos: pos2,
                    pos: pos1,
                    msgs: emsg,
                }),
                tyenv,
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Used for the arguments of function.
// ---------------------------------------------------------------------------

fn flip(reason: Reason, v: &Variance) -> Variance {
    match v {
        Variance::Vcovariant(stack) => {
            let mut l = vec![reason];
            l.extend(stack.iter().cloned());
            Variance::Vcontravariant(l)
        }
        Variance::Vcontravariant(stack) => {
            let mut l = vec![reason];
            l.extend(stack.iter().cloned());
            Variance::Vcovariant(l)
        }
        x @ Variance::Vinvariant(..) => x.clone(),
        Variance::Vboth => Variance::Vboth,
    }
}

fn detail(reason: Reason, v: &Variance) -> Variance {
    match v {
        Variance::Vcovariant(stack) => {
            let mut l = vec![reason];
            l.extend(stack.iter().cloned());
            Variance::Vcovariant(l)
        }
        Variance::Vcontravariant(stack) => {
            let mut l = vec![reason];
            l.extend(stack.iter().cloned());
            Variance::Vcontravariant(l)
        }
        variance => variance.clone(),
    }
}

fn hint(env: &env::T<'_>, variance: &Variance, h: &aast::Hint) {
    let aast::Hint(pos, h) = h;
    match &**h {
        aast::Hint_::Habstr(name) => {
            // This section makes the position more precise.
            // Say we find a return type that is a tuple (int, int, T).
            // The whole tuple is in covariant position, and so the position
            // is going to include the entire tuple.
            // That can make things pretty unreadable when the type is long.
            // Here we replace the position with the exact position of the generic
            // that was problematic.
            let variance = match variance {
                Variance::Vcovariant(stack)
                    if matches!(stack.first(), Some((pos_, _, _)) if !crate::pos::equal(pos, pos_)) =>
                {
                    let mut stack = stack.clone();
                    stack[0].0 = pos.clone();
                    Variance::Vcovariant(stack)
                }
                Variance::Vcontravariant(stack)
                    if matches!(stack.first(), Some((pos_, _, _)) if !crate::pos::equal(pos, pos_)) =>
                {
                    let mut stack = stack.clone();
                    stack[0].0 = pos.clone();
                    Variance::Vcontravariant(stack)
                }
                x => x.clone(),
            };
            generic_(env.env, &env.tpenv, &variance, name)
        }
        aast::Hint_::Hmixed
        | aast::Hint_::Hwildcard
        | aast::Hint_::Hnonnull
        | aast::Hint_::Hdynamic
        | aast::Hint_::Hnothing
        | aast::Hint_::Hvar(_)
        | aast::Hint_::HfunContext(_)
        | aast::Hint_::Hprim(_) => {}
        aast::Hint_::HvecOrDict(hk, hv) => {
            if let Some(hk) = hk {
                hint(env, variance, hk)
            }
            hint(env, variance, hv)
        }
        aast::Hint_::Hthis => {
            // Check that 'this' isn't being improperly referenced in a contravariant
            // position.
            // With the exception of that check, `this` constraints are bivariant
            // (otherwise any class that used the `this` type would not be able to use
            // covariant type params).
            if let Some(class_) = env.enclosing_class {
                check_final_this_pos_variance(env.env, variance, pos, class_)
            }
        }
        aast::Hint_::HclassPtr(_, h)
        | aast::Hint_::Hoption(h)
        | aast::Hint_::Hlike(h)
        | aast::Hint_::Hsoft(h)
        | aast::Hint_::Haccess(h, _) => hint(env, variance, h),
        aast::Hint_::Hunion(tyl) | aast::Hint_::Hintersection(tyl) => {
            hint_list(env, variance, tyl)
        }
        aast::Hint_::Htuple(aast::TupleInfo {
            required: tup_required,
            extra: tup_extra,
        }) => {
            hint_list(env, variance, tup_required);
            match tup_extra {
                aast::TupleExtra::Hextra(aast::TupleExtraInfo {
                    optional: tup_optional,
                    variadic: tup_variadic,
                }) => {
                    hint_list(env, variance, tup_optional);
                    if let Some(h) = tup_variadic {
                        hint(env, variance, h)
                    }
                }
                aast::TupleExtra::Hsplat(tup_splat) => hint(env, variance, tup_splat),
            }
        }
        aast::Hint_::Hshape(aast::NastShapeInfo {
            allows_unknown_fields: _,
            field_map: nsi_field_map,
            unknown_fields_type: nsi_unknown_fields_type,
        }) => {
            for e in nsi_field_map {
                match e {
                    aast::ShapeElement::SEField(aast::ShapeFieldInfo {
                        hint: sfi_hint,
                        optional: _,
                        name: _,
                    }) => hint(env, variance, sfi_hint),
                    aast::ShapeElement::SESplat(h) => hint(env, variance, h),
                }
            }
            if let Some(h) = nsi_unknown_fields_type {
                hint(env, variance, h)
            }
        }
        aast::Hint_::Hrefinement(h, members) => {
            for member in members {
                refinement_member(env, variance, member)
            }
            hint(env, variance, h)
        }
        aast::Hint_::Hfun(hfun) => {
            let aast::HintFun {
                is_readonly: _,
                tparams: _,
                param_tys: hf_param_tys,
                param_info: hf_param_info,
                variadic_ty: hf_variadic_ty,
                named_variadic_ty: hf_named_variadic_ty,
                return_ty: hf_return_ty,
                ctxs: _,
                is_readonly_return: _,
            } = hfun;
            // List.iter2_exn
            if hf_param_info.len() != hf_param_tys.len() {
                panic!(
                    "length mismatch in iter2_exn: {} <> {}",
                    hf_param_info.len(),
                    hf_param_tys.len()
                )
            }
            for (info, h) in hf_param_info.iter().zip(hf_param_tys.iter()) {
                hfun_param(env, variance, info.as_ref(), h)
            }
            fun_arity(env, variance, hf_variadic_ty.as_ref());
            fun_arity(env, variance, hf_named_variadic_ty.as_ref());
            fun_ret(env, variance, hf_return_ty)
        }
        aast::Hint_::Happly(_, hl) if hl.is_empty() => {}
        aast::Hint_::Happly(name, hl) => {
            let variancel = get_class_variance(env.env, &ast_defs::get_id(name));
            // Utils.iter2_shortest
            for (tparam_variance, h) in variancel.iter().zip(hl.iter()) {
                let pos = h.0.clone();
                let reason = PositionDescr::RtypeArgument(
                    utils::strip_ns(&ast_defs::get_id(name)).to_string(),
                );
                let variance = compose((pos, reason), variance, tparam_variance);
                hint(env, &variance, h)
            }
        }
    }
}

fn hint_list(env: &env::T<'_>, variance: &Variance, tyl: &[aast::Hint]) {
    for h in tyl {
        hint(env, variance, h)
    }
}

fn hfun_param(
    env: &env::T<'_>,
    variance: &Variance,
    info: Option<&aast::HfParamInfo>,
    h: &aast::Hint,
) {
    let pos = h.0.clone();
    match info.map(|x| &x.kind) {
        None | Some(ParamKind::Pnormal) => {
            let reason = (pos, PositionDescr::RfunParameter, PositionVariance::Pcontravariant);
            let variance = flip(reason, variance);
            hint(env, &variance, h)
        }
        Some(ParamKind::Pinout(_)) => {
            let variance = make_variance(
                PositionDescr::RfunInoutParameter,
                pos,
                ast_defs::Variance::Invariant,
            );
            hint(env, &variance, h)
        }
    }
}

fn fun_ret(env: &env::T<'_>, variance: &Variance, h: &aast::Hint) {
    let pos = h.0.clone();
    let reason_covariant = (pos, PositionDescr::RfunReturn, PositionVariance::Pcovariant);
    let variance = detail(reason_covariant, variance);
    hint(env, &variance, h)
}

fn fun_arity(env: &env::T<'_>, variance: &Variance, h: Option<&aast::Hint>) {
    let empty_param_info = None;
    if let Some(h) = h {
        hfun_param(env, variance, empty_param_info, h)
    }
}

fn refinement_member(env: &env::T<'_>, variance: &Variance, member: &aast::Refinement) {
    let check_exact = |h: &aast::Hint| {
        let pos = h.0.clone();
        let reason = vec![(pos, PositionDescr::RrefinementEq, PositionVariance::Pinvariant)];
        let var = Variance::Vinvariant(reason.clone(), reason);
        hint(env, &var, h)
    };
    let check_loose = |(lower, upper): (&[aast::Hint], &[aast::Hint])| {
        for h in lower {
            let pos = h.0.clone();
            let reason = (
                pos,
                PositionDescr::RrefinementSuper,
                PositionVariance::Pcontravariant,
            );
            let var = flip(reason, variance);
            hint(env, &var, h)
        }
        for h in upper {
            let pos = h.0.clone();
            let reason = (pos, PositionDescr::RrefinementAs, PositionVariance::Pcovariant);
            let var = detail(reason, variance);
            hint(env, &var, h)
        }
    };
    match member {
        aast::Refinement::Rtype(_, ref_) => match ref_ {
            aast::TypeRefinement::TRexact(h) => check_exact(h),
            aast::TypeRefinement::TRloose(aast::TypeRefinementBounds {
                lower: lb,
                upper: ub,
            }) => check_loose((lb, ub)),
        },
        aast::Refinement::Rctx(_, ref_) => match ref_ {
            aast::CtxRefinement::CRexact(h) => check_exact(h),
            aast::CtxRefinement::CRloose(aast::CtxRefinementBounds {
                lower: lb,
                upper: ub,
            }) => check_loose((lb.as_slice(), ub.as_slice())),
        },
    }
}

fn fun_param(env: &env::T<'_>, variance: &Variance, param: &nast::FunParam) {
    let aast::FunParam {
        type_hint: aast::TypeHint(_, h),
        pos: _,
        name: _,
        annotation: _,
        info: _,
        readonly: _,
        splat: param_splat,
        callconv: param_callconv,
        named: _,
        user_attributes: _,
        visibility: _,
    } = param;
    if let Some(h) = h {
        hfun_param(
            env,
            variance,
            Some(&aast::HfParamInfo {
                kind: param_callconv.clone(),
                readonlyness: None,
                optional: None,
                splat: *param_splat,
                named: None,
            }),
            h,
        )
    }
}

fn fun_where_constraint(env: &env::T<'_>, wc: &aast::WhereConstraintHint) {
    let aast::WhereConstraintHint(h1, ck, h2) = wc;
    let pos1 = h1.0.clone();
    let pos2 = h2.0.clone();
    match ck {
        ConstraintKind::ConstraintSuper => {
            let var1 = Variance::Vcontravariant(vec![(
                pos1,
                PositionDescr::RwhereSuper,
                PositionVariance::Pcontravariant,
            )]);
            let var2 = Variance::Vcovariant(vec![(
                pos2,
                PositionDescr::RwhereSuper,
                PositionVariance::Pcovariant,
            )]);
            hint(env, &var1, h1);
            hint(env, &var2, h2)
        }
        ConstraintKind::ConstraintEq => {
            let reason1 = vec![(pos1, PositionDescr::RwhereEq, PositionVariance::Pinvariant)];
            let reason2 = vec![(pos2, PositionDescr::RwhereEq, PositionVariance::Pinvariant)];
            let var = Variance::Vinvariant(reason1, reason2);
            hint(env, &var, h1);
            hint(env, &var, h2)
        }
        ConstraintKind::ConstraintAs => {
            let var1 = Variance::Vcovariant(vec![(
                pos1,
                PositionDescr::RwhereAs,
                PositionVariance::Pcovariant,
            )]);
            let var2 = Variance::Vcontravariant(vec![(
                pos2,
                PositionDescr::RwhereAs,
                PositionVariance::Pcontravariant,
            )]);
            hint(env, &var1, h1);
            hint(env, &var2, h2)
        }
    }
}

/// `as` constraints on method type parameters must be contravariant
/// and `super` constraints on method type parameters are covariant. To
/// see why, suppose that we allow the wrong variance:
///
/// ```text
///   class Foo<+T> {
///     public function bar<Tu as T>(Tu $x) {}
///   }
/// ```
///
/// Let A and B be classes, with B a subtype of A. Then
///
/// ```text
///   function f(Foo<A> $x) {
///     $x->(new A());
///   }
/// ```
///
/// typechecks. However, covariance means that we could call `f()` with an
/// instance of B. However, B::bar would expect its argument $x to be a subtype
/// of B, but we would be passing an instance of A to it, which should be a type
/// error. In other words, `as` constraints are upper type bounds, and since
/// subtypes must have more relaxed constraints than their supertypes, `as`
/// constraints must be contravariant. (Reversing this argument shows that
/// `super` constraints must be covariant.)
///
/// The preceding discussion might lead one to think that the constraints should
/// have the same variance as the class parameter types, i.e. that `as`
/// constraints used in the return type should be covariant. In particular,
/// suppose
///
/// ```text
///   class Foo<-T> {
///     public function bar<Tu as T>(Tu $x): Tu { ... }
///     public function baz<Tu as T>(): Tu { ... }
///   }
///
///   class A {}
///   class B extends A {
///     public function qux() {}
///   }
///
///   function f(Foo<B> $x) {
///     $x->baz()->qux();
///   }
/// ```
///
/// Now `f($x)` could be a runtime error if `$x` was an instance of Foo<A>, and
/// it seems like we should enforce covariance on Tu. However, the real problem
/// is that constraints apply to _instantiation_, not usage. As far as Hack
/// knows, $x->bar() could be of any type, since we have not provided any clues
/// about how `Tu` should be instantiated. In fact `$x->bar()->whatever()`
/// succeeds as well, because `Tu` is of type Tany -- though in an ideal world
/// we would make it Tmixed in order to ensure soundness. Also, the signature
/// of `baz()` doesn't entirely make sense -- why constrain Tu if it it's only
/// getting used in one place?
///
/// Thus, if one wants type safety, how `$x` _should_ be used is
///
/// ```text
///   function f(Foo<B> $x) {
///     $x->bar(new B()))->qux();
///   }
/// ```
///
/// Thus we can see that, if `$x` is used correctly (or if we enforced correct
/// use by returning Tmixed for uninstantiated type variables), we would always
/// know the exact type of Tu, and Tu can be validly used in both co- and
/// contravariant positions.
///
/// Remark: This is far more intuitive if you think about how Vector::concat is
/// typed with its `Tu super T` type in both the parameter and return type
/// positions. Uninstantiated `super` types are less likely to cause confusion,
/// however -- you can't imagine doing very much with a returned value that is
/// some (unspecified) supertype of a class.
fn tparam_constraint(env: &env::T<'_>, (ck, h): &(ConstraintKind, aast::Hint)) {
    let pos = h.0.clone();
    let var = match ck {
        ConstraintKind::ConstraintAs => Variance::Vcontravariant(vec![(
            pos,
            PositionDescr::RconstraintAs,
            PositionVariance::Pcontravariant,
        )]),
        ConstraintKind::ConstraintEq => {
            let reasons = vec![(pos, PositionDescr::RconstraintEq, PositionVariance::Pinvariant)];
            Variance::Vinvariant(reasons.clone(), reasons)
        }
        ConstraintKind::ConstraintSuper => Variance::Vcovariant(vec![(
            pos,
            PositionDescr::RconstraintSuper,
            PositionVariance::Pcovariant,
        )]),
    };
    hint(env, &var, h)
}

fn method_tparam<'a>(env: env::T<'a>, tparam: &nast::Tparam) -> env::T<'a> {
    let aast::Tparam {
        variance: _,
        name: tp_name,
        constraints: tp_constraints,
        reified: _,
        user_attributes: _,
    } = tparam;
    for c in tp_constraints {
        tparam_constraint(&env, c)
    }
    let env = env::remove_type_parameter(&env, &ast_defs::get_id(tp_name));
    env
}

fn class_property(env: &env::T<'_>, prop: &nast::ClassVar) {
    if let Some(h) = &prop.type_.1 {
        if prop.is_static {
            // Static properties should not be generic at all. This is checked in
            // Typing_toplevel.check_no_generic_static_property on the class decl,
            // Since we need properties imported from traits as well.
        } else {
            match prop.visibility {
                aast::Visibility::Private
                    if !naming_attributes::mem(
                        sn::user_attributes::TESTS_BYPASS_VISIBILITY,
                        &prop.user_attributes.0,
                    ) => {}
                aast::Visibility::Private
                | aast::Visibility::Public
                | aast::Visibility::Protected
                | aast::Visibility::Internal
                | aast::Visibility::ProtectedInternal => {
                    let variance = make_variance(
                        PositionDescr::Rproperty,
                        h.0.clone(),
                        ast_defs::Variance::Invariant,
                    );
                    hint(env, &variance, h)
                }
            }
        }
    }
}

fn class_method(env: &env::T<'_>, class_: &nast::Class_, method_: &nast::Method_) {
    let aast::Method_ {
        visibility: m_visibility,
        final_: m_final,
        static_: m_static,
        tparams: m_tparams,
        params: m_params,
        readonly_this: _,
        ret: aast::TypeHint(_, m_ret),
        name: ast_defs::Id(_, m_name),
        where_constraints: m_where_constraints,
        ctxs: _,
        unsafe_ctxs: _,
        span: _,
        annotation: _,
        abstract_: _,
        body: _,
        fun_kind: _,
        user_attributes: m_user_attributes,
        readonly_ret: _,
        external: _,
        hidden: _,
        doc_comment: _,
    } = method_;
    if m_name == sn::members::__CONSTRUCT {
    } else {
        match m_visibility {
            aast::Visibility::Private
                if !naming_attributes::mem(
                    sn::user_attributes::TESTS_BYPASS_VISIBILITY,
                    &m_user_attributes.0,
                ) => {}
            aast::Visibility::Private
            | aast::Visibility::Public
            | aast::Visibility::Protected
            | aast::Visibility::Internal
            | aast::Visibility::ProtectedInternal => {
                if (class_.final_ || *m_final) && *m_static {
                } else {
                    let env = m_tparams
                        .iter()
                        .fold(env.clone(), |env, tp| method_tparam(env, tp));
                    let variance = Variance::Vcovariant(vec![]);
                    for p in m_params {
                        fun_param(&env, &variance, p)
                    }
                    if let Some(h) = m_ret {
                        fun_ret(&env, &variance, h)
                    }
                    for wc in m_where_constraints {
                        fun_where_constraint(&env, wc)
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The entry point (for classes).
// ---------------------------------------------------------------------------

fn props_from_constructors(methods: &[nast::Method_]) -> Vec<nast::ClassVar> {
    let constructors = methods
        .iter()
        .filter(|m| ast_defs::get_id(&m.name) == sn::members::__CONSTRUCT);
    constructors
        .flat_map(|m| {
            m.params
                .iter()
                .filter_map(|param| {
                    let aast::FunParam {
                        type_hint: param_type_hint,
                        pos: param_pos,
                        name: param_name,
                        annotation: (),
                        readonly: param_readonly,
                        info: _,
                        splat: _,
                        callconv: _,
                        named: _,
                        user_attributes: param_user_attributes,
                        visibility: param_visibility,
                    } = param;
                    param_visibility.map(|cv_visibility| aast::ClassVar {
                        final_: false,
                        xhp_attr: None,
                        abstract_: false,
                        visibility: cv_visibility,
                        readonly: param_readonly.is_some(),
                        type_: param_type_hint.clone(),
                        id: ast_defs::Id(param_pos.clone(), param_name.clone()),
                        expr: crate::aast_utils::get_param_default(param).cloned(),
                        user_attributes: param_user_attributes.clone(),
                        doc_comment: None,
                        is_static: false,
                        span: param_pos.clone(),
                    })
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Check a class definition for correct usage of variant generic parameters
pub fn class_def(env: &TEnv, class_: &nast::Class_) {
    let aast::Class_ {
        tparams: c_tparams,
        extends: c_extends,
        uses: c_uses,
        implements: c_implements,
        vars: c_vars,
        methods: c_methods,
        final_: _,
        typeconsts: _, // TODO
        kind: _,
        span: _,
        annotation: _,
        mode: _,
        is_xhp: _,
        has_xhp_keyword: _,
        name: _,
        xhp_attr_uses: _,
        xhp_category: _,
        reqs: _,
        consts: _,
        xhp_children: _,
        xhp_attrs: _,
        namespace: _,
        user_attributes: _,
        file_attributes: _,
        module: _,
        enum_: _,
        doc_comment: _,
        emit_id: _,
        internal: _,
        docs_url: _,
        package: _,
    } = class_;
    let env = env::T {
        tpenv: c_tparams.iter().fold(im::OrdMap::new(), |env, tp| {
            let mut env = env;
            env.insert(tp.name.1.clone(), get_declared_variance(tp));
            env
        }),
        enclosing_class: Some(class_),
        env,
    };
    let parents = c_extends.iter().chain(c_implements.iter()).chain(c_uses.iter());
    for h in parents {
        hint(&env, &Variance::Vboth, h)
    }
    let props = props_from_constructors(c_methods);
    for prop in c_vars.iter().chain(props.iter()) {
        class_property(&env, prop)
    }
    for m in c_methods {
        class_method(&env, class_, m)
    }
}

/// in case type where clauses:
///    `as` constraints are contravariant on the left and covariant on the right
///    `super` constraints are covariant on the left and contravariant on the right
fn case_type_where_constraint(env: &env::T<'_>, wc: &aast::WhereConstraintHint) {
    let aast::WhereConstraintHint(h1, ck, h2) = wc;
    let pos1 = h1.0.clone();
    let pos2 = h2.0.clone();
    match ck {
        ConstraintKind::ConstraintSuper => {
            let var1 = Variance::Vcovariant(vec![(
                pos1,
                PositionDescr::RcaseTypeWhereSuper,
                PositionVariance::Pcovariant,
            )]);
            let var2 = Variance::Vcontravariant(vec![(
                pos2,
                PositionDescr::RcaseTypeWhereSuper,
                PositionVariance::Pcontravariant,
            )]);
            hint(env, &var1, h1);
            hint(env, &var2, h2)
        }
        ConstraintKind::ConstraintEq => {
            let reason1 = vec![(
                pos1,
                PositionDescr::RcaseTypeWhereEq,
                PositionVariance::Pinvariant,
            )];
            let reason2 = vec![(
                pos2,
                PositionDescr::RcaseTypeWhereEq,
                PositionVariance::Pinvariant,
            )];
            let var = Variance::Vinvariant(reason1, reason2);
            hint(env, &var, h1);
            hint(env, &var, h2)
        }
        ConstraintKind::ConstraintAs => {
            let var1 = Variance::Vcontravariant(vec![(
                pos1,
                PositionDescr::RcaseTypeWhereAs,
                PositionVariance::Pcontravariant,
            )]);
            let var2 = Variance::Vcovariant(vec![(
                pos2,
                PositionDescr::RcaseTypeWhereAs,
                PositionVariance::Pcovariant,
            )]);
            hint(env, &var1, h1);
            hint(env, &var2, h2)
        }
    }
}

// ---------------------------------------------------------------------------
// The entry point (for typedefs).
// ---------------------------------------------------------------------------

/// Check a type definition for correct usage of variant generic parameters
pub fn typedef(env: &TEnv, typedef: &nast::Typedef) {
    let aast::Typedef {
        tparams: t_tparams,
        assignment: t_assignment,
        runtime_type: _,
        annotation: _,
        name: _,
        as_constraint: _,
        super_constraint: _,
        user_attributes: _,
        mode: _,
        namespace: _,
        span: _,
        emit_id: _,
        is_ctx: _,
        file_attributes: _,
        internal: _,
        module: _,
        docs_url: _,
        doc_comment: _,
        package: _,
    } = typedef;
    let (hints, where_constraints): (Vec<&aast::Hint>, Vec<&aast::WhereConstraintHint>) =
        match t_assignment {
            aast::TypedefAssignment::SimpleTypeDef(aast::TypedefVisibilityAndHint {
                vis: _,
                hint: tvh_hint,
            }) => (vec![tvh_hint], vec![]),
            aast::TypedefAssignment::CaseType(variant, variants) => {
                let variants: Vec<&aast::TypedefCaseTypeVariant> =
                    std::iter::once(variant).chain(variants.iter()).collect();
                let hints = variants.iter().map(|v| &v.hint).collect();
                let where_constraints = variants
                    .iter()
                    .flat_map(|v| v.where_constraints.iter())
                    .collect();
                (hints, where_constraints)
            }
        };
    let env = env::T {
        tpenv: t_tparams.iter().fold(im::OrdMap::new(), |env, tp| {
            let mut env = env;
            env.insert(tp.name.1.clone(), get_declared_variance(tp));
            env
        }),
        enclosing_class: None,
        env,
    };
    for t_kind in hints {
        let reason_covariant = vec![(
            t_kind.0.clone(),
            PositionDescr::Rtypedef,
            PositionVariance::Pcovariant,
        )];
        hint(&env, &Variance::Vcovariant(reason_covariant), t_kind)
    }
    for wc in where_constraints {
        case_type_where_constraint(&env, wc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p() -> Pos {
        Pos::NONE
    }

    #[test]
    fn compose_signs() {
        let co = Variance::Vcovariant(vec![(p(), PositionDescr::RfunReturn, PositionVariance::Pcovariant)]);
        let contra = Variance::Vcontravariant(vec![(
            p(),
            PositionDescr::RfunParameter,
            PositionVariance::Pcontravariant,
        )]);
        let r = || (p(), PositionDescr::RtypeArgument("A".to_string()));
        // --T is T
        match compose(r(), &contra, &contra) {
            Variance::Vcovariant(stack) => {
                assert_eq!(stack.len(), 2);
                assert_eq!(stack[0].2, PositionVariance::Pcontravariant);
            }
            v => panic!("{:?}", v),
        }
        match compose(r(), &co, &contra) {
            Variance::Vcontravariant(stack) => assert_eq!(stack.len(), 2),
            v => panic!("{:?}", v),
        }
        assert_eq!(compose(r(), &Variance::Vboth, &co), co);
        assert_eq!(compose(r(), &co, &Variance::Vboth), co);
    }

    #[test]
    fn messages() {
        let stack = vec![
            (p(), PositionDescr::RfunReturn, PositionVariance::Pcovariant),
            (p(), PositionDescr::RfunParameter, PositionVariance::Pcontravariant),
        ];
        let msgs = detailed_message("covariant (+)", &p(), &stack);
        assert_eq!(msgs.len(), 3);
        assert!(
            msgs[0]
                .1
                .to_string()
                .starts_with("This position is covariant (+) because it is the composition of (+)(-)\n")
        );
        assert_eq!(
            msgs[2].1.to_string(),
            "(-) Function parameters are contravariant"
        );
        let one = detailed_message("covariant (+)", &p(), &stack[..1]);
        assert_eq!(one[0].1.to_string(), "Function return types are covariant");
    }
}
