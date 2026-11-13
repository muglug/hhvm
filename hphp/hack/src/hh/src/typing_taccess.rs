// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_taccess.ml`. See `hh/PORTING.md`.
//!
//! The OCaml type `result` is [`Result`] (as the naming rules say); the
//! standard `Result` is written `std::result::Result` in this module.
//!
//! The functions that return `((env, ty_err_opt, cycles), x)` in OCaml
//! return `(ty_err_opt, cycles, x)`.
//!
//! The last line of `typing_taccess.ml`, `Typing_utils.expand_typeconst_ref
//! := expand_with_env`, has no counterpart: OCaml breaks the dependency cycle
//! between the two modules with a reference, and `crate::typing_utils` calls
//! [`expand_with_env`] directly.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Id;
use oxidized::pos::Pos;
use pos::ToOxidized;
use pos::TypeName;
use ty::decl::ty as d;

use crate::ast_defs;
use crate::class_refinement;
use crate::decl_entry;
use crate::expression_id;
use crate::folded_class;
use crate::pos_or_decl;
use crate::type_expansions;
use crate::type_expansions::CycleReporter;
use crate::typing_defs;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::dependent_kind;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DependentType;
use crate::typing_defs_core::Exact;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::RefinedConst;
use crate::typing_defs_core::RefinedConstBound;
use crate::typing_defs_core::RefinedConstBounds;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::TransformTopDown;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::equal_locl_ty;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::map_reason;
use crate::typing_defs_core::map_ty;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::nonexact;
use crate::typing_defs_core::transform_top_down_decl_ty;
use crate::typing_dynamic_utils;
use crate::typing_env as env_;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::ReadOrWrite;
use crate::typing_error::primary::NonObjectMemberKind;
use crate::typing_error::primary::SmemberNotFoundKind;
use crate::typing_error::secondary;
use crate::typing_log as log;
use crate::typing_make_type as make_type;
use crate::typing_phase as phase;
use crate::typing_print;
use crate::typing_reason as reason;
use crate::typing_reason::LazyString;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;
use crate::typing_set as ty_set;
use crate::typing_subtype_tconst;
use crate::typing_utils;

// A guiding principle when expanding a type access C::T is that if C <: D and
// we know that D::T = X (represented by an Exact result below), then C::T is
// also X. So Exact is propagated down the <: relation, see `update_class_name`
// below where this behavior is encoded.

/// When the access code is going to return a `Tgeneric "Foo::Bar"`,
/// we use the following type to tell the difference between legit
/// accesses from known concrete types (`this`, or expression-
/// dependent types), and unsound accesses from arbitrary generic
/// variables.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RootKind {
    ConcreteClass,
    GenericType,
}

#[derive(Clone)]
struct Context {
    /// The T in the type access C::T
    id: PosId,
    /// The expand environment as passed in by Phase.localize
    ety_env: ExpandEnv,
    /// The set of visited generics used to avoid infinite loops during expansion.
    /// These are all some `Tgeneric (name, tyargs)`.
    generics_seen: ty_set::T,
    /// Whether or not an abstract type constant is allowed as the result. In the
    /// future, this boolean should disappear and abstract type constants should
    /// appear only in the class where they are defined.
    allow_abstract: bool,
    /// If set, abstract type constants will be expanded as type variables. This
    /// is a hack which should naturally go away when the semantics of abstract
    /// type constants is cleaned up.
    abstract_as_tyvar_at_pos: Option<Pos>,
    /// The origin of the extension. For example if TC is a generic parameter
    /// subject to the constraint TC as C and we would like to expand TC::T we
    /// will expand C::T with base set to `Some (Tgeneric "TC")` (and root set
    /// to C). If it is None the base is exactly the current root.
    base: Option<Ty>,
    /// See documentation for the [root_kind] type.
    root_kind: RootKind,
}

/// The result of an expansion
/// - Missing err means that the type constant is not present, with error function
///   to be called if we need to report this
/// - Exact ty means that the expansion results precisely in 'ty'
/// - Abstract (n0, [n1, n2, n3], lower_bound, upper_bound) means that the result is a
///   generic with name n0::T such that:
///   n0::T as n1::T as n2::T as n3::T as upper_bound super lower_bound
#[derive(Clone, Debug)]
enum Result {
    Missing(Option<typing_error::T>),
    Exact(Ty),
    Abstract(Abstract),
}

#[derive(Clone, Debug)]
struct Abstract {
    name: String,
    names: Vec<String>,
    lower_bounds: ty_set::T,
    upper_bounds: ty_set::T,
}

/// What the functions that return `((env, ty_err_opt, cycles), x)` in OCaml
/// return.
type ErrCycles<X> = (Option<typing_error::T>, Vec<CycleReporter>, X);

/// `Option.merge e1 e2 ~f`
fn option_merge<A>(e1: Option<A>, e2: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (e1, e2) {
        (Some(e1), Some(e2)) => Some(f(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    }
}

/// `lazy (Typing_print.error env ty)`, for a typing error.
fn lazy_print_error(env: &Env, ty: &Ty) -> Lazy<String> {
    let env = env.clone();
    let ty = ty.clone();
    Lazy::new(move || typing_print::error(None, &env, &ty))
}

fn make_reason(env: &Env, id: &PosId, root: &Ty, r: Reason) -> Reason {
    // `lazy (Typing_print.error env root)`: the lazy string of a reason
    // (`Typing_reason.LazyString`) must be `Send + Sync`, which the
    // environment and the type are not, so the type is printed now. Printing
    // has no effect (it only reads the environment), and the environment is
    // the one OCaml would have printed with.
    reason::typeconst((
        r,
        id.clone(),
        LazyString::from_val(typing_print::error(None, env, root)),
        get_reason(root).clone(),
    ))
}

// FIXME: It is bogus to use strings here and put them in Tgeneric; one
// possible problem is when a type parameter has a name which conflicts
// with a class name
fn tp_name(class_name: &str, id: &PosId) -> String {
    format!("{}::{}", class_name, id.1)
}

/// A smart constructor for Abstract that also checks if the type we are
/// creating is known to be equal to some other type
fn abstract_or_exact(env: &Env, id: &PosId, abstr: Abstract) -> Result {
    let tp_name = tp_name(&abstr.name, id);
    if !ty_set::is_empty(&env_::get_equal_bounds(env, &tp_name)) {
        // If the resulting abstract type is exactly equal to something,
        // mark the result as exact.
        // For example, if we have the following
        // abstract class Box {
        //   abstract const type T;
        // }
        // function addFiveToValue<T1 as Box>(T1 $x) : int where T1::T = int {
        //     return $x->get() + 5;
        // }
        // Here, $x->get() has type expr#1::T as T1::T (as Box::T).
        // But T1::T is exactly equal to int, so $x->get() no longer needs
        // to be expression dependent. Thus, $x->get() typechecks.
        Result::Exact(make_type::generic(reason::none(), tp_name))
    } else {
        Result::Abstract(abstr)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RecursiveAccessScope {
    Everywhere,
    OnlyInRefinement,
}

#[derive(Clone, Debug)]
struct RecursiveAccessInfo {
    this_name: String,
    scope: RecursiveAccessScope,
}

/// Recursive class refinements (the "fluent builder" pattern) introduce
/// self-referential bounds on abstract type constants:
///
/// ```text
///   interface I {
///     abstract const type T as I with { type T = this::T; };
///     public function next(): this::T;
///   }
/// ```
///
/// When we expand T from I, the upper bound contains `this::T`. Naively
/// localizing that bound would expand T from I again, producing a cycle.
/// This function breaks the cycle by replacing `this::T` in the decl-phase
/// bound with a mangled Tgeneric whose name matches the generic that
/// [type_of_result] will create for this access, establishing a fixpoint.
///
/// We need to determine a [this_name] prefix so that the replacement
/// generic `this_name::T` matches what [type_of_result] / [tp_name]
/// produces. There are three cases, distinguished by what [this_ty] is
/// when we reach this function:
///
/// ```text
///   Example            | Receiver type        | make_with_dep_kind    | this_ty                      | this_name
///   -------------------|----------------------|-----------------------|------------------------------|---------------------
///   I $i; $i->next()   | Tclass(I, nonexact)  | wraps in Tdependent   | Tdependent(DTexpr e1, ...)   | Expression_id e1
///   this::TB $b;       | Tgeneric("C::TB")    | no-op (has "::")      | Tgeneric("C::TB")            | "C::TB"
///     $b->next()       |                      |                       |                              |
///   $this->builder()   | Tgeneric("this")     | no-op                 | Tgeneric("this")             | "this"
/// ```
///
/// Case 1 — [this_ty] is [Tdependent (DTexpr expr_id, _)]:
///   The receiver is a concrete class type. [ExprDepTy.make_with_dep_kind]
///   wraps it in [Tdependent], and the [Tdependent] case in [expand] uses
///   [DependentKind.to_string] (= [Expression_id.display]) as the
///   outermost name in the abstract result chain. So we use
///   [Expression_id.display expr_id] as [this_name].
///
/// Case 2 — [this_ty] is [Tgeneric s] where [s] is an expression-dependent
/// generic (its name contains "::"):
///   The receiver is itself the result of a type constant access (e.g.
///   [this::TBuilder] localizes to [Tgeneric("C::TBuilder")]). When
///   [$b->next()] is called, [ExprDepTy.make_with_dep_kind] sees that the
///   receiver type is a generic whose name already contains "::" and
///   returns it without [Tdependent] wrapping (see
///   [typing_dependent_type.ml], the [is_generic_dep_ty] guard). The
///   [Tgeneric] case in [expand] uses the generic name directly via
///   [update_class_name], so [type_of_result] / [tp_name] will produce
///   ["C::TBuilder::T"]. We therefore use the generic name [s] as
///   [this_name].
///
/// Case 3 — [this_ty] is the bare generic [this]:
///   We only perform the replacement inside a class-refinement bound. Direct
///   self-referential bounds still need to produce a cycle so [to_tys] can
///   restore their implicit SDT bound.
///
/// In all cases the replacement generic name is [this_name :: T], which
/// is exactly the name that [type_of_result] will register in the typing
/// environment with the refined upper bound, establishing the fixpoint.
fn eliminate_recursive_access(ty: DeclTy, type_const_name: &str, this_ty: &Ty) -> DeclTy {
    let this_info_opt = match get_node(this_ty) {
        Ty_::Tdependent(DependentType::DTexpr(expr_id), _) => Some(RecursiveAccessInfo {
            this_name: expression_id::display(*expr_id),
            scope: RecursiveAccessScope::Everywhere,
        }),
        Ty_::Tgeneric(s) if s == sn::typehints::THIS => Some(RecursiveAccessInfo {
            this_name: s.clone(),
            scope: RecursiveAccessScope::OnlyInRefinement,
        }),
        Ty_::Tgeneric(s) if dependent_kind::is_generic_dep_ty(s) => Some(RecursiveAccessInfo {
            this_name: s.clone(),
            scope: RecursiveAccessScope::Everywhere,
        }),
        _ => None,
    };
    // `Option.value_map this_info_opt ~default:ty ~f:(...)`
    match this_info_opt {
        None => ty,
        Some(RecursiveAccessInfo { this_name, scope }) => {
            let on_ty =
                |ty: DeclTy, nested_in_refinement: &bool| -> (bool, TransformTopDown<DeclTy>) {
                    let nested_in_refinement = *nested_in_refinement;
                    let in_scope = match scope {
                        RecursiveAccessScope::Everywhere => true,
                        RecursiveAccessScope::OnlyInRefinement => nested_in_refinement,
                    };
                    match ty.node_ref() {
                        d::Ty_::Taccess(ta)
                            if ta.type_const.id_ref().as_str() == type_const_name && in_scope =>
                        {
                            match ta.ty.node_ref() {
                                d::Ty_::Tthis => {
                                    let ty = DeclTy::new(
                                        ty.reason().clone(),
                                        d::Ty_::Tgeneric(TypeName::new(format!(
                                            "{}::{}",
                                            this_name, type_const_name
                                        ))),
                                    );
                                    (nested_in_refinement, TransformTopDown::Stop(ty))
                                }
                                _ => (nested_in_refinement, TransformTopDown::Continue(ty)),
                            }
                        }
                        _ => (nested_in_refinement, TransformTopDown::Continue(ty)),
                    }
                };
            let on_rc_bound = |rc_bound, _ctx: &bool| (true, TransformTopDown::Continue(rc_bound));
            transform_top_down_decl_ty(ty, &on_ty, &on_rc_bound, &false)
        }
    }
}

/// [create_root_from_type_constant ctx env root class_name class_]
/// looks up a type constant in a class and returns a `result`. More precisely, it looks up
/// [ctx.id] in [class_]. [class_name] is the class name for [class_] and [root]
/// is a `Tclass (class_name, ...)`.
///
/// A type constant has both a constraint type and assigned type. Which one we choose depends if
/// the current root is the base (origin) of the expansion (in which case [ctx.base] is `None`),
/// or if it is an upper bound of the base (in which case [ctx.base] is `Some`).
fn create_root_from_type_constant(
    ctx: &Context,
    env: &mut Env,
    root: &Ty,
    (_class_pos, class_name): &PosId,
    class_: &folded_class::T,
) -> (Option<typing_error::T>, Vec<CycleReporter>, Result) {
    let id = &ctx.id;
    let (id_pos, type_const_name) = id;
    match env_::get_typeconst(env, class_, type_const_name) {
        None => (
            None,
            vec![],
            Result::Missing(ctx.ety_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Smember_not_found {
                        pos: id_pos.clone(),
                        kind: SmemberNotFoundKind::class_typeconst,
                        class_name: class_name.clone(),
                        class_pos: folded_class::pos(class_),
                        member_name: type_const_name.clone(),
                        hint: None,
                    },
                    on_error,
                )
            })),
        ),
        Some(typeconst) => {
            match typing_defs::add_type_expansion_check_cycles(
                &ctx.ety_env,
                type_expansions::Expansion {
                    name: type_expansions::expandable::T::TypeConstant {
                        receiver_name: class_name.clone(),
                        type_const_name: type_const_name.clone(),
                    },
                    use_pos: id_pos.clone(),
                    def_pos: None,
                },
            ) {
                Err(cycle) => {
                    // This is a cycle through a type constant that we are using
                    (None, vec![cycle], Result::Missing(None))
                }
                Ok(ety_env) => {
                    let ctx = Context {
                        ety_env,
                        ..ctx.clone()
                    };
                    let ety_env = {
                        let drop_exact = |ty: Ty| {
                            // Legacy behavior is to preserve exactness only on `this` and not
                            // through `this::T`
                            map_ty(ty, |ty_| match ty_ {
                                Ty_::Tclass(cid, _, tyl) => Ty_::Tclass(cid, nonexact(), tyl),
                                ty_ => ty_,
                            })
                        };
                        ExpandEnv {
                            this_ty: drop_exact(ctx.base.clone().unwrap_or_else(|| root.clone())),
                            ..ctx.ety_env.clone()
                        }
                    };
                    let abstract_or_exact =
                        |env: &Env, lower_bounds: ty_set::T, upper_bounds: ty_set::T| {
                            let ty_err_opt = if !ctx.allow_abstract {
                                ctx.ety_env.on_error.clone().map(|on_error| {
                                    typing_error::apply_reasons(
                                        secondary::T::Abstract_tconst_not_allowed {
                                            pos: id_pos.clone(),
                                            decl_pos: typeconst.name.pos().clone().to_oxidized(),
                                            tconst_name: type_const_name.clone(),
                                        },
                                        on_error,
                                    )
                                })
                            } else {
                                None
                            };
                            // TODO(T59448452): this treatment of abstract type constants is unsound
                            (
                                abstract_or_exact(
                                    env,
                                    id,
                                    Abstract {
                                        name: class_name.clone(),
                                        names: vec![],
                                        lower_bounds,
                                        upper_bounds,
                                    },
                                ),
                                ty_err_opt,
                            )
                        };
                    // Don't report errors in expanded definition or constraint.
                    // These will have been reported at the definition site already.
                    let ety_env = ExpandEnv {
                        on_error: None,
                        ..ety_env
                    };
                    match &typeconst.kind {
                        // Concrete type constants
                        d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty }) => {
                            let (ty_err_opt, cycles, ty): ErrCycles<Ty> =
                                phase::localize_rec(&ety_env, env, ty);
                            let ty = map_reason(ty, |r| make_reason(env, id, root, r));
                            (ty_err_opt, cycles, Result::Exact(ty))
                        }
                        // Abstract type constants
                        d::Typeconst::TCAbstract(d::AbstractTypeconst {
                            as_constraint: upper,
                            super_constraint: lower,
                            ..
                        }) => {
                            let upper = upper.clone().map(|ty| {
                                eliminate_recursive_access(
                                    ty,
                                    type_const_name,
                                    &ctx.ety_env.this_ty,
                                )
                            });
                            let lower = lower.clone().map(|ty| {
                                eliminate_recursive_access(
                                    ty,
                                    type_const_name,
                                    &ctx.ety_env.this_ty,
                                )
                            });
                            let to_tys = |env: &mut Env,
                                          ty: &Option<DeclTy>|
                             -> (
                                Option<typing_error::T>,
                                Vec<CycleReporter>,
                                ty_set::T,
                            ) {
                                match ty {
                                    Some(ty) => {
                                        let (err, cycles, ty): ErrCycles<Ty> =
                                            phase::localize_rec(&ety_env, env, ty);
                                        // When a cycle is detected (e.g. `abstract const type T as this::T`),
                                        // the localized type is Tany which is unsound. Drop the bound instead,
                                        // effectively treating the constraint as absent; this function is
                                        // used for both upper and lower bound but the interpretation of
                                        // the empty set is correct:
                                        // - upper bound = /\ {} = mixed
                                        // - lower bound = \/ {} = nothing
                                        let bounds =
                                            if !cycles.is_empty() && typing_defs::is_any(&ty) {
                                                ty_set::empty()
                                            } else {
                                                ty_set::singleton(ty)
                                            };
                                        (err, cycles, bounds)
                                    }
                                    None => (None, vec![], ty_set::empty()),
                                }
                            };
                            let (e1, cycles_lower, lower_bounds) = to_tys(env, &lower);
                            let (e2, cycles_upper, upper_bounds) = to_tys(env, &upper);
                            // Under everything_sdt, abstract type constants without an
                            // explicit bound get supportdyn<mixed> as their upper bound
                            // (see maybe_add_supportdyn_bound in decl_folded_class.ml).
                            // When the only upper bound is self-referential and gets dropped
                            // by cycle detection above, we must add back supportdyn<mixed>
                            // so that the type constant remains compatible with SDT
                            // requirements.
                            let upper_bounds = if ty_set::is_empty(&upper_bounds)
                                && upper.is_some()
                                // `Typechecker_options.everything_sdt`
                                && env_::get_tcopt(env).po.everything_sdt
                            {
                                ty_set::singleton(make_type::supportdyn_mixed(reason::none()))
                            } else {
                                upper_bounds
                            };
                            let (res, e3) = abstract_or_exact(env, lower_bounds, upper_bounds);
                            let ty_err_opt = typing_error::multiple_opt(
                                [e1, e2, e3].into_iter().flatten().collect(),
                            );
                            let mut cycles = cycles_lower;
                            cycles.extend(cycles_upper);
                            (ty_err_opt, cycles, res)
                        }
                    }
                }
            }
        }
    }
}

/// Cheap intersection operation. Do not call Typing_intersection.intersect
/// as this calls into subtype which in turn calls into expand_with_env below
fn intersect(ty1: Ty, ty2: Ty) -> Ty {
    if equal_locl_ty(&ty1, &ty2) {
        ty1
    } else {
        let r = get_reason(&ty1).clone();
        make_type::intersection(r, vec![ty1, ty2])
    }
}

/// Cheap union operation. Do not call Typing_union.union
/// as this calls into subtype which in turn calls into expand_with_env below
fn union(ty1: Ty, ty2: Ty) -> Ty {
    if equal_locl_ty(&ty1, &ty2) {
        ty1
    } else {
        let r = get_reason(&ty1).clone();
        make_type::union(r, vec![ty1, ty2])
    }
}

/// Given the results of projecting a type constant from types t1 , ... , tn,
/// determine the result of projecting a type constant from type (t1 | ... | tn).
/// If the type constant is missing from any of the disjuncts, then it's treated
/// as missing from the union.
fn union_results(err: Option<typing_error::T>, rl: Vec<Result>) -> Result {
    let mut rl = rl;
    match rl.len() {
        0 => Result::Missing(err),
        1 => rl.pop().unwrap(),
        _ => {
            let rl_ = rl.split_off(1);
            let r1 = rl.pop().unwrap();
            let r2 = union_results(err.clone(), rl_);

            // Union is defined iff both are defined concretely
            match (r1, r2) {
                (Result::Missing(err), _) | (_, Result::Missing(err)) => Result::Missing(err),
                // In essence, this says (C | D)::TP = (C::TP) | (D::TP)
                (Result::Exact(ty1), Result::Exact(ty2)) => Result::Exact(union(ty1, ty2)),
                // We don't support projecting through any other kind of union
                _ => Result::Missing(err),
            }
        }
    }
}

/// Given the results of projecting a type constant from types t1, ..., tn,
/// determine the result of projecting a type constant from type (t1 & ... & tn).
fn intersect_results(err: Option<typing_error::T>, rl: Vec<Result>) -> Result {
    let mut rl = rl;
    match rl.len() {
        // Essentially, this is `mixed`.
        0 => Result::Missing(err),
        1 => rl.pop().unwrap(),
        _ => {
            let rs = rl.split_off(1);
            let r1 = rl.pop().unwrap();
            let r2 = intersect_results(err, rs);
            match (r1, r2) {
                (Result::Missing(_), r) | (r, Result::Missing(_)) => r,
                // In essence, we're saying (C & D)::TP = (C::TP) & (D::TP)
                (Result::Exact(ty1), Result::Exact(ty2)) => Result::Exact(intersect(ty1, ty2)),
                // Here, we merge the bounds on abstract type constants. Effectively this is intersection.
                (
                    Result::Abstract(Abstract {
                        name,
                        names,
                        lower_bounds: lowerl1,
                        upper_bounds: upperl1,
                    }),
                    Result::Abstract(Abstract {
                        lower_bounds: lowerl2,
                        upper_bounds: upperl2,
                        ..
                    }),
                ) => Result::Abstract(Abstract {
                    name,
                    names,
                    lower_bounds: ty_set::union(&lowerl1, &lowerl2),
                    upper_bounds: ty_set::union(&upperl1, &upperl2),
                }),
                // Exact type overrides abstract type: the bound on abstract type will be checked
                // against the exact type at implementation site.
                (Result::Abstract(_), Result::Exact(ty))
                | (Result::Exact(ty), Result::Abstract(_)) => Result::Exact(ty),
            }
        }
    }
}

fn type_of_result(
    ignore_errors: bool,
    ctx: &Context,
    env: &mut Env,
    root: &Ty,
    res: Result,
) -> (Option<typing_error::T>, Ty) {
    fn type_with_bound(
        ctx: &Context,
        root: &Ty,
        env: &mut Env,
        as_tyvar: Option<Pos>,
        name: &str,
        lower_bounds: &ty_set::T,
        upper_bounds: &ty_set::T,
    ) -> Ty {
        match as_tyvar {
            Some(tyvar_pos) => {
                let tvar = env_::fresh_type_invariant(env, tyvar_pos.clone());
                log::log_new_tvar_for_tconst_access(env, &tyvar_pos, &tvar, name, &ctx.id);
                tvar
            }
            None => {
                let generic_name = tp_name(name, &ctx.id);
                let reason = make_reason(env, &ctx.id, root, reason::none());
                let ty = make_type::generic(reason, generic_name.clone());
                for bnd in upper_bounds.iter() {
                    // TODO(T59317869): play well with flow sensitivity
                    env_::add_upper_bound_global(env, &generic_name, bnd.clone())
                }
                for bnd in lower_bounds.iter() {
                    // TODO(T59317869): play well with flow sensitivity
                    env_::add_lower_bound_global(env, &generic_name, bnd.clone())
                }
                ty
            }
        }
    }
    match res {
        Result::Exact(ty) => (None, ty),
        Result::Abstract(Abstract {
            name,
            names,
            lower_bounds,
            upper_bounds,
        }) if !names.is_empty() => {
            let mut namel = names;
            let name_ = namel.remove(0);
            let res_ = Result::Abstract(Abstract {
                name: name_,
                names: namel,
                lower_bounds: lower_bounds.clone(),
                upper_bounds,
            });
            let (ty_err_opt, ty) = type_of_result(ignore_errors, ctx, env, root, res_);
            let ty = type_with_bound(
                ctx,
                root,
                env,
                None,
                &name,
                &lower_bounds,
                &ty_set::singleton(ty),
            );
            (ty_err_opt, ty)
        }
        Result::Abstract(Abstract {
            name,
            names: _,
            lower_bounds,
            upper_bounds,
        }) => {
            let ty = type_with_bound(
                ctx,
                root,
                env,
                ctx.abstract_as_tyvar_at_pos.clone(),
                &name,
                &lower_bounds,
                &upper_bounds,
            );
            (None, ty)
        }
        Result::Missing(err) => {
            let ty_err_opt = if !ignore_errors { err } else { None };
            // TODO akenn: this is a source of unsoundness
            let ty: Ty = typing_utils::mk_tany(env, pos_or_decl::unsafe_to_raw_pos(get_pos(root)));
            (ty_err_opt, ty)
        }
    }
}

fn update_class_name(env: &Env, id: &PosId, new_name: String, res: Result) -> Result {
    match res {
        res @ (Result::Exact(_) | Result::Missing(_)) => res,
        Result::Abstract(Abstract {
            name,
            names,
            lower_bounds,
            upper_bounds,
        }) => {
            let mut names_ = vec![name];
            names_.extend(names);
            abstract_or_exact(
                env,
                id,
                Abstract {
                    name: new_name,
                    names: names_,
                    lower_bounds,
                    upper_bounds,
                },
            )
        }
    }
}

fn is_opaque_internal(ty: &Ty) -> bool {
    reason::predicates::is_opaque_type_from_module(get_reason(ty))
}

fn expand(
    ctx: &Context,
    env: &mut Env,
    root: Ty,
) -> (Option<typing_error::T>, Vec<CycleReporter>, Result) {
    let root = env_::expand_type(env, root);
    let err_opt = {
        let (pos, tconst) = &ctx.id;
        // The secondary error is built only when there is a callback to
        // apply it to; building it has no effect (its type name is lazy).
        ctx.ety_env.on_error.clone().map(|on_error| {
            let ty_name = lazy_print_error(env, &root);
            let reason = secondary::T::Non_object_member {
                pos: pos.clone(),
                ctxt: ReadOrWrite::read,
                kind: NonObjectMemberKind::class_typeconst,
                member_name: tconst.clone(),
                ty_name,
                decl_pos: get_pos(&root),
            };
            typing_error::apply_reasons(reason, on_error)
        })
    };
    // `fun env root -> let ety_env = { ctx.ety_env with this_ty = root } in
    // let ctx = { ctx with ety_env } in expand ctx env root`
    let expand_with_this_ty = |env: &mut Env, root: &Ty| {
        let ety_env = ExpandEnv {
            this_ty: root.clone(),
            ..ctx.ety_env.clone()
        };
        let ctx = Context {
            ety_env,
            ..ctx.clone()
        };
        expand(&ctx, env, root.clone())
    };
    if typing_utils::is_tyvar_error(env, &root) {
        (None, vec![], Result::Missing(None))
    } else {
        match get_node(&root) {
            Ty_::Tany(_) => (None, vec![], Result::Exact(root.clone())),
            // We allow inheritance of members from internal classes and traits into public ones,
            // even if their signatures include internal types, but when localizing such internal
            // types we pretend that a Tclass is a Tnewtype i.e. is opaque.
            // Here we deal with projection from a newtype that was generated in such cases e.g.
            //     internal class Base { const type TC = int; public static function foo(self::TC $_):void { } }
            //     class Derived extends Base { }
            //     function bar():void { Derived::foo("A"); }
            //  Generate another fake newtype by mangling the name using the projection syntax.
            Ty_::Tnewtype(name, _tyl, bound) if is_opaque_internal(&root) => (
                None,
                vec![],
                Result::Exact(mk((
                    get_reason(&root).clone(),
                    Ty_::Tnewtype(format!("{}::{}", name, ctx.id.1), vec![], bound.clone()),
                ))),
            ),
            Ty_::Tnewtype(name, _, ty) => {
                let ctx = {
                    let base = Some(ctx.base.clone().unwrap_or_else(|| root.clone()));
                    let allow_abstract = true;
                    Context {
                        base,
                        allow_abstract,
                        ..ctx.clone()
                    }
                };
                let (ty_err_opt, cycles, res) = expand(&ctx, env, ty.clone());
                let name = format!("<cls#{}>", name);
                (
                    ty_err_opt,
                    cycles,
                    update_class_name(env, &ctx.id, name, res),
                )
            }
            Ty_::Tclass(cid, Exact::Nonexact(cr), targs)
                if class_refinement::has_refined_const(&ctx.id, cr) =>
            {
                let refined_const: Option<RefinedConst> =
                    class_refinement::get_refined_const(&ctx.id, cr);
                match refined_const {
                    Some(RefinedConst {
                        bound: RefinedConstBound::TRexact(ty),
                        ..
                    }) => (None, vec![], Result::Exact(ty)),
                    Some(RefinedConst {
                        bound:
                            RefinedConstBound::TRloose(RefinedConstBounds {
                                lower: tr_lower,
                                upper: tr_upper,
                            }),
                        ..
                    }) => {
                        let alt_root = mk((
                            get_reason(&root).clone(),
                            Ty_::Tclass(cid.clone(), nonexact(), targs.clone()),
                        ));
                        let (ty_err_opt, cycles_alt_root, result) = expand(ctx, env, alt_root);
                        match result {
                            Result::Exact(_) | Result::Missing(_) => {
                                (ty_err_opt, cycles_alt_root, result)
                            }
                            Result::Abstract(abstr) => {
                                // Flag an error if the root is not a concrete class type.
                                let ty_err_opt_ = match ctx.root_kind {
                                    RootKind::ConcreteClass => None,
                                    RootKind::GenericType => {
                                        let pos = reason::to_pos(get_reason(&root));
                                        ctx.ety_env.on_error.clone().map(|on_error| {
                                            typing_error::apply_reasons(
                                                secondary::T::Inexact_tconst_access(
                                                    pos,
                                                    ctx.id.clone(),
                                                ),
                                                on_error,
                                            )
                                        })
                                    }
                                };
                                // `Option.first_some ty_err_opt' ty_err_opt`
                                let ty_err_opt = ty_err_opt_.or(ty_err_opt);
                                let add_bounds = |tyset: ty_set::T, bnds: Vec<Ty>| {
                                    bnds.into_iter()
                                        .fold(tyset, |tyset, t| ty_set::add(t, &tyset))
                                };
                                let abstr = Abstract {
                                    lower_bounds: add_bounds(abstr.lower_bounds, tr_lower),
                                    upper_bounds: add_bounds(abstr.upper_bounds, tr_upper),
                                    ..abstr
                                };
                                (ty_err_opt, cycles_alt_root, Result::Abstract(abstr))
                            }
                        }
                    }
                    None => {
                        // unreachable
                        (None, vec![], Result::Missing(None))
                    }
                }
            }
            Ty_::Tclass(cls, _, _) => decl_entry::map_or(
                env_::get_class(env, &cls.1),
                |ci| {
                    // Hack: `self` in a trait is mistakenly replaced by the trait instead
                    // of the class using the trait, so if a trait is the root, it is
                    // likely because originally there was `self::T` written.
                    // TODO(T54081153): fix `self` in traits and clean this up
                    let allow_abstract =
                        ast_defs::is_c_trait(folded_class::kind(&ci)) || ctx.allow_abstract;
                    let ctx = Context {
                        allow_abstract,
                        ..ctx.clone()
                    };
                    create_root_from_type_constant(&ctx, env, &root, cls, &ci)
                },
                (None, vec![], Result::Missing(None)),
            ),
            Ty_::Tgeneric(s) => {
                let ctx = Context {
                    generics_seen: ty_set::add(root.clone(), &ctx.generics_seen),
                    base: Some(ctx.base.clone().unwrap_or_else(|| root.clone())),
                    allow_abstract: true,
                    abstract_as_tyvar_at_pos: None,
                    root_kind: {
                        let this_name = sn::special_idents::THIS;
                        // The `this` type stands for a concrete class.
                        if s == this_name {
                            RootKind::ConcreteClass
                        } else {
                            ctx.root_kind
                        }
                    },
                    ..ctx.clone()
                };
                // `Typing_utils.strip_supportdyn` and
                // `Typing_dynamic_utils.strip_dynamic` return an environment
                // that OCaml drops: they work on copies.
                let is_supportdyn_mixed = |t: &Ty| {
                    let (is_supportdyn, t): (bool, Ty) =
                        typing_utils::strip_supportdyn(&mut env.clone(), t.clone());
                    is_supportdyn && typing_utils::is_mixed(env, &t)
                };
                // Ignore seen bounds to avoid infinite loops
                let upper_bounds = {
                    let ub = env_::get_upper_bounds(env, s);
                    ty_set::elements(&ty_set::filter(
                        |ty: &Ty| {
                            !is_supportdyn_mixed(ty)
                                // Also ignore ~T if we've seen T
                                && !ty_set::mem(
                                    &typing_dynamic_utils::strip_dynamic(
                                        &mut env.clone(),
                                        ty.clone(),
                                    ),
                                    &ctx.generics_seen,
                                )
                        },
                        &ub,
                    ))
                };
                // TODO: should we be taking the intersection of the errors?
                let (ty_err_opt, cycles_upper_bounds, resl): ErrCycles<Vec<Result>> =
                    phase::list_map_env_err_cycles(
                        env,
                        &upper_bounds,
                        typing_error::multiple_opt,
                        |env: &mut Env, ty: &Ty| expand(&ctx, env, ty.clone()),
                    );
                let res = intersect_results(err_opt, resl);
                (
                    ty_err_opt,
                    cycles_upper_bounds,
                    update_class_name(env, &ctx.id, s.clone(), res),
                )
            }
            Ty_::Tdependent(dep_ty, ty) => {
                let ctx = {
                    let root_kind = RootKind::ConcreteClass;
                    let base = Some(ctx.base.clone().unwrap_or_else(|| root.clone()));
                    let allow_abstract = true;
                    let abstract_as_tyvar_at_pos = None;
                    Context {
                        base,
                        allow_abstract,
                        abstract_as_tyvar_at_pos,
                        root_kind,
                        ..ctx.clone()
                    }
                };
                let (ty_err_opt, cycles, res) = expand(&ctx, env, ty.clone());
                (
                    ty_err_opt,
                    cycles,
                    update_class_name(env, &ctx.id, dependent_kind::to_string(dep_ty), res),
                )
            }
            Ty_::Tintersection(tyl) => {
                // Terrible hack (compatible with previous behaviour) that first attempts to project off the
                // non-type-variable conjuncts. If this doesn't succeed, then try the type variable
                // conjuncts, which will cause type-const constraints to be added to the type variables.
                let (tyl_vars, tyl_nonvars): (Vec<Ty>, Vec<Ty>) =
                    tyl.iter().cloned().partition(|t| {
                        // `let (_env, t) = Env.expand_type env t`: only a
                        // type variable is expanded, in a copy of the
                        // environment.
                        let t = match get_node(t) {
                            Ty_::Tvar(_) => env_::expand_type(&mut env.clone(), t.clone()),
                            _ => t.clone(),
                        };
                        typing_defs::is_tyvar(&t)
                    });
                // TODO: should we be taking the intersection of the errors?
                let (e1, cycles_tyl_nonvars, resl): ErrCycles<Vec<Result>> =
                    phase::list_map_env_err_cycles(
                        env,
                        &tyl_nonvars,
                        typing_error::multiple_opt,
                        &expand_with_this_ty,
                    );
                let result = intersect_results(err_opt.clone(), resl);
                let (e2, cycles_tyl_vars, res) = match result {
                    Result::Missing(_) => {
                        // TODO: should we be taking the intersection of the errors?
                        let (e2, cycles_tyl_vars, resl): ErrCycles<Vec<Result>> =
                            phase::list_map_env_err_cycles(
                                env,
                                &tyl_vars,
                                typing_error::multiple_opt,
                                &expand_with_this_ty,
                            );
                        // TODO: should we be taking the intersection of the errors?
                        (e2, cycles_tyl_vars, intersect_results(err_opt, resl))
                    }
                    _ => (None, vec![], result),
                };
                let ty_err_opt =
                    option_merge(e1, e2, |e1, e2| typing_error::multiple(vec![e1, e2]));
                let mut cycles = cycles_tyl_vars;
                cycles.extend(cycles_tyl_nonvars);
                (ty_err_opt, cycles, res)
            }
            Ty_::Tunion(tyl) => {
                let (ty_err_opt, cycles, resl): ErrCycles<Vec<Result>> =
                    phase::list_map_env_err_cycles(
                        env,
                        tyl,
                        typing_error::union_opt,
                        &expand_with_this_ty,
                    );
                let result = union_results(err_opt, resl);
                (ty_err_opt, cycles, result)
            }
            Ty_::Tvar(n) => {
                let (err, cycles, ty): ErrCycles<Ty> = typing_subtype_tconst::get_tyvar_type_const(
                    env,
                    *n,
                    &ctx.id,
                    ctx.ety_env.on_error.clone(),
                );
                (err, cycles, Result::Exact(ty))
            }
            Ty_::Taccess(_)
            | Ty_::Tnonnull
            | Ty_::Tprim(_)
            | Ty_::Tshape(ShapeType::ShapeSimple(_) | ShapeType::ShapeSplat(_))
            | Ty_::Ttuple(_)
            | Ty_::TvecOrDict(_, _)
            | Ty_::Tfun(_)
            | Ty_::Tdynamic(_)
            | Ty_::Toption(_)
            | Ty_::Tlabel(_)
            | Ty_::Tneg(_)
            | Ty_::TclassPtr(_) => (None, vec![], Result::Missing(err_opt)),
        }
    }
}

/// Expands a type constant access like A::T to its definition.
pub fn expand_with_env(
    ety_env: &ExpandEnv,
    env: &mut Env,
    ignore_errors: Option<bool>,
    as_tyvar_with_cnstr: Option<Option<Pos>>,
    root: Ty,
    id: PosId,
    allow_abstract_tconst: bool,
) -> (Option<typing_error::T>, Vec<CycleReporter>, Ty) {
    let ignore_errors = ignore_errors.unwrap_or(false);
    let as_tyvar_with_cnstr = as_tyvar_with_cnstr.unwrap_or(None);
    let (ty_err_opt, cycles, ty) = {
        let ctx = Context {
            id: id.clone(),
            ety_env: ety_env.clone(),
            base: None,
            generics_seen: ty_set::empty(),
            allow_abstract: allow_abstract_tconst,
            abstract_as_tyvar_at_pos: as_tyvar_with_cnstr,
            // Worst-case assumption; may be refined during [expand].
            root_kind: RootKind::GenericType,
        };
        let (e1, cycles, res) = expand(&ctx, env, root.clone());
        let (e2, ty) = type_of_result(ignore_errors, &ctx, env, &root, res);
        let ty_err_opt = option_merge(e1, e2, typing_error::both);
        (ty_err_opt, cycles, ty)
    };
    let ty: Ty = log::log_type_access(1, &root, &id, (env, ty));
    (ty_err_opt, cycles, ty)
}

/// Returns (class_name, tconst_name, tconst_reference_position) for each type
/// constant referenced in a type access.
///
/// This is called with non-nested type accesses e.g. this::T1::T2 is
/// represented by (this, [T1; T2])
///
/// OCaml drops the environment that it threads through the accesses: this
/// works on a copy of `env`.
pub fn referenced_typeconsts(
    env: &Env,
    ety_env: &ExpandEnv,
    (root, ids): (&DeclTy, &[aast::Sid]),
) -> (Vec<(String, String, Pos)>, Option<typing_error::T>) {
    let mut env = env.clone();
    let env = &mut env;
    let (e1, root): (Option<typing_error::T>, Ty) = phase::localize(ety_env, env, root);
    // `ty_errs` and `acc` are OCaml lists built by consing: the head of the
    // list is the last element of the vector.
    let mut ty_errs: Vec<typing_error::T> = e1.into_iter().collect();
    let mut acc: Vec<(String, String, Pos)> = vec![];
    let mut root = root;
    for Id(pos, tconst) in ids {
        let tyl: Vec<Ty> =
            typing_utils::get_concrete_supertypes(None, None, None, true, env, root.clone());
        for ty in tyl {
            // `let (env, ty) = Env.expand_type env ty`: this environment is
            // dropped at the end of the iteration.
            let mut env = env.clone();
            let ty = env_::expand_type(&mut env, ty);
            match get_node(&ty) {
                Ty_::Tclass((_, class_name), _, _) => {
                    // `Env.get_class env class_name |> Decl_entry.to_option >>= fun class_ ->
                    //  Env.get_typeconst env class_ tconst >>= fun typeconst -> Some (...)`
                    let found = decl_entry::to_option(env_::get_class(&env, class_name))
                        .and_then(|class_| env_::get_typeconst(&env, &class_, tconst))
                        .map(|typeconst| {
                            (
                                typeconst.origin.as_str().to_string(),
                                tconst.clone(),
                                pos.clone(),
                            )
                        });
                    if let Some(x) = found {
                        acc.push(x)
                    }
                }
                _ => {}
            }
        }
        let (ty_err_opt, _cycles, root_) = expand_with_env(
            ety_env,
            env,
            None,
            Some(None),
            root,
            (pos_or_decl::of_raw_pos(pos.clone()), tconst.clone()),
            true,
        );
        root = root_;
        if let Some(e) = ty_err_opt {
            ty_errs.push(e)
        }
    }
    let _ty = root;
    acc.reverse();
    ty_errs.reverse();
    (acc, typing_error::multiple_opt(ty_errs))
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;

    fn prim(p: Tprim) -> Ty {
        mk((reason::none(), Ty_::Tprim(p)))
    }

    fn abstr(name: &str, lower: Vec<Ty>, upper: Vec<Ty>) -> Result {
        Result::Abstract(Abstract {
            name: name.to_string(),
            names: vec![],
            lower_bounds: ty_set::of_list(lower),
            upper_bounds: ty_set::of_list(upper),
        })
    }

    #[test]
    fn cheap_union_and_intersection() {
        let int = prim(Tprim::Tint);
        assert!(crate::typing_defs_core::phys_equal(
            &union(int.clone(), prim(Tprim::Tint)),
            &int
        ));
        let u = union(int.clone(), prim(Tprim::Tbool));
        assert!(matches!(get_node(&u), Ty_::Tunion(tyl) if tyl.len() == 2));
        let i = intersect(int, prim(Tprim::Tbool));
        assert!(matches!(get_node(&i), Ty_::Tintersection(tyl) if tyl.len() == 2));
    }

    #[test]
    fn union_results_needs_every_disjunct() {
        assert!(matches!(union_results(None, vec![]), Result::Missing(None)));
        let r = union_results(
            None,
            vec![
                Result::Exact(prim(Tprim::Tint)),
                Result::Exact(prim(Tprim::Tbool)),
            ],
        );
        assert!(matches!(r, Result::Exact(ty) if matches!(get_node(&ty), Ty_::Tunion(_))));
        let r = union_results(
            None,
            vec![Result::Exact(prim(Tprim::Tint)), Result::Missing(None)],
        );
        assert!(matches!(r, Result::Missing(None)));
        // Abstract results do not project through a union
        let r = union_results(
            None,
            vec![Result::Exact(prim(Tprim::Tint)), abstr("C", vec![], vec![])],
        );
        assert!(matches!(r, Result::Missing(None)));
    }

    #[test]
    fn intersect_results_keeps_what_it_can() {
        assert!(matches!(
            intersect_results(None, vec![]),
            Result::Missing(None)
        ));
        let r = intersect_results(
            None,
            vec![Result::Missing(None), Result::Exact(prim(Tprim::Tint))],
        );
        assert!(matches!(r, Result::Exact(_)));
        let r = intersect_results(
            None,
            vec![
                abstr("C", vec![], vec![prim(Tprim::Tint)]),
                abstr("D", vec![prim(Tprim::Tbool)], vec![prim(Tprim::Tfloat)]),
            ],
        );
        match r {
            Result::Abstract(Abstract {
                name,
                lower_bounds,
                upper_bounds,
                ..
            }) => {
                assert_eq!(name, "C");
                assert_eq!(lower_bounds.len(), 1);
                assert_eq!(upper_bounds.len(), 2);
            }
            _ => panic!("expected an abstract result"),
        }
        let r = intersect_results(
            None,
            vec![abstr("C", vec![], vec![]), Result::Exact(prim(Tprim::Tint))],
        );
        assert!(matches!(r, Result::Exact(_)));
    }

    #[test]
    fn type_parameter_names() {
        let id = (oxidized::pos::Pos::NONE, "T".to_string());
        assert_eq!(tp_name("<expr#1>", &id), "<expr#1>::T");
    }
}
