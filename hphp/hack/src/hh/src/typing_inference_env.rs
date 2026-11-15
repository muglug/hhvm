// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_inference_env.ml`. See `hh/PORTING.md`.
//!
//! `T` is cheap to clone: the type variable environment, the stack of type
//! variables and the occurrence maps are persistent collections (`Rc`
//! trees), and `Typing_logic.subtype_prop`, which is not, is behind an `Rc`
//! and copied on the first write after a clone.
//!
//! `InconsistentTypeVarState` is raised with `std::panic::panic_any`, so the
//! functions keep the signatures of the `.mli`. The one place that catches it
//! in OCaml (`Typing.expr`) can catch the unwind and downcast the payload.

use std::rc::Rc;

use oxidized::ast_defs;
use oxidized::pos::Pos;

use crate::hack_event_logger;
use crate::internal_type_set as ity_set;
use crate::tvid;
use crate::type_force_lazy_values;
use crate::type_mapper_generic;
use crate::type_visitor;
use crate::typing_defs_constraints::ConstraintType;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::deref_constraint_type;
use crate::typing_defs_constraints::internal_type;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::map_reason;
use crate::typing_defs_core::mk;
use crate::typing_logic as tl;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_tyvar_occurrences as occ;

/// `Internal_type_set.t`
type ITySet = ity_set::T;

/// `Tvid.Set.t`, as `oxidized` defines it.
type TvidSet = oxidized::tvid::set::Set;

/// `S_map.t`
type SMap<V> = im::OrdMap<String, V>;

/// `exception InconsistentTypeVarState of string`. It is the payload of the
/// panic that the functions of this module raise where the OCaml raises the
/// exception.
#[derive(Clone, PartialEq, Eq)]
pub struct InconsistentTypeVarState(pub String);

impl std::fmt::Display for InconsistentTypeVarState {
    /// `Printexc.to_string (InconsistentTypeVarState s)`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Typing_inference_env.InconsistentTypeVarState({:?})", self.0)
    }
}

impl std::fmt::Debug for InconsistentTypeVarState {
    /// As `Display`: `crate::exception::wrap` names an exception by its
    /// `Debug` (`Exception.to_string`).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl std::error::Error for InconsistentTypeVarState {}

/// `raise @@ InconsistentTypeVarState msg`
fn raise(exn: InconsistentTypeVarState) -> ! {
    std::panic::panic_any(exn)
}

#[derive(Clone, Debug)]
struct TyvarConstraints {
    /// Does this type variable appear covariantly in the type of the expression?
    appears_covariantly: bool,
    /// Does this type variable appear contravariantly in the type of the expression?
    /// If it appears in an invariant position then both will be true; if it doesn't
    /// appear at all then both will be false.
    appears_contravariantly: bool,
    lower_bounds: ITySet,
    upper_bounds: ITySet,
    /// Map associating a type to each type constant id of this variable.
    /// Whenever we localize "T1::T" in a constraint, we add a fresh type variable
    /// indexed by "T" in the type_constants of the type variable representing T1.
    /// This allows to properly check constraints on "T1::T".
    type_constants: SMap<(
        // id of the type constant "T", containing its position.
        PosId,
        Ty,
    )>,
}

#[derive(Clone, Debug)]
enum SolvingInfo {
    /// when the type variable is bound to a type
    TVIType(Ty),
    /// when the type variable is still unsolved
    TVIConstraints(TyvarConstraints),
}

#[derive(Clone, Debug)]
struct TyvarInfo {
    /// Where was the type variable introduced? (e.g. generic method invocation,
    /// new object construction)
    tyvar_pos: Pos,
    eager_solve_failed: bool,
    solving_info: SolvingInfo,
    is_error: bool,
    /// Shadow type variables collect upper-bound constraints for dynamic
    /// inference but are never solved. Attached to Tdynamic(Some v) types.
    is_shadow: bool,
    /// If this shadow type variable was created for a local variable, stores
    /// the variable name (e.g., "$d") for diagnostic output.
    shadow_local_name: Option<String>,
    rank: isize,
}

/// The information on each type variable: `tyvar_info Tvid.Map.t`, a
/// persistent map whose versions share their entries (`crate::pmap`), as the
/// OCaml ones do.
type Tvenv = crate::pmap::IntMap<TyvarInfo>;

/// contains the inference env, containing all the information necessary to
/// perform type inference.
#[derive(Clone, Debug)]
pub struct T {
    tvenv: Tvenv,
    /// Not in the OCaml: false only if no variable of `tvenv` has a
    /// `shadow_local_name` (then `collect_shadow_locals` need not walk it).
    /// The OCaml's `collect_shadow_locals` folds the whole tvenv once per
    /// function body and lambda (3% of the instructions on one file with
    /// tens of thousands of type variables). Exact: the flag is set wherever
    /// such a variable can enter `tvenv` (`set_tyvar_info`, `simple_merge`,
    /// `set_tvenv_handle`).
    may_have_shadow_locals: bool,
    /// The head of the OCaml lists is the front of the vectors.
    tyvars_stack: crate::plist::List<(Pos, crate::plist::List<tvid::T>)>,
    subtype_prop: Rc<tl::SubtypeProp>,
    tyvar_occurrences: occ::T,
    pos: Option<Pos>,
}

/// `Pos.string (Pos.to_absolute pos)`
fn pos_string_absolute(pos: &Pos) -> String {
    crate::pos::string(&crate::pos::to_absolute(pos))
}

pub mod log {
    use super::ITySet;
    use super::InternalType;
    use super::Pos;
    use super::SolvingInfo;
    use super::T;
    use super::Tvenv;
    use super::Ty;
    use super::TyvarConstraints;
    use super::TyvarInfo;
    use super::occ;
    use super::pos_string_absolute;
    use super::tvid;
    use crate::typing_log_value::Value;
    use crate::typing_log_value::bool_as_value;
    use crate::typing_log_value::internal_type_set_as_value;
    use crate::typing_log_value::locl_type_as_value;
    use crate::typing_log_value::make_map;
    use crate::typing_log_value::pos_as_value;
    use crate::typing_log_value::smap_as_value;
    use crate::typing_log_value::subtype_prop_as_value;
    use crate::typing_log_value::var_as_string;
    use crate::typing_log_value::variant_as_value;

    fn tyvar_constraints_as_value(tvcstr: &TyvarConstraints) -> Value {
        let TyvarConstraints {
            appears_covariantly,
            appears_contravariantly,
            type_constants,
            lower_bounds,
            upper_bounds,
        } = tvcstr;
        make_map(vec![
            (
                "appears_covariantly".to_string(),
                bool_as_value(*appears_covariantly),
            ),
            (
                "appears_contravariantly".to_string(),
                bool_as_value(*appears_contravariantly),
            ),
            (
                "lower_bounds".to_string(),
                internal_type_set_as_value(lower_bounds),
            ),
            (
                "upper_bounds".to_string(),
                internal_type_set_as_value(upper_bounds),
            ),
            (
                "type_constants".to_string(),
                smap_as_value(|(_, ty)| locl_type_as_value(Ty::clone(ty)), type_constants),
            ),
        ])
    }

    fn solving_info_as_value(sinfo: &SolvingInfo) -> Value {
        match sinfo {
            SolvingInfo::TVIType(ty) => {
                variant_as_value("TVIType".to_string(), locl_type_as_value(ty.clone()))
            }
            SolvingInfo::TVIConstraints(tvcstr) => variant_as_value(
                "TVIConstraints".to_string(),
                tyvar_constraints_as_value(tvcstr),
            ),
        }
    }

    fn tyvar_info_as_value(tvinfo: &TyvarInfo) -> Value {
        let TyvarInfo {
            tyvar_pos,
            eager_solve_failed,
            solving_info,
            is_error,
            is_shadow,
            shadow_local_name: _,
            rank,
        } = tvinfo;
        make_map(vec![
            ("tyvar_pos".to_string(), pos_as_value(tyvar_pos)),
            (
                "eager_solve_failed".to_string(),
                bool_as_value(*eager_solve_failed),
            ),
            (
                "solving_info".to_string(),
                solving_info_as_value(solving_info),
            ),
            ("is_error".to_string(), bool_as_value(*is_error)),
            ("is_shadow".to_string(), bool_as_value(*is_shadow)),
            ("rank".to_string(), Value::Atom(rank.to_string())),
        ])
    }

    fn tvenv_as_value(tvenv: &Tvenv) -> Value {
        Value::Map(
            tvenv
                .iter()
                .map(|(i, tvinfo)| (var_as_string(*i), tyvar_info_as_value(tvinfo)))
                .collect(),
        )
    }

    fn tyvars_stack_as_value(tyvars_stack: &crate::plist::List<(Pos, crate::plist::List<tvid::T>)>) -> Value {
        Value::List(
            tyvars_stack
                .iter()
                .map(|(_p, l)| {
                    Value::List(l.iter().map(|i| Value::Atom(var_as_string(*i))).collect())
                })
                .collect(),
        )
    }

    pub fn inference_env_as_value(env: &T) -> Value {
        let T {
            tvenv,
            may_have_shadow_locals: _,
            tyvars_stack,
            subtype_prop,
            tyvar_occurrences,
            pos: _,
        } = env;
        make_map(vec![
            ("tvenv".to_string(), tvenv_as_value(tvenv)),
            (
                "tyvars_stack".to_string(),
                tyvars_stack_as_value(tyvars_stack),
            ),
            (
                "subtype_prop".to_string(),
                subtype_prop_as_value((**subtype_prop).clone()),
            ),
            (
                "tyvar_occurrences".to_string(),
                occ::log::as_value(tyvar_occurrences),
            ),
        ])
    }

    /// `` `Assoc ``. The fields keep the order of the OCaml only if
    /// `serde_json` is built with `preserve_order`.
    fn assoc(fields: Vec<(&str, serde_json::Value)>) -> serde_json::Value {
        serde_json::Value::Object(
            fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
        )
    }

    fn solving_info_to_json(
        p_locl_ty: &dyn Fn(&Ty) -> String,
        p_internal_type: &dyn Fn(&InternalType) -> String,
        solving_info: &SolvingInfo,
    ) -> serde_json::Value {
        let constraints_to_json = |cstr: &TyvarConstraints| {
            let TyvarConstraints {
                appears_covariantly,
                appears_contravariantly,
                lower_bounds,
                upper_bounds,
                type_constants: _,
            } = cstr;
            let bounds_to_json = |bs: &ITySet| -> Vec<serde_json::Value> {
                bs.iter()
                    .map(|b| serde_json::Value::String(p_internal_type(b)))
                    .collect()
            };
            assoc(vec![
                (
                    "appears_covariantly",
                    serde_json::Value::Bool(*appears_covariantly),
                ),
                (
                    "appears_contravariantly",
                    serde_json::Value::Bool(*appears_contravariantly),
                ),
                (
                    "lower_bounds",
                    serde_json::Value::Array(bounds_to_json(lower_bounds)),
                ),
                (
                    "upper_bounds",
                    serde_json::Value::Array(bounds_to_json(upper_bounds)),
                ),
            ])
        };
        let locl_ty_to_json = |x: &Ty| serde_json::Value::String(p_locl_ty(x));
        match solving_info {
            SolvingInfo::TVIType(locl_ty) => assoc(vec![("type", locl_ty_to_json(locl_ty))]),
            SolvingInfo::TVIConstraints(cstr) => {
                assoc(vec![("constraints", constraints_to_json(cstr))])
            }
        }
    }

    /// Convert a type variable from an environment into json
    pub fn tyvar_to_json(
        p_locl_ty: impl Fn(&Ty) -> String,
        p_internal_type: impl Fn(&InternalType) -> String,
        env: &T,
        v: tvid::T,
    ) -> serde_json::Value {
        match env.tvenv.get(&v) {
            None => serde_json::Value::Null,
            Some(TyvarInfo {
                tyvar_pos,
                eager_solve_failed,
                solving_info,
                is_error,
                is_shadow,
                shadow_local_name: _,
                rank,
            }) => assoc(vec![
                (
                    "tyvar_pos",
                    serde_json::Value::String(pos_string_absolute(tyvar_pos)),
                ),
                (
                    "eager_solve_failed",
                    serde_json::Value::Bool(*eager_solve_failed),
                ),
                (
                    "solving_info",
                    solving_info_to_json(&p_locl_ty, &p_internal_type, solving_info),
                ),
                ("is_error", serde_json::Value::Bool(*is_error)),
                ("is_shadow", serde_json::Value::Bool(*is_shadow)),
                // `Intlit (Int.to_string rank)
                ("rank", serde_json::Value::Number((*rank).into())),
            ]),
        }
    }
}

fn empty_tvenv() -> Tvenv {
    Tvenv::new()
}

pub fn empty_inference_env() -> T {
    T {
        tvenv: empty_tvenv(),
        may_have_shadow_locals: false,
        tyvars_stack: crate::plist::List::new(),
        subtype_prop: Rc::new(tl::valid()),
        tyvar_occurrences: occ::init(),
        pos: None,
    }
}

fn empty_ity_set() -> ITySet {
    ITySet::default()
}

/// `ITySet.singleton`
fn singleton_ity_set(ty: InternalType) -> ITySet {
    std::iter::once(ty).collect()
}

fn empty_tyvar_constraints() -> TyvarConstraints {
    TyvarConstraints {
        lower_bounds: empty_ity_set(),
        upper_bounds: empty_ity_set(),
        appears_covariantly: false,
        appears_contravariantly: false,
        type_constants: SMap::new(),
    }
}

fn empty_tyvar_info(tyvar_pos: Pos, rank: isize) -> TyvarInfo {
    TyvarInfo {
        tyvar_pos,
        rank,
        eager_solve_failed: false,
        solving_info: SolvingInfo::TVIConstraints(empty_tyvar_constraints()),
        is_error: false,
        is_shadow: false,
        shadow_local_name: None,
    }
}

fn get_tyvar_info_opt(env: &T, v: tvid::T) -> Option<&TyvarInfo> {
    env.tvenv.get(&v)
}

fn set_tyvar_info(env: &mut T, v: tvid::T, tvinfo: TyvarInfo) {
    if tvinfo.shadow_local_name.is_some() {
        env.may_have_shadow_locals = true;
    }
    env.tvenv.insert(v, tvinfo);
}

fn get_solving_info_opt(env: &T, var: tvid::T) -> Option<&SolvingInfo> {
    match get_tyvar_info_opt(env, var) {
        None => None,
        Some(tvinfo) => Some(&tvinfo.solving_info),
    }
}

fn set_solving_info(env: &mut T, tyvar_pos: Option<Pos>, x: tvid::T, solving_info: SolvingInfo) {
    let tyvar_pos = tyvar_pos.unwrap_or(Pos::NONE);
    let tvinfo = match get_tyvar_info_opt(env, x) {
        Some(tvinfo) => TyvarInfo {
            tyvar_pos: tvinfo.tyvar_pos.clone(),
            eager_solve_failed: tvinfo.eager_solve_failed,
            solving_info,
            is_error: tvinfo.is_error,
            is_shadow: tvinfo.is_shadow,
            shadow_local_name: tvinfo.shadow_local_name.clone(),
            rank: tvinfo.rank,
        },
        None => TyvarInfo {
            solving_info,
            ..empty_tyvar_info(tyvar_pos, 0)
        },
    };
    set_tyvar_info(env, x, tvinfo)
}

pub fn tyvar_occurs_in_tyvar(env: &T, v: tvid::T, in_: tvid::T) -> bool {
    occ::occurs_in(&env.tyvar_occurrences, v, in_)
}

/// [`get_tyvar_occurrences`], as a persistent set (no copy).
pub fn get_tyvar_occurrences_set(env: &T, v: tvid::T) -> occ::OccSet {
    occ::get_tyvar_occurrences_set(&env.tyvar_occurrences, v)
}

pub fn get_tyvar_occurrences(env: &T, v: tvid::T) -> TvidSet {
    occ::get_tyvar_occurrences(&env.tyvar_occurrences, v)
}

pub fn get_tyvars_in_tyvar(env: &T, v: tvid::T) -> TvidSet {
    occ::get_tyvars_in_tyvar(&env.tyvar_occurrences, v)
}

pub fn contains_unsolved_tyvars(env: &T, v: tvid::T) -> bool {
    occ::contains_unsolved_tyvars(&env.tyvar_occurrences, v)
}

pub fn tyvar_is_solved(env: &T, var: tvid::T) -> bool {
    match get_solving_info_opt(env, var) {
        None => false,
        Some(sinfo) => match sinfo {
            SolvingInfo::TVIConstraints(_) => false,
            SolvingInfo::TVIType(_) => true,
        },
    }
}

/// Get type variables in a type that are either unsolved or
/// solved to a type that itself contains unsolved type variables.
fn get_unsolved_vars_in_ty(env: &T, ty: &Ty) -> TvidSet {
    struct Gatherer<'a> {
        env: &'a T,
    }
    impl type_visitor::LoclTypeVisitor<TvidSet> for Gatherer<'_> {
        fn on_tvar(&mut self, mut vars: TvidSet, _r: &Reason, v: tvid::T) -> TvidSet {
            let env = self.env;
            // Add it if it has unsolved type vars or if it is itself unsolved.
            if !tyvar_is_solved(env, v) || occ::contains_unsolved_tyvars(&env.tyvar_occurrences, v)
            {
                vars.insert(v);
                vars
            } else {
                vars
            }
        }

        fn on_type(&mut self, vars: TvidSet, ty: &Ty) -> TvidSet {
            // Not in the OCaml, which visits it: a type without type
            // variables has none to gather (see `typing_defs_core::ty_flags`:
            // a clear TVAR flag means no `Tvar` occurs). Skipping tyvar-free
            // types in this and the other tyvar-only visitors saved 3.0% of
            // the instructions of the check phase on the benchmark sample.
            if !ty.may_have_tyvars() {
                return vars;
            }
            crate::typing_utils::locl_type_visitor_on_type(self, vars, ty)
        }
    }
    let mut gatherer = Gatherer { env };
    type_visitor::LoclTypeVisitor::on_type(&mut gatherer, TvidSet::new(), ty)
}

fn make_tyvars_occur_in_tyvar(env: &mut T, vars: TvidSet, occur_in: tvid::T) {
    let x = occur_in;
    occ::make_tyvars_occur_in_tyvar(&mut env.tyvar_occurrences, vars, x)
}

pub fn make_tyvar_no_more_occur_in_tyvar(env: &mut T, v: tvid::T, no_more_in: tvid::T) {
    let v_ = no_more_in;
    occ::make_tyvar_no_more_occur_in_tyvar(&mut env.tyvar_occurrences, v, v_)
}

pub fn get_direct_binding(env: &T, v: tvid::T) -> Option<Ty> {
    match get_solving_info_opt(env, v) {
        None | Some(SolvingInfo::TVIConstraints(_)) => None,
        Some(SolvingInfo::TVIType(ty)) => Some(ty.clone()),
    }
}

pub fn bind(env: &mut T, tyvar_pos: Option<Pos>, v: tvid::T, ty: Ty) {
    let tyvar_pos = tyvar_pos.unwrap_or(Pos::NONE);
    set_solving_info(env, Some(tyvar_pos), v, SolvingInfo::TVIType(ty))
}

fn update_tyvar_occurrences(env: &mut T, v: tvid::T, ty: &Ty) {
    occ::unbind_tyvar(&mut env.tyvar_occurrences, v);
    let unsolved_vars_in_ty = get_unsolved_vars_in_ty(env, ty);
    make_tyvars_occur_in_tyvar(env, unsolved_vars_in_ty, v);
}

pub fn add(env: &mut T, tyvar_pos: Option<Pos>, v: tvid::T, ty: Ty) {
    let tyvar_pos = tyvar_pos.unwrap_or(Pos::NONE);
    bind(env, Some(tyvar_pos), v, ty.clone());
    update_tyvar_occurrences(env, v, &ty);
}

/// Call this from any functions below that can produce InconsistentTypeVarState
/// That way we can enforce in tests that we are not making
/// unactionable error messages in prod (errors without even filenames are hard to repro)
fn check_env_pos_invariant(env: &T) {
    match &env.pos {
        Some(pos) if crate::pos::equal_none(pos) => hack_event_logger::invariant_violation_bug(
            None,
            None,
            None,
            None,
            None,
            "missing env.pos. Make sure we're propagating positions correctly, see D91705550.",
        ),
        None => hack_event_logger::invariant_violation_bug(
            None,
            None,
            None,
            None,
            None,
            "expected Some pos, but env.pos is None. Make sure we're propagating positions correctly, see D91705550.",
        ),
        Some(_) => (),
    }
}

/// The aliases that `get_type` found on its way to the solution of a type
/// variable, and that it makes point straight at the end of the chain
/// (`shorten_paths`) before returning `ty`.
pub struct PendingShortening {
    ty: Ty,
    aliases: TvidSet,
    r: Reason,
    v: tvid::T,
}

/// `get r v aliases`: follows the chain of aliased type variables. Every step
/// of the OCaml recursion reads the environment it started with; only
/// `shorten_paths`, at the end, changes it. The shortening is returned to the
/// caller as `Err` (`Ok` when `aliases` is empty, where `shorten_paths` does
/// nothing), so that the common case reads the environment without needing
/// to write it.
///
/// The OCaml's `get_type` (typing_inference_env.ml) always returns the
/// environment of `shorten_paths`. Here the lookup works on `&T` and the
/// write is done only when there are aliases: `expand_var` runs at almost
/// every step of typing, and a write would copy the shared environment data
/// (copy-on-write) for nothing. Same result: `shorten_paths` on no aliases
/// leaves the environment as it is.
fn get_type_resolve(
    env: &T,
    reason_in: &Reason,
    tvid_in: tvid::T,
) -> Result<Ty, PendingShortening> {
    get_type_resolve_and_eager_solve_fail(env, reason_in, tvid_in).0
}

/// [`get_type_resolve`], and `get_tyvar_eager_solve_fail env tvid_in` (read
/// in the same lookup: not in the OCaml, which looks the variable up again).
/// The two tvenv lookups of `expand_var` were 10-15% of the instructions on
/// files with tens of thousands of type variables; the environment does not
/// change between them, so one lookup gives the same flag.
fn get_type_resolve_and_eager_solve_fail(
    env: &T,
    reason_in: &Reason,
    tvid_in: tvid::T,
) -> (Result<Ty, PendingShortening>, bool) {
    let mut eager_solve_failed = false;
    // `r` is borrowed (`None` for `reason_in`), and cloned only into what is
    // returned.
    let mut r: Option<&Reason> = None;
    let mut v = tvid_in;
    let mut aliases = TvidSet::new();
    let pending = |ty: Ty, aliases: TvidSet, r: Option<&Reason>, v: tvid::T| {
        if aliases.is_empty() {
            Ok(ty)
        } else {
            let r = r.unwrap_or(reason_in).clone();
            Err(PendingShortening { ty, aliases, r, v })
        }
    };
    let mut first = true;
    loop {
        let tvinfo = get_tyvar_info_opt(env, v);
        if first {
            first = false;
            eager_solve_failed = tvinfo.is_some_and(|tvinfo| tvinfo.eager_solve_failed);
        }
        match tvinfo.map(|tvinfo| &tvinfo.solving_info) {
            Some(SolvingInfo::TVIType(ty)) => match get_node(ty) {
                Ty_::Tvar(v_) => {
                    if aliases.contains(&v) {
                        raise(InconsistentTypeVarState(
                            "Two type variables are aliasing each other!".to_string(),
                        ));
                    }
                    aliases.insert(v);
                    r = Some(get_reason(ty));
                    v = *v_;
                }
                _ => {
                    // When we have a concrete solution r, record the flow of that solution as a
                    // prefix to the original type variables's reason; when report in an error
                    // we should then see the path of the relevant uppper / lower bounds
                    // as the prefix for any flow through typing.
                    // We don't record the flow when we are pointing at another tyvar on the
                    // heap since we would end up with a chain of flows representing unification
                    let ty = map_reason(ty.clone(), |solution| {
                        typing_reason::solved(tvid_in, solution, reason_in.clone())
                    });
                    return (pending(ty, aliases, r, v), eager_solve_failed);
                }
            },
            None | Some(SolvingInfo::TVIConstraints(_)) => {
                let ty = mk((r.unwrap_or(reason_in).clone(), Ty_::Tvar(v)));
                return (pending(ty, aliases, r, v), eager_solve_failed);
            }
        }
    }
}

/// `shorten_paths` (local to `get_type`), then the result of `get`.
pub fn shorten_paths(env: &mut T, pending: PendingShortening) -> Ty {
    let PendingShortening { ty, aliases, r, v } = pending;
    for &v_ in &aliases {
        add(env, None, v_, mk((r.clone(), Ty_::Tvar(v))))
    }
    ty
}

pub fn get_type(env: &mut T, reason_in: Reason, tvid_in: tvid::T) -> Ty {
    match get_type_shared(env, reason_in, tvid_in) {
        Ok(ty) => ty,
        Err(pending) => shorten_paths(env, pending),
    }
}

/// `get_type` on an environment that is only read: `Err` when the OCaml
/// would shorten a chain of aliases (the caller then finishes with
/// [`shorten_paths`] on a mutable environment).
pub fn get_type_shared(
    env: &T,
    reason_in: Reason,
    tvid_in: tvid::T,
) -> Result<Ty, PendingShortening> {
    check_env_pos_invariant(env);
    get_type_resolve(env, &reason_in, tvid_in)
}

fn create_tyvar_constraints(variance: Option<ast_defs::Variance>) -> SolvingInfo {
    let (appears_covariantly, appears_contravariantly) = match variance {
        Some(ast_defs::Variance::Invariant) => (true, true),
        Some(ast_defs::Variance::Covariant) => (true, false),
        Some(ast_defs::Variance::Contravariant) => (false, true),
        None => (false, false),
    };
    let tyvar_constraints = TyvarConstraints {
        appears_covariantly,
        appears_contravariantly,
        ..empty_tyvar_constraints()
    };
    SolvingInfo::TVIConstraints(tyvar_constraints)
}

fn fresh_unsolved_tyvar(
    env: &mut T,
    v: tvid::T,
    rank: isize,
    variance: Option<ast_defs::Variance>,
    is_error: Option<bool>,
    tyvar_pos: Pos,
) {
    let is_error = is_error.unwrap_or(false);
    let solving_info = create_tyvar_constraints(variance);
    let tvinfo = TyvarInfo {
        tyvar_pos,
        solving_info,
        eager_solve_failed: false,
        is_error,
        is_shadow: false,
        shadow_local_name: None,
        rank,
    };
    set_tyvar_info(env, v, tvinfo)
}

/// Create a shadow type variable — a type variable that only accumulates upper
/// bounds and is excluded from solving. Used for dynamic inference: tracks how
/// dynamic-typed expressions are used, building a constraint set that describes
/// their inferred use-type.
pub fn fresh_shadow_tyvar(
    env: &mut T,
    id_provider: &tvid::Provider,
    local_name: Option<String>,
    pos: Pos,
) -> tvid::T {
    let v = tvid::make(id_provider);
    let solving_info = create_tyvar_constraints(Some(ast_defs::Variance::Invariant));
    let tvinfo = TyvarInfo {
        tyvar_pos: pos,
        solving_info,
        eager_solve_failed: false,
        is_error: false,
        is_shadow: true,
        shadow_local_name: local_name,
        rank: 0,
    };
    set_tyvar_info(env, v, tvinfo);
    v
}

pub fn is_shadow(env: &T, v: tvid::T) -> bool {
    match get_tyvar_info_opt(env, v) {
        Some(tvinfo) => tvinfo.is_shadow,
        None => false,
    }
}

pub fn iter_shadow_tyvars(env: &T, mut f: impl FnMut(tvid::T)) {
    for (v, tvinfo) in &env.tvenv {
        if tvinfo.is_shadow {
            f(*v)
        }
    }
}

pub fn collect_shadow_locals(env: &T) -> Vec<(String, Pos, tvid::T)> {
    // Not in the OCaml, which always folds the tvenv: see
    // `T.may_have_shadow_locals`.
    if !env.may_have_shadow_locals {
        return vec![];
    }
    // `Tvid.Map.fold` consing onto the accumulator: the largest variable
    // comes first.
    let mut acc = vec![];
    for (v, tvinfo) in env.tvenv.iter().rev() {
        match &tvinfo.shadow_local_name {
            Some(name) => acc.push((name.clone(), tvinfo.tyvar_pos.clone(), *v)),
            None => {}
        }
    }
    acc
}

fn add_current_tyvar(
    variance: Option<ast_defs::Variance>,
    is_error: Option<bool>,
    env: &mut T,
    p: Pos,
    v: tvid::T,
    rank: isize,
) {
    fresh_unsolved_tyvar(env, v, rank, variance, is_error, p);
    match env.tyvars_stack.front_mut() {
        Some((_expr_pos, tyvars)) => tyvars.push_front(v),
        None => {}
    }
}

/// Same as fresh_type but takes a specific reason as parameter.
pub fn fresh_type_reason(
    variance: Option<ast_defs::Variance>,
    is_error: Option<bool>,
    env: &mut T,
    id_provider: &tvid::Provider,
    p: Pos,
    mk_reason: impl FnOnce(tvid::T) -> Reason,
) -> Ty {
    let v = tvid::make(id_provider);
    let r = mk_reason(v);
    add_current_tyvar(variance, is_error, env, p, v, 0);
    mk((r, Ty_::Tvar(v)))
}

pub fn fresh_type(
    variance: Option<ast_defs::Variance>,
    env: &mut T,
    id_provider: &tvid::Provider,
    p: Pos,
) -> Ty {
    let p_ = p.clone();
    fresh_type_reason(variance, Some(false), env, id_provider, p, |v| {
        typing_reason::type_variable(p_, v)
    })
}

pub fn fresh_type_invariant(env: &mut T, id_provider: &tvid::Provider, p: Pos) -> Ty {
    fresh_type(Some(ast_defs::Variance::Invariant), env, id_provider, p)
}

pub fn fresh_type_invariant_with_rank(
    env: &mut T,
    provider: &tvid::Provider,
    rank: isize,
    pos: Pos,
) -> Ty {
    let tvid = tvid::make(provider);
    let reason = typing_reason::type_variable(pos.clone(), tvid);
    add_current_tyvar(
        Some(ast_defs::Variance::Invariant),
        Some(false),
        env,
        pos,
        tvid,
        rank,
    );
    mk((reason, Ty_::Tvar(tvid)))
}

pub fn wrap_ty_in_var(env: &mut T, id_provider: &tvid::Provider, r: Reason, ty: Ty) -> Ty {
    let v = tvid::make(id_provider);
    let tvinfo = TyvarInfo {
        // `Reason.to_pos r |> Pos_or_decl.unsafe_to_raw_pos`: `PosOrDecl` is
        // `Pos` in `oxidized`, so the conversion is the identity.
        tyvar_pos: typing_reason::to_pos(&r),
        eager_solve_failed: false,
        solving_info: SolvingInfo::TVIType(ty.clone()),
        is_error: false,
        is_shadow: false,
        shadow_local_name: None,
        rank: 0,
    };
    set_tyvar_info(env, v, tvinfo);
    update_tyvar_occurrences(env, v, &ty);
    mk((r, Ty_::Tvar(v)))
}

pub fn open_tyvars(env: &mut T, p: Pos) {
    env.tyvars_stack.push_front((p, crate::plist::List::new()))
}

pub fn close_tyvars(env: &mut T) {
    check_env_pos_invariant(env);
    match env.tyvars_stack.pop_front() {
        None => raise(InconsistentTypeVarState(
            "close_tyvars: empty stack".to_string(),
        )),
        Some(_) => {}
    }
}

pub fn get_current_tyvars(env: &T) -> Vec<tvid::T> {
    match env.tyvars_stack.front() {
        None => vec![],
        Some((_, tyvars)) => tyvars.iter().copied().collect(),
    }
}

fn get_tyvar_constraints_opt(env: &T, var: tvid::T) -> Option<&TyvarConstraints> {
    check_env_pos_invariant(env);
    match get_solving_info_opt(env, var) {
        Some(SolvingInfo::TVIConstraints(constraints)) => Some(constraints),
        None | Some(SolvingInfo::TVIType(_)) => None,
    }
}

fn get_tyvar_constraints_exn(env: &T, var: tvid::T) -> TyvarConstraints {
    check_env_pos_invariant(env);
    let error = |msg: &str| match &env.pos {
        None => InconsistentTypeVarState(format!(
            "Attempting to get constraints for {} type variable {}.",
            msg,
            crate::typing_log_value::var_as_string(var)
        )),
        Some(pos) => InconsistentTypeVarState(format!(
            "Attempting to get constraints for {} type variable {} at {}",
            msg,
            crate::typing_log_value::var_as_string(var),
            pos_string_absolute(pos)
        )),
    };
    match get_solving_info_opt(env, var) {
        None => raise(error("non-existing")),
        Some(SolvingInfo::TVIType(_)) => raise(error("already solved")),
        Some(SolvingInfo::TVIConstraints(constraints)) => constraints.clone(),
    }
}

fn set_tyvar_constraints(env: &mut T, v: tvid::T, tyvar_constraints: TyvarConstraints) {
    set_solving_info(env, None, v, SolvingInfo::TVIConstraints(tyvar_constraints))
}

pub fn get_tyvar_eager_solve_fail(env: &T, v: tvid::T) -> bool {
    match get_tyvar_info_opt(env, v) {
        None => false,
        Some(tvinfo) => tvinfo.eager_solve_failed,
    }
}

pub fn expand_var(env: &mut T, r: Reason, v: tvid::T) -> Ty {
    let ty = get_type(env, r.clone(), v);
    expand_var_finish(env, r, v, ty)
}

/// `expand_var` on an environment that is only read: `Err` as for
/// [`get_type_shared`] (finish with [`expand_var_pending`]).
pub fn expand_var_shared(env: &T, r: Reason, v: tvid::T) -> Result<Ty, PendingShortening> {
    let ty = get_type_shared(env, r.clone(), v)?;
    Ok(expand_var_finish(env, r, v, ty))
}

pub fn expand_var_pending(env: &mut T, r: Reason, v: tvid::T, pending: PendingShortening) -> Ty {
    let ty = shorten_paths(env, pending);
    expand_var_finish(env, r, v, ty)
}

/// [`expand_var_shared`] with a borrowed reason (which is copied only into
/// the result).
pub fn expand_var_shared_ref(env: &T, r: &Reason, v: tvid::T) -> Result<Ty, PendingShortening> {
    // `get_type_shared`
    check_env_pos_invariant(env);
    let (ty, eager_solve_failed) = get_type_resolve_and_eager_solve_fail(env, r, v);
    let ty = ty?;
    // `expand_var_finish_ref`, with the flag read by the lookup above (the
    // environment did not change since).
    Ok(if eager_solve_failed {
        map_reason(ty, |_| typing_reason::solve_fail(typing_reason::to_pos(r)))
    } else {
        ty
    })
}

/// The end of `expand_var`, once `get_type` has returned `ty` (and changed
/// the environment, if it did).
fn expand_var_finish(env: &T, r: Reason, v: tvid::T, ty: Ty) -> Ty {
    expand_var_finish_ref(env, &r, v, ty)
}

fn expand_var_finish_ref(env: &T, r: &Reason, v: tvid::T, ty: Ty) -> Ty {
    if get_tyvar_eager_solve_fail(env, v) {
        // `mk (Reason.solve_fail (Reason.to_pos r), get_node ty)`
        map_reason(ty, |_| typing_reason::solve_fail(typing_reason::to_pos(r)))
    } else {
        ty
    }
}

pub fn expand_type(env: &mut T, x: Ty) -> Ty {
    match get_node(&x) {
        Ty_::Tvar(v) => expand_var(env, get_reason(&x).clone(), *v),
        _ => x,
    }
}

struct FullExpander;

impl type_mapper_generic::InternalTypeMapper<T> for FullExpander {
    fn on_tvar(&mut self, env: &mut T, r: Reason, v: tvid::T) -> Ty {
        let ty = expand_var(env, r, v);
        match get_node(&ty) {
            Ty_::Tvar(_) => ty,
            _ => type_mapper_generic::InternalTypeMapper::on_type(self, env, ty),
        }
    }
}

pub fn fully_expand_type(env: &mut T, ty: Ty) -> Ty {
    let mut full_expander = FullExpander;
    type_mapper_generic::InternalTypeMapper::on_type(&mut full_expander, env, ty)
}

pub fn expand_internal_type(env: &mut T, ty: InternalType) -> InternalType {
    match ty {
        InternalType::ConstraintType(_) => ty,
        InternalType::LoclType(ty) => {
            let ty = expand_type(env, ty);
            InternalType::LoclType(ty)
        }
    }
}

pub fn get_tyvar_pos(env: &T, var: tvid::T) -> Pos {
    match get_tyvar_info_opt(env, var) {
        None => Pos::NONE,
        Some(tvinfo) => tvinfo.tyvar_pos.clone(),
    }
}

fn get_tyvar_lower_bounds_opt(env: &T, v: tvid::T) -> Option<ITySet> {
    get_tyvar_constraints_opt(env, v).map(|x| x.lower_bounds.clone())
}

fn get_tyvar_upper_bounds_opt(env: &T, v: tvid::T) -> Option<ITySet> {
    get_tyvar_constraints_opt(env, v).map(|x| x.upper_bounds.clone())
}

pub fn get_tyvar_lower_bounds(env: &T, var: tvid::T) -> ITySet {
    match get_solving_info_opt(env, var) {
        None => empty_ity_set(),
        Some(solving_info) => match solving_info {
            SolvingInfo::TVIType(ty) => singleton_ity_set(InternalType::LoclType(ty.clone())),
            SolvingInfo::TVIConstraints(cstr) => cstr.lower_bounds.clone(),
        },
    }
}

pub fn get_tyvar_upper_bounds(env: &T, var: tvid::T) -> ITySet {
    match get_solving_info_opt(env, var) {
        None => empty_ity_set(),
        Some(solving_info) => match solving_info {
            SolvingInfo::TVIType(ty) => singleton_ity_set(InternalType::LoclType(ty.clone())),
            SolvingInfo::TVIConstraints(cstr) => cstr.upper_bounds.clone(),
        },
    }
}

pub fn set_tyvar_lower_bounds(env: &mut T, var: tvid::T, lower_bounds: ITySet) {
    match get_tyvar_constraints_opt(env, var) {
        None => {}
        Some(tyvar_constraints) => {
            let tyvar_constraints = TyvarConstraints {
                lower_bounds,
                ..tyvar_constraints.clone()
            };
            set_tyvar_constraints(env, var, tyvar_constraints)
        }
    }
}

pub fn set_tyvar_upper_bounds(env: &mut T, var: tvid::T, upper_bounds: ITySet) {
    match get_tyvar_constraints_opt(env, var) {
        None => {}
        Some(tyvar_constraints) => {
            let tyvar_constraints = TyvarConstraints {
                upper_bounds,
                ..tyvar_constraints.clone()
            };
            set_tyvar_constraints(env, var, tyvar_constraints)
        }
    }
}

pub fn set_tyvar_eager_solve_fail(env: &mut T, v: tvid::T) {
    match get_tyvar_info_opt(env, v) {
        None => {}
        Some(tvinfo) => {
            let tvinfo = TyvarInfo {
                eager_solve_failed: true,
                ..tvinfo.clone()
            };
            set_tyvar_info(env, v, tvinfo)
        }
    }
}

pub fn get_tyvar_appears_covariantly(env: &T, var: tvid::T) -> bool {
    match get_tyvar_constraints_opt(env, var) {
        Some(cstr) => cstr.appears_covariantly,
        None => false,
    }
}

pub fn get_tyvar_appears_contravariantly(env: &T, var: tvid::T) -> bool {
    match get_tyvar_constraints_opt(env, var) {
        Some(cstr) => cstr.appears_contravariantly,
        None => false,
    }
}

pub fn get_tyvar_appears_invariantly(env: &T, var: tvid::T) -> bool {
    get_tyvar_appears_covariantly(env, var) && get_tyvar_appears_contravariantly(env, var)
}

pub fn set_tyvar_appears_covariantly(env: &mut T, v: tvid::T) {
    let tyvar_constraints = get_tyvar_constraints_exn(env, v);
    let tyvar_constraints = TyvarConstraints {
        appears_covariantly: true,
        ..tyvar_constraints
    };
    set_tyvar_constraints(env, v, tyvar_constraints);
}

pub fn set_tyvar_appears_contravariantly(env: &mut T, v: tvid::T) {
    let tyvar_constraints = get_tyvar_constraints_exn(env, v);
    let tyvar_constraints = TyvarConstraints {
        appears_contravariantly: true,
        ..tyvar_constraints
    };
    set_tyvar_constraints(env, v, tyvar_constraints);
}

pub fn get_tyvar_type_consts(env: &T, var: tvid::T) -> SMap<(PosId, Ty)> {
    match get_tyvar_constraints_opt(env, var) {
        Some(cstr) => cstr.type_constants.clone(),
        None => SMap::new(),
    }
}

pub fn get_tyvar_type_const(env: &T, var: tvid::T, tyconstid: &PosId) -> Option<(PosId, Ty)> {
    let (_, tyconstid) = tyconstid;
    get_tyvar_type_consts(env, var).get(tyconstid).cloned()
}

pub fn set_tyvar_type_const(env: &mut T, var: tvid::T, tyconstid: PosId, ty: Ty) {
    let tyconstid_ = tyconstid.1.clone();
    let mut tvinfo = get_tyvar_constraints_exn(env, var);
    tvinfo.type_constants.insert(tyconstid_, (tyconstid, ty));
    set_tyvar_constraints(env, var, tvinfo);
    // We don't want to solve such type variables too early, because of valid
    // code patterns like that one:
    //
    // abstract class A { abstract type const T; }
    //
    // function f<TA as A, T>(TA $_, T $_) : ... where T = TA::T
    //
    // We force it covariantly until we can implement a proper fix to
    // avoid eager solving (to the upperbound) as it would bind TA to
    // an abstract class
    set_tyvar_appears_covariantly(env, var);
}

/// Conjoin a subtype proposition onto the subtype_prop in the environment
pub fn add_subtype_prop(env: &mut T, prop: tl::SubtypeProp) {
    let subtype_prop = Rc::make_mut(&mut env.subtype_prop);
    let old = std::mem::replace(subtype_prop, tl::valid());
    *subtype_prop = tl::conj(old, prop);
}

pub fn get_current_pos_from_tyvar_stack(env: &T) -> Option<Pos> {
    match env.tyvars_stack.front() {
        Some((p, _)) => Some(p.clone()),
        None => None,
    }
}

/// Add a single new upper bound [ty] to type variable [var] in [env.tvenv].
/// If the optional [intersect] operation is supplied, then use this to avoid
/// adding redundant bounds by merging the type with existing bounds. This makes
/// sense because a conjunction of upper bounds
///   (v <: t1) /\ ... /\ (v <: tn)
/// is equivalent to a single upper bound
///   v <: (t1 & ... & tn)
pub fn add_tyvar_upper_bound(
    intersect: Option<&mut dyn FnMut(InternalType, &[InternalType]) -> Vec<InternalType>>,
    env: &mut T,
    var: tvid::T,
    ty: InternalType,
) {
    let tvconstraints = get_tyvar_constraints_exn(env, var);
    let upper_bounds = match intersect {
        None => {
            let mut upper_bounds = tvconstraints.upper_bounds.clone();
            upper_bounds.insert(ty);
            upper_bounds
        }
        Some(intersect) => intersect(
            ty,
            &tvconstraints
                .upper_bounds
                .iter()
                .cloned()
                .collect::<Vec<InternalType>>(),
        )
        .into_iter()
        .collect(),
    };
    set_tyvar_constraints(
        env,
        var,
        TyvarConstraints {
            upper_bounds,
            ..tvconstraints
        },
    );
}

/// Add a single new lower bound [ty] to type variable [var] in [env.tvenv].
/// If the optional [union] operation is supplied, then use this to avoid
/// adding redundant bounds by merging the type with existing bounds. This makes
/// sense because a conjunction of lower bounds
///   (t1 <: v) /\ ... /\ (tn <: v)
/// is equivalent to a single lower bound
///   (t1 | ... | tn) <: v
pub fn add_tyvar_lower_bound(
    union: Option<&mut dyn FnMut(InternalType, &[InternalType]) -> Vec<InternalType>>,
    env: &mut T,
    var: tvid::T,
    ty: InternalType,
) {
    let tvconstraints = get_tyvar_constraints_exn(env, var);
    let lower_bounds = match union {
        None => {
            let mut lower_bounds = tvconstraints.lower_bounds.clone();
            lower_bounds.insert(ty);
            lower_bounds
        }
        Some(union) => union(
            ty,
            &tvconstraints
                .lower_bounds
                .iter()
                .cloned()
                .collect::<Vec<InternalType>>(),
        )
        .into_iter()
        .collect(),
    };
    set_tyvar_constraints(
        env,
        var,
        TyvarConstraints {
            lower_bounds,
            ..tvconstraints
        },
    );
}

/// Remove type variable `upper_var` from the upper bounds on `var`, if it exists
pub fn remove_tyvar_upper_bound(env: &mut T, var: tvid::T, upper_var: tvid::T) {
    match get_tyvar_constraints_opt(env, var) {
        None => {}
        Some(tvconstraints) => {
            // `ITySet.filter`, which keeps the tree OCaml keeps.
            let upper_bounds = ity_set::filter(
                |ty| {
                    // The OCaml drops the environment that the expansion
                    // returns and goes on with `env`: expand in a copy (only
                    // a type variable is expanded, so only it needs one).
                    !internal_type::is_var_v(&expand_in_copy(env, ty), upper_var)
                },
                &tvconstraints.upper_bounds,
            );
            let tvconstraints = TyvarConstraints {
                upper_bounds,
                ..tvconstraints.clone()
            };
            set_tyvar_constraints(env, var, tvconstraints)
        }
    }
}

/// `expand_internal_type` in a copy of `env`, which is dropped: the copy is
/// made only for a type variable, the one type that the expansion changes.
fn expand_in_copy(env: &T, ty: &InternalType) -> InternalType {
    match ty {
        InternalType::LoclType(lty) if matches!(get_node(lty), Ty_::Tvar(_)) => {
            expand_internal_type(&mut env.clone(), ty.clone())
        }
        _ => ty.clone(),
    }
}

/// Remove type variable `lower_var` from the lower bounds on `var`, if it exists
pub fn remove_tyvar_lower_bound(env: &mut T, var: tvid::T, lower_var: tvid::T) {
    match get_tyvar_constraints_opt(env, var) {
        None => {}
        Some(tvconstraints) => {
            // `ITySet.filter`, which keeps the tree OCaml keeps.
            let lower_bounds = ity_set::filter(
                |ty| {
                    // As in `remove_tyvar_upper_bound`: expand in a copy.
                    !internal_type::is_var_v(&expand_in_copy(env, ty), lower_var)
                },
                &tvconstraints.lower_bounds,
            );
            let tvconstraints = TyvarConstraints {
                lower_bounds,
                ..tvconstraints.clone()
            };
            set_tyvar_constraints(env, var, tvconstraints)
        }
    }
}

/// Get the list of all type variables in the environment
pub fn get_vars(env: &T) -> Vec<tvid::T> {
    // `Tvid.Map.keys` is `fold (fun k _ acc -> k :: acc) m []`: the largest
    // variable comes first.
    env.tvenv.keys().rev().copied().collect()
}

/// Get the list of all unsolved type variables in the environment
pub fn get_unsolved_vars(env: &T) -> Vec<tvid::T> {
    // As in `get_vars`, the largest variable comes first.
    let mut vars = vec![];
    for (v, tvinfo) in env.tvenv.iter().rev() {
        match &tvinfo.solving_info {
            SolvingInfo::TVIConstraints(_) => vars.push(*v),
            SolvingInfo::TVIType(_) => {}
        }
    }
    vars
}

pub mod size {
    use super::ConstraintType;
    use super::ConstraintType_;
    use super::ITySet;
    use super::InternalType;
    use super::PosId;
    use super::SMap;
    use super::SolvingInfo;
    use super::T;
    use super::Ty;
    use super::TyvarConstraints;
    use super::TyvarInfo;
    use super::deref_constraint_type;

    /// This can be useful to debug type which blow up in size
    pub fn ty_size(env: &T, ty: &Ty) -> isize {
        use crate::type_visitor::LoclTypeVisitor;
        use crate::type_visitor::locl_type_visitor_on_type;
        struct TySizeVisitor<'e> {
            env: &'e T,
        }
        impl LoclTypeVisitor<isize> for TySizeVisitor<'_> {
            fn on_type(&mut self, acc: isize, ty: &Ty) -> isize {
                1 + locl_type_visitor_on_type(self, acc, ty)
            }

            fn on_tvar(&mut self, acc: isize, r: &crate::typing_reason::T, v: isize) -> isize {
                // `let (_, ty) = expand_var env r v`: the environment it
                // returns (with shortened paths) is dropped.
                let ty = match super::expand_var_shared_ref(self.env, r, v) {
                    Ok(ty) => ty,
                    Err(pending) => {
                        super::expand_var_pending(&mut self.env.clone(), r.clone(), v, pending)
                    }
                };
                match crate::typing_defs::get_node(&ty) {
                    crate::typing_defs::Ty_::Tvar(v_) if *v_ == v => acc,
                    _ => locl_type_visitor_on_type(self, acc, &ty),
                }
            }
        }
        TySizeVisitor { env }.on_type(0, ty)
    }

    fn constraint_type_size(env: &T, ty: &ConstraintType) -> isize {
        let type_size_list = |env: &T, l: &[Ty]| {
            let mut size = 0;
            for ty in l {
                size = size + ty_size(env, ty);
            }
            size
        };
        let type_size_option = |f: &dyn Fn(&Ty) -> isize, opt: &Option<Ty>| match opt {
            None => 0,
            Some(ty) => f(ty),
        };
        match deref_constraint_type(ty) {
            (_, ConstraintType_::Tdestructure(d)) => {
                1 + type_size_list(env, &d.required)
                    + type_size_list(env, &d.optional)
                    + type_size_option(&|ty| ty_size(env, ty), &d.variadic)
            }
            (_, ConstraintType_::ThasMember(hm)) => 1 + ty_size(env, &hm.type_),
            (_, ConstraintType_::ThasTypeMember(htm)) => {
                1 + ty_size(env, &htm.lower) + ty_size(env, &htm.upper)
            }
            (_, ConstraintType_::TcanIndex(ci)) => {
                1 + ty_size(env, &ci.val) + ty_size(env, &ci.key)
            }
            (_, ConstraintType_::TcanIndexAssign(cia)) => {
                1 + ty_size(env, &cia.key) + ty_size(env, &cia.write) + ty_size(env, &cia.val)
            }
            (_, ConstraintType_::TcanTraverse(ct)) => {
                1 + ty_size(env, &ct.val) + type_size_option(&|ty| ty_size(env, ty), &ct.key)
            }
            (
                _,
                ConstraintType_::TtypeSwitch {
                    predicate: _,
                    ty_true,
                    ty_false,
                },
            ) => 1 + ty_size(env, &ty_true) + ty_size(env, &ty_false),
            (_, ConstraintType_::ThasConst { name: _, ty }) => 1 + ty_size(env, &ty),
        }
    }

    fn internal_type_size(env: &T, ty: &InternalType) -> isize {
        match ty {
            InternalType::LoclType(ty) => ty_size(env, ty),
            InternalType::ConstraintType(ty) => constraint_type_size(env, ty),
        }
    }

    fn internal_type_set_size(env: &T, tys: &ITySet) -> isize {
        let mut size = 0;
        for ty in tys.iter() {
            size = size + internal_type_size(env, ty);
        }
        size
    }

    fn type_constants_size(env: &T, tconsts: &SMap<(PosId, Ty)>) -> isize {
        let mut y = 0;
        for (_, (_id, ty)) in tconsts {
            y = ty_size(env, ty) + y;
        }
        y
    }

    fn solving_info_size(env: &T, solving_info: &SolvingInfo) -> isize {
        match solving_info {
            SolvingInfo::TVIType(ty) => ty_size(env, ty),
            SolvingInfo::TVIConstraints(tvcstr) => {
                let TyvarConstraints {
                    appears_covariantly: _,
                    appears_contravariantly: _,
                    upper_bounds,
                    lower_bounds,
                    type_constants,
                } = tvcstr;
                let ubound_size = internal_type_set_size(env, upper_bounds);
                let lbound_size = internal_type_set_size(env, lower_bounds);
                let tconst_size = type_constants_size(env, type_constants);
                ubound_size + lbound_size + tconst_size
            }
        }
    }

    fn tyvar_info_size(env: &T, tvinfo: &TyvarInfo) -> isize {
        let TyvarInfo {
            tyvar_pos: _,
            solving_info,
            eager_solve_failed: _,
            is_error: _,
            is_shadow: _,
            shadow_local_name: _,
            rank: _,
        } = tvinfo;
        solving_info_size(env, solving_info)
    }

    pub fn inference_env_size(env: &T) -> isize {
        let T {
            tvenv,
            may_have_shadow_locals: _,
            subtype_prop: _,
            tyvars_stack: _,
            tyvar_occurrences: _,
            pos: _,
        } = env;
        let mut y = 0;
        for (_, tvinfo) in tvenv {
            y = tyvar_info_size(env, tvinfo) + y;
        }
        y
    }
}

// The following merging logic is used to gather all the information we have
// on a global type variable from multiple sub-graphs. It simply unions
// all the constraints and does not try to do anything clever like
// keeping the graph transitively closed.

fn merge_constraints(cstr1: TyvarConstraints, cstr2: TyvarConstraints) -> TyvarConstraints {
    let TyvarConstraints {
        lower_bounds: lb1,
        upper_bounds: ub1,
        type_constants: tc1,
        appears_covariantly: cov1,
        appears_contravariantly: contra1,
    } = cstr1;
    let TyvarConstraints {
        lower_bounds: lb2,
        upper_bounds: ub2,
        type_constants: tc2,
        appears_covariantly: cov2,
        appears_contravariantly: contra2,
    } = cstr2;
    TyvarConstraints {
        lower_bounds: ity_set::union(&lb1, &lb2),
        upper_bounds: ity_set::union(&ub1, &ub2),
        appears_covariantly: cov1 || cov2,
        appears_contravariantly: contra1 || contra2,
        // Type constants must already have been made equivalent, so picking any should be fine
        // TODO: that might actually not be true during initial merging, but let's fix that later.
        //
        // `S_map.union` without `~combine`: the binding of the first map wins
        // (`im::OrdMap::union` keeps the binding of the larger map).
        type_constants: tc1.union_with(tc2, |a, _| a),
    }
}

fn solving_info_as_constraints(sinfo: SolvingInfo) -> TyvarConstraints {
    match sinfo {
        SolvingInfo::TVIConstraints(c) => c,
        SolvingInfo::TVIType(ty) => TyvarConstraints {
            lower_bounds: singleton_ity_set(InternalType::LoclType(ty.clone())),
            upper_bounds: singleton_ity_set(InternalType::LoclType(ty)),
            appears_covariantly: false,
            appears_contravariantly: false,
            type_constants: SMap::new(),
        },
    }
}

fn merge_solving_infos(sinfo1: SolvingInfo, sinfo2: SolvingInfo) -> SolvingInfo {
    let cstr1 = solving_info_as_constraints(sinfo1);
    let cstr2 = solving_info_as_constraints(sinfo2);
    let cstr = merge_constraints(cstr1, cstr2);
    SolvingInfo::TVIConstraints(cstr)
}

fn merge_tyvar_infos(tvinfo1: TyvarInfo, tvinfo2: TyvarInfo) -> TyvarInfo {
    let TyvarInfo {
        tyvar_pos: pos1,
        eager_solve_failed: esf1,
        solving_info: sinfo1,
        is_error: is_error1,
        is_shadow: is_shadow1,
        shadow_local_name: sln1,
        rank: rank1,
    } = tvinfo1;
    let TyvarInfo {
        tyvar_pos: pos2,
        eager_solve_failed: esf2,
        solving_info: sinfo2,
        is_error: is_error2,
        is_shadow: is_shadow2,
        shadow_local_name: sln2,
        rank: rank2,
    } = tvinfo2;
    TyvarInfo {
        tyvar_pos: if crate::pos::equal_none(&pos1) { pos2 } else { pos1 },
        eager_solve_failed: esf1 || esf2,
        solving_info: merge_solving_infos(sinfo1, sinfo2),
        is_error: is_error1 || is_error2,
        is_shadow: is_shadow1 || is_shadow2,
        shadow_local_name: sln1.or(sln2),
        rank: std::cmp::min(rank1, rank2),
    }
}

/// Merge type variables by transferring all constraints from the first to the second
/// and binding the first to the second.
/// Does not perform anything clever, especially does not perform any transitive closure.
/// Will throw an exception of the type variables are already solved.
pub fn merge_tyvars(env: &mut T, v1: tvid::T, v2: tvid::T) {
    if v1 == v2 {
    } else {
        // `Tvid.Map.find`
        let tvinfo1 = match env.tvenv.get(&v1) {
            Some(tvinfo) => tvinfo.clone(),
            None => panic!("Not_found"),
        };
        let tvinfo2 = match env.tvenv.get(&v2) {
            Some(tvinfo) => tvinfo.clone(),
            None => panic!("Not_found"),
        };
        let tvinfo = merge_tyvar_infos(tvinfo1, tvinfo2);
        set_tyvar_info(env, v2, tvinfo);
        add(env, None, v1, mk((typing_reason::none(), Ty_::Tvar(v2))));
        remove_tyvar_lower_bound(env, v2, v2);
        remove_tyvar_upper_bound(env, v2, v2);
    }
}

/// Only merge the tvenv parts. Resolve conflicts stupidly by taking the first mapping of the two.
pub fn simple_merge(env1: &mut T, env2: &T) {
    let T {
        tvenv: tvenv2,
        may_have_shadow_locals: may_have_shadow_locals2,
        subtype_prop: _,
        tyvars_stack: _,
        tyvar_occurrences: _,
        pos: _,
    } = env2;
    env1.may_have_shadow_locals |= *may_have_shadow_locals2;
    // `Tvid.Map.union ~combine`: the variables of `env1` alone are kept as
    // they are, the others come from `env2` or from both.
    //
    // The OCaml (typing_inference_env.ml, `simple_merge`) notes that this is a
    // hot path (every function and lambda visited by each TAST check) and
    // relies on `union` keeping shared subtrees and on `phys_equal` entries.
    // Here the same idea is applied to the persistent `pmap`: no work for the
    // same map or an empty side, and otherwise a walk of only the entries
    // that differ between the two maps (`simple_merge_tvenv`), updating
    // `env1` in place. The result is the OCaml's union.
    let tvenv1 = &mut env1.tvenv;
    // Both maps often descend from the same one: nothing to do if they are
    // the same map, and nothing to do for a variable whose information is
    // the same object in both (merging it with itself gives it back).
    if tvenv1.ptr_eq(tvenv2) {
        return;
    }
    // Merging into no variables at all gives the variables of `env2` (this
    // is what restoring a saved environment into a fresh one does).
    if tvenv1.is_empty() {
        *tvenv1 = tvenv2.clone();
        return;
    }
    if tvenv2.is_empty() {
        return;
    }
    // (`tast_env` remembers the merges it makes; a second cache here, keyed
    // by the two maps, cost more in dropping its results than it saved.)
    simple_merge_tvenv(tvenv1, tvenv2);
}

fn simple_merge_tvenv(tvenv1: &mut Tvenv, tvenv2: &Tvenv) {
    // The merge of the information of a variable that both maps have, or
    // `None` when it is the information `env1` already has (equal to
    // `tvinfo1`, field by field): then there is nothing to update.
    fn merge_tvinfo(tvinfo1: &TyvarInfo, tvinfo2: &TyvarInfo) -> Option<TyvarInfo> {
        let TyvarInfo {
            tyvar_pos: tyvar_pos1,
            eager_solve_failed: eager_solve_failed1,
            solving_info: sinfo1,
            is_error: is_error1,
            is_shadow: is_shadow1,
            shadow_local_name: sln1,
            rank: rank1,
        } = tvinfo1;
        let TyvarInfo {
            tyvar_pos: tyvar_pos2,
            eager_solve_failed: eager_solve_failed2,
            solving_info: sinfo2,
            is_error: is_error2,
            is_shadow: is_shadow2,
            shadow_local_name: sln2,
            rank: rank2,
        } = tvinfo2;
        let same_as_tvinfo1 = (!crate::pos::equal_none(tyvar_pos1)
            || crate::pos::equal_none(tyvar_pos2))
            && (*eager_solve_failed1 || !*eager_solve_failed2)
            && !matches!(
                (sinfo1, sinfo2),
                (SolvingInfo::TVIConstraints(_), SolvingInfo::TVIType(_))
            )
            && (*is_error1 || !*is_error2)
            && (*is_shadow1 || !*is_shadow2)
            && (sln1.is_some() || sln2.is_none())
            && *rank1 <= *rank2;
        if same_as_tvinfo1 {
            return None;
        }
        Some(TyvarInfo {
            tyvar_pos: if crate::pos::equal_none(tyvar_pos1) {
                tyvar_pos2.clone()
            } else {
                tyvar_pos1.clone()
            },
            eager_solve_failed: *eager_solve_failed1 || *eager_solve_failed2,
            solving_info: match (sinfo1, sinfo2) {
                (SolvingInfo::TVIConstraints(_), SolvingInfo::TVIType(ty))
                | (SolvingInfo::TVIType(ty), SolvingInfo::TVIConstraints(_)) => {
                    SolvingInfo::TVIType(ty.clone())
                }
                (SolvingInfo::TVIConstraints(_), SolvingInfo::TVIConstraints(_))
                | (SolvingInfo::TVIType(_), SolvingInfo::TVIType(_)) => sinfo1.clone(),
            },
            is_error: *is_error1 || *is_error2,
            is_shadow: *is_shadow1 || *is_shadow2,
            shadow_local_name: sln1.clone().or_else(|| sln2.clone()),
            rank: std::cmp::min(*rank1, *rank2),
        })
    }
    // The updates of `env1`. Only the variables whose information differs
    // between the two maps (is not the same object) can change: the walk
    // skips what the maps share, which is most of them when one environment
    // descends from the other.
    let mut updates: Vec<crate::pmap::Entry<tvid::T, TyvarInfo>> = vec![];
    crate::pmap::for_each_difference_int(tvenv1, tvenv2, |entry2, tvinfo1| match tvinfo1 {
        None => updates.push(Rc::clone(entry2)),
        Some(tvinfo1) => {
            if let Some(tvinfo) = merge_tvinfo(tvinfo1, &entry2.1) {
                updates.push(Rc::new((entry2.0, tvinfo)))
            }
        }
    });
    for entry in updates {
        tvenv1.insert_entry(entry);
    }
}

/// The type-variable map of an environment (the only part [`simple_merge`]
/// reads or writes), as a cheap handle: `tast_env` keeps the merges it has
/// made, to make each one once (no OCaml counterpart: the TAST checks restore
/// the same lambda environments 4-6 times per definition, and `tast_env`
/// memoises `simple_merge` by the identity of the two maps).
#[derive(Clone)]
pub struct TvenvHandle(Tvenv);

pub fn tvenv_handle(env: &T) -> TvenvHandle {
    TvenvHandle(env.tvenv.clone())
}

/// The same map (one is a copy of the other with no change since).
pub fn tvenv_handle_is(env: &T, h: &TvenvHandle) -> bool {
    env.tvenv.ptr_eq(&h.0)
}

pub fn set_tvenv_handle(env: &mut T, h: &TvenvHandle) {
    // The map may come from another environment.
    env.may_have_shadow_locals = true;
    env.tvenv = h.0.clone()
}

/// The address of the root of the map of `env` (an identity while a handle
/// of the map is kept: see [`tvenv_handle_is`]).
pub fn tvenv_addr(env: &T) -> usize {
    env.tvenv.root_addr()
}

/// Gets the part of the subtype proposition that should not be added to the
/// constraint graph (e.g. because it contains disjunctions).
pub fn get_nongraph_subtype_prop(env: &T) -> tl::SubtypeProp {
    (*env.subtype_prop).clone()
}

pub fn is_alias_for_another_var(env: &T, v: tvid::T) -> bool {
    match get_solving_info_opt(env, v) {
        Some(SolvingInfo::TVIType(ty)) => match get_node(ty) {
            Ty_::Tvar(v_) if !(v == *v_) => true,
            _ => false,
        },
        _ => false,
    }
}

/// Some ty vars in the map will carry no additional information, e.g.
/// some ty vars belong to methods declared in parent classes, even
/// when these methods are not used in the subclass itself. In those cases,
/// the ty var will be registered, but the accompagnying ty var info
/// will contain nothing useful. It will in essence be an identity element
/// under the merge operation.
fn solving_info_carries_information(solving_info: &SolvingInfo) -> bool {
    match solving_info {
        SolvingInfo::TVIType(_) => true,
        SolvingInfo::TVIConstraints(tvcstr) => {
            let TyvarConstraints {
                appears_covariantly,
                appears_contravariantly,
                upper_bounds,
                lower_bounds,
                type_constants,
            } = tvcstr;
            *appears_contravariantly
                || *appears_covariantly
                || !upper_bounds.is_empty()
                || !lower_bounds.is_empty()
                || !type_constants.is_empty()
        }
    }
}

fn tyvar_info_carries_information(tvinfo: &TyvarInfo) -> bool {
    let TyvarInfo {
        tyvar_pos: _,
        solving_info,
        eager_solve_failed: _,
        is_error: _,
        is_shadow: _,
        shadow_local_name: _,
        rank,
    } = tvinfo;
    solving_info_carries_information(solving_info) || *rank > 0
}

/// Remove variables containing no information.
pub fn compress(env: &mut T) {
    let dropped: Vec<tvid::T> = env
        .tvenv
        .iter()
        .filter(|(_k, tvinfo)| !tyvar_info_carries_information(tvinfo))
        .map(|(k, _)| *k)
        .collect();
    for k in dropped {
        env.tvenv.remove_key(&k);
    }
}

fn remove_var_from_bounds(
    env: &mut T,
    v: tvid::T,
    search_in_upper_bounds_of: &TvidSet,
    search_in_lower_bounds_of: &TvidSet,
) {
    for &v_ in search_in_upper_bounds_of {
        match get_tyvar_upper_bounds_opt(env, v_) {
            None => {}
            Some(bounds) => {
                // `ITySet.filter`, which keeps the tree OCaml keeps.
                let bounds = ity_set::filter(|ty| internal_type::is_not_var_v(ty, v), &bounds);
                set_tyvar_upper_bounds(env, v_, bounds)
            }
        }
    }
    for &v_ in search_in_lower_bounds_of {
        match get_tyvar_lower_bounds_opt(env, v_) {
            None => {}
            Some(bounds) => {
                // `ITySet.filter`, which keeps the tree OCaml keeps.
                let bounds = ity_set::filter(|ty| internal_type::is_not_var_v(ty, v), &bounds);
                set_tyvar_lower_bounds(env, v_, bounds)
            }
        }
    }
}

fn remove_var_from_tyvars_stack(
    tyvars_stack: &crate::plist::List<(Pos, crate::plist::List<tvid::T>)>,
    var: tvid::T,
) -> crate::plist::List<(Pos, crate::plist::List<tvid::T>)> {
    tyvars_stack
        .iter()
        .map(|(p, vars)| {
            (
                p.clone(),
                vars.iter().copied().filter(|v| !(var == *v)).collect(),
            )
        })
        .collect()
}

fn replace_var_by_ty_in_prop(prop: tl::SubtypeProp, v: tvid::T, ty: &Ty) -> tl::SubtypeProp {
    fn replace(prop: tl::SubtypeProp, v: tvid::T, ty: &Ty) -> tl::SubtypeProp {
        match prop {
            tl::SubtypeProp::IsSubtype(cd, ty1, ty2) => {
                let ty1 = if internal_type::is_var_v(&ty1, v) {
                    InternalType::LoclType(ty.clone())
                } else {
                    ty1
                };
                let ty2 = if internal_type::is_var_v(&ty2, v) {
                    InternalType::LoclType(ty.clone())
                } else {
                    ty2
                };
                tl::SubtypeProp::IsSubtype(cd, ty1, ty2)
            }
            tl::SubtypeProp::Disj(f, props) => {
                let props = props.into_iter().map(|prop| replace(prop, v, ty)).collect();
                tl::SubtypeProp::Disj(f, props)
            }
            tl::SubtypeProp::Conj(props) => {
                let props = props.into_iter().map(|prop| replace(prop, v, ty)).collect();
                tl::SubtypeProp::Conj(props)
            }
            tl::SubtypeProp::AmbiguousShapeSplat(_) => prop,
        }
    }
    replace(prop, v, ty)
}

/// Remove solved variable from environment by replacing it by its binding.
pub fn remove_var(
    env: &mut T,
    var: tvid::T,
    search_in_upper_bounds_of: &TvidSet,
    search_in_lower_bounds_of: &TvidSet,
) {
    remove_var_from_bounds(
        env,
        var,
        search_in_upper_bounds_of,
        search_in_lower_bounds_of,
    );
    let ty = expand_var(env, typing_reason::none(), var);
    occ::remove_var(&mut env.tyvar_occurrences, var);
    env.tvenv.remove_key(&var);
    env.tyvars_stack = remove_var_from_tyvars_stack(&env.tyvars_stack, var);
    let subtype_prop = Rc::make_mut(&mut env.subtype_prop);
    let old = std::mem::replace(subtype_prop, tl::valid());
    *subtype_prop = replace_var_by_ty_in_prop(old, var, &ty);
}

fn force_lazy_values_tyvar_constraints(cstrs: TyvarConstraints) -> TyvarConstraints {
    let TyvarConstraints {
        appears_covariantly,
        appears_contravariantly,
        lower_bounds,
        upper_bounds,
        type_constants,
    } = cstrs;
    TyvarConstraints {
        appears_covariantly,
        appears_contravariantly,
        lower_bounds: ity_set::force_lazy_values(lower_bounds),
        upper_bounds: ity_set::force_lazy_values(upper_bounds),
        type_constants: type_constants
            .into_iter()
            .map(|(name, (p, ty))| (name, (p, type_force_lazy_values::locl_ty(ty))))
            .collect(),
    }
}

fn force_lazy_values_solving_info(solving_info: SolvingInfo) -> SolvingInfo {
    match solving_info {
        SolvingInfo::TVIType(ty) => SolvingInfo::TVIType(type_force_lazy_values::locl_ty(ty)),
        SolvingInfo::TVIConstraints(cstrs) => {
            SolvingInfo::TVIConstraints(force_lazy_values_tyvar_constraints(cstrs))
        }
    }
}

fn force_lazy_values_tyvar_info(tyvar_info: TyvarInfo) -> TyvarInfo {
    let TyvarInfo {
        tyvar_pos,
        eager_solve_failed,
        solving_info,
        is_error,
        is_shadow,
        shadow_local_name,
        rank,
    } = tyvar_info;
    TyvarInfo {
        tyvar_pos,
        eager_solve_failed,
        solving_info: force_lazy_values_solving_info(solving_info),
        is_error,
        is_shadow,
        shadow_local_name,
        rank,
    }
}

fn force_lazy_values_tvenv(tvenv: Tvenv) -> Tvenv {
    let mut res = Tvenv::new();
    for (v, tyvar_info) in &tvenv {
        res.insert(*v, force_lazy_values_tyvar_info(tyvar_info.clone()));
    }
    res
}

pub fn force_lazy_values(env: &mut T) {
    env.tvenv = force_lazy_values_tvenv(std::mem::take(&mut env.tvenv));
    let subtype_prop = Rc::make_mut(&mut env.subtype_prop);
    let old = std::mem::replace(subtype_prop, tl::valid());
    *subtype_prop = tl::force_lazy_values(old);
}

pub fn is_error(env: &T, tvid: tvid::T) -> bool {
    match env.tvenv.get(&tvid) {
        None => false,
        Some(TyvarInfo { is_error, .. }) => *is_error,
    }
}

pub fn get_rank(env: &T, tvid: tvid::T) -> isize {
    match env.tvenv.get(&tvid) {
        None => 0,
        Some(TyvarInfo { rank, .. }) => *rank,
    }
}

pub fn get_pos(env: &T) -> Option<Pos> {
    env.pos.clone()
}

/// [`get_pos`] without the copy.
pub fn get_pos_ref(env: &T) -> &Option<Pos> {
    &env.pos
}

/// Propagate the position for better error reporting.
/// Returns a `restore_pos` function.
/// Call the `restore_pos` function at the end
/// of the scope in cases where you're not throwing
/// the `env` away.
pub fn set_pos(env: &mut T, pos: Option<Pos>) -> impl Fn(&mut T) + use<> {
    let old_pos = env.pos.clone();
    let restore = move |env: &mut T| env.pos = old_pos.clone();
    env.pos = pos;
    restore
}

#[cfg(test)]
mod tests {
    use std::panic::AssertUnwindSafe;
    use std::panic::catch_unwind;

    use super::*;

    fn tvar(v: tvid::T) -> Ty {
        mk((typing_reason::none(), Ty_::Tvar(v)))
    }

    /// A type that is not a type variable.
    fn generic(name: &str) -> Ty {
        mk((typing_reason::none(), Ty_::Tgeneric(name.to_string())))
    }

    fn option(ty: Ty) -> Ty {
        mk((typing_reason::none(), Ty_::Toption(ty)))
    }

    fn locl(ty: Ty) -> InternalType {
        InternalType::LoclType(ty)
    }

    /// The elements of a set of bounds, which must all be `LoclType`s.
    fn elements(tys: &ITySet) -> Vec<Ty> {
        tys.iter()
            .map(|ty| match ty {
                InternalType::LoclType(ty) => ty.clone(),
                InternalType::ConstraintType(_) => panic!("unexpected constraint type"),
            })
            .collect()
    }

    fn unlocl(tys: &[InternalType]) -> Vec<Ty> {
        tys.iter()
            .map(|ty| match ty {
                InternalType::LoclType(ty) => ty.clone(),
                InternalType::ConstraintType(_) => panic!("unexpected constraint type"),
            })
            .collect()
    }

    fn vars(vs: &[tvid::T]) -> TvidSet {
        vs.iter().copied().collect()
    }

    fn pos() -> Pos {
        Pos::NONE
    }

    /// An environment with `n` invariant type variables, and their ids.
    fn env_with_vars(n: usize) -> (T, tvid::Provider, Vec<tvid::T>) {
        let mut env = empty_inference_env();
        let provider = tvid::make_provider();
        let mut vs = vec![];
        for _ in 0..n {
            match get_node(&fresh_type_invariant(&mut env, &provider, pos())) {
                Ty_::Tvar(v) => vs.push(*v),
                _ => panic!("fresh_type did not return a type variable"),
            }
        }
        (env, provider, vs)
    }

    #[test]
    fn fresh_types_are_unsolved_and_record_variance() {
        let mut env = empty_inference_env();
        let provider = tvid::make_provider();
        let fresh = |variance, env: &mut T, provider: &tvid::Provider| match get_node(&fresh_type(
            variance,
            env,
            provider,
            pos(),
        )) {
            Ty_::Tvar(v) => *v,
            _ => panic!("fresh_type did not return a type variable"),
        };
        let none = fresh(None, &mut env, &provider);
        let co = fresh(Some(ast_defs::Variance::Covariant), &mut env, &provider);
        let contra = fresh(Some(ast_defs::Variance::Contravariant), &mut env, &provider);
        let inv = fresh(Some(ast_defs::Variance::Invariant), &mut env, &provider);
        for v in [none, co, contra, inv] {
            assert!(!tyvar_is_solved(&env, v));
            assert!(get_direct_binding(&env, v).is_none());
            assert!(!is_error(&env, v));
            assert!(!is_shadow(&env, v));
            assert_eq!(get_rank(&env, v), 0);
            assert!(elements(&get_tyvar_lower_bounds(&env, v)).is_empty());
            assert!(elements(&get_tyvar_upper_bounds(&env, v)).is_empty());
        }
        let appears = |v| {
            (
                get_tyvar_appears_covariantly(&env, v),
                get_tyvar_appears_contravariantly(&env, v),
                get_tyvar_appears_invariantly(&env, v),
            )
        };
        assert_eq!(appears(none), (false, false, false));
        assert_eq!(appears(co), (true, false, false));
        assert_eq!(appears(contra), (false, true, false));
        assert_eq!(appears(inv), (true, true, true));
        // The largest variable comes first.
        assert_eq!(get_vars(&env), vec![inv, contra, co, none]);
        assert_eq!(get_unsolved_vars(&env), vec![inv, contra, co, none]);
    }

    #[test]
    fn fresh_type_with_rank_and_error() {
        let mut env = empty_inference_env();
        let provider = tvid::make_provider();
        let ty = fresh_type_invariant_with_rank(&mut env, &provider, 3, pos());
        let &Ty_::Tvar(v) = get_node(&ty) else {
            panic!()
        };
        assert_eq!(get_rank(&env, v), 3);
        assert!(get_tyvar_appears_invariantly(&env, v));
        let ty = fresh_type_reason(None, Some(true), &mut env, &provider, pos(), |_| {
            typing_reason::none()
        });
        let &Ty_::Tvar(v) = get_node(&ty) else {
            panic!()
        };
        assert!(is_error(&env, v));
        assert!(!is_error(&env, v + 100));
        assert_eq!(get_rank(&env, v + 100), 0);
    }

    #[test]
    fn tyvars_stack() {
        let mut env = empty_inference_env();
        let provider = tvid::make_provider();
        let fresh = |env: &mut T, provider: &tvid::Provider| match get_node(&fresh_type_invariant(
            env,
            provider,
            pos(),
        )) {
            Ty_::Tvar(v) => *v,
            _ => panic!(),
        };
        // No frame: the variable is not recorded anywhere.
        let v0 = fresh(&mut env, &provider);
        assert!(get_current_tyvars(&env).is_empty());
        assert!(get_current_pos_from_tyvar_stack(&env).is_none());
        open_tyvars(&mut env, pos());
        assert!(get_current_pos_from_tyvar_stack(&env).is_some());
        let v1 = fresh(&mut env, &provider);
        let v2 = fresh(&mut env, &provider);
        // The most recent variable comes first.
        assert_eq!(get_current_tyvars(&env), vec![v2, v1]);
        open_tyvars(&mut env, pos());
        let v3 = fresh(&mut env, &provider);
        assert_eq!(get_current_tyvars(&env), vec![v3]);
        close_tyvars(&mut env);
        assert_eq!(get_current_tyvars(&env), vec![v2, v1]);
        close_tyvars(&mut env);
        assert!(get_current_tyvars(&env).is_empty());
        assert_eq!(get_vars(&env), vec![v3, v2, v1, v0]);
    }

    #[test]
    fn close_tyvars_on_empty_stack_raises() {
        let mut env = empty_inference_env();
        let result = catch_unwind(AssertUnwindSafe(|| close_tyvars(&mut env)));
        let payload = result.unwrap_err();
        assert_eq!(
            payload.downcast_ref::<InconsistentTypeVarState>(),
            Some(&InconsistentTypeVarState(
                "close_tyvars: empty stack".to_string()
            ))
        );
    }

    #[test]
    fn solutions() {
        let (mut env, _, vs) = env_with_vars(2);
        let (v1, v2) = (vs[0], vs[1]);
        add(&mut env, None, v1, generic("T"));
        assert!(tyvar_is_solved(&env, v1));
        assert!(!tyvar_is_solved(&env, v2));
        assert_eq!(get_direct_binding(&env, v1), Some(generic("T")));
        assert_eq!(get_direct_binding(&env, v2), None);
        assert_eq!(get_unsolved_vars(&env), vec![v2]);
        assert_eq!(get_vars(&env), vec![v2, v1]);
        // The bounds of a solved variable are its solution.
        assert_eq!(
            elements(&get_tyvar_lower_bounds(&env, v1)),
            vec![generic("T")]
        );
        assert_eq!(
            elements(&get_tyvar_upper_bounds(&env, v1)),
            vec![generic("T")]
        );
        // ... and it has no constraints any more.
        assert!(!get_tyvar_appears_covariantly(&env, v1));
        assert!(!get_tyvar_appears_contravariantly(&env, v1));
        // Setting the bounds of a solved variable does nothing.
        set_tyvar_upper_bounds(&mut env, v1, singleton_ity_set(locl(generic("U"))));
        assert_eq!(get_direct_binding(&env, v1), Some(generic("T")));
        // Binding a variable that the environment does not know creates it.
        bind(&mut env, None, v2 + 10, generic("U"));
        assert!(tyvar_is_solved(&env, v2 + 10));
        assert_eq!(get_rank(&env, v2 + 10), 0);
    }

    #[test]
    fn expansion_of_solved_and_unsolved_variables() {
        let (mut env, _, vs) = env_with_vars(2);
        let (v1, v2) = (vs[0], vs[1]);
        add(&mut env, None, v1, generic("T"));
        assert_eq!(expand_type(&mut env, tvar(v1)), generic("T"));
        assert_eq!(expand_type(&mut env, tvar(v2)), tvar(v2));
        // Not a variable: unchanged, and only the head is expanded.
        assert_eq!(expand_type(&mut env, generic("U")), generic("U"));
        assert_eq!(expand_type(&mut env, option(tvar(v1))), option(tvar(v1)));
        // A variable that the environment does not know expands to itself.
        assert_eq!(expand_type(&mut env, tvar(v2 + 10)), tvar(v2 + 10));
        assert_eq!(
            unlocl(&[expand_internal_type(&mut env, locl(tvar(v1)))]),
            vec![generic("T")]
        );
    }

    #[test]
    fn expansion_follows_aliases_and_shortens_paths() {
        let (mut env, _, vs) = env_with_vars(4);
        let (v1, v2, v3, v4) = (vs[0], vs[1], vs[2], vs[3]);
        // #1 := #2, #2 := #3, #3 := T
        add(&mut env, None, v1, tvar(v2));
        add(&mut env, None, v2, tvar(v3));
        add(&mut env, None, v3, generic("T"));
        assert!(is_alias_for_another_var(&env, v1));
        assert!(!is_alias_for_another_var(&env, v3));
        assert!(!is_alias_for_another_var(&env, v4));
        let before = env.clone();
        assert_eq!(expand_type(&mut env, tvar(v1)), generic("T"));
        // Both aliases now point at the last variable of the chain.
        assert_eq!(get_direct_binding(&env, v1), Some(tvar(v3)));
        assert_eq!(get_direct_binding(&env, v2), Some(tvar(v3)));
        assert_eq!(get_direct_binding(&env, v3), Some(generic("T")));
        // The copy made before the expansion is untouched.
        assert_eq!(get_direct_binding(&before, v1), Some(tvar(v2)));

        // A chain that ends in an unsolved variable expands to that variable.
        let (mut env, _, vs) = env_with_vars(3);
        let (v1, v2, v3) = (vs[0], vs[1], vs[2]);
        add(&mut env, None, v1, tvar(v2));
        add(&mut env, None, v2, tvar(v3));
        assert_eq!(expand_type(&mut env, tvar(v1)), tvar(v3));
        assert_eq!(get_direct_binding(&env, v1), Some(tvar(v3)));
        assert_eq!(get_direct_binding(&env, v2), Some(tvar(v3)));
        assert!(tyvar_occurs_in_tyvar(&env, v3, v1));
        assert!(tyvar_occurs_in_tyvar(&env, v3, v2));
        assert!(!tyvar_occurs_in_tyvar(&env, v2, v1));
    }

    #[test]
    fn aliasing_cycle_raises() {
        let (mut env, _, vs) = env_with_vars(2);
        let (v1, v2) = (vs[0], vs[1]);
        add(&mut env, None, v1, tvar(v2));
        add(&mut env, None, v2, tvar(v1));
        let result = catch_unwind(AssertUnwindSafe(|| expand_type(&mut env, tvar(v1))));
        let payload = result.unwrap_err();
        assert_eq!(
            payload.downcast_ref::<InconsistentTypeVarState>(),
            Some(&InconsistentTypeVarState(
                "Two type variables are aliasing each other!".to_string()
            ))
        );
    }

    #[test]
    fn occurrences_follow_bindings() {
        let (mut env, _, vs) = env_with_vars(3);
        let (v1, v2, v3) = (vs[0], vs[1], vs[2]);
        add(&mut env, None, v3, generic("T"));
        // #1 := ?#2. #2 is unsolved: it occurs in #1.
        add(&mut env, None, v1, option(tvar(v2)));
        assert!(tyvar_occurs_in_tyvar(&env, v2, v1));
        assert_eq!(get_tyvar_occurrences(&env, v2), vars(&[v1]));
        assert_eq!(get_tyvars_in_tyvar(&env, v1), vars(&[v2]));
        assert!(contains_unsolved_tyvars(&env, v1));
        // Rebinding #1 to a type whose only variable is solved, and holds no
        // unsolved variable itself, clears the occurrence.
        add(&mut env, None, v1, option(tvar(v3)));
        assert!(!tyvar_occurs_in_tyvar(&env, v2, v1));
        assert!(!tyvar_occurs_in_tyvar(&env, v3, v1));
        assert!(!contains_unsolved_tyvars(&env, v1));
        // `bind` does not touch the occurrences.
        bind(&mut env, None, v1, option(tvar(v2)));
        assert!(!tyvar_occurs_in_tyvar(&env, v2, v1));
        make_tyvar_no_more_occur_in_tyvar(&mut env, v2, v1);
        assert!(!tyvar_occurs_in_tyvar(&env, v2, v1));
    }

    #[test]
    fn wrap_ty_in_var_makes_a_solved_variable() {
        let (mut env, provider, vs) = env_with_vars(1);
        let v1 = vs[0];
        let ty = wrap_ty_in_var(&mut env, &provider, typing_reason::none(), option(tvar(v1)));
        let &Ty_::Tvar(v) = get_node(&ty) else {
            panic!()
        };
        assert!(tyvar_is_solved(&env, v));
        assert_eq!(get_direct_binding(&env, v), Some(option(tvar(v1))));
        assert!(tyvar_occurs_in_tyvar(&env, v1, v));
        // It is not recorded in the stack of type variables.
        open_tyvars(&mut env, pos());
        wrap_ty_in_var(&mut env, &provider, typing_reason::none(), generic("T"));
        assert!(get_current_tyvars(&env).is_empty());
    }

    #[test]
    fn bounds() {
        let (mut env, _, vs) = env_with_vars(2);
        let (v1, v2) = (vs[0], vs[1]);
        add_tyvar_upper_bound(None, &mut env, v1, locl(generic("A")));
        add_tyvar_upper_bound(None, &mut env, v1, locl(generic("B")));
        add_tyvar_upper_bound(None, &mut env, v1, locl(generic("A")));
        add_tyvar_lower_bound(None, &mut env, v1, locl(generic("C")));
        let mut expected = vec![generic("A"), generic("B")];
        expected.sort();
        assert_eq!(elements(&get_tyvar_upper_bounds(&env, v1)), expected);
        assert_eq!(
            elements(&get_tyvar_lower_bounds(&env, v1)),
            vec![generic("C")]
        );
        assert!(elements(&get_tyvar_upper_bounds(&env, v2)).is_empty());

        // With an operation, the result of the operation replaces the bounds.
        let mut seen = vec![];
        let mut intersect = |ty: InternalType, tys: &[InternalType]| {
            seen = tys.to_vec();
            vec![ty]
        };
        add_tyvar_upper_bound(Some(&mut intersect), &mut env, v1, locl(generic("D")));
        assert_eq!(unlocl(&seen), expected);
        assert_eq!(
            elements(&get_tyvar_upper_bounds(&env, v1)),
            vec![generic("D")]
        );
        let mut union = |ty: InternalType, tys: &[InternalType]| {
            let mut tys = tys.to_vec();
            tys.push(ty);
            tys
        };
        add_tyvar_lower_bound(Some(&mut union), &mut env, v1, locl(generic("E")));
        assert_eq!(elements(&get_tyvar_lower_bounds(&env, v1)).len(), 2);

        set_tyvar_lower_bounds(&mut env, v1, empty_ity_set());
        assert!(elements(&get_tyvar_lower_bounds(&env, v1)).is_empty());
        set_tyvar_upper_bounds(&mut env, v2, singleton_ity_set(locl(generic("F"))));
        assert_eq!(
            elements(&get_tyvar_upper_bounds(&env, v2)),
            vec![generic("F")]
        );
        // The variance flags are untouched by all of this.
        assert!(get_tyvar_appears_invariantly(&env, v1));
    }

    #[test]
    fn adding_a_bound_to_a_solved_or_unknown_variable_raises() {
        let (mut env, _, vs) = env_with_vars(1);
        let v1 = vs[0];
        add(&mut env, None, v1, generic("T"));
        for (v, msg) in [
            (
                v1,
                format!(
                    "Attempting to get constraints for already solved type variable {}.",
                    crate::typing_log_value::var_as_string(v1)
                ),
            ),
            (
                v1 + 10,
                format!(
                    "Attempting to get constraints for non-existing type variable {}.",
                    crate::typing_log_value::var_as_string(v1 + 10)
                ),
            ),
        ] {
            let mut env = env.clone();
            let result = catch_unwind(AssertUnwindSafe(|| {
                add_tyvar_upper_bound(None, &mut env, v, locl(generic("A")))
            }));
            let payload = result.unwrap_err();
            assert_eq!(
                payload.downcast_ref::<InconsistentTypeVarState>(),
                Some(&InconsistentTypeVarState(msg))
            );
        }
    }

    #[test]
    fn removing_a_variable_from_bounds_looks_through_aliases() {
        let (mut env, _, vs) = env_with_vars(3);
        let (v1, v2, v3) = (vs[0], vs[1], vs[2]);
        // #3 := #2, and #1 has the bounds #3 and A.
        add(&mut env, None, v3, tvar(v2));
        add_tyvar_upper_bound(None, &mut env, v1, locl(tvar(v3)));
        add_tyvar_upper_bound(None, &mut env, v1, locl(generic("A")));
        add_tyvar_lower_bound(None, &mut env, v1, locl(tvar(v3)));
        // #3 is not #1.
        remove_tyvar_upper_bound(&mut env, v1, v1);
        assert_eq!(elements(&get_tyvar_upper_bounds(&env, v1)).len(), 2);
        // #3 expands to #2.
        remove_tyvar_upper_bound(&mut env, v1, v2);
        assert_eq!(
            elements(&get_tyvar_upper_bounds(&env, v1)),
            vec![generic("A")]
        );
        assert_eq!(elements(&get_tyvar_lower_bounds(&env, v1)).len(), 1);
        remove_tyvar_lower_bound(&mut env, v1, v2);
        assert!(elements(&get_tyvar_lower_bounds(&env, v1)).is_empty());
        // Nothing happens for a solved variable.
        remove_tyvar_upper_bound(&mut env, v3, v2);
        assert_eq!(get_direct_binding(&env, v3), Some(tvar(v2)));
    }

    #[test]
    fn eager_solve_fail() {
        let (mut env, _, vs) = env_with_vars(1);
        let v1 = vs[0];
        assert!(!get_tyvar_eager_solve_fail(&env, v1));
        set_tyvar_eager_solve_fail(&mut env, v1);
        assert!(get_tyvar_eager_solve_fail(&env, v1));
        // Unknown variable: nothing happens.
        set_tyvar_eager_solve_fail(&mut env, v1 + 10);
        assert!(!get_tyvar_eager_solve_fail(&env, v1 + 10));
        assert_eq!(get_vars(&env), vec![v1]);
        // The flag survives solving, and the expansion keeps the node.
        add(&mut env, None, v1, generic("T"));
        assert!(get_tyvar_eager_solve_fail(&env, v1));
        assert_eq!(expand_type(&mut env, tvar(v1)), generic("T"));
    }

    #[test]
    fn type_constants() {
        let mut env = empty_inference_env();
        let provider = tvid::make_provider();
        let ty = fresh_type(None, &mut env, &provider, pos());
        let &Ty_::Tvar(v) = get_node(&ty) else {
            panic!()
        };
        let id: PosId = (Pos::NONE, "T".to_string());
        assert!(get_tyvar_type_const(&env, v, &id).is_none());
        assert!(!get_tyvar_appears_covariantly(&env, v));
        set_tyvar_type_const(&mut env, v, id.clone(), generic("A"));
        assert_eq!(
            get_tyvar_type_const(&env, v, &id),
            Some((id.clone(), generic("A")))
        );
        assert_eq!(get_tyvar_type_consts(&env, v).len(), 1);
        // Setting a type constant forces the variable to appear covariantly.
        assert!(get_tyvar_appears_covariantly(&env, v));
        assert!(!get_tyvar_appears_contravariantly(&env, v));
        // Solved: no type constants.
        add(&mut env, None, v, generic("B"));
        assert!(get_tyvar_type_consts(&env, v).is_empty());
    }

    #[test]
    fn merge_tyvars_moves_the_constraints_and_binds() {
        let mut env = empty_inference_env();
        let provider = tvid::make_provider();
        let fresh = |variance, env: &mut T, provider: &tvid::Provider| match get_node(&fresh_type(
            variance,
            env,
            provider,
            pos(),
        )) {
            Ty_::Tvar(v) => *v,
            _ => panic!(),
        };
        let v1 = fresh(Some(ast_defs::Variance::Covariant), &mut env, &provider);
        let v2 = fresh(Some(ast_defs::Variance::Contravariant), &mut env, &provider);
        add_tyvar_upper_bound(None, &mut env, v1, locl(generic("A")));
        add_tyvar_upper_bound(None, &mut env, v1, locl(tvar(v2)));
        add_tyvar_lower_bound(None, &mut env, v2, locl(generic("B")));
        add_tyvar_lower_bound(None, &mut env, v2, locl(tvar(v1)));
        merge_tyvars(&mut env, v1, v2);
        assert_eq!(get_direct_binding(&env, v1), Some(tvar(v2)));
        assert!(!tyvar_is_solved(&env, v2));
        assert!(tyvar_occurs_in_tyvar(&env, v2, v1));
        // The bounds are united, minus the variable itself (#1 is now #2).
        assert_eq!(
            elements(&get_tyvar_upper_bounds(&env, v2)),
            vec![generic("A")]
        );
        assert_eq!(
            elements(&get_tyvar_lower_bounds(&env, v2)),
            vec![generic("B")]
        );
        assert!(get_tyvar_appears_invariantly(&env, v2));
        // Merging a variable with itself does nothing.
        let n = get_vars(&env).len();
        merge_tyvars(&mut env, v2, v2);
        assert_eq!(get_vars(&env).len(), n);
        assert!(!tyvar_is_solved(&env, v2));
    }

    #[test]
    fn simple_merge_prefers_solutions_and_the_first_environment() {
        let (env, _, vs) = env_with_vars(3);
        let (v1, v2, v3) = (vs[0], vs[1], vs[2]);
        let mut env1 = env.clone();
        let mut env2 = env.clone();
        // #1: solved in the second only. #2: solved in both. #3: in neither.
        add(&mut env2, None, v1, generic("A"));
        add(&mut env1, None, v2, generic("B"));
        add(&mut env2, None, v2, generic("C"));
        add_tyvar_upper_bound(None, &mut env1, v3, locl(generic("D")));
        add_tyvar_upper_bound(None, &mut env2, v3, locl(generic("E")));
        set_tyvar_eager_solve_fail(&mut env2, v3);
        // Only in the second.
        bind(&mut env2, None, v3 + 10, generic("F"));
        open_tyvars(&mut env2, pos());
        simple_merge(&mut env1, &env2);
        assert_eq!(get_direct_binding(&env1, v1), Some(generic("A")));
        assert_eq!(get_direct_binding(&env1, v2), Some(generic("B")));
        assert_eq!(
            elements(&get_tyvar_upper_bounds(&env1, v3)),
            vec![generic("D")]
        );
        assert!(get_tyvar_eager_solve_fail(&env1, v3));
        assert_eq!(get_direct_binding(&env1, v3 + 10), Some(generic("F")));
        // Nothing but the variables comes from the second environment.
        assert!(get_current_pos_from_tyvar_stack(&env1).is_none());
    }

    #[test]
    fn compress_drops_variables_without_information() {
        let mut env = empty_inference_env();
        let provider = tvid::make_provider();
        let fresh = |variance, env: &mut T, provider: &tvid::Provider| match get_node(&fresh_type(
            variance,
            env,
            provider,
            pos(),
        )) {
            Ty_::Tvar(v) => *v,
            _ => panic!(),
        };
        let empty = fresh(None, &mut env, &provider);
        let with_variance = fresh(Some(ast_defs::Variance::Covariant), &mut env, &provider);
        let with_bound = fresh(None, &mut env, &provider);
        add_tyvar_lower_bound(None, &mut env, with_bound, locl(generic("A")));
        let solved = fresh(None, &mut env, &provider);
        add(&mut env, None, solved, generic("B"));
        let ty = fresh_type_invariant_with_rank(&mut env, &provider, 1, pos());
        let &Ty_::Tvar(with_rank) = get_node(&ty) else {
            panic!()
        };
        let failed = fresh(None, &mut env, &provider);
        set_tyvar_eager_solve_fail(&mut env, failed);
        compress(&mut env);
        assert_eq!(
            get_vars(&env),
            vec![with_rank, solved, with_bound, with_variance]
        );
        let _ = empty;
    }

    #[test]
    fn remove_var_replaces_the_variable_everywhere() {
        let mut env = empty_inference_env();
        let provider = tvid::make_provider();
        open_tyvars(&mut env, pos());
        let fresh = |env: &mut T, provider: &tvid::Provider| match get_node(&fresh_type_invariant(
            env,
            provider,
            pos(),
        )) {
            Ty_::Tvar(v) => *v,
            _ => panic!(),
        };
        let v1 = fresh(&mut env, &provider);
        let v2 = fresh(&mut env, &provider);
        let v3 = fresh(&mut env, &provider);
        add_tyvar_upper_bound(None, &mut env, v2, locl(tvar(v1)));
        add_tyvar_upper_bound(None, &mut env, v2, locl(generic("A")));
        add_tyvar_lower_bound(None, &mut env, v3, locl(tvar(v1)));
        add_tyvar_upper_bound(None, &mut env, v3, locl(tvar(v1)));
        add(&mut env, None, v1, option(tvar(v2)));
        assert!(tyvar_occurs_in_tyvar(&env, v2, v1));
        // Search the upper bounds of #2 and the lower bounds of #3 only.
        remove_var(&mut env, v1, &vars(&[v2]), &vars(&[v3]));
        assert_eq!(get_vars(&env), vec![v3, v2]);
        assert_eq!(get_current_tyvars(&env), vec![v3, v2]);
        assert_eq!(
            elements(&get_tyvar_upper_bounds(&env, v2)),
            vec![generic("A")]
        );
        assert!(elements(&get_tyvar_lower_bounds(&env, v3)).is_empty());
        assert_eq!(elements(&get_tyvar_upper_bounds(&env, v3)), vec![tvar(v1)]);
        assert!(get_tyvar_occurrences(&env, v2).is_empty());
        assert!(get_tyvars_in_tyvar(&env, v1).is_empty());
    }

    #[test]
    fn shadow_tyvars() {
        let mut env = empty_inference_env();
        let provider = tvid::make_provider();
        open_tyvars(&mut env, pos());
        let ty = fresh_type_invariant(&mut env, &provider, pos());
        let &Ty_::Tvar(v0) = get_node(&ty) else {
            panic!()
        };
        let s1 = fresh_shadow_tyvar(&mut env, &provider, Some("$a".to_string()), pos());
        let s2 = fresh_shadow_tyvar(&mut env, &provider, None, pos());
        let s3 = fresh_shadow_tyvar(&mut env, &provider, Some("$b".to_string()), pos());
        assert!(!is_shadow(&env, v0));
        assert!(is_shadow(&env, s1) && is_shadow(&env, s2) && is_shadow(&env, s3));
        assert!(!is_shadow(&env, s3 + 10));
        assert!(get_tyvar_appears_invariantly(&env, s1));
        // Shadow variables are not recorded in the stack.
        assert_eq!(get_current_tyvars(&env), vec![v0]);
        let mut seen = vec![];
        iter_shadow_tyvars(&env, |v| seen.push(v));
        assert_eq!(seen, vec![s1, s2, s3]);
        let locals: Vec<_> = collect_shadow_locals(&env)
            .into_iter()
            .map(|(name, _, v)| (name, v))
            .collect();
        assert_eq!(locals, vec![("$b".to_string(), s3), ("$a".to_string(), s1)]);
    }

    #[test]
    fn positions() {
        let mut env = empty_inference_env();
        assert!(get_pos(&env).is_none());
        let restore = set_pos(&mut env, Some(pos()));
        assert_eq!(get_pos(&env), Some(pos()));
        let restore_inner = set_pos(&mut env, None);
        assert!(get_pos(&env).is_none());
        restore_inner(&mut env);
        assert_eq!(get_pos(&env), Some(pos()));
        restore(&mut env);
        assert!(get_pos(&env).is_none());
        assert_eq!(get_tyvar_pos(&env, 0), Pos::NONE);
    }

    #[test]
    fn clones_are_independent() {
        let (mut env, provider, vs) = env_with_vars(2);
        let (v1, v2) = (vs[0], vs[1]);
        open_tyvars(&mut env, pos());
        let old = env.clone();
        add(&mut env, None, v1, option(tvar(v2)));
        add_tyvar_upper_bound(None, &mut env, v2, locl(generic("A")));
        let ty = fresh_type_invariant(&mut env, &provider, pos());
        let &Ty_::Tvar(v3) = get_node(&ty) else {
            panic!()
        };
        close_tyvars(&mut env);
        assert!(!tyvar_is_solved(&old, v1));
        assert!(elements(&get_tyvar_upper_bounds(&old, v2)).is_empty());
        assert!(!tyvar_occurs_in_tyvar(&old, v2, v1));
        assert_eq!(get_vars(&old), vec![v2, v1]);
        assert!(get_current_pos_from_tyvar_stack(&old).is_some());
        assert!(get_current_tyvars(&old).is_empty());
        assert!(tyvar_occurs_in_tyvar(&env, v2, v1));
        assert_eq!(get_vars(&env), vec![v3, v2, v1]);
    }
}
