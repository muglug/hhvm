// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/switch_exhaustivity_check.ml`.
//! See `hh/PORTING.md`.
//!
//! The primary guarantee provided with this check:
//!
//!   In the absence of unsoundness, `switch` statements will not throw a
//!   `RuntimeException` because the implicit default case is hit. The check
//!   either proves that all cases are covered exhaustively or insist on a
//!   default.
//!
//! The secondary utility of this check:
//!
//!   It detects cases in switch statements that will not be hit/needed. These
//!   are surfaced as warnings rather than errors and are best effort.

use std::collections::BTreeSet;
use std::sync::LazyLock;

use oxidized::aast;
use oxidized::pos::Pos;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_make_type as make_type;
use crate::typing_reason as reason;
use crate::typing_warning;
use crate::typing_warning::switch_redundancy;
use crate::utils;

/// `default_case` of a TAST.
type DefaultCase = aast::DefaultCase<tast::Ty, tast::SavedEnv>;

pub fn is_nothing(env: &Env, ty: &Ty) -> bool {
    tast_env::is_sub_type(env, ty, &make_type::nothing(reason::none()))
}

pub fn is_null(env: &Env, ty: &Ty) -> bool {
    tast_env::is_sub_type(env, ty, &make_type::null(reason::none()))
}

/// If we have a type `((A & B) | C)` or `(C | (A & B))`,
/// normalise it to `((C | A) & (C | B))`.
///
/// We do this because pessimisation might lead to types such as
/// `(arraykey & dynamic) | E` from which we cannot strip the like type and
/// consequently cannot check for exhaustivity. The transposition gives us
/// `(arraykey | E) & (dynamic | E)` to which the like type stripping can apply
/// and hence we can check for exhaustivity, i.e., by covering all values of
/// `E`.
pub fn transpose_union_of_intersection(env: &Env, ty: Ty) -> Ty {
    fn transpose_disjunct_binary(env: &Env, ty1: Ty, ty2: Ty) -> Ty {
        let mut env = env.clone();
        let ty1 = tast_env::expand_type(&mut env, ty1);
        let (_, ty1) = tast_env::strip_supportdyn(&env, ty1);
        let ty2 = tast_env::expand_type(&mut env.clone(), ty2);
        let (_, ty2) = tast_env::strip_supportdyn(&env, ty2);
        let components = match (get_node(&ty1), get_node(&ty2)) {
            (Ty_::Tintersection(tyl), _) => Some((tyl.clone(), ty2.clone())),
            (_, Ty_::Tintersection(tyl)) => Some((tyl.clone(), ty1.clone())),
            (_, _) => None,
        };
        match components {
            Some((conjuncts, ty)) => {
                let conjuncts = conjuncts
                    .into_iter()
                    .map(|conjunct| {
                        make_type::union(get_reason(&conjunct).clone(), vec![conjunct, ty.clone()])
                    })
                    .collect();
                make_type::intersection(get_reason(&ty).clone(), conjuncts)
            }
            None => make_type::union(get_reason(&ty1).clone(), vec![ty1, ty2]),
        }
    }
    // `let rec transpose_disjunct_list`; `outer` is the type being
    // transposed.
    fn transpose_disjunct_list(env: &Env, outer: &Ty, tyl: &[Ty]) -> Ty {
        match tyl {
            [] => make_type::union(get_reason(outer).clone(), vec![]),
            [ty] => ty.clone(),
            [ty1, ty2] => transpose_disjunct_binary(env, ty1.clone(), ty2.clone()),
            [ty1, tyl @ ..] => {
                let ty2 = transpose_disjunct_list(env, outer, tyl);
                transpose_disjunct_binary(env, ty1.clone(), ty2)
            }
        }
    }
    match get_node(&ty) {
        Ty_::Tunion(tyl) => transpose_disjunct_list(env, &ty, tyl),
        _ => ty,
    }
}

/// Values that are supported in the context of exhaustivity checking.
pub mod value {
    use bstr::BString;
    use oxidized::aast;

    use crate::tast;
    use crate::utils;

    /// `[@@deriving ord]`: the derived `Ord` orders the constructors as they
    /// are declared, then their arguments, as OCaml's does.
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub enum T {
        True,
        False,
        Null,
        /// Only used for duplicate case detection
        Int(String),
        /// Only used for duplicate case detection
        String(BString),
        /// Only used for duplicate case detection
        Id(String),
        EnumConstant(String, String),
        EnumClassLabel(String),
        Tuple(Vec<T>),
    }

    pub fn compare(v1: &T, v2: &T) -> std::cmp::Ordering {
        v1.cmp(v2)
    }

    pub fn show(v: &T) -> String {
        match v {
            T::True => "true".to_string(),
            T::False => "false".to_string(),
            T::Null => "null".to_string(),
            T::Int(str) | T::Id(str) => str.clone(),
            T::String(str) => str.to_string(),
            T::EnumConstant(enum_, label) => format!("{}::{}", utils::strip_ns(enum_), label),
            T::EnumClassLabel(label) => format!("#{}", label),
            T::Tuple(values) => format!(
                "({})",
                values.iter().map(show).collect::<Vec<_>>().join(", ")
            ),
        }
    }

    pub fn of_ast(e: &tast::Expr) -> Option<T> {
        let tast::Expr(_, _, expr) = e;
        match expr {
            aast::Expr_::True => Some(T::True),
            aast::Expr_::False => Some(T::False),
            aast::Expr_::Null => Some(T::Null),
            aast::Expr_::Int(str) => Some(T::Int(str.clone())),
            aast::Expr_::String(str) => Some(T::String(str.clone())),
            aast::Expr_::Id(id) => Some(T::Id(id.1.clone())),
            aast::Expr_::ClassConst(cc) => match &**cc {
                (aast::ClassId(_, _, aast::ClassId_::CI(enum_id)), (_, label)) => {
                    // Don't worry if the class constant is not an enum, we'll use this as the
                    // second operand to set diference and the first operand only.
                    Some(T::EnumConstant(enum_id.1.clone(), label.clone()))
                }
                _ => None,
            },
            aast::Expr_::EnumClassLabel(ecl) => {
                let (_, label) = &**ecl;
                Some(T::EnumClassLabel(label.clone()))
            }
            aast::Expr_::Tuple(exprs) => {
                // `List.map ~f:of_ast exprs |> Option.all`
                let vals: Vec<Option<T>> = exprs.iter().map(of_ast).collect();
                let vals: Option<Vec<T>> = vals.into_iter().collect();
                Some(T::Tuple(vals?))
            }
            _ => None,
        }
    }
}

pub mod value_with_pos {
    use std::cmp::Ordering;

    use oxidized::pos::Pos;

    use super::value;

    /// `Pos.t * Value.t`, ordered (and compared) by `compare`.
    #[derive(Clone, Debug)]
    pub struct T(pub Pos, pub value::T);

    /// We want different cases with same contents to comapre equal and that is
    /// only possible if we disregard their positions.
    pub fn compare(T(_, v1): &T, T(_, v2): &T) -> Ordering {
        value::compare(v1, v2)
    }

    impl PartialEq for T {
        fn eq(&self, other: &Self) -> bool {
            compare(self, other) == Ordering::Equal
        }
    }

    impl Eq for T {}

    impl PartialOrd for T {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(compare(self, other))
        }
    }

    impl Ord for T {
        fn cmp(&self, other: &Self) -> Ordering {
            compare(self, other)
        }
    }

    pub fn of_value(v: value::T) -> T {
        T(Pos::NONE, v)
    }
}

pub mod value_set {
    use std::collections::BTreeSet;

    use oxidized::aast;
    use oxidized::pos::Pos;

    use super::value;
    use super::value_with_pos;
    use crate::tast;

    /// `Stdlib.Set.Make (ValueWithPos)`. As in OCaml, adding a value that is
    /// already there keeps the one that is there (and its position).
    pub type T = BTreeSet<value_with_pos::T>;

    /// `of_list`
    pub fn of_list(values: impl IntoIterator<Item = value_with_pos::T>) -> T {
        let mut set = T::new();
        for v in values {
            set.insert(v);
        }
        set
    }

    /// Turn a list of cases into a set of duplicate cases and a value set
    /// representation of the cases that are recognised.
    pub fn of_case_list(cases: &[tast::Case]) -> (Vec<(Pos, Pos, value::T)>, T) {
        let mut duplicates = vec![];
        let mut values = T::new();
        for aast::Case(label, _) in cases {
            let tast::Expr(_, pos, _) = label;
            match value::of_ast(label) {
                Some(value) => {
                    let pval = value_with_pos::T(pos.clone(), value);
                    match values.get(&pval) {
                        Some(value_with_pos::T(first_occurrence, _)) => {
                            // `(first_occurrence, pos, value) :: duplicates`
                            duplicates.insert(0, (first_occurrence.clone(), pos.clone(), pval.1))
                        }
                        None => {
                            values.insert(pval);
                        }
                    }
                }
                None => {}
            }
        }
        (duplicates, values)
    }
}

pub mod alternative_set {
    use naming_special_names_rust as sn;
    use pos::Positioned;
    use pos::TypeName;
    use ty::decl::ty as d;

    use super::is_nothing;
    use super::is_null;
    use super::transpose_union_of_intersection;
    use super::value;
    use super::value_set;
    use super::value_with_pos;
    use crate::decl_entry;
    use crate::tast_env;
    use crate::tast_env::Env;
    use crate::typing_defs::ClassConst;
    use crate::typing_defs::DeclTy;
    use crate::typing_defs::empty_expand_env;
    use crate::typing_defs_core::TupleExtra;
    use crate::typing_defs_core::TupleType;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::get_node;
    use crate::typing_defs_core::get_reason;
    use crate::typing_deps;
    use crate::typing_deps::dep::Variant as Dep;
    use crate::typing_error;
    use crate::typing_make_type as make_type;
    use crate::typing_utils;

    /// Disjunctive-normal form for set of values we can satisfy to make the
    /// switch statement exhaustive. Each value set is one way of satisfying
    /// switch exhaustivity.
    ///
    /// Example: for enums E and F, switching over `E & F` can be exhaustive by
    /// covering all cases of `E` or all cases of `F`.
    pub type T = Vec<value_set::T>;

    /// `List.Cartesian_product.all`: every list made of one element of each
    /// list, the first list varying slowest.
    fn cartesian_product_all<A: Clone>(ls: &[Vec<A>]) -> Vec<Vec<A>> {
        let mut acc: Vec<Vec<A>> = vec![vec![]];
        for l in ls {
            let mut next = vec![];
            for prefix in &acc {
                for x in l {
                    let mut v = prefix.clone();
                    v.push(x.clone());
                    next.push(v)
                }
            }
            acc = next
        }
        acc
    }

    /// This helper handles vanilla enums and enum classes (`HH\EnumClass\Label`
    /// and `HH\MemberOf`).
    ///
    /// For enums and enum classes referenced through `HH\MemberOf` we are
    /// interested in constant cases. For `HH\EnumClass\Label` we are interested
    /// in label cases.
    ///
    /// For enum classes, the `bound` parameter is set and is used to eliminate
    /// cases don't need to be covered, e.g., `HH\MemberOf<E, int>` need not
    /// consider enum class values that has type string.
    ///
    /// (The environment is returned as it is given.)
    pub fn of_enum_name(
        is_enum_class_label: bool,
        bound: Option<Ty>,
        env: &mut Env,
        name: &str,
    ) -> Option<T> {
        let env: &Env = env;
        let (bound_is_nothing, bound) = match bound {
            Some(bound) => {
                let is_bound_nothing = is_nothing(env, &bound);
                let like_bound = typing_utils::make_like(None, env, bound);
                (is_bound_nothing, Some(like_bound))
            }
            None => (false, None),
        };
        if bound_is_nothing {
            // If we have `HH\MemberOf<Foo, nothing>` or
            // `HH\EnumClass\Label<Foo, nothing>` or similar, there won't be any cases
            // that needs matching.
            Some(vec![value_set::T::new()])
        } else {
            let dep = Dep::AllMembers(name.to_string());
            let decl_env = tast_env::get_decl_env(env);
            if let Some(root) = &decl_env.droot {
                typing_deps::add_idep(&tast_env::get_deps_mode(env), root, &dep)
            }
            match tast_env::get_enum(env, name) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
                decl_entry::T::Found(decl) => {
                    let of_const = |bound: Option<&Ty>,
                                    (const_, decl): &(String, ClassConst)|
                     -> Option<value_with_pos::T> {
                        let value_of_const = || {
                            // If we are scrutinising `HH\EnumClass\Label` then we need to match
                            // a label value, otherwise (`HH\MemberOf` or vanilla enum) we need an
                            // enum constant.
                            if is_enum_class_label {
                                Some(value::T::EnumClassLabel(const_.clone()))
                            } else {
                                Some(value::T::EnumConstant(name.to_string(), const_.clone()))
                            }
                        };
                        if const_ == sn::members::M_CLASS {
                            // Every class has `class` constant defined and since enums are
                            // represented as classes, so do they. Skip those.
                            None
                        } else {
                            let v = match bound {
                                Some(bound) => {
                                    let const_ty: DeclTy = match decl.ty.node_ref() {
                                        d::Ty_::Tapply(id_and_args)
                                            if is_enum_class_label
                                                && id_and_args.0.id_ref().as_str()
                                                    == sn::classes::MEMBER_OF =>
                                        {
                                            let (pos_id, args) = &**id_and_args;
                                            // Enum class constants are typed with `HH\MemberOf`,
                                            // but we have an enum class label at hand.
                                            // Construct the corresponding `HH\EnumClass\Label`
                                            // so that subtype based filtering works.
                                            DeclTy::new(
                                                decl.ty.reason().clone(),
                                                d::Ty_::Tapply(Box::new((
                                                    Positioned::new(
                                                        pos_id.pos().clone(),
                                                        TypeName::new(
                                                            sn::classes::ENUM_CLASS_LABEL,
                                                        ),
                                                    ),
                                                    args.clone(),
                                                ))),
                                            )
                                        }
                                        _ => decl.ty.clone(),
                                    };
                                    // If there is a bound (we're dealing with an enum class), filter the case out
                                    let const_ty = tast_env::localize(
                                        &mut env.clone(),
                                        &empty_expand_env(),
                                        &const_ty,
                                    );
                                    if tast_env::is_sub_type(env, &const_ty, bound) {
                                        value_of_const()
                                    } else {
                                        None
                                    }
                                }
                                None => value_of_const(),
                            };
                            v.map(value_with_pos::of_value)
                        }
                    };
                    let consts = tast_env::consts(env, &decl);
                    let values: Vec<value_with_pos::T> = consts
                        .iter()
                        .filter_map(|c| of_const(bound.as_ref(), c))
                        .collect();
                    let values = {
                        // If there are no values in the presence of a bound, it is possible
                        // that we eliminated everything which shouldn't happen. Instead of
                        // requiring a default from the get go, retry without a bound which would
                        // treat exhaustivity checking of enum class as if it was an enum and
                        // require covering every value.
                        if bound.is_some() && values.is_empty() {
                            consts.iter().filter_map(|c| of_const(None, c)).collect()
                        } else {
                            values
                        }
                    };
                    Some(vec![value_set::of_list(values)])
                }
            }
        }
    }

    /// Helper to shallowly expand types found in TAST so that we can recurse and
    /// scrutenise types. It strips like types and specially treats `~nothing` and
    /// `~null`.
    pub fn expand_type(env: &mut Env, ty: Ty) -> Ty {
        let ty = tast_env::expand_type(env, ty);
        let (_, ty) = tast_env::strip_supportdyn(env, ty);
        match get_node(&ty) {
            Ty_::Tunion(tyl) => {
                let tyl: Vec<Ty> = tyl
                    .iter()
                    .map(|ty| tast_env::expand_type(env, ty.clone()))
                    .collect();
                let (dynamic_tyl, other_tyl): (Vec<Ty>, Vec<Ty>) = tyl
                    .iter()
                    .cloned()
                    .partition(|ty| matches!(get_node(ty), Ty_::Tdynamic(_)));
                let r = get_reason(&ty).clone();
                match dynamic_tyl.as_slice() {
                    // We expanded tyl, let's not throw it away and reconstruct the union.
                    [] => make_type::union(r, tyl),
                    [_, ..] => match other_tyl.as_slice() {
                        [ty] if is_nothing(env, ty) || is_null(env, ty) => {
                            // Treat `~nothing` and `~null` as `dynamic . This is where writing
                            // a check is more of an art than science.
                            //
                            // `~nothing` is morally equivalent to `dynamic` and we want it to
                            // be treated as such.
                            //
                            // As for `~null`, although technically we should treat this the
                            // same as we treat other like types, almost always gets produced
                            // due to an operator such as `idx` or `??` through the default
                            // branch and it is more useful to ask for a default which would
                            // likely coincide with the null case anyway.
                            make_type::dynamic(r)
                        }
                        // Reconstruct the union without the like types
                        _ => make_type::union(r, other_tyl),
                    },
                }
            }
            _ => ty,
        }
    }

    /// If the type can be exhaustively checked returns a set of alternative
    /// values to satisfy.
    ///
    /// None corresponds to the universal set which we use for non-enumerable
    /// types such as `string` but also for enumerable ones that we do not
    /// support, e.g., shape of enumerable values.
    ///
    /// The universal set is useful because if we have a `E & string`, we can
    /// satisfy exhaustivity by enumerating `E` despite `string` leading to the
    /// universal value set (i.e., `None`).
    pub fn of_ty(env: &mut Env, ty: Ty) -> Option<T> {
        let ty = expand_type(env, ty);
        let ty = transpose_union_of_intersection(env, ty);
        match get_node(&ty) {
            Ty_::Tprim(oxidized::aast::Tprim::Tbool) => Some(vec![value_set::of_list(
                [value::T::True, value::T::False]
                    .into_iter()
                    .map(value_with_pos::of_value),
            )]),
            Ty_::Tprim(oxidized::aast::Tprim::Tnull) => Some(vec![value_set::of_list([
                value_with_pos::of_value(value::T::Null),
            ])]),
            Ty_::Toption(ty) => {
                // ?ty is exhaustively covered if `null` is covered and all values of `ty`
                // are covered.
                let disjuncts = of_ty(env, ty.clone());
                let disjuncts = disjuncts?;
                Some(
                    disjuncts
                        .into_iter()
                        .map(|mut values| {
                            values.insert(value_with_pos::of_value(value::T::Null));
                            values
                        })
                        .collect(),
                )
            }
            Ty_::Tnewtype(name, args, _)
                if args.len() == 2
                    && [sn::classes::MEMBER_OF, sn::classes::ENUM_CLASS_LABEL]
                        .contains(&name.as_str()) =>
            {
                // This case covers switching on enum classes through `HH\EnumClass\Label`
                // and `HH\MemberOf`.
                let enum_class = tast_env::expand_type(env, args[0].clone());
                match get_node(&enum_class) {
                    Ty_::Tclass((_, enum_class_name), _, _) => of_enum_name(
                        name == sn::classes::ENUM_CLASS_LABEL,
                        Some(ty.clone()),
                        env,
                        enum_class_name,
                    ),
                    _ => None,
                }
            }
            Ty_::Tnewtype(enum_name, _, _) if tast_env::is_enum(env, enum_name) => {
                // An enum E is exhaustively switched if there is a case for all of its
                // declared values (including inherited ones).
                of_enum_name(false, None, env, enum_name)
            }
            Ty_::Tnewtype(_, _, bound) => {
                // For newtypes with an upper bound (e.g., `newtype T as E = E`),
                // check exhaustivity against the bound type. This enables exhaustive
                // switching on newtypes whose upper bound is an enum.
                of_ty(env, bound.clone())
            }
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: TupleExtra::Tvariadic(t_variadic),
            }) if t_optional.is_empty() && is_nothing(env, t_variadic) => {
                // We only consider closed tuples for exhaustivity.
                // A tuple (E, F) can be satisfied by tuples formed by the cartesian
                // product of all values in E and F.
                let dnfs: Vec<Option<T>> =
                    t_required.iter().map(|ty| of_ty(env, ty.clone())).collect();
                let dnfs: Vec<T> = dnfs.into_iter().collect::<Option<Vec<T>>>()?;
                Some(
                    cartesian_product_all(&dnfs)
                        .into_iter()
                        .map(|vsl| {
                            let vsl: Vec<Vec<value_with_pos::T>> =
                                vsl.iter().map(|vs| vs.iter().cloned().collect()).collect();
                            value_set::of_list(cartesian_product_all(&vsl).into_iter().map(
                                |tyl| {
                                    value_with_pos::of_value(value::T::Tuple(
                                        tyl.into_iter().map(|value_with_pos::T(_, v)| v).collect(),
                                    ))
                                },
                            ))
                        })
                        .collect(),
                )
            }
            Ty_::Tunion(tyl) => {
                // A switch on E | F must satisfy values of both E and F to be exhaustive.
                let dnfs: Vec<Option<T>> = tyl.iter().map(|ty| of_ty(env, ty.clone())).collect();
                let dnfs: Vec<T> = dnfs.into_iter().collect::<Option<Vec<T>>>()?;
                Some(
                    cartesian_product_all(&dnfs)
                        .into_iter()
                        .map(|vsl| {
                            vsl.into_iter()
                                .fold(value_set::T::new(), |acc, vs| acc.union(&vs).cloned().collect())
                        })
                        .collect(),
                )
            }
            Ty_::Tintersection(tyl) => {
                // A switch on E & F can satisfy values of either E or F to be exhaustive.
                let dnfs: Vec<Option<T>> = tyl.iter().map(|ty| of_ty(env, ty.clone())).collect();
                let dnfs: Vec<T> = dnfs.into_iter().flatten().collect();
                // If none of the conjuncts can be made exhaustive, neither can the
                // intersection type.
                if dnfs.is_empty() {
                    None
                } else {
                    Some(dnfs.into_iter().flatten().collect())
                }
            }
            _ => None,
        }
    }

    pub enum Result {
        Satisfiable {
            model: value_set::T,
        },
        Unsatisfiable {
            missing: Vec<typing_error::Lazy<value_set::T>>,
        },
    }

    /// Given a set of cases we observed and possible value sets that can be
    /// satisfied to make the siwtch exhaustive, decides if any of the
    /// alternatives are covered. If so returns a model (the set of values that
    /// were satisfied), otherwise, return the set of alternative values that can
    /// be covered to satisfy ehxaustivity.
    pub fn satisfies(seen_values: &value_set::T, alternatives: &T) -> Result {
        let satisfiable_alternative = alternatives.iter().find(|values_to_exhaust| {
            values_to_exhaust.difference(seen_values).next().is_none()
        });
        match satisfiable_alternative {
            Some(values_to_exhaust) => Result::Satisfiable {
                model: values_to_exhaust.clone(),
            },
            None => {
                let alternative_missing_sets = alternatives
                    .iter()
                    .map(|values_to_exhaust| {
                        let values_to_exhaust = values_to_exhaust.clone();
                        let seen_values = seen_values.clone();
                        typing_error::Lazy::new(move || {
                            values_to_exhaust.difference(&seen_values).cloned().collect()
                        })
                    })
                    .collect();
                Result::Unsatisfiable {
                    missing: alternative_missing_sets,
                }
            }
        }
    }
}

pub fn pick_n_values(n: usize, values: &value_set::T) -> Vec<String> {
    values
        .iter()
        .take(n)
        .map(|value_with_pos::T(_, v)| utils::strip_ns(&value::show(v)).to_string())
        .collect()
}

pub fn check_exhaustiveness<'a>(
    env: &Env,
    switch_pos: &Pos,
    scrutinee_pos: &Pos,
    ty: &Ty,
    case_list: &'a [tast::Case],
    default: &'a Option<DefaultCase>,
) {
    let scrutinee_type = {
        let env = env.clone();
        let ty = ty.clone();
        typing_error::Lazy::new(move || tast_env::print_ty(&env, &ty))
    };
    let alternative_set = alternative_set::of_ty(&mut env.clone(), ty.clone());
    let (duplicates, seen_values) = value_set::of_case_list(case_list);
    // If there are identical cases, report duplicate case errors. One error for
    // each duplicate.
    for (first_occurrence, second_occurrence, case) in duplicates {
        let case: typing_warning::Lazy<'_, String> =
            LazyLock::new(Box::new(move || utils::strip_ns(&value::show(&case)).to_string()));
        tast_env::add_warning(
            env,
            (
                second_occurrence,
                typing_warning::Kind::SWITCH_REDUNDANCY,
                switch_redundancy::T::DuplicatedCase {
                    first_occurrence,
                    case,
                },
            ),
        )
    }
    match alternative_set {
        Some(alternative_set) => match alternative_set::satisfies(&seen_values, &alternative_set) {
            alternative_set::Result::Satisfiable { model } => {
                match default {
                    Some(aast::DefaultCase(default_pos, _)) => {
                        // The switch is exhaustive but has a default, report an error for
                        // dead code.
                        tast_env::add_warning(
                            env,
                            (
                                default_pos.clone(),
                                typing_warning::Kind::SWITCH_REDUNDANCY,
                                switch_redundancy::T::RedundantDefault,
                            ),
                        )
                    }
                    None => {}
                }
                let seen_size = case_list.len();
                let model_size = model.len();
                if model_size < seen_size {
                    // There must be some redundancies since the values needed to satisfy
                    // exhaustivity is smaller than there are cases.
                    let positions: typing_warning::Lazy<'_, Vec<Pos>> =
                        LazyLock::new(Box::new(move || {
                            // `Pos.Set.of_list`
                            let case_positions: BTreeSet<Pos> = case_list
                                .iter()
                                .map(|aast::Case(tast::Expr(_, p, _), _)| p.clone())
                                .collect();
                            // `ValueSet.inter seen_values model` keeps the
                            // elements of `seen_values`.
                            let model_positions: BTreeSet<Pos> = seen_values
                                .iter()
                                .filter(|v| model.contains(*v))
                                .map(|value_with_pos::T(p, _)| p.clone())
                                .collect();
                            case_positions
                                .difference(&model_positions)
                                .take(10)
                                .cloned()
                                .collect()
                        }));
                    tast_env::add_warning(
                        env,
                        (
                            switch_pos.clone(),
                            typing_warning::Kind::SWITCH_REDUNDANCY,
                            switch_redundancy::T::SwitchHasRedundancy {
                                positions,
                                redundancy_size: (seen_size - model_size) as isize,
                            },
                        ),
                    )
                }
            }
            alternative_set::Result::Unsatisfiable { missing } => match default {
                None => {
                    for missing_values in missing {
                        let missing = typing_error::Lazy::new(move || {
                            pick_n_values(10, missing_values.force())
                        });
                        // The values do not satisfy any of the value sets. For each
                        // alternative value set, emit an exhaustivity error reporting what
                        // values need to be provided to make the switch exhaustive.
                        tast_env::add_typing_error(
                            &typing_error::switch(primary::switch::T::SwitchNonexhaustive {
                                switch_pos: switch_pos.clone(),
                                scrutinee_pos: scrutinee_pos.clone(),
                                scrutinee_type: scrutinee_type.clone(),
                                missing,
                            }),
                            env,
                        )
                    }
                }
                Some(_) => {}
            },
        },
        None => match default {
            None => {
                // We can't check the type for exhaustivity and there is no default, require
                // one.
                tast_env::add_typing_error(
                    &typing_error::switch(primary::switch::T::SwitchNeedsDefault {
                        switch_pos: switch_pos.clone(),
                        scrutinee_pos: scrutinee_pos.clone(),
                        scrutinee_type,
                    }),
                    env,
                )
            }
            Some(_) => {}
        },
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_stmt(&mut self, env: &Env, s: &'a tast::Stmt) {
        let aast::Stmt(st_pos, st) = s;
        match st {
            aast::Stmt_::Switch(switch) => {
                let (tast::Expr(scrutinee_ty, scrutinee_pos, _), case_list, default) = &**switch;
                check_exhaustiveness(env, st_pos, scrutinee_pos, scrutinee_ty, case_list, default)
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values() {
        assert_eq!(
            value::show(&value::T::Tuple(vec![
                value::T::True,
                value::T::EnumConstant("\\NS\\E".to_string(), "A".to_string()),
                value::T::EnumClassLabel("L".to_string()),
            ])),
            // `Utils.strip_ns`: the leading backslash only.
            "(true, NS\\E::A, #L)"
        );
        // Constructors are ordered as they are declared.
        assert!(value::T::Null < value::T::Int("0".to_string()));
        // Positions are ignored, and the first one added is kept.
        let p = Pos::NONE;
        let mut set = value_set::T::new();
        set.insert(value_with_pos::T(p.clone(), value::T::True));
        assert!(set.contains(&value_with_pos::of_value(value::T::True)));
        assert_eq!(
            pick_n_values(1, &value_set::of_list([
                value_with_pos::of_value(value::T::False),
                value_with_pos::of_value(value::T::True),
            ])),
            vec!["true".to_string()]
        );
    }
}
