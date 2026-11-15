// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_reason.ml`, lines 3164-4480: module `Derivation`
//! and the functions `explain`, `debug_reason`, `debug_derivation` at the end
//! of the file.
//! See `hh/PORTING.md`.
//!
//! `Typing_reason.Derivation` is [`derivation`] (with its submodules
//! `Subtype_rule`, `Subtype_step` and `Explain`); the three functions of
//! `typing_reason.mli` that use it are [`explain`], [`debug_reason`] and
//! [`debug_derivation`], which `typing_reason.rs` calls.
//!
//! The functions of `typing_reason.ml` that are tail recursive along a chain
//! of reasons (`extract_last`, `extract_first`, the `aux` of `of_reason`, and
//! the cases of `explain_reason` that only move to an inner reason) are loops
//! here: OCaml runs them in constant stack, and Rust does not eliminate tail
//! calls. Everything else recurses as the OCaml does.
//!
//! The JSON (`debug_reason`, `debug_derivation`, the `to_json` of this
//! module) needs three things that are not in `typing_reason.rs`; see the
//! section "From the rest of `typing_reason.ml`" below.

use oxidized::explanation;
use oxidized::explanation::Explanation;
use oxidized::pos_or_decl::PosOrDecl;

use super::Axiom;
use super::CstrVariance;
use super::CtorKind;
use super::FieldKind;
use super::PrjAsymm;
use super::PrjSymm;
use super::T_;
use super::VarianceDir;
// `Yojson.Safe.t`. `crate::yojson` is compiled only with the features `port`
// and `server`, whereas `typing_reason` is compiled in every build: the JSON
// functions of this file are compiled with those features only.
#[cfg(any(feature = "port", feature = "server"))]
use crate::yojson::safe::T as Json;

/// A list of `Pos_or_decl.t Explanation.elem`.
type Expl = Vec<explanation::Elem<PosOrDecl>>;

// ~~ From the rest of `typing_reason.ml` ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//
// The JSON form of reasons is not in `typing_reason.rs`. The small
// converters that this file needs are transliterated here from the top of
// `typing_reason.ml`, under their OCaml names; `to_json` itself (the
// `to_json_help` of lines 1913-2125 and the `*_to_json` of witnesses, blames,
// ...) is not, and is a `todo!`. Once `typing_reason.rs` has them, these
// should go and the calls should use `super::`.

#[cfg(any(feature = "port", feature = "server"))]
/// `variance_dir_to_json` (typing_reason.ml)
fn variance_dir_to_json(dir: &VarianceDir) -> Json {
    match dir {
        VarianceDir::Co => Json::Assoc(vec![("Co".to_string(), Json::List(vec![]))]),
        VarianceDir::Contra => Json::Assoc(vec![("Contr".to_string(), Json::List(vec![]))]),
    }
}

#[cfg(any(feature = "port", feature = "server"))]
/// `cstr_variance_to_json` (typing_reason.ml)
fn cstr_variance_to_json(variance: &CstrVariance) -> Json {
    match variance {
        CstrVariance::Dir(dir) => Json::Assoc(vec![(
            "Dir".to_string(),
            Json::List(vec![variance_dir_to_json(dir)]),
        )]),
        CstrVariance::Inv(dir) => Json::Assoc(vec![(
            "Inv".to_string(),
            Json::List(vec![variance_dir_to_json(dir)]),
        )]),
    }
}

#[cfg(any(feature = "port", feature = "server"))]
/// `field_kind_to_json` (typing_reason.ml)
fn field_kind_to_json(fld_kind: &FieldKind) -> Json {
    match fld_kind {
        FieldKind::Absent => Json::Assoc(vec![("Absent".to_string(), Json::List(vec![]))]),
        FieldKind::Optional => Json::Assoc(vec![("Optional".to_string(), Json::List(vec![]))]),
        FieldKind::Required => Json::Assoc(vec![("Required".to_string(), Json::List(vec![]))]),
    }
}

#[cfg(any(feature = "port", feature = "server"))]
/// `ctor_kind_to_json` (typing_reason.ml)
fn ctor_kind_to_json(ctor_kind: &CtorKind) -> Json {
    match ctor_kind {
        CtorKind::CtorClass => Json::String("Ctor_class".to_string()),
        CtorKind::CtorNewtype => Json::String("Ctor_newtype".to_string()),
    }
}

#[cfg(any(feature = "port", feature = "server"))]
/// `prj_symm_to_json` (typing_reason.ml)
fn prj_symm_to_json(prj: &PrjSymm) -> Json {
    match prj {
        PrjSymm::PrjSymmNeg => Json::String("Prj_symm_neg".to_string()),
        PrjSymm::PrjSymmNullable => Json::String("Prj_symm_nullable".to_string()),
        PrjSymm::PrjSymmSupportdyn => Json::String("Prj_symm_supportdyn".to_string()),
        PrjSymm::PrjSymmCtor(ctor_kind, nm, idx, variance) => Json::Assoc(vec![(
            "Prj_symm_ctor".to_string(),
            Json::List(vec![
                ctor_kind_to_json(ctor_kind),
                Json::String(nm.clone()),
                Json::Int(*idx),
                cstr_variance_to_json(variance),
            ]),
        )]),
        PrjSymm::PrjSymmTuple(idx) => {
            Json::Assoc(vec![("Prj_symm_tuple".to_string(), Json::Int(*idx))])
        }
        PrjSymm::PrjSymmShape(fld_nm, fld_kind_sub, fld_kind_super) => Json::Assoc(vec![(
            "Prj_symm_shape".to_string(),
            Json::List(vec![
                Json::String(fld_nm.clone()),
                field_kind_to_json(fld_kind_sub),
                field_kind_to_json(fld_kind_super),
            ]),
        )]),
        PrjSymm::PrjSymmFnParam(idx_sub, idx_sup) => Json::Assoc(vec![(
            "Prj_symm_fn_param".to_string(),
            Json::List(vec![Json::Int(*idx_sub), Json::Int(*idx_sup)]),
        )]),
        PrjSymm::PrjSymmFnParamInout(idx_sub, idx_sup, variance) => Json::Assoc(vec![(
            "Prj_symm_fn_param_inout".to_string(),
            Json::List(vec![
                Json::Int(*idx_sub),
                Json::Int(*idx_sup),
                variance_dir_to_json(variance),
            ]),
        )]),
        PrjSymm::PrjSymmFnRet => Json::String("Prj_symm_fn_ret".to_string()),
    }
}

#[cfg(any(feature = "port", feature = "server"))]
/// `prj_asymm_to_json` (typing_reason.ml)
fn prj_asymm_to_json(prj: &PrjAsymm) -> Json {
    match prj {
        PrjAsymm::PrjAsymmUnion => Json::String("Prj_asymm_union".to_string()),
        PrjAsymm::PrjAsymmInter => Json::String("Prj_asymm_inter".to_string()),
        PrjAsymm::PrjAsymmNeg => Json::String("Prj_asymm_neg".to_string()),
        PrjAsymm::PrjAsymmNullable => Json::String("Prj_asymm_nullable".to_string()),
        PrjAsymm::PrjAsymmArraykey => Json::String("Prj_asymm_arraykey".to_string()),
        PrjAsymm::PrjAsymmNum => Json::String("Prj_asymm_num".to_string()),
        PrjAsymm::PrjAsymmContains => Json::String("Prj_asymm_contains".to_string()),
    }
}

#[cfg(any(feature = "port", feature = "server"))]
/// `axiom_to_json` (typing_reason.ml)
fn axiom_to_json(axiom: &Axiom) -> Json {
    match axiom {
        Axiom::Extends => Json::String("Extends".to_string()),
        Axiom::UpperBound(_) => Json::String("Upper_bound".to_string()),
        Axiom::LowerBound => Json::String("Lower_bound".to_string()),
    }
}

#[cfg(any(feature = "port", feature = "server"))]
/// `Typing_reason.to_json` (`fst (to_json_help t (Some 20))`).
fn to_json(_r: &T_) -> Json {
    todo!(
        "Typing_reason.to_json: the JSON form of reasons (to_json_help and the *_to_json of witnesses, typing_reason.ml 23-1909 and 1913-2125) is not ported in typing_reason.rs"
    )
}

#[cfg(any(feature = "port", feature = "server"))]
/// `Yojson.Safe.pretty_to_string`. Its port,
/// `crate::yojson::safe::pretty_to_string`, is compiled only with the
/// feature `server`.
fn yojson_safe_pretty_to_string(json: &Json) -> String {
    #[cfg(feature = "server")]
    {
        crate::yojson::safe::pretty_to_string(json)
    }
    #[cfg(not(feature = "server"))]
    {
        let _ = json;
        todo!(
            "Yojson.Safe.pretty_to_string: ported as crate::rt::yojson_ext::pretty_to_string, which is compiled only with the feature `server`"
        )
    }
}

// ~~ Derivation ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Typing_reason.Derivation`
pub mod derivation {
    #[cfg(any(feature = "port", feature = "server"))]
    use super::Json;
    use super::T_;
    use crate::typing_reason::LazyString;
    use crate::typing_reason::Tvid;
    use crate::typing_reason::WitnessLocl;

    /// `Tvid.Map.t` of the solutions of type variables, as reasons. It is
    /// extended on the way down and each branch keeps its own: a persistent
    /// map.
    pub type Solutions = im::OrdMap<Tvid, T_>;

    pub mod subtype_rule {
        use super::super::Axiom;
        use super::super::CstrVariance;
        use super::super::CtorKind;
        use super::super::FieldKind;
        #[cfg(any(feature = "port", feature = "server"))]
        use super::super::Json;
        use super::super::PrjAsymm;
        use super::super::PrjSymm;
        use super::super::VarianceDir;
        #[cfg(any(feature = "port", feature = "server"))]
        use super::super::axiom_to_json;
        #[cfg(any(feature = "port", feature = "server"))]
        use super::super::prj_asymm_to_json;
        #[cfg(any(feature = "port", feature = "server"))]
        use super::super::prj_symm_to_json;
        use crate::typing_reason::strip_ns;

        /// Tells us why a derivation step follows the previous one
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum T {
            UsingPrj(PrjSymm),
            UsingPrjSub(PrjAsymm),
            UsingPrjSuper(PrjAsymm),
            UsingAxiomSub(Axiom),
            UsingAxiomSuper(Axiom),
        }

        pub fn is_supportdyn(t: &T) -> bool {
            match t {
                T::UsingPrj(PrjSymm::PrjSymmSupportdyn) => true,
                _ => false,
            }
        }

        /// We reached the next step in the derivation by projecting into both
        /// the subtype and supertype
        pub fn using_prj(prj: PrjSymm) -> T {
            T::UsingPrj(prj)
        }

        /// We reached the next step in the derivation by projecting into the
        /// subtype
        pub fn using_prj_sub(prj: PrjAsymm) -> T {
            T::UsingPrjSub(prj)
        }

        /// We reached the next step in the derivation by projecting into the
        /// supertype
        pub fn using_prj_super(prj: PrjAsymm) -> T {
            T::UsingPrjSuper(prj)
        }

        /// We reached the next step in the derivation by making use of some
        /// user-declared axiom on about the subtype
        pub fn using_axiom_sub(axiom: Axiom) -> T {
            T::UsingAxiomSub(axiom)
        }

        /// We reached the next step in the derivation by making use of some
        /// user-declared axiom on about the supertype
        pub fn using_axiom_super(axiom: Axiom) -> T {
            T::UsingAxiomSuper(axiom)
        }

        #[cfg(any(feature = "port", feature = "server"))]
        pub fn to_json(t: &T) -> Json {
            match t {
                T::UsingPrj(prj) => {
                    Json::Assoc(vec![("Using_prj".to_string(), prj_symm_to_json(prj))])
                }
                T::UsingPrjSub(prj) => {
                    Json::Assoc(vec![("Using_prj_sub".to_string(), prj_asymm_to_json(prj))])
                }
                T::UsingPrjSuper(prj) => {
                    Json::Assoc(vec![("Using_prj_super".to_string(), prj_asymm_to_json(prj))])
                }
                T::UsingAxiomSub(axiom) => {
                    Json::Assoc(vec![("Using axiom_sub".to_string(), axiom_to_json(axiom))])
                }
                T::UsingAxiomSuper(axiom) => {
                    Json::Assoc(vec![("Using axiom_super".to_string(), axiom_to_json(axiom))])
                }
            }
        }

        pub(crate) fn int_to_ordinal(n: isize) -> String {
            const SFXS: [&str; 5] = ["th", "st", "nd", "rd", "th"];
            let sfx = if n >= 10 && n <= 20 {
                "th"
            } else {
                // `sfxs.(min 4 (n mod 10))`: OCaml's `mod` and Rust's `%`
                // both give a result of the sign of `n`, and OCaml raises
                // `Invalid_argument "index out of bounds"` on a negative index.
                match usize::try_from(std::cmp::min(4, n % 10)) {
                    Ok(i) => SFXS[i],
                    Err(_) => panic!("index out of bounds"),
                }
            };
            format!("{}{}", n, sfx)
        }

        fn explain_axiom(axiom: &Axiom, sub: bool) -> String {
            let (subject, other) = if sub {
                ("subtype", "supertype")
            } else {
                ("supertype", "subtype")
            };
            match axiom {
                Axiom::Extends => format!(
                    "The {} extends or implements the {} class or interface so next I checked that subtype constraint.",
                    subject, other
                ),
                Axiom::UpperBound(_) => format!(
                    "The {} declares an upper bound so next I checked that was a {} of the {}.",
                    subject, subject, other
                ),
                Axiom::LowerBound => format!(
                    "The {} declares a lower bound so next I checked that was a {} of the {}.",
                    subject, subject, other
                ),
            }
        }

        fn explain_ctor_kind(ctor_kind: &CtorKind) -> &'static str {
            match ctor_kind {
                CtorKind::CtorClass => "class or interface",
                CtorKind::CtorNewtype => "newtype",
            }
        }

        fn explain_field_kind(fld_kind: &FieldKind) -> &'static str {
            match fld_kind {
                FieldKind::Absent => "missing",
                FieldKind::Required => "required",
                FieldKind::Optional => "optional",
            }
        }

        fn explain_prj(prj: &PrjSymm) -> String {
            match prj {
                PrjSymm::PrjSymmNeg => "These are negated types so I checked the inner type.".to_string(),
                PrjSymm::PrjSymmNullable => {
                    "These are nullable types so next I checked the non-null parts.".to_string()
                }
                PrjSymm::PrjSymmSupportdyn => {
                    "These are `supportdyn` types so next I checked the non-dynamic parts."
                        .to_string()
                }
                PrjSymm::PrjSymmFnRet => {
                    "These are function types so next I checked function return types."
                        .to_string()
                }
                PrjSymm::PrjSymmTuple(idx) => format!(
                    "These are tuple types so next I checked {} elements.",
                    int_to_ordinal(idx + 1)
                ),
                PrjSymm::PrjSymmFnParam(idx_sub, idx_sup) if idx_sub == idx_sup => format!(
                    "These are function types so next I checked the {} function parameters.\nFunctions are contravariant in their parameters so the direction of the subtype relationship is reversed.",
                    int_to_ordinal(idx_sub + 1)
                ),
                PrjSymm::PrjSymmFnParam(idx_sub, idx_sup) => format!(
                    "These are function types so next I checked the {} function parameter of the subtype and the {} parameter of the supertype.\nFunctions are contravariant in their parameters the direction of the subtype relationship is reversed.",
                    int_to_ordinal(idx_sub + 1),
                    int_to_ordinal(idx_sup + 1)
                ),
                PrjSymm::PrjSymmFnParamInout(idx_sub, idx_sup, VarianceDir::Co)
                    if idx_sub == idx_sup =>
                {
                    format!(
                        "These are function types so next I checked the {} function parameters.\nThis is an `inout` parameter which is invariant. This means the subtype relation must hold in both directions.\nHere I checked the covariant direction.",
                        int_to_ordinal(idx_sub + 1)
                    )
                }
                PrjSymm::PrjSymmFnParamInout(idx_sub, idx_sup, VarianceDir::Co) => format!(
                    "These are function types so next I checked the {} function parameter of the subtype and the {} parameter of the supertype.\nThese are `inout` parameters which are invariant. This means the subtype relation must hold in both directions.\nHere I checked the covariant direction.",
                    int_to_ordinal(idx_sub + 1),
                    int_to_ordinal(idx_sup + 1)
                ),
                PrjSymm::PrjSymmFnParamInout(idx_sub, idx_sup, VarianceDir::Contra)
                    if idx_sub == idx_sup =>
                {
                    format!(
                        "These are function types so next I checked the {} function parameters.\nThis is an `inout` parameter which is invariant. This means the subtype relation must hold in both directions.\nHere I checked the contravariant case so the direction of the subtype relationship is reversed.",
                        int_to_ordinal(idx_sub + 1)
                    )
                }
                PrjSymm::PrjSymmFnParamInout(idx_sub, idx_sup, VarianceDir::Contra) => format!(
                    "These are function types so next I checked the {} function parameter of the supertype and the {} parameter of the subtype. These are `inout` parameters which are invariant. This means the relation must hold in both directions.\nHere I checked the contravariant case so the direction of the subtype relationship is reversed.",
                    int_to_ordinal(idx_sup + 1),
                    int_to_ordinal(idx_sub + 1)
                ),
                PrjSymm::PrjSymmCtor(ctor_kind, nm, idx, CstrVariance::Dir(VarianceDir::Co)) => {
                    format!(
                        "`{}` is a {} so next I checked the {} type arguments.",
                        strip_ns(nm),
                        explain_ctor_kind(ctor_kind),
                        int_to_ordinal(idx + 1)
                    )
                }
                PrjSymm::PrjSymmCtor(ctor_kind, nm, idx, CstrVariance::Dir(VarianceDir::Contra)) => {
                    format!(
                        "`{}` is a {} so next I checked the {} type arguments.\nThe type parameter is contravariant so the direction of the subtype relationship is reversed.",
                        strip_ns(nm),
                        explain_ctor_kind(ctor_kind),
                        int_to_ordinal(idx + 1)
                    )
                }
                PrjSymm::PrjSymmCtor(ctor_kind, nm, idx, CstrVariance::Inv(VarianceDir::Co)) => {
                    format!(
                        "`{}` is a {} so next I checked the {} type arguments are subtypes.\nThe type parameter is invariant so the subtype relationship must hold in both directions.\nHere I check the covariant case.",
                        strip_ns(nm),
                        explain_ctor_kind(ctor_kind),
                        int_to_ordinal(idx + 1)
                    )
                }
                PrjSymm::PrjSymmCtor(ctor_kind, nm, idx, CstrVariance::Inv(VarianceDir::Contra)) => {
                    format!(
                        "`{}` is a {} so next I checked the {} type arguments are subtypes.\nThe type parameter is invariant so the subtype relationship must hold in both directions.\nHere I check the contravariant case so the direction of the subtype relationship is reversed.",
                        strip_ns(nm),
                        explain_ctor_kind(ctor_kind),
                        int_to_ordinal(idx + 1)
                    )
                }
                PrjSymm::PrjSymmShape(nm, FieldKind::Absent, fld_kind_sup) => format!(
                    "These are shape types so next I tried to check the `{}` field.\nThe field is {} in the supertype but missing in the subtype.",
                    nm,
                    explain_field_kind(fld_kind_sup)
                ),
                PrjSymm::PrjSymmShape(nm, fld_kind_sub, FieldKind::Absent) => format!(
                    "These are shape types so next I tried to check the `{}` field.\nThe field is {} in the subtype but missing in the supertype.",
                    nm,
                    explain_field_kind(fld_kind_sub)
                ),
                PrjSymm::PrjSymmShape(nm, fld_kind_sub, fld_kind_sup)
                    if fld_kind_sub == fld_kind_sup =>
                {
                    format!(
                        "These are shape types so next I checked the {} `{}` field.",
                        explain_field_kind(fld_kind_sub),
                        nm
                    )
                }
                PrjSymm::PrjSymmShape(nm, fld_kind_sub, fld_kind_sup) => format!(
                    "These are shape types so next I checked the `{}` field.\nThe field was {} in the subtype and {} in the supertype.",
                    nm,
                    explain_field_kind(fld_kind_sub),
                    explain_field_kind(fld_kind_sup)
                ),
            }
        }

        fn explain_prj_asymm_sub(prj: &PrjAsymm) -> &'static str {
            match prj {
                PrjAsymm::PrjAsymmUnion => {
                    "The subtype is a union type so next I checked the subtype constraint is satisfied for all its elements."
                }
                PrjAsymm::PrjAsymmInter => {
                    "The subtype is an intersection type so next I checked that the subtype constraint is satisfied for at least one of its element."
                }
                PrjAsymm::PrjAsymmNullable => {
                    "The subtype is a nullable type so next I checked the subtype constraint is satisfied for both the null & non-null parts."
                }
                PrjAsymm::PrjAsymmNum => {
                    "The subtype is a num type so next I checked the subtype constraint is satisfied for both the int and float parts."
                }
                PrjAsymm::PrjAsymmArraykey => {
                    "The subtype is an arraykey type so next I checked the subtype constraint is satisfied for both the int and string parts."
                }
                PrjAsymm::PrjAsymmNeg => {
                    "The subtype is a negated type so next I checked the inner type."
                }
                PrjAsymm::PrjAsymmContains => {
                    "The subtype is some aggregate type so next I checked one the types that it contains."
                }
            }
        }

        fn explain_prj_asymm_super(prj: &PrjAsymm) -> &'static str {
            match prj {
                PrjAsymm::PrjAsymmUnion => {
                    "The supertype is a union type so next I checked the subtype constraint is satisfied for at least one element."
                }
                PrjAsymm::PrjAsymmInter => {
                    "The supertype is an intersection type so next I checked the subtype constraint is satsified for all of its elements."
                }
                PrjAsymm::PrjAsymmNullable => {
                    "The supertype is a nullable type so next I checked the subtype constraint is satisfied for either the null or non-null part."
                }
                PrjAsymm::PrjAsymmNum => {
                    "The supertype is a num type so next I checked the subtype constraint is satisfied for either the int or float part."
                }
                PrjAsymm::PrjAsymmArraykey => {
                    "The supertype is an arraykey type so next I checked the subtype constraint is satisfied for either the int or string part."
                }
                PrjAsymm::PrjAsymmNeg => {
                    "The supertype is a negated type so I checked the inner type."
                }
                PrjAsymm::PrjAsymmContains => {
                    "The supertype is some aggregate type so next I checked one the types that it contains."
                }
            }
        }

        pub fn explain(t: &T) -> String {
            match t {
                T::UsingPrj(prj) => explain_prj(prj),
                T::UsingPrjSub(prj) => explain_prj_asymm_sub(prj).to_string(),
                T::UsingPrjSuper(prj) => explain_prj_asymm_super(prj).to_string(),
                T::UsingAxiomSub(axiom) => explain_axiom(axiom, true),
                T::UsingAxiomSuper(axiom) => explain_axiom(axiom, false),
            }
        }
    }

    pub mod subtype_step {
        #[cfg(any(feature = "port", feature = "server"))]
        use super::super::Json;
        use super::super::T_;
        use super::subtype_rule;

        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum Arg {
            Subtype,
            Supertype,
            Both,
        }

        #[cfg(any(feature = "port", feature = "server"))]
        fn arg_to_json(arg: &Arg) -> Json {
            match arg {
                Arg::Subtype => Json::String("Subtype".to_string()),
                Arg::Supertype => Json::String("Supertype".to_string()),
                Arg::Both => Json::String("Both".to_string()),
            }
        }

        /// Represents a step in a subtyping derivation for a single subtype
        /// proposition
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum T {
            Begin {
                sub: T_,
                super_: T_,
            },
            Step {
                rule: subtype_rule::T,
                on_: Arg,
                sub: T_,
                super_: T_,
            },
        }

        pub fn step(rule: subtype_rule::T, on_: Arg, sub: T_, super_: T_) -> T {
            T::Step {
                sub,
                super_,
                rule,
                on_,
            }
        }

        pub fn uses_supportdyn(t: &T) -> bool {
            match t {
                T::Begin { .. } => false,
                T::Step { rule, .. } => subtype_rule::is_supportdyn(rule),
            }
        }

        pub fn begin_(sub: T_, super_: T_) -> T {
            T::Begin { sub, super_ }
        }

        #[cfg(any(feature = "port", feature = "server"))]
        pub fn to_json(t: &T) -> Json {
            match t {
                T::Begin { sub, super_ } => Json::Assoc(vec![(
                    "Begin".to_string(),
                    Json::Assoc(vec![
                        ("sub".to_string(), super::super::to_json(sub)),
                        ("super".to_string(), super::super::to_json(super_)),
                    ]),
                )]),
                T::Step {
                    sub,
                    super_,
                    rule,
                    on_,
                } => Json::Assoc(vec![(
                    "Step".to_string(),
                    Json::Assoc(vec![
                        ("rule".to_string(), subtype_rule::to_json(rule)),
                        ("on_".to_string(), arg_to_json(on_)),
                        ("sub".to_string(), super::super::to_json(sub)),
                        ("super".to_string(), super::super::to_json(super_)),
                    ]),
                )]),
            }
        }
    }

    /// Represents a complete derivation for a single subtype proposition and
    /// the typing rule used to reach it from the previous subtype proposition
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum T {
        Derivation(Vec<subtype_step::T>),
        Lower {
            bound: Box<T>,
            in_: Box<T>,
        },
        Transitive {
            lower: Box<T>,
            upper: Box<T>,
            in_: Box<T>,
            on_: T_,
        },
    }

    pub fn derivation(steps: Vec<subtype_step::T>) -> T {
        T::Derivation(steps)
    }

    pub fn transitive(upper: T, lower: T, on_: T_, in_: T) -> T {
        T::Transitive {
            in_: Box::new(in_),
            on_,
            upper: Box::new(upper),
            lower: Box::new(lower),
        }
    }

    pub fn lower_bound(bound: T, in_: T) -> T {
        T::Lower {
            bound: Box::new(bound),
            in_: Box::new(in_),
        }
    }

    #[cfg(any(feature = "port", feature = "server"))]
    pub fn to_json(t: &T) -> Json {
        fn aux(t: &T) -> Json {
            match t {
                T::Derivation(steps) => Json::Assoc(vec![(
                    "Derivation".to_string(),
                    Json::List(steps.iter().map(subtype_step::to_json).collect()),
                )]),
                T::Lower { bound, in_ } => Json::Assoc(vec![(
                    "Lower".to_string(),
                    Json::Assoc(vec![
                        ("bound".to_string(), aux(bound)),
                        ("in_".to_string(), aux(in_)),
                    ]),
                )]),
                T::Transitive {
                    lower,
                    upper,
                    on_,
                    in_,
                } => Json::Assoc(vec![(
                    "Transitive".to_string(),
                    Json::Assoc(vec![
                        ("lower".to_string(), aux(lower)),
                        ("upper".to_string(), aux(upper)),
                        ("on_".to_string(), super::to_json(on_)),
                        ("in_".to_string(), aux(in_)),
                    ]),
                )]),
            }
        }
        aux(t)
    }

    // ~~ Construct a derviation from a reason ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    pub fn push_solutions(t: &T_, solutions: &Solutions) -> T_ {
        match t {
            T_::FromWitnessLocl(
                WitnessLocl::TypeVariable(_, id)
                | WitnessLocl::TypeVariableGenerics(_, _, _, id)
                | WitnessLocl::TypeVariableError(_, id),
            ) => solutions.get(id).cloned().unwrap_or_else(|| t.clone()),
            T_::Flow { from, into, kind } => T_::Flow {
                from: crate::typing_reason::T::new(push_solutions(from, solutions)),
                into: crate::typing_reason::T::new(push_solutions(into, solutions)),
                kind: kind.clone(),
            },
            T_::Def(pos, of_) => T_::Def(
                pos.clone(),
                crate::typing_reason::T::new(push_solutions(of_, solutions)),
            ),
            T_::Instantiate {
                type_,
                var_name,
                var,
            } => T_::Instantiate {
                type_: crate::typing_reason::T::new(push_solutions(type_, solutions)),
                var_name: var_name.clone(),
                var: crate::typing_reason::T::new(push_solutions(var, solutions)),
            },
            T_::Typeconst(r1, p, q, r2) => T_::Typeconst(
                crate::typing_reason::T::new(push_solutions(r1, solutions)),
                p.clone(),
                q.clone(),
                crate::typing_reason::T::new(push_solutions(r2, solutions)),
            ),
            T_::ExprDepType(r, s, t) => T_::ExprDepType(
                crate::typing_reason::T::new(push_solutions(r, solutions)),
                s.clone(),
                t.clone(),
            ),
            T_::LostInfo(x, t, y) => T_::LostInfo(
                x.clone(),
                crate::typing_reason::T::new(push_solutions(t, solutions)),
                y.clone(),
            ),
            T_::TypeAccess(t, x) => T_::TypeAccess(
                crate::typing_reason::T::new(push_solutions(t, solutions)),
                x.clone(),
            ),
            T_::DynamicCoercion(t) => {
                T_::DynamicCoercion(crate::typing_reason::T::new(push_solutions(t, solutions)))
            }
            _ => t.clone(),
        }
    }

    pub fn extract_last(t: &T_) -> &T_ {
        let mut t = t;
        loop {
            match t {
                T_::PrjBoth { sub, .. } => t = &**sub,
                T_::PrjOne { whole, .. } => t = &**whole,
                T_::Axiom { prev, .. } => t = &**prev,
                T_::Flow { into, .. } => t = &**into,
                T_::LowerBound { of_, .. } => t = &**of_,
                T_::Solved { .. }
                | T_::NoReason
                | T_::FromWitnessDecl(_)
                | T_::FromWitnessLocl(_)
                | T_::Instantiate { .. }
                | T_::Def(..)
                | T_::Invalid
                | T_::MissingField
                | T_::Idx(..)
                | T_::ArithRetFloat(..)
                | T_::ArithRetNum(..)
                | T_::LostInfo(..)
                | T_::Format(..)
                | T_::Typeconst(..)
                | T_::TypeAccess(..)
                | T_::ExprDepType(..)
                | T_::LambdaParam(..)
                | T_::DynamicCoercion(_)
                | T_::DynamicPartialEnforcement(..)
                | T_::RigidTvarEscape(..)
                | T_::OpaqueTypeFromModule(..)
                | T_::SDTCall(..)
                | T_::LikeCall(..) => return t,
            }
        }
    }

    pub fn extract_first(t: &T_) -> &T_ {
        let mut t = t;
        loop {
            match t {
                T_::PrjBoth { sub_prj, .. } => t = &**sub_prj,
                T_::PrjOne { part, .. } => t = &**part,
                T_::Axiom { next, .. } => t = &**next,
                T_::Flow { from, .. } => t = &**from,
                T_::LowerBound { bound, .. } => t = &**bound,
                T_::Solved { .. }
                | T_::NoReason
                | T_::FromWitnessDecl(_)
                | T_::FromWitnessLocl(_)
                | T_::Instantiate { .. }
                | T_::Def(..)
                | T_::Invalid
                | T_::MissingField
                | T_::Idx(..)
                | T_::ArithRetFloat(..)
                | T_::ArithRetNum(..)
                | T_::LostInfo(..)
                | T_::Format(..)
                | T_::Typeconst(..)
                | T_::TypeAccess(..)
                | T_::ExprDepType(..)
                | T_::LambdaParam(..)
                | T_::DynamicCoercion(_)
                | T_::DynamicPartialEnforcement(..)
                | T_::RigidTvarEscape(..)
                | T_::OpaqueTypeFromModule(..)
                | T_::SDTCall(..)
                | T_::LikeCall(..) => return t,
            }
        }
    }

    /// Bottom up traversal of a reason applying available solutions in order
    /// to eliminate type variable associated and [Solved] reasons
    pub fn resolve(t: &T_, depth: isize, solutions: &Solutions) -> T_ {
        use std::rc::Rc;
        if depth <= 0 {
            return t.clone();
        }
        let res = |r: &Rc<T_>| Rc::new(resolve(r, depth, solutions));
        match t {
            // Substitute a tvar for its solution
            T_::FromWitnessLocl(
                WitnessLocl::TypeVariable(_, id)
                | WitnessLocl::TypeVariableGenerics(_, _, _, id)
                | WitnessLocl::TypeVariableError(_, id),
            ) => solutions.get(id).cloned().unwrap_or_else(|| t.clone()),
            T_::FromWitnessLocl(witness) => T_::FromWitnessLocl(witness.clone()),
            T_::FromWitnessDecl(witness) => T_::FromWitnessDecl(witness.clone()),
            T_::Solved {
                solution,
                of_,
                in_,
            } => {
                let depth = depth - 1;
                let solution = resolve(solution, depth, solutions);
                let solutions = solutions.update(*of_, solution);
                resolve(in_, depth, &solutions)
            }
            T_::TypeAccess(r, l) => T_::TypeAccess(
                res(r),
                l.iter()
                    .map(|(r, x): &(Rc<T_>, LazyString)| (res(r), x.clone()))
                    .collect(),
            ),
            T_::Typeconst(r1, x, s, r2) => T_::Typeconst(res(r1), x.clone(), s.clone(), res(r2)),
            T_::ArithRetFloat(x, r, z) => T_::ArithRetFloat(x.clone(), res(r), *z),
            T_::ArithRetNum(x, r, z) => T_::ArithRetNum(x.clone(), res(r), *z),
            T_::LostInfo(x, r, z) => T_::LostInfo(x.clone(), res(r), z.clone()),
            T_::Format(x, y, r) => T_::Format(x.clone(), y.clone(), res(r)),
            T_::Instantiate {
                type_,
                var_name,
                var,
            } => T_::Instantiate {
                type_: res(type_),
                var_name: var_name.clone(),
                var: res(var),
            },
            T_::ExprDepType(r, y, z) => T_::ExprDepType(res(r), y.clone(), z.clone()),
            T_::LambdaParam(x, r) => T_::LambdaParam(x.clone(), res(r)),
            T_::DynamicCoercion(r) => T_::DynamicCoercion(res(r)),
            T_::DynamicPartialEnforcement(x, y, r) => {
                T_::DynamicPartialEnforcement(x.clone(), y.clone(), res(r))
            }
            T_::RigidTvarEscape(x, y, z, r) => {
                T_::RigidTvarEscape(x.clone(), y.clone(), z.clone(), res(r))
            }
            T_::OpaqueTypeFromModule(x, y, r) => {
                T_::OpaqueTypeFromModule(x.clone(), y.clone(), res(r))
            }
            T_::SDTCall(x, r) => T_::SDTCall(x.clone(), res(r)),
            T_::LikeCall(x, r) => T_::LikeCall(x.clone(), res(r)),
            T_::NoReason => T_::NoReason,
            T_::Invalid => T_::Invalid,
            T_::MissingField => T_::MissingField,
            T_::Idx(x, y) => T_::Idx(x.clone(), y.clone()),
            T_::Flow { from, kind, into } => T_::Flow {
                from: res(from),
                kind: kind.clone(),
                into: res(into),
            },
            T_::Axiom { prev, axiom, next } => T_::Axiom {
                prev: res(prev),
                axiom: axiom.clone(),
                next: res(next),
            },
            T_::LowerBound { bound, of_ } => T_::LowerBound {
                bound: res(bound),
                of_: res(of_),
            },
            T_::Def(def, t) => T_::Def(def.clone(), res(t)),
            T_::PrjBoth {
                sub_prj,
                prj,
                sub,
                super_,
            } => T_::PrjBoth {
                sub_prj: res(sub_prj),
                prj: prj.clone(),
                sub: res(sub),
                super_: res(super_),
            },
            T_::PrjOne { part, prj, whole } => T_::PrjOne {
                part: res(part),
                prj: *prj,
                whole: res(whole),
            },
        }
    }

    /// Reasons are constructed by keeping track of preceding subtype
    /// propositions during subtype constraint simplification. We reach a child
    /// subtype proposition either through a projection into a type
    /// constructor or using some user-declared axiom.
    ///
    /// We can convert this to a list of derivation steps for each subtype
    /// constraint along with the term-level steps through which an expression
    /// was given its type.
    ///
    /// Since we also apply transitivity during constraint simplification, each
    /// reason may actually contain multiple subtype derivations. We reach a
    /// new derivation either because a upper- or lower-bound was added to a
    /// type variable and a new constraint generated for an exist lower- or
    /// upper-bound.
    ///
    /// This function is used to recover this representation from the reason
    /// representation.
    pub fn of_reason(
        sub: &T_,
        super_: &T_,
        is_derivation_suppressed: impl Fn(isize) -> bool,
    ) -> T {
        use std::rc::Rc;

        /// `aux (sub, super) ~deriv ~solutions ~depth`. `deriv` is the OCaml
        /// list in reverse (its head is the last element). The tail calls of
        /// the OCaml are the iterations of the loop.
        fn aux(
            (sub, super_): (&T_, &T_),
            deriv: Vec<subtype_step::T>,
            solutions: &Solutions,
            depth: isize,
            is_derivation_suppressed: &dyn Fn(isize) -> bool,
        ) -> T {
            let mut sub: Rc<T_> = Rc::new(sub.clone());
            let mut super_: Rc<T_> = Rc::new(super_.clone());
            let mut deriv = deriv;
            let mut solutions = solutions.clone();
            loop {
                let (next_sub, next_super) = match (&*sub, &*super_) {
                    // -- Accumulate solutions --
                    (
                        T_::Solved {
                            solution,
                            of_,
                            in_,
                        },
                        _,
                    ) => {
                        let solution = extract_first(&resolve(solution, 20, &solutions)).clone();
                        solutions = solutions.update(*of_, solution);
                        (in_.clone(), super_.clone())
                    }
                    (
                        _,
                        T_::Solved {
                            solution,
                            of_,
                            in_,
                        },
                    ) => {
                        let solution = extract_first(&resolve(solution, 20, &solutions)).clone();
                        solutions = solutions.update(*of_, solution);
                        (sub.clone(), in_.clone())
                    }
                    // -- Transitive constraints --
                    (
                        T_::LowerBound {
                            bound,
                            of_: ub_sub,
                        },
                        ub_super,
                    ) if matches!(&**bound, T_::LowerBound { .. }) => {
                        let T_::LowerBound {
                            bound: lb_sub,
                            of_: lb_super,
                        } = &**bound
                        else {
                            unreachable!()
                        };
                        let lower = nested(
                            (lb_sub, lb_super),
                            &solutions,
                            depth,
                            is_derivation_suppressed,
                        );
                        let upper = nested(
                            (ub_sub, ub_super),
                            &solutions,
                            depth,
                            is_derivation_suppressed,
                        );
                        let in_ = aux(
                            (lb_sub, ub_super),
                            deriv,
                            &solutions,
                            depth,
                            is_derivation_suppressed,
                        );
                        let on_ = extract_last(lb_super).clone();
                        return transitive(upper, lower, on_, in_);
                    }
                    (T_::LowerBound { bound, of_ }, super_) => {
                        let bound_ = nested((bound, of_), &solutions, depth, is_derivation_suppressed);
                        let in_ = aux(
                            (bound, super_),
                            deriv,
                            &solutions,
                            depth,
                            is_derivation_suppressed,
                        );
                        return lower_bound(bound_, in_);
                    }
                    (sub, T_::LowerBound { bound, of_ }) => {
                        let bound_ = nested((bound, of_), &solutions, depth, is_derivation_suppressed);
                        let in_ = aux(
                            (sub, bound),
                            deriv,
                            &solutions,
                            depth,
                            is_derivation_suppressed,
                        );
                        return lower_bound(bound_, in_);
                    }
                    // -- One-sided projection on subtype --
                    (T_::PrjOne { part, whole, prj }, _) => {
                        let step = {
                            let sub = push_solutions(part, &solutions);
                            let super_ = push_solutions(&super_, &solutions);
                            let rule = subtype_rule::using_prj_sub(*prj);
                            subtype_step::step(rule, subtype_step::Arg::Subtype, sub, super_)
                        };
                        deriv.push(step);
                        (whole.clone(), super_.clone())
                    }
                    (T_::Axiom { next, prev, axiom }, _) => {
                        let step = {
                            let sub = push_solutions(next, &solutions);
                            let super_ = push_solutions(&super_, &solutions);
                            let rule = subtype_rule::using_axiom_sub(axiom.clone());
                            subtype_step::step(rule, subtype_step::Arg::Subtype, sub, super_)
                        };
                        deriv.push(step);
                        (prev.clone(), super_.clone())
                    }
                    // -- One-sided projection on supertype --
                    (_, T_::PrjOne { part, whole, prj }) => {
                        let step = {
                            let sub = push_solutions(&sub, &solutions);
                            let super_ = push_solutions(part, &solutions);
                            let rule = subtype_rule::using_prj_super(*prj);
                            subtype_step::step(rule, subtype_step::Arg::Supertype, sub, super_)
                        };
                        deriv.push(step);
                        (sub.clone(), whole.clone())
                    }
                    (_, T_::Axiom { next, prev, axiom }) => {
                        let step = {
                            let sub = push_solutions(&sub, &solutions);
                            let super_ = push_solutions(next, &solutions);
                            let rule = subtype_rule::using_axiom_super(axiom.clone());
                            subtype_step::step(rule, subtype_step::Arg::Supertype, sub, super_)
                        };
                        deriv.push(step);
                        (sub.clone(), prev.clone())
                    }
                    // -- Two-sided projections --
                    (
                        T_::PrjBoth {
                            sub_prj,
                            sub: parent_sub,
                            super_: parent_super,
                            prj,
                        },
                        _,
                    ) => {
                        let step = {
                            let sub = push_solutions(sub_prj, &solutions);
                            let super_ = push_solutions(&super_, &solutions);
                            let rule = subtype_rule::using_prj(prj.clone());
                            subtype_step::step(rule, subtype_step::Arg::Both, sub, super_)
                        };
                        deriv.push(step);
                        (parent_sub.clone(), parent_super.clone())
                    }
                    (
                        _,
                        T_::PrjBoth {
                            sub_prj,
                            sub: parent_sub,
                            super_: parent_super,
                            prj,
                        },
                    ) => {
                        // Does this happen? Should it??
                        let step = {
                            let sub = push_solutions(&sub, &solutions);
                            let super_ = push_solutions(sub_prj, &solutions);
                            let rule = subtype_rule::using_prj(prj.clone());
                            subtype_step::step(rule, subtype_step::Arg::Both, sub, super_)
                        };
                        deriv.push(step);
                        (parent_sub.clone(), parent_super.clone())
                    }
                    // -- Reasons corresponding to a single step --
                    (
                        T_::NoReason
                        | T_::FromWitnessDecl(_)
                        | T_::FromWitnessLocl(_)
                        | T_::Instantiate { .. }
                        | T_::Flow { .. }
                        | T_::Def(..)
                        | T_::Invalid
                        | T_::MissingField
                        | T_::Idx(..)
                        | T_::ArithRetFloat(..)
                        | T_::ArithRetNum(..)
                        | T_::LostInfo(..)
                        | T_::Format(..)
                        | T_::Typeconst(..)
                        | T_::TypeAccess(..)
                        | T_::ExprDepType(..)
                        | T_::LambdaParam(..)
                        | T_::DynamicCoercion(_)
                        | T_::DynamicPartialEnforcement(..)
                        | T_::RigidTvarEscape(..)
                        | T_::OpaqueTypeFromModule(..)
                        | T_::SDTCall(..)
                        | T_::LikeCall(..),
                        T_::NoReason
                        | T_::FromWitnessDecl(_)
                        | T_::FromWitnessLocl(_)
                        | T_::Instantiate { .. }
                        | T_::Flow { .. }
                        | T_::Def(..)
                        | T_::Invalid
                        | T_::MissingField
                        | T_::Idx(..)
                        | T_::ArithRetFloat(..)
                        | T_::ArithRetNum(..)
                        | T_::LostInfo(..)
                        | T_::Format(..)
                        | T_::Typeconst(..)
                        | T_::TypeAccess(..)
                        | T_::ExprDepType(..)
                        | T_::LambdaParam(..)
                        | T_::DynamicCoercion(_)
                        | T_::DynamicPartialEnforcement(..)
                        | T_::RigidTvarEscape(..)
                        | T_::OpaqueTypeFromModule(..)
                        | T_::SDTCall(..)
                        | T_::LikeCall(..),
                    ) => {
                        let step = {
                            let sub = push_solutions(&sub, &solutions);
                            let super_ = push_solutions(&super_, &solutions);
                            subtype_step::begin_(sub, super_)
                        };
                        // `derivation (step :: deriv)`
                        deriv.push(step);
                        deriv.reverse();
                        return derivation(deriv);
                    }
                };
                sub = next_sub;
                super_ = next_super;
            }
        }

        /// A supporting derivation starts a separate path one level below its
        /// parent, so it must reset [deriv]. Check the renderer's depth policy
        /// before descending: suppressed branches have no observable
        /// explanation and need not be materialized.
        fn nested(
            (sub, super_): (&T_, &T_),
            solutions: &Solutions,
            depth: isize,
            is_derivation_suppressed: &dyn Fn(isize) -> bool,
        ) -> T {
            let depth = depth + 1;
            if is_derivation_suppressed(depth) {
                derivation(vec![])
            } else {
                aux(
                    (sub, super_),
                    vec![],
                    solutions,
                    depth,
                    is_derivation_suppressed,
                )
            }
        }

        aux(
            (sub, super_),
            vec![],
            &Solutions::new(),
            0,
            &is_derivation_suppressed,
        )
    }

    // ~~ Human-readable explanation of full derivation ~~~~~~~~~~~~~~~~~~~~~~~

    /// `Derivation.Explain`
    pub mod explain {
        use oxidized::explanation::Elem;
        use oxidized::pos_or_decl::PosOrDecl;

        use super::super::Expl;
        use super::T;
        use super::extract_last;
        use super::subtype_rule;
        use super::subtype_step;
        use crate::typing_reason::FlowKind;
        use crate::typing_reason::T_;
        use crate::typing_reason::WitnessDecl;
        use crate::typing_reason::WitnessLocl;
        use crate::typing_reason::to_pos;
        use crate::typing_reason::witness_decl_to_raw_pos;
        use crate::typing_reason::witness_locl_to_raw_pos;

        pub mod derivation_path {
            #[derive(Clone, Debug, PartialEq, Eq)]
            pub enum Elem {
                Main,
                Upper,
                Lower,
                Step(isize),
            }

            /// `[@@deriving eq]`
            pub fn equal_elem(a: &Elem, b: &Elem) -> bool {
                a == b
            }

            pub fn elem_to_string(elem: &Elem) -> String {
                match elem {
                    Elem::Main => "Main".to_string(),
                    Elem::Upper => "Upper".to_string(),
                    Elem::Lower => "Lower".to_string(),
                    Elem::Step(n) => format!("Step {}", n + 1),
                }
            }

            /// `elem list`, in the order of the OCaml list: the innermost
            /// element (the last one entered) first.
            pub type T = Vec<Elem>;

            /// `[@@deriving eq]`
            pub fn equal(a: &T, b: &T) -> bool {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| equal_elem(a, b))
            }

            pub fn explain(elems: &T) -> Option<String> {
                let mut acc: Option<String> = None;
                for elem in elems {
                    let part = elem_to_string(elem);
                    acc = Some(match acc {
                        None => part,
                        Some(acc) => format!("{} / {}", part, acc),
                    });
                }
                acc
            }
        }

        pub mod state {
            use oxidized::pos_or_decl::PosOrDecl;

            use super::derivation_path;

            #[derive(Clone, Debug)]
            pub struct T {
                /// `Pos_or_decl.Map.t` (`crate::pos_or_decl::map::T`)
                pub defs_seen: im::OrdMap<PosOrDecl, derivation_path::T>,
            }

            pub fn empty() -> T {
                T {
                    defs_seen: im::OrdMap::new(),
                }
            }

            pub fn def_seen(t: &mut T, pos: PosOrDecl, path: derivation_path::T) {
                t.defs_seen.insert(pos, path);
            }
        }

        pub mod config {

            use oxidized::pos_or_decl::PosOrDecl;

            use super::derivation_path;

            /// `Either.t`
            #[derive(Clone, Debug, PartialEq, Eq)]
            pub enum Either<A, B> {
                First(A),
                Second(B),
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub enum DefConfig {
                /// Always render a types definition whenever it appears
                Always,
                /// Render a types definition the first time it appears and
                /// provide a reference to it when it appear subsequently
                Once,
                /// Don't render definitions
                Never,
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub enum FlowConfig {
                /// Render all steps of a flow
                Full,
                /// Only render the start and endpoints of a flow
                Ends,
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub enum DerivConfig {
                /// Render only the top-level derivation
                Main,
                /// Render all transitive derivations
                All,
                /// Render derivations to a fixed depth
                Depth(isize),
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct T {
                pub def_config: DefConfig,
                pub flow_config: FlowConfig,
                pub deriv_config: DerivConfig,
                pub suppress_supportdyn: bool,
            }

            pub const VERBOSE: T = T {
                def_config: DefConfig::Always,
                flow_config: FlowConfig::Full,
                deriv_config: DerivConfig::All,
                suppress_supportdyn: false,
            };

            pub const CHATTY: T = T {
                def_config: DefConfig::Once,
                flow_config: FlowConfig::Full,
                deriv_config: DerivConfig::Depth(2),
                suppress_supportdyn: true,
            };

            pub const TERSE: T = T {
                def_config: DefConfig::Never,
                flow_config: FlowConfig::Ends,
                deriv_config: DerivConfig::Main,
                suppress_supportdyn: true,
            };

            pub fn from_complexity(complexity: isize) -> T {
                if complexity == 0 {
                    TERSE
                } else if complexity == 1 {
                    CHATTY
                } else {
                    VERBOSE
                }
            }

            pub fn suppress_derivation(t: &T, cur_depth: isize) -> bool {
                match t.deriv_config {
                    DerivConfig::All => false,
                    DerivConfig::Main => cur_depth > 0,
                    DerivConfig::Depth(max_depth) => cur_depth > max_depth,
                }
            }

            pub fn get_def(
                t: &T,
                pos: &PosOrDecl,
                seen: &im::OrdMap<PosOrDecl, derivation_path::T>,
            ) -> Option<Either<PosOrDecl, derivation_path::T>> {
                match t.def_config {
                    DefConfig::Never => None,
                    _ if t.suppress_supportdyn
                        && super::filename_suffix(pos) == "supportdynamic.hhi" =>
                    {
                        None
                    }
                    DefConfig::Always => Some(Either::First(pos.clone())),
                    DefConfig::Once => match seen.get(pos) {
                        Some(path) => Some(Either::Second(path.clone())),
                        None => Some(Either::First(pos.clone())),
                    },
                }
            }
        }

        pub mod context {
            use super::derivation_path;

            #[derive(Clone, Debug, PartialEq, Eq)]
            pub struct T {
                pub derivation_depth: isize,
                pub derivation_path: derivation_path::T,
                pub in_flow: bool,
            }

            pub fn empty() -> T {
                T {
                    derivation_depth: 0,
                    derivation_path: vec![],
                    in_flow: false,
                }
            }

            pub fn deepen(t: &T) -> T {
                T {
                    derivation_depth: t.derivation_depth + 1,
                    ..t.clone()
                }
            }

            pub fn enter(t: &T, elem: derivation_path::Elem) -> T {
                // `elem :: d`
                let mut derivation_path = Vec::with_capacity(t.derivation_path.len() + 1);
                derivation_path.push(elem);
                derivation_path.extend(t.derivation_path.iter().cloned());
                T {
                    derivation_path,
                    in_flow: false,
                    ..t.clone()
                }
            }

            pub fn enter_main(t: &T) -> T {
                enter(t, derivation_path::Elem::Main)
            }

            pub fn enter_upper(t: &T) -> T {
                enter(t, derivation_path::Elem::Upper)
            }

            pub fn enter_lower(t: &T) -> T {
                enter(t, derivation_path::Elem::Lower)
            }

            pub fn enter_step(t: &T, n: isize) -> T {
                enter(t, derivation_path::Elem::Step(n))
            }

            pub fn set_in_flow(t: &T) -> T {
                T {
                    in_flow: true,
                    ..t.clone()
                }
            }

            pub fn in_flow(t: &T) -> bool {
                t.in_flow
            }

            pub fn explain_path(t: &T) -> Option<String> {
                derivation_path::explain(&t.derivation_path)
            }

            pub fn is_toplevel(t: &T) -> bool {
                match t.derivation_path.as_slice() {
                    [] | [derivation_path::Elem::Main] => true,
                    _ => false,
                }
            }
        }

        // `Pos_or_decl.of_raw_pos`, `Pos_or_decl.is_hhi` and
        // `Relative_path.suffix (Pos_or_decl.filename pos)`, as
        // `crate::pos_or_decl` and `crate::relative_path` have them (those
        // modules are compiled only with the features `port` and `server`).

        /// `Pos_or_decl.of_raw_pos`
        fn of_raw_pos(p: oxidized::pos::Pos) -> PosOrDecl {
            p
        }

        /// `Pos_or_decl.is_hhi`
        fn is_hhi(p: &PosOrDecl) -> bool {
            p.filename().is_hhi()
        }

        /// `Relative_path.suffix (Pos_or_decl.filename p)`
        fn filename_suffix(p: &PosOrDecl) -> &str {
            p.filename().path_str()
        }

        fn with_suffix(ls: Expl, suffix: Elem<PosOrDecl>) -> Expl {
            let mut ls = ls;
            if !ls.is_empty() {
                // `hd :: suffix :: tl`
                ls.insert(1, suffix);
            }
            ls
        }

        fn explain_flow_kind(kind: &FlowKind) -> String {
            match kind {
                FlowKind::FlowArrayGet => "by the result of this array access".to_string(),
                FlowKind::FlowAssign => "via an assignment".to_string(),
                FlowKind::FlowCall => "as the return type of the function call".to_string(),
                FlowKind::FlowPropAccess => "as the type of the property".to_string(),
                FlowKind::FlowConstAccess => "as the type of the constant".to_string(),
                FlowKind::FlowLocal => "as the type of the local variable".to_string(),
                FlowKind::FlowFunReturn => "as the return hint".to_string(),
                FlowKind::FlowParamHint => "as the parameter hint".to_string(),
                FlowKind::FlowReturnExpr => "because it is used in a return position".to_string(),
                FlowKind::FlowInstantiate(nm) => {
                    format!("as the instantiation of the generic `{}`", nm)
                }
                FlowKind::FlowElab => "as the elaboration of".to_string(),
            }
        }

        fn sep() -> String {
            " ".to_string()
        }

        pub fn explain(
            t: &T,
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            match t {
                _ if config::suppress_derivation(cfg, ctxt.derivation_depth) => vec![],
                T::Derivation(steps) => explain_steps(steps, st, cfg, ctxt),
                T::Transitive {
                    lower,
                    upper,
                    in_,
                    on_,
                } => {
                    let expl_main = explain(in_, st, cfg, &context::enter_main(ctxt));
                    let ctxt = &context::deepen(ctxt);
                    let expl_lower = explain(lower, st, cfg, &context::enter_lower(ctxt));
                    let expl_upper = explain(upper, st, cfg, &context::enter_upper(ctxt));

                    let main_path = context::explain_path(&context::enter_main(ctxt))
                        .expect("Option.value_exn None");
                    let prefix_main = {
                        // The state this returns is dropped.
                        let middle = match explain_reason(on_, &mut st.clone(), cfg, ctxt)
                            .as_slice()
                        {
                            [Elem::Witness(_, x), ..] => x.clone(),
                            _ => "an inferred type".to_string(),
                        };
                        Elem::Trans(format!(
                            "I checked the subtype constraint in [{}] because it was implied by the other constraints on the {}.",
                            main_path, middle
                        ))
                    };
                    let prefix_lower = {
                        let lower_path = context::explain_path(&context::enter_lower(ctxt))
                            .expect("Option.value_exn None");
                        Elem::Trans(format!(
                            "I found the subtype for [{}] when I checked the subtype constraint in [{}].",
                            main_path, lower_path
                        ))
                    };
                    let prefix_upper = {
                        let upper_path = context::explain_path(&context::enter_upper(ctxt))
                            .expect("Option.value_exn None");
                        Elem::Trans(format!(
                            "I found the supertype for [{}] when I checked the subtype constraint in [{}].",
                            main_path, upper_path
                        ))
                    };
                    let mut expl = vec![prefix_main];
                    expl.extend(expl_main);
                    expl.push(prefix_lower);
                    expl.extend(expl_lower);
                    expl.push(prefix_upper);
                    expl.extend(expl_upper);
                    expl
                }
                T::Lower { bound, in_ } => {
                    let expl_main = explain(in_, st, cfg, &context::enter_main(ctxt));
                    let ctxt = &context::deepen(ctxt);
                    let expl_lower = explain(bound, st, cfg, &context::enter_lower(ctxt));
                    let main_path = context::explain_path(&context::enter_main(ctxt))
                        .expect("Option.value_exn None");
                    let prefix_main = Elem::Trans(format!(
                        "I checked the subtype constraint in [{}] because it was implied by transitivity.",
                        main_path
                    ));
                    let prefix_lower = {
                        let lower_path = context::explain_path(&context::enter_lower(ctxt))
                            .expect("Option.value_exn None");
                        Elem::Trans(format!(
                            "I found the subtype for [{}] is when I checked the subtype constraint in [{}].",
                            main_path, lower_path
                        ))
                    };
                    let mut expl = vec![prefix_main];
                    expl.extend(expl_main);
                    expl.push(prefix_lower);
                    expl.extend(expl_lower);
                    expl
                }
            }
        }

        fn explain_steps(
            steps: &[subtype_step::T],
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            let steps: Vec<&subtype_step::T> = if cfg.suppress_supportdyn {
                steps
                    .iter()
                    .filter(|step| !subtype_step::uses_supportdyn(step))
                    .collect()
            } else {
                steps.iter().collect()
            };
            let n_steps = steps.len() as isize;
            let path = context::explain_path(ctxt);
            let pfx = match path {
                None => "Step".to_string(),
                Some(path) => format!("[{}] Step", path),
            };
            let toplevel = context::is_toplevel(ctxt);
            // The explanations of the steps, one after the other (the fold
            // accumulates them in reverse and the `fold_right` appends them
            // back in order).
            let mut expl = vec![];
            for (idx, step) in steps.into_iter().enumerate() {
                let idx = idx as isize;
                expl.extend(explain_step(
                    step,
                    (idx, n_steps, &pfx, toplevel),
                    st,
                    cfg,
                    ctxt,
                ));
            }
            expl
        }

        fn explain_step(
            step: &subtype_step::T,
            (idx, n_steps, pfx, toplevel): (isize, isize, &str, bool),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            let ctxt = &context::enter_step(ctxt, idx);
            let (sub, super_, rule_opt, arg_opt) = match step {
                subtype_step::T::Begin { sub, super_ } => (sub, super_, None, None),
                subtype_step::T::Step {
                    sub,
                    super_,
                    rule,
                    on_,
                } => (sub, super_, Some(rule), Some(on_)),
            };

            let expl_sub = match (arg_opt, sub) {
                (Some(subtype_step::Arg::Supertype), _) => {
                    let pos = to_pos(sub);
                    vec![Elem::Witness(
                        pos,
                        "The subtype is the same as before.".to_string(),
                    )]
                }
                (_, T_::MissingField) => vec![Elem::WitnessNoPos(
                    "The subtype didn't exist because the field was missing.".to_string(),
                )],
                _ => {
                    let expl_sub = explain_reason(sub, st, cfg, ctxt);
                    let mut expl = vec![Elem::Prefix {
                        prefix: "The subtype comes from this".to_string(),
                        sep: sep(),
                    }];
                    expl.extend(expl_sub);
                    expl
                }
            };
            let expl_super = match (arg_opt, super_) {
                (Some(subtype_step::Arg::Subtype), _) => {
                    let pos = to_pos(super_);
                    vec![Elem::Witness(
                        pos,
                        "The supertype is the same as before.".to_string(),
                    )]
                }
                (_, T_::MissingField) => vec![Elem::WitnessNoPos(
                    "The supertype didn't exist because the field was missing.".to_string(),
                )],
                _ => {
                    let expl_super = explain_reason(super_, st, cfg, ctxt);
                    let prefix = Elem::Prefix {
                        prefix: "The supertype comes from this".to_string(),
                        sep: sep(),
                    };
                    let mut expl = vec![prefix];
                    expl.extend(expl_super);
                    expl
                }
            };

            let rule = Elem::Rule(match rule_opt {
                None => "I started by checking this subtype relationship.".to_string(),
                Some(rule) => subtype_rule::explain(rule),
            });

            let step = Elem::Step(
                format!("{} {} of {}", pfx, idx + 1, n_steps),
                toplevel && idx == n_steps - 1,
            );

            let mut expl = vec![step, rule];
            expl.extend(expl_sub);
            expl.extend(expl_super);
            expl
        }

        fn explain_reason(
            reason: &T_,
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            // The cases that only move to an inner reason are tail calls in
            // the OCaml: they are the iterations of this loop.
            let mut reason = reason;
            loop {
                return match reason {
                    // -- Expected 'atoms' in a derivation step --
                    T_::FromWitnessLocl(witness) => vec![explain_witness_locl(witness)],
                    T_::FromWitnessDecl(witness) => vec![explain_witness_decl(witness)],
                    T_::Def(pos, r) => explain_def((pos, r), st, cfg, ctxt),
                    T_::Flow { from, into, kind } => {
                        let into = match cfg.flow_config {
                            config::FlowConfig::Full => &**into,
                            config::FlowConfig::Ends => extract_last(into),
                        };
                        explain_flow((from, into, kind), st, cfg, ctxt)
                    }
                    T_::Solved { in_, .. } => {
                        reason = &**in_;
                        continue;
                    }
                    T_::MissingField => {
                        // This needs to be special cased in [explain_step]
                        vec![Elem::WitnessNoPos("missing field".to_string())]
                    }
                    // Special handling of legacy structured reasons
                    // TODO(mjt) translate to flow?
                    T_::Instantiate {
                        type_,
                        var_name,
                        var,
                    } => explain_instantiate(type_, var_name, var, st, cfg, ctxt),
                    T_::Idx(pos, r) => explain_idx((pos, r), st, cfg, ctxt),
                    T_::ArithRetFloat(pos, r, arg_pos) => {
                        explain_arith_ret_float((pos, r, arg_pos), st, cfg, ctxt)
                    }
                    T_::ArithRetNum(pos, r, arg_pos) => {
                        explain_arith_ret_num((pos, r, arg_pos), st, cfg, ctxt)
                    }
                    T_::LostInfo(nm, r, blame) => {
                        explain_lost_info((nm, r, blame), st, cfg, ctxt)
                    }
                    T_::Format(pos, nm, r) => explain_format((pos, nm, r), st, cfg, ctxt),
                    T_::Typeconst(r1, rs, str, r2) => {
                        explain_typeconst((r1, rs, str, r2), st, cfg, ctxt)
                    }
                    T_::TypeAccess(r, rs) => explain_type_access((r, rs), st, cfg, ctxt),
                    T_::ExprDepType(r, pos, expr_dep_type_reason) => {
                        explain_expr_dep_type((r, pos, expr_dep_type_reason), st, cfg, ctxt)
                    }
                    T_::LambdaParam(pos, r) => explain_lambda_param((pos, r), st, cfg, ctxt),
                    T_::DynamicCoercion(r) => explain_dynamic_coercion(r, st, cfg, ctxt),
                    T_::DynamicPartialEnforcement(pos, nm, r) => {
                        explain_dynamic_partial_enforcement((pos, nm, r), st, cfg, ctxt)
                    }
                    T_::RigidTvarEscape(pos, str1, str2, r) => {
                        explain_rigid_tvar_escape((pos, str1, str2, r), st, cfg, ctxt)
                    }
                    T_::OpaqueTypeFromModule(pos, str, r) => {
                        explain_opaque_type_from_module((pos, str, r), st, cfg, ctxt)
                    }
                    T_::SDTCall(pos, r) => explain_sdt_call((pos, r), st, cfg, ctxt),
                    T_::LikeCall(pos, r) => explain_like_call((pos, r), st, cfg, ctxt),
                    // Its possible that one of the following remains in the
                    // derivation since we can have `Prj_one` in both subtype
                    // and supertype or `Prj_both` as subtype and `Prj_one` in
                    // supertype and we will always follow `Prj_one` before
                    // moving into `Prj_both`
                    T_::LowerBound { of_, .. } => {
                        reason = &**of_;
                        continue;
                    }
                    T_::PrjBoth { sub_prj, .. } => {
                        reason = &**sub_prj;
                        continue;
                    }
                    T_::PrjOne { part, .. } => {
                        reason = &**part;
                        continue;
                    }
                    T_::Axiom { next, .. } => {
                        reason = &**next;
                        continue;
                    }
                    // We have no provenance information
                    T_::NoReason | T_::Invalid => {
                        vec![Elem::WitnessNoPos("this element".to_string())]
                    }
                };
            }
        }

        fn explain_witness_locl(witness: &WitnessLocl) -> Elem<PosOrDecl> {
            match witness {
                WitnessLocl::IsRefinement(pos) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "`is` expression".to_string())
                }
                WitnessLocl::Witness(pos) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "expression".to_string())
                }
                WitnessLocl::TypeVariable(pos, _id) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "type variable".to_string())
                }
                WitnessLocl::TypeVariableGenerics(pos, x, y, _id) => Elem::Witness(
                    of_raw_pos(pos.clone()),
                    format!("generic parameter `{}` of `{}`", x, y),
                ),
                WitnessLocl::UnpackParam(pos, _, _) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "unpacked parameter".to_string())
                }
                WitnessLocl::Bitwise(pos) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "expression".to_string())
                }
                WitnessLocl::Arith(pos) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "arithmetic expression".to_string())
                }
                WitnessLocl::IdxVector(pos) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "index expression".to_string())
                }
                WitnessLocl::Splice(pos) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "splice expression".to_string())
                }
                WitnessLocl::NoReturn(pos) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "declaration".to_string())
                }
                WitnessLocl::ShapeLiteral(pos) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "`shape` literal".to_string())
                }
                WitnessLocl::Destructure(pos) => Elem::Witness(
                    of_raw_pos(pos.clone()),
                    "destructure expression".to_string(),
                ),
                WitnessLocl::ShapeOrTupleDestructure(pos) => Elem::Witness(
                    of_raw_pos(pos.clone()),
                    "shape or tuple destructuring pattern".to_string(),
                ),
                WitnessLocl::JoinPoint(pos) => {
                    Elem::Witness(of_raw_pos(pos.clone()), "join point".to_string())
                }
                WitnessLocl::StaticPropertyAccess(pos) => Elem::Witness(
                    of_raw_pos(pos.clone()),
                    "static property access expression".to_string(),
                ),
                WitnessLocl::ClassConstantAccess(pos) => Elem::Witness(
                    of_raw_pos(pos.clone()),
                    "class constant access expression".to_string(),
                ),
                _ => Elem::Witness(witness_locl_to_raw_pos(witness), "element".to_string()),
            }
        }

        fn explain_witness_decl(witness: &WitnessDecl) -> Elem<PosOrDecl> {
            match witness {
                WitnessDecl::Hint(pos) => Elem::Witness(pos.clone(), "hint".to_string()),
                WitnessDecl::WitnessFromDecl(pos) => {
                    Elem::Witness(pos.clone(), "declaration".to_string())
                }
                WitnessDecl::SupportDynamicType(pos) => Elem::Witness(
                    pos.clone(),
                    "function or method declaration".to_string(),
                ),
                WitnessDecl::PessimisedInout(pos) => {
                    Elem::Witness(pos.clone(), "`inout` parameter".to_string())
                }
                WitnessDecl::PessimisedProp(pos, _) => {
                    Elem::Witness(pos.clone(), "property".to_string())
                }
                WitnessDecl::PessimisedThis(pos) => {
                    Elem::Witness(pos.clone(), "`this` hint".to_string())
                }
                WitnessDecl::PessimisedReturn(pos, _) => {
                    Elem::Witness(pos.clone(), "return hint".to_string())
                }
                WitnessDecl::VarParamFromDecl(pos) => Elem::Witness(
                    pos.clone(),
                    "variadic parameter declaration".to_string(),
                ),
                WitnessDecl::TupleFromSplat(pos) => {
                    Elem::Witness(pos.clone(), "tuple from parameters".to_string())
                }
                WitnessDecl::CstrOnGenerics(pos, _) => Elem::Witness(
                    pos.clone(),
                    "constraint on the generic parameter".to_string(),
                ),
                WitnessDecl::ImplicitUpperBound(pos, nm) => Elem::Witness(
                    pos.clone(),
                    format!("implicit upper bound (`{}`) on the generic parameter", nm),
                ),
                WitnessDecl::ClassClass(pos, nm) => Elem::Witness(
                    pos.clone(),
                    format!("implicitly defined constant `::class` of class `{}`", nm),
                ),
                _ => Elem::Witness(witness_decl_to_raw_pos(witness), "declaration".to_string()),
            }
        }

        fn explain_def(
            (pos, reason): (&PosOrDecl, &T_),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            let expl_reason = explain_reason(reason, st, cfg, ctxt);
            match config::get_def(cfg, pos, &st.defs_seen) {
                None => expl_reason,
                Some(config::Either::Second(seen_at)) => {
                    if derivation_path::equal(&seen_at, &ctxt.derivation_path) {
                        let suffix = Elem::Suffix {
                            suffix: "(its definition was given above)".to_string(),
                            sep: sep(),
                        };
                        with_suffix(expl_reason, suffix)
                    } else {
                        match derivation_path::explain(&seen_at) {
                            None => expl_reason,
                            Some(path) => {
                                let suffix = Elem::Suffix {
                                    suffix: format!("(its definition was given in [{}])", path),
                                    sep: sep(),
                                };
                                with_suffix(expl_reason, suffix)
                            }
                        }
                    }
                }
                Some(config::Either::First(pos)) => {
                    // Suppress the 'definition' of supportdyn
                    if cfg.suppress_supportdyn
                        && is_hhi(&pos)
                        && filename_suffix(&pos).contains("supportdynamic")
                    {
                        expl_reason
                    } else {
                        state::def_seen(st, pos.clone(), ctxt.derivation_path.clone());
                        let mut expl = expl_reason;
                        expl.push(Elem::Witness(pos, "which is defined here".to_string()));
                        expl
                    }
                }
            }
        }

        fn explain_flow(
            (from, into, kind): (&T_, &T_, &FlowKind),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            let expl_from = explain_reason(from, st, cfg, ctxt);
            let expl_into = explain_reason(into, st, cfg, &context::set_in_flow(ctxt));
            let suffix = Elem::Suffix {
                suffix: explain_flow_kind(kind),
                sep: sep(),
            };
            let prefix = Elem::Prefix {
                prefix: if context::in_flow(ctxt) {
                    "which itself flows into this".to_string()
                } else {
                    "and flows into this".to_string()
                },
                sep: sep(),
            };
            let mut expl = expl_from;
            expl.push(prefix);
            expl.extend(with_suffix(expl_into, suffix));
            expl
        }

        fn explain_instantiate(
            type_: &T_,
            var_name: &str,
            var: &T_,
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_flow(
                (type_, var, &FlowKind::FlowInstantiate(var_name.to_string())),
                st,
                cfg,
                ctxt,
            )
        }

        fn explain_idx(
            (pos, _r): (&oxidized::pos::Pos, &T_),
            _st: &mut state::T,
            _cfg: &config::T,
            _ctxt: &context::T,
        ) -> Expl {
            vec![Elem::Witness(
                of_raw_pos(pos.clone()),
                "index expression".to_string(),
            )]
        }

        fn explain_arith_ret_float(
            (pos, _r, _arg_pos): (&oxidized::pos::Pos, &T_, &crate::typing_reason::ArgPosition),
            _st: &mut state::T,
            _cfg: &config::T,
            _ctxt: &context::T,
        ) -> Expl {
            vec![Elem::Witness(
                of_raw_pos(pos.clone()),
                "arithmetic expression".to_string(),
            )]
        }

        fn explain_arith_ret_num(
            (pos, _r, _arg_pos): (&oxidized::pos::Pos, &T_, &crate::typing_reason::ArgPosition),
            _st: &mut state::T,
            _cfg: &config::T,
            _ctxt: &context::T,
        ) -> Expl {
            vec![Elem::Witness(
                of_raw_pos(pos.clone()),
                "arithmetic expression".to_string(),
            )]
        }

        fn explain_lost_info(
            (_nm, r, _blame): (&String, &T_, &crate::typing_reason::Blame),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_reason(r, st, cfg, ctxt)
        }

        fn explain_format(
            (pos, _nm, _r): (&oxidized::pos::Pos, &String, &T_),
            _st: &mut state::T,
            _cfg: &config::T,
            _ctxt: &context::T,
        ) -> Expl {
            vec![Elem::Witness(
                of_raw_pos(pos.clone()),
                "format expression".to_string(),
            )]
        }

        fn explain_typeconst(
            (_r1, (pos, _), _str, _t2): (
                &T_,
                &(PosOrDecl, String),
                &crate::typing_reason::LazyString,
                &T_,
            ),
            _st: &mut state::T,
            _cfg: &config::T,
            _ctxt: &context::T,
        ) -> Expl {
            vec![Elem::Witness(pos.clone(), "this type constant".to_string())]
        }

        fn explain_type_access(
            (r, _rs): (&T_, &[(crate::typing_reason::T, crate::typing_reason::LazyString)]),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_reason(r, st, cfg, ctxt)
        }

        fn explain_expr_dep_type(
            (r, _pos, _expr_dep_type_reason): (
                &T_,
                &PosOrDecl,
                &crate::typing_reason::ExprDepTypeReason,
            ),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_reason(r, st, cfg, ctxt)
        }

        fn explain_lambda_param(
            (pos, _r): (&oxidized::pos::Pos, &T_),
            _st: &mut state::T,
            _cfg: &config::T,
            _ctxt: &context::T,
        ) -> Expl {
            vec![Elem::Witness(
                of_raw_pos(pos.clone()),
                "lambda parameter".to_string(),
            )]
        }

        fn explain_dynamic_coercion(
            r: &T_,
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_reason(r, st, cfg, ctxt)
        }

        fn explain_dynamic_partial_enforcement(
            (_pos, _nm, r): (&PosOrDecl, &String, &T_),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_reason(r, st, cfg, ctxt)
        }

        fn explain_rigid_tvar_escape(
            (_pos, _str1, _str2, r): (&oxidized::pos::Pos, &String, &String, &T_),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_reason(r, st, cfg, ctxt)
        }

        fn explain_opaque_type_from_module(
            (_pos, _str, r): (&PosOrDecl, &String, &T_),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_reason(r, st, cfg, ctxt)
        }

        fn explain_sdt_call(
            (_pos, r): (&PosOrDecl, &T_),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_reason(r, st, cfg, ctxt)
        }

        fn explain_like_call(
            (_pos, r): (&PosOrDecl, &T_),
            st: &mut state::T,
            cfg: &config::T,
            ctxt: &context::T,
        ) -> Expl {
            explain_reason(r, st, cfg, ctxt)
        }
    }

    /// `Derivation.explain ~sub ~super ~complexity`
    pub fn explain(sub: &T_, super_: &T_, complexity: isize) -> super::Expl {
        let mut st = explain::state::empty();
        let cfg = explain::config::from_complexity(complexity);
        let ctxt = explain::context::empty();
        let deriv = of_reason(sub, super_, |cur_depth| {
            explain::config::suppress_derivation(&cfg, cur_depth)
        });
        explain::explain(&deriv, &mut st, &cfg, &ctxt)
    }
}

/// `Typing_reason.explain ~sub ~super ~complexity`
pub fn explain(sub: &T_, super_: &T_, complexity: isize) -> Explanation<PosOrDecl> {
    Explanation::Derivation(derivation::explain(sub, super_, complexity))
}

/// `Typing_reason.debug_reason ~sub ~super`
#[cfg(any(feature = "port", feature = "server"))]
pub fn debug_reason(sub: &T_, super_: &T_) -> Explanation<PosOrDecl> {
    let json = Json::Assoc(vec![(
        "Subtype".to_string(),
        Json::Assoc(vec![
            ("sub".to_string(), to_json(sub)),
            ("super".to_string(), to_json(super_)),
        ]),
    )]);
    Explanation::Debug(yojson_safe_pretty_to_string(&json))
}

/// `Typing_reason.debug_reason ~sub ~super`, in the build without the
/// features `port` and `server` (which have the JSON).
#[cfg(not(any(feature = "port", feature = "server")))]
pub fn debug_reason(_sub: &T_, _super_: &T_) -> Explanation<PosOrDecl> {
    todo!("Typing_reason.debug_reason: Yojson (crate::yojson) is compiled only with the features port and server")
}

/// `Typing_reason.debug_derivation ~sub ~super`
#[cfg(any(feature = "port", feature = "server"))]
pub fn debug_derivation(sub: &T_, super_: &T_) -> Explanation<PosOrDecl> {
    let json = derivation::to_json(&derivation::of_reason(sub, super_, |_| false));
    Explanation::Debug(yojson_safe_pretty_to_string(&json))
}

/// `Typing_reason.debug_derivation ~sub ~super`, in the build without the
/// features `port` and `server` (which have the JSON).
#[cfg(not(any(feature = "port", feature = "server")))]
pub fn debug_derivation(_sub: &T_, _super_: &T_) -> Explanation<PosOrDecl> {
    todo!("Typing_reason.debug_derivation: Yojson (crate::yojson) is compiled only with the features port and server")
}

#[cfg(test)]
mod tests {
    //! The sequences of elements were checked against the expected outputs of
    //! `hphp/hack/test/extended_reasons` where a comment names a file (the
    //! renderer prints one element per paragraph); the others follow the
    //! OCaml.

    use std::rc::Rc;
    use std::sync::Arc;

    use oxidized::explanation::Elem;
    use oxidized::pos::Pos;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::derivation::subtype_rule;
    use super::*;
    use crate::typing_reason::FlowKind;
    use crate::typing_reason::WitnessDecl;
    use crate::typing_reason::WitnessLocl;

    fn pos_in(prefix: Prefix, file: &str, line: usize) -> Pos {
        let file = Arc::new(RelativePath::make(prefix, file.into()));
        Pos::from_line_cols_offset(file, line, 0..1, line * 100)
    }

    /// A position on line `line` of `a.php`.
    fn p(line: usize) -> Pos {
        pos_in(Prefix::Root, "a.php", line)
    }

    fn expr(line: usize) -> T_ {
        T_::FromWitnessLocl(WitnessLocl::Witness(p(line)))
    }

    fn hint(line: usize) -> T_ {
        T_::FromWitnessDecl(WitnessDecl::Hint(p(line)))
    }

    fn flow(from: T_, kind: FlowKind, into: T_) -> T_ {
        T_::Flow {
            from: std::rc::Rc::new(from),
            kind,
            into: std::rc::Rc::new(into),
        }
    }

    fn w(pos: Pos, s: &str) -> Elem<PosOrDecl> {
        Elem::Witness(pos, s.to_string())
    }

    fn prefix(s: &str) -> Elem<PosOrDecl> {
        Elem::Prefix {
            prefix: s.to_string(),
            sep: " ".to_string(),
        }
    }

    fn suffix(s: &str) -> Elem<PosOrDecl> {
        Elem::Suffix {
            suffix: s.to_string(),
            sep: " ".to_string(),
        }
    }

    fn step(s: &str, is_error: bool) -> Elem<PosOrDecl> {
        Elem::Step(s.to_string(), is_error)
    }

    fn rule(s: &str) -> Elem<PosOrDecl> {
        Elem::Rule(s.to_string())
    }

    fn trans(s: &str) -> Elem<PosOrDecl> {
        Elem::Trans(s.to_string())
    }

    const START: &str = "I started by checking this subtype relationship.";

    fn elems(sub: &T_, super_: &T_, complexity: isize) -> Vec<Elem<PosOrDecl>> {
        match explain(sub, super_, complexity) {
            Explanation::Derivation(elems) => elems,
            e => panic!("expected a derivation, got {:?}", e),
        }
    }

    #[test]
    fn ordinals() {
        let o = subtype_rule::int_to_ordinal;
        assert_eq!(o(1), "1st");
        assert_eq!(o(2), "2nd");
        assert_eq!(o(3), "3rd");
        assert_eq!(o(4), "4th");
        assert_eq!(o(9), "9th");
        assert_eq!(o(10), "10th");
        assert_eq!(o(11), "11th");
        assert_eq!(o(13), "13th");
        assert_eq!(o(20), "20th");
        assert_eq!(o(21), "21st");
        assert_eq!(o(23), "23rd");
        // As the OCaml has it: only 10 to 20 are special.
        assert_eq!(o(111), "111st");
    }

    #[test]
    fn rules() {
        let e = |r| subtype_rule::explain(&r);
        // test/extended_reasons/vector_invariant.php.exp
        assert_eq!(
            e(subtype_rule::using_prj(PrjSymm::PrjSymmCtor(
                CtorKind::CtorClass,
                "\\HH\\Vector".to_string(),
                0,
                CstrVariance::Inv(VarianceDir::Co)
            ))),
            "`Vector` is a class or interface so next I checked the 1st type arguments are subtypes.\nThe type parameter is invariant so the subtype relationship must hold in both directions.\nHere I check the covariant case."
        );
        assert_eq!(
            e(subtype_rule::using_prj(PrjSymm::PrjSymmFnParam(1, 2))),
            "These are function types so next I checked the 2nd function parameter of the subtype and the 3rd parameter of the supertype.\nFunctions are contravariant in their parameters the direction of the subtype relationship is reversed."
        );
        // The parameter of the supertype first.
        assert_eq!(
            e(subtype_rule::using_prj(PrjSymm::PrjSymmFnParamInout(
                0,
                1,
                VarianceDir::Contra
            ))),
            "These are function types so next I checked the 2nd function parameter of the supertype and the 1st parameter of the subtype. These are `inout` parameters which are invariant. This means the relation must hold in both directions.\nHere I checked the contravariant case so the direction of the subtype relationship is reversed."
        );
        // `Absent` on both sides is the first case.
        assert_eq!(
            e(subtype_rule::using_prj(PrjSymm::PrjSymmShape(
                "a".to_string(),
                FieldKind::Absent,
                FieldKind::Absent
            ))),
            "These are shape types so next I tried to check the `a` field.\nThe field is missing in the supertype but missing in the subtype."
        );
        assert_eq!(
            e(subtype_rule::using_prj(PrjSymm::PrjSymmShape(
                "a".to_string(),
                FieldKind::Optional,
                FieldKind::Optional
            ))),
            "These are shape types so next I checked the optional `a` field."
        );
        assert_eq!(
            e(subtype_rule::using_prj(PrjSymm::PrjSymmShape(
                "a".to_string(),
                FieldKind::Optional,
                FieldKind::Required
            ))),
            "These are shape types so next I checked the `a` field.\nThe field was optional in the subtype and required in the supertype."
        );
        assert_eq!(
            e(subtype_rule::using_axiom_super(Axiom::UpperBound(
                "T".to_string()
            ))),
            "The supertype declares an upper bound so next I checked that was a supertype of the subtype."
        );
        assert_eq!(
            e(subtype_rule::using_prj_super(PrjAsymm::PrjAsymmInter)),
            "The supertype is an intersection type so next I checked the subtype constraint is satsified for all of its elements."
        );
    }

    /// test/extended_reasons/num.php.exp (the first error)
    #[test]
    fn num() {
        let string_hhi = pos_in(Prefix::Hhi, "string.hhi", 6);
        let arith = || {
            flow(
                T_::ArithRetNum(p(9), Rc::new(T_::NoReason), super::super::ArgPosition::Asecond),
                FlowKind::FlowReturnExpr,
                expr(90),
            )
        };
        let sub = T_::PrjOne {
            part: Rc::new(arith()),
            whole: Rc::new(arith()),
            prj: PrjAsymm::PrjAsymmNum,
        };
        let super_ = T_::Def(string_hhi.clone(), Rc::new(hint(3)));
        let flowed = vec![
            prefix("The subtype comes from this"),
            w(p(9), "arithmetic expression"),
            prefix("and flows into this"),
            w(p(90), "expression"),
            suffix("because it is used in a return position"),
        ];
        let mut expected = vec![step("Step 1 of 2", false), rule(START)];
        expected.extend(flowed.clone());
        expected.extend(vec![
            prefix("The supertype comes from this"),
            w(p(3), "hint"),
            w(string_hhi, "which is defined here"),
            step("Step 2 of 2", true),
            rule(
                "The subtype is a num type so next I checked the subtype constraint is satisfied for both the int and float parts.",
            ),
        ]);
        expected.extend(flowed);
        expected.push(w(p(3), "The supertype is the same as before."));
        assert_eq!(elems(&sub, &super_, 1), expected);
    }

    /// The flows of test/extended_reasons/vector_invariant.php.exp
    #[test]
    fn flows() {
        let sub = flow(
            expr(4),
            FlowKind::FlowAssign,
            flow(expr(40), FlowKind::FlowLocal, expr(5)),
        );
        let super_ = hint(3);
        assert_eq!(
            elems(&sub, &super_, 1),
            vec![
                step("Step 1 of 1", true),
                rule(START),
                prefix("The subtype comes from this"),
                w(p(4), "expression"),
                prefix("and flows into this"),
                w(p(40), "expression"),
                suffix("via an assignment"),
                prefix("which itself flows into this"),
                w(p(5), "expression"),
                suffix("as the type of the local variable"),
                prefix("The supertype comes from this"),
                w(p(3), "hint"),
            ]
        );
        // Terse: only the ends of a flow.
        assert_eq!(
            elems(&sub, &super_, 0),
            vec![
                step("Step 1 of 1", true),
                rule(START),
                prefix("The subtype comes from this"),
                w(p(4), "expression"),
                prefix("and flows into this"),
                w(p(5), "expression"),
                suffix("via an assignment"),
                prefix("The supertype comes from this"),
                w(p(3), "hint"),
            ]
        );
    }

    /// The structure of test/extended_reasons/vector_invariant.php.exp
    #[test]
    fn transitive() {
        let generic = T_::FromWitnessLocl(WitnessLocl::TypeVariableGenerics(
            p(41),
            "T".to_string(),
            "HH\\Vector".to_string(),
            3,
        ));
        let sub = T_::LowerBound {
            bound: Rc::new(T_::LowerBound {
                bound: Rc::new(expr(4)),
                of_: Rc::new(generic.clone()),
            }),
            of_: Rc::new(expr(42)),
        };
        let super_ = hint(3);
        let expected = vec![
            trans(
                "I checked the subtype constraint in [Main] because it was implied by the other constraints on the generic parameter `T` of `HH\\Vector`.",
            ),
            step("[Main] Step 1 of 1", true),
            rule(START),
            prefix("The subtype comes from this"),
            w(p(4), "expression"),
            prefix("The supertype comes from this"),
            w(p(3), "hint"),
            trans("I found the subtype for [Main] when I checked the subtype constraint in [Lower]."),
            step("[Lower] Step 1 of 1", false),
            rule(START),
            prefix("The subtype comes from this"),
            w(p(4), "expression"),
            prefix("The supertype comes from this"),
            w(p(41), "generic parameter `T` of `HH\\Vector`"),
            trans("I found the supertype for [Main] when I checked the subtype constraint in [Upper]."),
            step("[Upper] Step 1 of 1", false),
            rule(START),
            prefix("The subtype comes from this"),
            w(p(42), "expression"),
            prefix("The supertype comes from this"),
            w(p(3), "hint"),
        ];
        assert_eq!(elems(&sub, &super_, 1), expected);
        // Terse: the supporting derivations are not explained, but their
        // headings are.
        assert_eq!(
            elems(&sub, &super_, 0),
            expected
                .iter()
                .enumerate()
                .filter(|(i, _)| *i < 8 || *i == 14)
                .map(|(_, e)| e.clone())
                .collect::<Vec<_>>()
        );
        // A lower bound on its own.
        let sub = T_::LowerBound {
            bound: Rc::new(expr(4)),
            of_: Rc::new(generic),
        };
        let lower = elems(&sub, &super_, 1);
        assert_eq!(
            lower[0],
            trans("I checked the subtype constraint in [Main] because it was implied by transitivity.")
        );
        assert_eq!(
            lower[7],
            trans(
                "I found the subtype for [Main] is when I checked the subtype constraint in [Lower]."
            )
        );
    }

    #[test]
    fn definition_seen_before() {
        let def = pos_in(Prefix::Hhi, "classes.hhi", 7);
        let super_ = T_::PrjOne {
            part: Rc::new(T_::Def(def.clone(), Rc::new(hint(3)))),
            whole: Rc::new(T_::Def(def.clone(), Rc::new(hint(4)))),
            prj: PrjAsymm::PrjAsymmNullable,
        };
        let sub = expr(1);
        let expected = vec![
            step("Step 1 of 2", false),
            rule(START),
            prefix("The subtype comes from this"),
            w(p(1), "expression"),
            prefix("The supertype comes from this"),
            w(p(4), "hint"),
            w(def.clone(), "which is defined here"),
            step("Step 2 of 2", true),
            rule(
                "The supertype is a nullable type so next I checked the subtype constraint is satisfied for either the null or non-null part.",
            ),
            w(p(1), "The subtype is the same as before."),
            prefix("The supertype comes from this"),
            w(p(3), "hint"),
            suffix("(its definition was given in [Step 1])"),
        ];
        assert_eq!(elems(&sub, &super_, 1), expected);
        // Verbose: always given.
        let verbose = elems(&sub, &super_, 2);
        assert_eq!(verbose[12], w(def, "which is defined here"));
    }

    #[test]
    fn supportdyn() {
        let supportdynamic = pos_in(Prefix::Hhi, "supportdynamic.hhi", 2);
        let sub = T_::PrjBoth {
            sub_prj: Rc::new(expr(5)),
            prj: PrjSymm::PrjSymmSupportdyn,
            sub: Rc::new(expr(1)),
            super_: Rc::new(T_::Def(supportdynamic.clone(), Rc::new(hint(2)))),
        };
        let super_ = hint(3);
        // The step through `supportdyn` and the definition of `supportdyn`
        // are left out.
        assert_eq!(
            elems(&sub, &super_, 1),
            vec![
                step("Step 1 of 1", true),
                rule(START),
                prefix("The subtype comes from this"),
                w(p(1), "expression"),
                prefix("The supertype comes from this"),
                w(p(2), "hint"),
            ]
        );
        assert_eq!(
            elems(&sub, &super_, 2),
            vec![
                step("Step 1 of 2", false),
                rule(START),
                prefix("The subtype comes from this"),
                w(p(1), "expression"),
                prefix("The supertype comes from this"),
                w(p(2), "hint"),
                w(supportdynamic, "which is defined here"),
                step("Step 2 of 2", true),
                rule("These are `supportdyn` types so next I checked the non-dynamic parts."),
                prefix("The subtype comes from this"),
                w(p(5), "expression"),
                prefix("The supertype comes from this"),
                w(p(3), "hint"),
            ]
        );
    }

    #[test]
    fn solved() {
        let sub = T_::Solved {
            solution: Rc::new(flow(expr(8), FlowKind::FlowLocal, expr(9))),
            of_: 7,
            in_: Rc::new(T_::FromWitnessLocl(WitnessLocl::TypeVariable(p(2), 7))),
        };
        let super_ = T_::MissingField;
        // The solution, `extract_first`ed, replaces the type variable.
        assert_eq!(
            elems(&sub, &super_, 1),
            vec![
                step("Step 1 of 1", true),
                rule(START),
                prefix("The subtype comes from this"),
                w(p(8), "expression"),
                Elem::WitnessNoPos(
                    "The supertype didn't exist because the field was missing.".to_string()
                ),
            ]
        );
        // A type variable without a solution stays.
        let sub = T_::FromWitnessLocl(WitnessLocl::TypeVariable(p(2), 7));
        assert_eq!(elems(&sub, &super_, 1)[3], w(p(2), "type variable"));
    }

    /// The state that the explanation of `on_` returns, for the heading of a
    /// `Transitive`, is dropped (OCaml: `match explain_reason on_ ~st ... with
    /// (..., _)`): a definition seen only there is given again, in full, by a
    /// later derivation.
    #[test]
    fn transitive_heading_drops_state() {
        use super::derivation::explain::config;
        use super::derivation::explain::context;
        use super::derivation::explain::state;
        use super::derivation::subtype_step;

        let def = pos_in(Prefix::Hhi, "classes.hhi", 7);
        let begin = |sub: T_, super_: T_| derivation::derivation(vec![subtype_step::begin_(sub, super_)]);
        let inner = derivation::transitive(
            derivation::derivation(vec![]),
            derivation::derivation(vec![]),
            T_::Def(def.clone(), Rc::new(hint(5))),
            begin(expr(3), hint(4)),
        );
        let deriv = derivation::transitive(
            begin(T_::Def(def.clone(), Rc::new(hint(6))), hint(7)),
            inner,
            expr(8),
            begin(expr(1), hint(2)),
        );
        let mut st = state::empty();
        let expl = derivation::explain::explain(
            &deriv,
            &mut st,
            &config::CHATTY,
            &context::empty(),
        );
        let expected = vec![
            trans(
                "I checked the subtype constraint in [Main] because it was implied by the other constraints on the expression.",
            ),
            step("[Main] Step 1 of 1", true),
            rule(START),
            prefix("The subtype comes from this"),
            w(p(1), "expression"),
            prefix("The supertype comes from this"),
            w(p(2), "hint"),
            trans("I found the subtype for [Main] when I checked the subtype constraint in [Lower]."),
            trans(
                "I checked the subtype constraint in [Lower / Main] because it was implied by the other constraints on the hint.",
            ),
            step("[Lower / Main] Step 1 of 1", false),
            rule(START),
            prefix("The subtype comes from this"),
            w(p(3), "expression"),
            prefix("The supertype comes from this"),
            w(p(4), "hint"),
            trans(
                "I found the subtype for [Lower / Main] when I checked the subtype constraint in [Lower / Lower].",
            ),
            trans(
                "I found the supertype for [Lower / Main] when I checked the subtype constraint in [Lower / Upper].",
            ),
            trans("I found the supertype for [Main] when I checked the subtype constraint in [Upper]."),
            step("[Upper] Step 1 of 1", false),
            rule(START),
            prefix("The subtype comes from this"),
            w(p(6), "hint"),
            // Not "(its definition was given in [Lower])".
            w(def.clone(), "which is defined here"),
            prefix("The supertype comes from this"),
            w(p(7), "hint"),
        ];
        assert_eq!(expl, expected);
        // The definition was recorded by the last derivation only.
        assert_eq!(
            st.defs_seen.get(&def),
            Some(&vec![
                super::derivation::explain::derivation_path::Elem::Step(0),
                super::derivation::explain::derivation_path::Elem::Upper,
            ])
        );
    }

    #[test]
    fn no_reason() {
        assert_eq!(
            elems(&T_::NoReason, &T_::Invalid, 1),
            vec![
                step("Step 1 of 1", true),
                rule(START),
                prefix("The subtype comes from this"),
                Elem::WitnessNoPos("this element".to_string()),
                prefix("The supertype comes from this"),
                Elem::WitnessNoPos("this element".to_string()),
            ]
        );
    }
}
