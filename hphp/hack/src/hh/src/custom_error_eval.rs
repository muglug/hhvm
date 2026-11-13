// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `custom_error_eval.ml`. See `hh/PORTING.md`.
//!
//! Matches the custom error rules of a `Custom_error_config.t` against a
//! typing or naming error, and evaluates the message of each rule that
//! matches.
//!
//! The `.mli` exports [`value`], [`eval_typing_error`] and
//! [`eval_naming_error`]; the rest is private, as in OCaml.
//!
//! Notes on the transliteration:
//!
//! - `Base.Either.t` is `itertools::Either`: `First` is `Left`, `Second` is
//!   `Right`.
//! - The environment of a match (`Env.t`) is a value, as in OCaml: the
//!   functions take it by value and return it in `Match.Matched`; where the
//!   OCaml uses the same environment twice (`Or` patterns, `match_exists`, the
//!   `>>= fun _ ->` of names), it is cloned. Its map is an `im::OrdMap`.
//! - OCaml strings are bytes, and the constraint names of
//!   `Secondary.Subtyping_error` are byte strings (`Message.t`): string
//!   patterns match `&[u8]`.
//! - `Map.add_exn` and `Map.find_exn` (`Env.add`, `Env.get`, `split_fields`)
//!   and `assert false` panic.

use bstr::ByteSlice;
use itertools::Either;
use oxidized::custom_error::CustomError;
use oxidized::custom_error::VersionedErrorMessage;
use oxidized::custom_error::VersionedPattError;
use oxidized::error_message::Elem;
use oxidized::error_message::ErrorMessage;
use oxidized::message::Message;
use oxidized::name_context::NameContext;
use oxidized::naming_error::NamingError;
use oxidized::patt_error::PattError;
use oxidized::patt_file::FilePath;
use oxidized::patt_file::PattFile;
use oxidized::patt_locl_ty::Params;
use oxidized::patt_locl_ty::PattLoclTy;
use oxidized::patt_locl_ty::Prim;
use oxidized::patt_locl_ty::ShapeField;
use oxidized::patt_locl_ty::ShapeFields;
use oxidized::patt_locl_ty::ShapeLabel;
use oxidized::patt_member_name::PattMemberName;
use oxidized::patt_name::Namespace;
use oxidized::patt_name::PattName;
use oxidized::patt_naming_error::PattNameContext;
use oxidized::patt_naming_error::PattNamingError;
use oxidized::patt_string::PattString;
use oxidized::patt_typing_error::Callback;
use oxidized::patt_typing_error::MemberKindPattern;
use oxidized::patt_typing_error::PattTypingError;
use oxidized::patt_typing_error::Primary;
use oxidized::patt_typing_error::ReasonsCallback;
use oxidized::patt_typing_error::Secondary;
use oxidized::patt_typing_error::StaticPattern;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::validation_err::ValidationErr;
use relative_path::RelativePath;

use crate::custom_error_config;
use crate::typing_defs_constraints::InternalType;
// module Ty = Typing_defs
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::t_shape_map::TShapeMap;
use crate::typing_error;
use crate::typing_error::InstanceOrStatic;
use crate::typing_error::MethodOrProperty;
use crate::typing_error::primary::SmemberNotFoundKind;

/// `module Value`
pub mod value {
    use std::cmp::Ordering;

    use relative_path::RelativePath;

    use crate::typing_defs_core::Ty;

    #[derive(Clone, Debug)]
    pub enum T {
        Ty(Ty),
        Name(String),
        File(RelativePath),
        MemberName(String),
    }

    /// `compare` (`[@@deriving compare]`): by the order of the constructors;
    /// two `Ty` are equal (`[@compare.ignore]`).
    pub fn compare(x: &T, y: &T) -> Ordering {
        fn ordinal(t: &T) -> u8 {
            match t {
                T::Ty(_) => 0,
                T::Name(_) => 1,
                T::File(_) => 2,
                T::MemberName(_) => 3,
            }
        }
        match (x, y) {
            (T::Ty(_), T::Ty(_)) => Ordering::Equal,
            (T::Name(x), T::Name(y)) => x.cmp(y),
            (T::File(x), T::File(y)) => crate::relative_path::compare(x, y),
            (T::MemberName(x), T::MemberName(y)) => x.cmp(y),
            _ => ordinal(x).cmp(&ordinal(y)),
        }
    }
}

/// `module Match`
mod match_ {
    // TODO[mjt] - decompose into safe and unsafe match?
    #[derive(Clone, Debug)]
    pub enum T<A, Err> {
        Matched(A),
        NoMatch,
        MatchErr(Err),
    }

    pub fn map<A, B, Err>(t: T<A, Err>, f: impl FnOnce(A) -> B) -> T<B, Err> {
        match t {
            T::Matched(a) => T::Matched(f(a)),
            T::NoMatch => T::NoMatch,
            T::MatchErr(err) => T::MatchErr(err),
        }
    }

    pub fn map_err<A, E1, E2>(t: T<A, E1>, f: impl FnOnce(E1) -> E2) -> T<A, E2> {
        match t {
            T::MatchErr(err) => T::MatchErr(f(err)),
            T::Matched(a) => T::Matched(a),
            T::NoMatch => T::NoMatch,
        }
    }

    /// `bind`, also `>>=`
    pub fn bind<A, B, Err>(t: T<A, Err>, f: impl FnOnce(A) -> T<B, Err>) -> T<B, Err> {
        match t {
            T::Matched(x) => f(x),
            T::NoMatch => T::NoMatch,
            T::MatchErr(err) => T::MatchErr(err),
        }
    }

    pub fn return_<A, Err>(x: A) -> T<A, Err> {
        T::Matched(x)
    }

    pub fn matched<A, Err>(x: A) -> T<A, Err> {
        T::Matched(x)
    }

    pub fn no_match<A, Err>() -> T<A, Err> {
        T::NoMatch
    }

    pub fn match_err<A, Err>(err: Err) -> T<A, Err> {
        T::MatchErr(err)
    }
}

use match_::T::MatchErr;
use match_::T::Matched;
use match_::T::NoMatch;

/// `module Env`
mod env {
    use relative_path::RelativePath;

    use super::value;
    use crate::typing_defs_core::Ty;

    /// `type t = Env of Value.t String.Map.t`
    #[derive(Clone, Debug)]
    pub struct T(im::OrdMap<String, value::T>);

    pub fn empty() -> T {
        T(im::OrdMap::new())
    }

    /// `Map.add_exn`: the label must not be bound yet.
    pub fn add(t: T, lbl: &str, data: value::T) -> T {
        let T(mut t) = t;
        if t.contains_key(lbl) {
            panic!("Map.add_exn got key already present: {}", lbl)
        }
        t.insert(lbl.to_string(), data);
        T(t)
    }

    pub fn add_name(t: T, lbl: &str, name: &str) -> T {
        add(t, lbl, value::T::Name(name.to_string()))
    }

    pub fn add_ty(t: T, lbl: &str, ty: &Ty) -> T {
        add(t, lbl, value::T::Ty(ty.clone()))
    }

    pub fn add_file(t: T, lbl: &str, file: &RelativePath) -> T {
        add(t, lbl, value::T::File(file.clone()))
    }

    pub fn add_member_name(t: T, lbl: &str, member_name: &str) -> T {
        add(t, lbl, value::T::MemberName(member_name.to_string()))
    }

    /// `Map.find_exn`: the label must be bound.
    pub fn get(t: &T, lbl: &str) -> value::T {
        let T(t) = t;
        match t.get(lbl) {
            Some(v) => v.clone(),
            None => panic!("Map.find_exn: not found: {}", lbl),
        }
    }
}

/// What every match returns: the environment, extended with the variables
/// the pattern binds, or the validation errors of an invalid pattern.
type M = match_::T<env::T, Vec<ValidationErr>>;

// -- Helpers -------------------------------------------------------------------

fn match_opt<P: ?Sized, S: ?Sized>(
    match_with: impl FnOnce(&P, &S, env::T) -> M,
    patt: &P,
    scrut: Option<&S>,
    env: env::T,
) -> M {
    match scrut {
        None => match_::matched(env),
        Some(scrut) => match_with(patt, scrut, env),
    }
}

fn match_exists<P: ?Sized, S, A: Clone, Err>(
    patt: &P,
    matches: impl Fn(&P, &S, A) -> match_::T<A, Err>,
    scruts: &[S],
    env: A,
) -> match_::T<A, Err> {
    let mut scruts = scruts.iter();
    loop {
        match scruts.next() {
            None => return match_::no_match(),
            Some(scrut) => match matches(patt, scrut, env.clone()) {
                m @ Matched(_) => return m,
                _ => {}
            },
        }
    }
}

// -- Member not found pattern helpers -------------------------------------------

fn matches_static_pattern(
    patt_is_static: &Option<StaticPattern>,
    scrut: InstanceOrStatic,
    env: env::T,
) -> M {
    match patt_is_static {
        // No static pattern means match any
        None => match_::matched(env),
        Some(StaticPattern::StaticOnly) => match scrut {
            InstanceOrStatic::static_ => match_::matched(env),
            InstanceOrStatic::instance => match_::no_match(),
        },
        Some(StaticPattern::InstanceOnly) => match scrut {
            InstanceOrStatic::instance => match_::matched(env),
            InstanceOrStatic::static_ => match_::no_match(),
        },
    }
}

fn matches_member_kind_instance(
    patt_kind: &MemberKindPattern,
    scrut: MethodOrProperty,
    env: env::T,
) -> M {
    let scrut_kind_matches = |patt_kind: &MemberKindPattern| match patt_kind {
        MemberKindPattern::AnyMemberKind => true,
        MemberKindPattern::MethodOnly => match scrut {
            MethodOrProperty::method_ => true,
            _ => false,
        },
        MemberKindPattern::PropertyOnly => match scrut {
            MethodOrProperty::property => true,
            _ => false,
        },
        // These don't exist for instance members
        MemberKindPattern::ClassConstantOnly | MemberKindPattern::ClassTypeconstOnly => false,
    };
    if scrut_kind_matches(patt_kind) {
        match_::matched(env)
    } else {
        match_::no_match()
    }
}

fn matches_member_kind_static(
    patt_kind: &MemberKindPattern,
    scrut: SmemberNotFoundKind,
    env: env::T,
) -> M {
    let scrut_kind_matches = |patt_kind: &MemberKindPattern| match patt_kind {
        MemberKindPattern::AnyMemberKind => true,
        MemberKindPattern::MethodOnly => match scrut {
            SmemberNotFoundKind::static_method => true,
            _ => false,
        },
        MemberKindPattern::PropertyOnly => match scrut {
            SmemberNotFoundKind::class_variable => true,
            _ => false,
        },
        MemberKindPattern::ClassConstantOnly => match scrut {
            SmemberNotFoundKind::class_constant => true,
            _ => false,
        },
        MemberKindPattern::ClassTypeconstOnly => match scrut {
            SmemberNotFoundKind::class_typeconst => true,
            _ => false,
        },
    };
    if scrut_kind_matches(patt_kind) {
        match_::matched(env)
    } else {
        match_::no_match()
    }
}

// -- Strings ---------------------------------------------------------------------

fn matches_patt_string_help(t: &PattString, scrut: &[u8]) -> bool {
    fn aux(t: &PattString, scrut: &[u8]) -> bool {
        match t {
            PattString::Wildcard => true,
            PattString::Exactly(str) => scrut == str.as_bytes(),
            PattString::StartsWith(prefix) => scrut.starts_with(prefix.as_bytes()),
            PattString::EndsWith(suffix) => scrut.ends_with(suffix.as_bytes()),
            PattString::Contains(substring) => scrut.contains_str(substring),
            PattString::Or(ts) => ts.iter().any(|t| aux(t, scrut)),
            PattString::And(ts) => ts.iter().all(|t| aux(t, scrut)),
            PattString::Not(t) => !aux(t, scrut),
        }
    }
    aux(t, scrut)
}

/// Since this pattern can never bind a variable we can't produce a match
/// error. We use this invariant to simply the inner matching function
fn matches_string(t: &PattString, scrut: &[u8], env: env::T) -> M {
    if matches_patt_string_help(t, scrut) {
        match_::matched(env)
    } else {
        match_::no_match()
    }
}

// -- Names -----------------------------------------------------------------------

fn matches_member_name(t: &PattMemberName, scrut: &str, env: env::T) -> M {
    match t {
        PattMemberName::Wildcard => match_::matched(env),
        PattMemberName::MemberName { patt_string } => {
            matches_string(patt_string, scrut.as_bytes(), env)
        }
        PattMemberName::As { lbl, patt } => match_::map(
            match_::map_err(
                matches_member_name(patt, scrut, env),
                |_| -> Vec<ValidationErr> {
                    panic!("Custom_error_eval.matches_member_name: assert false")
                },
            ),
            |env| env::add_member_name(env, lbl, scrut),
        ),
        PattMemberName::Invalid { errs, .. } => match_::match_err(errs.clone()),
    }
}

fn split_namespace(name: &str) -> Option<(&str, Vec<&str>)> {
    let mut ls: Vec<&str> = name.split('\\').filter(|s| !s.is_empty()).collect();
    ls.reverse();
    let mut ls = ls.into_iter();
    match ls.next() {
        Some(name) => Some((name, ls.collect())),
        None => None,
    }
}

fn matches_name(env: Option<env::T>, t: &PattName, scrut: &str) -> M {
    let env = env.unwrap_or_else(env::empty);
    match t {
        PattName::Wildcard => match_::matched(env),
        PattName::Name {
            namespace: patt_namespace,
            name: patt_name,
        } => match split_namespace(scrut) {
            Some((name, namespace)) => {
                let env_ = env.clone();
                match_::bind(matches_string(patt_name, name.as_bytes(), env), |_| {
                    matches_namespace(patt_namespace, &namespace, env_)
                })
            }
            _ => match_::no_match(),
        },
        PattName::As { lbl, patt } => match_::map(
            match_::map_err(
                matches_name(Some(env), patt, scrut),
                |_| -> Vec<ValidationErr> {
                    panic!("Custom_error_eval.matches_name: assert false")
                },
            ),
            |env| env::add_name(env, lbl, scrut),
        ),
        PattName::Invalid { errs, .. } => match_::match_err(errs.clone()),
    }
}

fn matches_namespace(patt_namespace: &Namespace, scrut: &[&str], env: env::T) -> M {
    match (patt_namespace, scrut) {
        (Namespace::Root, []) => match_::return_(env),
        (Namespace::Slash { prefix, elt }, [next, rest @ ..]) => {
            let env_ = env.clone();
            match_::bind(matches_string(elt, next.as_bytes(), env), |_| {
                matches_namespace(prefix, rest, env_)
            })
        }
        _ => match_::no_match(),
    }
}

// -- Files -----------------------------------------------------------------------

/// `Either.First (env, segs)`: the prefix matched, `segs` remain;
/// `Either.Second None`: no match; `Either.Second (Some err)`: an error.
type FilePathResult<'a> = Either<(env::T, &'a [String]), Option<Vec<ValidationErr>>>;

fn matches_file_path_help<'a>(t: &FilePath, segs: &'a [String], env: env::T) -> FilePathResult<'a> {
    match t {
        FilePath::Dot => Either::Left((env, segs)),
        FilePath::Slash { prefix, segment } => {
            let prefix_res = matches_file_path_help(prefix, segs, env);
            match prefix_res {
                Either::Right(_) => {
                    // If the prefix doesn't match then the path doesn't match
                    prefix_res
                }
                Either::Left((_, [])) => {
                    // The prefix matched but we have a required segment which doesn't so
                    // the path doesn't match
                    Either::Right(None)
                }
                Either::Left((env, [next, rest @ ..])) => {
                    // The prefix matched and we have a non-empty residual path; check if
                    // the current segment matches
                    match matches_string(segment, next.as_bytes(), env) {
                        Matched(env) => {
                            // The current segment also matches so the path matches
                            Either::Left((env, rest))
                        }
                        NoMatch => {
                            // The current segment doesn't match so the path doesn't match
                            Either::Right(None)
                        }
                        MatchErr(err) => Either::Right(Some(err)),
                    }
                }
            }
        }
        FilePath::SlashOpt { prefix, segment } => {
            let prefix_res = matches_file_path_help(prefix, segs, env);
            match prefix_res {
                Either::Right(_) => {
                    // If the prefix doesn't match then the path doesn't match
                    prefix_res
                }
                Either::Left((_, [])) => {
                    // The prefix matched and we have an optional segment so the path matches
                    prefix_res
                }
                Either::Left((env, segs @ [next, rest @ ..])) => {
                    // The prefix matched and we have a non-empty residual path; check if
                    // the current segment matches
                    match matches_string(segment, next.as_bytes(), env.clone()) {
                        Matched(env) => {
                            // The current segment also matches so the path matches
                            Either::Left((env, rest))
                        }
                        NoMatch => {
                            // The current segment doesn't match but it's optional so the path matches
                            Either::Left((env, segs))
                        }
                        MatchErr(err) => Either::Right(Some(err)),
                    }
                }
            }
        }
    }
}

/// A [Patt_file.t] matches the prefix of the path [scrut], represented as a list
/// of strings, when we have an elementwise match starting from [Dot] allowing
/// for a non-empty path suffix
fn matches_file_path_prefix(t: &FilePath, scrut: &[String], env: env::T) -> M {
    match matches_file_path_help(t, scrut, env) {
        Either::Left((env, _)) => match_::matched(env),
        Either::Right(None) => match_::no_match(),
        Either::Right(Some(err)) => match_::match_err(err),
    }
}

/// A [Patt_file.t] exactgly matches the path [scrut], represented as a list
/// of strings, when we have an elementwise match starting from [Dot] such that
/// the suffix is empty
fn matches_file_path_exact(t: &FilePath, scrut: &[String], env: env::T) -> M {
    match matches_file_path_help(t, scrut, env) {
        Either::Left((env, [])) => match_::matched(env),
        Either::Left(_) | Either::Right(None) => match_::no_match(),
        Either::Right(Some(err)) => match_::match_err(err),
    }
}

fn matches_file(t: &PattFile, scrut: &RelativePath, env: env::T) -> M {
    match t {
        PattFile::Wildcard => match_::matched(env),
        PattFile::As { lbl, patt } => match_::map(
            match_::map_err(matches_file(patt, scrut, env), |_| -> Vec<ValidationErr> {
                panic!("Custom_error_eval.matches_file: assert false")
            }),
            |env| env::add_file(env, lbl, scrut),
        ),
        PattFile::Invalid { errs, .. } => match_::match_err(errs.clone()),
        PattFile::Name {
            patt_file_path,
            patt_file_name,
            patt_file_extension,
            allow_glob,
        } => {
            // Match on complete path
            let path: Vec<String> = crate::relative_path::suffix(scrut)
                .split('/')
                .map(|s| s.to_string())
                .collect();
            let mut rev_path = path;
            rev_path.reverse();
            match rev_path.split_first() {
                Some((name, scrut_path)) => {
                    let (scrut_name, scrut_extensionopt) = match name.split_once('.') {
                        Some((name, ext)) => (name, Some(ext)),
                        None => (name.as_str(), None),
                    };
                    match_::bind(
                        matches_string(patt_file_name, scrut_name.as_bytes(), env),
                        |env| {
                            match_::bind(
                                match_opt(
                                    matches_string,
                                    patt_file_extension,
                                    scrut_extensionopt.map(|ext| ext.as_bytes()),
                                    env,
                                ),
                                |env| match patt_file_path {
                                    None => match_::matched(env),
                                    Some(patt_file_path) => {
                                        let mut scrut: Vec<String> = scrut_path.to_vec();
                                        scrut.reverse();
                                        if *allow_glob {
                                            matches_file_path_prefix(patt_file_path, &scrut, env)
                                        } else {
                                            matches_file_path_exact(patt_file_path, &scrut, env)
                                        }
                                    }
                                },
                            )
                        },
                    )
                }
                _ => match_::no_match(),
            }
        }
    }
}

// -- Types -----------------------------------------------------------------------

/// The fields of a shape, by kind of label and name, without their positions.
/// The names are OCaml strings (bytes): the names of string literal fields
/// are byte strings.
#[derive(Clone, Debug)]
struct ShapeFieldsSplit {
    groups: im::OrdMap<Vec<u8>, ShapeFieldType>,
    strs: im::OrdMap<Vec<u8>, ShapeFieldType>,
    cconsts: im::OrdMap<Vec<u8>, ShapeFieldType>,
}

/// `Map.add_exn`
fn map_add_exn(
    m: &im::OrdMap<Vec<u8>, ShapeFieldType>,
    key: Vec<u8>,
    data: ShapeFieldType,
) -> im::OrdMap<Vec<u8>, ShapeFieldType> {
    if m.contains_key(&key) {
        panic!("Map.add_exn got key already present: {}", key.as_bstr())
    }
    m.update(key, data)
}

fn split_fields(flds: &TShapeMap<ShapeFieldType>) -> ShapeFieldsSplit {
    let init = ShapeFieldsSplit {
        groups: im::OrdMap::new(),
        strs: im::OrdMap::new(),
        cconsts: im::OrdMap::new(),
    };
    // `Ty.TShapeMap.elements flds`
    let mut acc = init;
    for (k, ty) in flds {
        acc = match &k.0 {
            TshapeFieldName::TSFregexGroup(crate::typing_defs_core::PosString(_, n)) => {
                ShapeFieldsSplit {
                    groups: map_add_exn(&acc.groups, n.as_bytes().to_vec(), ty.clone()),
                    ..acc
                }
            }
            TshapeFieldName::TSFlitStr(crate::typing_defs_core::PosByteString(_, nm)) => {
                ShapeFieldsSplit {
                    strs: map_add_exn(&acc.strs, nm.to_vec(), ty.clone()),
                    ..acc
                }
            }
            TshapeFieldName::TSFclassConst(
                (_, cls_nm),
                crate::typing_defs_core::PosString(_, cnst_nm),
            ) => ShapeFieldsSplit {
                cconsts: map_add_exn(
                    &acc.cconsts,
                    format!("{}::{}", cls_nm, cnst_nm).into_bytes(),
                    ty.clone(),
                ),
                ..acc
            },
        }
    }
    acc
}

fn matches_locl_ty(env: Option<env::T>, t: &PattLoclTy, scrut: &Ty) -> M {
    let env = env.unwrap_or_else(env::empty);

    fn aux(t: &PattLoclTy, ty: &Ty, env: env::T) -> M {
        match (t, ty.get_node()) {
            // -- Type wildcards ----------------------------------------------------
            (PattLoclTy::Any, _) => Matched(env),
            // -- Type constructor like types ---------------------------------------
            (
                PattLoclTy::Apply {
                    name: patt_name,
                    params: patt_params,
                },
                Ty_::Tclass(name, _, tys),
            ) => match_::bind(matches_name(Some(env), patt_name, &name.1), |env| {
                aux_params(patt_params, tys, env)
            }),
            (
                PattLoclTy::Apply {
                    name: patt_name,
                    params: patt_params,
                },
                Ty_::Tnewtype(id, tys, _),
            ) => match_::bind(matches_name(Some(env), patt_name, id), |env| {
                aux_params(patt_params, tys, env)
            }),
            (
                PattLoclTy::Apply {
                    name: patt_name,
                    params: patt_params,
                },
                Ty_::TvecOrDict(ty_key, ty_val),
            ) => match_::bind(matches_name(Some(env), patt_name, "vec_or_dict"), |env| {
                aux_params(patt_params, &[ty_key.clone(), ty_val.clone()], env)
            }),
            (PattLoclTy::Option(t), Ty_::Toption(ty)) => aux(t, ty, env),
            // TODO optional and variadic fields T201398626 T201398652
            (
                PattLoclTy::Tuple(ts),
                Ty_::Ttuple(TupleType {
                    required: t_required,
                    optional: t_optional,
                    extra: TupleExtra::Tvariadic(t_variadic),
                }),
            ) if t_optional.is_empty() && crate::typing_defs::is_nothing(t_variadic) => {
                aux_tuple(ts, t_required, env)
            }
            // -- Primitives & other base types -------------------------------------
            (PattLoclTy::Prim(Prim::Null), Ty_::Tprim(oxidized::ast_defs::Tprim::Tnull))
            | (PattLoclTy::Prim(Prim::Void), Ty_::Tprim(oxidized::ast_defs::Tprim::Tvoid))
            | (PattLoclTy::Prim(Prim::Int), Ty_::Tprim(oxidized::ast_defs::Tprim::Tint))
            | (PattLoclTy::Prim(Prim::Bool), Ty_::Tprim(oxidized::ast_defs::Tprim::Tbool))
            | (PattLoclTy::Prim(Prim::Float), Ty_::Tprim(oxidized::ast_defs::Tprim::Tfloat))
            | (
                PattLoclTy::Prim(Prim::Resource),
                Ty_::Tprim(oxidized::ast_defs::Tprim::Tresource),
            )
            | (PattLoclTy::Prim(Prim::Num), Ty_::Tprim(oxidized::ast_defs::Tprim::Tnum))
            | (
                PattLoclTy::Prim(Prim::Arraykey),
                Ty_::Tprim(oxidized::ast_defs::Tprim::Tarraykey),
            )
            | (
                PattLoclTy::Prim(Prim::Noreturn),
                Ty_::Tprim(oxidized::ast_defs::Tprim::Tnoreturn),
            )
            | (PattLoclTy::Dynamic, Ty_::Tdynamic(_))
            | (PattLoclTy::Nonnull, Ty_::Tnonnull) => match_::matched(env),
            // `Naming_special_names.Classes.cString` (`naming_special_names_rust`
            // has it as `typehints::HH_STRING` only)
            (PattLoclTy::Prim(Prim::String), Ty_::Tclass((_, name), _, _))
                if naming_special_names_rust::typehints::HH_STRING == name =>
            {
                match_::matched(env)
            }
            // -- Variable binding --------------------------------------------------
            (PattLoclTy::As { lbl, patt }, _) => {
                match_::map(aux(patt, ty, env), |env| env::add_ty(env, lbl, ty))
            }
            // -- Or patterns -------------------------------------------------------
            (
                PattLoclTy::Or {
                    fst: patt_fst,
                    snd: patt_snd,
                },
                _,
            ) => match aux(patt_fst, ty, env.clone()) {
                m @ Matched(_) => m,
                _ => aux(patt_snd, ty, env),
            },
            // -- Shapes ------------------------------------------------------------
            (
                PattLoclTy::Shape(patt_flds),
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple { fields: flds, .. })),
            ) => {
                // Split [TShapeMap.t] into three [String.Map.t]s, eliminating positional
                // information
                let splits = split_fields(flds);
                aux_shape(patt_flds, splits, env)
            }
            // -- Mismatches --------------------------------------------------------
            (
                PattLoclTy::Apply { .. }
                | PattLoclTy::Option(_)
                | PattLoclTy::Tuple(_)
                | PattLoclTy::Prim(_)
                | PattLoclTy::Dynamic
                | PattLoclTy::Nonnull
                | PattLoclTy::Shape(_),
                _,
            ) => match_::no_match(),
            (PattLoclTy::Invalid(errs, _), _) => match_::match_err(errs.clone()),
        }
    }

    fn aux_shape(t: &ShapeFields, splits: ShapeFieldsSplit, env: env::T) -> M {
        match t {
            ShapeFields::Fld {
                fld: patt_fld,
                rest: patt_rest,
            } => match aux_shape_field(patt_fld, &splits, env) {
                Matched((splits, env)) => aux_shape(patt_rest, splits, env),
                NoMatch => NoMatch,
                MatchErr(err) => match_::match_err(err),
            },
            // -- Open matches any remaining shape fields ---------------------------
            ShapeFields::Open => match_::matched(env),
            // -- Closed matches when we have no remaining shape fields -------------
            ShapeFields::Closed
                if splits.groups.is_empty()
                    && splits.strs.is_empty()
                    && splits.cconsts.is_empty() =>
            {
                match_::matched(env)
            }
            ShapeFields::Closed => match_::no_match(),
        }
    }

    fn aux_shape_field(
        fld: &ShapeField,
        splits: &ShapeFieldsSplit,
        env: env::T,
    ) -> match_::T<(ShapeFieldsSplit, env::T), Vec<ValidationErr>> {
        let aux_ = |get: &dyn Fn(&ShapeFieldsSplit) -> &im::OrdMap<Vec<u8>, ShapeFieldType>,
                    set: &dyn Fn(
            &ShapeFieldsSplit,
            im::OrdMap<Vec<u8>, ShapeFieldType>,
        ) -> ShapeFieldsSplit,
                    str: &[u8]| {
            let split = get(splits);
            match split.get(str) {
                None => match_::no_match(),
                Some(ShapeFieldType {
                    optional: sft_optional,
                    ty: sft_ty,
                }) => {
                    if *sft_optional == fld.optional {
                        match aux(&fld.patt, sft_ty, env) {
                            Matched(env) => match_::matched((set(splits, split.without(str)), env)),
                            NoMatch => NoMatch,
                            MatchErr(err) => MatchErr(err),
                        }
                    } else {
                        match_::no_match()
                    }
                }
            }
        };
        // These funcs can be derived with ppx_sexp_conv
        match &fld.lbl {
            ShapeLabel::RegGroupLabel(n) => aux_(
                &|splits| &splits.groups,
                &|splits, groups| ShapeFieldsSplit {
                    groups,
                    ..splits.clone()
                },
                n.as_bytes(),
            ),
            ShapeLabel::StrLbl(str) => aux_(
                &|splits| &splits.strs,
                &|splits, strs| ShapeFieldsSplit {
                    strs,
                    ..splits.clone()
                },
                str.as_bytes(),
            ),
            ShapeLabel::CConstLbl { cls_nm, cnst_nm } => {
                let str = format!("{}::{}", cls_nm, cnst_nm);
                aux_(
                    &|splits| &splits.cconsts,
                    &|splits, cconsts| ShapeFieldsSplit {
                        cconsts,
                        ..splits.clone()
                    },
                    str.as_bytes(),
                )
            }
        }
    }

    fn aux_params(t: &Params, tys: &[Ty], env: env::T) -> M {
        match (t, tys) {
            (
                Params::Cons {
                    hd: patt_hd,
                    tl: patt_tl,
                },
                [ty, tys @ ..],
            ) => match_::bind(aux(patt_hd, ty, env), |env| aux_params(patt_tl, tys, env)),
            (Params::Exists(t), _) => match_exists(t, aux, tys, env),
            (Params::Nil, []) | (Params::Wildcard, _) => match_::matched(env),
            (Params::Nil, _) | (Params::Cons { .. }, []) => match_::no_match(),
        }
    }

    fn aux_tuple(ts: &[PattLoclTy], t_required: &[Ty], env: env::T) -> M {
        fn aux_tys(ts: &[PattLoclTy], tys: &[Ty], env: env::T) -> M {
            match (ts, tys) {
                ([t, ts @ ..], [ty, tys @ ..]) => {
                    match_::bind(aux(t, ty, env), |env| aux_tys(ts, tys, env))
                }
                ([], []) => match_::matched(env),
                _ => match_::no_match(),
            }
        }
        aux_tys(ts, t_required, env)
    }

    aux(t, scrut, env)
}

// -- Typing errors ---------------------------------------------------------------

fn matches_typing_error(t: &PattTypingError, scrut: &typing_error::T, env: env::T) -> M {
    use typing_error::T as Error;
    use typing_error::primary::T as P;
    use typing_error::primary::expr_tree;
    use typing_error::primary::package;
    use typing_error::secondary;

    // -- Top-level typing errors ---------------------------------------------------
    fn aux(t: &PattTypingError, err: &Error, env: env::T) -> M {
        match (t, err) {
            // Not in OCaml: an error not built yet is matched as the error
            // it stands for.
            (_, Error::Deferred(d)) => aux(t, d.force(), env),
            (_, Error::Intersection(errs))
            | (_, Error::Union(errs))
            | (_, Error::Multiple(errs)) => match_exists(t, aux, errs, env),
            // -- Primary errors ----------------------------------------------------
            (PattTypingError::Primary(patt_prim), Error::Primary(err_prim)) => {
                aux_primary(patt_prim, err_prim, env)
            }
            // -- Callback application ----------------------------------------------
            (
                PattTypingError::Apply {
                    cb: patt_cb,
                    err: patt_err,
                },
                Error::Apply(cb, err),
            ) => match_::bind(aux_callback(patt_cb, cb, env), |env| {
                aux(patt_err, err, env)
            }),
            // -- Reasons callback application --------------------------------------
            (
                PattTypingError::ApplyReasons {
                    rsns_cb: patt_rsns_cb,
                    secondary: patt_secondary,
                },
                Error::Apply_reasons(err_rsns_cb, err_secondary),
            ) => match_::bind(
                aux_reasons_callback(patt_rsns_cb, err_rsns_cb, env),
                |env| aux_secondary(patt_secondary, err_secondary, env),
            ),
            // -- Or patterns -------------------------------------------------------
            (
                PattTypingError::Or {
                    fst: patt_fst,
                    snd: patt_snd,
                },
                _,
            ) => match aux(patt_fst, err, env.clone()) {
                m @ Matched(_) => m,
                _ => aux(patt_snd, err, env),
            },
            // -- Mismatches --------------------------------------------------------
            (PattTypingError::Primary(_), _)
            | (PattTypingError::Apply { .. }, _)
            | (PattTypingError::ApplyReasons { .. }, _) => match_::no_match(),
            (PattTypingError::InvalidTyping { errs, .. }, _) => match_::match_err(errs.clone()),
        }
    }

    // -- Primary errors ------------------------------------------------------------
    fn aux_primary(t: &Primary, err_prim: &P, env: env::T) -> M {
        match (t, err_prim) {
            (Primary::AnyPrim, _) => match_::matched(env),
            // -- Member not found patterns -----------------------------------------
            (
                Primary::MemberNotFound {
                    is_static: patt_is_static,
                    kind: patt_kind,
                    class_name: patt_class_name,
                    member_name: patt_member_name,
                    visibility: _,
                },
                P::Member_not_found {
                    kind,
                    class_name,
                    member_name,
                    ..
                },
            ) => match_::bind(
                matches_static_pattern(patt_is_static, InstanceOrStatic::instance, env),
                |env| {
                    match_::bind(matches_member_kind_instance(patt_kind, *kind, env), |env| {
                        match_::bind(
                            matches_name(Some(env), patt_class_name, class_name),
                            |env| matches_member_name(patt_member_name, member_name, env),
                        )
                    })
                },
            ),
            (
                Primary::MemberNotFound {
                    is_static: patt_is_static,
                    kind: patt_kind,
                    class_name: patt_class_name,
                    member_name: patt_member_name,
                    visibility: _,
                },
                P::Smember_not_found {
                    kind,
                    class_name,
                    member_name,
                    ..
                },
            ) => match_::bind(
                matches_static_pattern(patt_is_static, InstanceOrStatic::static_, env),
                |env| {
                    match_::bind(matches_member_kind_static(patt_kind, *kind, env), |env| {
                        match_::bind(
                            matches_name(Some(env), patt_class_name, class_name),
                            |env| matches_member_name(patt_member_name, member_name, env),
                        )
                    })
                },
            ),
            (Primary::MemberNotFound { .. }, _) => match_::no_match(),
            // -- Package errors ----------------------------------------------------
            (
                Primary::AnyPkg {
                    use_file: patt_use_file,
                    decl_file: patt_decl_file,
                }
                | Primary::CrossPkgAccess {
                    use_file: patt_use_file,
                    decl_file: patt_decl_file,
                },
                P::Package(package::T::Cross_pkg_access { pos, decl_pos, .. }),
            )
            | (
                Primary::AnyPkg {
                    use_file: patt_use_file,
                    decl_file: patt_decl_file,
                }
                | Primary::CrossPkgAccessWithRequirepackage {
                    use_file: patt_use_file,
                    decl_file: patt_decl_file,
                },
                P::Package(package::T::Cross_pkg_access_with_requirepackage {
                    pos, decl_pos, ..
                }),
            )
            | (
                Primary::AnyPkg {
                    use_file: patt_use_file,
                    decl_file: patt_decl_file,
                }
                | Primary::CrossPkgAccessWithSoftrequirepackage {
                    use_file: patt_use_file,
                    decl_file: patt_decl_file,
                },
                P::Package(package::T::Cross_pkg_access_with_softrequirepackage {
                    pos,
                    decl_pos,
                    ..
                }),
            )
            | (
                Primary::AnyPkg {
                    use_file: patt_use_file,
                    decl_file: patt_decl_file,
                }
                | Primary::SoftIncludedAccess {
                    use_file: patt_use_file,
                    decl_file: patt_decl_file,
                },
                P::Package(package::T::Soft_included_access { pos, decl_pos, .. }),
            ) => match_::bind(matches_file(patt_use_file, pos.filename(), env), |env| {
                matches_file(patt_decl_file, &crate::pos_or_decl::filename(decl_pos), env)
            }),
            (
                Primary::AnyPkg { .. }
                | Primary::CrossPkgAccess { .. }
                | Primary::CrossPkgAccessWithRequirepackage { .. }
                | Primary::CrossPkgAccessWithSoftrequirepackage { .. }
                | Primary::SoftIncludedAccess { .. },
                _,
            ) => match_::no_match(),
            // -- Expression tree errors --------------------------------------------
            (
                Primary::ExpressionTreeUnsupportedOperator {
                    class_name: patt_class_name,
                    member_name: patt_member_name,
                },
                P::Expr_tree(expr_tree::T::Expression_tree_unsupported_operator {
                    class_name,
                    member_name,
                    ..
                }),
            ) => match_::bind(
                matches_name(Some(env), patt_class_name, class_name),
                |env| matches_member_name(patt_member_name, member_name, env),
            ),
            (Primary::ExpressionTreeUnsupportedOperator { .. }, _) => match_::no_match(),
        }
    }

    // -- Secondary errors ----------------------------------------------------------
    fn aux_secondary(t: &Secondary, err_snd: &secondary::T, env: env::T) -> M {
        match (t, err_snd) {
            (Secondary::OfError(patt_err), secondary::T::Of_error(err)) => aux(patt_err, err, env),
            (Secondary::OfError(_), _) => match_::no_match(),
            // We don't expose our internal `constraint_ty` so we handle this here
            (
                Secondary::ViolatedConstraint {
                    cstr: patt_cstr,
                    ty_sub: patt_ty_sub,
                    ty_sup: patt_ty_sup,
                },
                secondary::T::Subtyping_error {
                    cstrs,
                    ty_sub,
                    ty_sup,
                    ..
                },
            ) => match_::bind(
                match_exists(patt_cstr, aux_param, cstrs.force(), env),
                |env| {
                    match_::bind(aux_internal_ty(patt_ty_sub, ty_sub, env), |env| {
                        aux_internal_ty(patt_ty_sup, ty_sup, env)
                    })
                },
            ),
            (Secondary::ViolatedConstraint { .. }, _) => match_::no_match(),
            (
                Secondary::SubtypingError {
                    sub: patt_ty_sub,
                    sup: patt_ty_sup,
                },
                secondary::T::Subtyping_error {
                    cstrs,
                    ty_sub,
                    ty_sup,
                    ..
                },
            ) => {
                if cstrs.force().is_empty() {
                    match_::bind(aux_internal_ty(patt_ty_sub, ty_sub, env), |env| {
                        aux_internal_ty(patt_ty_sup, ty_sup, env)
                    })
                } else {
                    match_::no_match()
                }
            }
            (Secondary::SubtypingError { .. }, _) => match_::no_match(),
            (Secondary::AnySnd, _) => match_::matched(env),
        }
    }

    // -- Primary callbacks ---------------------------------------------------------
    fn aux_callback(t: &Callback, _err_callback: &typing_error::callback::T, env: env::T) -> M {
        match t {
            Callback::AnyCallback => match_::matched(env),
        }
    }

    // -- Secondary / reasons callbacks ---------------------------------------------
    fn aux_reasons_callback(
        t: &ReasonsCallback,
        _err_reasons_callback: &typing_error::reasons_callback::T,
        env: env::T,
    ) -> M {
        match t {
            ReasonsCallback::AnyReasonsCallback => match_::matched(env),
        }
    }

    // -- Internal types: we don't expose contraint types so handle here --------------
    fn aux_internal_ty(patt_locl_ty: &PattLoclTy, internal_ty: &InternalType, env: env::T) -> M {
        match internal_ty {
            InternalType::LoclType(scrut) => matches_locl_ty(Some(env), patt_locl_ty, scrut),
            _ => match_::no_match(),
        }
    }

    // -- Type parameters -----------------------------------------------------------
    fn aux_param(patt_name: &PattString, cstr: &(PosOrDecl, Message<PosOrDecl>), env: env::T) -> M {
        let (_, Message(_, scrut)) = cstr;
        matches_string(patt_name, scrut, env)
    }

    aux(t, scrut, env)
}

// -- Naming errors ---------------------------------------------------------------

fn matches_name_context(
    patt_name_context: &PattNameContext,
    scrut: &NameContext,
    env: env::T,
) -> M {
    match patt_name_context {
        PattNameContext::AnyNameContext => match_::matched(env),
        PattNameContext::OneOfNameContext(ctxts) if ctxts.iter().any(|ctxt| ctxt == scrut) => {
            match_::matched(env)
        }
        _ => match_::no_match(),
    }
}

fn matches_naming_error(t: &PattNamingError, scrut: &NamingError, env: env::T) -> M {
    match (t, scrut) {
        (
            PattNamingError::UnboundName {
                name_context: patt_name_context,
                name: patt_name,
            },
            NamingError::UnboundName { name, kind, .. },
        ) => match_::bind(matches_name_context(patt_name_context, kind, env), |env| {
            matches_name(Some(env), patt_name, name)
        }),
        _ => match_::no_match(),
    }
}

// -- Top level error matches -----------------------------------------------------

enum PhaseError<'a> {
    TypingPhase(&'a typing_error::T),
    NamingPhase(&'a NamingError),
}

fn matches_error(env: Option<env::T>, t: &PattError, scrut: &PhaseError<'_>) -> M {
    let env = env.unwrap_or_else(env::empty);
    match (t, scrut) {
        (PattError::Typing(patt_typing_error), PhaseError::TypingPhase(scrut)) => {
            matches_typing_error(patt_typing_error, scrut, env)
        }
        (PattError::Naming(patt_naming_error), PhaseError::NamingPhase(scrut)) => {
            matches_naming_error(patt_naming_error, scrut, env)
        }
        _ => match_::no_match(),
    }
}

fn eval_error_message(error_message: &ErrorMessage, env: &env::T) -> Vec<Either<String, value::T>> {
    let ErrorMessage { message } = error_message;
    let f = |t: &Elem| match t {
        Elem::Lit(str) => Either::Left(str.clone()),
        Elem::FileVar(var) | Elem::TyVar(var) | Elem::NameVar(var) | Elem::MemberNameVar(var) => {
            Either::Right(env::get(env, var))
        }
    };
    message.iter().map(f).collect()
}

fn eval_custom_error_v1(
    patt_typing_err: &PattTypingError,
    error_message: &ErrorMessage,
    err: &typing_error::T,
) -> Option<Vec<Either<String, value::T>>> {
    match matches_typing_error(patt_typing_err, err, env::empty()) {
        Matched(env) => Some(eval_error_message(error_message, &env)),
        _ => None,
    }
}

fn eval_custom_error_v2(
    patt_err: &PattError,
    error_message: &ErrorMessage,
    err: &PhaseError<'_>,
) -> Option<Vec<Either<String, value::T>>> {
    match matches_error(None, patt_err, err) {
        Matched(env) => Some(eval_error_message(error_message, &env)),
        _ => None,
    }
}

fn eval_custom_error(
    custom_error: &CustomError,
    err: &PhaseError<'_>,
) -> Option<Vec<Either<String, value::T>>> {
    let CustomError {
        patt,
        error_message: VersionedErrorMessage::MessageV1(error_message),
        ..
    } = custom_error;
    match (patt, err) {
        (VersionedPattError::ErrorV1(patt), PhaseError::TypingPhase(err)) => {
            eval_custom_error_v1(patt, error_message, err)
        }
        (VersionedPattError::ErrorV1(_), _) => {
            // Version 1 only supports typing errors
            None
        }
        (VersionedPattError::ErrorV2(patt), _) => eval_custom_error_v2(patt, error_message, err),
    }
}

pub fn eval_naming_error(
    config: &custom_error_config::T,
    err: &NamingError,
) -> Vec<Vec<Either<String, value::T>>> {
    let custom_error_config::T { valid, .. } = config;
    let err = PhaseError::NamingPhase(err);
    valid
        .iter()
        .filter_map(|custom_error| eval_custom_error(custom_error, &err))
        .collect()
}

pub fn eval_typing_error(
    config: &custom_error_config::T,
    err: &typing_error::T,
) -> Vec<Vec<Either<String, value::T>>> {
    let custom_error_config::T { valid, .. } = config;
    let err = PhaseError::TypingPhase(err);
    valid
        .iter()
        .filter_map(|custom_error| eval_custom_error(custom_error, &err))
        .collect()
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::Arc;

    use oxidized::ast_defs::Tprim;
    use oxidized::pos::Pos;
    use oxidized::pos_span_raw::PosSpanRaw;
    use relative_path::Prefix;

    use super::*;
    use crate::typing_defs_core::Exact;
    use crate::typing_defs_core::mk;
    use crate::typing_reason;

    fn s(x: &str) -> PattString {
        PattString::Exactly(x.to_string())
    }

    fn name(namespace: &[&str], n: &str) -> PattName {
        let mut ns = Namespace::Root;
        for elt in namespace {
            ns = Namespace::Slash {
                prefix: Box::new(ns),
                elt: s(elt),
            };
        }
        PattName::Name {
            namespace: ns,
            name: s(n),
        }
    }

    fn file(path: &str) -> RelativePath {
        RelativePath::make(Prefix::Root, PathBuf::from(path))
    }

    fn pos(path: &str) -> Pos {
        Pos::from_raw_span(Arc::new(file(path)), PosSpanRaw::make_dummy())
    }

    fn ty(ty_: Ty_) -> Ty {
        mk((typing_reason::none(), ty_))
    }

    fn class(name: &str, tys: Vec<Ty>) -> Ty {
        ty(Ty_::Tclass(
            (Pos::NONE, name.to_string()),
            Exact::Exact,
            tys,
        ))
    }

    fn is_matched(m: M) -> bool {
        matches!(m, Matched(_))
    }

    #[test]
    fn strings() {
        let scrut = b"FooBar";
        assert!(matches_patt_string_help(&PattString::Wildcard, scrut));
        assert!(matches_patt_string_help(&s("FooBar"), scrut));
        assert!(!matches_patt_string_help(&s("Foo"), scrut));
        assert!(matches_patt_string_help(
            &PattString::StartsWith("Foo".to_string()),
            scrut
        ));
        assert!(matches_patt_string_help(
            &PattString::EndsWith("Bar".to_string()),
            scrut
        ));
        assert!(matches_patt_string_help(
            &PattString::Contains("oB".to_string()),
            scrut
        ));
        assert!(matches_patt_string_help(
            &PattString::Contains(String::new()),
            scrut
        ));
        assert!(matches_patt_string_help(
            &PattString::Not(Box::new(s("x"))),
            scrut
        ));
        assert!(matches_patt_string_help(
            &PattString::Or(vec![s("x"), s("FooBar")]),
            scrut
        ));
        assert!(!matches_patt_string_help(
            &PattString::And(vec![s("x"), s("FooBar")]),
            scrut
        ));
        assert!(matches_patt_string_help(&PattString::And(vec![]), scrut));
        assert!(!matches_patt_string_help(&PattString::Or(vec![]), scrut));
    }

    #[test]
    fn namespaces() {
        assert_eq!(split_namespace("\\HH\\Foo"), Some(("Foo", vec!["HH"])));
        assert_eq!(split_namespace("Foo"), Some(("Foo", vec![])));
        assert_eq!(split_namespace(""), None);
        assert!(is_matched(matches_name(
            None,
            &name(&["HH"], "Foo"),
            "\\HH\\Foo"
        )));
        assert!(!is_matched(matches_name(
            None,
            &name(&[], "Foo"),
            "\\HH\\Foo"
        )));
        assert!(is_matched(matches_name(
            None,
            &name(&["A", "B"], "C"),
            "\\A\\B\\C"
        )));
        assert!(!is_matched(matches_name(
            None,
            &name(&["B", "A"], "C"),
            "\\A\\B\\C"
        )));
        let as_ = PattName::As {
            lbl: "x".to_string(),
            patt: Box::new(PattName::Wildcard),
        };
        match matches_name(None, &as_, "\\Foo") {
            Matched(env) => match env::get(&env, "x") {
                value::T::Name(n) => assert_eq!(n, "\\Foo"),
                v => panic!("{:?}", v),
            },
            _ => panic!("no match"),
        }
    }

    #[test]
    fn files() {
        let patt = |path: Option<FilePath>, allow_glob| PattFile::Name {
            allow_glob,
            patt_file_path: path,
            patt_file_name: s("foo"),
            patt_file_extension: s("php"),
        };
        let dir = |segs: &[&str]| {
            let mut p = FilePath::Dot;
            for seg in segs {
                p = crate::patt_file::slash(p, s(seg));
            }
            p
        };
        let scrut = file("a/b/foo.php");
        assert!(is_matched(matches_file(
            &patt(None, false),
            &scrut,
            env::empty()
        )));
        assert!(is_matched(matches_file(
            &patt(Some(dir(&["a", "b"])), false),
            &scrut,
            env::empty()
        )));
        assert!(!is_matched(matches_file(
            &patt(Some(dir(&["a"])), false),
            &scrut,
            env::empty()
        )));
        assert!(is_matched(matches_file(
            &patt(Some(dir(&["a"])), true),
            &scrut,
            env::empty()
        )));
        assert!(!is_matched(matches_file(
            &patt(Some(dir(&["b"])), true),
            &scrut,
            env::empty()
        )));
        // An optional segment that is missing.
        let opt = crate::patt_file::slash_opt(dir(&["a"]), s("x"));
        let opt = crate::patt_file::slash(opt, s("b"));
        assert!(is_matched(matches_file(
            &patt(Some(opt), false),
            &scrut,
            env::empty()
        )));
        // `foo.blade.php`: the extension is what follows the first dot.
        let scrut = file("foo.blade.php");
        assert!(!is_matched(matches_file(
            &patt(None, false),
            &scrut,
            env::empty()
        )));
        // No extension: any extension pattern matches.
        let scrut = file("foo");
        assert!(is_matched(matches_file(
            &patt(None, false),
            &scrut,
            env::empty()
        )));
    }

    #[test]
    fn types() {
        let int = ty(Ty_::Tprim(Tprim::Tint));
        assert!(is_matched(matches_locl_ty(
            None,
            &PattLoclTy::Prim(Prim::Int),
            &int
        )));
        assert!(!is_matched(matches_locl_ty(
            None,
            &PattLoclTy::Prim(Prim::Bool),
            &int
        )));
        let string = class("\\HH\\string", vec![]);
        assert!(is_matched(matches_locl_ty(
            None,
            &PattLoclTy::Prim(Prim::String),
            &string
        )));
        let vec_int = class("\\HH\\vec", vec![int.clone()]);
        let apply = |params| PattLoclTy::Apply {
            name: name(&["HH"], "vec"),
            params: Box::new(params),
        };
        assert!(is_matched(matches_locl_ty(
            None,
            &apply(Params::Cons {
                hd: PattLoclTy::Prim(Prim::Int),
                tl: Box::new(Params::Nil),
            }),
            &vec_int
        )));
        assert!(!is_matched(matches_locl_ty(
            None,
            &apply(Params::Nil),
            &vec_int
        )));
        assert!(is_matched(matches_locl_ty(
            None,
            &apply(Params::Exists(PattLoclTy::Prim(Prim::Int))),
            &vec_int
        )));
        let or = PattLoclTy::Or {
            fst: Box::new(PattLoclTy::Prim(Prim::Bool)),
            snd: Box::new(PattLoclTy::As {
                lbl: "t".to_string(),
                patt: Box::new(PattLoclTy::Any),
            }),
        };
        match matches_locl_ty(None, &or, &int) {
            Matched(env) => assert!(matches!(env::get(&env, "t"), value::T::Ty(_))),
            _ => panic!("no match"),
        }
        let invalid = PattLoclTy::Invalid(vec![], Box::new(PattLoclTy::Any));
        assert!(matches!(matches_locl_ty(None, &invalid, &int), MatchErr(_)));
    }

    #[test]
    fn typing_errors() {
        let err = typing_error::primary(typing_error::primary::T::Member_not_found {
            pos: pos("a.php"),
            kind: MethodOrProperty::method_,
            class_name: "\\Foo".to_string(),
            class_pos: Pos::NONE,
            member_name: "bar".to_string(),
            hint: typing_error::Lazy::from_val(None),
            reason: typing_error::Lazy::from_val(vec![]),
        });
        let patt = |is_static, kind| {
            PattTypingError::Primary(Primary::MemberNotFound {
                is_static,
                kind,
                class_name: PattName::As {
                    lbl: "c".to_string(),
                    patt: Box::new(PattName::Wildcard),
                },
                member_name: PattMemberName::As {
                    lbl: "m".to_string(),
                    patt: Box::new(PattMemberName::Wildcard),
                },
                visibility: None,
            })
        };
        let custom_error = |patt| CustomError {
            name: "test".to_string(),
            patt: VersionedPattError::ErrorV1(patt),
            error_message: VersionedErrorMessage::MessageV1(ErrorMessage {
                message: vec![
                    Elem::Lit("Class ".to_string()),
                    Elem::NameVar("c".to_string()),
                    Elem::Lit(" member ".to_string()),
                    Elem::MemberNameVar("m".to_string()),
                ],
            }),
        };
        let config = custom_error_config::T {
            valid: vec![
                custom_error(patt(None, MemberKindPattern::MethodOnly)),
                custom_error(patt(
                    Some(StaticPattern::StaticOnly),
                    MemberKindPattern::AnyMemberKind,
                )),
                custom_error(patt(None, MemberKindPattern::PropertyOnly)),
            ],
            invalid: vec![],
        };
        let msgs = eval_typing_error(&config, &err);
        assert_eq!(msgs.len(), 1);
        let msg: Vec<String> = msgs[0]
            .iter()
            .map(|v| match v {
                Either::Left(s) => s.clone(),
                Either::Right(value::T::Name(n)) => format!("<{}>", n),
                Either::Right(value::T::MemberName(n)) => format!("[{}]", n),
                Either::Right(v) => panic!("{:?}", v),
            })
            .collect();
        assert_eq!(msg.concat(), "Class <\\Foo> member [bar]");
        // A rule of version 2 for naming errors does not match a typing error,
        // and a rule of version 1 does not match a naming error.
        let naming_err = NamingError::UnboundName {
            pos: pos("a.php"),
            name: "\\Foo".to_string(),
            kind: NameContext::TypeNamespace,
        };
        assert!(eval_naming_error(&config, &naming_err).is_empty());
        let v2 = CustomError {
            name: "test".to_string(),
            patt: VersionedPattError::ErrorV2(PattError::Naming(PattNamingError::UnboundName {
                name_context: PattNameContext::OneOfNameContext(vec![NameContext::TypeNamespace]),
                name: name(&[], "Foo"),
            })),
            error_message: VersionedErrorMessage::MessageV1(ErrorMessage {
                message: vec![Elem::Lit("unbound".to_string())],
            }),
        };
        let config = custom_error_config::T {
            valid: vec![v2],
            invalid: vec![],
        };
        assert_eq!(eval_naming_error(&config, &naming_err).len(), 1);
        assert!(eval_typing_error(&config, &err).is_empty());
        // Multiple: one of the errors is enough.
        let multiple = typing_error::T::Multiple(vec![err.clone()]);
        let config = custom_error_config::T {
            valid: vec![custom_error(patt(None, MemberKindPattern::AnyMemberKind))],
            invalid: vec![],
        };
        assert_eq!(eval_typing_error(&config, &multiple).len(), 1);
    }
}
