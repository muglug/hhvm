// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_error_utils.ml`. See `mod.rs`.
//!
//! The mutually recursive modules `Eval_error`, `Eval_secondary`,
//! `Eval_callback` and `Eval_reasons_callback` (one `pub mod` each, in the
//! order of the OCaml file), then the functions of `Typing_error_utils` itself
//! that follow them (`add_typing_error`, ...), which `mod.rs` re-exports.
//!
//! Notes on the transliteration:
//!
//! - An error is evaluated from a reference (it is only read), so what the
//!   OCaml shares between the error and the evaluated error (positions,
//!   quickfixes, lazy values) is cloned here. Clones of a lazy value share its
//!   computation.
//! - `lazy e` is `Lazy::new(move || e)`; `Lazy.(x >>= fun x -> y >>= fun y ->
//!   return e)` is `Lazy::new` of a closure that forces `x`, then `y`.
//! - `claim_and_reasons` is `Lazy.(claim >>= fun x -> reasons >>= fun xs ->
//!   return (x :: xs))`, which the OCaml writes out each time.
//! - `Pos_or_decl.t` and `Pos.t` are the same Rust type, and
//!   `Pos_or_decl.of_raw_pos` is the identity in OCaml too, so it disappears
//!   (`Message.map ~f:Pos_or_decl.of_raw_pos` with it).
//! - `Error_code.to_enum code` is `code as isize`.

use oxidized::diagnostics::Diagnostic;
use oxidized::error_codes::Typing as ErrorCode;
use oxidized::explanation::Explanation;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::quickfix::Quickfix;

use super::common::Lazy;
use super::eval_result;
use crate::naming_errors::render::md_codify;
use crate::naming_errors::render::strip_ns;
use crate::typing_env_types::Env;
use crate::typing_error;

/// `x :: xs`
fn cons<A: Clone>(x: A, xs: &[A]) -> Vec<A> {
    let mut l = Vec::with_capacity(xs.len() + 1);
    l.push(x);
    l.extend_from_slice(xs);
    l
}

/// `xs @ ys`
fn append<A: Clone>(xs: &[A], ys: &[A]) -> Vec<A> {
    let mut l = Vec::with_capacity(xs.len() + ys.len());
    l.extend_from_slice(xs);
    l.extend_from_slice(ys);
    l
}

/// A `(Pos_or_decl.t * string) list` (what `Typing_reason.to_string` returns)
/// as the `Pos_or_decl.t Message.t list` it is in OCaml.
fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, msg.into()))
        .collect()
}

pub mod eval_error {
    use oxidized::pos_or_decl::Ctx;

    use super::super::common;
    use super::super::eval_primary;
    use super::eval_callback;
    use super::eval_reasons_callback;
    use super::eval_secondary;
    use super::*;

    /// `Eval_error.t`
    #[derive(Clone, Debug)]
    pub struct T {
        pub code: ErrorCode,
        pub claim: Lazy<Message<Pos>>,
        pub reasons: Lazy<Vec<Message<PosOrDecl>>>,
        pub explanation: Lazy<Explanation<PosOrDecl>>,
        pub quickfixes: Vec<Quickfix<Pos>>,
    }

    /// `Eval_error.partial`
    #[derive(Clone, Debug)]
    pub struct Partial {
        pub code_opt: Option<ErrorCode>,
        pub claim: Lazy<Message<Pos>>,
        pub reasons_opt: Option<Lazy<Vec<Message<PosOrDecl>>>>,
        pub explanation_opt: Option<Lazy<Explanation<PosOrDecl>>>,
        pub quickfixes_opt: Option<Vec<Quickfix<Pos>>>,
    }

    fn of_eval_primary(t: eval_primary::T) -> T {
        let eval_primary::T {
            code,
            claim,
            reasons,
            quickfixes,
        } = t;
        T {
            code,
            claim,
            reasons,
            quickfixes,
            explanation: Lazy::new(|| Explanation::Empty),
        }
    }

    pub fn of_eval_secondary_opt(ctx: &Ctx, current_span: &Pos, t: eval_secondary::T) -> Option<T> {
        let eval_secondary::T {
            code,
            reasons,
            explanation,
        } = t;
        match reasons.force().as_slice() {
            [Message(pos, msg), rest @ ..] => {
                let (claim, reasons) =
                    match crate::pos_or_decl::fill_in_filename_if_in_current_decl(ctx, pos) {
                        Some(pos) => {
                            let msg = msg.clone();
                            (Lazy::new(move || Message(pos, msg)), rest.to_vec())
                        }
                        None => common::wrap_error_in_different_file(
                            ctx.file.clone(),
                            current_span.clone(),
                            reasons.force().clone(),
                        ),
                    };
                Some(T {
                    code,
                    claim,
                    reasons: Lazy::new(move || reasons),
                    explanation,
                    quickfixes: vec![],
                })
            }
            [] => None,
        }
    }

    pub fn eval(t: &typing_error::T, env: &Env, current_span: &Pos) -> eval_result::T<T> {
        // The OCaml `aux` and `auxs` take a continuation `k`, so that they are
        // tail recursive. A continuation is only ever applied to the result
        // of the recursive call it is passed to, so plain recursion evaluates
        // the same things in the same order.
        fn aux(t: &typing_error::T, env: &Env, current_span: &Pos) -> eval_result::T<T> {
            use typing_error::T::*;
            match t {
                Primary(base) => {
                    eval_result::single(of_eval_primary(eval_primary::to_error((**base).clone(), env)))
                }
                With_code(t, code) => {
                    let code = *code;
                    eval_result::map(aux(t, env, current_span), |t| T { code, ..t })
                }
                With_pos(t, pos) => eval_result::map(aux(t, env, current_span), |t| {
                    let T {
                        code,
                        claim,
                        reasons,
                        explanation,
                        quickfixes,
                    } = t;
                    let pos = pos.clone();
                    T {
                        code,
                        claim: claim.map(move |Message(_, s)| Message(pos, s.clone())),
                        reasons,
                        explanation,
                        quickfixes,
                    }
                }),
                Intersection(ts) => eval_result::intersect(auxs(ts, env, current_span)),
                Union(ts) => eval_result::union(auxs(ts, env, current_span)),
                Multiple(ts) => eval_result::multiple(auxs(ts, env, current_span)),
                Apply(cb, err) => eval_result::bind(aux(err, env, current_span), |t| {
                    let T {
                        code,
                        claim,
                        reasons,
                        explanation,
                        quickfixes,
                    } = t;
                    eval_result::single(eval_callback::apply(
                        Partial {
                            claim,
                            code_opt: Some(code),
                            reasons_opt: Some(reasons),
                            explanation_opt: Some(explanation),
                            quickfixes_opt: Some(quickfixes),
                        },
                        cb,
                        env,
                    ))
                }),
                Apply_reasons(cb, snd_err) => eval_result::bind(
                    eval_secondary::eval(snd_err, env, current_span),
                    |eval_snd| eval_reasons_callback::apply_help(eval_snd, cb, env, current_span),
                ),
                Assert_in_current_decl(snd_err, ctx) => {
                    eval_result::bind(eval_secondary::eval(snd_err, env, current_span), |e| {
                        eval_result::of_option(of_eval_secondary_opt(ctx, current_span, e))
                    })
                }
                Deferred(d) => aux(d.force(), env, current_span),
            }
        }
        fn auxs(ts: &[typing_error::T], env: &Env, current_span: &Pos) -> Vec<eval_result::T<T>> {
            let mut xs = Vec::with_capacity(ts.len());
            for next in ts {
                xs.push(aux(next, env, current_span))
            }
            xs
        }
        aux(t, env, current_span)
    }

    fn make_error(t: T, custom_msgs: Vec<String>, function_pos: Pos) -> Diagnostic {
        let T {
            code,
            claim,
            reasons,
            explanation,
            quickfixes,
        } = t;
        // The arguments of an OCaml application are evaluated from the last
        // to the first.
        let explanation = explanation.force().clone();
        let reasons = reasons.force().clone();
        let claim = claim.force().clone();
        crate::user_diagnostic::make_err(
            code as isize,
            None,
            Some(quickfixes),
            Some(custom_msgs),
            Some(function_pos),
            claim,
            reasons,
            explanation,
        )
    }

    fn render_custom_error(
        t: &[itertools::Either<String, crate::custom_error_eval::value::T>],
        env: &Env,
    ) -> String {
        use itertools::Either;

        use crate::custom_error_eval::value;
        // `List.fold_right`: from the last element to the first.
        let mut acc = String::new();
        for v in t.iter().rev() {
            acc = match v {
                Either::Left(str) => format!("{}{}", str, acc),
                Either::Right(value::T::Name(class_name)) => {
                    format!("{}{}", md_codify(strip_ns(class_name)), acc)
                }
                Either::Right(value::T::MemberName(nm)) => format!("{}{}", md_codify(nm), acc),
                Either::Right(value::T::File(rel_path)) => {
                    let path = crate::relative_path::to_absolute(rel_path);
                    format!("{}{}", md_codify(&path), acc)
                }
                Either::Right(value::T::Ty(ty)) => format!(
                    "{}{}",
                    md_codify(&crate::typing_print::full_strip_ns_i(
                        true,
                        env,
                        &crate::typing_defs_constraints::InternalType::LoclType(ty.clone()),
                    )),
                    acc
                ),
            }
        }
        acc
    }

    pub fn to_user_diagnostic(
        t: &typing_error::T,
        env: &Env,
        current_span: &Pos,
    ) -> eval_result::T<Diagnostic> {
        let result = eval(t, env, current_span);
        let custom_err_config =
            crate::typechecker_options::custom_error_config(&crate::typing_env::get_tcopt(env));
        let custom_msgs: Vec<String> =
            crate::custom_error_eval::eval_typing_error(&custom_err_config, t)
                .iter()
                .map(|t| render_custom_error(t, env))
                .collect();
        let function_pos = env.genv.function_pos.clone();
        eval_result::map(result, |t| {
            make_error(t, custom_msgs.clone(), function_pos.clone())
        })
    }
}

pub mod eval_secondary {
    use oxidized::global_options::ExtendedReasonsConfig;

    use super::super::common;
    use super::eval_error;
    use super::*;
    use crate::typing_defs_constraints::ConstraintType_;
    use crate::typing_defs_constraints::InternalType;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::Ty_;
    use crate::typing_error::secondary;
    use crate::typing_reason;

    /// `Eval_secondary.t`
    #[derive(Clone, Debug)]
    pub struct T {
        pub code: ErrorCode,
        pub reasons: Lazy<Vec<Message<PosOrDecl>>>,
        pub explanation: Lazy<Explanation<PosOrDecl>>,
    }

    /// `create ~code ?(reasons = lazy []) ?(explanation = lazy Explanation.empty) ()`
    fn create(
        code: ErrorCode,
        reasons: Option<Lazy<Vec<Message<PosOrDecl>>>>,
        explanation: Option<Lazy<Explanation<PosOrDecl>>>,
    ) -> T {
        let reasons = reasons.unwrap_or_else(|| Lazy::new(Vec::new));
        let explanation = explanation.unwrap_or_else(|| Lazy::new(|| Explanation::Empty));
        T {
            code,
            reasons,
            explanation,
        }
    }

    fn fun_too_many_args(pos: PosOrDecl, decl_pos: PosOrDecl, actual: isize, expected: isize) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!(
                        "Too many mandatory arguments (expected {} but got {})",
                        expected, actual
                    )
                    .into(),
                ),
                Message(decl_pos, "Because of this definition".into()),
            ]
        });
        create(ErrorCode::FunTooManyArgs, Some(reasons), None)
    }

    fn fun_too_few_args(pos: PosOrDecl, decl_pos: PosOrDecl, actual: isize, expected: isize) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!(
                        "Too few positional arguments (required {} but got {})",
                        expected, actual
                    )
                    .into(),
                ),
                Message(decl_pos, "Because of this definition".into()),
            ]
        });
        create(ErrorCode::FunTooFewArgs, Some(reasons), None)
    }

    fn fun_unexpected_nonvariadic(pos: PosOrDecl, decl_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(pos, "Should have a variadic argument".into()),
                Message(decl_pos, "Because of this definition".into()),
            ]
        });
        create(ErrorCode::FunUnexpectedNonvariadic, Some(reasons), None)
    }

    fn fun_variadicity_hh_vs_php56(pos: PosOrDecl, decl_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "Variadic arguments: `...`-style is not a subtype of `...$args`".into(),
                ),
                Message(decl_pos, "Because of this definition".into()),
            ]
        });
        create(ErrorCode::FunVariadicityHhVsPhp56, Some(reasons), None)
    }

    fn fun_extra_named_args(pos: PosOrDecl, decl_pos: PosOrDecl, extra_names: Vec<String>) -> T {
        let names_str = extra_names.join(", ");
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!(
                        "Unexpected named parameter{}: {}",
                        if extra_names.len() > 1 { "s" } else { "" },
                        names_str
                    )
                    .into(),
                ),
                Message(decl_pos, "Because of this definition".into()),
            ]
        });
        create(ErrorCode::FunTooManyArgs, Some(reasons), None)
    }

    fn fun_missing_named_args(
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        missing_names: Vec<String>,
    ) -> T {
        let names_str = missing_names.join(", ");
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!(
                        "Missing required named parameter{}: {}",
                        if missing_names.len() > 1 { "s" } else { "" },
                        names_str
                    )
                    .into(),
                ),
                Message(decl_pos, "Because of this definition".into()),
            ]
        });
        create(ErrorCode::FunTooFewArgs, Some(reasons), None)
    }

    fn fun_param_required_but_expected_optional(
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        param_names: Vec<String>,
    ) -> T {
        let names_str = param_names.join(", ");
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    if param_names.is_empty() {
                        "Parameter required but expected to be optional".into()
                    } else {
                        format!(
                            "Named parameter{} {} {} required but expected to be optional",
                            if param_names.len() > 1 { "s" } else { "" },
                            names_str,
                            if param_names.len() > 1 { "are" } else { "is" }
                        )
                        .into()
                    },
                ),
                Message(decl_pos, "Because of this definition".into()),
            ]
        });
        create(ErrorCode::BadMethodOverride, Some(reasons), None)
    }

    fn type_arity_mismatch(
        pos: PosOrDecl,
        actual: isize,
        decl_pos: PosOrDecl,
        expected: isize,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(pos, format!("This type has {} arguments", actual).into()),
                Message(decl_pos, format!("This one has {}", expected).into()),
            ]
        });
        create(ErrorCode::TypeArityMismatch, Some(reasons), None)
    }

    fn describe_coeffect(env: &Env, ty: &Ty) -> Lazy<String> {
        // `Typing_utils.simplify_intersections` returns a new environment,
        // which is only used to print the type: it works on a copy.
        let mut env = env.clone();
        let ty = ty.clone();
        Lazy::new(move || {
            let ty = crate::typing_utils::simplify_intersections(&mut env, None, &ty);
            crate::typing_print::coeffects(&env, &ty)
        })
    }

    fn describe_ty_default(env: &Env, ty: &InternalType) -> String {
        crate::typing_print::full_strip_ns_i(true, env, ty)
    }

    // The OCaml returns a closure, to check `is_coeffect` once when it is
    // partially applied.
    fn describe_ty(is_coeffect: bool, env: &Env, ty: &InternalType) -> String {
        if !is_coeffect {
            describe_ty_default(env, ty)
        } else {
            match ty {
                InternalType::LoclType(ty) => describe_coeffect(env, ty).force().clone(),
                ty => describe_ty_default(env, ty),
            }
        }
    }

    fn describe_ty_super(is_coeffect: bool, env: &Env, ty: &InternalType) -> String {
        // `print` and `default` use the `env` and the `ty` that the function is
        // called with, not the ones that shadow them below.
        let print = |ty: &InternalType| describe_ty(is_coeffect, env, ty);
        let default = || print(ty);
        match ty {
            InternalType::LoclType(ty) => {
                // `Typing_env.expand_type` returns a new environment, which is
                // the one used from here on, but which is not returned: it is
                // a copy.
                let mut env = env.clone();
                let ty = crate::typing_env::expand_type(&mut env, ty.clone());
                let env = &env;
                match crate::typing_defs_core::get_node(&ty) {
                    Ty_::Tvar(v) => {
                        // `Internal_type_set.elements`
                        let upper_bounds: Vec<InternalType> =
                            crate::typing_env::get_tyvar_upper_bounds(env, v.clone())
                                .iter()
                                .cloned()
                                .collect();
                        // The constraint graph is transitively closed so we can filter tyvars.
                        let upper_bounds: Vec<InternalType> = upper_bounds
                            .into_iter()
                            .filter(|t| !crate::typing_defs_constraints::is_tyvar_i(t))
                            .collect();
                        if upper_bounds.is_empty() {
                            "some type not known yet".to_string()
                        } else {
                            let tyl = upper_bounds;
                            let (locl_tyl, cstr_tyl): (Vec<InternalType>, Vec<InternalType>) = tyl
                                .into_iter()
                                .partition(crate::typing_defs_constraints::is_locl_type);
                            let sep = if !locl_tyl.is_empty() && !cstr_tyl.is_empty() {
                                " and "
                            } else {
                                ""
                            };
                            let locl_descr = if locl_tyl.is_empty() {
                                String::new()
                            } else {
                                format!(
                                    "of type {}",
                                    md_codify(
                                        &locl_tyl
                                            .iter()
                                            .map(|ty| print(ty))
                                            .collect::<Vec<_>>()
                                            .join(" & ")
                                    )
                                )
                            };
                            let cstr_descr = cstr_tyl
                                .iter()
                                .map(|ty| describe_ty_super(is_coeffect, env, ty))
                                .collect::<Vec<_>>()
                                .join(" and ");
                            format!("something {}{}{}", locl_descr, sep, cstr_descr)
                        }
                    }
                    Ty_::Toption(ty) if crate::typing_defs::is_tyvar(ty) => format!(
                        "`null` or {}",
                        describe_ty_super(is_coeffect, env, &InternalType::LoclType(ty.clone()))
                    ),
                    _ => md_codify(&default()),
                }
            }
            InternalType::ConstraintType(ty) => {
                let (_, ty_) = crate::typing_defs_constraints::deref_constraint_type(ty);
                match &ty_ {
                    ConstraintType_::ThasMember(hm) => {
                        let oxidized::ast_defs::Id(_, name) = &hm.name;
                        let method_info = &hm.method;
                        match method_info {
                            None => format!("an object with property `{}`", name),
                            Some(_) => format!("an object with method `{}`", name),
                        }
                    }
                    ConstraintType_::ThasTypeMember(htm) => {
                        let id = &htm.id;
                        let lo = &htm.lower;
                        let up = &htm.upper;
                        // OCaml: `phys_equal lo up`, "as a heuristic to
                        // generate slightly more readable descriptions". Two
                        // fields are never the same Rust value, so this is
                        // equality: what is physically equal in OCaml is equal.
                        if lo == up {
                            format!(
                                "a class with `{{type {} = {}}}`",
                                id,
                                describe_ty(false, env, &InternalType::LoclType(lo.clone()))
                            )
                        } else {
                            let bound_desc =
                                |prefix: &str, is_trivial: fn(&Env, &Ty) -> bool, bnd: &Ty| {
                                    if is_trivial(env, bnd) {
                                        String::new()
                                    } else {
                                        format!(
                                            "{}{}",
                                            prefix,
                                            describe_ty(
                                                false,
                                                env,
                                                &InternalType::LoclType(bnd.clone())
                                            )
                                        )
                                    }
                                };
                            format!(
                                "a class with `{{type {}{}{}}}`",
                                id,
                                bound_desc(" super ", crate::typing_utils::is_nothing, lo),
                                bound_desc(" as ", crate::typing_utils::is_mixed, up)
                            )
                        }
                    }
                    ConstraintType_::TcanTraverse(_) => {
                        "an array that can be traversed with foreach".to_string()
                    }
                    ConstraintType_::TcanIndex(_) => "an array that can be indexed".to_string(),
                    ConstraintType_::TcanIndexAssign(_) => {
                        "an array that can be updated".to_string()
                    }
                    ConstraintType_::Tdestructure(_) => {
                        md_codify(&crate::typing_print::full_strip_ns_i(
                            true,
                            env,
                            &InternalType::ConstraintType(ty.clone()),
                        ))
                    }
                    ConstraintType_::TtypeSwitch { .. } => {
                        md_codify(&crate::typing_print::full_strip_ns_i(
                            true,
                            env,
                            &InternalType::ConstraintType(ty.clone()),
                        ))
                    }
                    ConstraintType_::ThasConst { name, ty: _ } => {
                        format!("a class with a constant `{}`", name)
                    }
                }
            }
        }
    }

    fn describe_ty_sub(is_coeffect: bool, env: &Env, ety: &InternalType) -> String {
        let ty_descr = describe_ty(is_coeffect, env, ety);
        let ty_constraints = match ety {
            InternalType::LoclType(ty) => crate::typing_print::constraints_for_type(true, env, ty),
            InternalType::ConstraintType(_) => String::new(),
        };

        let ty_constraints =
            // Don't say `T as T` as it's not helpful (occurs in some coffect errors).
            if ty_constraints == format!("as {}", ty_descr) {
                String::new()
            } else if ty_constraints.is_empty() {
                String::new()
            } else {
                format!(" {}", ty_constraints)
            };
        md_codify(&format!("{}{}", ty_descr, ty_constraints))
    }

    fn explain_subtype_failure(
        is_coeffect: bool,
        ty_sub: &InternalType,
        ty_sup: &InternalType,
        env: &Env,
    ) -> (Lazy<Vec<Message<PosOrDecl>>>, Lazy<Explanation<PosOrDecl>>) {
        let r_super = typing_reason::reverse_flow(crate::typing_defs_constraints::reason(ty_sup));
        let r_sub: typing_reason::T = crate::typing_defs_constraints::reason(ty_sub).clone();
        let reasons = {
            // The types are described when the reasons are forced, with the
            // environment the error is evaluated in.
            let env = env.clone();
            let ty_sub = ty_sub.clone();
            let ty_sup = ty_sup.clone();
            let r_super = r_super.clone();
            let r_sub = r_sub.clone();
            Lazy::new(move || {
                let ty_super_descr = describe_ty_super(is_coeffect, &env, &ty_sup);
                let ty_sub_descr = describe_ty_sub(is_coeffect, &env, &ty_sub);
                let (ty_super_descr, ty_sub_descr) = if ty_super_descr == ty_sub_descr {
                    (
                        format!("exactly the type {}", ty_super_descr),
                        format!("the nonexact type {}", ty_sub_descr),
                    )
                } else {
                    (ty_super_descr, ty_sub_descr)
                };
                let left = messages(typing_reason::to_string(
                    &format!("Expected {}", ty_super_descr),
                    &r_super,
                ));
                let right = messages(typing_reason::to_string(
                    &format!("But got {}", ty_sub_descr),
                    &r_sub,
                ));
                append(&left, &right)
            })
        };

        let lod = crate::typechecker_options::tco_extended_reasons(&env.genv.tcopt)
            .unwrap_or(ExtendedReasonsConfig::Legacy);
        let explanation = match lod {
            ExtendedReasonsConfig::Legacy => {
                Lazy::new(move || typing_reason::explain(&r_sub, &r_super, 1))
            }
            ExtendedReasonsConfig::Extended(complexity) => {
                Lazy::new(move || typing_reason::explain(&r_sub, &r_super, complexity))
            }
            ExtendedReasonsConfig::Debug => {
                Lazy::new(move || typing_reason::debug_reason(&r_sub, &r_super))
            }
        };
        (reasons, explanation)
    }

    fn subtyping_error(
        is_coeffect: bool,
        ty_sub: &InternalType,
        ty_sup: &InternalType,
        env: &Env,
    ) -> T {
        let (reasons, explanation) = explain_subtype_failure(is_coeffect, ty_sub, ty_sup, env);
        create(ErrorCode::UnifyError, Some(reasons), Some(explanation))
    }

    fn violated_constraint(
        cstrs: Vec<(PosOrDecl, Message<PosOrDecl>)>,
        is_coeffect: bool,
        ty_sub: &InternalType,
        ty_sup: &InternalType,
        env: &Env,
    ) -> T {
        let (reasons, explanation) = explain_subtype_failure(is_coeffect, ty_sub, ty_sup, env);
        let reasons = reasons.map(move |reasons| {
            let pos_msg = "This type constraint is violated";
            let f = |(p_cstr, Message(p_tparam, tparam)): &(PosOrDecl, Message<PosOrDecl>)| {
                vec![
                    Message(
                        p_tparam.clone(),
                        format!(
                            "{} is a constrained type parameter",
                            md_codify(&tparam.to_string())
                        )
                        .into(),
                    ),
                    Message(p_cstr.clone(), pos_msg.into()),
                ]
            };
            let msgs: Vec<Message<PosOrDecl>> = cstrs.iter().flat_map(f).collect();
            append(&msgs, reasons)
        });
        create(
            ErrorCode::TypeConstraintViolation,
            Some(reasons),
            Some(explanation),
        )
    }

    fn concrete_const_interface_override(
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        name: String,
        parent_origin: String,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "Non-abstract constants defined in an interface cannot be overridden when implementing or extending that interface."
                        .into(),
                ),
                Message(
                    parent_pos,
                    format!(
                        "You could make {} abstract in {}.",
                        md_codify(&name),
                        md_codify(strip_ns(&parent_origin))
                    )
                    .into(),
                ),
            ]
        });
        create(
            ErrorCode::ConcreteConstInterfaceOverride,
            Some(reasons),
            None,
        )
    }

    fn interface_or_trait_const_multiple_defs(
        pos: PosOrDecl,
        origin: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
        name: String,
    ) -> T {
        let reasons = Lazy::new(move || {
            let parent_origin = strip_ns(&parent_origin);
            let child_origin = strip_ns(&origin);
            vec![
                Message(
                    pos.clone(),
                    "Non-abstract constants defined in an interface or trait cannot conflict with other inherited constants."
                        .into(),
                ),
                Message(
                    parent_pos,
                    format!(
                        "{} inherited from {}",
                        md_codify(&name),
                        md_codify(parent_origin)
                    )
                    .into(),
                ),
                Message(
                    pos,
                    format!(
                        "conflicts with constant {} inherited from {}.",
                        md_codify(&name),
                        md_codify(child_origin)
                    )
                    .into(),
                ),
            ]
        });
        create(
            ErrorCode::ConcreteConstInterfaceOverride,
            Some(reasons),
            None,
        )
    }

    fn interface_typeconst_multiple_defs(
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        name: String,
        origin: String,
        parent_origin: String,
        is_abstract: bool,
    ) -> T {
        let reasons = Lazy::new(move || {
            let parent_origin = strip_ns(&parent_origin);
            let child_origin = strip_ns(&origin);
            let child_pos = pos.clone();
            let child = if is_abstract {
                "abstract type constant with default value"
            } else {
                "concrete type constant"
            };
            vec![
                Message(
                    pos,
                    [
                        "Concrete and abstract type constants with default values in an interface cannot conflict with inherited",
                        " concrete or abstract type constants with default values.",
                    ]
                    .concat()
                    .into(),
                ),
                Message(
                    parent_pos,
                    format!(
                        "{} inherited from {}",
                        md_codify(&name),
                        md_codify(parent_origin)
                    )
                    .into(),
                ),
                Message(
                    child_pos,
                    format!(
                        "conflicts with {} {} inherited from {}.",
                        md_codify(child),
                        md_codify(&name),
                        md_codify(child_origin)
                    )
                    .into(),
                ),
            ]
        });
        create(
            ErrorCode::ConcreteConstInterfaceOverride,
            Some(reasons),
            None,
        )
    }

    fn missing_field(
        pos: PosOrDecl,
        name: String,
        decl_pos: PosOrDecl,
        reason_sub: typing_reason::T,
        reason_super: &typing_reason::T,
        env: &Env,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!("The field {} is missing", md_codify(&name)).into(),
                ),
                Message(
                    decl_pos,
                    format!("The field {} is required here", md_codify(&name)).into(),
                ),
            ]
        });
        let reason_super = typing_reason::reverse_flow(reason_super);
        let lod = crate::typechecker_options::tco_extended_reasons(&env.genv.tcopt)
            .unwrap_or(ExtendedReasonsConfig::Legacy);
        let explanation = match lod {
            ExtendedReasonsConfig::Legacy => {
                Lazy::new(move || typing_reason::explain(&reason_sub, &reason_super, 1))
            }
            ExtendedReasonsConfig::Extended(complexity) => {
                Lazy::new(move || typing_reason::explain(&reason_sub, &reason_super, complexity))
            }
            ExtendedReasonsConfig::Debug => {
                Lazy::new(move || typing_reason::debug_reason(&reason_sub, &reason_super))
            }
        };
        create(ErrorCode::MissingField, Some(reasons), Some(explanation))
    }

    fn shape_fields_unknown(pos: PosOrDecl, decl_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "This shape type allows unknown fields, and so it may contain fields other than those explicitly declared in its declaration."
                        .into(),
                ),
                Message(
                    decl_pos,
                    "It is incompatible with a shape that does not allow unknown fields.".into(),
                ),
            ]
        });
        create(ErrorCode::ShapeFieldsUnknown, Some(reasons), None)
    }

    fn splat_may_require_fields(pos: PosOrDecl, decl_pos: PosOrDecl, name: Option<&str>) -> T {
        let explanation = match name {
            Some(name) => format!("{} may have required fields of its own", md_codify(name)),
            None => "This may require fields beyond those written here".to_string(),
        };
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "This shape is not guaranteed to have the fields required here".into(),
                ),
                Message(decl_pos, explanation.into()),
            ]
        });
        create(ErrorCode::SplatMayRequireFields, Some(reasons), None)
    }

    fn splat_field_not_known(pos: PosOrDecl, decl_pos: PosOrDecl, name: &str, field: &str) -> T {
        let name = md_codify(name);
        let field = md_codify(field);
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!(
                        "The field {} here is not compatible with every instantiation of {}",
                        field, name
                    )
                    .into(),
                ),
                Message(
                    decl_pos,
                    format!("{} may provide {} with a type of its own", name, field).into(),
                ),
            ]
        });
        create(ErrorCode::SplatFieldNotKnown, Some(reasons), None)
    }

    fn abstract_tconst_not_allowed(pos: PosOrDecl, decl_pos: PosOrDecl, tconst_name: String) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!(
                        "An abstract type constant is not allowed in this position. Did you mean {}?",
                        md_codify(&format!("this::{}", tconst_name))
                    )
                    .into(),
                ),
                Message(
                    decl_pos,
                    format!("{} is abstract here.", md_codify(&tconst_name)).into(),
                ),
            ]
        });
        create(ErrorCode::AbstractTconstNotAllowed, Some(reasons), None)
    }

    fn invalid_destructure(pos: PosOrDecl, decl_pos: PosOrDecl, ty_name: Lazy<String>) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "This expression cannot be destructured with a `list(...)` expression".into(),
                ),
                Message(
                    decl_pos,
                    format!("This is {}", md_codify(ty_name.force())).into(),
                ),
            ]
        });
        create(ErrorCode::InvalidDestructure, Some(reasons), None)
    }

    fn unpack_array_required_argument(pos: PosOrDecl, decl_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "An array cannot be unpacked into the required arguments of a function".into(),
                ),
                Message(decl_pos, "Definition is here".into()),
            ]
        });
        create(ErrorCode::SplatArrayRequired, Some(reasons), None)
    }

    fn unpack_array_variadic_argument(pos: PosOrDecl, decl_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "A function that receives an unpacked array as an argument must have a variadic parameter to accept the elements of the array"
                        .into(),
                ),
                Message(decl_pos, "Definition is here".into()),
            ]
        });
        create(ErrorCode::SplatArrayRequired, Some(reasons), None)
    }

    fn overriding_prop_const_mismatch(pos: PosOrDecl, is_const: bool, parent_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            let (msg, reason_msg) = if is_const {
                (
                    "This property is `__Const`",
                    "This property is not `__Const`",
                )
            } else {
                (
                    "This property is not `__Const`",
                    "This property is `__Const`",
                )
            };
            vec![
                Message(pos, msg.into()),
                Message(parent_pos, reason_msg.into()),
            ]
        });
        create(ErrorCode::OverridingPropConstMismatch, Some(reasons), None)
    }

    fn visibility_extends(
        pos: PosOrDecl,
        vis: String,
        parent_pos: PosOrDecl,
        parent_vis: String,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!("This member visibility is: {}", md_codify(&vis)).into(),
                ),
                Message(
                    parent_pos,
                    format!("{} was expected", md_codify(&parent_vis)).into(),
                ),
            ]
        });
        create(ErrorCode::VisibilityExtends, Some(reasons), None)
    }

    fn visibility_override_internal(
        pos: PosOrDecl,
        module_name: Option<String>,
        parent_module: String,
        parent_pos: PosOrDecl,
    ) -> T {
        let reasons = Lazy::new(move || {
            let msg = match module_name {
                None => format!(
                    "Cannot override this member outside module `{}`",
                    parent_module
                ),
                Some(m) => format!("Cannot override this member in module `{}`", m),
            };
            vec![
                Message(pos, msg.into()),
                Message(
                    parent_pos,
                    format!("This member is internal to module `{}`", parent_module).into(),
                ),
            ]
        });
        create(ErrorCode::ModuleError, Some(reasons), None)
    }

    fn missing_constructor(pos: PosOrDecl) -> T {
        let reasons =
            Lazy::new(move || vec![Message(pos, "The constructor is not implemented".into())]);
        create(ErrorCode::MissingConstructor, Some(reasons), None)
    }

    fn accept_disposable_invariant(pos: PosOrDecl, decl_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "This parameter is marked `<<__AcceptDisposable>>`".into(),
                ),
                Message(
                    decl_pos,
                    "This parameter is not marked `<<__AcceptDisposable>>`".into(),
                ),
            ]
        });
        create(ErrorCode::AcceptDisposableInvariant, Some(reasons), None)
    }

    fn required_field_is_optional(
        pos: PosOrDecl,
        name: String,
        decl_pos: PosOrDecl,
        def_pos: PosOrDecl,
        r_sub: typing_reason::T,
        r_super: &typing_reason::T,
        env: &Env,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!("The field {} is **optional**", md_codify(&name)).into(),
                ),
                Message(
                    decl_pos,
                    format!("The field {} is defined as **required**", md_codify(&name)).into(),
                ),
                Message(
                    def_pos,
                    format!("{} is defined here", md_codify(&name)).into(),
                ),
            ]
        });
        let r_super = typing_reason::reverse_flow(r_super);
        let lod = crate::typechecker_options::tco_extended_reasons(&env.genv.tcopt)
            .unwrap_or(ExtendedReasonsConfig::Legacy);
        let explanation = match lod {
            ExtendedReasonsConfig::Legacy => {
                Lazy::new(move || typing_reason::explain(&r_sub, &r_super, 1))
            }
            ExtendedReasonsConfig::Extended(complexity) => {
                Lazy::new(move || typing_reason::explain(&r_sub, &r_super, complexity))
            }
            ExtendedReasonsConfig::Debug => {
                Lazy::new(move || typing_reason::debug_reason(&r_sub, &r_super))
            }
        };
        create(
            ErrorCode::RequiredFieldIsOptional,
            Some(reasons),
            Some(explanation),
        )
    }

    fn return_disposable_mismatch(
        pos_sub: PosOrDecl,
        is_marked_return_disposable: bool,
        pos_super: PosOrDecl,
    ) -> T {
        let reasons = Lazy::new(move || {
            let (msg, reason_msg) = if is_marked_return_disposable {
                (
                    "This is marked `<<__ReturnDisposable>>`.",
                    "This is not marked `<<__ReturnDisposable>>`.",
                )
            } else {
                (
                    "This is not marked `<<__ReturnDisposable>>`.",
                    "This is marked `<<__ReturnDisposable>>`.",
                )
            };
            vec![
                Message(pos_super, msg.into()),
                Message(pos_sub, reason_msg.into()),
            ]
        });
        create(ErrorCode::ReturnDisposableMismatch, Some(reasons), None)
    }

    fn override_final(pos: PosOrDecl, parent_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(pos, "You cannot override this method".into()),
                Message(parent_pos, "It was declared as final".into()),
            ]
        });
        create(ErrorCode::OverrideFinal, Some(reasons), None)
    }

    fn override_tests_bypass_visibility(
        pos: PosOrDecl,
        member_name: String,
        parent_pos: PosOrDecl,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!("Cannot override or shadow `{}`", member_name).into(),
                ),
                Message(
                    parent_pos,
                    "This concrete private member is in the same hierarchy as a member marked with `<<__TestsBypassVisibility>>`"
                        .into(),
                ),
            ]
        });
        create(
            ErrorCode::TestsBypassVisibilityOverride,
            Some(reasons),
            None,
        )
    }

    fn abstract_tests_bypass_visibility_missing_attr(
        pos: PosOrDecl,
        member_name: String,
        parent_pos: PosOrDecl,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!(
                        "`{}` must also have `<<__TestsBypassVisibility>>` because it overrides a method with the attribute",
                        member_name
                    )
                    .into(),
                ),
                Message(
                    parent_pos,
                    "The parent method was declared with `<<__TestsBypassVisibility>>` here"
                        .into(),
                ),
            ]
        });
        create(
            ErrorCode::TestsBypassVisibilityAbstractMissingAttr,
            Some(reasons),
            None,
        )
    }

    fn override_async(pos: PosOrDecl, parent_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "You cannot override this method with a non-async method".into(),
                ),
                Message(parent_pos, "It was declared as async".into()),
            ]
        });
        create(ErrorCode::OverrideAsync, Some(reasons), None)
    }

    fn override_lsb(pos: PosOrDecl, member_name: String, parent_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!(
                        "Member {} may not override `__LSB` member of parent",
                        md_codify(&member_name)
                    )
                    .into(),
                ),
                Message(parent_pos, "This is being overridden".into()),
            ]
        });
        create(ErrorCode::OverrideLSB, Some(reasons), None)
    }

    fn multiple_concrete_defs(
        pos: PosOrDecl,
        origin: String,
        name: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
        class_name: String,
    ) -> T {
        let reasons = Lazy::new(move || {
            let child_origin = md_codify(strip_ns(&origin));
            let parent_origin = md_codify(strip_ns(&parent_origin));
            let class_ = md_codify(strip_ns(&class_name));
            let name = md_codify(&name);
            vec![
                Message(
                    pos.clone(),
                    format!(
                        "{} and {} both declare ambiguous implementations of {}.",
                        child_origin, parent_origin, name
                    )
                    .into(),
                ),
                Message(
                    pos.clone(),
                    format!("{}'s definition is here.", child_origin).into(),
                ),
                Message(
                    parent_pos,
                    format!("{}'s definition is here.", parent_origin).into(),
                ),
                Message(
                    pos,
                    format!(
                        "Redeclare {} in {} with a compatible signature.",
                        name, class_
                    )
                    .into(),
                ),
            ]
        });
        create(ErrorCode::MultipleConcreteDefs, Some(reasons), None)
    }

    fn cyclic_enum_constraint(pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || vec![Message(pos, "Cyclic enum constraint".into())]);
        create(ErrorCode::CyclicEnumConstraint, Some(reasons), None)
    }

    fn inoutness_mismatch(pos: PosOrDecl, decl_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(pos, "This is an `inout` parameter".into()),
                Message(
                    decl_pos,
                    "It is incompatible with a normal parameter".into(),
                ),
            ]
        });
        create(ErrorCode::InoutnessMismatch, Some(reasons), None)
    }

    fn bad_lateinit_override(pos: PosOrDecl, parent_pos: PosOrDecl, parent_is_lateinit: bool) -> T {
        let reasons = Lazy::new(move || {
            let verb = if parent_is_lateinit { "is" } else { "is not" };
            vec![
                Message(
                    pos,
                    "Redeclared properties must be consistently declared `__LateInit`".into(),
                ),
                Message(
                    parent_pos,
                    format!("The property {} declared `__LateInit` here", verb).into(),
                ),
            ]
        });

        create(ErrorCode::BadLateInitOverride, Some(reasons), None)
    }

    fn bad_xhp_attr_required_override(
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        parent_tag: String,
        tag: String,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(pos, "Redeclared attribute must not be less strict".into()),
                Message(
                    parent_pos,
                    format!(
                        "The attribute is {}, which is stricter than {}",
                        parent_tag, tag
                    )
                    .into(),
                ),
            ]
        });
        create(ErrorCode::BadXhpAttrRequiredOverride, Some(reasons), None)
    }

    fn coeffect_subtyping(
        pos: PosOrDecl,
        cap: Lazy<String>,
        pos_expected: PosOrDecl,
        cap_expected: Lazy<String>,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos_expected,
                    format!("Expected a function that requires {}", cap_expected.force()).into(),
                ),
                Message(
                    pos,
                    format!("But got a function that requires {}", cap.force()).into(),
                ),
            ]
        });
        create(ErrorCode::SubtypeCoeffects, Some(reasons), None)
    }

    fn not_sub_dynamic(
        pos: PosOrDecl,
        ty_name: Lazy<String>,
        dynamic_part: Lazy<Vec<Message<PosOrDecl>>>,
    ) -> T {
        let reasons = dynamic_part.map(move |xs| {
            append(
                xs,
                &[Message(
                    pos,
                    format!(
                        "Type {} is not a subtype of `dynamic` under dynamic-aware subtyping",
                        md_codify(ty_name.force())
                    )
                    .into(),
                )],
            )
        });
        create(ErrorCode::UnifyError, Some(reasons), None)
    }

    fn override_method_support_dynamic_type(
        pos: PosOrDecl,
        method_name: String,
        parent_origin: String,
        parent_pos: PosOrDecl,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    format!(
                        "Method {} must be declared <<__SupportDynamicType>> because it overrides method in class {} which does.",
                        method_name,
                        strip_ns(&parent_origin)
                    )
                    .into(),
                ),
                Message(parent_pos, "Overridden method is defined here.".into()),
            ]
        });
        create(ErrorCode::ImplementsDynamic, Some(reasons), None)
    }

    fn readonly_mismatch(
        pos: PosOrDecl,
        kind: secondary::ReadonlyMismatchKind,
        reason_sub: Lazy<Vec<Message<PosOrDecl>>>,
        reason_super: Lazy<Vec<Message<PosOrDecl>>>,
    ) -> T {
        let reasons = Lazy::new(move || {
            let reason_sub = reason_sub.force();
            let reason_super = reason_super.force();
            cons(
                Message(
                    pos,
                    match kind {
                        secondary::ReadonlyMismatchKind::fn_ => "Function readonly mismatch",
                        secondary::ReadonlyMismatchKind::fn_return => {
                            "Function readonly return mismatch"
                        }
                        secondary::ReadonlyMismatchKind::param => {
                            "Mismatched parameter readonlyness"
                        }
                    }
                    .into(),
                ),
                &append(reason_sub, reason_super),
            )
        });
        create(ErrorCode::ReadonlyMismatch, Some(reasons), None)
    }

    fn require_package_mismatch(
        pos: PosOrDecl,
        reason_sub: Lazy<Vec<Message<PosOrDecl>>>,
        reason_super: Lazy<Vec<Message<PosOrDecl>>>,
    ) -> T {
        let reasons = Lazy::new(move || {
            let reason_sub = reason_sub.force();
            let reason_super = reason_super.force();
            append(
                &cons(
                    Message(pos, "Mismatch in `__RequirePackage` attribute".into()),
                    reason_sub,
                ),
                reason_super,
            )
        });
        create(ErrorCode::InvalidCrossPackage, Some(reasons), None)
    }

    /// `Lazy.(claim >>= fun x -> reasons >>= fun xs -> return (x :: xs))`
    fn claim_and_reasons(
        claim: Lazy<Message<Pos>>,
        reasons: Lazy<Vec<Message<PosOrDecl>>>,
    ) -> Lazy<Vec<Message<PosOrDecl>>> {
        Lazy::new(move || {
            let x = claim.force();
            let xs = reasons.force();
            cons(x.clone(), xs)
        })
    }

    fn typing_too_many_args(
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
        hint_convert_to_optional: Option<PosOrDecl>,
    ) -> T {
        let (code, claim, reasons) =
            common::typing_too_many_args(pos, decl_pos, actual, expected, hint_convert_to_optional);
        let reasons = claim_and_reasons(claim, reasons);
        create(code, Some(reasons), None)
    }

    fn typing_too_few_args(
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
        hint_missing_optional: Option<PosOrDecl>,
    ) -> T {
        let (code, claim, reasons) =
            common::typing_too_few_args(pos, decl_pos, actual, expected, hint_missing_optional);
        let reasons = claim_and_reasons(claim, reasons);
        create(code, Some(reasons), None)
    }

    fn non_object_member(
        pos: PosOrDecl,
        ctxt: secondary::ReadOrWrite,
        ty_name: Lazy<String>,
        member_name: String,
        kind: secondary::NonObjectMemberKind,
        decl_pos: PosOrDecl,
    ) -> T {
        let (code, claim, reasons) = common::non_object_member(
            pos,
            ctxt,
            ty_name.force().clone(),
            member_name,
            kind,
            decl_pos,
        );
        let reasons = claim_and_reasons(claim, reasons);
        create(code, Some(reasons), None)
    }

    fn rigid_tvar_escape(pos: PosOrDecl, name: String) -> T {
        let reasons = Lazy::new(move || {
            vec![Message(
                pos,
                format!("Rigid type variable {} is escaping", name).into(),
            )]
        });
        create(ErrorCode::RigidTVarEscape, Some(reasons), None)
    }

    fn smember_not_found(
        pos: PosOrDecl,
        kind: secondary::SmemberNotFoundKind,
        member_name: String,
        class_name: String,
        class_pos: PosOrDecl,
        hint: Option<(secondary::InstanceOrStatic, PosOrDecl, String)>,
    ) -> T {
        let (code, claim, reasons) =
            common::smember_not_found(pos, kind, member_name, class_name, class_pos, hint);
        let reasons = claim_and_reasons(claim, reasons);
        create(code, Some(reasons), None)
    }

    fn bad_method_override(pos: PosOrDecl, member_name: &str) -> T {
        let member_name = md_codify(strip_ns(member_name));
        let reasons = Lazy::new(move || {
            vec![Message(
                pos,
                format!(
                    "The method {} is not compatible with the overridden method",
                    member_name
                )
                .into(),
            )]
        });
        create(ErrorCode::BadMethodOverride, Some(reasons), None)
    }

    fn override_sealed(child_pos: PosOrDecl, parent_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    child_pos,
                    "You cannot override the method because it is sealed.".into(),
                ),
                Message(parent_pos, "Declaration is here".into()),
            ]
        });
        create(ErrorCode::OverrideSealed, Some(reasons), None)
    }

    fn bad_member_override_not_subtype(
        is_method: bool,
        class_name: &str,
        parent_name: &str,
        parent_type: &str,
        member_pos: PosOrDecl,
        member_name: &str,
        member_type: &str,
        origin_name: &str,
        origin_type: &str,
        member_parent_pos: PosOrDecl,
        member_parent_type: &str,
        member_parent_origin: &str,
        member_parent_origin_type: &str,
    ) -> T {
        let member_name = md_codify(strip_ns(member_name));
        let class_name = md_codify(strip_ns(class_name));
        let parent_name = md_codify(strip_ns(parent_name));
        let origin_name = md_codify(strip_ns(origin_name));
        let member_parent_origin = md_codify(strip_ns(member_parent_origin));
        let parent_type = md_codify(parent_type);
        let member_type = md_codify(member_type);
        let origin_type = md_codify(origin_type);
        let member_parent_type = md_codify(member_parent_type);
        let member_parent_origin_type = md_codify(member_parent_origin_type);
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    member_pos.clone(),
                    format!(
                        "{} {} has type {} in {}{}",
                        if is_method { "Method" } else { "Property" },
                        member_name,
                        member_type,
                        class_name,
                        if origin_name == class_name {
                            String::new()
                        } else {
                            format!(" and comes from ancestor or trait {}", origin_type)
                        }
                    )
                    .into(),
                ),
                Message(
                    member_parent_pos,
                    format!(
                        "But it has type {} in parent {}{}",
                        member_parent_type,
                        parent_type,
                        if member_parent_origin == parent_name {
                            String::new()
                        } else {
                            format!(
                                " and comes from ancestor or trait {}",
                                member_parent_origin_type
                            )
                        }
                    )
                    .into(),
                ),
                Message(
                    member_pos,
                    format!(
                        "Type {} is not a subtype of {}",
                        member_type, member_parent_type
                    )
                    .into(),
                ),
            ]
        });
        create(ErrorCode::BadMethodOverride, Some(reasons), None)
    }

    fn bad_prop_override(pos: PosOrDecl, member_name: String) -> T {
        let reasons = Lazy::new(move || {
            vec![Message(
                pos,
                format!(
                    "The property {} has the wrong type",
                    md_codify(strip_ns(&member_name))
                )
                .into(),
            )]
        });
        create(ErrorCode::BadMethodOverride, Some(reasons), None)
    }

    fn method_not_dynamically_callable(pos: PosOrDecl, parent_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(parent_pos, "This method is `__DynamicallyCallable`.".into()),
                Message(pos, "This method is **not**.".into()),
            ]
        });
        create(ErrorCode::BadMethodOverride, Some(reasons), None)
    }

    fn this_final(pos_sub: PosOrDecl, pos_super: PosOrDecl, class_name: String) -> T {
        let reasons = Lazy::new(move || {
            let n = md_codify(strip_ns(&class_name));
            let message1 = format!("Since {} is not final", n);
            let message2 = format!("this might not be a {}", n);
            vec![
                Message(pos_super, message1.into()),
                Message(pos_sub, message2.into()),
            ]
        });
        create(ErrorCode::ThisFinal, Some(reasons), None)
    }

    fn typeconst_concrete_concrete_override(pos: PosOrDecl, parent_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(pos, "Cannot re-declare this type constant".into()),
                Message(parent_pos, "Previously defined here".into()),
            ]
        });
        create(
            ErrorCode::TypeconstConcreteConcreteOverride,
            Some(reasons),
            None,
        )
    }

    fn abstract_concrete_override(
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        kind: secondary::AbstractConcreteOverrideKind,
    ) -> T {
        let reasons = Lazy::new(move || {
            let kind_str = match kind {
                secondary::AbstractConcreteOverrideKind::method_ => "method",
                secondary::AbstractConcreteOverrideKind::typeconst => "type constant",
                secondary::AbstractConcreteOverrideKind::constant => "constant",
                secondary::AbstractConcreteOverrideKind::property => "property",
            };
            vec![
                Message(
                    pos,
                    format!("Cannot re-declare this {} as abstract", kind_str).into(),
                ),
                Message(parent_pos, "Previously defined here".into()),
            ]
        });
        create(ErrorCode::AbstractConcreteOverride, Some(reasons), None)
    }

    fn override_no_default_typeconst(pos: PosOrDecl, parent_pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    pos,
                    "This abstract type constant does not have a default type".into(),
                ),
                Message(
                    parent_pos,
                    "It cannot override an abstract type constant that has a default type".into(),
                ),
            ]
        });
        create(ErrorCode::OverrideNoDefaultTypeconst, Some(reasons), None)
    }

    fn unsupported_refinement(pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![Message(
                pos,
                "Unsupported refinement, only class types can be refined".into(),
            )]
        });
        create(ErrorCode::UnsupportedRefinement, Some(reasons), None)
    }

    fn splat_not_a_shape(pos: PosOrDecl) -> T {
        let reasons = Lazy::new(move || {
            vec![Message(
                pos,
                "Only shapes can be unpacked with `...` inside a shape type".into(),
            )]
        });
        create(ErrorCode::InvalidTypeHint, Some(reasons), None)
    }

    fn missing_class_constant(pos: PosOrDecl, class_name: String, const_name: String) -> T {
        let reasons = Lazy::new(move || {
            vec![Message(
                pos,
                format!(
                    "Class {} has no constant {}",
                    md_codify(strip_ns(&class_name)),
                    md_codify(&const_name)
                )
                .into(),
            )]
        });
        create(ErrorCode::SmemberNotFound, Some(reasons), None)
    }

    fn invalid_refined_const_kind(
        pos: PosOrDecl,
        class_name: String,
        const_name: String,
        correct_kind: String,
        wrong_kind: String,
    ) -> T {
        let reasons = Lazy::new(move || {
            vec![Message(
                pos,
                format!(
                    "Constant {} in {} is not a {}, did you mean {}?",
                    md_codify(&const_name),
                    md_codify(strip_ns(&class_name)),
                    wrong_kind,
                    correct_kind
                )
                .into(),
            )]
        });
        create(ErrorCode::InvalidRefinedConstKind, Some(reasons), None)
    }

    fn inexact_tconst_access(pos: PosOrDecl, id: (PosOrDecl, String)) -> T {
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    id.0,
                    format!("Type member `{}` cannot be accessed", id.1).into(),
                ),
                Message(pos, "  on a loose refinement".into()),
            ]
        });
        create(ErrorCode::InexactTConstAccess, Some(reasons), None)
    }

    fn violated_refinement_constraint(
        (kind, pos): (secondary::RefinementConstraintKind, PosOrDecl),
    ) -> T {
        let kind = match kind {
            secondary::RefinementConstraintKind::As => "`as` or `=`",
            secondary::RefinementConstraintKind::Super => "`super`",
        };
        let reasons = Lazy::new(move || {
            vec![Message(
                pos,
                format!("This {} refinement constraint is violated", kind).into(),
            )]
        });
        create(ErrorCode::UnifyError, Some(reasons), None)
    }

    fn label_unknown(
        enum_name: String,
        decl_pos: PosOrDecl,
        most_similar: Option<(String, PosOrDecl)>,
    ) -> T {
        let reasons = Lazy::new(move || {
            let enum_name = md_codify(strip_ns(&enum_name));
            cons(
                Message(decl_pos, format!("{} is defined here", enum_name).into()),
                &match most_similar {
                    Some((similar_name, similar_pos)) => vec![Message(
                        similar_pos,
                        format!("Did you mean {}?", md_codify(&similar_name)).into(),
                    )],
                    None => vec![],
                },
            )
        });
        create(ErrorCode::EnumClassLabelUnknown, Some(reasons), None)
    }

    fn higher_rank_tparam_escape(
        tvar_pos: PosOrDecl,
        pos_with_generic: PosOrDecl,
        generic_reason: typing_reason::T,
        generic_name_opt: Option<String>,
    ) -> T {
        let reasons = match generic_name_opt {
            Some(generic_name) => {
                let msg = "Expected a first-class polymorphic function type.";
                let prefix = format!(
                    "A higher rank generic `{}` will escape its scope",
                    generic_name
                );
                Lazy::new(move || {
                    cons(
                        Message(pos_with_generic, msg.into()),
                        &append(
                            &messages(typing_reason::to_string(&prefix, &generic_reason)),
                            &[Message(tvar_pos, "Please make this type explicit".into())],
                        ),
                    )
                })
            }
            None => {
                let msg = "A higher rank generic will escape its scope";
                let pos = typing_reason::to_pos(&generic_reason);
                Lazy::new(move || {
                    vec![
                        Message(pos, msg.into()),
                        Message(tvar_pos, "Please make this type explicit".into()),
                    ]
                })
            }
        };
        create(ErrorCode::RigidTVarEscape, Some(reasons), None)
    }

    pub fn eval(t: &secondary::T, env: &Env, current_span: &Pos) -> eval_result::T<T> {
        use secondary::T::*;
        match t {
            Of_error(err) => eval_result::map(eval_error::eval(err, env, current_span), |t| {
                let eval_error::T {
                    code,
                    claim,
                    reasons,
                    explanation,
                    quickfixes: _,
                } = t;
                // We discard quickfixes here because a secondary error
                // can be in a decl and it doesn't make sense to quickfix a decl
                let reasons = claim_and_reasons(claim, reasons);
                T {
                    code,
                    reasons,
                    explanation,
                }
            }),
            Fun_too_many_args {
                pos,
                decl_pos,
                actual,
                expected,
            } => eval_result::single(fun_too_many_args(
                pos.clone(),
                decl_pos.clone(),
                *actual,
                *expected,
            )),
            Fun_too_few_args {
                pos,
                decl_pos,
                actual,
                expected,
            } => eval_result::single(fun_too_few_args(
                pos.clone(),
                decl_pos.clone(),
                *actual,
                *expected,
            )),
            Fun_unexpected_nonvariadic { pos, decl_pos } => {
                eval_result::single(fun_unexpected_nonvariadic(pos.clone(), decl_pos.clone()))
            }
            Fun_variadicity_hh_vs_php56 { pos, decl_pos } => {
                eval_result::single(fun_variadicity_hh_vs_php56(pos.clone(), decl_pos.clone()))
            }
            Fun_extra_named_args {
                pos,
                decl_pos,
                extra_names,
            } => eval_result::single(fun_extra_named_args(
                pos.clone(),
                decl_pos.clone(),
                extra_names.clone(),
            )),
            Fun_missing_named_args {
                pos,
                decl_pos,
                missing_names,
            } => eval_result::single(fun_missing_named_args(
                pos.clone(),
                decl_pos.clone(),
                missing_names.clone(),
            )),
            Fun_param_required_but_expected_optional {
                pos,
                decl_pos,
                param_names,
            } => eval_result::single(fun_param_required_but_expected_optional(
                pos.clone(),
                decl_pos.clone(),
                param_names.clone(),
            )),
            Type_arity_mismatch {
                pos,
                actual,
                decl_pos,
                expected,
            } => eval_result::single(type_arity_mismatch(
                pos.clone(),
                *actual,
                decl_pos.clone(),
                *expected,
            )),
            Concrete_const_interface_override {
                pos,
                parent_pos,
                name,
                parent_origin,
            } => eval_result::single(concrete_const_interface_override(
                pos.clone(),
                parent_pos.clone(),
                name.clone(),
                parent_origin.clone(),
            )),
            Interface_or_trait_const_multiple_defs {
                pos,
                origin,
                parent_pos,
                parent_origin,
                name,
            } => eval_result::single(interface_or_trait_const_multiple_defs(
                pos.clone(),
                origin.clone(),
                parent_pos.clone(),
                parent_origin.clone(),
                name.clone(),
            )),
            Interface_typeconst_multiple_defs {
                pos,
                parent_pos,
                name,
                origin,
                parent_origin,
                is_abstract,
            } => eval_result::single(interface_typeconst_multiple_defs(
                pos.clone(),
                parent_pos.clone(),
                name.clone(),
                origin.clone(),
                parent_origin.clone(),
                *is_abstract,
            )),
            Missing_field {
                pos,
                name,
                decl_pos,
                reason_sub,
                reason_super,
            } => eval_result::single(missing_field(
                pos.clone(),
                name.clone(),
                decl_pos.clone(),
                reason_sub.clone(),
                reason_super,
                env,
            )),
            Shape_fields_unknown { pos, decl_pos } => {
                eval_result::single(shape_fields_unknown(pos.clone(), decl_pos.clone()))
            }
            Splat_may_require_fields {
                pos,
                decl_pos,
                name,
            } => eval_result::single(splat_may_require_fields(
                pos.clone(),
                decl_pos.clone(),
                name.as_deref(),
            )),
            Splat_field_not_known {
                pos,
                decl_pos,
                name,
                field,
            } => eval_result::single(splat_field_not_known(
                pos.clone(),
                decl_pos.clone(),
                name,
                field,
            )),
            Abstract_tconst_not_allowed {
                pos,
                decl_pos,
                tconst_name,
            } => eval_result::single(abstract_tconst_not_allowed(
                pos.clone(),
                decl_pos.clone(),
                tconst_name.clone(),
            )),
            Invalid_destructure {
                pos,
                decl_pos,
                ty_name,
            } => eval_result::single(invalid_destructure(
                pos.clone(),
                decl_pos.clone(),
                ty_name.clone(),
            )),
            Unpack_array_required_argument { pos, decl_pos } => eval_result::single(
                unpack_array_required_argument(pos.clone(), decl_pos.clone()),
            ),
            Unpack_array_variadic_argument { pos, decl_pos } => eval_result::single(
                unpack_array_variadic_argument(pos.clone(), decl_pos.clone()),
            ),
            Overriding_prop_const_mismatch {
                pos,
                is_const,
                parent_pos,
                ..
            } => eval_result::single(overriding_prop_const_mismatch(
                pos.clone(),
                *is_const,
                parent_pos.clone(),
            )),
            Visibility_extends {
                pos,
                vis,
                parent_pos,
                parent_vis,
            } => eval_result::single(visibility_extends(
                pos.clone(),
                vis.clone(),
                parent_pos.clone(),
                parent_vis.clone(),
            )),
            Visibility_override_internal {
                pos,
                module_name,
                parent_module,
                parent_pos,
            } => eval_result::single(visibility_override_internal(
                pos.clone(),
                module_name.clone(),
                parent_module.clone(),
                parent_pos.clone(),
            )),
            Missing_constructor(pos) => eval_result::single(missing_constructor(pos.clone())),
            Accept_disposable_invariant { pos, decl_pos } => {
                eval_result::single(accept_disposable_invariant(pos.clone(), decl_pos.clone()))
            }
            Required_field_is_optional {
                pos,
                name,
                decl_pos,
                def_pos,
                reason_sub,
                reason_super,
            } => eval_result::single(required_field_is_optional(
                pos.clone(),
                name.clone(),
                decl_pos.clone(),
                def_pos.clone(),
                reason_sub.clone(),
                reason_super,
                env,
            )),
            Return_disposable_mismatch {
                pos_sub,
                is_marked_return_disposable,
                pos_super,
            } => eval_result::single(return_disposable_mismatch(
                pos_sub.clone(),
                *is_marked_return_disposable,
                pos_super.clone(),
            )),
            Override_final { pos, parent_pos } => {
                eval_result::single(override_final(pos.clone(), parent_pos.clone()))
            }
            Override_tests_bypass_visibility {
                pos,
                member_name,
                parent_pos,
            } => eval_result::single(override_tests_bypass_visibility(
                pos.clone(),
                member_name.clone(),
                parent_pos.clone(),
            )),
            Abstract_tests_bypass_visibility_missing_attr {
                pos,
                member_name,
                parent_pos,
            } => eval_result::single(abstract_tests_bypass_visibility_missing_attr(
                pos.clone(),
                member_name.clone(),
                parent_pos.clone(),
            )),
            Override_async { pos, parent_pos } => {
                eval_result::single(override_async(pos.clone(), parent_pos.clone()))
            }
            Override_lsb {
                pos,
                member_name,
                parent_pos,
            } => eval_result::single(override_lsb(
                pos.clone(),
                member_name.clone(),
                parent_pos.clone(),
            )),
            Multiple_concrete_defs {
                pos,
                origin,
                name,
                parent_pos,
                parent_origin,
                class_name,
            } => eval_result::single(multiple_concrete_defs(
                pos.clone(),
                origin.clone(),
                name.clone(),
                parent_pos.clone(),
                parent_origin.clone(),
                class_name.clone(),
            )),
            Cyclic_enum_constraint(pos) => eval_result::single(cyclic_enum_constraint(pos.clone())),
            Inoutness_mismatch { pos, decl_pos } => {
                eval_result::single(inoutness_mismatch(pos.clone(), decl_pos.clone()))
            }
            Bad_lateinit_override {
                pos,
                parent_pos,
                parent_is_lateinit,
            } => eval_result::single(bad_lateinit_override(
                pos.clone(),
                parent_pos.clone(),
                *parent_is_lateinit,
            )),
            Bad_xhp_attr_required_override {
                pos,
                parent_pos,
                parent_tag,
                tag,
            } => eval_result::single(bad_xhp_attr_required_override(
                pos.clone(),
                parent_pos.clone(),
                parent_tag.clone(),
                tag.clone(),
            )),
            Coeffect_subtyping {
                pos,
                cap,
                pos_expected,
                cap_expected,
            } => eval_result::single(coeffect_subtyping(
                pos.clone(),
                cap.clone(),
                pos_expected.clone(),
                cap_expected.clone(),
            )),
            Not_sub_dynamic {
                pos,
                ty_name,
                dynamic_part,
            } => eval_result::single(not_sub_dynamic(
                pos.clone(),
                ty_name.clone(),
                dynamic_part.clone(),
            )),
            Override_method_support_dynamic_type {
                pos,
                method_name,
                parent_origin,
                parent_pos,
            } => eval_result::single(override_method_support_dynamic_type(
                pos.clone(),
                method_name.clone(),
                parent_origin.clone(),
                parent_pos.clone(),
            )),
            Readonly_mismatch {
                pos,
                kind,
                reason_sub,
                reason_super,
            } => eval_result::single(readonly_mismatch(
                pos.clone(),
                kind.clone(),
                reason_sub.clone(),
                reason_super.clone(),
            )),
            Require_package_mismatch {
                pos,
                reason_sub,
                reason_super,
            } => eval_result::single(require_package_mismatch(
                pos.clone(),
                reason_sub.clone(),
                reason_super.clone(),
            )),
            Typing_too_many_args {
                pos,
                decl_pos,
                actual,
                expected,
            } => eval_result::single(typing_too_many_args(
                pos.clone(),
                decl_pos.clone(),
                *actual,
                *expected,
                None,
            )),
            Typing_too_few_args {
                pos,
                decl_pos,
                actual,
                expected,
            } => eval_result::single(typing_too_few_args(
                pos.clone(),
                decl_pos.clone(),
                *actual,
                *expected,
                None,
            )),
            Non_object_member {
                pos,
                ctxt,
                ty_name,
                member_name,
                kind,
                decl_pos,
            } => eval_result::single(non_object_member(
                pos.clone(),
                ctxt.clone(),
                ty_name.clone(),
                member_name.clone(),
                kind.clone(),
                decl_pos.clone(),
            )),
            Rigid_tvar_escape { pos, name } => {
                eval_result::single(rigid_tvar_escape(pos.clone(), name.clone()))
            }
            Smember_not_found {
                pos,
                kind,
                member_name,
                class_name,
                class_pos,
                hint,
            } => eval_result::single(smember_not_found(
                pos.clone(),
                kind.clone(),
                member_name.clone(),
                class_name.clone(),
                class_pos.clone(),
                hint.clone(),
            )),
            Bad_method_override { pos, member_name } => {
                eval_result::single(bad_method_override(pos.clone(), member_name))
            }
            Bad_member_override_not_subtype {
                is_method,
                class_name,
                parent_name,
                parent_type,
                member_pos,
                member_name,
                member_type,
                origin_name,
                origin_type,
                member_parent_pos,
                member_parent_type,
                member_parent_origin,
                member_parent_origin_type,
            } => {
                // The pattern forces the lazy fields.
                let parent_type = parent_type.force();
                let member_type = member_type.force();
                let origin_type = origin_type.force();
                let member_parent_type = member_parent_type.force();
                let member_parent_origin_type = member_parent_origin_type.force();
                eval_result::single(bad_member_override_not_subtype(
                    *is_method,
                    class_name,
                    parent_name,
                    parent_type,
                    member_pos.clone(),
                    member_name,
                    member_type,
                    origin_name,
                    origin_type,
                    member_parent_pos.clone(),
                    member_parent_type,
                    member_parent_origin,
                    member_parent_origin_type,
                ))
            }
            Bad_prop_override { pos, member_name } => {
                eval_result::single(bad_prop_override(pos.clone(), member_name.clone()))
            }
            Subtyping_error {
                cstrs,
                ty_sub,
                ty_sup,
                is_coeffect,
            } => {
                let cstrs = cstrs.force();
                if cstrs.is_empty() {
                    eval_result::single(subtyping_error(*is_coeffect, ty_sub, ty_sup, env))
                } else {
                    eval_result::single(violated_constraint(
                        cstrs.clone(),
                        *is_coeffect,
                        ty_sub,
                        ty_sup,
                        env,
                    ))
                }
            }
            Method_not_dynamically_callable { pos, parent_pos } => eval_result::single(
                method_not_dynamically_callable(pos.clone(), parent_pos.clone()),
            ),
            This_final {
                pos_sub,
                pos_super,
                class_name,
            } => eval_result::single(this_final(
                pos_sub.clone(),
                pos_super.clone(),
                class_name.clone(),
            )),
            Typeconst_concrete_concrete_override { pos, parent_pos } => eval_result::single(
                typeconst_concrete_concrete_override(pos.clone(), parent_pos.clone()),
            ),
            Abstract_concrete_override {
                pos,
                parent_pos,
                kind,
            } => eval_result::single(abstract_concrete_override(
                pos.clone(),
                parent_pos.clone(),
                kind.clone(),
            )),
            Override_no_default_typeconst { pos, parent_pos } => eval_result::single(
                override_no_default_typeconst(pos.clone(), parent_pos.clone()),
            ),
            Unsupported_refinement(pos) => eval_result::single(unsupported_refinement(pos.clone())),
            Splat_not_a_shape(pos) => eval_result::single(splat_not_a_shape(pos.clone())),
            Missing_class_constant {
                pos,
                class_name,
                const_name,
            } => eval_result::single(missing_class_constant(
                pos.clone(),
                class_name.clone(),
                const_name.clone(),
            )),
            Invalid_refined_const_kind {
                pos,
                class_name,
                const_name,
                correct_kind,
                wrong_kind,
            } => eval_result::single(invalid_refined_const_kind(
                pos.clone(),
                class_name.clone(),
                const_name.clone(),
                correct_kind.clone(),
                wrong_kind.clone(),
            )),
            Inexact_tconst_access(pos, id) => {
                eval_result::single(inexact_tconst_access(pos.clone(), id.clone()))
            }
            Violated_refinement_constraint { cstr } => {
                eval_result::single(violated_refinement_constraint(cstr.clone()))
            }
            Unknown_label {
                enum_name,
                decl_pos,
                most_similar,
            } => eval_result::single(label_unknown(
                enum_name.clone(),
                decl_pos.clone(),
                most_similar.clone(),
            )),
            Higher_rank_tparam_escape {
                tvar_pos,
                pos_with_generic,
                generic_reason,
                generic_name,
            } => eval_result::single(higher_rank_tparam_escape(
                tvar_pos.clone(),
                pos_with_generic.clone(),
                generic_reason.clone(),
                generic_name.clone(),
            )),
            Override_sealed { pos, parent_pos } => {
                eval_result::single(override_sealed(pos.clone(), parent_pos.clone()))
            }
        }
    }
}

pub mod eval_callback {
    use super::super::eval_primary;
    use super::eval_error;
    use super::*;
    use crate::typing_error::callback;

    struct ErrorState {
        code_opt: Option<ErrorCode>,
        claim_opt: Option<Lazy<Message<Pos>>>,
        reasons: Lazy<Vec<Message<PosOrDecl>>>,
        explanation: Lazy<Explanation<PosOrDecl>>,
        quickfixes: Vec<Quickfix<Pos>>,
    }

    fn error_state_of_error_eval_partial(t: eval_error::Partial) -> ErrorState {
        let eval_error::Partial {
            code_opt,
            claim,
            reasons_opt,
            explanation_opt,
            quickfixes_opt,
        } = t;
        ErrorState {
            code_opt,
            claim_opt: Some(claim),
            reasons: reasons_opt.unwrap_or_else(|| Lazy::new(Vec::new)),
            explanation: explanation_opt.unwrap_or_else(|| Lazy::new(|| Explanation::Empty)),
            quickfixes: quickfixes_opt.unwrap_or_default(),
        }
    }

    fn eval(
        t: &callback::T,
        env: &Env,
        st: ErrorState,
    ) -> (
        ErrorCode,
        Option<Lazy<Message<Pos>>>,
        Lazy<Vec<Message<PosOrDecl>>>,
        Lazy<Explanation<PosOrDecl>>,
        Vec<Quickfix<Pos>>,
    ) {
        use callback::T::*;
        match t {
            With_side_effect(t, eff) => {
                eff();
                eval(t, env, st)
            }
            Always(err) => {
                let eval_primary::T {
                    code,
                    claim,
                    reasons,
                    quickfixes,
                } = eval_primary::to_error(err.clone(), env);
                (
                    code,
                    Some(claim),
                    reasons,
                    Lazy::new(|| Explanation::Empty),
                    quickfixes,
                )
            }
            Of_primary(err) => {
                let eval_primary::T {
                    code, quickfixes, ..
                } = eval_primary::to_error(err.clone(), env);
                (
                    st.code_opt.unwrap_or(code),
                    st.claim_opt,
                    st.reasons,
                    st.explanation,
                    append(&quickfixes, &st.quickfixes),
                )
            }
            With_claim_as_reason(err, claim_from) => {
                let reasons = match &st.claim_opt {
                    None => st.reasons.clone(),
                    Some(claim) => {
                        let claim = claim.clone();
                        let reasons = st.reasons.clone();
                        Lazy::new(move || {
                            let claim = claim.force();
                            let reasons = reasons.force();
                            cons(claim.clone(), reasons)
                        })
                    }
                };
                let eval_primary::T { claim, .. } = eval_primary::to_error(claim_from.clone(), env);
                eval(
                    err,
                    env,
                    ErrorState {
                        claim_opt: Some(claim),
                        reasons,
                        ..st
                    },
                )
            }
            Retain_code(t) => eval(
                t,
                env,
                ErrorState {
                    code_opt: None,
                    ..st
                },
            ),
            With_code(code, qfs) => (
                st.code_opt.unwrap_or(*code),
                st.claim_opt,
                st.reasons,
                st.explanation,
                append(qfs, &st.quickfixes),
            ),
        }
    }

    pub fn apply(eval_partial: eval_error::Partial, t: &callback::T, env: &Env) -> eval_error::T {
        let eval_partial_claim = eval_partial.claim.clone();
        let st = error_state_of_error_eval_partial(eval_partial);
        let (code, claim_opt, reasons, explanation, quickfixes) = eval(t, env, st);
        eval_error::T {
            code,
            claim: claim_opt.unwrap_or(eval_partial_claim),
            reasons,
            explanation,
            quickfixes,
        }
    }
}

pub mod eval_reasons_callback {
    use super::super::common;
    use super::super::eval_primary;
    use super::eval_callback;
    use super::eval_error;
    use super::eval_secondary;
    use super::*;
    use crate::typing_error::callback;
    use crate::typing_error::reasons_callback;
    use crate::typing_error::reasons_callback::Component;
    use crate::typing_error::reasons_callback::Op;

    mod error_state {
        use super::*;
        use crate::typing_error::secondary;

        /// `Error_state.t`
        #[derive(Clone)]
        pub struct T {
            pub code_opt: Option<ErrorCode>,
            pub claim_opt: Option<Lazy<Message<Pos>>>,
            pub reasons_opt: Option<Lazy<Vec<Message<PosOrDecl>>>>,
            pub explanation_opt: Option<Lazy<Explanation<PosOrDecl>>>,
            pub quickfixes_opt: Option<Vec<Quickfix<Pos>>>,
        }

        pub fn with_code(t: T, code_opt: Option<ErrorCode>) -> T {
            T {
                code_opt: t.code_opt.or(code_opt),
                ..t
            }
        }

        pub fn with_claim(t: T, claim_opt: Option<Lazy<Message<Pos>>>) -> T {
            T {
                claim_opt: t.claim_opt.or(claim_opt),
                ..t
            }
        }

        pub fn prepend_secondary(
            t: T,
            snd_err: &secondary::T,
            env: &Env,
            current_span: &Pos,
        ) -> eval_result::T<T> {
            let T {
                claim_opt,
                reasons_opt,
                quickfixes_opt,
                ..
            } = t;
            eval_result::map(eval_secondary::eval(snd_err, env, current_span), |t| {
                let eval_secondary::T {
                    code,
                    reasons,
                    explanation,
                } = t;
                let reasons_opt = Some(match &reasons_opt {
                    None => Lazy::new(Vec::new),
                    Some(rlz) => {
                        let rlz = rlz.clone();
                        Lazy::new(move || {
                            let rlz = rlz.force();
                            let reasons = reasons.force();
                            append(reasons, rlz)
                        })
                    }
                });
                T {
                    code_opt: Some(code),
                    claim_opt: claim_opt.clone(),
                    reasons_opt,
                    explanation_opt: Some(explanation),
                    quickfixes_opt: quickfixes_opt.clone(),
                }
            })
        }

        /// Replace any missing values in the error state with those of the error
        pub fn with_defaults(
            t: T,
            err: &typing_error::T,
            env: &Env,
            current_span: &Pos,
        ) -> eval_result::T<eval_error::T> {
            let T {
                code_opt,
                claim_opt,
                reasons_opt,
                explanation_opt,
                quickfixes_opt,
            } = t;
            eval_result::map(eval_error::eval(err, env, current_span), |t| {
                let eval_error::T {
                    code,
                    claim,
                    reasons,
                    explanation,
                    quickfixes,
                } = t;
                eval_error::T {
                    code: code_opt.unwrap_or(code),
                    claim: claim_opt.clone().unwrap_or(claim),
                    reasons: reasons_opt.clone().unwrap_or(reasons),
                    explanation: explanation_opt.clone().unwrap_or(explanation),
                    quickfixes: quickfixes_opt.clone().unwrap_or(quickfixes),
                }
            })
        }
    }

    fn eval_callback(
        k: &callback::T,
        st: error_state::T,
        env: &Env,
        claim: Lazy<Message<Pos>>,
    ) -> eval_error::T {
        let error_state::T {
            code_opt,
            reasons_opt,
            explanation_opt,
            quickfixes_opt,
            ..
        } = st;
        eval_callback::apply(
            eval_error::Partial {
                code_opt,
                claim,
                reasons_opt,
                explanation_opt,
                quickfixes_opt,
            },
            k,
            env,
        )
    }

    fn eval(
        t: &reasons_callback::T,
        env: &Env,
        st: error_state::T,
        current_span: &Pos,
    ) -> eval_result::T<eval_error::T> {
        fn aux(
            t: &reasons_callback::T,
            st: error_state::T,
            env: &Env,
            current_span: &Pos,
        ) -> eval_result::T<eval_error::T> {
            use reasons_callback::T::*;
            match t {
                From_on_error(f) => {
                    let code = st.code_opt.map(|code| code as isize);
                    let quickfixes = st.quickfixes_opt;
                    let reasons = match &st.reasons_opt {
                        None => vec![],
                        Some(reasons) => reasons.force().clone(),
                    };
                    f(code, quickfixes, reasons);
                    eval_result::empty()
                }
                Always(err) => eval_error::eval(err, env, current_span),
                Prefix(prim) => {
                    let error_state::T {
                        code_opt,
                        claim_opt,
                        reasons_opt,
                        explanation_opt,
                        quickfixes_opt,
                    } = st;
                    let eval_primary::T {
                        code,
                        claim,
                        reasons,
                        quickfixes,
                    } = eval_primary::to_error((**prim).clone(), env);
                    let code = code_opt.unwrap_or(code);
                    let claim = claim_opt.unwrap_or(claim);
                    let reasons = match reasons_opt {
                        None => reasons,
                        Some(st_reasons) => Lazy::new(move || {
                            let reasons = reasons.force();
                            let st_reasons = st_reasons.force();
                            append(reasons, st_reasons)
                        }),
                    };
                    let explanation =
                        explanation_opt.unwrap_or_else(|| Lazy::new(|| Explanation::Empty));
                    let quickfixes = append(&quickfixes, &quickfixes_opt.unwrap_or_default());
                    eval_result::single(eval_error::T {
                        code,
                        claim,
                        reasons,
                        explanation,
                        quickfixes,
                    })
                }
                Of_error(err) => error_state::with_defaults(st, err, env, current_span),
                Of_callback(k, claim) => {
                    eval_result::single(eval_callback(k, st, env, claim.clone()))
                }
                Assert_in_current_decl(default, ctx) => {
                    let error_state::T {
                        code_opt,
                        reasons_opt,
                        explanation_opt,
                        ..
                    } = st;
                    let eval_snd = eval_secondary::T {
                        code: code_opt.unwrap_or(*default),
                        reasons: reasons_opt.unwrap_or_else(|| Lazy::new(Vec::new)),
                        explanation: explanation_opt
                            .unwrap_or_else(|| Lazy::new(|| Explanation::Empty)),
                    };
                    eval_result::of_option(eval_error::of_eval_secondary_opt(
                        ctx,
                        current_span,
                        eval_snd,
                    ))
                }
                With_code(err, code) => {
                    let st = error_state::with_code(st, Some(*code));
                    aux(err, st, env, current_span)
                }
                With_claim(err, claim) => {
                    let st = error_state::with_claim(st, Some(claim.clone()));
                    aux(err, st, env, current_span)
                }
                With_reasons(err, reasons) => aux(
                    err,
                    error_state::T {
                        reasons_opt: Some(reasons.clone()),
                        ..st
                    },
                    env,
                    current_span,
                ),
                Add_quickfixes(err, qfxs) => {
                    let quickfixes_opt = st
                        .quickfixes_opt
                        .as_ref()
                        .map(|quickfixes| append(qfxs, quickfixes))
                        .or_else(|| Some(Vec::clone(qfxs)));
                    aux(
                        err,
                        error_state::T {
                            quickfixes_opt,
                            ..st
                        },
                        env,
                        current_span,
                    )
                }
                Add_reason(err, op, reason) => {
                    aux_reason_op(op, err, reason.clone(), st, env, current_span)
                }
                Retain(t, comp) => aux_retain(t, comp, st, env, current_span),
                Incoming_reasons(err, op) => {
                    let st_reasons_opt = st.reasons_opt.clone();
                    eval_result::map(
                        aux(
                            err,
                            error_state::T {
                                reasons_opt: None,
                                ..st
                            },
                            env,
                            current_span,
                        ),
                        |err| {
                            let reasons = err.reasons.clone();
                            match (&st_reasons_opt, op) {
                                (None, _) => err,
                                (Some(rs), Op::Append) => eval_error::T {
                                    reasons: common::map2(
                                        |x: &Vec<Message<PosOrDecl>>, y: &Vec<Message<PosOrDecl>>| {
                                            append(x, y)
                                        },
                                        reasons,
                                        rs.clone(),
                                    ),
                                    ..err
                                },
                                (Some(rs), Op::Prepend) => eval_error::T {
                                    reasons: common::map2(
                                        |x: &Vec<Message<PosOrDecl>>, y: &Vec<Message<PosOrDecl>>| {
                                            append(x, y)
                                        },
                                        rs.clone(),
                                        reasons,
                                    ),
                                    ..err
                                },
                            }
                        },
                    )
                }
                Prepend_on_apply(t, snd_err) => eval_result::bind(
                    error_state::prepend_secondary(st, snd_err, env, current_span),
                    |st| aux(t, st, env, current_span),
                ),
                Drop_reasons_on_apply(t) => {
                    let st = error_state::T {
                        reasons_opt: Some(Lazy::new(Vec::new)),
                        ..st
                    };
                    aux(t, st, env, current_span)
                }
                Choose(condition, if_true, if_false) => {
                    let condition: bool = condition.force().clone();
                    aux(
                        if condition { if_true } else { if_false },
                        st,
                        env,
                        current_span,
                    )
                }
            }
        }
        fn aux_reason_op(
            op: &Op,
            err: &reasons_callback::T,
            base_reason: Lazy<Message<PosOrDecl>>,
            st: error_state::T,
            env: &Env,
            current_span: &Pos,
        ) -> eval_result::T<eval_error::T> {
            let reasons_opt = Some(match &st.reasons_opt {
                None => base_reason.map(|x| vec![x.clone()]),
                Some(reasons_lz) => {
                    let reasons_lz = reasons_lz.clone();
                    match op {
                        Op::Append => Lazy::new(move || {
                            let rs = reasons_lz.force();
                            let r = base_reason.force();
                            append(rs, std::slice::from_ref(r))
                        }),
                        Op::Prepend => Lazy::new(move || {
                            let rs = reasons_lz.force();
                            let r = base_reason.force();
                            cons(r.clone(), rs)
                        }),
                    }
                }
            });

            aux(err, error_state::T { reasons_opt, ..st }, env, current_span)
        }
        fn aux_retain(
            t: &reasons_callback::T,
            comp: &Component,
            st: error_state::T,
            env: &Env,
            current_span: &Pos,
        ) -> eval_result::T<eval_error::T> {
            match comp {
                Component::Code => aux(
                    t,
                    error_state::T {
                        code_opt: None,
                        ..st
                    },
                    env,
                    current_span,
                ),
                Component::Reasons => aux(
                    t,
                    error_state::T {
                        reasons_opt: None,
                        ..st
                    },
                    env,
                    current_span,
                ),
                Component::Quickfixes => aux(
                    t,
                    error_state::T {
                        quickfixes_opt: None,
                        ..st
                    },
                    env,
                    current_span,
                ),
            }
        }
        aux(t, st, env, current_span)
    }

    pub fn apply_help(
        eval_snd: eval_secondary::T,
        t: &reasons_callback::T,
        env: &Env,
        current_span: &Pos,
    ) -> eval_result::T<eval_error::T> {
        let eval_secondary::T {
            code,
            reasons,
            explanation,
        } = eval_snd;
        eval(
            t,
            env,
            error_state::T {
                code_opt: Some(code),
                claim_opt: None,
                reasons_opt: Some(reasons),
                explanation_opt: Some(explanation),
                quickfixes_opt: None,
            },
            current_span,
        )
    }

    pub fn apply(
        eval_snd: eval_secondary::T,
        t: &reasons_callback::T,
        env: &Env,
        current_span: &Pos,
    ) -> eval_result::T<Diagnostic> {
        let f = |t: eval_error::T| {
            let eval_error::T {
                code,
                claim,
                reasons,
                explanation,
                quickfixes,
            } = t;
            // The arguments of an OCaml application are evaluated from the
            // last to the first.
            let explanation = explanation.force().clone();
            let reasons = reasons.force().clone();
            let claim = claim.force().clone();
            crate::user_diagnostic::make_err(
                code as isize,
                Some(false),
                Some(quickfixes),
                None,
                None,
                claim,
                reasons,
                explanation,
            )
        };
        eval_result::map(apply_help(eval_snd, t, env, current_span), f)
    }
}

fn is_suppressed(error: &Diagnostic) -> bool {
    crate::diagnostics_state::is_suppressed(error)
}

pub fn add_typing_error(err: &typing_error::T, env: &Env) {
    let current_span = crate::diagnostics_state::get_current_span();
    eval_result::iter(
        eval_result::suppress_intersection(
            eval_error::to_user_diagnostic(err, env, &current_span),
            is_suppressed,
        ),
        crate::diagnostics_state::add_diagnostic,
    )
}

fn apply_error_from_reasons_callback(
    eval_snd: eval_secondary::T,
    err: &typing_error::reasons_callback::T,
    env: &Env,
) {
    let current_span = crate::diagnostics_state::get_current_span();
    eval_result::iter(
        eval_result::suppress_intersection(
            eval_reasons_callback::apply(eval_snd, err, env, &current_span),
            is_suppressed,
        ),
        crate::diagnostics_state::add_diagnostic,
    )
}

fn claim_as_reason(claim: Message<Pos>) -> Message<PosOrDecl> {
    let Message(p, m) = claim;
    Message(p, m)
}

/// TODO: Remove use of `User_diagnostic.t` representation for nested error &
/// callback application
pub fn ambiguous_inheritance(
    pos: PosOrDecl,
    class_: &str,
    origin: &str,
    error: Diagnostic,
    on_error: &typing_error::reasons_callback::T,
    env: &Env,
) {
    let oxidized::user_diagnostic::UserDiagnostic {
        code,
        claim,
        reasons,
        explanation,
        ..
    } = error;
    let origin = strip_ns(origin);
    let class_ = strip_ns(class_);
    let message = format!(
        "This declaration was inherited from an object of type {}. Redeclare this member in {} with a compatible signature.",
        md_codify(origin),
        md_codify(class_)
    );
    let code = crate::error_codes::typing::of_enum(code)
        .unwrap_or_else(|| panic!("Option.value_exn: no typing error has the code {}", code));
    apply_error_from_reasons_callback(
        eval_secondary::T {
            code,
            reasons: Lazy::new(move || {
                append(
                    &cons(claim_as_reason(claim), &reasons),
                    &[Message(pos, message.into())],
                )
            }),
            explanation: Lazy::new(move || explanation),
        },
        on_error,
        env,
    )
}

fn discard_outermost(err: typing_error::T) -> typing_error::T {
    match err {
        typing_error::T::Apply_reasons(_, snd_err)
            if matches!(&*snd_err, typing_error::secondary::T::Of_error(_)) =>
        {
            match std::rc::Rc::unwrap_or_clone(snd_err) {
                typing_error::secondary::T::Of_error(err) => *err,
                _ => unreachable!(),
            }
        }
        typing_error::T::Deferred(d) => discard_outermost(d.force().clone()),
        err => err,
    }
}

fn get_arg_idx_secondary(second: &typing_error::secondary::T) -> Option<isize> {
    use typing_error::secondary::T::*;
    match second {
        Subtyping_error { ty_sub, .. } => crate::typing_reason::get_top_fun_param_prj_idx(
            crate::typing_defs_constraints::get_reason_i(ty_sub),
        ),
        Of_error(err) => get_arg_idx(err),
        _ => None,
    }
}

/// Search the error to get the outermost parameter projection from the reason, and update
/// the primary position accordingly.
fn get_arg_idx(err: &typing_error::T) -> Option<isize> {
    use typing_error::T::*;
    match err {
        Apply_reasons(_, second) => get_arg_idx_secondary(second),
        With_code(err, _) | With_pos(err, _) | Apply(_, err) => get_arg_idx(err),
        Primary(_) | Assert_in_current_decl(_, _) => None,
        Multiple(errs) | Union(errs) | Intersection(errs) => errs.iter().find_map(get_arg_idx),
        Deferred(d) => get_arg_idx(d.force()),
    }
}

fn update_error_for_method_call_prim(arg_posl: &[Pos], err: typing_error::T) -> typing_error::T {
    match get_arg_idx(&err) {
        None => discard_outermost(err),
        Some(i) => {
            // `List.nth_exn arg_posl i`
            let pos = usize::try_from(i)
                .ok()
                .and_then(|i| arg_posl.get(i))
                .unwrap_or_else(|| {
                    panic!(
                        "List.nth_exn {} called on list of length {}",
                        i,
                        arg_posl.len()
                    )
                })
                .clone();
            typing_error::T::With_pos(std::rc::Rc::new(err), pos)
        }
    }
}

/// Inspect the typing error, and update it by changing the primary position, or dropping the
/// outermost wrapper. When checking a method call with subtyping, we use the whole
/// call expression's position and add an "Illegal argument" message. If one of the parameters
/// doesn't match, this focusses on the position. Alternately, if something else went wrong, we
/// need to drop the "Invalid argument" (e.g., if the method isn't there).
pub fn update_error_for_method_call(arg_posl: &[Pos], err: typing_error::T) -> typing_error::T {
    match err {
        typing_error::T::Multiple(errs) => typing_error::T::Multiple(
            errs.into_iter()
                .map(|err| update_error_for_method_call(arg_posl, err))
                .collect(),
        ),
        typing_error::T::Deferred(d) => update_error_for_method_call(arg_posl, d.force().clone()),
        err => update_error_for_method_call_prim(arg_posl, err),
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::path::Path;
    use std::path::PathBuf;
    use std::rc::Rc;
    use std::sync::Arc;

    use oxidized::ast_defs::Tprim;
    use oxidized::pos_or_decl::Ctx;
    use oxidized::quickfix::Edits;
    use oxidized::typechecker_options::TypecheckerOptions;
    use oxidized::user_diagnostic::Severity;
    use oxidized::user_diagnostic::UserDiagnostic;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::super::common;
    use super::super::common::testing::pos;
    use super::super::common::testing::render;
    use super::*;
    use crate::typing_defs_constraints::InternalType;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::mk;
    use crate::typing_error::callback;
    use crate::typing_error::primary;
    use crate::typing_error::reasons_callback;
    use crate::typing_error::secondary;
    use crate::typing_reason;

    /// The `Lazy` of the fields of a `Typing_error` value.
    type ELazy<A> = crate::typing_error::Lazy<A>;

    /// What an error evaluates to: its code, claim and reasons.
    type Evaluated = (isize, Message<Pos>, Vec<Message<PosOrDecl>>);

    fn file(name: &str) -> RelativePath {
        RelativePath::make(Prefix::Root, PathBuf::from(name))
    }

    fn env() -> Env {
        let ctx = crate::ctx::Ctx::new(Path::new("/"), TypecheckerOptions::default()).unwrap();
        crate::typing_env_types::empty(None, None, Arc::new(ctx), Arc::new(file("foo.php")), None)
    }

    fn m(pos: &Pos, msg: &str) -> Message<Pos> {
        Message(pos.clone(), msg.into())
    }

    fn lazy_m(pos: &Pos, msg: &str) -> ELazy<Message<Pos>> {
        let m = m(pos, msg);
        ELazy::new(move || m)
    }

    fn evaluated(t: eval_result::T<eval_error::T>) -> Vec<Evaluated> {
        let mut out = vec![];
        eval_result::iter(t, |t| {
            out.push((
                t.code as isize,
                t.claim.force().clone(),
                t.reasons.force().clone(),
            ))
        });
        out
    }

    fn eval(err: &typing_error::T) -> Vec<Evaluated> {
        evaluated(eval_error::eval(err, &env(), &Pos::NONE))
    }

    /// `int`, because of an expression at `p`.
    fn int(p: &Pos) -> InternalType {
        InternalType::LoclType(mk((
            typing_reason::witness(p.clone()),
            Ty_::Tprim(Tprim::Tint),
        )))
    }

    /// `float`, because of a hint at `p`.
    fn float(p: &Pos) -> InternalType {
        InternalType::LoclType(mk((
            typing_reason::hint(p.clone()),
            Ty_::Tprim(Tprim::Tfloat),
        )))
    }

    fn subtyping_error(ty_sub: InternalType, ty_sup: InternalType) -> secondary::T {
        secondary::T::Subtyping_error {
            cstrs: ELazy::new(Vec::new),
            ty_sub,
            ty_sup,
            is_coeffect: false,
        }
    }

    // Positions of `foo.php`, named after what the tests put there.
    fn p_claim() -> Pos {
        pos("foo.php", 4, 10, 11)
    }
    fn p_hint() -> Pos {
        pos("foo.php", 3, 24, 28)
    }
    fn p_call() -> Pos {
        pos("foo.php", 7, 3, 12)
    }
    fn p_decl() -> Pos {
        pos("foo.php", 1, 10, 12)
    }
    fn p_other() -> Pos {
        pos("foo.php", 9, 1, 5)
    }

    /// A secondary error with code 4041 and the two reasons `too_many_args_reasons()`.
    fn too_many_args() -> secondary::T {
        secondary::T::Fun_too_many_args {
            pos: p_call(),
            decl_pos: p_decl(),
            actual: 2,
            expected: 1,
        }
    }

    fn too_many_args_reasons() -> Vec<Message<PosOrDecl>> {
        vec![
            m(
                &p_call(),
                "Too many mandatory arguments (expected 1 but got 2)",
            ),
            m(&p_decl(), "Because of this definition"),
        ]
    }

    /// `Unify_error` (code 4110) with the claim "Claim" at `p_claim()` and one reason.
    fn prim() -> primary::T {
        let r0 = prim_reason();
        primary::T::Unify_error {
            pos: p_claim(),
            msg_opt: Some("Claim".to_string()),
            reasons_opt: Some(ELazy::new(move || vec![r0])),
        }
    }

    fn prim_reason() -> Message<PosOrDecl> {
        m(&p_hint(), "Reason of the primary error")
    }

    /// `Callback.unify_error` with the claim "Invalid argument" at `p_claim()`.
    fn invalid_argument() -> reasons_callback::T {
        reasons_callback::with_claim(
            callback::unify_error(),
            lazy_m(&p_claim(), "Invalid argument"),
        )
    }

    #[test]
    fn invalid_return_type() {
        // What `return 1;` in a function that returns `float` is reported as.
        let err = typing_error::apply_reasons(
            subtyping_error(int(&p_claim()), float(&p_hint())),
            reasons_callback::with_claim(
                callback::unify_error(),
                lazy_m(&p_claim(), "Invalid return type"),
            ),
        );
        let mut out = vec![];
        eval_result::iter(eval_error::eval(&err, &env(), &Pos::NONE), |t| {
            out.push(render(t.code, &t.claim, &t.reasons))
        });
        assert_eq!(
            out,
            vec![
                [
                    "ERROR: File \"foo.php\", line 4, characters 10-11:\n",
                    "Invalid return type (Typing[4110])\n",
                    "  File \"foo.php\", line 3, characters 24-28:\n",
                    "  Expected `float`\n",
                    "  File \"foo.php\", line 4, characters 10-11:\n",
                    "  But got `int`\n",
                ]
                .concat()
            ]
        );
    }

    #[test]
    fn subtyping_error_under_unify_error_at() {
        // The claim and the code are the ones of `Primary.Unify_error`, the
        // reasons the ones of the secondary error.
        let err = typing_error::apply_reasons(
            subtyping_error(int(&p_claim()), float(&p_hint())),
            reasons_callback::unify_error_at(p_call()),
        );
        assert_eq!(
            eval(&err),
            vec![(
                4110,
                m(&p_call(), "Typing error"),
                vec![
                    m(&p_hint(), "Expected `float`"),
                    m(&p_claim(), "But got `int`")
                ]
            )]
        );
        // Types that are described in the same way.
        let err = typing_error::apply_reasons(
            subtyping_error(int(&p_claim()), int(&p_hint())),
            reasons_callback::unify_error_at(p_call()),
        );
        assert_eq!(
            eval(&err),
            vec![(
                4110,
                m(&p_call(), "Typing error"),
                vec![
                    m(&p_hint(), "Expected exactly the type `int`"),
                    m(&p_claim(), "But got the nonexact type `int`")
                ]
            )]
        );
    }

    #[test]
    fn violated_constraint() {
        let p_cstr = p_decl();
        let p_tparam = p_other();
        let cstrs = vec![(p_cstr.clone(), m(&p_tparam, "T"))];
        let err = typing_error::apply_reasons(
            secondary::T::Subtyping_error {
                cstrs: ELazy::new(move || cstrs),
                ty_sub: int(&p_claim()),
                ty_sup: float(&p_hint()),
                is_coeffect: false,
            },
            invalid_argument(),
        );
        assert_eq!(
            eval(&err),
            vec![(
                4323,
                m(&p_claim(), "Invalid argument"),
                vec![
                    m(&p_tparam, "`T` is a constrained type parameter"),
                    m(&p_cstr, "This type constraint is violated"),
                    m(&p_hint(), "Expected `float`"),
                    m(&p_claim(), "But got `int`")
                ]
            )]
        );
    }

    #[test]
    fn which_code() {
        let eval = |on_error| eval(&typing_error::apply_reasons(too_many_args(), on_error));
        let with_code = |code: isize| {
            vec![(
                code,
                m(&p_claim(), "Invalid argument"),
                too_many_args_reasons(),
            )]
        };
        // The code of the secondary error wins over the one of the callback...
        assert_eq!(eval(invalid_argument()), with_code(4041));
        // ... unless the callback retains its own.
        assert_eq!(
            eval(reasons_callback::retain_code(invalid_argument())),
            with_code(4110)
        );
        assert_eq!(
            eval(reasons_callback::with_claim(
                callback::retain_code(callback::unify_error()),
                lazy_m(&p_claim(), "Invalid argument"),
            )),
            with_code(4110)
        );
        // `With_code` only gives a code when there is none yet.
        assert_eq!(
            eval(reasons_callback::with_code(
                invalid_argument(),
                ErrorCode::TypeConstantMismatch
            )),
            with_code(4041)
        );
        assert_eq!(
            eval(reasons_callback::retain_code(reasons_callback::with_code(
                invalid_argument(),
                ErrorCode::TypeConstantMismatch
            ))),
            with_code(4326)
        );
        assert_eq!(
            eval(reasons_callback::with_code(
                reasons_callback::retain_code(invalid_argument()),
                ErrorCode::TypeConstantMismatch
            )),
            with_code(4110)
        );
    }

    #[test]
    fn which_reasons() {
        let of_error = || reasons_callback::of_primary_error(prim());
        let eval = |on_error| eval(&typing_error::apply_reasons(too_many_args(), on_error));
        // The claim of the primary error, the code of the secondary error.
        let with_reasons =
            |reasons: Vec<Message<PosOrDecl>>| vec![(4041, m(&p_claim(), "Claim"), reasons)];
        let (a, b) = (
            m(
                &p_call(),
                "Too many mandatory arguments (expected 1 but got 2)",
            ),
            m(&p_decl(), "Because of this definition"),
        );
        let r0 = prim_reason();
        let x = m(&p_other(), "Extra reason");
        let lazy_x = || {
            let x = x.clone();
            ELazy::new(move || x)
        };

        // The reasons of the secondary error replace those of the error.
        assert_eq!(eval(of_error()), with_reasons(vec![a.clone(), b.clone()]));
        assert_eq!(
            eval(reasons_callback::retain_reasons(of_error())),
            with_reasons(vec![r0.clone()])
        );
        assert_eq!(
            eval(reasons_callback::append_incoming_reasons(of_error())),
            with_reasons(vec![r0.clone(), a.clone(), b.clone()])
        );
        assert_eq!(
            eval(reasons_callback::prepend_incoming_reasons(of_error())),
            with_reasons(vec![a.clone(), b.clone(), r0.clone()])
        );
        assert_eq!(
            eval(reasons_callback::prepend_reason(of_error(), lazy_x())),
            with_reasons(vec![x.clone(), a.clone(), b.clone()])
        );
        assert_eq!(
            eval(reasons_callback::append_reason(of_error(), lazy_x())),
            with_reasons(vec![a.clone(), b.clone(), x.clone()])
        );
        // The callbacks apply from the outside in.
        assert_eq!(
            eval(reasons_callback::append_reason(
                reasons_callback::retain_reasons(of_error()),
                lazy_x()
            )),
            with_reasons(vec![r0.clone()])
        );
        assert_eq!(
            eval(reasons_callback::retain_reasons(
                reasons_callback::append_reason(of_error(), lazy_x())
            )),
            with_reasons(vec![x.clone()])
        );
        assert_eq!(
            eval(reasons_callback::with_reasons(of_error(), {
                let x = x.clone();
                ELazy::new(move || vec![x])
            })),
            with_reasons(vec![x.clone()])
        );
        assert_eq!(
            eval(reasons_callback::drop_reasons_on_apply(of_error())),
            with_reasons(vec![])
        );
        assert_eq!(
            eval(reasons_callback::choose(
                ELazy::new(|| false),
                reasons_callback::drop_reasons_on_apply(of_error()),
                reasons_callback::retain_reasons(of_error()),
            )),
            with_reasons(vec![r0.clone()])
        );
        // `Prefix`: the reasons of the primary error come first.
        assert_eq!(
            eval(reasons_callback::T::Prefix(std::rc::Rc::new(prim()))),
            with_reasons(vec![r0.clone(), a.clone(), b.clone()])
        );
        // `Always`: nothing of the secondary error is used.
        assert_eq!(
            eval(reasons_callback::always(typing_error::primary(prim()))),
            vec![(4110, m(&p_claim(), "Claim"), vec![r0.clone()])]
        );

        // `Prepend_on_apply`: the code and the reasons of the other secondary
        // error come first.
        let missing_constructor = || secondary::T::Missing_constructor(p_other());
        let c = m(&p_other(), "The constructor is not implemented");
        assert_eq!(
            eval(reasons_callback::prepend_on_apply(
                of_error(),
                missing_constructor()
            )),
            vec![(
                4056,
                m(&p_claim(), "Claim"),
                vec![c.clone(), a.clone(), b.clone()]
            )]
        );
        // ... and when there are no reasons to prepend to, there are none at
        // all.
        assert_eq!(
            eval(reasons_callback::retain_reasons(
                reasons_callback::prepend_on_apply(of_error(), missing_constructor())
            )),
            vec![(4056, m(&p_claim(), "Claim"), vec![])]
        );
    }

    #[test]
    fn from_on_error() {
        let calls = Rc::new(RefCell::new(vec![]));
        let on_error = {
            let calls = Rc::clone(&calls);
            reasons_callback::from_on_error(move |code, quickfixes, reasons| {
                calls.borrow_mut().push((code, quickfixes, reasons))
            })
        };
        let err = typing_error::apply_reasons(too_many_args(), on_error);
        // The function reports the error itself: there is nothing left.
        assert_eq!(eval(&err), vec![]);
        assert_eq!(
            *calls.borrow(),
            vec![(Some(4041), None, too_many_args_reasons())]
        );
    }

    #[test]
    fn quickfixes() {
        let quickfix = |title: &str| Quickfix {
            title: title.to_string(),
            edits: Edits::Eager(vec![]),
            hint_styles: vec![],
        };
        let eval = |on_error| {
            let err = typing_error::apply_reasons(too_many_args(), on_error);
            let mut out = vec![];
            eval_result::iter(eval_error::eval(&err, &env(), &Pos::NONE), |t| {
                out.push(t.quickfixes)
            });
            out
        };
        assert_eq!(eval(invalid_argument()), vec![vec![]]);
        // The quickfixes that are added last (innermost) come first.
        assert_eq!(
            eval(reasons_callback::add_quickfixes(
                reasons_callback::add_quickfixes(invalid_argument(), vec![quickfix("inner")]),
                vec![quickfix("outer")]
            )),
            vec![vec![quickfix("inner"), quickfix("outer")]]
        );
        // The quickfixes of a callback come before the ones of the state.
        assert_eq!(
            eval(reasons_callback::add_quickfixes(
                reasons_callback::with_claim(
                    callback::T::With_code(ErrorCode::UnifyError, vec![quickfix("callback")]),
                    lazy_m(&p_claim(), "Invalid argument"),
                ),
                vec![quickfix("outer")]
            )),
            vec![vec![quickfix("callback"), quickfix("outer")]]
        );
        assert_eq!(
            eval(reasons_callback::retain_quickfixes(
                reasons_callback::add_quickfixes(invalid_argument(), vec![quickfix("kept")])
            )),
            vec![vec![quickfix("kept")]]
        );
        assert_eq!(
            eval(reasons_callback::add_quickfixes(
                reasons_callback::retain_quickfixes(invalid_argument()),
                vec![quickfix("dropped")]
            )),
            vec![vec![]]
        );
    }

    #[test]
    fn assert_in_current_decl() {
        let ctx = |name: &str| Ctx {
            decl: None,
            file: file(name),
        };
        let (a, b) = (
            m(
                &p_call(),
                "Too many mandatory arguments (expected 1 but got 2)",
            ),
            m(&p_decl(), "Because of this definition"),
        );
        // The first reason is in the current file: it is the claim.
        let in_current_decl = vec![(4041, a.clone(), vec![b.clone()])];
        assert_eq!(
            eval(&typing_error::assert_in_current_decl(
                too_many_args(),
                ctx("foo.php")
            )),
            in_current_decl
        );
        assert_eq!(
            eval(&typing_error::apply_reasons(
                too_many_args(),
                reasons_callback::assert_in_current_decl(ErrorCode::UnifyError, ctx("foo.php"))
            )),
            in_current_decl
        );
        assert_eq!(
            eval(&typing_error::apply_reasons(
                too_many_args(),
                reasons_callback::retain_code(reasons_callback::assert_in_current_decl(
                    ErrorCode::UnifyError,
                    ctx("foo.php")
                ))
            )),
            vec![(4110, a.clone(), vec![b.clone()])]
        );
        // Without reasons there is no error.
        assert_eq!(
            eval(&typing_error::apply_reasons(
                too_many_args(),
                reasons_callback::drop_reasons_on_apply(reasons_callback::assert_in_current_decl(
                    ErrorCode::UnifyError,
                    ctx("foo.php")
                ))
            )),
            vec![]
        );
        // The first reason is in another file: the claim says so, at the
        // current span, and every reason is kept.
        let span = p_other();
        let res = evaluated(eval_error::eval(
            &typing_error::assert_in_current_decl(too_many_args(), ctx("bar.php")),
            &env(),
            &span,
        ));
        assert_eq!(
            res,
            vec![(
                4041,
                m(&span, &common::badpos_message_2()),
                vec![a.clone(), b.clone()]
            )]
        );
    }

    #[test]
    fn callbacks() {
        // An error with the code 4326, the claim "Claim" and one reason.
        let err = || {
            typing_error::with_code(
                typing_error::primary(prim()),
                ErrorCode::TypeConstantMismatch,
            )
        };
        let r0 = prim_reason();
        let eval = |on_error| eval(&typing_error::apply(err(), on_error));
        assert_eq!(
            eval(callback::unify_error()),
            vec![(4326, m(&p_claim(), "Claim"), vec![r0.clone()])]
        );
        assert_eq!(
            eval(callback::retain_code(callback::unify_error())),
            vec![(4110, m(&p_claim(), "Claim"), vec![r0.clone()])]
        );
        // The claim becomes the first reason.
        assert_eq!(
            eval(callback::with_claim_as_reason(
                callback::retain_code(callback::unify_error()),
                primary::T::Unify_error {
                    pos: p_other(),
                    msg_opt: Some("New claim".to_string()),
                    reasons_opt: None,
                }
            )),
            vec![(
                4110,
                m(&p_other(), "New claim"),
                vec![m(&p_claim(), "Claim"), r0.clone()]
            )]
        );
        assert_eq!(
            eval(callback::always(primary::T::Unify_error {
                pos: p_other(),
                msg_opt: Some("Always".to_string()),
                reasons_opt: None,
            })),
            vec![(4110, m(&p_other(), "Always"), vec![])]
        );
        assert_eq!(
            eval(callback::of_primary_error(primary::T::Unify_error {
                pos: p_other(),
                msg_opt: Some("Unused".to_string()),
                reasons_opt: None,
            })),
            vec![(4326, m(&p_claim(), "Claim"), vec![r0.clone()])]
        );

        // The side effect happens once for each error the callback applies to.
        let count = Rc::new(RefCell::new(0));
        let on_error = {
            let count = Rc::clone(&count);
            callback::with_side_effect(callback::unify_error(), move || *count.borrow_mut() += 1)
        };
        let errs = typing_error::apply(typing_error::multiple(vec![err(), err()]), on_error);
        assert_eq!(super::tests::eval(&errs).len(), 2);
        assert_eq!(*count.borrow(), 2);
    }

    #[test]
    fn errors() {
        let err = |msg: &str, pos: Pos| {
            typing_error::primary(primary::T::Unify_error {
                pos,
                msg_opt: Some(msg.to_string()),
                reasons_opt: None,
            })
        };
        // `With_pos` moves the claim.
        assert_eq!(
            eval(&typing_error::T::With_pos(
                std::rc::Rc::new(err("A", p_claim())),
                p_other()
            )),
            vec![(4110, m(&p_other(), "A"), vec![])]
        );
        // Every error of a `Multiple`, `Union` or `Intersection`, in order.
        let errs = || {
            vec![
                err("A", p_claim()),
                typing_error::union(vec![err("B", p_hint()), err("C", p_call())]),
                typing_error::intersect(vec![err("D", p_decl()), err("E", p_other())]),
            ]
        };
        let claims = |t: eval_result::T<eval_error::T>| -> Vec<String> {
            evaluated(t)
                .into_iter()
                .map(|(_, Message(_, msg), _)| msg.to_string())
                .collect()
        };
        assert_eq!(
            claims(eval_error::eval(
                &typing_error::multiple(errs()),
                &env(),
                &Pos::NONE
            )),
            vec!["A", "B", "C", "D", "E"]
        );
        // What `add_typing_error` does with an intersection: when one of its
        // errors is suppressed, it is the only one that is left.
        let suppressed =
            |msg: &'static str| move |t: &eval_error::T| t.claim.force().1.to_string() == msg;
        assert_eq!(
            claims(eval_result::suppress_intersection(
                eval_error::eval(&typing_error::multiple(errs()), &env(), &Pos::NONE),
                suppressed("E")
            )),
            vec!["A", "B", "C", "E"]
        );
        assert_eq!(
            claims(eval_result::suppress_intersection(
                eval_error::eval(&typing_error::multiple(errs()), &env(), &Pos::NONE),
                suppressed("B")
            )),
            vec!["A", "B", "C", "D", "E"]
        );
    }

    #[test]
    fn secondary_of_error() {
        // The claim of the error is the first reason of the secondary error.
        let err = typing_error::apply_reasons(
            secondary::T::Of_error(Box::new(typing_error::with_code(
                typing_error::primary(prim()),
                ErrorCode::TypeConstantMismatch,
            ))),
            invalid_argument(),
        );
        assert_eq!(
            eval(&err),
            vec![(
                4326,
                m(&p_claim(), "Invalid argument"),
                vec![m(&p_claim(), "Claim"), prim_reason()]
            )]
        );
    }

    #[test]
    fn user_diagnostic() {
        let env = env();
        let err = typing_error::apply_reasons(too_many_args(), invalid_argument());
        let mut out = vec![];
        eval_result::iter(
            eval_error::to_user_diagnostic(&err, &env, &Pos::NONE),
            |d| out.push(d),
        );
        assert_eq!(
            out,
            vec![UserDiagnostic {
                severity: Severity::Err,
                code: 4041,
                claim: m(&p_claim(), "Invalid argument"),
                reasons: too_many_args_reasons(),
                explanation: Explanation::Empty,
                quickfixes: vec![],
                custom_msgs: vec![],
                is_fixmed: false,
                function_pos: Some(env.genv.function_pos.clone()),
            }]
        );
    }

    #[test]
    fn add_typing_error_adds_diagnostics() {
        let env = env();
        let err = typing_error::multiple(vec![
            typing_error::apply_reasons(too_many_args(), invalid_argument()),
            typing_error::primary(prim()),
        ]);
        let (errors, ()) = crate::diagnostics_state::do_(None, || add_typing_error(&err, &env));
        let diagnostics: Vec<Evaluated> =
            crate::diagnostics_state::get_diagnostic_list(None, errors)
                .into_iter()
                .map(|d| (d.code, d.claim, d.reasons))
                .collect();
        assert_eq!(
            diagnostics,
            vec![
                (
                    4041,
                    m(&p_claim(), "Invalid argument"),
                    too_many_args_reasons()
                ),
                (4110, m(&p_claim(), "Claim"), vec![prim_reason()]),
            ]
        );
    }

    #[test]
    fn method_call() {
        let arg_posl = vec![p_decl(), p_other()];
        // The subtype comes from the second parameter of a function type.
        let r_param = typing_reason::prj_fn_param(
            typing_reason::witness(p_claim()),
            typing_reason::witness(p_hint()),
            typing_reason::witness(p_hint()),
            1,
            1,
        );
        let ty_sub = InternalType::LoclType(mk((r_param, Ty_::Tprim(Tprim::Tint))));
        let arg_err = || {
            typing_error::apply_reasons(
                subtyping_error(ty_sub.clone(), float(&p_hint())),
                invalid_argument(),
            )
        };
        // The claim moves to the argument.
        let res = update_error_for_method_call(&arg_posl, arg_err());
        assert!(matches!(
            &res,
            typing_error::T::With_pos(err, pos)
                if *pos == p_other() && matches!(**err, typing_error::T::Apply_reasons(_, _))
        ));
        assert_eq!(
            eval(&res)
                .into_iter()
                .map(|(code, claim, _)| (code, claim))
                .collect::<Vec<_>>(),
            vec![(4110, m(&p_other(), "Invalid argument"))]
        );
        // Not about an argument: the wrapper of an error goes away...
        let wrapped = || {
            typing_error::apply_reasons(
                secondary::T::Of_error(Box::new(typing_error::primary(prim()))),
                invalid_argument(),
            )
        };
        let res = update_error_for_method_call(&arg_posl, wrapped());
        assert!(matches!(&res, typing_error::T::Primary(_)));
        // ... and anything else stays as it is.
        let res = update_error_for_method_call(
            &arg_posl,
            typing_error::apply_reasons(too_many_args(), invalid_argument()),
        );
        assert!(matches!(
            &res,
            typing_error::T::Apply_reasons(_, snd_err)
                if matches!(&**snd_err, secondary::T::Fun_too_many_args { .. })
        ));
        // Each error of a `Multiple` is updated.
        let res = update_error_for_method_call(
            &arg_posl,
            typing_error::multiple(vec![arg_err(), wrapped()]),
        );
        assert!(matches!(
            &res,
            typing_error::T::Multiple(errs)
                if matches!(
                    errs.as_slice(),
                    [typing_error::T::With_pos(_, _), typing_error::T::Primary(_)]
                )
        ));
    }
}
