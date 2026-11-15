// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart as one module: this file collects the OCaml printers
//! of the types of a TAST that `crate::ast_show` does not have: `Typing_reason.pp_t_` (hand-written) with `pp_witness_locl`,
//! `pp_witness_decl` and the derived printers of its small types,
//! `Typing_defs_core.Pp` (hand-written: `pp_ty`, `pp_ty_`, ...) and the
//! derived printers of the records it calls (`fun_type`, `fun_param`,
//! `tparam`, the flag records of `Typing_defs_flags`), `Typing_set.pp`,
//! `Typing_kinding_defs.pp_kind`, `Type_parameter_env.pp`, and
//! `Tast.pp_saved_env` / `pp_fun_tast_info`: what `Tast.pp_program` prints
//! (`hh_client --show-tast`). See `hh/PORTING.md`.
//!
//! The `[@@deriving show]` printers follow
//! ppx_deriving's rules (as `ast_show`): a record is `@[<2>{ ` its fields
//! `@[name =@ ` .. `@]` separated by `;@ ` then `@ }@]`, the first field
//! qualified by the module unless `with_path = false`; a constructor with
//! one argument `(@[<2>C@ ` .. `@])`, with several `(@[<2>C (@,` .. `,@ ` ..
//! `@,))@]`; a list `@[<2>[` .. `;@ ` .. `@,]@]`; an option `None` or
//! `(Some ` .. `)`; a tuple `(@[` .. `,@ ` .. `@])`; strings `%S`.

use oxidized::aast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::ast_show;
use crate::format;
use crate::format::Formatter;
use crate::tast;
use crate::typing_defs_core::*;
use crate::typing_reason::T_ as R;
use crate::typing_reason::WitnessDecl as WD;
use crate::typing_reason::WitnessLocl as WL;

type F<'f> = &'f mut Formatter;

fn ps(fmt: F<'_>, s: &str) {
    format::pp_print_string(fmt, s)
}
fn ob(fmt: F<'_>, i: isize) {
    format::pp_open_box(fmt, i)
}
fn cb(fmt: F<'_>) {
    format::pp_close_box(fmt)
}
fn sp(fmt: F<'_>) {
    format::pp_print_space(fmt)
}
fn cut(fmt: F<'_>) {
    format::pp_print_cut(fmt)
}
/// `",@ "`
fn comma(fmt: F<'_>) {
    ps(fmt, ",");
    sp(fmt)
}
/// `";@ "`
fn semi(fmt: F<'_>) {
    ps(fmt, ";");
    sp(fmt)
}
/// `%S`
fn pp_s(fmt: F<'_>, s: &(impl AsRef<[u8]> + ?Sized)) {
    ps(fmt, &crate::rt::ocaml_printf::sprintf_s_bytes(s.as_ref()))
}
/// `%B`
fn pp_b(fmt: F<'_>, b: bool) {
    ps(fmt, if b { "true" } else { "false" })
}
/// `%d`
fn pp_d(fmt: F<'_>, i: isize) {
    ps(fmt, &i.to_string())
}

/// A printer of `crate::ast_show`, which takes the formatter in a `P`.
fn with_p(fmt: F<'_>, f: impl FnOnce(&mut ast_show::P<'_, (), ()>)) {
    let unit = |_: &mut Formatter, _: &()| ();
    let mut p = ast_show::P::new(fmt, &unit, &unit);
    f(&mut p)
}

/// `Pos.pp`
pub fn pp_pos(fmt: F<'_>, p: &Pos) {
    ps(fmt, &ast_show::show_pos(p))
}

/// `Pos_or_decl.pp` (`Pos_or_decl.t = Pos.t`)
pub fn pp_pos_or_decl(fmt: F<'_>, p: &PosOrDecl) {
    pp_pos(fmt, &crate::pos_or_decl::unsafe_to_raw_pos(p.clone()))
}

/// The start of a record field: `@[name =@ `.
fn field(fmt: F<'_>, name: &str) {
    ob(fmt, 0);
    ps(fmt, name);
    ps(fmt, " =");
    sp(fmt)
}

/// A list (ppx_deriving's).
fn pp_list<A>(fmt: F<'_>, l: &[A], pp: impl Fn(&mut Formatter, &A)) {
    ob(fmt, 2);
    ps(fmt, "[");
    for (i, x) in l.iter().enumerate() {
        if i > 0 {
            semi(fmt)
        }
        pp(fmt, x)
    }
    cut(fmt);
    ps(fmt, "]");
    cb(fmt)
}

/// An option (ppx_deriving's).
fn pp_option<A>(fmt: F<'_>, o: &Option<A>, pp: impl Fn(&mut Formatter, &A)) {
    match o {
        None => ps(fmt, "None"),
        Some(x) => {
            ps(fmt, "(Some ");
            pp(fmt, x);
            ps(fmt, ")")
        }
    }
}

/// A constructor with one argument: `(@[<2>C@ ` .. `@])`.
fn ctor1(fmt: F<'_>, c: &str, a: impl FnOnce(&mut Formatter)) {
    ps(fmt, "(");
    ob(fmt, 2);
    ps(fmt, c);
    sp(fmt);
    a(fmt);
    cb(fmt);
    ps(fmt, ")")
}

/// A constructor with several arguments: `(@[<2>C (@,` .. `,@ ` .. `@,))@]`.
fn ctorn(fmt: F<'_>, c: &str, args: &[&dyn Fn(&mut Formatter)]) {
    ps(fmt, "(");
    ob(fmt, 2);
    ps(fmt, c);
    ps(fmt, " (");
    cut(fmt);
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            comma(fmt)
        }
        a(fmt)
    }
    cut(fmt);
    ps(fmt, "))");
    cb(fmt)
}

/// A tuple: `(@[` .. `,@ ` .. `@])`.
fn tuple(fmt: F<'_>, args: &[&dyn Fn(&mut Formatter)]) {
    ps(fmt, "(");
    ob(fmt, 0);
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            comma(fmt)
        }
        a(fmt)
    }
    cb(fmt);
    ps(fmt, ")")
}

/// `Wrapped_map.make_pp pp_key pp_data` over the bindings in order.
fn make_pp<K, V>(fmt: F<'_>, bindings: &[(K, V)], pp_key: impl Fn(&mut Formatter, &K), pp_data: impl Fn(&mut Formatter, &V)) {
    format::pp_open_hvbox(fmt, 2);
    ps(fmt, "{");
    if !bindings.is_empty() {
        ps(fmt, " ")
    }
    for (i, (k, v)) in bindings.iter().enumerate() {
        if i > 0 {
            semi(fmt)
        }
        ob(fmt, 0);
        pp_key(fmt, k);
        ps(fmt, " ->");
        sp(fmt);
        pp_data(fmt, v);
        cb(fmt)
    }
    if !bindings.is_empty() {
        ps(fmt, " ")
    }
    ps(fmt, "}");
    cb(fmt)
}

/// `S_map.pp pp_data`
fn pp_smap<V>(fmt: F<'_>, m: &[(String, V)], pp_data: impl Fn(&mut Formatter, &V)) {
    make_pp(fmt, m, |fmt, k| pp_s(fmt, k), pp_data)
}

// ~~ Typing_reason ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `pp_pos_id` (derived: a tuple)
pub fn pp_pos_id(fmt: F<'_>, (p, s): &PosId) {
    tuple(fmt, &[&|f| pp_pos_or_decl(f, p), &|f| pp_s(f, s)]);
}

fn pp_fun_kind(fmt: F<'_>, fk: &oxidized::ast_defs::FunKind) {
    with_p(fmt, |p| ast_show::ast_defs::pp_fun_kind(p, fk))
}

/// `pp_witness_locl`
pub fn pp_witness_locl(fmt: F<'_>, witness: &WL) {
    ps(fmt, crate::typing_reason::constructor_string_of_witness_locl(witness));
    sp(fmt);
    ps(fmt, "(");
    ob(fmt, 0);
    match witness {
        WL::RetFunKind(p, fk) => {
            pp_pos(fmt, p);
            comma(fmt);
            pp_fun_kind(fmt, fk)
        }
        WL::TypeVariableGenerics(p, s1, s2, _) => {
            pp_pos(fmt, p);
            comma(fmt);
            ps(fmt, s1);
            comma(fmt);
            ps(fmt, s2)
        }
        WL::UnsetField(p, s) | WL::Shape(p, s) | WL::Predicated(p, s) => {
            pp_pos(fmt, p);
            comma(fmt);
            ps(fmt, s)
        }
        WL::UnpackParam(p1, p2, i) => {
            pp_pos(fmt, p1);
            comma(fmt);
            pp_pos_or_decl(fmt, p2);
            comma(fmt);
            pp_d(fmt, *i)
        }
        WL::TypeVariable(p, _) | WL::TypeVariableError(p, _) => pp_pos(fmt, p),
        WL::Witness(p)
        | WL::IdxVector(p)
        | WL::IdxString(p)
        | WL::Foreach(p)
        | WL::Asyncforeach(p)
        | WL::Arith(p)
        | WL::ArithRet(p)
        | WL::ArithRetInt(p)
        | WL::ArithDynamic(p)
        | WL::BitwiseDynamic(p)
        | WL::IncdecDynamic(p)
        | WL::Comp(p)
        | WL::ConcatRet(p)
        | WL::Condition(p)
        | WL::LogicRet(p)
        | WL::Bitwise(p)
        | WL::BitwiseRet(p)
        | WL::NoReturn(p)
        | WL::NoReturnAsync(p)
        | WL::Throw(p)
        | WL::Placeholder(p)
        | WL::RetDiv(p)
        | WL::YieldGen(p)
        | WL::YieldAsyncgen(p)
        | WL::YieldAsyncnull(p)
        | WL::YieldSend(p)
        | WL::UnknownClass(p)
        | WL::VarParam(p)
        | WL::NullsafeOp(p)
        | WL::NullsafePipeOp(p)
        | WL::IsRefinement(p)
        | WL::AsRefinement(p)
        | WL::Equal(p)
        | WL::Using(p)
        | WL::DynamicProp(p)
        | WL::DynamicCall(p)
        | WL::DynamicConstruct(p)
        | WL::IdxDict(p)
        | WL::IdxSetElement(p)
        | WL::Regex(p)
        | WL::ShapeLiteral(p)
        | WL::Destructure(p)
        | WL::ShapeOrTupleDestructure(p)
        | WL::KeyValueCollectionKey(p)
        | WL::Splice(p)
        | WL::EtBoolean(p)
        | WL::ConcatOperand(p)
        | WL::InterpOperand(p)
        | WL::MissingClass(p)
        | WL::CapturedLike(p)
        | WL::UnsafeCast(p)
        | WL::Pattern(p)
        | WL::JoinPoint(p)
        | WL::StaticPropertyAccess(p)
        | WL::ClassConstantAccess(p) => pp_pos(fmt, p),
    }
    cb(fmt);
    ps(fmt, ")")
}

/// `pp_witness_decl`
pub fn pp_witness_decl(fmt: F<'_>, witness: &WD) {
    ps(fmt, &crate::typing_reason::constructor_string_of_witness_decl(witness));
    sp(fmt);
    ps(fmt, "(");
    ob(fmt, 0);
    match witness {
        WD::RetFunKindFromDecl(p, fk) => {
            pp_pos_or_decl(fmt, p);
            comma(fmt);
            pp_fun_kind(fmt, fk)
        }
        WD::ImplicitUpperBound(p, s)
        | WD::IllegalRecursiveType(p, s)
        | WD::MissingOptionalField(p, s)
        | WD::ClassClass(p, s) => {
            pp_pos_or_decl(fmt, p);
            comma(fmt);
            ps(fmt, s)
        }
        WD::Hint(p)
        | WD::WitnessFromDecl(p)
        | WD::PessimisedInout(p)
        | WD::PessimisedReturn(p, _)
        | WD::PessimisedProp(p, _)
        | WD::PessimisedThis(p)
        | WD::VarParamFromDecl(p)
        | WD::TupleFromSplat(p)
        | WD::GlobalFunParam(p)
        | WD::GlobalFunRet(p)
        | WD::Enforceable(p)
        | WD::SolveFail(p)
        | WD::VarrayOrDarrayKey(p)
        | WD::VecOrDictKey(p)
        | WD::DefaultCapability(p)
        | WD::IdxVectorFromDecl(p)
        | WD::IdxStringFromDecl(p)
        | WD::InoutParam(p)
        | WD::SupportDynamicType(p)
        | WD::SupportDynamicTypeAssume(p)
        | WD::GlobalClassProp(p)
        | WD::EnforcedType(p) => pp_pos_or_decl(fmt, p),
        WD::PolymorphicTypeParam(p, s1, s2, r) => {
            pp_pos_or_decl(fmt, p);
            comma(fmt);
            ps(fmt, s1);
            comma(fmt);
            ps(fmt, s2);
            comma(fmt);
            pp_d(fmt, *r)
        }
        WD::TconstNoCstr(pid) => pp_pos_id(fmt, pid),
        WD::CstrOnGenerics(p, pid) => {
            pp_pos_or_decl(fmt, p);
            comma(fmt);
            pp_pos_id(fmt, pid)
        }
        WD::GlobalTypeVariableGenerics(p, s1, s2) => {
            pp_pos_or_decl(fmt, p);
            comma(fmt);
            ps(fmt, s1);
            comma(fmt);
            ps(fmt, s2)
        }
    }
    cb(fmt);
    ps(fmt, ")")
}

/// `pp_arg_position` (derived)
fn pp_arg_position(fmt: F<'_>, ap: &crate::typing_reason::ArgPosition) {
    use crate::typing_reason::ArgPosition as A;
    ps(
        fmt,
        match ap {
            A::Aonly => "Typing_reason.Aonly",
            A::Afirst => "Typing_reason.Afirst",
            A::Asecond => "Typing_reason.Asecond",
        },
    )
}

/// `pp_blame` (derived)
fn pp_blame(fmt: F<'_>, b: &crate::typing_reason::Blame) {
    use crate::typing_reason::BlameSource as B;
    let crate::typing_reason::Blame::Blame(p, src) = b;
    ctorn(
        fmt,
        "Typing_reason.Blame",
        &[&|f| pp_pos(f, p), &|f| {
            ps(
                f,
                match src {
                    B::BScall => "Typing_reason.BScall",
                    B::BSlambda => "Typing_reason.BSlambda",
                    B::BSassignment => "Typing_reason.BSassignment",
                    B::BSoutOfScope => "Typing_reason.BSout_of_scope",
                },
            )
        }],
    )
}

/// `pp_expr_dep_type_reason` (derived)
fn pp_expr_dep_type_reason(fmt: F<'_>, e: &crate::typing_reason::ExprDepTypeReason) {
    use crate::typing_reason::ExprDepTypeReason as E;
    match e {
        E::ERexpr(id) => ctor1(fmt, "Typing_reason.ERexpr", |f| pp_d(f, *id)),
        E::ERstatic => ps(fmt, "Typing_reason.ERstatic"),
        E::ERclass(s) => ctor1(fmt, "Typing_reason.ERclass", |f| pp_s(f, s)),
        E::ERparent(s) => ctor1(fmt, "Typing_reason.ERparent", |f| pp_s(f, s)),
        E::ERself(s) => ctor1(fmt, "Typing_reason.ERself", |f| pp_s(f, s)),
        E::ERpu(s) => ctor1(fmt, "Typing_reason.ERpu", |f| pp_s(f, s)),
    }
}

/// `Typing_reason.pp_t_`
pub fn pp_reason(fmt: F<'_>, r: &R) {
    let open_paren = |f: &mut Formatter| {
        ps(f, "(");
        ob(f, 0)
    };
    let close_paren = |f: &mut Formatter| {
        cb(f);
        ps(f, ")")
    };
    match r {
        R::NoReason | R::Invalid | R::MissingField => {
            ps(fmt, &crate::typing_reason::to_constructor_string(r))
        }
        R::FromWitnessLocl(w) => pp_witness_locl(fmt, w),
        R::FromWitnessDecl(w) => pp_witness_decl(fmt, w),
        _ => {
            ps(fmt, &crate::typing_reason::to_constructor_string(r));
            sp(fmt);
            ps(fmt, "(");
            ob(fmt, 0);
            match r {
                R::NoReason | R::Invalid | R::MissingField | R::FromWitnessLocl(_) | R::FromWitnessDecl(_) => {
                    unreachable!("already matched")
                }
                R::Typeconst(r1, (p, s1), s2, r2) => {
                    pp_reason(fmt, r1);
                    comma(fmt);
                    open_paren(fmt);
                    pp_pos_or_decl(fmt, p);
                    comma(fmt);
                    ps(fmt, s1);
                    close_paren(fmt);
                    comma(fmt);
                    ps(fmt, s2.force());
                    comma(fmt);
                    pp_reason(fmt, r2)
                }
                R::TypeAccess(r, l) => {
                    pp_reason(fmt, r);
                    comma(fmt);
                    ps(fmt, "[");
                    ob(fmt, 0);
                    for (i, (r, s)) in l.iter().enumerate() {
                        if i > 0 {
                            comma(fmt)
                        }
                        open_paren(fmt);
                        pp_reason(fmt, r);
                        comma(fmt);
                        ps(fmt, s.force());
                        close_paren(fmt)
                    }
                    cb(fmt);
                    ps(fmt, "]")
                }
                R::Instantiate { type_, var_name, var } => {
                    pp_reason(fmt, type_);
                    comma(fmt);
                    ps(fmt, var_name);
                    comma(fmt);
                    pp_reason(fmt, var)
                }
                R::ExprDepType(r, p, edtr) => {
                    pp_reason(fmt, r);
                    comma(fmt);
                    pp_pos_or_decl(fmt, p);
                    comma(fmt);
                    pp_expr_dep_type_reason(fmt, edtr)
                }
                R::Idx(p, r) | R::LambdaParam(p, r) => {
                    pp_pos(fmt, p);
                    comma(fmt);
                    pp_reason(fmt, r)
                }
                R::Format(p, s, r) => {
                    pp_pos(fmt, p);
                    comma(fmt);
                    ps(fmt, s);
                    comma(fmt);
                    pp_reason(fmt, r)
                }
                R::DynamicPartialEnforcement(p, s, r) | R::OpaqueTypeFromModule(p, s, r) => {
                    pp_pos_or_decl(fmt, p);
                    comma(fmt);
                    ps(fmt, s);
                    comma(fmt);
                    pp_reason(fmt, r)
                }
                R::SDTCall(p, r) | R::LikeCall(p, r) => {
                    pp_pos_or_decl(fmt, p);
                    comma(fmt);
                    pp_reason(fmt, r)
                }
                R::ArithRetFloat(p, r, ap) | R::ArithRetNum(p, r, ap) => {
                    pp_pos(fmt, p);
                    comma(fmt);
                    pp_reason(fmt, r);
                    comma(fmt);
                    pp_arg_position(fmt, ap)
                }
                R::RigidTvarEscape(p, s1, s2, r) => {
                    pp_pos(fmt, p);
                    comma(fmt);
                    ps(fmt, s1);
                    comma(fmt);
                    ps(fmt, s2);
                    comma(fmt);
                    pp_reason(fmt, r)
                }
                R::LostInfo(s, r, b) => {
                    ps(fmt, s);
                    comma(fmt);
                    pp_reason(fmt, r);
                    comma(fmt);
                    pp_blame(fmt, b)
                }
                R::DynamicCoercion(r) => pp_reason(fmt, r),
                R::Flow { from, .. } => pp_reason(fmt, from),
                R::Axiom { next, .. } => pp_reason(fmt, next),
                R::LowerBound { bound, .. } => pp_reason(fmt, bound),
                R::PrjBoth { sub_prj, .. } => pp_reason(fmt, sub_prj),
                R::PrjOne { part, .. } => pp_reason(fmt, part),
                R::Def(_, t) => pp_reason(fmt, t),
                R::Solved { solution, .. } => pp_reason(fmt, solution),
            }
            cb(fmt);
            ps(fmt, ")")
        }
    }
}

// ~~ Typing_defs_core ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Pp.pp_ty` (of a localized type)
pub fn pp_ty(fmt: F<'_>, t: &Ty) {
    ps(fmt, "(");
    ob(fmt, 0);
    pp_reason(fmt, get_reason(t));
    comma(fmt);
    pp_ty_(fmt, get_node(t));
    cb(fmt);
    ps(fmt, ")")
}

fn pp_tys(fmt: F<'_>, l: &[Ty]) {
    pp_list(fmt, l, |f, t| pp_ty(f, t))
}

/// `Pp.pp_ty_`
pub fn pp_ty_(fmt: F<'_>, ty: &Ty_) {
    match ty {
        Ty_::Tany(_) => ps(fmt, "Tany"),
        Ty_::Tdynamic(_) => ps(fmt, "Tdynamic"),
        Ty_::Tnonnull => ps(fmt, "Tnonnull"),
        Ty_::Tgeneric(a0) => ctor1(fmt, "Tgeneric", |f| pp_s(f, a0)),
        Ty_::Taccess(a0) => ctor1(fmt, "Taccess", |f| pp_taccess_type(f, a0)),
        Ty_::TvecOrDict(a0, a1) => {
            // `(@[<2>Tvec_or_dict@ ` a0 `,@ ` a1 `@])`
            ps(fmt, "(");
            ob(fmt, 2);
            ps(fmt, "Tvec_or_dict");
            sp(fmt);
            pp_ty(fmt, a0);
            comma(fmt);
            pp_ty(fmt, a1);
            cb(fmt);
            ps(fmt, ")")
        }
        Ty_::Toption(a0) => ctor1(fmt, "Toption", |f| pp_ty(f, a0)),
        Ty_::Tprim(a0) => ctor1(fmt, "Tprim", |f| with_p(f, |p| ast_show::aast_defs::pp_tprim(p, a0))),
        Ty_::Tfun(a0) => ctor1(fmt, "Tfun", |f| pp_fun_type(f, a0)),
        Ty_::Ttuple(a0) => ctor1(fmt, "Ttuple", |f| pp_tuple_type(f, a0)),
        Ty_::Tshape(a0) => ctor1(fmt, "Tshape", |f| pp_shape_type(f, a0)),
        Ty_::Tvar(a0) => ctor1(fmt, "Tvar", |f| pp_d(f, *a0)),
        Ty_::Tnewtype(a0, a1, a2) => ctorn(fmt, "Tnewtype", &[&|f| pp_s(f, a0), &|f| pp_tys(f, a1), &|f| pp_ty(f, a2)]),
        Ty_::Tdependent(a0, a1) => {
            ps(fmt, "(");
            ob(fmt, 2);
            ps(fmt, "Tdependent");
            sp(fmt);
            pp_dependent_type(fmt, a0);
            comma(fmt);
            pp_ty(fmt, a1);
            cb(fmt);
            ps(fmt, ")")
        }
        Ty_::Tunion(tyl) => ctor1(fmt, "Tunion", |f| pp_tys(f, tyl)),
        Ty_::Tintersection(tyl) => ctor1(fmt, "Tintersection", |f| pp_tys(f, tyl)),
        Ty_::Tclass(a0, a2, a1) => {
            ctorn(fmt, "Tclass", &[&|f| pp_pos_id(f, a0), &|f| pp_exact(f, a2), &|f| pp_tys(f, a1)])
        }
        Ty_::Tneg(a0) => ctor1(fmt, "Tneg", |f| pp_type_predicate(f, a0)),
        Ty_::Tlabel(a0) => ctor1(fmt, "Tlabel", |f| pp_s(f, a0)),
        Ty_::TclassPtr(a0) => ctor1(fmt, "Tclass_ptr", |f| pp_ty(f, a0)),
    }
}

/// `pp_dependent_type` (derived)
fn pp_dependent_type(fmt: F<'_>, d: &DependentType) {
    let DependentType::DTexpr(id) = d;
    ctor1(fmt, "Typing_defs_core.DTexpr", |f| pp_d(f, *id))
}

fn pp_refined_const(fmt: F<'_>, rc: &RefinedConst) {
    ob(fmt, 2);
    ps(fmt, "{");
    ps(fmt, "rc_bound = ");
    match &rc.bound {
        RefinedConstBound::TRexact(exact) => {
            ps(fmt, "TRexact ");
            pp_ty(fmt, exact)
        }
        RefinedConstBound::TRloose(RefinedConstBounds { lower, upper }) => {
            ps(fmt, "TRloose ");
            ob(fmt, 2);
            ps(fmt, "{");
            ps(fmt, "tr_lower = ");
            pp_tys(fmt, lower);
            semi(fmt);
            ps(fmt, "tr_upper = ");
            pp_tys(fmt, upper)
            // (The OCaml never closes this box.)
        }
    }
    semi(fmt);
    ps(fmt, "rc_is_ctx = ");
    pp_b(fmt, rc.is_ctx);
    ps(fmt, "}");
    cb(fmt)
}

fn pp_class_refinement(fmt: F<'_>, cr: &ClassRefinement) {
    ob(fmt, 2);
    ps(fmt, "{");
    ps(fmt, "cr_consts = ");
    let b: Vec<(String, RefinedConst)> = cr.cr_consts.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    pp_smap(fmt, &b, |f, rc| pp_refined_const(f, rc));
    semi(fmt);
    ps(fmt, "}");
    cb(fmt)
}

fn pp_exact(fmt: F<'_>, e: &Exact) {
    match e {
        Exact::Exact => ps(fmt, "Exact"),
        Exact::Nonexact(cr) => {
            ps(fmt, "Nonexact ");
            pp_class_refinement(fmt, cr)
        }
    }
}

fn pp_taccess_type(fmt: F<'_>, TaccessType(a0, a1): &TaccessType) {
    ps(fmt, "(");
    ob(fmt, 0);
    pp_ty(fmt, a0);
    comma(fmt);
    ob(fmt, 2);
    ps(fmt, "[");
    pp_pos_id(fmt, a1);
    cut(fmt);
    ps(fmt, "]");
    cb(fmt);
    cb(fmt);
    ps(fmt, ")")
}

/// `pp_tshape_field_name` (derived, with the path)
fn pp_tshape_field_name(fmt: F<'_>, n: &TshapeFieldName) {
    let pos_string = |f: &mut Formatter, (p, s): &(PosOrDecl, String)| tuple(f, &[&|f| pp_pos_or_decl(f, p), &|f| pp_s(f, s)]);
    match n {
        TshapeFieldName::TSFregexGroup(x) => {
            ctor1(fmt, "Typing_defs_core.TSFregex_group", |f| pos_string(f, &(x.0.clone(), x.1.clone())))
        }
        TshapeFieldName::TSFlitStr(x) => ctor1(fmt, "Typing_defs_core.TSFlit_str", |f| {
            tuple(f, &[&|f| pp_pos_or_decl(f, &x.0), &|f| pp_s(f, &x.1)])
        }),
        TshapeFieldName::TSFclassConst(pid, x) => ctorn(
            fmt,
            "Typing_defs_core.TSFclass_const",
            &[&|f| pp_pos_id(f, pid), &|f| pos_string(f, &(x.0.clone(), x.1.clone()))],
        ),
    }
}

fn pp_tshape_map<V>(fmt: F<'_>, m: &t_shape_map::TShapeMap<V>, pp_val: impl Fn(&mut Formatter, &V)) {
    let b: Vec<(&TshapeFieldName, &V)> = m.iter().map(|(k, v)| (&k.0, v)).collect();
    make_pp(fmt, &b, |f, k| pp_tshape_field_name(f, k), |f, v| pp_val(f, v))
}

/// A record (ppx_deriving's): the field names as printed (the first one
/// qualified by the module where the type has a path).
fn record_fields(fmt: F<'_>, fields: &[(&str, &dyn Fn(&mut Formatter))]) {
    ob(fmt, 2);
    ps(fmt, "{ ");
    for (i, (name, pp)) in fields.iter().enumerate() {
        if i > 0 {
            semi(fmt)
        }
        field(fmt, name);
        pp(fmt);
        cb(fmt)
    }
    sp(fmt);
    ps(fmt, "}");
    cb(fmt)
}

fn pp_shape_field_type(fmt: F<'_>, sft: &ShapeFieldType) {
    record_fields(fmt, &[("sft_optional", &|f| pp_b(f, sft.optional)), ("sft_ty", &|f| pp_ty(f, &sft.ty))])
}

/// `pp_type_origin` (derived, with the path; the position is `[@opaque]`)
fn pp_type_origin(fmt: F<'_>, o: &TypeOrigin) {
    match o {
        TypeOrigin::MissingOrigin => ps(fmt, "Typing_defs_core.Missing_origin"),
        TypeOrigin::FromAlias(s, _) => {
            ctorn(fmt, "Typing_defs_core.From_alias", &[&|f| pp_s(f, s), &|f| ps(f, "<opaque>")])
        }
    }
}

fn pp_shape_type(fmt: F<'_>, st: &ShapeType) {
    match st {
        ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => {
            ob(fmt, 2);
            ps(fmt, "Shape_splat { ");
            field(fmt, "ss_elems");
            ob(fmt, 2);
            ps(fmt, "[");
            for ty in ss_elems {
                sp(fmt);
                pp_ty(fmt, ty)
            }
            cb(fmt);
            sp(fmt);
            ps(fmt, "]");
            cb(fmt);
            sp(fmt);
            ps(fmt, "}");
            cb(fmt)
        }
        ShapeType::ShapeSimple(ShapeTypeSimple {
            origin,
            unknown_value,
            fields,
        }) => record_fields(
            fmt,
            &[
                ("s_origin", &|f| pp_type_origin(f, origin)),
                ("s_fields", &|f| pp_tshape_map(f, fields, |f, v| pp_shape_field_type(f, v))),
                ("s_unknown_value", &|f| pp_ty(f, unknown_value)),
            ],
        ),
    }
}

fn pp_tuple_type(fmt: F<'_>, t: &TupleType) {
    ob(fmt, 2);
    ps(fmt, "{ ");
    field(fmt, "t_required");
    pp_tys(fmt, &t.required);
    cb(fmt);
    semi(fmt);
    field(fmt, "t_optional");
    pp_tys(fmt, &t.optional);
    cb(fmt);
    semi(fmt);
    match &t.extra {
        TupleExtra::Tvariadic(t) => {
            field(fmt, "t_variadic");
            pp_ty(fmt, t);
            cb(fmt)
        }
        TupleExtra::Tsplat(t) => {
            field(fmt, "t_splat");
            pp_ty(fmt, t);
            cb(fmt)
        }
    }
    sp(fmt);
    ps(fmt, "}");
    cb(fmt)
}

fn pp_type_predicate(fmt: F<'_>, TypePredicate(_, p): &TypePredicate) {
    pp_type_predicate_(fmt, p)
}

fn pp_type_predicate_(fmt: F<'_>, p: &TypePredicate_) {
    match p {
        TypePredicate_::IsTag(tag) => ctor1(fmt, "IsTag", |f| pp_type_tag(f, tag)),
        TypePredicate_::IsTupleOf(TuplePredicate { required }) => ctor1(fmt, "IsTupleOf", |f| {
            record_fields(f, &[("tp_required", &|f| pp_list(f, required, |f, p| pp_type_predicate(f, p)))])
        }),
        TypePredicate_::IsShapeOf(ShapePredicate {
            allows_unknown_fields,
            fields,
        }) => ctor1(fmt, "IsShapeOf", |f| {
            record_fields(
                f,
                &[
                    ("sp_fields", &|f| {
                        pp_tshape_map(f, fields, |f, sfp| {
                            record_fields(
                                f,
                                &[
                                    ("sfp_predicate", &|f| pp_type_predicate(f, &sfp.predicate)),
                                    ("sfp_optional", &|f| pp_b(f, sfp.optional)),
                                ],
                            )
                        })
                    }),
                    ("sp_allows_unknown_fields", &|f| pp_b(f, *allows_unknown_fields)),
                ],
            )
        }),
        TypePredicate_::IsUnionOf(ps_) => ctor1(fmt, "IsUnionOf", |f| pp_list(f, ps_, |f, p| pp_type_predicate(f, p))),
        TypePredicate_::IsNot(p) => ctor1(fmt, "IsNot", |f| pp_type_predicate(f, p)),
    }
}

fn pp_type_tag(fmt: F<'_>, tag: &TypeTag) {
    match tag {
        TypeTag::BoolTag => ps(fmt, "BoolTag"),
        TypeTag::IntTag => ps(fmt, "IntTag"),
        TypeTag::ArraykeyTag => ps(fmt, "ArraykeyTag"),
        TypeTag::FloatTag => ps(fmt, "FloatTag"),
        TypeTag::NumTag => ps(fmt, "NumTag"),
        TypeTag::ResourceTag => ps(fmt, "ResourceTag"),
        TypeTag::NullTag => ps(fmt, "NullTag"),
        TypeTag::ClassTag(id, args) => ctorn(
            fmt,
            "ClassTag",
            &[&|f| ps(f, id), &|f| {
                pp_list(f, args, |f, g| match g {
                    TypeTagGeneric::Filled(ty) => ctor1(f, "Filled", |f| pp_ty(f, ty)),
                    TypeTagGeneric::Wildcard(id) => ctor1(f, "Wildcard", |f| pp_d(f, *id)),
                })
            }],
        ),
        TypeTag::EnumTag(id) => ctor1(fmt, "EnumTag", |f| ps(f, id)),
        TypeTag::GenericTag { name, from_like } => {
            ps(fmt, "(");
            ob(fmt, 2);
            ps(fmt, "GenericTag {");
            cut(fmt);
            ps(fmt, "name =");
            sp(fmt);
            ps(fmt, name);
            semi(fmt);
            ps(fmt, "from_like =");
            sp(fmt);
            pp_b(fmt, *from_like);
            cut(fmt);
            ps(fmt, "}");
            cb(fmt);
            ps(fmt, ")")
        }
    }
}

/// `pp_user_attribute` (derived, with the path)
fn pp_user_attribute(fmt: F<'_>, ua: &UserAttribute) {
    record_fields(
        fmt,
        &[
            ("Typing_defs_core.ua_name", &|f| pp_pos_id(f, &ua.name)),
            ("ua_params", &|f| {
                pp_list(f, &ua.params, |f, p| match p {
                    UserAttributeParam::Classname(s) => ctor1(f, "Typing_defs_core.Classname", |f| pp_s(f, s)),
                    UserAttributeParam::EnumClassLabel(s) => {
                        ctor1(f, "Typing_defs_core.EnumClassLabel", |f| pp_s(f, s))
                    }
                    UserAttributeParam::String(s) => ctor1(f, "Typing_defs_core.String", |f| pp_s(f, s)),
                    UserAttributeParam::Int(s) => ctor1(f, "Typing_defs_core.Int", |f| pp_s(f, s)),
                })
            }),
            ("ua_raw_val", &|f| pp_option(f, &ua.raw_val, |f, s| pp_s(f, s))),
        ],
    )
}

/// `pp_tparam` (derived, with the path)
fn pp_tparam(fmt: F<'_>, tp: &Tparam) {
    record_fields(
        fmt,
        &[
            ("Typing_defs_core.tp_variance", &|f| with_p(f, |p| ast_show::ast_defs::pp_variance(p, &tp.variance))),
            ("tp_name", &|f| pp_pos_id(f, &tp.name)),
            ("tp_constraints", &|f| {
                pp_list(f, &tp.constraints, |f, (ck, ty)| {
                    tuple(f, &[&|f| with_p(f, |p| ast_show::ast_defs::pp_constraint_kind(p, ck)), &|f| pp_ty(f, ty)])
                })
            }),
            ("tp_reified", &|f| with_p(f, |p| ast_show::ast_defs::pp_reify_kind(p, &tp.reified))),
            ("tp_user_attributes", &|f| pp_list(f, &tp.user_attributes, |f, ua| pp_user_attribute(f, ua))),
        ],
    )
}

/// `pp_where_constraint` (derived: a triple)
fn pp_where_constraint(fmt: F<'_>, WhereConstraint(a, ck, b): &WhereConstraint) {
    tuple(
        fmt,
        &[&|f| pp_ty(f, a), &|f| with_p(f, |p| ast_show::ast_defs::pp_constraint_kind(p, ck)), &|f| pp_ty(f, b)],
    )
}

/// `Typing_defs_flags.Fun.pp` (the derived printer of its record)
fn pp_fun_flags(fmt: F<'_>, t: crate::typing_defs_flags::fun::T) {
    use crate::typing_defs_flags::fun;
    let fk = fun::fun_kind(t);
    record_fields(
        fmt,
        &[
            ("Typing_defs_flags.Fun.return_disposable", &|f| pp_b(f, fun::return_disposable(t))),
            ("async", &|f| pp_b(f, fun::async_(t))),
            ("generator", &|f| pp_b(f, fun::generator(t))),
            ("fun_kind", &|f| pp_fun_kind(f, &fk)),
            ("is_function_pointer", &|f| pp_b(f, fun::is_function_pointer(t))),
            ("returns_readonly", &|f| pp_b(f, fun::returns_readonly(t))),
            ("readonly_this", &|f| pp_b(f, fun::readonly_this(t))),
            ("support_dynamic_type", &|f| pp_b(f, fun::support_dynamic_type(t))),
            ("is_memoized", &|f| pp_b(f, fun::is_memoized(t))),
            ("variadic", &|f| pp_b(f, fun::variadic(t))),
            ("named_variadic", &|f| pp_b(f, fun::named_variadic(t))),
        ],
    )
}

/// `Typing_defs_flags.FunParam.pp`
fn pp_fun_param_flags(fmt: F<'_>, t: crate::typing_defs_flags::fun_param::T) {
    use crate::typing_defs_flags::fun_param as fp;
    record_fields(
        fmt,
        &[
            ("Typing_defs_flags.FunParam.accept_disposable", &|f| pp_b(f, fp::accept_disposable(t))),
            ("inout", &|f| pp_b(f, fp::inout(t))),
            ("is_optional", &|f| pp_b(f, fp::is_optional(t))),
            ("readonly", &|f| pp_b(f, fp::readonly(t))),
            ("ignore_readonly_error", &|f| pp_b(f, fp::ignore_readonly_error(t))),
            ("splat", &|f| pp_b(f, fp::splat(t))),
            ("named", &|f| pp_b(f, fp::named(t))),
        ],
    )
}

/// `pp_fun_param` (derived, no path)
fn pp_fun_param(fmt: F<'_>, p: &FunParam) {
    record_fields(
        fmt,
        &[
            ("fp_pos", &|f| pp_pos_or_decl(f, &p.pos)),
            ("fp_name", &|f| pp_option(f, &p.name, |f, s| pp_s(f, s))),
            ("fp_type", &|f| pp_ty(f, &p.type_)),
            ("fp_flags", &|f| pp_fun_param_flags(f, p.flags)),
            ("fp_def_value", &|f| pp_option(f, &p.def_value, |f, s| pp_s(f, s))),
        ],
    )
}

/// `pp_fun_type pp_ty` (derived, no path)
fn pp_fun_type(fmt: F<'_>, ft: &FunType) {
    record_fields(
        fmt,
        &[
            ("ft_tparams", &|f| pp_list(f, &ft.tparams, |f, tp| pp_tparam(f, tp))),
            ("ft_where_constraints", &|f| pp_list(f, &ft.where_constraints, |f, wc| pp_where_constraint(f, wc))),
            ("ft_params", &|f| pp_list(f, &ft.params, |f, p| pp_fun_param(f, p))),
            ("ft_implicit_params", &|f| {
                record_fields(
                    f,
                    &[("capability", &|f| match &ft.implicit_params.capability {
                        Capability::CapDefaults(p) => ctor1(f, "CapDefaults", |f| pp_pos_or_decl(f, p)),
                        Capability::CapTy(t) => ctor1(f, "CapTy", |f| pp_ty(f, t)),
                    })],
                )
            }),
            ("ft_ret", &|f| pp_ty(f, &ft.ret)),
            ("ft_flags", &|f| pp_fun_flags(f, ft.flags)),
            ("ft_instantiated", &|f| pp_b(f, ft.instantiated)),
        ],
    )
}

// ~~ Typing_set, Typing_kinding_defs, Type_parameter_env ~~~~~~~~~~~~~~~~~~~~

/// `Typing_set.pp`
fn pp_ty_set(fmt: F<'_>, s: &crate::typing_set::T) {
    format::pp_open_hvbox(fmt, 2);
    ps(fmt, "{");
    for (i, ty) in s.iter().enumerate() {
        if i > 0 {
            semi(fmt)
        }
        pp_ty(fmt, ty)
    }
    cut(fmt);
    ps(fmt, "}");
    cb(fmt)
}

/// `Typing_kinding_defs.pp_kind` (derived, with the path)
fn pp_kind(fmt: F<'_>, k: &crate::typing_kinding_defs::Kind) {
    record_fields(
        fmt,
        &[
            ("Typing_kinding_defs.lower_bounds", &|f| pp_ty_set(f, &k.lower_bounds)),
            ("upper_bounds", &|f| pp_ty_set(f, &k.upper_bounds)),
            ("reified", &|f| with_p(f, |p| ast_show::aast_defs::pp_reify_kind(p, &k.reified))),
            ("enforceable", &|f| pp_b(f, k.enforceable)),
            ("newable", &|f| pp_b(f, k.newable)),
            ("require_dynamic", &|f| pp_b(f, k.require_dynamic)),
            ("rank", &|f| pp_d(f, k.rank)),
        ],
    )
}

/// `Type_parameter_env.pp` (derived, no path)
fn pp_tpenv(fmt: F<'_>, t: &crate::type_parameter_env::T) {
    let tparams: Vec<(String, (PosOrDecl, crate::typing_kinding_defs::Kind))> = crate::type_parameter_env::get_tparams(t)
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    record_fields(
        fmt,
        &[
            ("tparams", &|f| {
                pp_smap(f, &tparams, |f, (p, k)| tuple(f, &[&|f| pp_pos_or_decl(f, p), &|f| pp_kind(f, k)]))
            }),
            ("consistent", &|f| pp_b(f, crate::type_parameter_env::is_consistent(t))),
        ],
    )
}

// ~~ Tast ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Tast.pp_fun_tast_info` (derived, with the path)
fn pp_fun_tast_info(fmt: F<'_>, i: &tast::FunTastInfo) {
    record_fields(
        fmt,
        &[
            ("Tast.has_implicit_return", &|f| pp_b(f, i.has_implicit_return)),
            ("has_readonly", &|f| pp_b(f, i.has_readonly)),
            ("dynamic_locals", &|f| {
                pp_list(f, &i.dynamic_locals, |f, dl| {
                    record_fields(
                        f,
                        &[
                            ("Tast.dl_name", &|f| pp_s(f, &dl.name)),
                            ("dl_pos", &|f| pp_pos(f, &dl.pos)),
                            ("dl_shadow_tvid", &|f| pp_d(f, dl.shadow_tvid)),
                        ],
                    )
                })
            }),
        ],
    )
}

/// `Tast.pp_saved_env` (derived, with the path)
pub fn pp_saved_env(fmt: F<'_>, e: &tast::SavedEnv) {
    record_fields(
        fmt,
        &[
            ("Tast.tcopt", &|f| ps(f, "<opaque>")),
            ("inference_env", &|f| ps(f, "<opaque>")),
            ("tpenv", &|f| pp_tpenv(f, &e.tpenv)),
            ("fun_tast_info", &|f| pp_option(f, &e.fun_tast_info, |f, i| pp_fun_tast_info(f, i))),
            ("checked", &|f| with_p(f, |p| ast_show::aast_defs::pp_check_status(p, &e.checked))),
        ],
    )
}

/// `Tast.pp_program`
pub fn pp_program(fmt: F<'_>, program: &tast::Program) {
    let pp_ex = |f: &mut Formatter, t: &tast::Ty| pp_ty(f, t);
    let pp_en = |f: &mut Formatter, e: &tast::SavedEnv| pp_saved_env(f, e);
    let mut p = ast_show::P::new(fmt, &pp_ex, &pp_en);
    ast_show::aast_defs::pp_program(&mut p, program)
}

/// `Format.asprintf "%a" Pp.pp_ty ty` (`Typing_defs_core.Pp.show_ty`)
pub fn show_ty(ty: &Ty) -> String {
    format::asprintf(|f| pp_ty(f, ty))
}

#[allow(unused_imports)]
use aast as _aast;

/// What `hh_client --show-tast` prints of the TASTs of `STATUS_SINGLE`
/// (`client_check.ml`): `Relative_path.Map.map tasts ~f:Tast.program_by_names
/// |> Tast_hashes.hash_tasts_by_file |> Relative_path.Map.yojson_of_t
/// Tast_hashes.yojson_of_by_names |> pretty_to_channel`, and
/// `Relative_path.Map.show (Tast_with_dynamic.pp Tast.pp_program) tasts`.
/// Made by the server, which has the TASTs (they do not cross the socket).
pub fn show_tasts(
    tasts: &crate::relative_path::map::T<crate::tast_with_dynamic::T<tast::Program>>,
) -> (String, String) {
    use crate::yojson::safe::T as J;
    let hashes = J::Assoc(
        tasts
            .iter()
            .map(|(path, tast)| {
                let by_names = tast::program_by_names(tast.clone());
                let hashes = crate::tast_hashes::hash_tasts(&by_names);
                (
                    crate::relative_path::suffix(path).to_string(),
                    crate::tast_hashes::yojson_of_by_names(&hashes),
                )
            })
            .collect(),
    );
    let hashes = crate::yojson::safe::pretty_to_string(&hashes);
    let bindings: Vec<_> = tasts.iter().collect();
    let shown = format::asprintf(|fmt| {
        make_pp(
            fmt,
            &bindings,
            |f, p| crate::relative_path::pp(f, p),
            |f, t| crate::tast_with_dynamic::pp(|f, prog| pp_program(f, prog), f, t),
        )
    });
    (hashes, shown)
}
