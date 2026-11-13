// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `hint_print.ml`. See `hh/PORTING.md`.
//!
//! The printers of hints, expressions and type parameters of the (untyped or
//! typed) AST, on a `Format.formatter` (`crate::format::Formatter`), with
//! the combinators of `Format_helpers` (`Fmt`). They are generic in the
//! annotations of the AST (`'ex`, `'en`).
//!
//! Where OCaml applies a combinator partially, there is a closure; where it
//! calls `Format.fprintf ppf {|%a %a|}`, there are the calls that `fprintf`
//! makes for the format string (see `crate::format`).
//!
//! The strings of the AST that are byte strings (`String` literals, the
//! names of shape fields) are printed as UTF-8, with invalid bytes replaced
//! (`crate::format` prints `&str`).

#![allow(non_upper_case_globals)]

use oxidized::aast;
use oxidized::aast_defs;
use oxidized::ast_defs;

use crate::format;
use crate::format::Formatter;
use crate::format_helpers as fmt;
use crate::naming_special_names as sn;

/// `Fmt.(const string s)`
fn const_string(s: &str) -> impl Fn(&mut Formatter, ()) + '_ {
    move |ppf, ()| fmt::const_(fmt::string, s, ppf, ())
}

/// `pp_hint ~is_ctx:false`
fn pp_hint_no_ctx(ppf: &mut Formatter, hint: &aast::Hint) {
    pp_hint(false, ppf, hint)
}

/// `List.zip_exn`
fn zip_exn<A, B>(l1: Vec<A>, l2: Vec<B>) -> Vec<(A, B)> {
    if l1.len() != l2.len() {
        panic!(
            "Invalid_argument: length mismatch in zip_exn: {} <> {}",
            l1.len(),
            l2.len()
        )
    }
    l1.into_iter().zip(l2).collect()
}

fn strip_ns(obj_name: &str) -> &str {
    match obj_name.rsplit_once('\\') {
        Some((_, name)) => name,
        None => obj_name,
    }
}

fn pp_paramkind(ppf: &mut Formatter, k: &ast_defs::ParamKind) {
    match k {
        ast_defs::ParamKind::Pinout(_) => fmt::string(ppf, "inout"),
        ast_defs::ParamKind::Pnormal => (),
    }
}

pub const any_type_name: &str = "ANY_TYPE";

/// The kinds of the bounds of a refinement (`` `E | `L | `U ``).
#[derive(Clone, Copy)]
enum BoundKind {
    E,
    L,
    U,
}

pub fn pp_hint(is_ctx: bool, ppf: &mut Formatter, hint: &aast::Hint) {
    let aast::Hint(pos, hint_) = hint;
    use aast::Hint_;
    match &**hint_ {
        Hint_::Hthis => fmt::string(ppf, "this"),
        Hint_::Hdynamic => fmt::string(ppf, "dynamic"),
        Hint_::Hnothing => fmt::string(ppf, "nothing"),
        Hint_::Hmixed => fmt::string(ppf, "mixed"),
        Hint_::Hwildcard => fmt::string(ppf, "_"),
        Hint_::Hnonnull => fmt::string(ppf, "nonnull"),
        Hint_::Hvar(name) => fmt::string(ppf, name),
        Hint_::HfunContext(name) => {
            fmt::prefix(const_string("ctx "), fmt::string, ppf, name.as_str())
        }
        Hint_::Hoption(hint) => fmt::prefix(const_string("?"), pp_hint_no_ctx, ppf, hint),
        Hint_::Hlike(hint) => fmt::prefix(const_string("~"), pp_hint_no_ctx, ppf, hint),
        Hint_::Hsoft(hint) => fmt::prefix(const_string("@"), pp_hint_no_ctx, ppf, hint),
        // TODO optional and variadic components T201398626 T201398652
        Hint_::Htuple(aast::TupleInfo {
            required: tup_required,
            extra: _,
        }) => fmt::parens(
            |ppf, hints: &[aast::Hint]| fmt::list(Some(&fmt::comma), pp_hint_no_ctx, ppf, hints),
            ppf,
            tup_required.as_slice(),
        ),
        Hint_::Hunion(hints) => fmt::parens(
            |ppf, hints: &[aast::Hint]| fmt::list(Some(&fmt::vbar), pp_hint_no_ctx, ppf, hints),
            ppf,
            hints.as_slice(),
        ),
        Hint_::Hintersection(hints) if is_ctx => fmt::brackets(
            |ppf, hints: &[aast::Hint]| {
                fmt::list(Some(&fmt::comma), |ppf, h| pp_hint(true, ppf, h), ppf, hints)
            },
            ppf,
            hints.as_slice(),
        ),
        Hint_::Hintersection(hints) => fmt::parens(
            |ppf, hints: &[aast::Hint]| fmt::list(Some(&fmt::amp), pp_hint_no_ctx, ppf, hints),
            ppf,
            hints.as_slice(),
        ),
        Hint_::Hprim(prim) => fmt::string(ppf, &crate::aast_defs::string_of_tprim(*prim)),
        Hint_::Haccess(root, ids) => {
            let ids: Vec<String> = ids.iter().map(|ast_defs::Id(_, id)| id.clone()).collect();
            fmt::pair(
                Some(&fmt::dbl_colon),
                pp_hint_no_ctx,
                |ppf, ids: &[String]| {
                    fmt::list(
                        Some(&fmt::dbl_colon),
                        |ppf, id: &String| fmt::string(ppf, id),
                        ppf,
                        ids,
                    )
                },
                ppf,
                (root, ids.as_slice()),
            )
        }
        Hint_::Hrefinement(ty, members) => {
            let pp_bounds =
                |is_ctx: bool, ppf: &mut Formatter, bounds: &[(BoundKind, &aast::Hint)]| {
                    let bound = |ppf: &mut Formatter, (kind, hint): &(BoundKind, &aast::Hint)| {
                        fmt::string(
                            ppf,
                            match kind {
                                BoundKind::E => "= ",
                                BoundKind::L => "as ",
                                BoundKind::U => "super ",
                            },
                        );
                        pp_hint(is_ctx, ppf, hint)
                    };
                    fmt::list(Some(&const_string(" ")), bound, ppf, bounds)
                };
            let member = |ppf: &mut Formatter, member: &aast::Refinement| match member {
                aast::Refinement::Rtype(ident, ref_) => {
                    fmt::string(ppf, &("type ".to_string() + &ident.1 + " "));
                    pp_bounds(
                        false,
                        ppf,
                        &match ref_ {
                            aast::TypeRefinement::TRexact(hint) => vec![(BoundKind::E, hint)],
                            aast::TypeRefinement::TRloose(aast::TypeRefinementBounds {
                                lower: tr_lower,
                                upper: tr_upper,
                            }) => {
                                let mut bounds: Vec<(BoundKind, &aast::Hint)> =
                                    tr_lower.iter().map(|x| (BoundKind::L, x)).collect();
                                bounds.extend(tr_upper.iter().map(|x| (BoundKind::U, x)));
                                bounds
                            }
                        },
                    )
                }
                aast::Refinement::Rctx(ident, ref_) => {
                    fmt::string(ppf, &("ctx ".to_string() + &ident.1 + " "));
                    pp_bounds(
                        true,
                        ppf,
                        &match ref_ {
                            aast::CtxRefinement::CRexact(hint) => vec![(BoundKind::E, hint)],
                            aast::CtxRefinement::CRloose(aast::CtxRefinementBounds {
                                lower: cr_lower,
                                upper: cr_upper,
                            }) => {
                                // `Option.value_map ~default:[]`
                                fn opt_map(
                                    x: &Option<aast::Hint>,
                                    k: BoundKind,
                                ) -> Vec<(BoundKind, &aast::Hint)> {
                                    match x {
                                        None => vec![],
                                        Some(x) => vec![(k, x)],
                                    }
                                }
                                let mut bounds = opt_map(cr_lower, BoundKind::L);
                                bounds.extend(opt_map(cr_upper, BoundKind::U));
                                bounds
                            }
                        },
                    )
                }
            };
            fmt::suffix(fmt::with_, pp_hint_no_ctx, ppf, ty);
            fmt::braces(
                |ppf, members: &[aast::Refinement]| {
                    fmt::list(Some(&fmt::semi_sep), member, ppf, members)
                },
                ppf,
                members.as_slice(),
            )
        }
        Hint_::HvecOrDict(None, vhint) => fmt::prefix(
            const_string("vec_or_dict"),
            |ppf, h| fmt::angles(pp_hint_no_ctx, ppf, h),
            ppf,
            vhint,
        ),
        Hint_::HvecOrDict(Some(khint), vhint) => fmt::prefix(
            const_string("vec_or_dict"),
            |ppf, kv| {
                fmt::angles(
                    |ppf, kv| fmt::pair(Some(&fmt::comma), pp_hint_no_ctx, pp_hint_no_ctx, ppf, kv),
                    ppf,
                    kv,
                )
            },
            ppf,
            (khint, vhint),
        ),
        Hint_::Happly(ast_defs::Id(p, name), hs) if is_ctx => pp_hint(
            false,
            ppf,
            &aast::Hint(
                pos.clone(),
                Box::new(Hint_::Happly(
                    ast_defs::Id(p.clone(), strip_ns(name).to_string()),
                    hs.clone(),
                )),
            ),
        ),
        Hint_::Habstr(name) => fmt::string(ppf, name),
        Hint_::Happly(ast_defs::Id(_, name), hints) if hints.is_empty() => fmt::string(ppf, name),
        Hint_::HclassPtr(kind, h) => {
            let kind = match kind {
                aast::ClassPtrKind::CKclass => "class",
                aast::ClassPtrKind::CKenum => "enum",
            };
            fmt::prefix(
                const_string(kind),
                |ppf, h| fmt::angles(pp_hint_no_ctx, ppf, h),
                ppf,
                h,
            )
        }
        Hint_::Happly(ast_defs::Id(_, name), hints) => fmt::prefix(
            const_string(name),
            |ppf, hints: &[aast::Hint]| {
                fmt::angles(
                    |ppf, hints: &[aast::Hint]| {
                        fmt::list(Some(&fmt::comma), pp_hint_no_ctx, ppf, hints)
                    },
                    ppf,
                    hints,
                )
            },
            ppf,
            hints.as_slice(),
        ),
        Hint_::Hfun(aast::HintFun {
            param_tys: hf_param_tys,
            param_info: hf_param_info,
            variadic_ty: hf_variadic_ty,
            named_variadic_ty: hf_named_variadic_ty,
            return_ty: hf_return_ty,
            ctxs: hf_ctxs,
            ..
        }) => {
            let hf_param_kinds: Vec<Option<ast_defs::ParamKind>> = hf_param_info
                .iter()
                .map(|i| {
                    i.as_ref().and_then(|i| match &i.kind {
                        ast_defs::ParamKind::Pnormal => None,
                        ast_defs::ParamKind::Pinout(p) => {
                            Some(ast_defs::ParamKind::Pinout(p.clone()))
                        }
                    })
                })
                .collect();
            let pp_typed_param =
                |ppf: &mut Formatter, kp: &(Option<ast_defs::ParamKind>, &aast::Hint)| {
                    fmt::pair(
                        Some(&fmt::nop),
                        |ppf, k: Option<&ast_defs::ParamKind>| {
                            fmt::option(
                                None,
                                |ppf, k| fmt::suffix(fmt::sp, pp_paramkind, ppf, k),
                                ppf,
                                k,
                            )
                        },
                        pp_hint_no_ctx,
                        ppf,
                        (kp.0.as_ref(), kp.1),
                    )
                };
            let pp_fun_params = |ppf: &mut Formatter,
                                 (ps, v, nv): (
                &[(Option<ast_defs::ParamKind>, &aast::Hint)],
                Option<&aast::Hint>,
                Option<&aast::Hint>,
            )| {
                fmt::string(ppf, "(");
                fmt::list(Some(&fmt::comma), pp_typed_param, ppf, ps);
                match v {
                    None => (),
                    Some(h) => {
                        if !ps.is_empty() {
                            fmt::string(ppf, ", ")
                        }
                        pp_hint(false, ppf, h);
                        fmt::string(ppf, "...")
                    }
                }
                match nv {
                    None => (),
                    Some(h) => {
                        if !ps.is_empty() || v.is_some() {
                            fmt::string(ppf, ", ")
                        }
                        fmt::string(ppf, "named ");
                        pp_hint(false, ppf, h);
                        fmt::string(ppf, "...")
                    }
                }
                fmt::string(ppf, ")")
            };
            let all_params = (
                zip_exn(hf_param_kinds, hf_param_tys.iter().collect()),
                hf_variadic_ty.as_ref(),
                hf_named_variadic_ty.as_ref(),
            );
            type AllParams<'a> = (
                Vec<(Option<ast_defs::ParamKind>, &'a aast::Hint)>,
                Option<&'a aast::Hint>,
                Option<&'a aast::Hint>,
            );
            fmt::parens(
                |ppf, x: ((&AllParams<'_>, Option<&aast::Contexts>), &aast::Hint)| {
                    fmt::pair(
                        Some(&fmt::colon),
                        |ppf, y: (&AllParams<'_>, Option<&aast::Contexts>)| {
                            fmt::prefix(
                                const_string("function"),
                                |ppf, y: (&AllParams<'_>, Option<&aast::Contexts>)| {
                                    fmt::pair(
                                        Some(&fmt::nop),
                                        |ppf, (ps, v, nv): &AllParams<'_>| {
                                            pp_fun_params(ppf, (ps.as_slice(), *v, *nv))
                                        },
                                        |ppf, c| fmt::option(None, pp_contexts, ppf, c),
                                        ppf,
                                        y,
                                    )
                                },
                                ppf,
                                y,
                            )
                        },
                        pp_hint_no_ctx,
                        ppf,
                        x,
                    )
                },
                ppf,
                ((&all_params, hf_ctxs.as_ref()), hf_return_ty),
            )
        }
        Hint_::Hshape(aast::NastShapeInfo {
            allows_unknown_fields: nsi_allows_unknown_fields,
            field_map: nsi_field_map,
            unknown_fields_type: nsi_unknown_fields_type,
        }) if nsi_field_map.is_empty() => {
            let pp_ellipsis = |ppf: &mut Formatter, ()| match nsi_unknown_fields_type {
                Some(h) => {
                    pp_hint(false, ppf, h);
                    fmt::string(ppf, "...")
                }
                None => {
                    if *nsi_allows_unknown_fields {
                        fmt::string(ppf, "...")
                    }
                }
            };
            fmt::prefix(
                const_string("shape"),
                |ppf, ()| fmt::parens(pp_ellipsis, ppf, ()),
                ppf,
                (),
            )
        }
        Hint_::Hshape(aast::NastShapeInfo {
            allows_unknown_fields: nsi_allows_unknown_fields,
            field_map: nsi_field_map,
            unknown_fields_type: nsi_unknown_fields_type,
        }) => {
            let pp_ellipsis = |ppf: &mut Formatter, ()| match nsi_unknown_fields_type {
                Some(h) => {
                    fmt::string(ppf, ", ");
                    pp_hint(false, ppf, h);
                    fmt::string(ppf, "...")
                }
                None => {
                    if *nsi_allows_unknown_fields {
                        fmt::string(ppf, ", ...")
                    }
                }
            };
            fmt::prefix(
                const_string("shape"),
                |ppf, x: (&[aast::ShapeElement], ())| {
                    fmt::parens(
                        |ppf, x| {
                            fmt::pair(
                                Some(&fmt::nop),
                                |ppf, fields: &[aast::ShapeElement]| {
                                    fmt::list(Some(&fmt::comma), pp_shape_element, ppf, fields)
                                },
                                pp_ellipsis,
                                ppf,
                                x,
                            )
                        },
                        ppf,
                        x,
                    )
                },
                ppf,
                (nsi_field_map.as_slice(), ()),
            )
        }
    }
}

fn pp_shape_element(ppf: &mut Formatter, element: &aast::ShapeElement) {
    match element {
        aast::ShapeElement::SEField(sfi) => pp_shape_field(ppf, sfi),
        aast::ShapeElement::SESplat(h) => {
            fmt::prefix(const_string("..."), pp_hint_no_ctx, ppf, h)
        }
    }
}

fn pp_shape_field(ppf: &mut Formatter, sfi: &aast::ShapeFieldInfo) {
    let aast::ShapeFieldInfo {
        optional: sfi_optional,
        name: sfi_name,
        hint: sfi_hint,
    } = sfi;
    fmt::pair(
        Some(&fmt::fat_arrow),
        |ppf, x: (bool, &ast_defs::ShapeFieldName)| {
            fmt::pair(
                Some(&fmt::nop),
                |ppf, test| fmt::cond(const_string("?"), fmt::nop, ppf, test),
                pp_shape_field_name,
                ppf,
                x,
            )
        },
        pp_hint_no_ctx,
        ppf,
        ((*sfi_optional, sfi_name), sfi_hint),
    )
}

fn pp_shape_field_name(ppf: &mut Formatter, name: &ast_defs::ShapeFieldName) {
    match name {
        ast_defs::ShapeFieldName::SFlitStr((_, s)) => {
            fmt::quote(fmt::string, ppf, &String::from_utf8_lossy(s))
        }
        ast_defs::ShapeFieldName::SFclassname(ast_defs::Id(_, s)) => {
            fmt::prefix(const_string("nameof"), fmt::string, ppf, s.as_str())
        }
        ast_defs::ShapeFieldName::SFclassConst(ast_defs::Id(_, c), (_, s)) => fmt::pair(
            Some(&fmt::dbl_colon),
            fmt::string,
            fmt::string,
            ppf,
            (c.as_str(), s.as_str()),
        ),
    }
}

fn pp_contexts(ppf: &mut Formatter, aast::Contexts(_, ctxts): &aast::Contexts) {
    fmt::brackets(
        |ppf, ctxts: &[aast::Hint]| {
            fmt::list(Some(&fmt::comma), |ppf, h| pp_hint(true, ppf, h), ppf, ctxts)
        },
        ppf,
        ctxts.as_slice(),
    )
}

fn pp_binop(ppf: &mut Formatter, bop: &ast_defs::Bop) {
    use ast_defs::Bop;
    match bop {
        Bop::Plus => fmt::string(ppf, "+"),
        Bop::Minus => fmt::string(ppf, "-"),
        Bop::Star => fmt::string(ppf, "*"),
        Bop::Slash => fmt::string(ppf, "/"),
        Bop::Eqeq => fmt::string(ppf, "=="),
        Bop::Eqeqeq => fmt::string(ppf, "==="),
        Bop::Starstar => fmt::string(ppf, "**"),
        Bop::Diff => fmt::string(ppf, "diff"),
        Bop::Diff2 => fmt::string(ppf, "diff2"),
        Bop::Ampamp => fmt::string(ppf, "&&"),
        Bop::Barbar => fmt::string(ppf, "||"),
        Bop::Lt => fmt::string(ppf, "<"),
        Bop::Lte => fmt::string(ppf, "<="),
        Bop::Gt => fmt::string(ppf, ">"),
        Bop::Gte => fmt::string(ppf, ">="),
        Bop::Dot => fmt::string(ppf, "."),
        Bop::Amp => fmt::string(ppf, "&"),
        Bop::Bar => fmt::string(ppf, "|"),
        Bop::Ltlt => fmt::string(ppf, "<<"),
        Bop::Gtgt => fmt::string(ppf, ">>"),
        Bop::Percent => fmt::string(ppf, "%"),
        Bop::Xor => fmt::string(ppf, "^"),
        Bop::Cmp => fmt::string(ppf, "<=>"),
        Bop::QuestionQuestion => fmt::string(ppf, "??"),
    }
}

fn pp_assign(ppf: &mut Formatter, op: Option<&ast_defs::Bop>) {
    match op {
        Some(op) => fmt::suffix(const_string("="), pp_binop, ppf, op),
        None => fmt::string(ppf, "="),
    }
}

fn pp_unop(ppf: &mut Formatter, op: &ast_defs::Uop) {
    use ast_defs::Uop;
    match op {
        Uop::Utild => fmt::string(ppf, "~"),
        Uop::Unot => fmt::string(ppf, "!"),
        Uop::Uplus => fmt::string(ppf, "+"),
        Uop::Uminus => fmt::string(ppf, "-"),
        Uop::Uincr | Uop::Upincr => fmt::string(ppf, "++"),
        Uop::Udecr | Uop::Updecr => fmt::string(ppf, "--"),
        Uop::Usilence => fmt::string(ppf, "@"),
    }
}

fn is_postfix_unop(op: &ast_defs::Uop) -> bool {
    match op {
        ast_defs::Uop::Updecr | ast_defs::Uop::Upincr => true,
        _ => false,
    }
}

fn pp_targ<Ex>(ppf: &mut Formatter, aast::Targ(_, hint): &aast::Targ<Ex>) {
    pp_hint(false, ppf, hint)
}

fn pp_targs<Ex>(ppf: &mut Formatter, targs: &[aast::Targ<Ex>]) {
    match targs {
        [] => (),
        targs => fmt::angles(
            |ppf, targs: &[aast::Targ<Ex>]| fmt::list(Some(&fmt::comma), pp_targ, ppf, targs),
            ppf,
            targs,
        ),
    }
}

fn pp_vc_kind(ppf: &mut Formatter, kind: &aast_defs::VcKind) {
    use aast_defs::VcKind;
    match kind {
        VcKind::Vector => fmt::string(ppf, "Vector"),
        VcKind::ImmVector => fmt::string(ppf, "ImmVector"),
        VcKind::Vec => fmt::string(ppf, "vec"),
        VcKind::Set => fmt::string(ppf, "Set"),
        VcKind::ImmSet => fmt::string(ppf, "ImmSet"),
        VcKind::Keyset => fmt::string(ppf, "keyset"),
    }
}

fn pp_kvc_kind(ppf: &mut Formatter, kind: &aast_defs::KvcKind) {
    use aast_defs::KvcKind;
    match kind {
        KvcKind::Dict => fmt::string(ppf, "dict"),
        KvcKind::Map => fmt::string(ppf, "Map"),
        KvcKind::ImmMap => fmt::string(ppf, "ImmMap"),
    }
}

fn pp_lid(ppf: &mut Formatter, lid: &crate::local_id::T) {
    fmt::prefix(
        const_string("$"),
        fmt::string,
        ppf,
        crate::local_id::get_name(lid).as_str(),
    )
}

/// `delim @@ pp_v`, for the delimiters of collections (`Fmt.brackets` or
/// `Fmt.braces`).
type Delim<'a, A> = &'a dyn Fn(&dyn Fn(&mut Formatter, A), &mut Formatter, A);

fn pp_expr<Ex, En>(ppf: &mut Formatter, aast::Expr(_, _, expr_): &aast::Expr<Ex, En>) {
    pp_expr_(ppf, expr_)
}

fn pp_expr_<Ex, En>(ppf: &mut Formatter, expr_: &aast::Expr_<Ex, En>) {
    use aast::Expr_;
    match expr_ {
        Expr_::Shape(flds) => {
            let pp_shape_expr_field =
                |ppf: &mut Formatter, field: &aast::ShapeExprField<Ex, En>| match field {
                    aast::ShapeExprField::SFField(name, expr) => fmt::pair(
                        Some(&fmt::fat_arrow),
                        pp_shape_field_name,
                        pp_expr,
                        ppf,
                        (name, expr),
                    ),
                    aast::ShapeExprField::SFSplat(expr) => {
                        fmt::prefix(const_string("..."), pp_expr, ppf, expr)
                    }
                };
            fmt::prefix(
                const_string("shape"),
                |ppf, flds: &[aast::ShapeExprField<Ex, En>]| {
                    fmt::parens(
                        |ppf, flds: &[aast::ShapeExprField<Ex, En>]| {
                            fmt::list(Some(&fmt::comma), &pp_shape_expr_field, ppf, flds)
                        },
                        ppf,
                        flds,
                    )
                },
                ppf,
                flds.as_slice(),
            )
        }
        Expr_::ValCollection(b) => {
            let ((_, kind), targ_opt, exprs) = &**b;
            let delim: Delim<'_, &[aast::Expr<Ex, En>]> = match kind {
                aast_defs::VcKind::Keyset | aast_defs::VcKind::Vec => {
                    &|pp_v, ppf, v| fmt::brackets(pp_v, ppf, v)
                }
                _ => &|pp_v, ppf, v| fmt::braces(pp_v, ppf, v),
            };
            fmt::pair(
                Some(&fmt::nop),
                pp_vc_kind,
                |ppf, x: (Option<&aast::Targ<Ex>>, &[aast::Expr<Ex, En>])| {
                    fmt::pair(
                        Some(&fmt::nop),
                        |ppf, t| fmt::option(None, |ppf, t| fmt::angles(pp_targ, ppf, t), ppf, t),
                        |ppf, exprs| {
                            delim(
                                &|ppf, exprs| fmt::list(Some(&fmt::comma), pp_expr, ppf, exprs),
                                ppf,
                                exprs,
                            )
                        },
                        ppf,
                        x,
                    )
                },
                ppf,
                (kind, (targ_opt.as_ref(), exprs.as_slice())),
            )
        }
        Expr_::KeyValCollection(b) => {
            let ((_, kind), targs_opt, flds) = &**b;
            let delim: Delim<'_, &[aast::Field<Ex, En>]> = match kind {
                aast_defs::KvcKind::Dict => &|pp_v, ppf, v| fmt::brackets(pp_v, ppf, v),
                _ => &|pp_v, ppf, v| fmt::braces(pp_v, ppf, v),
            };
            fmt::pair(
                Some(&fmt::nop),
                pp_kvc_kind,
                |ppf, x: (Option<&(aast::Targ<Ex>, aast::Targ<Ex>)>, &[aast::Field<Ex, En>])| {
                    fmt::pair(
                        Some(&fmt::nop),
                        |ppf, t: Option<&(aast::Targ<Ex>, aast::Targ<Ex>)>| {
                            fmt::option(
                                None,
                                |ppf, (k, v): &(aast::Targ<Ex>, aast::Targ<Ex>)| {
                                    fmt::angles(
                                        |ppf, kv| {
                                            fmt::pair(Some(&fmt::comma), pp_targ, pp_targ, ppf, kv)
                                        },
                                        ppf,
                                        (k, v),
                                    )
                                },
                                ppf,
                                t,
                            )
                        },
                        |ppf, flds| {
                            delim(
                                &|ppf, flds| {
                                    fmt::list(
                                        Some(&fmt::comma),
                                        |ppf, aast::Field(k, v): &aast::Field<Ex, En>| {
                                            fmt::pair(
                                                Some(&fmt::fat_arrow),
                                                pp_expr,
                                                pp_expr,
                                                ppf,
                                                (k, v),
                                            )
                                        },
                                        ppf,
                                        flds,
                                    )
                                },
                                ppf,
                                flds,
                            )
                        },
                        ppf,
                        x,
                    )
                },
                ppf,
                (kind, (targs_opt.as_ref(), flds.as_slice())),
            )
        }
        Expr_::Null => fmt::string(ppf, "null"),
        Expr_::This => fmt::string(ppf, "this"),
        Expr_::True => fmt::string(ppf, "true"),
        Expr_::False => fmt::string(ppf, "false"),
        Expr_::Id(id) => fmt::string(ppf, &id.1),
        Expr_::Lvar(lid) => pp_lid(ppf, &lid.1),
        Expr_::Dollardollar(_) => fmt::string(ppf, "$$"),
        Expr_::Clone(expr) => fmt::prefix(const_string("clone"), pp_expr, ppf, &**expr),
        Expr_::ArrayGet(b) => {
            let (arr_expr, idx_expr_opt) = &**b;
            fmt::pair(
                Some(&fmt::nop),
                pp_expr,
                |ppf, idx| fmt::brackets(|ppf, idx| fmt::option(None, pp_expr, ppf, idx), ppf, idx),
                ppf,
                (arr_expr, idx_expr_opt.as_ref()),
            )
        }
        Expr_::ObjGet(b)
            if matches!(
                &**b,
                (_, _, aast_defs::OperatorNullFlavor::Nullsafe, aast_defs::PropOrMethod::IsMethod)
            ) =>
        {
            let (obj_expr, get_expr, _, _) = &**b;
            fmt::pair(
                Some(&fmt::arrow),
                |ppf, e| fmt::suffix(const_string("?"), pp_expr, ppf, e),
                pp_expr,
                ppf,
                (obj_expr, get_expr),
            )
        }
        Expr_::ObjGet(b) if matches!(&**b, (_, _, aast_defs::OperatorNullFlavor::Nullsafe, _)) => {
            let (obj_expr, get_expr, _, _) = &**b;
            fmt::parens(
                |ppf, x| {
                    fmt::pair(
                        Some(&fmt::arrow),
                        |ppf, e| fmt::suffix(const_string("?"), pp_expr, ppf, e),
                        pp_expr,
                        ppf,
                        x,
                    )
                },
                ppf,
                (obj_expr, get_expr),
            )
        }
        Expr_::ObjGet(b) if matches!(&**b, (_, _, _, aast_defs::PropOrMethod::IsMethod)) => {
            let (obj_expr, get_expr, _, _) = &**b;
            fmt::pair(Some(&fmt::arrow), pp_expr, pp_expr, ppf, (obj_expr, get_expr))
        }
        Expr_::ObjGet(b) => {
            let (obj_expr, get_expr, _, _) = &**b;
            fmt::parens(
                |ppf, x| fmt::pair(Some(&fmt::arrow), pp_expr, pp_expr, ppf, x),
                ppf,
                (obj_expr, get_expr),
            )
        }
        Expr_::ClassGet(b) if matches!(&**b, (_, _, aast_defs::PropOrMethod::IsMethod)) => {
            let (class_id, (_, cname), _) = &**b;
            fmt::pair(
                Some(&fmt::dbl_colon),
                pp_class_id,
                fmt::string,
                ppf,
                (class_id, cname.as_str()),
            )
        }
        Expr_::ClassGet(b) => {
            let (class_id, (_, cname), _) = &**b;
            fmt::parens(
                |ppf, x| fmt::pair(Some(&fmt::dbl_colon), pp_class_id, fmt::string, ppf, x),
                ppf,
                (class_id, cname.as_str()),
            )
        }
        Expr_::ClassConst(b) => {
            let (class_id, (_, cname)) = &**b;
            fmt::pair(
                Some(&fmt::dbl_colon),
                pp_class_id,
                fmt::string,
                ppf,
                (class_id, cname.as_str()),
            )
        }
        Expr_::Call(b) => {
            let aast::CallExpr {
                func,
                targs,
                args,
                unpacked_arg,
            } = &**b;
            fmt::pair(
                Some(&fmt::nop),
                pp_expr,
                |ppf, x| fmt::pair(Some(&fmt::nop), pp_targs, pp_arg_exprs, ppf, x),
                ppf,
                (func, (targs.as_slice(), (args.as_slice(), unpacked_arg.as_ref()))),
            )
        }
        Expr_::FunctionPointer(b) => {
            let (id, targs, _) = &**b;
            fmt::pair(
                Some(&fmt::nop),
                pp_function_ptr_id,
                |ppf, targs: &[aast::Targ<Ex>]| {
                    fmt::angles(
                        |ppf, targs: &[aast::Targ<Ex>]| {
                            fmt::list(Some(&fmt::comma), pp_targ, ppf, targs)
                        },
                        ppf,
                        targs,
                    )
                },
                ppf,
                (id, targs.as_slice()),
            )
        }
        Expr_::Int(str) | Expr_::Float(str) => fmt::string(ppf, str),
        Expr_::String(str) => fmt::quote(
            fmt::string,
            ppf,
            &String::from_utf8_lossy(str).replace('\'', "\\'"),
        ),
        Expr_::String2(exprs) => fmt::quote(
            |ppf, exprs: &[aast::Expr<Ex, En>]| fmt::list(Some(&fmt::sp), pp_expr, ppf, exprs),
            ppf,
            exprs.as_slice(),
        ),
        Expr_::PrefixedString(b) => {
            let (pfx, expr) = &**b;
            fmt::pair(
                Some(&fmt::nop),
                fmt::string,
                |ppf, e| fmt::quote(pp_expr, ppf, e),
                ppf,
                (pfx.as_str(), expr),
            )
        }
        Expr_::Yield(afield) => fmt::prefix(const_string("yield"), pp_afield, ppf, &**afield),
        Expr_::Await(expr) => fmt::prefix(const_string("await"), pp_expr, ppf, &**expr),
        Expr_::Delay(expr) => fmt::prefix(const_string("delay"), pp_expr, ppf, &**expr),
        Expr_::ReadonlyExpr(expr) => fmt::prefix(const_string("readonly"), pp_expr, ppf, &**expr),
        Expr_::List(exprs) => fmt::prefix(
            const_string("list"),
            |ppf, exprs: &[aast::Expr<Ex, En>]| {
                fmt::parens(
                    |ppf, exprs: &[aast::Expr<Ex, En>]| {
                        fmt::list(Some(&fmt::comma), pp_expr, ppf, exprs)
                    },
                    ppf,
                    exprs,
                )
            },
            ppf,
            exprs.as_slice(),
        ),
        Expr_::Tuple(exprs) => fmt::prefix(
            const_string("tuple"),
            |ppf, exprs: &[aast::Expr<Ex, En>]| {
                fmt::parens(
                    |ppf, exprs: &[aast::Expr<Ex, En>]| {
                        fmt::list(Some(&fmt::comma), pp_expr, ppf, exprs)
                    },
                    ppf,
                    exprs,
                )
            },
            ppf,
            exprs.as_slice(),
        ),
        Expr_::Cast(b) => {
            let (hint, expr) = &**b;
            fmt::pair(
                Some(&fmt::nop),
                |ppf, h| fmt::parens(pp_hint_no_ctx, ppf, h),
                pp_expr,
                ppf,
                (hint, expr),
            )
        }
        Expr_::Unop(b) if is_postfix_unop(&b.0) => {
            let (unop, expr) = &**b;
            fmt::pair(Some(&fmt::nop), pp_expr, pp_unop, ppf, (expr, unop))
        }
        Expr_::Unop(b) => {
            let (unop, expr) = &**b;
            fmt::pair(Some(&fmt::nop), pp_unop, pp_expr, ppf, (unop, expr))
        }
        Expr_::Binop(b) => {
            let aast::Binop { bop, lhs, rhs } = &**b;
            fmt::pair(
                Some(&fmt::sp),
                pp_expr,
                |ppf, x| fmt::pair(Some(&fmt::sp), pp_binop, pp_expr, ppf, x),
                ppf,
                (lhs, (bop, rhs)),
            )
        }
        Expr_::Assign(b) => {
            let (lhs, bop, rhs) = &**b;
            fmt::pair(
                Some(&fmt::sp),
                pp_expr,
                |ppf, x| fmt::pair(Some(&fmt::sp), pp_assign, pp_expr, ppf, x),
                ppf,
                (lhs, (bop.as_ref(), rhs)),
            )
        }
        Expr_::Pipe(b) => {
            let (_lid, e1, e2, null_flavor) = &**b;
            let is_nullsafe = match null_flavor {
                aast_defs::OperatorNullFlavor::Nullsafe => true,
                _ => false,
            };
            fmt::pair(
                Some(&const_string(if is_nullsafe { " |?> " } else { " |> " })),
                pp_expr,
                pp_expr,
                ppf,
                (e1, e2),
            )
        }
        Expr_::Eif(b) if b.1.is_some() => {
            let (cond, texpr, fexpr) = &**b;
            let texpr = texpr.as_ref().unwrap();
            fmt::pair(
                Some(&const_string(" ? ")),
                pp_expr,
                |ppf, x| fmt::pair(Some(&fmt::colon), pp_expr, pp_expr, ppf, x),
                ppf,
                (cond, (texpr, fexpr)),
            )
        }
        Expr_::Eif(b) => {
            let (cond, _, expr) = &**b;
            fmt::pair(Some(&const_string(" ?: ")), pp_expr, pp_expr, ppf, (cond, expr))
        }
        Expr_::Is(b) => {
            let (expr, hint) = &**b;
            fmt::pair(
                Some(&const_string(" is ")),
                pp_expr,
                pp_hint_no_ctx,
                ppf,
                (expr, hint),
            )
        }
        Expr_::As(b) if !b.is_nullable => {
            let aast::As_ {
                expr,
                hint,
                is_nullable: _,
                enforce_deep: _,
            } = &**b;
            fmt::pair(
                Some(&const_string(" as ")),
                pp_expr,
                pp_hint_no_ctx,
                ppf,
                (expr, hint),
            )
        }
        Expr_::As(b) => {
            let aast::As_ {
                expr,
                hint,
                is_nullable: _,
                enforce_deep: _,
            } = &**b;
            fmt::pair(
                Some(&const_string(" ?as ")),
                pp_expr,
                pp_hint_no_ctx,
                ppf,
                (expr, hint),
            )
        }
        Expr_::Upcast(b) => {
            let (expr, hint) = &**b;
            fmt::pair(
                Some(&const_string(" upcast ")),
                pp_expr,
                pp_hint_no_ctx,
                ppf,
                (expr, hint),
            )
        }
        Expr_::New(b) => {
            let (class_id, targs, exprs, expr_opt, _) = &**b;
            fmt::prefix(
                const_string("new"),
                |ppf, x| {
                    fmt::pair(
                        Some(&fmt::nop),
                        pp_class_id,
                        |ppf, x| fmt::pair(Some(&fmt::nop), pp_targs, pp_arg_exprs, ppf, x),
                        ppf,
                        x,
                    )
                },
                ppf,
                (class_id, (targs.as_slice(), (exprs.as_slice(), expr_opt.as_ref()))),
            )
        }
        Expr_::Lplaceholder(_) => fmt::string(ppf, "$_"),
        Expr_::Pair(b) => {
            let (targs_opt, fst, snd) = &**b;
            fmt::prefix(
                const_string("Pair"),
                |ppf, x: (Option<&(aast::Targ<Ex>, aast::Targ<Ex>)>, (&aast::Expr<Ex, En>, &aast::Expr<Ex, En>))| {
                    fmt::pair(
                        Some(&fmt::nop),
                        |ppf, t: Option<&(aast::Targ<Ex>, aast::Targ<Ex>)>| {
                            fmt::option(
                                None,
                                |ppf, (k, v): &(aast::Targ<Ex>, aast::Targ<Ex>)| {
                                    fmt::angles(
                                        |ppf, kv| {
                                            fmt::pair(Some(&fmt::comma), pp_targ, pp_targ, ppf, kv)
                                        },
                                        ppf,
                                        (k, v),
                                    )
                                },
                                ppf,
                                t,
                            )
                        },
                        |ppf, x| {
                            fmt::braces(
                                |ppf, x| fmt::pair(Some(&fmt::comma), pp_expr, pp_expr, ppf, x),
                                ppf,
                                x,
                            )
                        },
                        ppf,
                        x,
                    )
                },
                ppf,
                (targs_opt.as_ref(), (fst, snd)),
            )
        }
        Expr_::Hole(b) => pp_expr(ppf, &b.0),
        Expr_::EnumClassLabel(b) => {
            let (opt_sid, name) = &**b;
            match opt_sid {
                None => fmt::prefix(fmt::dbl_hash, fmt::string, ppf, name.as_str()),
                Some(ast_defs::Id(_, class_name)) => fmt::pair(
                    Some(&fmt::dbl_hash),
                    fmt::string,
                    fmt::string,
                    ppf,
                    (class_name.as_str(), name.as_str()),
                ),
            }
        }
        Expr_::Invalid(b) if b.is_some() => pp_expr(ppf, b.as_ref().as_ref().unwrap()),
        Expr_::Package(id) => fmt::string(ppf, &id.1),
        Expr_::Nameof(cid) => fmt::prefix(const_string("nameof"), pp_class_id, ppf, &**cid),
        Expr_::Invalid(_)
        | Expr_::Efun(_)
        | Expr_::Lfun(_)
        | Expr_::Xml(_)
        | Expr_::Import(_)
        | Expr_::Collection(_)
        | Expr_::ExpressionTree(_)
        | Expr_::MethodCaller(_)
        | Expr_::ETSplice(_)
        | Expr_::DestructureShape(_)
        | Expr_::DestructureTuple(_)
        | Expr_::Omitted => (),
    }
}

fn pp_arg_exprs<Ex, En>(
    ppf: &mut Formatter,
    (exprs, expr_opt): (&[aast::Argument<Ex, En>], Option<&aast::Expr<Ex, En>>),
) {
    match exprs {
        [] => fmt::parens(
            |ppf, e| {
                fmt::option(
                    None,
                    |ppf, e| fmt::prefix(const_string("..."), pp_expr, ppf, e),
                    ppf,
                    e,
                )
            },
            ppf,
            expr_opt,
        ),
        _ => fmt::parens(
            |ppf, x| {
                fmt::pair(
                    Some(&fmt::comma),
                    |ppf, exprs: &[aast::Argument<Ex, En>]| {
                        fmt::list(Some(&fmt::comma), pp_arg, ppf, exprs)
                    },
                    |ppf, e| {
                        fmt::option(
                            None,
                            |ppf, e| fmt::prefix(const_string("..."), pp_expr, ppf, e),
                            ppf,
                            e,
                        )
                    },
                    ppf,
                    x,
                )
            },
            ppf,
            (exprs, expr_opt),
        ),
    }
}

fn pp_arg<Ex, En>(ppf: &mut Formatter, arg: &aast::Argument<Ex, En>) {
    match arg {
        aast_defs::Argument::Anormal(e) => pp_expr(ppf, e),
        aast_defs::Argument::Ainout(pos, e) => fmt::pair(
            Some(&fmt::sp),
            pp_paramkind,
            pp_expr,
            ppf,
            (&ast_defs::ParamKind::Pinout(pos.clone()), e),
        ),
        aast_defs::Argument::Anamed(ast_defs::Id(_, name), e) => {
            fmt::pair(Some(&fmt::equal_to), fmt::string, pp_expr, ppf, (name.as_str(), e))
        }
    }
}

fn pp_afield<Ex, En>(ppf: &mut Formatter, afield: &aast::Afield<Ex, En>) {
    match afield {
        aast::Afield::AFvalue(expr) => pp_expr(ppf, expr),
        aast::Afield::AFkvalue(key_expr, val_expr) => fmt::pair(
            Some(&fmt::fat_arrow),
            pp_expr,
            pp_expr,
            ppf,
            (key_expr, val_expr),
        ),
    }
}

fn pp_class_id<Ex, En>(ppf: &mut Formatter, aast::ClassId(_, _, class_id_): &aast::ClassId<Ex, En>) {
    match class_id_ {
        aast::ClassId_::CIparent => fmt::string(ppf, "parent"),
        aast::ClassId_::CIstatic => fmt::string(ppf, "static"),
        aast::ClassId_::CIself => fmt::string(ppf, "self"),
        aast::ClassId_::CI(ast_defs::Id(_, name)) => fmt::string(ppf, name),
        aast::ClassId_::CIreified(ast_defs::Id(_, name)) => fmt::string(ppf, name),
        aast::ClassId_::CIexpr(expr) => pp_expr(ppf, expr),
    }
}

fn pp_function_ptr_id<Ex, En>(ppf: &mut Formatter, id: &aast::FunctionPtrId<Ex, En>) {
    match id {
        aast::FunctionPtrId::FPId(ast_defs::Id(_, name)) => fmt::string(ppf, name),
        aast::FunctionPtrId::FPClassConst(class_id, (_, str)) => fmt::pair(
            Some(&fmt::dbl_colon),
            pp_class_id,
            fmt::string,
            ppf,
            (class_id, str.as_str()),
        ),
    }
}

fn pp_user_attr<Ex, En>(ppf: &mut Formatter, ua: &aast::UserAttribute<Ex, En>) {
    let aast::UserAttribute {
        name: ast_defs::Id(_, nm),
        params: ua_params,
        ..
    } = ua;
    match ua_params.as_slice() {
        [] => fmt::string(ppf, nm),
        _ => fmt::pair(
            Some(&fmt::nop),
            fmt::string,
            |ppf, params: &[aast::Expr<Ex, En>]| {
                fmt::parens(
                    |ppf, params: &[aast::Expr<Ex, En>]| {
                        fmt::list(Some(&fmt::comma), pp_expr, ppf, params)
                    },
                    ppf,
                    params,
                )
            },
            ppf,
            (nm.as_str(), ua_params.as_slice()),
        ),
    }
}

pub fn pp_user_attrs<Ex, En>(ppf: &mut Formatter, attrs: &[aast::UserAttribute<Ex, En>]) {
    match attrs {
        [] => (),
        rs => fmt::angles(
            |ppf, rs: &[aast::UserAttribute<Ex, En>]| {
                fmt::angles(
                    |ppf, rs: &[aast::UserAttribute<Ex, En>]| {
                        fmt::list(Some(&fmt::comma), pp_user_attr, ppf, rs)
                    },
                    ppf,
                    rs,
                )
            },
            ppf,
            rs,
        ),
    }
}

fn pp_variance(ppf: &mut Formatter, variance: &ast_defs::Variance) {
    match variance {
        ast_defs::Variance::Covariant => fmt::string(ppf, "+"),
        ast_defs::Variance::Contravariant => fmt::string(ppf, "-"),
        ast_defs::Variance::Invariant => (),
    }
}

fn pp_constraint_kind(ppf: &mut Formatter, kind: &ast_defs::ConstraintKind) {
    match kind {
        ast_defs::ConstraintKind::ConstraintAs => fmt::string(ppf, "as"),
        ast_defs::ConstraintKind::ConstraintEq => fmt::string(ppf, "="),
        ast_defs::ConstraintKind::ConstraintSuper => fmt::string(ppf, "super"),
    }
}

fn pp_constraint(ppf: &mut Formatter, (kind, hint): &(ast_defs::ConstraintKind, aast::Hint)) {
    // Format.(fprintf ppf {|%a %a|}) pp_constraint_kind kind (pp_hint ~is_ctx:false) hint
    pp_constraint_kind(ppf, kind);
    format::pp_print_char(ppf, ' ');
    pp_hint(false, ppf, hint)
}

fn pp_tp_reified(ppf: &mut Formatter, reified: &aast::ReifyKind) {
    match reified {
        aast::ReifyKind::Erased => (),
        aast::ReifyKind::SoftReified | aast::ReifyKind::Reified => fmt::string(ppf, "reify"),
    }
}

pub fn pp_tparam<Ex, En>(ppf: &mut Formatter, tparam: &aast::Tparam<Ex, En>) {
    let aast::Tparam {
        variance: tp_variance,
        name: ast_defs::Id(_, name),
        constraints: tp_constraints,
        reified: tp_reified,
        user_attributes: tp_user_attributes,
    } = tparam;
    // Format.(fprintf ppf {|%a %a %a%s %a |} pp_user_attrs tp_user_attributes
    //   pp_tp_reified tp_reified pp_variance tp_variance name
    //   Fmt.(list ~sep:sp pp_constraint) tp_constraints)
    pp_user_attrs(ppf, &tp_user_attributes.0);
    format::pp_print_char(ppf, ' ');
    pp_tp_reified(ppf, tp_reified);
    format::pp_print_char(ppf, ' ');
    pp_variance(ppf, tp_variance);
    format::pp_print_string(ppf, name);
    format::pp_print_char(ppf, ' ');
    fmt::list(Some(&fmt::sp), pp_constraint, ppf, tp_constraints);
    format::pp_print_char(ppf, ' ')
}

pub fn pp_tparams<Ex, En>(ppf: &mut Formatter, ps: &[aast::Tparam<Ex, En>]) {
    let ps: Vec<&aast::Tparam<Ex, En>> = ps
        .iter()
        .filter(|tp| {
            let ast_defs::Id(_, name) = &tp.name;
            !sn::coeffects::is_generated_generic(name)
        })
        .collect();
    match ps.as_slice() {
        [] => (),
        ps => fmt::angles(
            |ppf, ps: &[&aast::Tparam<Ex, En>]| {
                fmt::list(
                    Some(&fmt::comma),
                    |ppf, tp: &&aast::Tparam<Ex, En>| pp_tparam(ppf, tp),
                    ppf,
                    ps,
                )
            },
            ppf,
            ps,
        ),
    }
}

pub fn pp_type_hint<Ex>(
    is_ret_type: bool,
    ppf: &mut Formatter,
    aast::TypeHint(_, hint): &aast::TypeHint<Ex>,
) {
    if is_ret_type {
        fmt::option(
            None,
            |ppf, h| fmt::prefix(const_string(": "), pp_hint_no_ctx, ppf, h),
            ppf,
            hint.as_ref(),
        )
    } else {
        fmt::option(
            None,
            |ppf, h| fmt::suffix(fmt::sp, pp_hint_no_ctx, ppf, h),
            ppf,
            hint.as_ref(),
        )
    }
}

#[cfg(test)]
mod tests {
    use oxidized::pos::Pos;

    use super::*;

    fn hint(h: aast::Hint_) -> aast::Hint {
        aast::Hint(Pos::NONE, Box::new(h))
    }

    fn apply(name: &str, args: Vec<aast::Hint>) -> aast::Hint {
        hint(aast::Hint_::Happly(
            ast_defs::Id(Pos::NONE, name.to_string()),
            args,
        ))
    }

    fn show(is_ctx: bool, h: &aast::Hint) -> String {
        fmt::to_to_string(|ppf, h| pp_hint(is_ctx, ppf, h), h)
    }

    // The expected outputs are those of the OCaml for the same calls (with
    // OCaml 5's `Format`): outside of a box, the last break hint breaks the
    // line (see the tests of `crate::format`).

    #[test]
    fn hints() {
        let int = hint(aast::Hint_::Hprim(aast_defs::Tprim::Tint));
        let string = apply("\\HH\\string", vec![]);
        assert_eq!(show(false, &int), "int");
        assert_eq!(show(false, &hint(aast::Hint_::Hoption(int.clone()))), "?int");
        assert_eq!(show(false, &hint(aast::Hint_::Hlike(int.clone()))), "~int");
        assert_eq!(
            show(false, &apply("\\C", vec![int.clone(), string.clone()])),
            "\\C<int,\n\\HH\\string>"
        );
        assert_eq!(
            show(false, &hint(aast::Hint_::Hunion(vec![int.clone(), string.clone()]))),
            "(int |\n\\HH\\string)"
        );
        assert_eq!(
            show(false, &hint(aast::Hint_::Hintersection(vec![int.clone(), int.clone()]))),
            "(int &\nint)"
        );
        // In contexts, namespaces are stripped and intersections are lists.
        let ctx = hint(aast::Hint_::Hintersection(vec![
            apply("\\HH\\Contexts\\write_props", vec![]),
            apply("\\HH\\Contexts\\defaults", vec![]),
        ]));
        assert_eq!(show(true, &ctx), "[write_props,\ndefaults]");
        assert_eq!(
            show(
                false,
                &hint(aast::Hint_::HvecOrDict(Some(int.clone()), string.clone()))
            ),
            "vec_or_dict<int,\n\\HH\\string>"
        );
        assert_eq!(
            show(false, &hint(aast::Hint_::HvecOrDict(None, int.clone()))),
            "vec_or_dict<int>"
        );
        assert_eq!(
            show(
                false,
                &hint(aast::Hint_::HclassPtr(aast::ClassPtrKind::CKclass, apply("\\C", vec![])))
            ),
            "class<\\C>"
        );
        assert_eq!(
            show(
                false,
                &hint(aast::Hint_::Haccess(
                    hint(aast::Hint_::Hthis),
                    vec![
                        ast_defs::Id(Pos::NONE, "T".to_string()),
                        ast_defs::Id(Pos::NONE, "U".to_string())
                    ]
                ))
            ),
            "this::T::U"
        );
        assert_eq!(
            show(false, &hint(aast::Hint_::HfunContext("$f".to_string()))),
            "ctx $f"
        );
    }

    #[test]
    fn shapes() {
        let int = hint(aast::Hint_::Hprim(aast_defs::Tprim::Tint));
        let shape = |allows_unknown_fields, field_map, unknown_fields_type| {
            hint(aast::Hint_::Hshape(aast::NastShapeInfo {
                allows_unknown_fields,
                field_map,
                unknown_fields_type,
            }))
        };
        assert_eq!(show(false, &shape(false, vec![], None)), "shape()");
        assert_eq!(show(false, &shape(true, vec![], None)), "shape(...)");
        let field = aast::ShapeElement::SEField(aast::ShapeFieldInfo {
            optional: true,
            hint: int.clone(),
            name: ast_defs::ShapeFieldName::SFlitStr((Pos::NONE, "a".into())),
        });
        assert_eq!(
            show(false, &shape(true, vec![field.clone()], None)),
            "shape(?'a' =>\nint, ...)"
        );
        assert_eq!(
            show(false, &shape(false, vec![field], Some(int))),
            "shape(?'a' =>\nint, int...)"
        );
    }

    #[test]
    fn functions() {
        let int = hint(aast::Hint_::Hprim(aast_defs::Tprim::Tint));
        let void = hint(aast::Hint_::Hprim(aast_defs::Tprim::Tvoid));
        let fun = |param_tys: Vec<aast::Hint>, param_info, variadic_ty| {
            hint(aast::Hint_::Hfun(aast::HintFun {
                is_readonly: None,
                tparams: vec![],
                param_tys,
                param_info,
                variadic_ty,
                named_variadic_ty: None,
                ctxs: None,
                return_ty: void.clone(),
                is_readonly_return: None,
            }))
        };
        assert_eq!(show(false, &fun(vec![], vec![], None)), "(function() :\nvoid)");
        let inout = Some(aast::HfParamInfo {
            kind: ast_defs::ParamKind::Pinout(Pos::NONE),
            readonlyness: None,
            optional: None,
            splat: None,
            named: None,
        });
        assert_eq!(
            show(
                false,
                &fun(vec![int.clone(), int.clone()], vec![None, inout], Some(int.clone()))
            ),
            "(function(int, inout int, int...) :\nvoid)"
        );
    }
}
