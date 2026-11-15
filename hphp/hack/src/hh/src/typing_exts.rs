// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_exts.ml`. See `hh/PORTING.md`.
//!
//! Ad-hoc rules for typing some common idioms
//!
//!   For printf-style functions: If the last argument (before varargs) of a
//!   function has the type FormatString<X>, we assume that the format
//!   string is interpreted by the formatter X, which should look like this:
//!
//!   interface PrintfFormatter {
//!     function format_0x25() : string;
//!     function format_x(int) : string;
//!     function format_f(float) : string;
//!     function format_upcase_l() : PrintfFormatter;
//!   }
//!
//!   Each method can return a string or another formatter (for
//!   multi-character sequences like %Ld); the parameters are copied into
//!   the function signature when instantiating it at the call site.
//!
//! The format string is a byte string (as OCaml strings and the string
//! literals of the AST are); the snippets and the format string that go into
//! reasons and errors (which hold `String`s) are converted with
//! `String::from_utf8_lossy`.

use bstr::BString;
use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::aast_utils;
use crate::decl_entry;
use crate::naming_special_names as sn;
use crate::naming_special_names::classes::C_STRING;
use crate::typing_defs::ClassElt;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs::is_dynamic;
use crate::typing_defs_core::DeclTy_;
use crate::typing_defs_core::FunParam;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_ft_variadic;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::map_reason;
use crate::typing_defs_flags;
use crate::typing_dynamic_utils;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_make_type as make_type;
use crate::typing_phase;
use crate::typing_print as print;
use crate::typing_reason as reason;

fn magic_method_name(input: Option<u8>) -> String {
    match input {
        None => "format_eof".to_string(),
        Some(c) => {
            // `Char.uppercase` and `Char.lowercase` (ASCII only)
            let uc = c.to_ascii_uppercase();
            let lc = c.to_ascii_lowercase();
            if lc == uc {
                format!("format_0x{:02x}", lc)
            } else if c == uc {
                format!("format_upcase_{}", lc as char)
            } else {
                format!("format_{}", lc as char)
            }
        }
    }
}

fn lookup_magic_type(
    env: &mut Env,
    use_pos: &Pos,
    class_: &Ty,
    fname: &str,
) -> Option<(Vec<FunParam>, Option<Ty>)> {
    let ty = typing_dynamic_utils::strip_dynamic(env, class_.clone());
    match get_node(&ty) {
        Ty_::Tclass(class_name, _, tyl) if tyl.is_empty() => {
            let class_name = &class_name.1;
            let lookup_def = |env: &Env, c: &crate::folded_class::T| -> Option<ClassElt> {
                // `Option.first_some a b`: the arguments, from the last to the first.
                let wild = env::get_method(env, c, "format_wild");
                let def = env::get_method(env, c, fname);
                def.or(wild)
            };
            let ce_type = match decl_entry::to_option(env::get_class(env, class_name)) {
                None => None,
                Some(c) => match lookup_def(env, &c) {
                    None => None,
                    Some(ce) => {
                        let ty = (*ce.ce_type).clone();
                        let pos = (*ce.ce_pos).clone();
                        match ty.node_ref() {
                            DeclTy_::Tfun(fty) => {
                                // Ugly hack to remove like-type from return syntactically so that in dynamic mode
                                // we don't simplify it to dynamic.
                                let mut fty = (**fty).clone();
                                fty.ret = match fty.ret.node_ref() {
                                    DeclTy_::Tlike(ty) => ty.clone(),
                                    _ => fty.ret.clone(),
                                };
                                let ety_env = empty_expand_env();
                                // Generate fresh type variables (and assert constraints, if any) for generic parameters on the format method
                                let (_ty_err_opt1, explicit_targs) = typing_phase::localize_targs(
                                    true,
                                    true,
                                    pos.clone(),
                                    use_pos.clone(),
                                    fname.to_string(),
                                    None,
                                    env,
                                    &fty.tparams,
                                    vec![],
                                );
                                let instantiation = typing_phase::MethodInstantiation {
                                    use_pos: use_pos.clone(),
                                    use_name: fname.to_string(),
                                    explicit_targs,
                                };
                                Some(typing_phase::localize_ft(
                                    Some(instantiation),
                                    &ety_env,
                                    pos,
                                    env,
                                    &fty,
                                ))
                            }
                            _ => None,
                        }
                    }
                },
            };
            match ce_type {
                Some((
                    ty_err_opt,
                    FunType {
                        params: pars,
                        ret: ty,
                        ..
                    },
                )) => {
                    if let Some(err) = &ty_err_opt {
                        typing_error_utils::add_typing_error(err, env)
                    }
                    let ty = env::expand_type(env, ty);
                    let ty_opt = match get_node(&ty) {
                        Ty_::Tclass(id, _, _) if id.1 == C_STRING => None,
                        Ty_::Tdynamic(_) => None,
                        _ => Some(ty),
                    };
                    Some((pars, ty_opt))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn get_char(s: &[u8], i: usize) -> Option<u8> {
    if i >= s.len() { None } else { Some(s[i]) }
}

/// `read_text env i` of `parse_printf_string`. `class_` is the argument of
/// `parse_printf_string`, which the OCaml closure captures (`read_modifier`
/// has a `class_` of its own).
fn read_text(env: &mut Env, s: &[u8], pos: &Pos, class_: &Ty, i: usize) -> Vec<FunParam> {
    // A loop for the tail calls of OCaml.
    let mut i = i;
    loop {
        match get_char(s, i) {
            Some(b'%') => return read_modifier(env, s, pos, class_, i + 1, class_, i),
            Some(_) => i += 1,
            None => return vec![],
        }
    }
}

/// `read_modifier env i class_ i0` of `parse_printf_string`. `root_class` is
/// the argument of `parse_printf_string` (the `class_` that `read_text`
/// sees).
fn read_modifier(
    env: &mut Env,
    s: &[u8],
    pos: &Pos,
    root_class: &Ty,
    i: usize,
    class_: &Ty,
    i0: usize,
) -> Vec<FunParam> {
    let fname = magic_method_name(get_char(s, i));
    let snippet = String::from_utf8_lossy(&s[i0..std::cmp::min(i + 1, s.len())]).into_owned();
    let add_reason = |params: Vec<FunParam>| -> Vec<FunParam> {
        params
            .into_iter()
            .map(|p| {
                let type_ = map_reason(p.type_.clone(), |r| {
                    reason::format((pos.clone(), snippet.clone(), r))
                });
                FunParam { type_, ..p }
            })
            .collect()
    };
    match lookup_magic_type(env, pos, class_, &fname) {
        Some((good_args, None)) => {
            let xs = read_text(env, s, pos, root_class, i + 1);
            let mut res = add_reason(good_args);
            res.extend(xs);
            res
        }
        Some((good_args, Some(next))) => {
            let xs = read_modifier(env, s, pos, root_class, i + 1, &next, i0);
            let mut res = add_reason(good_args);
            res.extend(xs);
            res
        }
        None => {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::FormatString {
                    pos: pos.clone(),
                    snippet: snippet.clone(),
                    fmt_string: String::from_utf8_lossy(s).into_owned(),
                    class_pos: get_pos(class_),
                    fn_name: fname,
                    class_suggest: print::full_strip_ns(true, env, class_),
                }),
                env,
            );
            let xs = read_text(env, s, pos, root_class, i + 1);
            add_reason(xs)
        }
    }
}

pub fn parse_printf_string(env: &mut Env, s: &[u8], pos: Pos, class_: Ty) -> Vec<FunParam> {
    read_text(env, s, &pos, &class_, 0)
}

/// `type ('a, 'b) either`
#[derive(Clone, Debug)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

/// `mapM f st xs`: `f` threads the state through the list, from left to
/// right.
pub fn map_m<S, X, Y>(mut f: impl FnMut(&mut S, &X) -> Y, st: &mut S, xs: &[X]) -> Vec<Y> {
    xs.iter().map(|x| f(st, x)).collect()
}

fn glue(x: Either<Pos, BString>, y: Either<Pos, BString>) -> Either<Pos, BString> {
    match (x, y) {
        (Either::Right(mut sx), Either::Right(sy)) => {
            sx.extend_from_slice(&sy);
            Either::Right(sx)
        }
        (Either::Left(p), _) => Either::Left(p),
        (_, Either::Left(p)) => Either::Left(p),
    }
}

/// If expr is a constant string, that string, otherwise a position
/// where it is obviously not
fn const_string_of(env: &mut Env, e: &nast::Expr) -> Either<Pos, BString> {
    match e {
        aast::Expr(_, _, aast::Expr_::String(s)) => Either::Right(s.clone()),
        // It's an invariant that this is going to fail, but look for the best
        // evidence
        aast::Expr(_, p, aast::Expr_::String2(xs)) => {
            let rev_xs: Vec<nast::Expr> = xs.iter().rev().cloned().collect();
            let xs = map_m(const_string_of, env, &rev_xs);
            // `List.fold_right ~f:glue xs ~init:(Left p)`
            xs.into_iter()
                .rev()
                .fold(Either::Left(p.clone()), |acc, x| glue(x, acc))
        }
        aast::Expr(_, _, aast::Expr_::Binop(binop)) if matches!(binop.bop, Bop::Dot) => {
            let aast::Binop { lhs, rhs, .. } = &**binop;
            let stra = const_string_of(env, lhs);
            let strb = const_string_of(env, rhs);
            glue(stra, strb)
        }
        aast::Expr(_, p, _) => Either::Left(p.clone()),
    }
}

fn get_format_string_type_arg(t: &Ty) -> Option<&Ty> {
    match get_node(t) {
        Ty_::Tnewtype(fs, tys, _) if tys.len() == 1 && sn::classes::is_format_string(fs) => {
            Some(&tys[0])
        }
        _ => None,
    }
}

fn get_possibly_like_format_string_type_arg(t: &Ty) -> Option<&Ty> {
    match get_node(t) {
        Ty_::Tunion(tyl) if tyl.len() == 2 && is_dynamic(&tyl[0]) => {
            get_possibly_like_format_string_type_arg(&tyl[1])
        }
        Ty_::Toption(t) => get_possibly_like_format_string_type_arg(t),
        _ => get_format_string_type_arg(t),
    }
}

/// `f env param_types args` of `retype_magic_func`.
fn retype_params(
    env: &mut Env,
    param_types: &[FunParam],
    args: &[&nast::Expr],
) -> Option<Vec<FunParam>> {
    match (param_types, args) {
        ([fp], [aast::Expr(_, _, aast::Expr_::Null)])
            if get_possibly_like_format_string_type_arg(&fp.type_).is_some() =>
        {
            None
        }
        ([fp], [arg, ..]) => match get_possibly_like_format_string_type_arg(&fp.type_) {
            Some(type_arg) => match const_string_of(env, arg) {
                Either::Right(str) => {
                    let aast::Expr(_, pos, _) = arg;
                    let argl = parse_printf_string(env, &str, pos.clone(), type_arg.clone());
                    let mut params = vec![FunParam {
                        type_: make_type::string(get_reason(&fp.type_).clone()),
                        ..fp.clone()
                    }];
                    params.extend(argl);
                    Some(params)
                }
                Either::Left(pos) => {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::ExpectedLiteralFormatString(pos)),
                        env,
                    );
                    None
                }
            },
            None => None,
        },
        ([param, params @ ..], [_, args @ ..]) => match retype_params(env, params, args) {
            None => None,
            Some(xs) => {
                let mut res = vec![param.clone()];
                res.extend(xs);
                Some(res)
            }
        },
        _ => None,
    }
}

/// Specialize a function type using whatever we can tell about the args
pub fn retype_magic_func(env: &mut Env, ft: FunType, el: &[nast::Argument]) -> FunType {
    let non_variadic_param_types: &[FunParam] = if get_ft_variadic(&ft) {
        match ft.params.split_last() {
            Some((_, init)) => init,
            None => panic!("List.drop_last_exn: empty list"),
        }
    } else {
        &ft.params
    };
    let args: Vec<&nast::Expr> = el.iter().map(aast_utils::arg_to_expr).collect();
    match retype_params(env, non_variadic_param_types, &args) {
        None => ft,
        Some(xs) => FunType {
            params: xs,
            flags: typing_defs_flags::fun::set_variadic(false, ft.flags),
            ..ft
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn magic_method_names() {
        assert_eq!(magic_method_name(None), "format_eof");
        assert_eq!(magic_method_name(Some(b'%')), "format_0x25");
        assert_eq!(magic_method_name(Some(b'd')), "format_d");
        assert_eq!(magic_method_name(Some(b'L')), "format_upcase_l");
        assert_eq!(magic_method_name(Some(0xe9)), "format_0xe9");
    }
}
