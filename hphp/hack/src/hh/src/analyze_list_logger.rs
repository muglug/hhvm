// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/analyze_list_logger.ml`. See `hh/PORTING.md`.
//!
//! TAST logger that records `list()` assignment patterns.

use std::collections::BTreeSet;
use std::io::Write;
use std::sync::LazyLock;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::pos::Pos;
use relative_path::RelativePath;

use crate::analyze_list_logger_types as types;
use crate::file_provider;
use crate::hh_logger;
use crate::pos;
use crate::provider_context;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_log;

pub static VEC_CLASSES: LazyLock<BTreeSet<String>> = LazyLock::new(|| {
    [
        sn::collections::VEC,
        sn::collections::VECTOR,
        sn::collections::IMM_VECTOR,
        sn::collections::CONST_VECTOR,
    ]
    .into_iter()
    .map(|s| s.to_string())
    .collect()
});

pub fn classify_type(env: &tast_env::Env, ty: &Ty) -> (types::Bucket, Ty) {
    let ty = tast_env::strip_dynamic(env, ty.clone());
    let (_, ty) = tast_env::strip_supportdyn(env, ty);
    match get_node(&ty) {
        Ty_::Ttuple(_) => (types::Bucket::Tuple, ty),
        Ty_::Tclass((_, name), _, _) => {
            if name == sn::collections::PAIR {
                (types::Bucket::Pair, ty)
            } else if VEC_CLASSES.contains(name) {
                (types::Bucket::Vec, ty)
            } else {
                (types::Bucket::Misc, ty)
            }
        }
        Ty_::Tunion(_) => (types::Bucket::Union, ty),
        Ty_::Tintersection(_) => (types::Bucket::Intersection, ty),
        Ty_::Tdynamic(_) => (types::Bucket::Dynamic, ty),
        Ty_::Tgeneric(_) => (types::Bucket::Generic, ty),
        _ => (types::Bucket::Misc, ty),
    }
}

pub fn ty_node_kind(ty: &Ty) -> String {
    match get_node(ty) {
        Ty_::Tany(_) => "Tany",
        Ty_::Tnonnull => "Tnonnull",
        Ty_::Tdynamic(_) => "Tdynamic",
        Ty_::Toption(_) => "Toption",
        Ty_::Tprim(_) => "Tprim",
        Ty_::Tfun(_) => "Tfun",
        Ty_::Ttuple(_) => "Ttuple",
        Ty_::Tshape(_) => "Tshape",
        Ty_::Tgeneric(_) => "Tgeneric",
        Ty_::Tunion(_) => "Tunion",
        Ty_::Tintersection(_) => "Tintersection",
        Ty_::TvecOrDict(_, _) => "Tvec_or_dict",
        Ty_::Taccess(_) => "Taccess",
        Ty_::TclassPtr(_) => "Tclass_ptr",
        Ty_::Tvar(_) => "Tvar",
        Ty_::Tnewtype(_, _, _) => "Tnewtype",
        Ty_::Tdependent(_, _) => "Tdependent",
        Ty_::Tclass(_, _, _) => "Tclass",
        Ty_::Tneg(_) => "Tneg",
        Ty_::Tlabel(_) => "Tlabel",
    }
    .to_string()
}

pub fn has_complex_lvalue(el: &[tast::Expr]) -> bool {
    el.iter().any(|aast::Expr(_, _, e)| match e {
        aast::Expr_::Lvar(_) | aast::Expr_::Omitted | aast::Expr_::Lplaceholder(_) => false,
        aast::Expr_::List(sub_el) => has_complex_lvalue(sub_el),
        aast::Expr_::ReadonlyExpr(inner) => {
            let aast::Expr(_, _, inner_e) = &**inner;
            match inner_e {
                aast::Expr_::Lvar(_) => false,
                _ => true,
            }
        }
        _ => true,
    })
}

/// Extract original source text from a position
pub fn source_text_of_pos(file: &RelativePath, pos: &Pos) -> String {
    match file_provider::get_contents(None, file) {
        Some(content) => {
            // `try Pos.get_text_from_pos ~content pos with _ -> ...`:
            // `Pos.get_text_from_pos` is `String.sub` of the bytes of the
            // file, which raises when the position is not in them.
            // `pos::get_text_from_pos` takes a `&str`, so what it does is
            // written out here on the bytes: converting the whole file to
            // UTF-8 first would move every offset after an invalid byte (and
            // a `str` cannot be cut inside a character, which panicked).
            // Only the text taken out is converted (`yojson` strings are
            // `String`s).
            let content: &[u8] = content.as_ref();
            let pos_length = pos::length(pos);
            let offset = pos::start_offset(pos);
            if offset < 0 || pos_length < 0 || (offset + pos_length) as usize > content.len() {
                "<source unavailable>".to_string()
            } else {
                String::from_utf8_lossy(&content[offset as usize..(offset + pos_length) as usize])
                    .into_owned()
            }
        }
        None => "<source unavailable>".to_string(),
    }
}

/// Classify the kind of a non-trivial lvalue expression
pub fn lvalue_kind(e: &tast::Expr) -> types::LvalueKind {
    let aast::Expr(_, _, e) = e;
    match e {
        aast::Expr_::ArrayGet(ag) if ag.1.is_none() => types::LvalueKind::ArrayAppend,
        aast::Expr_::ArrayGet(_) => types::LvalueKind::ArrayGet,
        aast::Expr_::ObjGet(_) => types::LvalueKind::ObjGet,
        aast::Expr_::ClassGet(_) => types::LvalueKind::ClassGet,
        aast::Expr_::Call(_) => types::LvalueKind::Call,
        aast::Expr_::ReadonlyExpr(_) => types::LvalueKind::ReadonlyExpr,
        _ => types::LvalueKind::Other,
    }
}

/// Convert a class_id_ to receiver_kind
pub fn receiver_kind_of_class_id_(
    cid: &aast::ClassId_<tast::Ty, tast::SavedEnv>,
) -> types::ReceiverKind {
    match cid {
        aast::ClassId_::CIself => types::ReceiverKind::Self_,
        aast::ClassId_::CIstatic => types::ReceiverKind::Static,
        aast::ClassId_::CIparent => types::ReceiverKind::Parent,
        aast::ClassId_::CI(_) => types::ReceiverKind::Explicit,
        aast::ClassId_::CIreified(_) => types::ReceiverKind::Explicit,
        aast::ClassId_::CIexpr(_) => types::ReceiverKind::Expr,
    }
}

/// Check whether an lvalue expression involves a function call anywhere
/// in its sub-expression chain (e.g. foo()[3] has Array_get at the top
/// but involves a call as the base expression)
pub fn involves_call(e: &tast::Expr) -> bool {
    let aast::Expr(_, _, e) = e;
    match e {
        aast::Expr_::Call(_) => true,
        aast::Expr_::ArrayGet(ag) => involves_call(&ag.0),
        aast::Expr_::ObjGet(og) => involves_call(&og.0),
        aast::Expr_::ReadonlyExpr(inner) => involves_call(inner),
        _ => false,
    }
}

pub fn pos_info_of_pos(p: &Pos) -> types::PosInfo {
    let p = pos::to_relative_string(p);
    let (line, char_start, char_end) = pos::info_pos(&p);
    types::PosInfo {
        filename: pos::filename(&p),
        line,
        char_start,
        char_end,
    }
}

/// Count total leaf lvalue positions in a list() expression.
/// Nested List nodes are recursed into (not counted themselves).
/// Everything else counts as one position.
pub fn count_lvalue_positions(el: &[tast::Expr]) -> isize {
    el.iter().fold(0, |count, aast::Expr(_, _, e)| match e {
        aast::Expr_::List(sub_el) => count + count_lvalue_positions(sub_el),
        _ => count + 1,
    })
}

/// Extract the receiver_kind for a Class_get expression
pub fn class_get_receiver_kind(ci: &tast::ClassId) -> Option<types::ReceiverKind> {
    let aast::ClassId(_, _, ci) = ci;
    Some(receiver_kind_of_class_id_(ci))
}

/// Collect info about non-trivial lvalue elements in a list() expression.
/// Skips Lvar, Omitted, and recursively descends into nested List.
/// Uses original source text from [file] for lvalue_code.
///
/// `acc` and the result are OCaml lists stored back to front: the last
/// element of the vector is the head of the list (so the vector is in the
/// order the elements are found, which is `List.rev` of the OCaml result).
pub fn collect_complex_lvalues(
    file: &RelativePath,
    acc: Vec<types::ComplexLvalueElement>,
    el: &[tast::Expr],
) -> Vec<types::ComplexLvalueElement> {
    // `elem :: acc` is `acc.push(elem)`.
    el.iter().fold(acc, |mut acc, expr| {
        let aast::Expr(_, p, e) = expr;
        match e {
            aast::Expr_::Lvar(_) | aast::Expr_::Omitted | aast::Expr_::Lplaceholder(_) => acc,
            aast::Expr_::List(sub_el) => collect_complex_lvalues(file, acc, sub_el),
            aast::Expr_::ReadonlyExpr(inner) => {
                let aast::Expr(_, _, inner_e) = &**inner;
                match inner_e {
                    aast::Expr_::Lvar(_) => acc,
                    _ => {
                        let lvalue_receiver_kind = match inner_e {
                            aast::Expr_::ClassGet(cg) => class_get_receiver_kind(&cg.0),
                            _ => None,
                        };
                        let elem = types::ComplexLvalueElement {
                            kind: lvalue_kind(inner),
                            pos: pos_info_of_pos(p),
                            code: source_text_of_pos(file, p),
                            involves_call: involves_call(inner),
                            receiver_kind: lvalue_receiver_kind,
                        };
                        acc.push(elem);
                        acc
                    }
                }
            }
            _ => {
                let lvalue_receiver_kind = match e {
                    aast::Expr_::ClassGet(cg) => class_get_receiver_kind(&cg.0),
                    _ => None,
                };
                let elem = types::ComplexLvalueElement {
                    kind: lvalue_kind(expr),
                    pos: pos_info_of_pos(p),
                    code: source_text_of_pos(file, p),
                    involves_call: involves_call(expr),
                    receiver_kind: lvalue_receiver_kind,
                };
                acc.push(elem);
                acc
            }
        }
    })
}

/// Level 1: write to out_channel for test capture and structured pipeline consumption.
/// Level > 1: write to Hh_logger for server logs (used in WWW runs).
pub fn log_output(level: isize, output: &str) {
    if level > 1 {
        hh_logger::log(output)
    } else {
        let line = format!("{}\n", output);
        typing_log::OUT_CHANNEL.with(|oc| {
            let mut oc = oc.borrow_mut();
            if let Err(e) = oc.write_all(line.as_bytes()) {
                panic!("Sys_error: {}", e)
            }
            if let Err(e) = oc.flush() {
                panic!("Sys_error: {}", e)
            }
        })
    }
}

/// The object `create_handler` returns.
struct AnalyzeListLogger {
    level: isize,
}

impl<'a> tast_visitor::Handler<'a> for AnalyzeListLogger {
    fn at_expr(&mut self, env: &tast_env::Env, e: &tast::Expr) {
        let aast::Expr(_, _, e) = e;
        match e {
            aast::Expr_::Assign(assign)
                if matches!(&assign.0.2, aast::Expr_::List(_)) && assign.1.is_none() =>
            {
                let (aast::Expr(_, lhs_pos, lhs_e), _, rhs_expr) = &**assign;
                let el = match lhs_e {
                    aast::Expr_::List(el) => el,
                    _ => unreachable!(),
                };
                let rhs_ty = tast::get_type(rhs_expr);
                let (bucket, stripped_ty) = classify_type(env, rhs_ty);
                let type_string = tast_env::print_ty(env, rhs_ty);
                let complex = has_complex_lvalue(el);
                let file = tast_env::get_file(env);
                let complex_lvalue_elements = if complex {
                    // `List.rev (collect_complex_lvalues file [] el)`: the
                    // vector is the OCaml list reversed.
                    collect_complex_lvalues(&file, vec![], el)
                } else {
                    vec![]
                };
                let aast::Expr(_, rhs_pos, _) = rhs_expr;
                let lhs_code = source_text_of_pos(&file, lhs_pos);
                let total_lvalue_count = count_lvalue_positions(el);
                let is_generated = crate::tast_logger_util::is_generated(lhs_pos);
                let entry = types::T {
                    bucket,
                    type_string,
                    has_complex_lvalue: complex,
                    pos: pos_info_of_pos(rhs_pos),
                    lhs_code,
                    total_lvalue_count,
                    is_generated,
                    ty_node_kind: match bucket {
                        types::Bucket::Misc => Some(ty_node_kind(&stripped_ty)),
                        _ => None,
                    },
                    complex_lvalue_elements,
                };
                let output = format!("@list_logger:{}", types::to_json_string(&entry));
                log_output(self.level, &output)
            }
            _ => {}
        }
    }
}

/// TAST logger that records list() assignment patterns.
///
/// To run on WWW and analyze:
/// ```text
/// buck run @//mode/opt //hphp/hack/src/analyze/list:run_list_analysis -- --root ~/www --pastry
/// ```
pub fn create_handler<'a>(ctx: &provider_context::T) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    let level = provider_context::get_tcopt(ctx)
        .log_levels
        .get("list_logger")
        .copied()
        .unwrap_or(1);
    Box::new(AnalyzeListLogger { level })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn node_kinds() {
        let ty = crate::typing_make_type::nothing(crate::typing_reason::none());
        assert_eq!(ty_node_kind(&ty), "Tunion");
        let ty = crate::typing_make_type::nonnull(crate::typing_reason::none());
        assert_eq!(ty_node_kind(&ty), "Tnonnull");
    }
}
