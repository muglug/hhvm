// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Index_xrefs` (`write_symbol_info/index_xrefs.ml`).

use std::cell::RefCell;

use oxidized::aast;
use oxidized::ast_defs;
use oxidized::pos::Pos;

use super::add_fact;
use super::build_fact;
use super::file_info;
use super::glean::fact_id;
use super::glean::hack::argument;
use super::glean::hack::class_declaration;
use super::glean::hack::container_declaration;
use super::glean::hack::declaration;
use super::glean::hack::enum_declaration;
use super::glean::hack::enumerator;
use super::glean::hack::function_declaration;
use super::glean::hack::global_const_declaration;
use super::glean::hack::interface_declaration;
use super::glean::hack::method_declaration;
use super::glean::hack::method_occurrence;
use super::glean::hack::occurrence;
use super::glean::hack::property_declaration;
use super::glean::hack::string_literal;
use super::glean::hack::trait_declaration;
use super::glean::hack::type_const_declaration;
use super::glean::hack::typedef_declaration;
use super::glean::hack::x_ref_target;
use super::glean::src;
use super::predicate;
use super::predicate::Failure;
use super::predicate::fact_acc;
use super::sym_def;
use super::util;
use super::xrefs;
use crate::aast_utils;
use crate::hh_logger;
use crate::provider_context;
use crate::symbol_occurrence as so;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;

type Fa = fact_acc::T;

fn process_arg(pos_map: &xrefs::PosMap, (exp, arg_pos): (&tast::Expr_, &Pos)) -> (Option<argument::T>, Pos) {
    let arg = match exp {
        aast::Expr_::String(s) if s.iter().all(|c| *c < 127) => {
            // TODO make this more general
            Some(argument::T::Lit(string_literal::T::key(
                String::from_utf8_lossy(s).into_owned(),
            )))
        }
        aast::Expr_::Id(id) => target_at(pos_map, &id.0),
        aast::Expr_::ClassConst(cc) => target_at(pos_map, &(cc.1).0),
        _ => None,
    };
    (arg, arg_pos.clone())
}

/// The argument of the `Id` and `Class_const` cases of `process_arg`.
fn target_at(pos_map: &xrefs::PosMap, id_pos: &Pos) -> Option<argument::T> {
    // there shouldn't be more than one target for a symbol in that
    // position
    xrefs::pos_map_find_first(pos_map, id_pos).map(|xrefs::TargetInfo { target, .. }| argument::T::Xref(target.clone()))
}

#[allow(clippy::too_many_arguments)]
fn process_call(
    path: &str,
    pos_map: &xrefs::PosMap,
    fa_ref: &RefCell<&mut Fa>,
    callee_pos: &Pos,
    id_pos: Option<&Pos>,
    receiver_span: Option<&Pos>,
    args: &[tast::Argument],
    arg_processor: impl Fn(&tast::Argument) -> (Option<argument::T>, Pos),
) {
    let call_args = build_fact::call_arguments(args.iter().map(arg_processor).collect());
    let dispatch_arg = receiver_span.and_then(|pos| {
        let mut l = build_fact::call_arguments(vec![(None, pos.clone())]);
        if l.len() == 1 { l.pop() } else { None }
    });
    let callee_infos: &[xrefs::TargetInfo] = match id_pos {
        None => &[],
        Some(pos) => match pos_map.get(pos) {
            Some(l) => l,
            None => &[],
        },
    };
    // (The OCaml list is the reverse of the vector: see `Xrefs.t`.)
    let callee_infos: Vec<xrefs::TargetInfo> = callee_infos.iter().rev().cloned().collect();
    let mut fa = fa_ref.borrow_mut();
    add_fact::file_call(path, callee_pos, &callee_infos, call_args, dispatch_arg, &mut fa);
}

struct CallHandler<'a, 'f> {
    path: &'a str,
    fa_ref: &'a RefCell<&'f mut Fa>,
    pos_map: &'a xrefs::PosMap,
}

impl<'a, 'f> tast_visitor::Handler<'a> for CallHandler<'a, 'f> {
    fn at_expr(&mut self, _env: &Env, expr: &'a tast::Expr) {
        if let aast::Expr_::New(new) = &expr.2 {
            let (aast::ClassId(_, callee_pos, _), _, args, _, _) = &**new;
            let pos_map = self.pos_map;
            let arg_processor = |arg: &tast::Argument| {
                let aast::Expr(_, arg_pos, exp) = aast_utils::arg_to_expr(arg);
                process_arg(pos_map, (exp, arg_pos))
            };
            process_call(
                self.path,
                self.pos_map,
                self.fa_ref,
                callee_pos,
                Some(callee_pos),
                None,
                args,
                arg_processor,
            )
        }
    }

    fn at_call(&mut self, _env: &Env, call: &'a tast::CallExpr) {
        let aast::CallExpr { func, args, .. } = call;
        let aast::Expr(_, callee_pos, callee_exp) = func;
        let pos_map = self.pos_map;
        let arg_processor = |arg: &tast::Argument| {
            let aast::Expr(_, arg_pos, exp) = aast_utils::arg_to_expr(arg);
            process_arg(pos_map, (exp, arg_pos))
        };
        let (id_pos, receiver_span) = match callee_exp {
            aast::Expr_::Id(id) => (Some(&id.0), None),
            aast::Expr_::ClassConst(cc) => (Some(&(cc.1).0), None),
            aast::Expr_::ObjGet(og) => match &**og {
                (aast::Expr(_, receiver_span, _), aast::Expr(_, _, aast::Expr_::Id(id)), _, _) => {
                    (Some(&id.0), Some(receiver_span))
                }
                _ => (None, None),
            },
            _ => (None, None),
        };
        process_call(
            self.path,
            self.pos_map,
            self.fa_ref,
            callee_pos,
            id_pos,
            receiver_span,
            args,
            arg_processor,
        )
    }
}

fn process_calls(
    ctx: &provider_context::T,
    path: &str,
    tast: &[(tast::Def, Vec<file_info::MemberCluster>)],
    map_pos_decl: &xrefs::PosMap,
    fa: &mut Fa,
) {
    let fa_ref = RefCell::new(fa);
    {
        let mut visitor = tast_visitor::iter_with(
            None,
            vec![Box::new(CallHandler {
                path,
                fa_ref: &fa_ref,
                pos_map: map_pos_decl,
            })],
        );
        // (`visitor#go ctx (List.map ~f:fst tast)`: `go` visits each
        // definition with `go_def`.)
        for (def, _) in tast {
            visitor.go_def(ctx, def);
        }
    }
}

fn process_xref(
    decl_fun: impl FnOnce(&str, &mut Fa) -> fact_id::T,
    decl_ref_fun: impl FnOnce(fact_id::T) -> declaration::T,
    symbol_name: &str,
    pos: &Pos,
    receiver_type: Option<declaration::T>,
    (xrefs, fa): (&mut xrefs::T, &mut Fa),
) {
    let target_id = decl_fun(symbol_name, fa);
    let target = x_ref_target::T::Declaration(decl_ref_fun(target_id));
    xrefs::add(
        xrefs,
        target_id,
        pos.clone(),
        xrefs::TargetInfo {
            target,
            receiver_type,
            fact_id: target_id,
        },
    )
}

fn process_enum_xref(symbol_name: &str, pos: &Pos, acc: (&mut xrefs::T, &mut Fa)) {
    process_xref(
        add_fact::enum_decl,
        |x| declaration::T::Container(container_declaration::T::Enum_(enum_declaration::T::Id(x))),
        symbol_name,
        pos,
        None,
        acc,
    )
}

fn process_typedef_xref(symbol_name: &str, pos: &Pos, acc: (&mut xrefs::T, &mut Fa)) {
    process_xref(
        add_fact::typedef_decl,
        |x| declaration::T::Typedef_(typedef_declaration::T::Id(x)),
        symbol_name,
        pos,
        None,
        acc,
    )
}

fn process_function_xref(symbol_name: &str, pos: &Pos, acc: (&mut xrefs::T, &mut Fa)) {
    process_xref(
        add_fact::func_decl,
        |x| declaration::T::Function_(function_declaration::T::Id(x)),
        symbol_name,
        pos,
        None,
        acc,
    )
}

fn process_gconst_xref(symbol_def: &str, pos: &Pos, acc: (&mut xrefs::T, &mut Fa)) {
    process_xref(
        add_fact::gconst_decl,
        |x| declaration::T::GlobalConst(global_const_declaration::T::Id(x)),
        symbol_def,
        pos,
        None,
        acc,
    )
}

/// The member declaration functions of `Add_fact` (`property_decl`,
/// `method_decl`, ...): `mem_decl_fun class_kind class_decl_id name fa`.
type MemDeclFun = fn(predicate::ParentContainerType, fact_id::T, &str, &mut Fa) -> fact_id::T;

#[allow(clippy::too_many_arguments)]
fn process_member_xref(
    ctx: &provider_context::T,
    class_name: &str,
    name: &str,
    pos: &Pos,
    mem_decl_fun: MemDeclFun,
    ref_fun: fn(fact_id::T) -> declaration::T,
    receiver_type: Option<declaration::T>,
    class_const: bool,
    (xrefs, fa): (&mut xrefs::T, &mut Fa),
) -> Result<(), Failure> {
    match sym_def::get_kind(ctx, class_name) {
        None => {
            hh_logger::log(&format!(
                "WARNING: could not find parent container {} processing reference to {}",
                class_name, name
            ));
        }
        Some(ast_defs::ClassishKind::Cenum) | Some(ast_defs::ClassishKind::CenumClass(_)) => {
            if class_const {
                let enum_id = add_fact::enum_decl(class_name, fa);
                process_xref(
                    |name, fa| add_fact::enumerator(enum_id, name, fa),
                    |x| declaration::T::Enumerator(enumerator::T::Id(x)),
                    name,
                    pos,
                    None,
                    (xrefs, fa),
                )
            }
        }
        Some(cls) => {
            let (class_kind, decl_pred) = predicate::classish_to_predicate(&cls)?;
            let class_decl_id = add_fact::container_decl(decl_pred, class_name, fa)?;
            process_xref(
                |name, fa| mem_decl_fun(class_kind, class_decl_id, name, fa),
                ref_fun,
                name,
                pos,
                receiver_type,
                (xrefs, fa),
            )
        }
    }
    Ok(())
}

fn process_container_xref(
    (con_type, decl_pred): (predicate::ParentContainerType, predicate::T),
    symbol_name: &str,
    pos: &Pos,
    (xrefs, fa): (&mut xrefs::T, &mut Fa),
) -> Result<(), Failure> {
    // (`Add_fact.container_decl` can fail: `decl_fun` raises inside
    // `process_xref` in the OCaml.)
    let target_id = add_fact::container_decl(decl_pred, symbol_name, fa)?;
    process_xref(
        |_, _| target_id,
        |x| predicate::container_ref(con_type, x),
        symbol_name,
        pos,
        None,
        (xrefs, fa),
    );
    Ok(())
}

fn process_attribute_xref(
    ctx: &provider_context::T,
    file_info::Symbol { occ, .. }: &file_info::Symbol,
    (xrefs, fa): (&mut xrefs::T, &mut Fa),
) {
    let get_con_preds_from_name = |con_name: &str| -> Result<Option<(predicate::ParentContainerType, predicate::T)>, Failure> {
        match sym_def::get_kind(ctx, con_name) {
            None => {
                hh_logger::log(&format!(
                    "WARNING: could not find declaration container {} for attribute reference",
                    con_name
                ));
                Ok(None)
            }
            Some(ast_defs::ClassishKind::CenumClass(_)) | Some(ast_defs::ClassishKind::Cenum) => {
                hh_logger::log(&format!("WARNING: unexpected enum {}", con_name));
                Ok(None)
            }
            Some(cls) => {
                let parent_kind = predicate::get_parent_kind(&cls)?;
                Ok(Some((parent_kind, predicate::parent_decl_predicate(parent_kind))))
            }
        }
    };
    // Process <<__Override>>, for which we write a MethodOverrides fact
    // instead of a cross-reference
    let so::T { name, pos, .. } = occ;
    if name.starts_with("__") {
    }
    // Process user-defined attributes
    else {
        // Look for a container declaration with the same name as the attribute,
        // which will be where it is defined
        let res = (|| -> Result<(), Failure> {
            match get_con_preds_from_name(name)? {
                None => Ok(()),
                Some(con_pred_types) => process_container_xref(con_pred_types, name, pos, (xrefs, fa)),
            }
        })();
        if let Err(e) = res {
            hh_logger::log(&format!(
                "WARNING: error processing reference to attribute {}\n: {}\n",
                name,
                e.exn_to_string()
            ));
        }
    }
}

fn receiver_type(ctx: &provider_context::T, occ: &so::T<Pos>) -> Option<declaration::T> {
    match &occ.type_ {
        so::Kind::Method(so::ReceiverClass::ClassName(receiver), _) => {
            let qname = util::make_qname(receiver);
            match sym_def::get_kind(ctx, receiver) {
                None => None,
                Some(ast_defs::ClassishKind::Cenum) | Some(ast_defs::ClassishKind::CenumClass(_)) => {
                    Some(declaration::T::Container(container_declaration::T::Enum_(
                        enum_declaration::T::key(enum_declaration::Key { name: qname }),
                    )))
                }
                Some(ast_defs::ClassishKind::Cinterface) => Some(declaration::T::Container(
                    container_declaration::T::Interface_(interface_declaration::T::key(
                        interface_declaration::Key { name: qname },
                    )),
                )),
                Some(ast_defs::ClassishKind::Ctrait) => Some(declaration::T::Container(
                    container_declaration::T::Trait(trait_declaration::T::key(trait_declaration::Key { name: qname })),
                )),
                Some(ast_defs::ClassishKind::Cclass(_)) => Some(declaration::T::Container(
                    container_declaration::T::Class_(class_declaration::T::key(class_declaration::Key { name: qname })),
                )),
            }
        }
        _ => None,
    }
}

fn process_def_xref(
    ctx: &provider_context::T,
    occ: &so::T<Pos>,
    pos: &Pos,
    def: &Option<sym_def::T>,
    (xrefs, fa): (&mut xrefs::T, &mut Fa),
) -> Result<(), Failure> {
    match def {
        None => {
            // no symbol info - likely dynamic
            if let so::Kind::Method(receiver_class, name) = &occ.type_ {
                let target_id = add_fact::method_occ(receiver_class, name, fa);
                let receiver_type = receiver_type(ctx, occ);
                let target = x_ref_target::T::Occurrence(occurrence::T::Method(method_occurrence::T::Id(target_id)));
                xrefs::add(
                    xrefs,
                    target_id,
                    pos.clone(),
                    xrefs::TargetInfo {
                        target,
                        receiver_type,
                        fact_id: target_id,
                    },
                )
            }
            Ok(())
        }
        Some(sym_def) => match sym_def {
            sym_def::T::Class {
                kind: ast_defs::ClassishKind::Cenum,
                name,
            }
            | sym_def::T::Class {
                kind: ast_defs::ClassishKind::CenumClass(_),
                name,
            } => {
                process_enum_xref(name, pos, (xrefs, fa));
                Ok(())
            }
            sym_def::T::Class { kind, name } => {
                process_container_xref(predicate::classish_to_predicate(kind)?, name, pos, (xrefs, fa))
            }
            sym_def::T::ClassConst { class_name, name } => process_member_xref(
                ctx,
                class_name,
                name,
                pos,
                add_fact::class_const_decl,
                |x| declaration::T::ClassConst(super::glean::hack::class_const_declaration::T::Id(x)),
                None,
                true,
                (xrefs, fa),
            ),
            sym_def::T::GlobalConst { name } => {
                process_gconst_xref(name, pos, (xrefs, fa));
                Ok(())
            }
            sym_def::T::Function { name } => {
                process_function_xref(name, pos, (xrefs, fa));
                Ok(())
            }
            sym_def::T::Method { class_name, name } => process_member_xref(
                ctx,
                class_name,
                name,
                pos,
                add_fact::method_decl,
                |x| declaration::T::Method(method_declaration::T::Id(x)), // TODO just pass the occurrence here
                receiver_type(ctx, occ),
                false,
                (xrefs, fa),
            ),
            sym_def::T::Property { class_name, name } => process_member_xref(
                ctx,
                class_name,
                name,
                pos,
                add_fact::property_decl,
                |x| declaration::T::Property_(property_declaration::T::Id(x)),
                None,
                false,
                (xrefs, fa),
            ),
            sym_def::T::Typeconst { class_name, name } => process_member_xref(
                ctx,
                class_name,
                name,
                pos,
                add_fact::type_const_decl,
                |x| declaration::T::TypeConst(type_const_declaration::T::Id(x)),
                None,
                false,
                (xrefs, fa),
            ),
            sym_def::T::Typedef { name } => {
                process_typedef_xref(name, pos, (xrefs, fa));
                Ok(())
            }
            _ => Ok(()),
        },
    }
}

/// Given symbols occurring in a file, compute the maps of xrefs
/// [path] The file path for which xrefs are being processed.
/// [ctx] The provider context used to query declaration information.
/// [symbols]  The list of symbol occurrences (and optional definitions) found
///     in the file. Each element pairs a {!SymbolOccurrence.t} with an optional
///     {!Sym_def.t} that identifies the declaration the occurrence refers to.
/// [fa] The fact accumulator that collects Glean facts during indexing.
fn process_xrefs(
    path: &str,
    ctx: &provider_context::T,
    symbols: &[file_info::Symbol],
    fa: &mut Fa,
) -> Result<xrefs::T, Failure> {
    let mut xrefs = xrefs::empty();
    for sym in symbols {
        let file_info::Symbol { occ, def } = sym;
        if occ.is_declaration.is_some() {
            continue;
        }
        let pos = &occ.pos;
        match &occ.type_ {
            so::Kind::Attribute(_info) => process_attribute_xref(ctx, sym, (&mut xrefs, fa)),
            _ => process_def_xref(ctx, occ, pos, def, (&mut xrefs, fa))?,
        }
        if let Some(xrefs::TargetInfo { fact_id, .. }) = xrefs::pos_map_find_first(&xrefs.pos_map, pos) {
            let fact_id = *fact_id;
            xrefs::mark_target_used_in_prod_build(&mut xrefs, fact_id, occ.affects_prod_build)
        }
    }
    // Emit TargetNotUsedInProdBuild for targets where no occurrence has
    // affects_prod_build = true
    for (fact_id, used_in_prod) in &xrefs.used_in_prod_build {
        if !*used_in_prod {
            if let Some((target, _)) = xrefs.fact_map.get(fact_id) {
                add_fact::target_not_used_in_prod_build(target.clone(), src::file::T::key(path.to_string()), fa);
            }
        }
    }
    Ok(xrefs)
}

pub fn process_xrefs_and_calls(
    ctx: &provider_context::T,
    fa: &mut Fa,
    file_info: &file_info::T,
) -> Result<xrefs::T, Failure> {
    let file_info::T {
        path, tast, symbols, ..
    } = file_info;
    fact_acc::set_ownership_unit(fa, Some(path.clone()));
    let xrefs = process_xrefs(path, ctx, symbols, fa)?;
    process_calls(ctx, path, tast, &xrefs.pos_map, fa);
    Ok(xrefs)
}
