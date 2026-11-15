// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Index_decls` (`write_symbol_info/index_decls.ml`).

use std::cell::RefCell;

use oxidized::aast;
use oxidized::ast_defs;
use oxidized::pos::Pos;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;

use super::add_fact;
use super::file_info;
use super::glean::fact_id;
use super::glean::hack::class_const_declaration;
use super::glean::hack::container_declaration;
use super::glean::hack::declaration;
use super::glean::hack::enum_declaration;
use super::glean::hack::enumerator;
use super::glean::hack::function_declaration;
use super::glean::hack::global_const_declaration;
use super::glean::hack::method_declaration;
use super::glean::hack::module_declaration;
use super::glean::hack::namespace_declaration;
use super::glean::hack::property_declaration;
use super::glean::hack::type_const_declaration;
use super::glean::hack::typedef_declaration;
use super::glean::hack::x_ref_target;
use super::predicate;
use super::predicate::Failure;
use super::predicate::fact_acc;
use super::sym_def;
use super::thrift;
use super::util;
use super::xrefs;
use crate::full_fidelity_source_text;
use crate::hh_logger;
use crate::provider_context;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;

type Fa = fact_acc::T;

/// `(xrefs, all_decls, fa)`, the accumulator of the `process_*_decl`
/// functions (`fa` is changed in place, see `Fact_acc.t`).
type Acc = (xrefs::T, Vec<declaration::T>);

fn process_doc_comment(comment: &Option<aast::DocComment>, path: &str, decl_ref: &declaration::T, fa: &mut Fa) {
    match comment {
        None => {}
        Some((pos, _doc)) => {
            add_fact::decl_comment(path, pos, decl_ref.clone(), fa);
        }
    }
}

fn process_thrift_container<Ex, En>(
    thrift_ctx: &mut Option<thrift::T>,
    con: &aast::Class_<Ex, En>,
    hack_decl: &declaration::T,
    fa: &mut Fa,
) {
    match thrift_ctx {
        None => {}
        Some(thrift_ctx) => match thrift::get_thrift_from_container(thrift_ctx, con) {
            Some(thrift_decl) => add_fact::hack_to_thrift(hack_decl.clone(), thrift_decl, fa),
            None => {}
        },
    }
}

/// Thrift declaration can be reconstructed from comments, enum values, or class members
/// names for union, see [Thrift]
enum ThriftMember<'a> {
    Comment(&'a str),
    Enumerator(&'a str),
    MemberName(&'a str),
}

fn process_thrift_member(
    thrift_ctx: &mut thrift::T,
    member: ThriftMember<'_>,
    hack_decl: &declaration::T,
    fa: &mut Fa,
) {
    match fact_acc::get_generated_from(fa) {
        Some(_) => {
            let decl = match member {
                ThriftMember::Enumerator(id) => thrift::get_thrift_from_enum(thrift_ctx, id),
                ThriftMember::Comment(doc) => thrift::get_thrift_from_comment(thrift_ctx, doc),
                ThriftMember::MemberName(member_name) => thrift::get_thrift_from_union_member(thrift_ctx, member_name),
            };
            match decl {
                None => {}
                Some(thrift_decl) => add_fact::hack_to_thrift(hack_decl.clone(), thrift_decl, fa),
            }
        }
        None => {}
    }
}

fn process_loc_span(path: &str, pos: &Pos, span: &Pos, ref_: &declaration::T, fa: &mut Fa) {
    add_fact::decl_loc(path, pos, ref_.clone(), fa);
    add_fact::decl_span(path, span, ref_.clone(), fa);
}

fn closure_name(pos: &Pos) -> String {
    let (line, col, _) = pos.info_pos();
    format!("(closure)${}_{}", line, col)
}

fn process_closure(
    path: &str,
    source_text: &full_fidelity_source_text::T,
    pos: &Pos,
    fun_: &tast::Fun_,
    (_xrefs, all_decls): &mut Acc,
    fa: &mut Fa,
) -> Result<(), Failure> {
    let name = closure_name(pos);
    let decl_id = add_fact::func_decl(&name, fa);
    add_fact::closure_defn(source_text, fun_, decl_id, fa)?;
    let decl_ref = declaration::T::Function_(function_declaration::T::Id(decl_id));
    process_loc_span(path, pos, &fun_.span, &decl_ref, fa);
    all_decls.push(decl_ref);
    Ok(())
}

/// The handler of `collect_and_process_closures`.
struct ClosureHandler<'a> {
    closures_ref: &'a RefCell<Vec<(&'a Pos, &'a tast::Fun_)>>,
}

impl<'a> tast_visitor::Handler<'a> for ClosureHandler<'a> {
    fn at_expr(&mut self, _env: &Env, expr: &'a tast::Expr) {
        match &expr.2 {
            aast::Expr_::Efun(efun) => self.closures_ref.borrow_mut().push((&expr.1, &efun.fun)),
            aast::Expr_::Lfun(lfun) => self.closures_ref.borrow_mut().push((&expr.1, &lfun.0)),
            _ => {}
        }
    }
}

fn collect_and_process_closures(
    ctx: &provider_context::T,
    path: &str,
    source_text: &full_fidelity_source_text::T,
    tast: &[(tast::Def, Vec<file_info::MemberCluster>)],
    acc: &mut Acc,
    fa: &mut Fa,
) -> Result<(), Failure> {
    // (The OCaml conses the closures and reverses the list: they are in the
    // order the visitor met them.)
    let closures_ref = RefCell::new(vec![]);
    let closures = {
        let mut visitor = tast_visitor::iter_with(
            None,
            vec![Box::new(ClosureHandler {
                closures_ref: &closures_ref,
            })],
        );
        for (def, _) in tast {
            visitor.go_def(ctx, def);
        }
        drop(visitor);
        closures_ref.take()
    };
    for (pos, fun_) in closures {
        process_closure(path, source_text, pos, fun_, acc, fa)?
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn process_decl_loc(
    decl_fun: impl FnOnce(&str, &mut Fa) -> Result<fact_id::T, Failure>,
    defn_fun: impl FnOnce(fact_id::T, &mut Fa) -> Result<fact_id::T, Failure>,
    decl_ref_fun: impl FnOnce(fact_id::T) -> declaration::T,
    path: &str,
    pos: &Pos,
    span: &Pos,
    id: &str,
    doc: &Option<aast::DocComment>,
    thrift_ctx: Option<&mut thrift::T>,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    let decl_id = decl_fun(id, fa)?;
    defn_fun(decl_id, fa)?;
    let ref_ = decl_ref_fun(decl_id);
    process_doc_comment(doc, path, &ref_, fa);
    let thrift_member = match doc {
        Some((_pos, doc)) => ThriftMember::Comment(doc),
        None => ThriftMember::MemberName(id),
    };
    if let Some(thrift_ctx) = thrift_ctx {
        process_thrift_member(thrift_ctx, thrift_member, &ref_, fa)
    }
    process_loc_span(path, pos, span, &ref_, fa);
    Ok(decl_id)
}

/// The member declaration functions of `Add_fact` (`method_decl`, ...).
type AddMemberDecl = fn(predicate::ParentContainerType, fact_id::T, &str, &mut Fa) -> fact_id::T;

fn process_member(
    add_member_decl: AddMemberDecl,
    build_decl_ref: fn(fact_id::T) -> declaration::T,
    container_type: predicate::ParentContainerType,
    container_id: fact_id::T,
    member_ids: &mut Vec<declaration::T>,
    fa: &mut Fa,
    file_info::Member { name }: &file_info::Member,
) {
    let member_id = add_member_decl(container_type, container_id, name, fa);
    // `build_decl_ref member_id :: member_ids`
    member_ids.insert(0, build_decl_ref(member_id))
}

fn process_member_cluster(mc: &file_info::MemberCluster, fa: &mut Fa) -> Result<Vec<declaration::T>, Failure> {
    let (container_type, container_id) = {
        let (parent_kind, decl_pred) = predicate::classish_to_predicate(&mc.container.kind)?;
        let con_decl_id = add_fact::container_decl(decl_pred, &mc.container.name, fa)?;
        (parent_kind, con_decl_id)
    };
    let mut acc = vec![];
    let mut process = |add_member_decl: AddMemberDecl,
                       build_decl_ref: fn(fact_id::T) -> declaration::T,
                       members: &[file_info::Member],
                       fa: &mut Fa| {
        for m in members {
            process_member(
                add_member_decl,
                build_decl_ref,
                container_type,
                container_id,
                &mut acc,
                fa,
                m,
            )
        }
    };
    process(
        add_fact::method_decl,
        |x| declaration::T::Method(method_declaration::T::Id(x)),
        &mc.methods,
        fa,
    );
    process(
        add_fact::property_decl,
        |x| declaration::T::Property_(property_declaration::T::Id(x)),
        &mc.properties,
        fa,
    );
    process(
        add_fact::type_const_decl,
        |x| declaration::T::TypeConst(type_const_declaration::T::Id(x)),
        &mc.type_constants,
        fa,
    );
    process(
        add_fact::class_const_decl,
        |x| declaration::T::ClassConst(class_const_declaration::T::Id(x)),
        &mc.class_constants,
        fa,
    );
    Ok(acc)
}

#[allow(clippy::too_many_arguments)]
fn process_container_decl(
    ctx: &provider_context::T,
    thrift_ctx: &mut Option<thrift::T>,
    path: &str,
    source_text: &full_fidelity_source_text::T,
    con: &tast::Class_,
    member_clusters: &[file_info::MemberCluster],
    (_xrefs, all_decls): &mut Acc,
    fa: &mut Fa,
) -> Result<(), Failure> {
    let ast_defs::Id(con_pos, con_name) = &con.name;
    let (parent_kind, decl_pred) = predicate::classish_to_predicate(&con.kind)?;
    let con_decl_id = add_fact::container_decl(decl_pred, con_name, fa)?;
    let ref_ = predicate::container_ref(parent_kind, con_decl_id);
    process_loc_span(path, con_pos, &con.span, &ref_, fa);
    process_thrift_container(thrift_ctx, con, &ref_, fa);
    // (`List.fold_right`: from the last element, consing: the declarations
    // end up in the order of the list.)
    let mut prop_decls = vec![];
    for prop in con.vars.iter().rev() {
        let ast_defs::Id(pos, id) = &prop.id;
        let decl_id = process_decl_loc(
            |id, fa| Ok(add_fact::property_decl(parent_kind, con_decl_id, id, fa)),
            |decl_id, fa| add_fact::property_defn(source_text, prop, decl_id, fa),
            |x| declaration::T::Property_(property_declaration::T::Id(x)),
            path,
            pos,
            &prop.span,
            id,
            &prop.doc_comment,
            thrift_ctx.as_mut(),
            fa,
        )?;
        prop_decls.insert(0, declaration::T::Property_(property_declaration::T::Id(decl_id)));
    }
    let mut class_const_decls = vec![];
    for const_ in con.consts.iter().rev() {
        let ast_defs::Id(pos, id) = &const_.id;
        let decl_id = process_decl_loc(
            |id, fa| Ok(add_fact::class_const_decl(parent_kind, con_decl_id, id, fa)),
            |decl_id, fa| add_fact::class_const_defn(source_text, const_, decl_id, fa),
            |x| declaration::T::ClassConst(class_const_declaration::T::Id(x)),
            path,
            pos,
            &const_.span,
            id,
            &const_.doc_comment,
            thrift_ctx.as_mut(),
            fa,
        )?;
        class_const_decls.insert(0, declaration::T::ClassConst(class_const_declaration::T::Id(decl_id)));
    }
    let mut type_const_decls = vec![];
    for tc in con.typeconsts.iter().rev() {
        let ast_defs::Id(pos, id) = &tc.name;
        let decl_id = process_decl_loc(
            |id, fa| Ok(add_fact::type_const_decl(parent_kind, con_decl_id, id, fa)),
            |decl_id, fa| add_fact::type_const_defn(source_text, tc, decl_id, fa),
            |x| declaration::T::TypeConst(type_const_declaration::T::Id(x)),
            path,
            pos,
            &tc.span,
            id,
            &tc.doc_comment,
            None,
            fa,
        )?;
        type_const_decls.insert(0, declaration::T::TypeConst(type_const_declaration::T::Id(decl_id)));
    }
    let mut method_decls = vec![];
    for meth in con.methods.iter().rev() {
        let ast_defs::Id(_, method_name) = &meth.name;
        let class_name = con_name;
        match sym_def::get_overridden_method_origin(ctx, class_name, method_name, meth.static_)? {
            None => {}
            Some((origin, override_kind)) => {
                let annotation = meth.user_attributes.iter().any(|ua| ua.name.1 == "__Override");
                add_fact::method_overrides(
                    annotation,
                    method_name,
                    &origin,
                    override_kind,
                    class_name,
                    parent_kind,
                    fa,
                );
            }
        }
        let ast_defs::Id(pos, id) = &meth.name;
        let decl_id = process_decl_loc(
            |id, fa| Ok(add_fact::method_decl(parent_kind, con_decl_id, id, fa)),
            |decl_id, fa| add_fact::method_defn(source_text, meth, decl_id, fa),
            |x| declaration::T::Method(method_declaration::T::Id(x)),
            path,
            pos,
            &meth.span,
            id,
            &meth.doc_comment,
            thrift_ctx.as_mut(),
            fa,
        )?;
        method_decls.insert(0, declaration::T::Method(method_declaration::T::Id(decl_id)));
    }
    let members: Vec<declaration::T> = type_const_decls
        .into_iter()
        .chain(class_const_decls)
        .chain(prop_decls)
        .chain(method_decls)
        .collect();
    let mut inherited_member_clusters = vec![];
    for mc in member_clusters {
        let members = process_member_cluster(mc, fa)?;
        let mc = add_fact::member_cluster(members, fa);
        inherited_member_clusters.push(mc);
    }
    if !inherited_member_clusters.is_empty() {
        let _id = add_fact::inherited_members(parent_kind, con_decl_id, &inherited_member_clusters, fa);
    }
    add_fact::container_defn(source_text, con, con_decl_id, members.clone(), fa)?;
    all_decls.push(ref_.clone());
    all_decls.extend(members);
    process_doc_comment(&con.doc_comment, path, &ref_, fa);
    Ok(())
}

fn process_enum_decl(
    thrift_ctx: &mut Option<thrift::T>,
    path: &str,
    source_text: &full_fidelity_source_text::T,
    enm: &tast::Class_,
    (_xrefs, all_decls): &mut Acc,
    fa: &mut Fa,
) -> Result<(), Failure> {
    let ast_defs::Id(pos, id) = &enm.name;
    match &enm.enum_ {
        None => {
            hh_logger::log(&format!("WARNING: skipping enum with missing data - {}", id));
            Ok(())
        }
        Some(enum_data) => {
            let enum_id = add_fact::enum_decl(id, fa);
            let enum_decl_ref =
                declaration::T::Container(container_declaration::T::Enum_(enum_declaration::T::Id(enum_id)));
            process_loc_span(path, pos, &enm.span, &enum_decl_ref, fa);
            process_doc_comment(&enm.doc_comment, path, &enum_decl_ref, fa);
            process_thrift_container(thrift_ctx, enm, &enum_decl_ref, fa);
            // (`List.fold_right`, consing: in the order of the constants.)
            let mut enumerators = vec![];
            let mut decl_refs = vec![];
            for enumerator in enm.consts.iter().rev() {
                let ast_defs::Id(pos, id) = &enumerator.id;
                let decl_id = add_fact::enumerator(enum_id, id, fa);
                let _span = &enumerator.span;
                let ref_ = declaration::T::Enumerator(enumerator::T::Id(decl_id));
                // TODO we're using pos instead of _span. _span refer to the whole enum container,
                // rather than the enumerator
                process_loc_span(path, pos, pos, &ref_, fa);
                match thrift_ctx {
                    None => {}
                    Some(thrift_ctx) => process_thrift_member(thrift_ctx, ThriftMember::Enumerator(id), &ref_, fa),
                }
                process_doc_comment(&enumerator.doc_comment, path, &ref_, fa);
                enumerators.insert(0, decl_id);
                decl_refs.insert(0, ref_);
            }
            add_fact::enum_defn(source_text, enm, enum_id, enum_data, &enumerators, fa)?;
            all_decls.push(enum_decl_ref);
            all_decls.extend(decl_refs);
            Ok(())
        }
    }
}

fn process_func_decl(
    path: &str,
    source_text: &full_fidelity_source_text::T,
    fd: &tast::FunDef,
    (_xrefs, all_decls): &mut Acc,
    fa: &mut Fa,
) -> Result<(), Failure> {
    let elem = &fd.fun;
    let ast_defs::Id(pos, id) = &fd.name;
    let decl_id = process_decl_loc(
        |id, fa| Ok(add_fact::func_decl(id, fa)),
        |decl_id, fa| add_fact::func_defn(source_text, fd, decl_id, fa),
        |x| declaration::T::Function_(function_declaration::T::Id(x)),
        path,
        pos,
        &elem.span,
        id,
        &elem.doc_comment,
        None,
        fa,
    )?;
    all_decls.push(declaration::T::Function_(function_declaration::T::Id(decl_id)));
    Ok(())
}

fn process_gconst_decl(
    path: &str,
    source_text: &full_fidelity_source_text::T,
    elem: &tast::Gconst,
    (_xrefs, all_decls): &mut Acc,
    fa: &mut Fa,
) -> Result<(), Failure> {
    let ast_defs::Id(pos, id) = &elem.name;
    let decl_id = process_decl_loc(
        |id, fa| Ok(add_fact::gconst_decl(id, fa)),
        |decl_id, fa| add_fact::gconst_defn(source_text, elem, decl_id, fa),
        |x| declaration::T::GlobalConst(global_const_declaration::T::Id(x)),
        path,
        pos,
        &elem.span,
        id,
        &None,
        None,
        fa,
    )?;
    all_decls.push(declaration::T::GlobalConst(global_const_declaration::T::Id(decl_id)));
    Ok(())
}

fn process_typedef_decl(
    path: &str,
    source_text: &full_fidelity_source_text::T,
    elem: &tast::Typedef,
    (_xrefs, all_decls): &mut Acc,
    fa: &mut Fa,
) -> Result<(), Failure> {
    let ast_defs::Id(pos, id) = &elem.name;
    let decl_id = process_decl_loc(
        |id, fa| Ok(add_fact::typedef_decl(id, fa)),
        |decl_id, fa| add_fact::typedef_defn(source_text, elem, decl_id, fa),
        |x| declaration::T::Typedef_(typedef_declaration::T::Id(x)),
        path,
        pos,
        &elem.span,
        id,
        &elem.doc_comment,
        None,
        fa,
    )?;
    all_decls.push(declaration::T::Typedef_(typedef_declaration::T::Id(decl_id)));
    Ok(())
}

fn process_module_decl(
    path: &str,
    source_text: &full_fidelity_source_text::T,
    elem: &tast::ModuleDef,
    (_xrefs, all_decls): &mut Acc,
    fa: &mut Fa,
) -> Result<(), Failure> {
    let ast_defs::Id(pos, id) = &elem.name;
    let decl_id = process_decl_loc(
        |id, fa| Ok(add_fact::module_decl(id, fa)),
        |decl_id, fa| Ok(add_fact::module_defn(source_text, elem, decl_id, fa)),
        |x| declaration::T::Module(module_declaration::T::Id(x)),
        path,
        pos,
        &elem.span,
        id,
        &None,
        None,
        fa,
    )?;
    all_decls.push(declaration::T::Module(module_declaration::T::Id(decl_id)));
    Ok(())
}

fn process_namespace_decl(
    path: &str,
    (pos, id): (&util::NamespacePos, &str),
    all_decls: &mut Vec<declaration::T>,
    fa: &mut Fa,
) {
    // `process_decl_loc Add_fact.namespace_decl (fun () fid acc -> (fid, acc))
    // ... pos pos (* no span for a namespace decl, we re-use the location *)
    // id () None None fa`, with the OCaml's offsets of `pos` (see
    // `Util.NamespacePos`): no definition, no doc comment, no thrift.
    let decl_id = add_fact::namespace_decl(id, fa);
    let ref_ = declaration::T::Namespace_(namespace_declaration::T::Id(decl_id));
    let span = util::make_byte_span_of_namespace_pos(pos);
    add_fact::decl_loc_of_byte_span(path, span.clone(), ref_.clone(), fa);
    add_fact::decl_span_of_byte_span(path, span, ref_, fa);
    all_decls.push(declaration::T::Namespace_(namespace_declaration::T::Id(decl_id)));
}

fn process_cst_decls(
    st: &full_fidelity_source_text::T,
    path: &str,
    root: &PositionedSyntax,
    decls: &mut Vec<declaration::T>,
    fa: &mut Fa,
) {
    match &root.syntax {
        SyntaxVariant::Script(script) => match &script.script_declarations.syntax {
            SyntaxVariant::SyntaxList(cst_decls) => {
                for cst_decl in cst_decls {
                    if let SyntaxVariant::NamespaceDeclaration(nd) = &cst_decl.syntax {
                        if let SyntaxVariant::NamespaceDeclarationHeader(h) = &nd.namespace_header.syntax {
                            let ns_ast = &h.namespace_name;
                            match util::namespace_ast_to_pos_id(ns_ast, st) {
                                Ok((pos, id)) => process_namespace_decl(path, (&pos, &id), decls, fa),
                                Err(util::NamespaceError::EmptyNamespace) => {}
                                Err(util::NamespaceError::AstError) => {
                                    hh_logger::log("Couldn't extract namespace from declaration")
                                }
                            }
                        }
                    }
                }
            }
            _ => hh_logger::log("Couldn't extract namespaces declarations"),
        },
        _ => hh_logger::log("Couldn't extract namespaces declarations"),
    }
}

fn process_mod_xref(fa: &mut Fa, xrefs: &mut xrefs::T, (pos, id): (&Pos, &str)) {
    let target_id = add_fact::module_decl(id, fa);
    let target = x_ref_target::T::Declaration(declaration::T::Module(module_declaration::T::Id(target_id)));
    xrefs::add(
        xrefs,
        target_id,
        pos.clone(),
        xrefs::TargetInfo {
            target,
            receiver_type: None,
            fact_id: target_id,
        },
    )
}

fn process_tast_decls(
    ctx: &provider_context::T,
    path: &str,
    tast: &[(tast::Def, Vec<file_info::MemberCluster>)],
    source_text: &full_fidelity_source_text::T,
    root_path: &str,
    decls: Vec<declaration::T>,
    fa: &mut Fa,
) -> Result<Acc, Failure> {
    let mut thrift_ctx = match fact_acc::get_generated_from(fa) {
        None => None,
        Some(thrift_path) => {
            // `Filename.concat`
            let thrift_path = if root_path.is_empty() || root_path.ends_with('/') {
                format!("{}{}", root_path, thrift_path)
            } else {
                format!("{}/{}", root_path, thrift_path)
            };
            Some(thrift::empty(thrift_path))
        }
    };
    let mut acc: Acc = (xrefs::empty(), decls.clone());
    for (def, im) in tast {
        match def {
            aast::Def::Class(en) if util::is_enum_or_enum_class(&en.kind) => {
                process_enum_decl(&mut thrift_ctx, path, source_text, en, &mut acc, fa)?
            }
            aast::Def::Class(cd) => process_container_decl(ctx, &mut thrift_ctx, path, source_text, cd, im, &mut acc, fa)?,
            aast::Def::Constant(gd) => process_gconst_decl(path, source_text, gd, &mut acc, fa)?,
            aast::Def::Fun(fd) => process_func_decl(path, source_text, fd, &mut acc, fa)?,
            aast::Def::Typedef(td) => process_typedef_decl(path, source_text, td, &mut acc, fa)?,
            aast::Def::Module(md) => process_module_decl(path, source_text, md, &mut acc, fa)?,
            aast::Def::SetModule(sm) => {
                // (The declarations so far are dropped: the OCaml goes on with
                // the [decls] it was given.)
                process_mod_xref(fa, &mut acc.0, (&sm.0, &sm.1));
                acc.1 = decls.clone();
            }
            _ => {}
        }
    }
    // Walk the TAST to find closures (Efun/Lfun) and emit declaration/span
    // facts for each, so that closure bodies get their own line ranges
    // rather than being lumped into the enclosing function/method.
    collect_and_process_closures(ctx, path, source_text, tast, &mut acc, fa)?;
    Ok(acc)
}

pub fn process_decls(
    ctx: &provider_context::T,
    fa: &mut Fa,
    file_info: &file_info::T,
) -> Result<xrefs::T, Failure> {
    let file_info::T {
        path,
        tast,
        source_text,
        cst,
        root_path,
        ..
    } = file_info;
    fact_acc::set_ownership_unit(fa, Some(path.clone()));
    add_fact::file_lines(path, source_text, fa);
    let (mod_xrefs, mut decls) = process_tast_decls(ctx, path, tast, source_text, root_path, vec![], fa)?;
    process_cst_decls(source_text, path, cst, &mut decls, fa);
    add_fact::file_decls(path, decls, fa);
    Ok(mod_xrefs)
}
