// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Add_fact` (`write_symbol_info/add_fact.ml`).
//!
//! Each function adds a fact to the accumulator `fa` and returns its id (the
//! OCaml returns `(id, fa)`). The functions that can raise `Failure` return
//! a `Result`.

use std::collections::BTreeMap;

use oxidized::aast;
use oxidized::aast_defs;
use oxidized::ast_defs;
use oxidized::pos::Pos;

use super::build_fact;
use super::glean::fact_id;
use super::glean::fbthrift;
use super::glean::gencode::gen_code;
use super::glean::gencode::gen_code_class;
use super::glean::gencode::gen_code_command;
use super::glean::gencode::gen_code_signature;
use super::glean::gencode::gen_code_variant;
use super::glean::hack::*;
use super::glean::src;
use super::glean::src::file_lines;
use super::glean::src::index_failure;
use super::glean::src::index_failure_reason;
use super::predicate;
use super::predicate::Failure;
use super::predicate::fact_acc;
use super::predicate::Hack;
use super::predicate::Src;
use super::predicate::T as P;
use super::pretty;
use super::util;
use super::xrefs;
use crate::full_fidelity_source_text;
use crate::hh_logger;
use crate::symbol_occurrence;
use crate::yojson::safe as yojson;

type Fa = fact_acc::T;

fn add(p: P, json: yojson::T, fa: &mut Fa) -> fact_id::T {
    fact_acc::add_fact(p, json, None, fa)
}

pub fn is_async(k: &ast_defs::FunKind) -> bool {
    match k {
        ast_defs::FunKind::FAsync => true,
        ast_defs::FunKind::FAsyncGenerator => true,
        _ => false,
    }
}

pub fn namespace_decl(name: &str, fa: &mut Fa) -> fact_id::T {
    let json = namespace_declaration::to_json_key(&namespace_declaration::Key {
        name: util::make_namespaceqname(name),
    });
    add(P::Hack(Hack::NamespaceDeclaration), json, fa)
}

/// create a namespace fact from a namespace attribute in node. Name can be empty
/// in that case we simply ignore it
pub fn namespace_decl_opt(name: &oxidized::namespace_env::Env, fa: &mut Fa) {
    match &name.name {
        None => {} // global name space
        Some(n) if n.is_empty() => {}
        Some(name) => {
            namespace_decl(name, fa);
        }
    }
}

pub fn container_decl_qname(decl_pred: P, qname: q_name::T, fa: &mut Fa) -> Result<fact_id::T, Failure> {
    let json = match decl_pred {
        P::Hack(Hack::ClassDeclaration) => class_declaration::to_json_key(&class_declaration::Key { name: qname }),
        P::Hack(Hack::EnumDeclaration) => enum_declaration::to_json_key(&enum_declaration::Key { name: qname }),
        P::Hack(Hack::InterfaceDeclaration) => {
            interface_declaration::to_json_key(&interface_declaration::Key { name: qname })
        }
        P::Hack(Hack::TraitDeclaration) => trait_declaration::to_json_key(&trait_declaration::Key { name: qname }),
        _ => return Err(Failure("Impossible has happened".to_string())),
    };
    Ok(add(decl_pred, json, fa))
}

/// (The OCaml conses the ids, and the callers use the list as it is: the
/// ids are in the reverse order of `decls`.)
fn parent_decls(decls: &[&aast_defs::ClassHint], pred: P, fa: &mut Fa) -> Result<Vec<fact_id::T>, Failure> {
    let mut decl_refs = vec![];
    for decl in decls {
        match util::class_hint_to_qname(decl) {
            Some(qname) => {
                let decl_id = container_decl_qname(pred, qname, fa)?;
                decl_refs.insert(0, decl_id)
            }
            None => {}
        }
    }
    Ok(decl_refs)
}

fn parent_decls_enum(decls: &[&aast_defs::ClassHint], fa: &mut Fa) -> Result<Vec<enum_declaration::T>, Failure> {
    let fact_ids = parent_decls(decls, P::Hack(Hack::EnumDeclaration), fa)?;
    Ok(fact_ids.into_iter().map(enum_declaration::T::Id).collect())
}

fn parent_decls_class(decls: &[&aast_defs::ClassHint], fa: &mut Fa) -> Result<Vec<class_declaration::T>, Failure> {
    let fact_ids = parent_decls(decls, P::Hack(Hack::ClassDeclaration), fa)?;
    Ok(fact_ids.into_iter().map(class_declaration::T::Id).collect())
}

fn parent_decls_trait(decls: &[&aast_defs::ClassHint], fa: &mut Fa) -> Result<Vec<trait_declaration::T>, Failure> {
    let fact_ids = parent_decls(decls, P::Hack(Hack::TraitDeclaration), fa)?;
    Ok(fact_ids.into_iter().map(trait_declaration::T::Id).collect())
}

fn parent_decls_interface(
    decls: &[&aast_defs::ClassHint],
    fa: &mut Fa,
) -> Result<Vec<interface_declaration::T>, Failure> {
    let fact_ids = parent_decls(decls, P::Hack(Hack::InterfaceDeclaration), fa)?;
    Ok(fact_ids.into_iter().map(interface_declaration::T::Id).collect())
}

pub fn module_decl(name: &str, fa: &mut Fa) -> fact_id::T {
    let json = module_declaration::to_json_key(&module_declaration::Key {
        name: util::make_name(name),
    });
    add(P::Hack(Hack::ModuleDeclaration), json, fa)
}

fn module_field(module_: &Option<ast_defs::Id>, internal: bool, fa: &mut Fa) -> Option<module_membership::T> {
    match module_ {
        None => None,
        Some(ast_defs::Id(_pos, module_name)) => {
            let decl_id = module_decl(module_name, fa);
            Some(build_fact::module_membership(decl_id, internal))
        }
    }
}

pub fn member_cluster(members: Vec<declaration::T>, fa: &mut Fa) -> fact_id::T {
    let json = member_cluster::to_json_key(&member_cluster::Key { members });
    add(P::Hack(Hack::MemberCluster), json, fa)
}

pub fn inherited_members(
    container_type: predicate::ParentContainerType,
    container_id: fact_id::T,
    member_clusters: &[fact_id::T],
    fa: &mut Fa,
) -> fact_id::T {
    let json = inherited_members::to_json_key(&inherited_members::Key {
        container: predicate::container_decl(container_type, container_id),
        inherited_members: member_clusters.iter().map(|x| member_cluster::T::Id(*x)).collect(),
    });
    add(P::Hack(Hack::InheritedMembers), json, fa)
}

pub fn property_decl(
    con_type: predicate::ParentContainerType,
    decl_id: fact_id::T,
    name: &str,
    fa: &mut Fa,
) -> fact_id::T {
    let json = property_declaration::to_json_key(&property_declaration::Key {
        name: util::make_name(name),
        container: predicate::container_decl(con_type, decl_id),
    });
    add(P::Hack(Hack::PropertyDeclaration), json, fa)
}

pub fn class_const_decl(
    con_type: predicate::ParentContainerType,
    decl_id: fact_id::T,
    name: &str,
    fa: &mut Fa,
) -> fact_id::T {
    let json = class_const_declaration::to_json_key(&class_const_declaration::Key {
        name: util::make_name(name),
        container: predicate::container_decl(con_type, decl_id),
    });
    add(P::Hack(Hack::ClassConstDeclaration), json, fa)
}

pub fn type_const_decl(
    con_type: predicate::ParentContainerType,
    decl_id: fact_id::T,
    name: &str,
    fa: &mut Fa,
) -> fact_id::T {
    let json = type_const_declaration::to_json_key(&type_const_declaration::Key {
        name: util::make_name(name),
        container: predicate::container_decl(con_type, decl_id),
    });
    add(P::Hack(Hack::TypeConstDeclaration), json, fa)
}

pub fn method_decl(
    con_type: predicate::ParentContainerType,
    decl_id: fact_id::T,
    name: &str,
    fa: &mut Fa,
) -> fact_id::T {
    let json = method_declaration::to_json_key(&method_declaration::Key {
        name: util::make_name(name),
        container: predicate::container_decl(con_type, decl_id),
    });
    add(P::Hack(Hack::MethodDeclaration), json, fa)
}

fn hint_to_type_info(hint: &aast::Hint, fa: &mut Fa) -> Result<(type_::T, type_info::T), Failure> {
    // `Map.Poly`: the targets in the order of the polymorphic compare, which
    // is that of the derived `Ord` of the schema types (none of them mixes
    // constant and non-constant constructors, where the two would differ).
    let aggregate_pos =
        |json_pos_list: Vec<(x_ref_target::T, pretty::Pos)>| -> Vec<(x_ref_target::T, Vec<pretty::Pos>)> {
            let mut jmap: BTreeMap<x_ref_target::T, Vec<pretty::Pos>> = BTreeMap::new();
            for (json, pos) in json_pos_list {
                // `pos :: prev`
                jmap.entry(json).or_default().insert(0, pos)
            }
            jmap.into_iter().collect()
        };
    let type_info = |ty: &str, sym_pos, hint, fa: &mut Fa| {
        let json = type_info::to_json_key(&type_info::Key {
            display_type: type_::T::key(crate::utils::strip_ns(ty).to_string()),
            xrefs: build_fact::hint_xrefs(sym_pos),
            hint: Some(hint),
        });
        add(P::Hack(Hack::TypeInfo), json, fa)
    };
    let (ty, sym_pos) = pretty::hint_to_string_and_symbols(false, hint);
    let hint = pretty::hint_to_angle(hint);
    let pos_map = match fact_acc::get_pos_map(fa) {
        Some(pos_map) => pos_map,
        None => {
            return Err(Failure(
                "Internal error: pos_map should be set in previous phase".to_string(),
            ));
        }
    };
    let decl_json_pos: Vec<(x_ref_target::T, pretty::Pos)> = sym_pos
        .into_iter()
        .filter_map(|(source_pos, pos)| {
            xrefs::pos_map_find_first(pos_map, &source_pos).map(|ti| (ti.target.clone(), pos))
        })
        .collect();
    let decl_json_aggr_pos = aggregate_pos(decl_json_pos);
    let fact_id = type_info(&ty, decl_json_aggr_pos, hint, fa);
    Ok((type_::T::key(ty), type_info::T::Id(fact_id)))
}

fn hint_opt_to_type_info(
    fa: &mut Fa,
    h: &Option<aast::Hint>,
) -> Result<(Option<type_::T>, Option<type_info::T>), Failure> {
    match h {
        None => Ok((None, None)),
        Some(type_) => {
            let (ty, ty_info) = hint_to_type_info(type_, fa)?;
            Ok((Some(ty), Some(ty_info)))
        }
    }
}

fn type_param<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    tp: &aast::Tparam<Ex, En>,
    fa: &mut Fa,
) -> Result<type_parameter::T, Failure> {
    let constraint_ = |(kind, hint): &(ast_defs::ConstraintKind, aast::Hint), fa: &mut Fa| {
        let (type_, type_info) = hint_to_type_info(hint, fa)?;
        Ok(constraint::T {
            constraint_kind: util::make_constraint_kind(kind),
            type_,
            type_info: Some(type_info),
        })
    };
    let ast_defs::Id(_, name) = &tp.name;
    let name = util::make_name(name);
    let mut constraints = vec![];
    for cst in &tp.constraints {
        constraints.push(constraint_(cst, fa)?);
    }
    Ok(type_parameter::T {
        name,
        variance: util::make_variance(&tp.variance),
        reify_kind: util::make_reify_kind(&tp.reified),
        constraints,
        attributes: build_fact::attributes(source_text, &tp.user_attributes),
    })
}

fn type_params<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    params: &[aast::Tparam<Ex, En>],
    fa: &mut Fa,
) -> Result<Vec<type_parameter::T>, Failure> {
    let mut type_params = vec![];
    for param in params {
        type_params.push(type_param(source_text, param, fa)?);
    }
    Ok(type_params)
}

pub fn container_defn<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    clss: &aast::Class_<Ex, En>,
    decl_id: fact_id::T,
    members: Vec<declaration::T>,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    namespace_decl_opt(&clss.namespace, fa);
    let type_params = type_params(source_text, &clss.tparams, fa)?;
    let module_ = module_field(&clss.module, clss.internal, fa);
    let attributes = build_fact::attributes(source_text, &clss.user_attributes);
    // T207902686: add Glean support for experimental require this as C constraints
    // (`Aast.partition_map_require_kind ~f:(fun x -> x)`, then `fst` of each.)
    let mut req_extends_hints = vec![];
    let mut req_implements_hints = vec![];
    let mut req_class_hints = vec![];
    let mut req_this_as_hints = vec![];
    for aast::ClassReq(h, kind) in &clss.reqs {
        match kind {
            aast::RequireKind::RequireExtends => req_extends_hints.push(h),
            aast::RequireKind::RequireImplements => req_implements_hints.push(h),
            aast::RequireKind::RequireClass => req_class_hints.push(h),
            aast::RequireKind::RequireThisAs => req_this_as_hints.push(h),
        }
    }
    let require_extends = parent_decls_class(&req_extends_hints, fa)?;
    let require_implements = parent_decls_interface(&req_implements_hints, fa)?;
    let require_class = parent_decls_class(&req_class_hints, fa)?;
    let require_this_as = parent_decls_class(&req_this_as_hints, fa)?;
    fn refs(l: &[aast::Hint]) -> Vec<&aast::Hint> {
        l.iter().collect()
    }
    match predicate::get_parent_kind(&clss.kind)? {
        predicate::ParentContainerType::InterfaceContainer => {
            let extends_ = parent_decls_interface(&refs(&clss.extends), fa)?;
            let json = interface_definition::to_json_key(&interface_definition::Key {
                declaration: interface_declaration::T::Id(decl_id),
                type_params,
                members,
                attributes,
                extends_,
                require_extends,
                module_,
            });
            Ok(add(P::Hack(Hack::InterfaceDefinition), json, fa))
        }
        predicate::ParentContainerType::TraitContainer => {
            let implements_ = parent_decls_interface(&refs(&clss.implements), fa)?;
            let uses = parent_decls_trait(&refs(&clss.uses), fa)?;
            let json = trait_definition::to_json_key(&trait_definition::Key {
                declaration: trait_declaration::T::Id(decl_id),
                members,
                implements_,
                uses,
                attributes,
                type_params,
                require_extends,
                require_implements,
                require_class: Some(require_class),
                require_this_as,
                module_,
            });
            Ok(add(P::Hack(Hack::TraitDefinition), json, fa))
        }
        predicate::ParentContainerType::ClassContainer => {
            let implements_ = parent_decls_interface(&refs(&clss.implements), fa)?;
            let uses = parent_decls_trait(&refs(&clss.uses), fa)?;
            let extends_ = match clss.extends.as_slice() {
                [] => None,
                [parent] => match util::class_hint_to_qname(parent) {
                    Some(qname) => {
                        let decl_id = {
                            let json = class_declaration::to_json_key(&class_declaration::Key { name: qname });
                            add(P::Hack(Hack::ClassDeclaration), json, fa)
                        };
                        Some(class_declaration::T::Id(decl_id))
                    }
                    None => None,
                },
                _ => {
                    hh_logger::log(&format!(
                        "WARNING: skipping extends field for class with multiple parents {}",
                        clss.name.1
                    ));
                    None
                }
            };
            let json = class_definition::to_json_key(&class_definition::Key {
                declaration: class_declaration::T::Id(decl_id),
                is_abstract: crate::ast_defs::is_classish_abstract(clss.kind),
                is_final: clss.final_,
                members,
                extends_,
                implements_,
                uses,
                attributes,
                type_params,
                module_,
            });
            Ok(add(P::Hack(Hack::ClassDefinition), json, fa))
        }
    }
}

fn build_signature<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    params: &[aast::FunParam<Ex, En>],
    ctxs: &Option<aast::Contexts>,
    ret: &aast::TypeHint<Ex>,
    fa: &mut Fa,
) -> Result<signature::T, Failure> {
    let mut t_params = vec![];
    for p in params {
        let (type_, type_info) = hint_opt_to_type_info(fa, crate::aast::hint_of_type_hint(&p.type_hint))?;
        t_params.push((p, type_info, type_));
    }
    let (returns, returns_type_info) = hint_opt_to_type_info(fa, crate::aast::hint_of_type_hint(ret))?;
    let signature = build_fact::signature(source_text, t_params, ctxs.as_ref(), returns, returns_type_info);
    Ok(signature)
}

pub fn method_defn<Ex: Clone, En: Clone>(
    source_text: &full_fidelity_source_text::T,
    meth: &aast::Method_<Ex, En>,
    decl_id: fact_id::T,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    let m_tparams = util::remove_generated_tparams(&meth.tparams);
    let type_params = type_params(source_text, &m_tparams, fa)?;
    let signature = build_signature(source_text, &meth.params, &meth.ctxs, &meth.ret, fa)?;
    let readonly_ret = meth.readonly_ret.as_ref().map(|_| readonly_kind::T::Readonly);
    let is_readonly_this = if meth.readonly_this {
        Some(meth.readonly_this)
    } else {
        None
    };
    let json = method_definition::to_json_key(&method_definition::Key {
        declaration: method_declaration::T::Id(decl_id),
        signature,
        visibility: util::make_visibility(&meth.visibility),
        is_abstract: meth.abstract_,
        is_async: is_async(&meth.fun_kind),
        is_final: meth.final_,
        is_static: meth.static_,
        attributes: build_fact::attributes(source_text, &meth.user_attributes),
        type_params,
        readonly_ret,
        is_readonly_this,
    });
    Ok(add(P::Hack(Hack::MethodDefinition), json, fa))
}

pub fn method_overrides(
    annotation: bool,
    meth_name: &str,
    base_cont_name: &str,
    base_cont_type: predicate::ParentContainerType,
    der_cont_name: &str,
    der_cont_type: predicate::ParentContainerType,
    fa: &mut Fa,
) -> fact_id::T {
    let json = method_overrides::to_json_key(&method_overrides::Key {
        annotation: Some(annotation),
        derived: build_fact::method_decl(meth_name, der_cont_name, der_cont_type),
        base: build_fact::method_decl(meth_name, base_cont_name, base_cont_type),
    });
    add(P::Hack(Hack::MethodOverrides), json, fa)
}

pub fn property_defn<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    prop: &aast::ClassVar<Ex, En>,
    decl_id: fact_id::T,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    let (type_, type_info) = hint_opt_to_type_info(fa, crate::aast::hint_of_type_hint(&prop.type_))?;
    let json = property_definition::to_json_key(&property_definition::Key {
        declaration: property_declaration::T::Id(decl_id),
        type_,
        visibility: util::make_visibility(&prop.visibility),
        is_final: prop.final_,
        is_abstract: prop.abstract_,
        is_static: prop.is_static,
        attributes: build_fact::attributes(source_text, &prop.user_attributes),
        type_info,
    });
    Ok(add(P::Hack(Hack::PropertyDefinition), json, fa))
}

pub fn class_const_defn<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    const_: &aast::ClassConst<Ex, En>,
    decl_id: fact_id::T,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    let value = match &const_.kind {
        aast::ClassConstKind::CCAbstract(None) => None,
        aast::ClassConstKind::CCAbstract(Some(expr)) | aast::ClassConstKind::CCConcrete(expr) => {
            Some(pretty::expr_to_string(source_text, expr))
        }
    };
    let (type_, type_info) = hint_opt_to_type_info(fa, &const_.type_)?;
    let json = class_const_definition::to_json_key(&class_const_definition::Key {
        declaration: class_const_declaration::T::Id(decl_id),
        type_,
        value,
        type_info,
    });
    Ok(add(P::Hack(Hack::ClassConstDefinition), json, fa))
}

pub fn type_const_defn<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    tc: &aast::ClassTypeconstDef<Ex, En>,
    decl_id: fact_id::T,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    // TODO(T88552052) should the default of an abstract type constant be used
    // as a value here
    let (type_, type_info) = match &tc.kind {
        aast::ClassTypeconst::TCConcrete(aast::ClassConcreteTypeconst { c_tc_type: h })
        | aast::ClassTypeconst::TCAbstract(aast::ClassAbstractTypeconst { default: Some(h), .. }) => {
            let (x, y) = hint_to_type_info(h, fa)?;
            (Some(x), Some(y))
        }
        aast::ClassTypeconst::TCAbstract(aast::ClassAbstractTypeconst { default: None, .. }) => (None, None),
    };
    let json = type_const_definition::to_json_key(&type_const_definition::Key {
        declaration: type_const_declaration::T::Id(decl_id),
        kind: util::make_type_const_kind(&tc.kind),
        type_,
        attributes: build_fact::attributes(source_text, &tc.user_attributes),
        type_info,
    });
    Ok(add(P::Hack(Hack::TypeConstDefinition), json, fa))
}

pub fn enum_decl(name: &str, fa: &mut Fa) -> fact_id::T {
    let json = enum_declaration::to_json_key(&enum_declaration::Key {
        name: util::make_qname(name),
    });
    add(P::Hack(Hack::EnumDeclaration), json, fa)
}

pub fn enum_defn<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    enm: &aast::Class_<Ex, En>,
    enum_id: fact_id::T,
    enum_data: &aast::Enum_,
    enumerators: &[fact_id::T],
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    let enumerators = enumerators.iter().map(|x| enumerator::T::Id(*x)).collect();
    namespace_decl_opt(&enm.namespace, fa);
    let includes = parent_decls_enum(&enum_data.includes.iter().collect::<Vec<_>>(), fa)?;
    let module_ = module_field(&enm.module, enm.internal, fa);
    let (enum_base, enum_base_type_info) = hint_to_type_info(&enum_data.base, fa)?;
    let (enum_constraint, enum_constraint_type_info) = hint_opt_to_type_info(fa, &enum_data.constraint)?;
    let json = enum_definition::to_json_key(&enum_definition::Key {
        declaration: enum_declaration::T::Id(enum_id),
        enum_base,
        enumerators,
        attributes: build_fact::attributes(source_text, &enm.user_attributes),
        includes,
        is_enum_class: matches!(enm.kind, ast_defs::ClassishKind::CenumClass(_)),
        module_,
        enum_constraint,
        enum_constraint_type_info,
        enum_base_type_info: Some(enum_base_type_info),
    });
    Ok(add(P::Hack(Hack::EnumDefinition), json, fa))
}

pub fn enumerator(decl_id: fact_id::T, const_name: &str, fa: &mut Fa) -> fact_id::T {
    let json = enumerator::to_json_key(&enumerator::Key {
        name: util::make_name(const_name),
        enumeration: enum_declaration::T::Id(decl_id),
    });
    add(P::Hack(Hack::Enumerator), json, fa)
}

pub fn func_decl(name: &str, fa: &mut Fa) -> fact_id::T {
    let json = function_declaration::to_json_key(&function_declaration::Key {
        name: util::make_qname(name),
    });
    add(P::Hack(Hack::FunctionDeclaration), json, fa)
}

pub fn func_defn<Ex: Clone, En: Clone>(
    source_text: &full_fidelity_source_text::T,
    fd: &aast::FunDef<Ex, En>,
    decl_id: fact_id::T,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    let elem = &fd.fun;
    namespace_decl_opt(&fd.namespace, fa);
    let fd_tparams = util::remove_generated_tparams(&fd.tparams);
    let type_params = type_params(source_text, &fd_tparams, fa)?;
    let module_ = module_field(&fd.module, fd.internal, fa);
    let signature = build_signature(source_text, &elem.params, &elem.ctxs, &elem.ret, fa)?;
    let readonly_ret = elem.readonly_ret.as_ref().map(|_| readonly_kind::T::Readonly);
    let json = function_definition::to_json_key(&function_definition::Key {
        declaration: function_declaration::T::Id(decl_id),
        signature,
        is_async: is_async(&elem.fun_kind),
        is_closure: false,
        attributes: build_fact::attributes(source_text, &elem.user_attributes),
        type_params,
        readonly_ret,
        module_,
    });
    Ok(add(P::Hack(Hack::FunctionDefinition), json, fa))
}

pub fn closure_defn<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    elem: &aast::Fun_<Ex, En>,
    decl_id: fact_id::T,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    let signature = build_signature(source_text, &elem.params, &elem.ctxs, &elem.ret, fa)?;
    let readonly_ret = elem.readonly_ret.as_ref().map(|_| readonly_kind::T::Readonly);
    let json = function_definition::to_json_key(&function_definition::Key {
        declaration: function_declaration::T::Id(decl_id),
        signature,
        is_async: is_async(&elem.fun_kind),
        is_closure: true,
        attributes: build_fact::attributes(source_text, &elem.user_attributes),
        type_params: vec![],
        readonly_ret,
        module_: None,
    });
    Ok(add(P::Hack(Hack::FunctionDefinition), json, fa))
}

pub fn module_defn<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    elem: &aast::ModuleDef<Ex, En>,
    decl_id: fact_id::T,
    fa: &mut Fa,
) -> fact_id::T {
    let json = module_definition::to_json_key(&module_definition::Key {
        declaration: module_declaration::T::Id(decl_id),
        attributes: build_fact::attributes(source_text, &elem.user_attributes),
    });
    add(P::Hack(Hack::ModuleDefinition), json, fa)
}

pub fn typedef_decl(name: &str, fa: &mut Fa) -> fact_id::T {
    let json = typedef_declaration::to_json_key(&typedef_declaration::Key {
        name: util::make_qname(name),
    });
    add(P::Hack(Hack::TypedefDeclaration), json, fa)
}

pub fn typedef_defn<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    elem: &aast::Typedef<Ex, En>,
    decl_id: fact_id::T,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    namespace_decl_opt(&elem.namespace, fa);
    let is_transparent = match &elem.assignment {
        aast::TypedefAssignment::SimpleTypeDef(aast::TypedefVisibilityAndHint {
            vis: ast_defs::TypedefVisibility::Transparent,
            hint: _,
        }) => true,
        aast::TypedefAssignment::SimpleTypeDef(aast::TypedefVisibilityAndHint {
            vis: ast_defs::TypedefVisibility::Opaque,
            hint: _,
        })
        | aast::TypedefAssignment::SimpleTypeDef(aast::TypedefVisibilityAndHint {
            vis: ast_defs::TypedefVisibility::OpaqueModule,
            hint: _,
        })
        | aast::TypedefAssignment::CaseType(..) => false,
    };
    let type_params = type_params(source_text, &elem.tparams, fa)?;
    let module_ = module_field(&elem.module, elem.internal, fa);
    let json = typedef_definition::to_json_key(&typedef_definition::Key {
        declaration: typedef_declaration::T::Id(decl_id),
        is_transparent,
        attributes: build_fact::attributes(source_text, &elem.user_attributes),
        type_params,
        module_,
    });
    Ok(add(P::Hack(Hack::TypedefDefinition), json, fa))
}

pub fn gconst_decl(name: &str, fa: &mut Fa) -> fact_id::T {
    let json = global_const_declaration::to_json_key(&global_const_declaration::Key {
        name: util::make_qname(name),
    });
    add(P::Hack(Hack::GlobalConstDeclaration), json, fa)
}

pub fn gconst_defn<Ex, En>(
    source_text: &full_fidelity_source_text::T,
    elem: &aast::Gconst<Ex, En>,
    decl_id: fact_id::T,
    fa: &mut Fa,
) -> Result<fact_id::T, Failure> {
    namespace_decl_opt(&elem.namespace, fa);
    let value = pretty::expr_to_string(source_text, &elem.value);
    let (type_, type_info) = hint_opt_to_type_info(fa, &elem.type_)?;
    let json = global_const_definition::to_json_key(&global_const_definition::Key {
        declaration: global_const_declaration::T::Id(decl_id),
        type_,
        value,
        type_info,
    });
    Ok(add(P::Hack(Hack::GlobalConstDefinition), json, fa))
}

pub fn decl_loc(path: &str, pos: &Pos, declaration: declaration::T, fa: &mut Fa) -> fact_id::T {
    decl_loc_of_byte_span(path, util::make_byte_span(pos), declaration, fa)
}

/// `decl_loc` of a span (Rust-only: the span of a namespace declaration
/// has the OCaml's offsets, see `Util.NamespacePos`).
pub fn decl_loc_of_byte_span(path: &str, span: src::byte_span::T, declaration: declaration::T, fa: &mut Fa) -> fact_id::T {
    let json = declaration_location::to_json_key(&declaration_location::Key {
        declaration,
        file: src::file::T::key(path.to_string()),
        span,
    });
    add(P::Hack(Hack::DeclarationLocation), json, fa)
}

pub fn decl_comment(path: &str, pos: &Pos, declaration: declaration::T, fa: &mut Fa) -> fact_id::T {
    let json = declaration_comment::to_json_key(&declaration_comment::Key {
        declaration,
        file: src::file::T::key(path.to_string()),
        span: util::make_byte_span(pos),
    });
    add(P::Hack(Hack::DeclarationComment), json, fa)
}

pub fn decl_span(path: &str, pos: &Pos, declaration: declaration::T, fa: &mut Fa) -> fact_id::T {
    decl_span_of_byte_span(path, util::make_byte_span(pos), declaration, fa)
}

/// `decl_span` of a span (Rust-only, as [`decl_loc_of_byte_span`]).
pub fn decl_span_of_byte_span(path: &str, span: src::byte_span::T, declaration: declaration::T, fa: &mut Fa) -> fact_id::T {
    let json = declaration_span::to_json_key(&declaration_span::Key {
        declaration,
        file: src::file::T::key(path.to_string()),
        span,
    });
    add(P::Hack(Hack::DeclarationSpan), json, fa)
}

pub fn index_failure(path: &str, reason: index_failure_reason::T, details: String, fa: &mut Fa) -> fact_id::T {
    let json = index_failure::to_json_key(&index_failure::Key {
        file: src::file::T::key(path.to_string()),
        reason,
        details,
    });
    add(P::Src(Src::IndexFailure), json, fa)
}

pub fn file_lines(path: &str, source_text: &full_fidelity_source_text::T, fa: &mut Fa) -> fact_id::T {
    let lengths = full_fidelity_source_text::offsets_to_line_lengths(&full_fidelity_source_text::offset_map(source_text));
    let ends_in_newline = util::ends_in_newline(source_text);
    let has_unicode_or_tabs = util::has_tabs_or_multibyte_codepoints(source_text);
    let json = file_lines::to_json_key(&file_lines::Key {
        file: src::file::T::key(path.to_string()),
        lengths,
        ends_in_newline,
        has_unicode_or_tabs,
    });
    add(P::Src(Src::FileLines), json, fa)
}

pub fn file_xrefs(path: &str, fact_map: &xrefs::FactMap, fa: &mut Fa) -> fact_id::T {
    let json = file_x_refs::to_json_key(&file_x_refs::Key {
        file: src::file::T::key(path.to_string()),
        xrefs: build_fact::xrefs(fact_map),
    });
    add(P::Hack(Hack::FileXRefs), json, fa)
}

pub fn file_decls(path: &str, declarations: Vec<declaration::T>, fa: &mut Fa) -> fact_id::T {
    let json = file_declarations::to_json_key(&file_declarations::Key {
        file: src::file::T::key(path.to_string()),
        declarations,
    });
    add(P::Hack(Hack::FileDeclarations), json, fa)
}

pub fn method_occ(receiver_class: &symbol_occurrence::ReceiverClass, name: &str, fa: &mut Fa) -> fact_id::T {
    let json = method_occurrence::to_json_key(&method_occurrence::Key {
        name: util::make_name(name),
        class_name: match receiver_class {
            symbol_occurrence::ReceiverClass::UnknownClass => None,
            symbol_occurrence::ReceiverClass::ClassName(class_name) => Some(util::make_name(class_name)),
        },
    });
    add(P::Hack(Hack::MethodOccurrence), json, fa)
}

pub fn file_call(
    path: &str,
    pos: &Pos,
    callee_infos: &[xrefs::TargetInfo],
    call_args: Vec<call_argument::T>,
    dispatch_arg: Option<call_argument::T>,
    fa: &mut Fa,
) -> fact_id::T {
    let callee_xrefs: Vec<x_ref_target::T> = callee_infos.iter().map(|ti| ti.target.clone()).collect();
    let callee_xref = {
        let mut sorted = callee_xrefs.clone();
        sorted.sort();
        sorted.into_iter().next()
    };
    let receiver_type = callee_infos.iter().find_map(|ti| ti.receiver_type.clone());
    let json = file_call::to_json_key(&file_call::Key {
        file: src::file::T::key(path.to_string()),
        callee_span: util::make_byte_span(pos),
        callee_xref,
        dispatch_arg,
        receiver_type,
        call_args,
        callee_xrefs,
    });
    add(P::Hack(Hack::FileCall), json, fa)
}

pub fn global_namespace_alias(from: &str, to_: &str, fa: &mut Fa) -> fact_id::T {
    let json = global_namespace_alias::to_json_key(&global_namespace_alias::Key {
        from: name::T::key(from.to_string()),
        to_: util::make_namespaceqname(to_),
    });
    add(P::Hack(Hack::GlobalNamespaceAlias), json, fa)
}

pub fn indexer_inputs_hash(key: &str, hashes: &[[u8; 16]], fa: &mut Fa) -> fact_id::T {
    let key = indexer_inputs_hash::to_json_key(&key.to_string());
    let value = indexer_inputs_hash::to_json_value(&hashes.iter().map(|h| h.to_vec()).collect());
    fact_acc::add_fact(P::Hack(Hack::IndexerInputsHash), key, Some(value), fa)
}

pub fn gen_code(
    path: &str,
    fully_generated: bool,
    signature: &Option<String>,
    source: &Option<String>,
    command: &Option<String>,
    class_: &Option<String>,
    fa: &mut Fa,
) -> fact_id::T {
    let json = gen_code::to_json_key(&gen_code::Key {
        file: src::file::T::key(path.to_string()),
        variant: if fully_generated {
            gen_code_variant::T::Full
        } else {
            gen_code_variant::T::Partial
        },
        source: source.as_ref().map(|x| src::file::T::key(x.clone())),
        signature: signature.as_ref().map(|x| gen_code_signature::T::key(x.clone())),
        command: command.as_ref().map(|x| gen_code_command::T::key(x.clone())),
        class_: class_.as_ref().map(|x| gen_code_class::T::key(x.clone())),
    });
    add(P::Gencode(predicate::Gencode::GenCode), json, fa)
}

pub fn hack_to_thrift(hack: declaration::T, thrift: fbthrift::declaration::T, fa: &mut Fa) {
    let json = hack_to_thrift::to_json_key(&hack_to_thrift::Key { from: hack, to_: thrift });
    add(P::Hack(Hack::HackToThrift), json, fa);
}

pub fn container_decl(decl_pred: P, name: &str, fa: &mut Fa) -> Result<fact_id::T, Failure> {
    let qname = util::make_qname(name);
    container_decl_qname(decl_pred, qname, fa)
}

pub fn file_package(path: &str, package_: package_::T, has_package_override: bool, fa: &mut Fa) -> fact_id::T {
    let json = file_package::to_json_key(&file_package::Key {
        file: src::file::T::key(path.to_string()),
        package_,
        has_package_override,
    });
    add(P::Hack(Hack::FilePackage), json, fa)
}

pub fn target_not_used_in_prod_build(target: x_ref_target::T, file: src::file::T, fa: &mut Fa) -> fact_id::T {
    let json = target_not_used_in_prod_build::to_json_key(&target_not_used_in_prod_build::Key { target, file });
    add(P::Hack(Hack::TargetNotUsedInProdBuild), json, fa)
}
