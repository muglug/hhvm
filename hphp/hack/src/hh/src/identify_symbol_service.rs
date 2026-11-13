// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/identify_symbol_service.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F1** (plan §7.3).
//!
//! `Result_set` (a `Set.Make` over `Symbol_occurrence.compare
//! Relative_path.compare`) is a `BTreeSet` of [`Occ`], whose `Ord` is that
//! comparison: [`Result_set.elements`] is the set in increasing order, as in
//! OCaml.
//!
//! The visitor inherits from `Tast_visitor.reduce` with `zero` the empty set
//! and `plus` the union: as the union is commutative and idempotent, the
//! visitor adds what each visit finds to its accumulator; where the OCaml
//! changes the result of some visits (`set_affects_prod_build_false`), the
//! result of those visits is computed apart (`reduce::result`). The state the
//! OCaml keeps in `ref`s of the object is in fields of the visitor.
//!
//! The OCaml visits records that it rebuilds (`{ fun_ with f_unsafe_ctxs =
//! None }`, the enums without their generated `extends`, the expression that
//! `Server_utils.resugar_invariant_call` makes): the visitor has no lifetime of
//! its own, so it visits these temporaries too. For `f_unsafe_ctxs` (on every
//! function and method) it skips the visit of those contexts instead of
//! copying the function: the same nodes are visited.
//!
//! The CST of `all_symbols_ctx` (`Ast_provider.compute_cst`, cached in
//! `entry.cst`, and the cache `entry.symbols`) is not in `Provider_context`
//! yet: [`compute_cst`] parses the entry as `PositionedSyntaxTree.make` does
//! (default parser environment), and the symbols are recomputed at each call.
//! Neither difference can be observed.

#![allow(non_snake_case)]

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs;
use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::lexable_token::LexableToken;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::positioned_token::PositionedToken;
use parser_core_types::positioned_trivia::PositionedTrivium;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::syntax_trait::SyntaxTrait;
use parser_core_types::token_kind::TokenKind;
use parser_core_types::trivia_kind::TriviaKind;

use crate::aast_utils;
use crate::ast_provider;
use crate::decl_entry;
use crate::diagnostics_state;
use crate::file_content;
use crate::full_fidelity_source_text;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path;
use crate::symbol_occurrence;
use crate::symbol_occurrence::BuiltInTypeHint;
use crate::symbol_occurrence::ClassIdType;
use crate::symbol_occurrence::Kind;
use crate::symbol_occurrence::KeywordWithHoverDocs;
use crate::symbol_occurrence::OverrideInfo;
use crate::symbol_occurrence::Receiver;
use crate::symbol_occurrence::ReceiverClass;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor;
use crate::tast_visitor::IterParams;
use crate::tast_visitor::Reduce;
use crate::tast_visitor::reduce;
use crate::typing_defs;
use crate::typing_defs::Ty_;

type Res = Result<(), ()>;

/// `Relative_path.t Symbol_occurrence.t`
pub type Elt = symbol_occurrence::T<Pos>;

/// An element of [`ResultSet`]: ordered by `Symbol_occurrence.compare
/// Relative_path.compare`.
#[derive(Clone, Debug)]
pub struct Occ(pub Elt);

impl PartialEq for Occ {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Occ {}

impl PartialOrd for Occ {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Occ {
    fn cmp(&self, other: &Self) -> Ordering {
        symbol_occurrence::compare(relative_path::compare, &self.0, &other.0)
    }
}

/// `Result_set.t`
pub type ResultSet = BTreeSet<Occ>;

/// `Result_set.singleton`
fn singleton(x: Elt) -> ResultSet {
    let mut s = ResultSet::new();
    s.insert(Occ(x));
    s
}

/// `Result_set.union`
fn union(mut a: ResultSet, b: ResultSet) -> ResultSet {
    if a.len() < b.len() {
        let mut b = b;
        b.append(&mut a);
        b
    } else {
        let mut b = b;
        a.append(&mut b);
        a
    }
}

/// `Result_set.elements`
fn elements(s: ResultSet) -> Vec<Elt> {
    s.into_iter().map(|Occ(x)| x).collect()
}

fn is_target(
    use_declaration_spans: bool,
    cursor: &file_content::position::T,
    occ: &Elt,
) -> bool {
    let pos = match (use_declaration_spans, &occ.is_declaration) {
        (true, Some(pos)) => pos,
        (true, None) | (false, _) => &occ.pos,
    };
    let (target_line, target_char) = file_content::position::line_column_one_based(cursor);
    if use_declaration_spans {
        crate::pos::inside_one_based(pos, target_line, target_char)
    } else {
        let (l, start, end_) = crate::pos::info_pos(pos);
        l == target_line
            && start <= target_char
            // Two facts explain the following line:
            //  - [start, end_] form a closed interval. This explains the `<=`
            //  - The cursor might be right at the end of a symbol span, e.g. `myvar|`,
            //    and in that case we still want to consider the symbol as "target".
            //    This explains the `- 1`
            && target_char - 1 <= end_
    }
}

fn process_class_id(
    is_declaration: Option<Pos>,
    class_id_type: Option<ClassIdType>,
    affects_prod_build: Option<bool>,
    (pos, cid): (&Pos, &str),
) -> ResultSet {
    let class_id_type = class_id_type.unwrap_or(ClassIdType::ClassId);
    let affects_prod_build = affects_prod_build.unwrap_or(true);
    singleton(symbol_occurrence::T {
        name: cid.to_string(),
        type_: Kind::Class(class_id_type),
        is_declaration,
        pos: pos.clone(),
        affects_prod_build,
    })
}

fn process_sid(sid: &aast::Sid) -> ResultSet {
    process_class_id(None, None, None, (&sid.0, &sid.1))
}

fn process_attribute(
    (pos, name): (&Pos, &str),
    class_name: Option<&aast::Sid>,
    method_: Option<&(aast::Sid, bool)>,
) -> ResultSet {
    let type_ = match (name, class_name, method_) {
        (name, Some(ast_defs::Id(_, class_name)), Some((ast_defs::Id(_, method_name), is_static)))
            if name == sn::user_attributes::OVERRIDE =>
        {
            Kind::Attribute(Some(OverrideInfo {
                class_name: class_name.clone(),
                method_name: method_name.clone(),
                is_static: *is_static,
            }))
        }
        _ => Kind::Attribute(None),
    };
    singleton(symbol_occurrence::T {
        name: name.to_string(),
        type_,
        is_declaration: None,
        pos: pos.clone(),
        affects_prod_build: true,
    })
}

fn process_xml_attrs(class_name: &str, attrs: &[aast::XhpAttribute<tast::Ty, tast::SavedEnv>]) -> ResultSet {
    let mut acc = ResultSet::new();
    for attr in attrs {
        match attr {
            aast::XhpAttribute::XhpSimple(aast::XhpSimple {
                name: (pos, name), ..
            }) => {
                acc.insert(Occ(symbol_occurrence::T {
                    name: name.clone(),
                    type_: Kind::XhpLiteralAttr(class_name.to_string(), crate::utils::add_xhp_ns(name)),
                    is_declaration: None,
                    pos: pos.clone(),
                    affects_prod_build: true,
                }));
            }
            _ => {}
        }
    }
    acc
}

pub fn clean_member_name(name: &str) -> String {
    crate::string_utils::lstrip(name, "$").to_string()
}

/// `` [ `Const | `Method | `EnumClassLabel | `Property ] ``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MemberKind {
    Const,
    Method,
    EnumClassLabel,
    Property,
}

fn process_member(
    is_declaration: Option<Pos>,
    recv_class: ReceiverClass,
    id: (&Pos, &str),
    kind: MemberKind,
) -> ResultSet {
    let member_name = id.1;
    let type_ = match kind {
        MemberKind::Const => Some(Kind::ClassConst(recv_class.clone(), member_name.to_string())),
        MemberKind::Method => Some(Kind::Method(recv_class.clone(), member_name.to_string())),
        MemberKind::EnumClassLabel => match &recv_class {
            ReceiverClass::ClassName(cls) => {
                Some(Kind::EnumClassLabel(cls.clone(), member_name.to_string()))
            }
            ReceiverClass::UnknownClass => None,
        },
        // Per comment in symbolOccurrence.mli, XhpLiteralAttr
        // is only used for attributes in XHP literals. Since
        // process_member is not being used to handle XML attributes
        // it is fine to define every symbol as Property.
        MemberKind::Property => Some(Kind::Property(recv_class.clone(), member_name.to_string())),
    };
    let c_name = match &recv_class {
        ReceiverClass::ClassName(name) => name.as_str(),
        ReceiverClass::UnknownClass => "_",
    };
    match type_ {
        None => ResultSet::new(),
        Some(type_) => {
            let delimiter = match kind {
                MemberKind::EnumClassLabel => "#",
                _ => "::",
            };
            singleton(symbol_occurrence::T {
                name: format!("{}{}{}", c_name, delimiter, clean_member_name(member_name)),
                type_,
                is_declaration,
                pos: id.0.clone(),
                affects_prod_build: true,
            })
        }
    }
}

/// If there's an exact class name can find for this type, return its name.
fn concrete_cls_name_from_ty(enclosing_class_name: Option<&str>, ty: &tast::Ty) -> Option<String> {
    let ty = match typing_defs::get_node(ty) {
        Ty_::Tnewtype(n, tys, _) if tys.len() == 1 && n == sn::classes::SUPPORT_DYN => &tys[0],
        _ => ty,
    };
    match typing_defs::get_node(ty) {
        Ty_::Tclass((_, cls_name), _, _) => Some(cls_name.clone()),
        Ty_::Tgeneric(name) if name == "this" => enclosing_class_name.map(|s| s.to_string()),
        _ => None,
    }
}

fn get_callee(enclosing_class_name: Option<&str>, recv: &tast::Expr) -> Option<Receiver> {
    let aast::Expr(_, _, recv_expr_) = recv;
    match recv_expr_ {
        aast::Expr_::Id(id) => Some(Receiver::FunctionReceiver(id.1.clone())),
        aast::Expr_::ClassConst(cc) => {
            let (aast::ClassId(ty, _, _), (_, meth_name)) = &**cc;
            match concrete_cls_name_from_ty(enclosing_class_name, ty) {
                Some(cls_name) => Some(Receiver::MethodReceiver {
                    cls_name,
                    meth_name: meth_name.clone(),
                    is_static: true,
                }),
                None => None,
            }
        }
        aast::Expr_::ObjGet(og) => match &**og {
            (aast::Expr(ty, _, _), aast::Expr(_, _, aast::Expr_::Id(meth_name)), _, _) => {
                match concrete_cls_name_from_ty(enclosing_class_name, ty) {
                    Some(cls_name) => Some(Receiver::MethodReceiver {
                        cls_name,
                        meth_name: meth_name.1.clone(),
                        is_static: false,
                    }),
                    None => None,
                }
            }
            _ => None,
        },
        _ => None,
    }
}

fn process_arg_names<'e>(recv: Option<Receiver>, args: impl Iterator<Item = &'e tast::Expr>) -> ResultSet {
    match recv {
        Some(recv_name) => args
            .enumerate()
            .map(|(i, aast::Expr(_, pos, _))| {
                Occ(symbol_occurrence::T {
                    name: "(unused)".to_string(),
                    type_: Kind::BestEffortArgument(recv_name.clone(), i as isize),
                    is_declaration: None,
                    pos: pos.clone(),
                    affects_prod_build: true,
                })
            })
            .collect(),
        None => ResultSet::new(),
    }
}

/// Add parameter names for all arguments at a call site. This enables
/// us to show hover information on arguments.
///
///     greet_user("John Doe");
///              //^ Hover shows: Parameter: $name
fn process_callee_arg_names(
    enclosing_class: Option<&aast::Sid>,
    recv: &tast::Expr,
    args: &[tast::Argument],
) -> ResultSet {
    let enclosing_class_name = enclosing_class.map(|x| x.1.as_str());
    let recv = get_callee(enclosing_class_name, recv);
    process_arg_names(recv, args.iter().map(aast_utils::arg_to_expr))
}

/// Add parameter names for all arguments at an instantiation
/// site. This enables us to show hover information on arguments.
///
///     new User("John Doe");
///            //^ Hover shows: Parameter: $name
fn process_constructor_arg_names(
    enclosing_class: Option<&aast::Sid>,
    parent_class_hint: Option<&aast::Hint>,
    aast::ClassId(_, _, cid): &tast::ClassId,
    args: &[tast::Argument],
) -> ResultSet {
    let enclosing_class_name = enclosing_class.map(|x| x.1.as_str());
    let cls_name = match cid {
        aast::ClassId_::CIparent => match parent_class_hint {
            Some(aast::Hint(_, h)) => match &**h {
                aast::Hint_::Happly(ast_defs::Id(_, cls_name), _) => Some(cls_name.clone()),
                _ => None,
            },
            _ => None,
        },
        aast::ClassId_::CIself => enclosing_class_name.map(|s| s.to_string()),
        aast::ClassId_::CIstatic => enclosing_class_name.map(|s| s.to_string()),
        aast::ClassId_::CIexpr(aast::Expr(ty, _, _)) => {
            concrete_cls_name_from_ty(enclosing_class_name, ty)
        }
        aast::ClassId_::CI(ast_defs::Id(_, id)) => Some(id.clone()),
        aast::ClassId_::CIreified(ast_defs::Id(_, id)) => Some(id.clone()),
    };
    let recv = match cls_name {
        Some(cls_name) => Some(Receiver::MethodReceiver {
            cls_name,
            meth_name: sn::members::__CONSTRUCT.to_string(),
            is_static: false,
        }),
        None => None,
    };
    process_arg_names(recv, args.iter().map(aast_utils::arg_to_expr))
}

fn process_fun_id(is_declaration: Option<Pos>, id: (&Pos, &str)) -> ResultSet {
    singleton(symbol_occurrence::T {
        name: id.1.to_string(),
        type_: Kind::Function,
        is_declaration,
        pos: id.0.clone(),
        affects_prod_build: true,
    })
}

fn process_global_const(is_declaration: Option<Pos>, id: (&Pos, &str)) -> ResultSet {
    singleton(symbol_occurrence::T {
        name: id.1.to_string(),
        type_: Kind::GConst,
        is_declaration,
        pos: id.0.clone(),
        affects_prod_build: true,
    })
}

fn process_lvar_id(id: (&Pos, &str)) -> ResultSet {
    singleton(symbol_occurrence::T {
        name: id.1.to_string(),
        type_: Kind::LocalVar,
        is_declaration: None,
        pos: id.0.clone(),
        affects_prod_build: true,
    })
}

fn process_typeconst(
    is_declaration: Option<Pos>,
    (class_name, tconst_name, pos): (&str, &str, &Pos),
) -> ResultSet {
    singleton(symbol_occurrence::T {
        name: format!("{}::{}", class_name, tconst_name),
        type_: Kind::Typeconst(class_name.to_string(), tconst_name.to_string()),
        is_declaration,
        pos: pos.clone(),
        affects_prod_build: true,
    })
}

fn process_class(class_: &tast::Class_) -> ResultSet {
    let mut acc = process_class_id(
        Some(class_.span.clone()),
        None,
        None,
        (&class_.name.0, &class_.name.1),
    );
    let c_name = &class_.name.1;
    let (constructor, static_methods, methods) = crate::aast::split_methods(&class_.methods);
    for method_ in static_methods.iter().chain(methods.iter()) {
        acc = union(
            acc,
            process_member(
                Some(method_.span.clone()),
                ReceiverClass::ClassName(c_name.clone()),
                (&method_.name.0, &method_.name.1),
                MemberKind::Method,
            ),
        );
    }
    for prop in &class_.vars {
        acc = union(
            acc,
            process_member(
                Some(prop.span.clone()),
                ReceiverClass::ClassName(c_name.clone()),
                (&prop.id.0, &prop.id.1),
                MemberKind::Property,
            ),
        );
    }
    for const_ in &class_.consts {
        acc = union(
            acc,
            process_member(
                Some(const_.span.clone()),
                ReceiverClass::ClassName(c_name.clone()),
                (&const_.id.0, &const_.id.1),
                MemberKind::Const,
            ),
        );
    }
    for typeconst in &class_.typeconsts {
        let ast_defs::Id(pos, tconst_name) = &typeconst.name;
        acc = union(
            acc,
            process_typeconst(Some(typeconst.span.clone()), (c_name, tconst_name, pos)),
        );
    }
    // We don't check anything about xhp attributes, so the hooks won't fire when
    // typechecking the class. Need to look at them individually.
    for attr in &class_.xhp_attr_uses {
        match &*attr.1 {
            aast::Hint_::Happly(cid, _) => acc = union(acc, process_sid(cid)),
            _ => {}
        }
    }
    match constructor {
        Some(method_) => union(
            acc,
            process_member(
                Some(method_.span.clone()),
                ReceiverClass::ClassName(c_name.clone()),
                (&method_.name.0, sn::members::__CONSTRUCT),
                MemberKind::Method,
            ),
        ),
        None => acc,
    }
}

fn possibly_remove_unknown_classes(classes: Vec<ReceiverClass>) -> Vec<ReceiverClass> {
    let is_class_name = |c: &ReceiverClass| match c {
        ReceiverClass::ClassName(_) => true,
        ReceiverClass::UnknownClass => false,
    };
    if classes.iter().any(is_class_name) {
        classes.into_iter().filter(is_class_name).collect()
    } else {
        classes
    }
}

fn typed_member_id(env: &Env, receiver_ty: &tast::Ty, mid: (&Pos, &str), kind: MemberKind) -> ResultSet {
    let ids = tast_env::get_receiver_ids(env, receiver_ty.clone())
        .into_iter()
        .map(|ri| match ri {
            tast_env::ReceiverIdentifier::RIclass(cid, _) => ReceiverClass::ClassName(cid),
            tast_env::ReceiverIdentifier::RIdynamic
            | tast_env::ReceiverIdentifier::RIerr
            | tast_env::ReceiverIdentifier::RIany => ReceiverClass::UnknownClass,
        })
        .collect();
    possibly_remove_unknown_classes(ids)
        .into_iter()
        .map(|rid| process_member(None, rid, mid, kind))
        .fold(ResultSet::new(), union)
}

fn typed_method(env: &Env, ty: &tast::Ty, mid: (&Pos, &str)) -> ResultSet {
    typed_member_id(env, ty, mid, MemberKind::Method)
}

fn typed_const(env: &Env, ty: &tast::Ty, mid: (&Pos, &str)) -> ResultSet {
    typed_member_id(env, ty, mid, MemberKind::Const)
}

fn typed_property(env: &Env, ty: &tast::Ty, mid: (&Pos, &str)) -> ResultSet {
    typed_member_id(env, ty, mid, MemberKind::Property)
}

fn typed_constructor(env: &Env, ty: &tast::Ty, pos: &Pos) -> ResultSet {
    typed_method(env, ty, (pos, sn::members::__CONSTRUCT))
}

fn typed_class_id(
    class_id_type: Option<ClassIdType>,
    affects_prod_build: Option<bool>,
    env: &Env,
    ty: &tast::Ty,
    pos: &Pos,
) -> ResultSet {
    let class_id_type = class_id_type.unwrap_or(ClassIdType::ClassId);
    let affects_prod_build = affects_prod_build.unwrap_or(true);
    tast_env::get_class_ids(env, ty.clone())
        .into_iter()
        .map(|cid| process_class_id(None, Some(class_id_type), Some(affects_prod_build), (pos, &cid)))
        .fold(ResultSet::new(), union)
}

/// When we detect a function reference encapsulated in a string,
/// we want to update the function reference without removing the apostrophes.
///
/// Example: class_meth(myclass::class, 'myfunc');
///
/// In this case, we only want to replace the text 'myfunc' - so we need
/// to shrink our positional data by the apostrophes.
fn remove_apostrophes_from_function_eval(mid: &ast_defs::Pstring) -> ast_defs::Pstring {
    let (pos, member_name) = mid;
    let new_pos = crate::pos::shrink_by_one_char_both_sides(pos);
    (new_pos, member_name.clone())
}

fn is_pkg_name_intern(s: &[u8]) -> bool {
    s == b"intern"
}

fn has_require_package_intern(attrs: &aast::UserAttributes<tast::Ty, tast::SavedEnv>) -> bool {
    attrs.0.iter().any(|ua| {
        ua.name.1 == sn::user_attributes::REQUIRE_PACKAGE
            && ua.params.iter().any(|aast::Expr(_, _, e)| match e {
                aast::Expr_::String(pkg) => is_pkg_name_intern(pkg),
                _ => false,
            })
    })
}

fn set_affects_prod_build_false(result_set: ResultSet) -> ResultSet {
    result_set
        .into_iter()
        .map(|Occ(occ)| {
            Occ(symbol_occurrence::T {
                affects_prod_build: false,
                ..occ
            })
        })
        .collect()
}

fn is_package_intern_expr(aast::Expr(_, _, expr_): &tast::Expr) -> bool {
    match expr_ {
        aast::Expr_::Package(pkg) => is_pkg_name_intern(pkg.1.as_bytes()),
        _ => false,
    }
}

fn is_not_package_intern_expr(aast::Expr(_, _, expr_): &tast::Expr) -> bool {
    match expr_ {
        aast::Expr_::Unop(u) => match &**u {
            (ast_defs::Uop::Unot, e) => is_package_intern_expr(e),
            _ => false,
        },
        _ => false,
    }
}

fn is_invariant_package_intern_call(aast::Expr(_, _, expr_): &tast::Expr) -> bool {
    match expr_ {
        aast::Expr_::Call(call) => match (&call.func, call.args.first()) {
            (aast::Expr(_, _, aast::Expr_::Id(fun_name)), Some(aast::Argument::Anormal(arg)))
                if fun_name.1 == sn::autoimported_functions::INVARIANT =>
            {
                is_package_intern_expr(arg)
            }
            _ => false,
        },
        _ => false,
    }
}

fn stmt_is_invariant_package_intern(env: &Env, aast::Stmt(_, stmt_): &tast::Stmt) -> bool {
    match stmt_ {
        aast::Stmt_::If(x) => {
            let (cond, then_block, _) = &**x;
            resugar_invariant_call(env, cond, then_block)
                .is_some_and(|e| is_invariant_package_intern_call(&e))
        }
        _ => false,
    }
}

/// `Server_utils.resugar_invariant_call` (`client_and_server/server_utils.ml`):
/// here because `server_utils` is behind the feature `server`, and this
/// module (reachable from `hh single`) is behind `port`.
pub fn resugar_invariant_call(
    env: &Env,
    cond: &tast::Expr,
    then_body: &tast::Block,
) -> Option<tast::Expr> {
    // If a user has actually written
    //
    // if (!foo()) {
    //   invariant_violation("oh dear");
    // }
    //
    // then the position of the if statement and the call will be different. If
    // the positions are the same, we know that we desugared a call to invariant().
    let has_same_start = |pos1: &Pos, pos2: &Pos| {
        let pos1_start = crate::pos::start_offset(pos1);
        let pos2_start = crate::pos::start_offset(pos2);
        pos1_start == pos2_start
    };
    let aast::Expr(_, _, aast::Expr_::Unop(u)) = cond else {
        return None;
    };
    let (ast_defs::Uop::Unot, invariant_cond) = &**u else {
        return None;
    };
    let [aast::Stmt(stmt_pos, aast::Stmt_::Expr(e))] = &then_body.0[..] else {
        return None;
    };
    let aast::Expr(call_ty, call_pos, aast::Expr_::Call(call)) = &**e else {
        return None;
    };
    let aast::Expr(recv_ty, recv_pos, aast::Expr_::Id(id)) = &call.func else {
        return None;
    };
    let ast_defs::Id(name_pos, name) = &**id;
    if !(name == sn::autoimported_functions::INVARIANT_VIOLATION && has_same_start(stmt_pos, call_pos))
    {
        return None;
    }
    let recv_ty_invariant = match tast_env::get_fun(env, sn::autoimported_functions::INVARIANT) {
        decl_entry::T::Found(fun_decl) => {
            // `let (_, f_locl_ty) = Tast_env.localize_no_subst env ...`: the
            // new environment is dropped.
            tast_env::localize_no_subst(&mut env.clone(), true, &fun_decl.ty)
        }
        decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => recv_ty.clone(),
    };
    let mut args = vec![aast::Argument::Anormal(invariant_cond.clone())];
    args.extend(call.args.iter().cloned());
    Some(aast::Expr(
        call_ty.clone(),
        call_pos.clone(),
        aast::Expr_::Call(Box::new(aast::CallExpr {
            func: aast::Expr(
                recv_ty_invariant,
                recv_pos.clone(),
                aast::Expr_::Id(Box::new(ast_defs::Id(
                    name_pos.clone(),
                    sn::autoimported_functions::INVARIANT.to_string(),
                ))),
            ),
            targs: vec![],
            args,
            unpacked_arg: None,
        })),
    ))
}

/// The object `visitor` of the OCaml, with its `ref`s.
struct SymbolVisitor {
    acc: ResultSet,
    class_name: Option<aast::Sid>,
    parent_class_hint: Option<aast::Hint>,
    method_name: Option<(aast::Sid, bool)>,
    // state for computing affects_prod_build
    in_nameof: bool,
    in_class_ptr: bool,
    in_attribute: bool,
    in_require_package_intern: bool,
    in_newtype: bool,
    in_is_expression: bool,
    /// The `f_unsafe_ctxs` / `m_unsafe_ctxs` of the functions and methods
    /// being visited (by address), which the OCaml sets to `None` before it
    /// visits them.
    skipped_contexts: HashSet<*const aast::Contexts>,
}

impl SymbolVisitor {
    fn new() -> Self {
        SymbolVisitor {
            acc: ResultSet::new(),
            class_name: None,
            parent_class_hint: None,
            method_name: None,
            in_nameof: false,
            in_class_ptr: false,
            in_attribute: false,
            in_require_package_intern: false,
            in_newtype: false,
            in_is_expression: false,
            skipped_contexts: HashSet::new(),
        }
    }

    /// `self#plus acc r`, into the accumulator.
    fn add(&mut self, r: ResultSet) {
        let acc = std::mem::take(&mut self.acc);
        self.acc = union(acc, r);
    }

    /// The result of the visits that `f` makes.
    fn sub<'b>(&mut self, f: impl FnOnce(&mut Self) -> Res) -> ResultSet
    where
        Self: Reduce<'b, Acc = ResultSet>,
    {
        let (_, r) = reduce::result(self, f);
        r
    }

    /// `method! on_block`
    fn on_block<'b>(&mut self, env: &mut Env, block: impl Iterator<Item = &'b tast::Stmt>) -> Res {
        let mut is_after_package_intern_invariant = false;
        for stmt in block {
            let stmt_result = self.sub(|v| v.visit_stmt(env, stmt));
            let stmt_result = if is_after_package_intern_invariant {
                set_affects_prod_build_false(stmt_result)
            } else {
                stmt_result
            };
            is_after_package_intern_invariant =
                is_after_package_intern_invariant || stmt_is_invariant_package_intern(env, stmt);
            self.add(stmt_result);
        }
        Ok(())
    }

    /// `method! on_expr`
    fn on_expr<'b>(&mut self, env: &mut Env, expr: &'b tast::Expr) -> Res {
        let aast::Expr(_, pos, expr_) = expr;
        let acc = match expr_ {
            aast::Expr_::Hole(h) => match &h.3 {
                aast::HoleSource::UnsafeCast(_) => {
                    process_fun_id(None, (pos, sn::pseudo_functions::UNSAFE_CAST))
                }
                aast::HoleSource::UnsafeNonnullCast => {
                    process_fun_id(None, (pos, sn::pseudo_functions::UNSAFE_NONNULL_CAST))
                }
                _ => ResultSet::new(),
            },
            aast::Expr_::New(n) => {
                let aast::ClassId(ty, p, _) = &n.0;
                typed_constructor(env, ty, p)
            }
            aast::Expr_::ObjGet(og) => match &**og {
                (aast::Expr(ty, _, _), aast::Expr(_, _, aast::Expr_::Id(mid)), _, _) => {
                    typed_property(env, ty, (&mid.0, &mid.1))
                }
                _ => ResultSet::new(),
            },
            aast::Expr_::ClassConst(cc) => {
                let (aast::ClassId(ty, _, _), mid) = &**cc;
                typed_const(env, ty, (&mid.0, &mid.1))
            }
            aast::Expr_::ClassGet(cg) => {
                let (aast::ClassId(ty, _, _), mid, _) = &**cg;
                typed_property(env, ty, (&mid.0, &mid.1))
            }
            aast::Expr_::Xml(x) => {
                let (cid, attrs, _) = &**x;
                let class_id = process_sid(cid);
                let xhp_attributes = process_xml_attrs(&cid.1, attrs);
                union(class_id, xhp_attributes)
            }
            aast::Expr_::FunctionPointer(fp) => match &fp.0 {
                aast::FunctionPtrId::FPId(id) => process_fun_id(None, (&id.0, &id.1)),
                aast::FunctionPtrId::FPClassConst(aast::ClassId(ty, _, _cid), mid) => {
                    typed_method(env, ty, (&mid.0, &mid.1))
                }
            },
            aast::Expr_::MethodCaller(mc) => {
                let (pcid, mid) = &**mc;
                let cid = &pcid.1;
                let mid = remove_apostrophes_from_function_eval(mid);
                union(
                    union(
                        process_fun_id(None, (pos, sn::autoimported_functions::METH_CALLER)),
                        process_sid(pcid),
                    ),
                    process_member(
                        None,
                        ReceiverClass::ClassName(cid.clone()),
                        (&mid.0, &mid.1),
                        MemberKind::Method,
                    ),
                )
            }
            aast::Expr_::ValCollection(vc) => {
                let ((_, kind), _, _) = &**vc;
                let type_name = match kind {
                    aast::VcKind::Vector => "Vector",
                    aast::VcKind::ImmVector => "ImmVector",
                    aast::VcKind::Set => "Set",
                    aast::VcKind::ImmSet => "ImmSet",
                    aast::VcKind::Keyset => "keyset",
                    aast::VcKind::Vec => "vec",
                };
                process_class_id(None, None, None, (pos, &format!("\\HH\\{}", type_name)))
            }
            aast::Expr_::KeyValCollection(kvc) => {
                let ((_, kind), _, _) = &**kvc;
                let type_name = match kind {
                    aast::KvcKind::Map => "Map",
                    aast::KvcKind::ImmMap => "ImmMap",
                    aast::KvcKind::Dict => "dict",
                };
                process_class_id(None, None, None, (pos, &format!("\\HH\\{}", type_name)))
            }
            aast::Expr_::EnumClassLabel(ecl) => {
                let (enum_name, label_name) = &**ecl;
                match enum_name {
                    None => {
                        let aast::Expr(ety, _, _) = expr;
                        // `let (env, ty_enum_class) = ...`: the new
                        // environment is used for this call only.
                        let mut env = env.clone();
                        let ty_enum_class = tast_env::get_label_receiver_ty(&mut env, ety.clone());
                        typed_member_id(
                            &env,
                            &ty_enum_class,
                            (pos, label_name),
                            MemberKind::EnumClassLabel,
                        )
                    }
                    Some(enum_id) => {
                        let enum_name = &enum_id.1;
                        union(
                            process_sid(enum_id),
                            singleton(symbol_occurrence::T {
                                name: format!(
                                    "{}#{}",
                                    crate::utils::strip_ns(enum_name),
                                    label_name
                                ),
                                type_: Kind::EnumClassLabel(enum_name.clone(), label_name.clone()),
                                is_declaration: None,
                                pos: pos.clone(),
                                affects_prod_build: true,
                            }),
                        )
                    }
                }
            }
            _ => ResultSet::new(),
        };
        let old_nameof = self.in_nameof;
        let old_class_ptr = self.in_class_ptr;
        match expr_ {
            aast::Expr_::Nameof(_) => self.in_nameof = true,
            aast::Expr_::ClassConst(cc) if cc.1.1 == sn::members::M_CLASS => {
                self.in_class_ptr = true
            }
            _ => {}
        }
        // `acc + super#on_expr env expr`
        self.add(acc);
        let res = expr.recurse(env, self);
        self.in_nameof = old_nameof;
        self.in_class_ptr = old_class_ptr;
        res
    }

    /// `method! on_If`
    fn on_If<'b>(
        &mut self,
        env: &mut Env,
        stmt_: &'b tast::Stmt_,
        cond: &'b tast::Expr,
        then_block: &'b tast::Block,
        else_block: &'b tast::Block,
    ) -> Res {
        match resugar_invariant_call(env, cond, then_block) {
            Some(e) => self.on_expr(env, &e),
            None if is_package_intern_expr(cond) => {
                self.visit_expr(env, cond)?;
                let then_ = self.sub(|v| v.on_block(env, then_block.0.iter()));
                self.add(set_affects_prod_build_false(then_));
                self.on_block(env, else_block.0.iter())
            }
            None if is_not_package_intern_expr(cond) => {
                self.visit_expr(env, cond)?;
                self.on_block(env, then_block.0.iter())?;
                let else_ = self.sub(|v| v.on_block(env, else_block.0.iter()));
                self.add(set_affects_prod_build_false(else_));
                Ok(())
            }
            None => stmt_.recurse(env, self),
        }
    }

    /// `method! on_Is`
    fn on_Is<'b>(&mut self, env: &mut Env, e: &'b tast::Expr, h: &'b aast::Hint) -> Res {
        self.visit_expr(env, e)?;
        let old_in_is_expression = self.in_is_expression;
        self.in_is_expression = true;
        let res = self.visit_hint(env, h);
        self.in_is_expression = old_in_is_expression;
        res
    }

    /// `method! on_As`
    fn on_As<'b>(&mut self, env: &mut Env, as_: &'b aast::As_<tast::Ty, tast::SavedEnv>) -> Res {
        self.visit_expr(env, &as_.expr)?;
        self.visit_hint(env, &as_.hint)
    }

    /// `method! on_Call`
    fn on_Call<'b>(&mut self, env: &mut Env, call: &'b tast::CallExpr) -> Res {
        // For Id, Obj_get (with an Id member), and Class_const, we don't want to
        // use the result of `self#on_expr env e`, since it would record a
        // property, class const, or global const access instead of a method call.
        // So instead of invoking super#on_Call, we reimplement it here, omitting
        // `self#on_expr env e` when necessary.
        let aast::CallExpr {
            func: e,
            targs: tal,
            args: el,
            unpacked_arg,
        } = call;
        let aast::Expr(_, _, expr_) = e;
        if tast_env::is_in_expr_tree(env) {
            // In an expression tree, we desugar function calls and
            // method calls to calls to ::symbolType(). Any other
            // function call is just calling typing helpers, and isn't
            // useful in hover or go-to-definition.
            //
            // This ensures that when a user hovers over a literal "abc" we only
            // show the inferred type, and don't show
            // MyVisitor::stringType() information.
            match expr_ {
                aast::Expr_::Call(c) => match (&c.func, &c.args[..]) {
                    (aast::Expr(_, _, aast::Expr_::ClassConst(cc)), [arg])
                        if cc.1.1 == sn::expression_trees::SYMBOL_TYPE =>
                    {
                        // Treat MyVisitor::symbolType(foo<>) as just foo().
                        self.visit_argument(env, arg)?
                    }
                    _ => {}
                },
                _ => {}
            }
        } else {
            let expr_ = match expr_ {
                aast::Expr_::ReadonlyExpr(e) => &e.2,
                _ => expr_,
            };
            match expr_ {
                aast::Expr_::Id(id) => {
                    // E.g. foo()
                    self.add(process_fun_id(None, (&id.0, &id.1)))
                }
                aast::Expr_::ObjGet(og)
                    if matches!(
                        &**og,
                        (_, aast::Expr(_, _, aast::Expr_::Id(_)), _, ast_defs::PropOrMethod::IsMethod)
                    ) =>
                {
                    // E.g. $bar->foo()
                    let (obj, member, _, _) = &**og;
                    let aast::Expr(_, _, aast::Expr_::Id(mid)) = member else {
                        unreachable!()
                    };
                    self.visit_expr(env, obj)?;
                    self.add(typed_method(env, &obj.0, (&mid.0, &mid.1)))
                }
                aast::Expr_::ObjGet(og)
                    if matches!(
                        &**og,
                        (_, aast::Expr(_, _, aast::Expr_::Id(_)), _, ast_defs::PropOrMethod::IsProp)
                    ) =>
                {
                    // E.g. ($bar->foo)()
                    let (obj, member, _, _) = &**og;
                    let aast::Expr(_, _, aast::Expr_::Id(mid)) = member else {
                        unreachable!()
                    };
                    self.visit_expr(env, obj)?;
                    self.add(typed_property(env, &obj.0, (&mid.0, &mid.1)))
                }
                aast::Expr_::ClassConst(cc) => {
                    // E.g. Bar::foo()
                    let (cid, mid) = &**cc;
                    self.visit_class_id(env, cid)?;
                    self.add(typed_method(env, &cid.0, (&mid.0, &mid.1)))
                }
                _ => self.visit_expr(env, e)?,
            }
        }
        for targ in tal {
            self.visit_targ(env, targ)?;
        }
        for arg in el {
            self.visit_argument(env, arg)?;
        }
        let arg_names = process_callee_arg_names(self.class_name.as_ref(), e, el);
        self.add(arg_names);
        if let Some(unpacked_arg) = unpacked_arg {
            self.visit_expr(env, unpacked_arg)?;
        }
        Ok(())
    }

    /// `method! on_hint`
    fn on_hint<'b>(&mut self, env: &mut Env, h: &'b aast::Hint) -> Res {
        let mk_hint = |name: &str, type_: Kind, pos: &Pos| symbol_occurrence::T {
            name: name.to_string(),
            type_,
            is_declaration: None,
            pos: pos.clone(),
            affects_prod_build: true,
        };
        let aast::Hint(pos, hint_) = h;
        let acc = match &**hint_ {
            aast::Hint_::Habstr(name) => singleton(mk_hint(name, Kind::TypeVar, pos)),
            aast::Hint_::Hprim(prim) => {
                let name = crate::aast_defs::string_of_tprim(*prim);
                singleton(mk_hint(&name, Kind::BuiltInType(BuiltInTypeHint::BIprimitive(*prim)), pos))
            }
            aast::Hint_::Happly(ast_defs::Id(_, name), _) if name == sn::typehints::HH_STRING => {
                singleton(mk_hint("string", Kind::BuiltInType(BuiltInTypeHint::BIstring), pos))
            }
            aast::Hint_::Hnothing => {
                singleton(mk_hint("nothing", Kind::BuiltInType(BuiltInTypeHint::BInothing), pos))
            }
            aast::Hint_::Hmixed => {
                singleton(mk_hint("mixed", Kind::BuiltInType(BuiltInTypeHint::BImixed), pos))
            }
            aast::Hint_::Hnonnull => {
                singleton(mk_hint("nonnull", Kind::BuiltInType(BuiltInTypeHint::BInonnull), pos))
            }
            aast::Hint_::Hdynamic => {
                singleton(mk_hint("dynamic", Kind::BuiltInType(BuiltInTypeHint::BIdynamic), pos))
            }
            aast::Hint_::Hshape(_) => {
                singleton(mk_hint("shape", Kind::BuiltInType(BuiltInTypeHint::BIshape), pos))
            }
            aast::Hint_::Hthis => {
                singleton(mk_hint("this", Kind::BuiltInType(BuiltInTypeHint::BIthis), pos))
            }
            aast::Hint_::Hoption(_) => {
                // Narrow the position to just the '?', not the whole ?Foo<Complicated<Bar>>.
                let (_start_line, start_column) = crate::pos::line_column(pos);
                let qmark_pos = crate::pos::set_col_end(start_column + 1, pos);
                singleton(mk_hint("?", Kind::BuiltInType(BuiltInTypeHint::BIoption), &qmark_pos))
            }
            _ => ResultSet::new(),
        };
        self.add(acc);
        h.recurse(env, self)
    }

    /// `method! on_Happly`
    fn on_Happly<'b>(&mut self, env: &mut Env, hint_: &'b aast::Hint_, sid: &'b aast::Sid, hl: &'b [aast::Hint]) -> Res {
        match hl {
            [h] if sid.1 == sn::classes::SUPPORT_DYN => self.visit_hint(env, h),
            _ => {
                let affects_prod_build = if self.in_attribute {
                    false
                } else if self.in_newtype || self.in_is_expression {
                    false
                } else {
                    true
                };
                self.add(process_class_id(None, None, Some(affects_prod_build), (&sid.0, &sid.1)));
                hint_.recurse(env, self)
            }
        }
    }

    /// `method! on_class_`
    fn on_class_<'b>(&mut self, env: &mut Env, class_: &'b tast::Class_) -> Res {
        self.class_name = Some(class_.name.clone());
        self.parent_class_hint = class_.extends.first().cloned();
        let acc = process_class(class_);
        self.add(acc);

        // Enums implicitly extend BuiltinEnum. However, BuiltinEnums also extend
        // the same Enum as a type parameter.
        //
        // Ex: enum Size extends BuiltinEnum<Size> { ... }
        //
        // This will return the definition of the enum twice when finding references
        // on it. As a result, we set the extends property of an enum's tast to an empty list.
        //
        // The same situation applies to Enum classes that extends
        // BuiltinEnumClass. However in this case we just want to filter out
        // this one extends, and keep the other unchanged.
        let c_name = &class_.name.1;
        // Checks if the hint is matching the pattern
        // `HH\BuiltinEnumClass<HH\MemberOf<c_name, _>>`
        let is_generated_builtin_enum_class = |h: &aast::Hint| match &*h.1 {
            aast::Hint_::Happly(ast_defs::Id(_, builtin_enum_class), args) if args.len() == 1 => {
                match &*args[0].1 {
                    aast::Hint_::Happly(ast_defs::Id(_, memberof), margs) if margs.len() == 2 => {
                        match &*margs[0].1 {
                            aast::Hint_::Happly(ast_defs::Id(_, name), nargs) if nargs.is_empty() => {
                                builtin_enum_class == sn::classes::HH_BUILTIN_ENUM_CLASS
                                    && memberof == sn::classes::MEMBER_OF
                                    && name == c_name
                            }
                            _ => false,
                        }
                    }
                    _ => false,
                }
            }
            aast::Hint_::Happly(ast_defs::Id(_, builtin_abstract_enum_class), args)
                if args.is_empty() =>
            {
                builtin_abstract_enum_class == sn::classes::HH_BUILTIN_ABSTRACT_ENUM_CLASS
            }
            _ => false,
        };
        // Checks if the hint is matching the pattern
        // `HH\BuiltinEnum<c_name>`
        let is_generated_builtin_enum = |h: &aast::Hint| match &*h.1 {
            aast::Hint_::Happly(ast_defs::Id(_, builtin_enum), args) if args.len() == 1 => {
                match &*args[0].1 {
                    aast::Hint_::Happly(ast_defs::Id(_, name), nargs) if nargs.is_empty() => {
                        builtin_enum == sn::classes::HH_BUILTIN_ENUM && name == c_name
                    }
                    _ => false,
                }
            }
            _ => false,
        };
        // If the class is an enum or enum class, remove the generated
        // occurrences.
        let res = if crate::ast_defs::is_c_enum_class(class_.kind) {
            // Enum classes might extend other classes, so we filter
            // the list and we don't depend on their order.
            let mut c = class_.clone();
            c.extends = class_
                .extends
                .iter()
                .filter(|h| !is_generated_builtin_enum_class(h))
                .cloned()
                .collect();
            // We also have to take care of the type of constants that
            // are rewritten from Foo to MemberOf<EnumName, Foo>
            for cc in c.consts.iter_mut() {
                cc.type_ = cc.type_.take().map(|h| match &*h.1 {
                    aast::Hint_::Happly(ast_defs::Id(_, name), args)
                        if args.len() == 2 && name == sn::classes::MEMBER_OF =>
                    {
                        args[1].clone()
                    }
                    _ => h,
                });
            }
            c.recurse(env, self)
        } else if crate::ast_defs::is_c_enum(class_.kind) {
            // For enums, we could remove everything as they don't extends
            // other classes, but let's filter anyway, just to be resilient
            // to future evolutions
            let mut c = class_.clone();
            c.extends = class_
                .extends
                .iter()
                .filter(|h| !is_generated_builtin_enum(h))
                .cloned()
                .collect();
            c.recurse(env, self)
        } else {
            class_.recurse(env, self)
        };
        self.class_name = None;
        self.parent_class_hint = None;
        res
    }
}

impl<'a> Reduce<'a> for SymbolVisitor {
    type Acc = ResultSet;

    fn zero(&self) -> ResultSet {
        ResultSet::new()
    }

    fn plus(&self, a: ResultSet, b: ResultSet) -> ResultSet {
        union(a, b)
    }

    fn acc(&mut self) -> &mut ResultSet {
        &mut self.acc
    }
}

impl<'a> Visitor<'a> for SymbolVisitor {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a; class_var);

    fn visit_block(&mut self, env: &mut Env, block: &'a tast::Block) -> Res {
        self.on_block(env, block.0.iter())
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Res {
        self.on_expr(env, expr)
    }

    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Res {
        match expr_ {
            aast::Expr_::Is(x) => {
                let (e, h) = &**x;
                self.on_Is(env, e, h)
            }
            aast::Expr_::As(as_) => self.on_As(env, as_),
            aast::Expr_::Call(call) => self.on_Call(env, call),
            aast::Expr_::New(n) => {
                // `method! on_New`
                let (cid, _targs, args, _var_arg, _constr_ty) = &**n;
                let named_params = process_constructor_arg_names(
                    self.class_name.as_ref(),
                    self.parent_class_hint.as_ref(),
                    cid,
                    args,
                );
                self.add(named_params);
                reduce::on_expr_(self, env, expr_)
            }
            aast::Expr_::Lvar(lid) => {
                // `method! on_Lvar`
                let aast::Lid(pos, id) = &**lid;
                let acc = if crate::local_id::is_user_denotable(id) {
                    process_lvar_id((pos, crate::local_id::get_name(id)))
                } else {
                    ResultSet::new()
                };
                self.add(acc);
                reduce::on_expr_(self, env, expr_)
            }
            aast::Expr_::Id(id) => {
                // `method! on_Id`
                self.add(process_global_const(None, (&id.0, &id.1)));
                reduce::on_expr_(self, env, expr_)
            }
            aast::Expr_::ObjGet(og) => {
                // `method! on_Obj_get`
                let (obj, member, ognf, _prop_or_method) = &**og;
                match &member.2 {
                    aast::Expr_::Id(_) => {
                        // Don't visit this Id, since we would record it as a gconst access.
                        self.visit_expr(env, obj)?;
                        self.visit_operator_null_flavor(env, ognf)
                    }
                    _ => reduce::on_expr_(self, env, expr_),
                }
            }
            _ => reduce::on_expr_(self, env, expr_),
        }
    }

    fn visit_stmt_(&mut self, env: &mut Env, stmt_: &'a tast::Stmt_) -> Res {
        match stmt_ {
            aast::Stmt_::If(x) => {
                let (cond, then_block, else_block) = &**x;
                self.on_If(env, stmt_, cond, then_block, else_block)
            }
            _ => stmt_.recurse(env, self),
        }
    }

    fn visit_expression_tree(&mut self, env: &mut Env, expr: &'a tast_visitor::ExpressionTree) -> Res {
        // We only want to consider completion from the hint and the
        // virtualized expression, not the visitor expression. The
        // visitor expression is unityped, so we can't do much.
        let et_class = &expr.class;
        self.add(process_class_id(
            None,
            Some(ClassIdType::ExpressionTreeVisitor),
            None,
            (&et_class.0, &et_class.1),
        ));

        let et_splices = aast_utils::get_splices_from_et(expr);
        // `self#on_Block env None et_splices`
        self.on_block(env, et_splices.into_iter())?;

        // We're overriding super#on_expression_tree, so we need to
        // update the environment.
        let saved = env.clone();
        tast_env::inside_expr_tree(env, et_class.clone());

        let e = match aast_utils::get_virtual_expr_from_et(expr) {
            Some(e) => e,
            _ => &expr.runtime_expr,
        };
        let res = self.visit_expr(env, e);
        *env = saved;
        res
    }

    fn visit_class_id(&mut self, env: &mut Env, x: &'a tast::ClassId) -> Res {
        let aast::ClassId(ty, p, cid) = x;
        match cid {
            aast::ClassId_::CIexpr(expr) => {
                // We want to special case this because we want to get the type of the
                // inner expression, which will have a type like `classname<Foo>`, rather
                // than the resolved type of the class ID, which will have a type like
                // `Foo`. Since the class ID and the inner expression have the same span,
                // it is not easy to distinguish them later.
                self.visit_expr(env, expr)
            }
            aast::ClassId_::CIparent | aast::ClassId_::CIself | aast::ClassId_::CIstatic => {
                // We want to special case these because we want to keep track of the
                // original class id type. This information is useful in some cases, for
                // instance when refactoring class names, because we want to avoid
                // refactoring `self`, `static`, and `parent` class ids.
                self.add(typed_class_id(Some(ClassIdType::Other), None, env, ty, p));
                Ok(())
            }
            aast::ClassId_::CI(sid) => {
                let affects_prod_build = if self.in_nameof || self.in_attribute {
                    false
                } else if self.in_class_ptr {
                    let tcopt = tast_env::get_tcopt(env);
                    !tcopt.tco_package_allow_classconst_violations
                } else if self.in_newtype || self.in_is_expression {
                    false
                } else {
                    true
                };
                self.add(process_class_id(None, None, Some(affects_prod_build), (&sid.0, &sid.1)));
                Ok(())
            }
            aast::ClassId_::CIreified(ast_defs::Id(id_pos, _)) => {
                // TODO(T259578698) causes bug where reified generic identifies to its bounds
                self.add(typed_class_id(None, None, env, ty, id_pos));
                Ok(())
            }
        }
    }

    fn visit_hint_(&mut self, env: &mut Env, hint_: &'a aast::Hint_) -> Res {
        match hint_ {
            aast::Hint_::Haccess(root, ids) => {
                // `method! on_Haccess`
                let acc = tast_env::referenced_typeconsts(env, root, ids)
                    .iter()
                    .map(|(c, t, p)| process_typeconst(None, (c, t, p)))
                    .fold(ResultSet::new(), union);
                self.add(acc);
                hint_.recurse(env, self)
            }
            aast::Hint_::Hrefinement(root, refs) => {
                // `method! on_Hrefinement`
                let mut acc = ResultSet::new();
                for r in refs {
                    let id = match r {
                        aast::Refinement::Rctx(id, _) | aast::Refinement::Rtype(id, _) => id,
                    };
                    acc = tast_env::referenced_typeconsts(env, root, std::slice::from_ref(id))
                        .iter()
                        .map(|(c, t, p)| process_typeconst(None, (c, t, p)))
                        .fold(acc, union);
                }
                self.add(acc);
                hint_.recurse(env, self)
            }
            aast::Hint_::Happly(sid, hl) => self.on_Happly(env, hint_, sid, hl),
            _ => hint_.recurse(env, self),
        }
    }

    fn visit_tparam(&mut self, env: &mut Env, tp: &'a tast::Tparam) -> Res {
        let ast_defs::Id(pos, name) = &tp.name;
        self.add(singleton(symbol_occurrence::T {
            name: name.clone(),
            type_: Kind::TypeVar,
            is_declaration: Some(pos.clone()),
            pos: pos.clone(),
            affects_prod_build: true,
        }));
        tp.recurse(env, self)
    }

    fn visit_capture_lid(&mut self, _env: &mut Env, x: &'a tast::CaptureLid) -> Res {
        let aast::CaptureLid(_, aast::Lid(pos, id)) = x;
        self.add(process_lvar_id((pos, crate::local_id::get_name(id))));
        Ok(())
    }

    fn visit_hint(&mut self, env: &mut Env, h: &'a aast::Hint) -> Res {
        self.on_hint(env, h)
    }

    fn visit_fun_param(&mut self, env: &mut Env, param: &'a tast::FunParam) -> Res {
        self.add(process_lvar_id((&param.pos, &param.name)));
        param.recurse(env, self)
    }

    fn visit_catch(&mut self, env: &mut Env, x: &'a aast::Catch<tast::Ty, tast::SavedEnv>) -> Res {
        let aast::Catch(sid, _, _) = x;
        self.add(process_sid(sid));
        x.recurse(env, self)
    }

    fn visit_class_(&mut self, env: &mut Env, class_: &'a tast::Class_) -> Res {
        self.on_class_(env, class_)
    }

    fn visit_fun_def(&mut self, env: &mut Env, fd: &'a tast::FunDef) -> Res {
        assert!(!self.in_require_package_intern);
        self.in_require_package_intern = has_require_package_intern(&fd.fun.user_attributes);
        let acc = process_fun_id(Some(fd.name.0.clone()), (&fd.name.0, &fd.name.1));
        let mut result = self.sub(|v| fd.recurse(env, v));
        result = union(acc, result);
        // rather than checking in_require_package_intern everywhere, postprocess the results
        let result = if self.in_require_package_intern {
            set_affects_prod_build_false(result)
        } else {
            result
        };
        self.in_require_package_intern = false;
        self.add(result);
        Ok(())
    }

    fn visit_fun_(&mut self, env: &mut Env, fun_: &'a tast::Fun_) -> Res {
        // `super#on_fun_ env { fun_ with Aast.f_unsafe_ctxs = None }`
        let skipped = fun_.unsafe_ctxs.as_ref().map(|c| c as *const aast::Contexts);
        if let Some(c) = skipped {
            self.skipped_contexts.insert(c);
        }
        let res = reduce::on_fun_(self, env, fun_);
        if let Some(c) = skipped {
            self.skipped_contexts.remove(&c);
        }
        res
    }

    fn visit_contexts(&mut self, env: &mut Env, x: &'a aast::Contexts) -> Res {
        if self.skipped_contexts.contains(&(x as *const aast::Contexts)) {
            Ok(())
        } else {
            x.recurse(env, self)
        }
    }

    fn visit_typedef(&mut self, env: &mut Env, typedef: &'a tast::Typedef) -> Res {
        self.add(process_class_id(
            Some(typedef.span.clone()),
            None,
            None,
            (&typedef.name.0, &typedef.name.1),
        ));
        let is_newtype = match &typedef.assignment {
            aast::TypedefAssignment::SimpleTypeDef(aast::TypedefVisibilityAndHint {
                vis: aast::TypedefVisibility::Opaque | aast::TypedefVisibility::OpaqueModule,
                ..
            }) => true,
            _ => false,
        };
        let old_in_newtype = self.in_newtype;
        self.in_newtype = is_newtype;
        let res = typedef.recurse(env, self);
        self.in_newtype = old_in_newtype;
        res
    }

    fn visit_gconst(&mut self, env: &mut Env, cst: &'a tast::Gconst) -> Res {
        self.add(process_global_const(
            Some(cst.span.clone()),
            (&cst.name.0, &cst.name.1),
        ));
        cst.recurse(env, self)
    }

    fn visit_shape_field_name(&mut self, env: &mut Env, x: &'a ast_defs::ShapeFieldName) -> Res {
        match x {
            ast_defs::ShapeFieldName::SFclassConst(cid, mid) => {
                // `method! on_SFclass_const`
                self.add(process_sid(cid));
                self.add(process_member(
                    None,
                    ReceiverClass::ClassName(cid.1.clone()),
                    (&mid.0, &mid.1),
                    MemberKind::Const,
                ));
                x.recurse(env, self)
            }
            _ => x.recurse(env, self),
        }
    }

    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> Res {
        assert!(!self.in_require_package_intern);
        self.in_require_package_intern = has_require_package_intern(&m.user_attributes);
        self.method_name = Some((m.name.clone(), m.static_));
        // `super#on_method_ env { m with m_unsafe_ctxs = None }`
        let skipped = m.unsafe_ctxs.as_ref().map(|c| c as *const aast::Contexts);
        if let Some(c) = skipped {
            self.skipped_contexts.insert(c);
        }
        let acc = self.sub(|v| reduce::on_method_(v, env, m));
        if let Some(c) = skipped {
            self.skipped_contexts.remove(&c);
        }
        self.method_name = None;
        // rather than checking in_require_package_intern everywhere, postprocess the results
        let acc = if self.in_require_package_intern {
            set_affects_prod_build_false(acc)
        } else {
            acc
        };
        self.in_require_package_intern = false;
        self.add(acc);
        Ok(())
    }

    fn visit_user_attribute(&mut self, env: &mut Env, ua: &'a tast::UserAttribute) -> Res {
        let old_in_attribute = self.in_attribute;
        self.in_attribute = true;
        let tcopt = tast_env::get_tcopt(env);
        // Don't show __SupportDynamicType if it's implicit everywhere
        let res = if ua.name.1 == sn::user_attributes::SUPPORT_DYNAMIC_TYPE
            && tcopt.po.everything_sdt
            && !tcopt.tco_enable_no_auto_dynamic
        {
            Ok(())
        } else {
            let acc = process_attribute(
                (&ua.name.0, &ua.name.1),
                self.class_name.as_ref(),
                self.method_name.as_ref(),
            );
            self.add(acc);
            ua.recurse(env, self)
        };
        self.in_attribute = old_in_attribute;
        res
    }

    fn visit_def(&mut self, env: &mut Env, def: &'a tast::Def) -> Res {
        match def {
            aast::Def::SetModule(sm) => {
                // `method! on_SetModule`
                let ast_defs::Id(pos, id) = &**sm;
                self.add(singleton(symbol_occurrence::T {
                    name: id.clone(),
                    type_: Kind::Module,
                    is_declaration: None,
                    pos: pos.clone(),
                    affects_prod_build: true,
                }));
                def.recurse(env, self)
            }
            _ => def.recurse(env, self),
        }
    }

    fn visit_module_def(&mut self, env: &mut Env, md: &'a tast::ModuleDef) -> Res {
        let ast_defs::Id(pos, id) = &md.name;
        self.add(singleton(symbol_occurrence::T {
            name: id.clone(),
            type_: Kind::Module,
            is_declaration: None,
            pos: pos.clone(),
            affects_prod_build: true,
        }));
        md.recurse(env, self)
    }
}

/// Types of decls used in keyword extraction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClassishDeclKind {
    DKclass,
    DKinterface,
    DKenumclass,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ModuleDeclKind {
    DKModuleDeclaration,
    DKModuleMembershipDeclaration,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum KeywordContext {
    ClassishDecl(ClassishDeclKind),
    Method,
    Parameter,
    ReturnType,
    TypeConst,
    AsyncBlockHeader,
    ModuleDecl(ModuleDeclKind),
    ClassType,
}

/// `Full_fidelity_source_text.relative_pos` of the CST's source text, with
/// the line index of the text built once (`relative_pos` builds it at each
/// call).
struct CstPositions<'t> {
    file_path: Arc<relative_path::T>,
    indexed: IndexedSourceText<'t>,
}

impl CstPositions<'_> {
    fn relative_pos(&self, start_offset: usize, end_offset: usize) -> Pos {
        let pos = self.indexed.relative_pos(start_offset, end_offset);
        Pos::from_lnum_bol_offset(Arc::clone(&self.file_path), pos.start, pos.end)
    }
}

fn trivia_pos(positions: &CstPositions<'_>, t: &PositionedTrivium) -> Pos {
    positions.relative_pos(t.offset, t.offset + t.width)
}

fn fixme_elt(positions: &CstPositions<'_>, t: &PositionedTrivium) -> Option<Elt> {
    match t.kind {
        TriviaKind::FixMe => {
            let pos = trivia_pos(positions, t);
            Some(symbol_occurrence::T {
                name: "HH_FIXME".to_string(),
                type_: Kind::HhFixme,
                is_declaration: None,
                pos,
                affects_prod_build: true,
            })
        }
        TriviaKind::Ignore => {
            let pos = trivia_pos(positions, t);
            Some(symbol_occurrence::T {
                name: "HH_IGNORE".to_string(),
                type_: Kind::HhIgnore,
                is_declaration: None,
                pos,
                affects_prod_build: true,
            })
        }
        _ => None,
    }
}

fn fixmes(positions: &CstPositions<'_>, tree: &PositionedSyntax) -> Vec<Elt> {
    // `List.fold (children s) ~init:(fixme_elts @ acc) ~f:aux`: the elements
    // of the nodes visited last come first. Here the elements of each node
    // are collected in the order of the visits, and put together backwards.
    fn aux(positions: &CstPositions<'_>, acc: &mut Vec<Vec<Elt>>, s: &PositionedSyntax) {
        let trivia_list: &[PositionedTrivium] = match s.leading_token() {
            None => &[],
            Some(t) => &t.leading,
        };
        let fixme_elts: Vec<Elt> = trivia_list.iter().filter_map(|t| fixme_elt(positions, t)).collect();
        acc.push(fixme_elts);
        for child in s.iter_children() {
            aux(positions, acc, child)
        }
    }
    let mut acc = vec![];
    aux(positions, &mut acc, tree);
    acc.into_iter().rev().flatten().collect()
}

fn token_pos(positions: &CstPositions<'_>, t: &PositionedToken) -> Pos {
    let offset = t.offset + t.leading_width;
    positions.relative_pos(offset, offset + t.width)
}

fn syntax_pos(positions: &CstPositions<'_>, s: &PositionedSyntax) -> Pos {
    // (`start_offset s` already counts the leading trivia, which the OCaml
    // adds a second time.)
    let offset = s.start_offset() + s.leading_width();
    positions.relative_pos(offset, offset + s.width())
}

/// Get keyword positions from the FFP for every keyword that has hover
/// documentation.
fn keywords(positions: &CstPositions<'_>, tree: &PositionedSyntax) -> Vec<Elt> {
    let make_kw = |name: &str, type_: Kind, pos: Pos| symbol_occurrence::T {
        name: name.to_string(),
        type_,
        is_declaration: None,
        pos,
        affects_prod_build: true,
    };
    let elt_of_token = |ctx: Option<KeywordContext>, t: &PositionedToken| -> Option<Elt> {
        use KeywordContext as C;
        use KeywordWithHoverDocs as K;
        match t.kind() {
            TokenKind::Class => match ctx {
                Some(C::ClassishDecl(ClassishDeclKind::DKenumclass)) => {
                    Some(make_kw("enum class", Kind::Keyword(K::EnumClass), token_pos(positions, t)))
                }
                Some(C::ClassType) => Some(make_kw(
                    "class pointer",
                    Kind::BuiltInType(BuiltInTypeHint::BIclassPtr),
                    token_pos(positions, t),
                )),
                _ => Some(make_kw("class", Kind::Keyword(K::Class), token_pos(positions, t))),
            },
            TokenKind::Interface => {
                Some(make_kw("interface", Kind::Keyword(K::Interface), token_pos(positions, t)))
            }
            TokenKind::Trait => Some(make_kw("trait", Kind::Keyword(K::Trait), token_pos(positions, t))),
            TokenKind::Enum => match ctx {
                Some(C::ClassishDecl(ClassishDeclKind::DKenumclass)) => {
                    Some(make_kw("enum class", Kind::Keyword(K::EnumClass), token_pos(positions, t)))
                }
                _ => Some(make_kw("enum", Kind::Keyword(K::Enum), token_pos(positions, t))),
            },
            TokenKind::Type => {
                let kw = match ctx {
                    Some(C::TypeConst) => K::ConstType,
                    _ => K::Type,
                };
                Some(make_kw("type", Kind::Keyword(kw), token_pos(positions, t)))
            }
            TokenKind::Newtype => {
                Some(make_kw("newtype", Kind::Keyword(K::Newtype), token_pos(positions, t)))
            }
            TokenKind::Attribute => {
                Some(make_kw("attribute", Kind::Keyword(K::XhpAttribute), token_pos(positions, t)))
            }
            TokenKind::Children => {
                Some(make_kw("children", Kind::Keyword(K::XhpChildren), token_pos(positions, t)))
            }
            TokenKind::Const => {
                let kw = match ctx {
                    None => K::ConstGlobal,
                    Some(C::TypeConst) => K::ConstType,
                    _ => K::ConstOnClass,
                };
                Some(make_kw("const", Kind::Keyword(kw), token_pos(positions, t)))
            }
            TokenKind::Static => {
                let kw = match ctx {
                    Some(C::Method) => K::StaticOnMethod,
                    _ => K::StaticOnProperty,
                };
                Some(make_kw("static", Kind::Keyword(kw), token_pos(positions, t)))
            }
            TokenKind::Use => Some(make_kw("use", Kind::Keyword(K::Use), token_pos(positions, t))),
            TokenKind::Function => {
                let kw = match ctx {
                    Some(C::Method) => K::FunctionOnMethod,
                    _ => K::FunctionGlobal,
                };
                Some(make_kw("function", Kind::Keyword(kw), token_pos(positions, t)))
            }
            TokenKind::Extends => {
                let kw = match ctx {
                    Some(C::ClassishDecl(ClassishDeclKind::DKclass)) => K::ExtendsOnClass,
                    Some(C::ClassishDecl(ClassishDeclKind::DKinterface)) => K::ExtendsOnInterface,
                    _ => K::ExtendsOnClass,
                };
                Some(make_kw("extends", Kind::Keyword(kw), token_pos(positions, t)))
            }
            TokenKind::Abstract => {
                let kw = match ctx {
                    Some(C::Method) => K::AbstractOnMethod,
                    _ => K::AbstractOnClass,
                };
                Some(make_kw("abstract", Kind::Keyword(kw), token_pos(positions, t)))
            }
            TokenKind::Final => {
                let kw = match ctx {
                    Some(C::Method) => K::FinalOnMethod,
                    _ => K::FinalOnClass,
                };
                Some(make_kw("final", Kind::Keyword(kw), token_pos(positions, t)))
            }
            TokenKind::Public => Some(make_kw("public", Kind::Keyword(K::Public), token_pos(positions, t))),
            TokenKind::Protected => {
                Some(make_kw("protected", Kind::Keyword(K::Protected), token_pos(positions, t)))
            }
            TokenKind::Private => {
                Some(make_kw("private", Kind::Keyword(K::Private), token_pos(positions, t)))
            }
            TokenKind::Async => {
                let kw = match ctx {
                    Some(C::AsyncBlockHeader) => K::AsyncBlock,
                    _ => K::Async,
                };
                Some(make_kw("async", Kind::Keyword(kw), token_pos(positions, t)))
            }
            TokenKind::Await => Some(make_kw("await", Kind::Keyword(K::Await), token_pos(positions, t))),
            TokenKind::Concurrent => {
                Some(make_kw("concurrent", Kind::Keyword(K::Concurrent), token_pos(positions, t)))
            }
            TokenKind::Readonly => {
                let kw = match ctx {
                    Some(C::Method) => K::ReadonlyOnMethod,
                    Some(C::Parameter) => K::ReadonlyOnParameter,
                    Some(C::ReturnType) => K::ReadonlyOnReturnType,
                    _ => K::ReadonlyOnExpression,
                };
                Some(make_kw("readonly", Kind::Keyword(kw), token_pos(positions, t)))
            }
            TokenKind::Internal => {
                Some(make_kw("internal", Kind::Keyword(K::Internal), token_pos(positions, t)))
            }
            TokenKind::Module => {
                let kw = match ctx {
                    Some(C::ModuleDecl(ModuleDeclKind::DKModuleDeclaration)) => {
                        K::ModuleInModuleDeclaration
                    }
                    Some(C::ModuleDecl(ModuleDeclKind::DKModuleMembershipDeclaration)) => {
                        K::ModuleInModuleMembershipDeclaration
                    }
                    _ => K::ModuleInModuleDeclaration,
                };
                Some(make_kw("module", Kind::Keyword(kw), token_pos(positions, t)))
            }
            _ => None,
        }
    };

    // Walk FFP syntax node [s], tracking the current context [ctx]
    // (e.g. are we in an interface?) and accumulate hover items.
    // (`elt :: acc`: the elements are pushed in the order of the visits, and
    // the list is reversed at the end.)
    fn aux(
        positions: &CstPositions<'_>,
        make_kw: &dyn Fn(&str, Kind, Pos) -> Elt,
        elt_of_token: &dyn Fn(Option<KeywordContext>, &PositionedToken) -> Option<Elt>,
        ctx: Option<KeywordContext>,
        acc: &mut Vec<Elt>,
        s: &PositionedSyntax,
    ) {
        let rec = |ctx: Option<KeywordContext>, acc: &mut Vec<Elt>, s: &PositionedSyntax| {
            aux(positions, make_kw, elt_of_token, ctx, acc, s)
        };
        match &s.syntax {
            SyntaxVariant::ClassishDeclaration(cd) => {
                let classish_decl_kind = match &cd.classish_keyword.syntax {
                    SyntaxVariant::Token(t) => match t.kind() {
                        TokenKind::Class => ClassishDeclKind::DKclass,
                        TokenKind::Interface => ClassishDeclKind::DKinterface,
                        _ => ClassishDeclKind::DKclass,
                    },
                    _ => ClassishDeclKind::DKclass,
                };
                let ctx = Some(KeywordContext::ClassishDecl(classish_decl_kind));
                for child in s.iter_children() {
                    rec(ctx, acc, child)
                }
            }
            SyntaxVariant::EnumClassDeclaration(_) => {
                for child in s.iter_children() {
                    rec(Some(KeywordContext::ClassishDecl(ClassishDeclKind::DKenumclass)), acc, child)
                }
            }
            SyntaxVariant::MethodishDeclaration(_) => {
                for child in s.iter_children() {
                    rec(Some(KeywordContext::Method), acc, child)
                }
            }
            SyntaxVariant::FunctionDeclarationHeader(h) => {
                rec(ctx, acc, &h.function_modifiers);
                rec(ctx, acc, &h.function_keyword);
                rec(ctx, acc, &h.function_name);
                rec(ctx, acc, &h.function_type_parameter_list);
                rec(ctx, acc, &h.function_left_paren);
                rec(ctx, acc, &h.function_parameter_list);
                rec(ctx, acc, &h.function_right_paren);
                rec(ctx, acc, &h.function_contexts);
                rec(ctx, acc, &h.function_colon);
                rec(Some(KeywordContext::ReturnType), acc, &h.function_readonly_return);
                rec(ctx, acc, &h.function_type);
                rec(ctx, acc, &h.function_where_clause);
            }
            SyntaxVariant::ParameterDeclaration(_) => {
                for child in s.iter_children() {
                    rec(Some(KeywordContext::Parameter), acc, child)
                }
            }
            SyntaxVariant::AwaitableCreationExpression(a) => {
                rec(ctx, acc, &a.awaitable_attribute_spec);
                rec(Some(KeywordContext::AsyncBlockHeader), acc, &a.awaitable_async);
                rec(ctx, acc, &a.awaitable_compound_statement);
            }
            SyntaxVariant::ModuleDeclaration(_) => {
                for child in s.iter_children() {
                    rec(
                        Some(KeywordContext::ModuleDecl(ModuleDeclKind::DKModuleDeclaration)),
                        acc,
                        child,
                    )
                }
            }
            SyntaxVariant::ModuleMembershipDeclaration(_) => {
                for child in s.iter_children() {
                    rec(
                        Some(KeywordContext::ModuleDecl(
                            ModuleDeclKind::DKModuleMembershipDeclaration,
                        )),
                        acc,
                        child,
                    )
                }
            }
            SyntaxVariant::TypeConstDeclaration(_) => {
                for child in s.iter_children() {
                    rec(Some(KeywordContext::TypeConst), acc, child)
                }
            }
            SyntaxVariant::Contexts(c) => {
                for child in s.iter_children() {
                    rec(ctx, acc, child)
                }
                let is_empty = matches!(c.contexts_types.syntax, SyntaxVariant::Missing);
                if is_empty {
                    acc.push(make_kw("pure function", Kind::PureFunctionContext, syntax_pos(positions, s)))
                }
            }
            SyntaxVariant::Token(t) => {
                if let Some(elt) = elt_of_token(ctx, t) {
                    acc.push(elt)
                }
            }
            SyntaxVariant::ClassPtrTypeSpecifier(_) => {
                for child in s.iter_children() {
                    rec(Some(KeywordContext::ClassType), acc, child)
                }
            }
            _ => {
                for child in s.iter_children() {
                    rec(ctx, acc, child)
                }
            }
        }
    }

    let mut acc = vec![];
    aux(positions, &make_kw, &elt_of_token, None, &mut acc, tree);
    acc.reverse();
    acc
}

pub fn all_symbols(ctx: &provider_context::T, tast: &[tast::Def]) -> Vec<Elt> {
    diagnostics_state::ignore_(|| {
        let mut visitor = SymbolVisitor::new();
        elements(reduce::go(&mut visitor, ctx, tast))
    })
}

/// `Ast_provider.compute_cst ~ctx ~entry` (`Provider_context.PositionedSyntaxTree.make
/// source_text`, with the default parser environment): the source text and
/// the root of the tree. (Not cached in the entry: see the module doc.)
pub fn compute_cst(entry: &provider_context::Entry) -> (full_fidelity_source_text::T, PositionedSyntax) {
    let source_text = ast_provider::compute_source_text(entry);
    let (root, _errors, _state) = positioned_parser::parse_script(
        &full_fidelity_source_text::source_text(&source_text),
        parser_core_types::parser_env::ParserEnv::default(),
    );
    (source_text, root)
}

pub fn all_symbols_ctx(ctx: &provider_context::T, entry: &Arc<provider_context::Entry>) -> Vec<Elt> {
    let (source_text, tree) = compute_cst(entry);
    let positions = CstPositions {
        file_path: Arc::new(full_fidelity_source_text::file_path(&source_text).clone()),
        indexed: IndexedSourceText::new(full_fidelity_source_text::source_text(&source_text)),
    };

    let fixme_symbols = fixmes(&positions, &tree);
    let keyword_symbols = keywords(&positions, &tree);
    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);

    let mut symbols = fixme_symbols;
    symbols.extend(keyword_symbols);
    symbols.extend(all_symbols(ctx, &tast.under_normal_assumptions));
    symbols
}

pub fn go_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    cursor: &file_content::position::T,
    use_declaration_spans: bool,
) -> Vec<Elt> {
    all_symbols_ctx(ctx, entry)
        .into_iter()
        .filter(|x| is_target(use_declaration_spans, cursor, x))
        .collect()
}

#[cfg(test)]
mod tests;
