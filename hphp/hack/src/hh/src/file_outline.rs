// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/file_outline.ml`. See `hh/PORTING.md`.
//!
//! The summaries are generic over the annotations of the AST (`('a, 'b)
//! Aast.*`). The source text (`string`) is bytes; the texts cut out of it for
//! `detail` are made `String`s (`Symbol_definition.t` holds `String`s), which
//! is exact for UTF-8 sources.
//!
//! The printers write to stdout, as the OCaml's `Printf.printf`; the `_to`
//! variants write the same text into a buffer.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::io::Write as _;

use oxidized::aast;
use oxidized::ast_defs;
use oxidized::parser_options::ParserOptions;
use oxidized::pos::Pos;

use crate::aast_utils;
use crate::ast_provider;
use crate::diagnostics as diagnostics;
use crate::docblock_finder;
use crate::full_fidelity_ast as parser;
use crate::ide_parser_cache;
use crate::parser_return;
use crate::pos;
use crate::pos::Absolute;
use crate::provider_context;
use crate::relative_path;
use crate::string_utils;
use crate::symbol_definition;
use crate::symbol_definition::ClassishKind;
use crate::symbol_definition::Kind;
use crate::symbol_definition::MemberKind;
use crate::symbol_definition::Modifier;
use crate::utils;

/// `type outline = string Symbol_definition.t list`
pub type Outline = Vec<symbol_definition::T<Absolute>>;

type Def = symbol_definition::T<Pos>;

fn modifiers_to_list(
    is_final: bool,
    visibility: &ast_defs::Visibility,
    is_abstract: bool,
    is_static: bool,
) -> Vec<Modifier> {
    let mut modifiers = vec![match visibility {
        ast_defs::Visibility::Public => Modifier::Public,
        ast_defs::Visibility::Private => Modifier::Private,
        ast_defs::Visibility::Protected => Modifier::Protected,
        ast_defs::Visibility::Internal => Modifier::Internal,
        ast_defs::Visibility::ProtectedInternal => Modifier::ProtectedInternal,
    }];
    // (Built in reverse by consing, then reversed: the visibility comes
    // first, then final, abstract and static.)
    if is_final {
        modifiers.push(Modifier::Final)
    }
    if is_abstract {
        modifiers.push(Modifier::Abstract)
    }
    if is_static {
        modifiers.push(Modifier::Static)
    }
    modifiers
}

fn pos_of_hint(h: &Option<aast::Hint>) -> Option<&Pos> {
    match h {
        Some(aast::Hint(p, _)) if !pos::equal(&pos::NONE, p) => Some(p),
        _ => None,
    }
}

/// `Pos.get_text_from_pos ~content p`, on the bytes of the source.
fn get_text_from_pos(content: &[u8], p: &Pos) -> String {
    let pos_length = pos::length(p);
    let offset = pos::start_offset(p);
    if offset < 0 || pos_length < 0 || (offset + pos_length) as usize > content.len() {
        panic!(
            "Invalid_argument: pos + len past end: {} + {} > {}",
            offset,
            pos_length,
            content.len()
        );
    }
    String::from_utf8_lossy(&content[offset as usize..(offset + pos_length) as usize]).into_owned()
}

/// `summarize_property` of file_outline.ml:50, shadowed at :639 (which calls it with
/// `~source_text:None`).
fn summarize_property_shadowed<Ex, En>(
    source_text: Option<&[u8]>,
    class_name: &str,
    var: &aast::ClassVar<Ex, En>,
) -> Def {
    let modifiers = modifiers_to_list(var.final_, &var.visibility, var.abstract_, var.is_static);
    let ast_defs::Id(pos, name) = &var.id;
    let detail = source_text.map(|source_text| {
        let readonly = if var.readonly { "readonly " } else { "" };
        let ty = match pos_of_hint(&var.type_.1) {
            Some(p) => get_text_from_pos(source_text, p) + " ",
            None => String::new(),
        };
        let dollar = if var.xhp_attr.is_some() { "" } else { "$" };
        let name = &var.id.1;
        format!("{}{}{}{}", readonly, ty, dollar, name)
    });
    symbol_definition::T {
        kind: Kind::Member {
            member_kind: MemberKind::Property,
            class_name: class_name.to_string(),
        },
        name: name.clone(),
        pos: pos.clone(),
        span: var.span.clone(),
        modifiers,
        params: None,
        docblock: None,
        detail,
    }
}

fn maybe_summarize_property<Ex, En>(
    source_text: Option<&[u8]>,
    class_name: &str,
    skip: &BTreeSet<String>,
    var: &aast::ClassVar<Ex, En>,
) -> Vec<Def> {
    let ast_defs::Id(_, name) = &var.id;
    if skip.contains(name) {
        vec![]
    } else {
        vec![summarize_property_shadowed(source_text, class_name, var)]
    }
}

/// `summarize_class_const` of file_outline.ml:100, shadowed at :642 (which calls it with
/// `~source_text:None`).
fn summarize_class_const_shadowed<Ex, En>(
    source_text: Option<&[u8]>,
    class_name: &str,
    cc: &aast::ClassConst<Ex, En>,
) -> Def {
    let ast_defs::Id(pos, name) = &cc.id;
    let (span, modifiers) = match &cc.kind {
        aast::ClassConstKind::CCConcrete(aast::Expr(_, p, _)) => (pos::btw(pos, p), vec![]),
        aast::ClassConstKind::CCAbstract(Some(aast::Expr(_, p_default, _))) => {
            (pos::btw(pos, p_default), vec![Modifier::Abstract])
        }
        aast::ClassConstKind::CCAbstract(None) => (pos.clone(), vec![Modifier::Abstract]),
    };
    let detail = source_text.map(|source_text| {
        let ty: String = match pos_of_hint(&cc.type_) {
            Some(p) => get_text_from_pos(source_text, p) + " ",
            _ => String::new(),
        };
        ty + &get_text_from_pos(source_text, &span)
    });
    symbol_definition::T {
        kind: Kind::Member {
            member_kind: MemberKind::ClassConst,
            class_name: class_name.to_string(),
        },
        name: name.clone(),
        pos: pos.clone(),
        span,
        modifiers,
        params: None,
        docblock: None,
        detail,
    }
}

fn modifier_of_fun_kind(mut acc: Vec<Modifier>, k: &ast_defs::FunKind) -> Vec<Modifier> {
    match k {
        ast_defs::FunKind::FAsync | ast_defs::FunKind::FAsyncGenerator => {
            acc.insert(0, Modifier::Async);
            acc
        }
        _ => acc,
    }
}

fn modifier_of_param_kind(mut acc: Vec<Modifier>, k: &ast_defs::ParamKind) -> Vec<Modifier> {
    match k {
        ast_defs::ParamKind::Pinout(_) => {
            acc.insert(0, Modifier::Inout);
            acc
        }
        ast_defs::ParamKind::Pnormal => acc,
    }
}

/// `summarize_class_typeconst` of file_outline.ml:138, shadowed at :647 (which calls it with
/// `~source_text:None`).
fn summarize_class_typeconst_shadowed<Ex, En>(
    source_text: Option<&[u8]>,
    class_name: &str,
    t: &aast::ClassTypeconstDef<Ex, En>,
) -> Def {
    let ast_defs::Id(pos, name) = &t.name;
    let modifiers = match &t.kind {
        aast::ClassTypeconst::TCAbstract(_) => vec![Modifier::Abstract],
        _ => vec![],
    };
    let detail = source_text.map(|source_text| get_text_from_pos(source_text, &t.span));
    symbol_definition::T {
        kind: Kind::Member {
            member_kind: MemberKind::TypeConst,
            class_name: class_name.to_string(),
        },
        name: name.clone(),
        pos: pos.clone(),
        span: t.span.clone(),
        modifiers,
        params: None,
        docblock: None,
        detail,
    }
}

fn summarize_param<Ex, En>(param: &aast::FunParam<Ex, En>) -> Def {
    let pos = &param.pos;
    let name = &param.name;
    let param_start = match crate::aast::hint_of_type_hint(&param.type_hint) {
        Some(aast::Hint(p, _)) => p,
        None => pos,
    };
    let param_end = match aast_utils::get_param_default(param) {
        Some(aast::Expr(_, p, _)) => p,
        None => pos,
    };
    let modifiers = modifier_of_param_kind(vec![], &param.callconv);
    let modifiers = match &param.visibility {
        Some(ast_defs::Visibility::Public) => cons(Modifier::Public, modifiers),
        Some(ast_defs::Visibility::Private) => cons(Modifier::Private, modifiers),
        Some(ast_defs::Visibility::Protected) => cons(Modifier::Protected, modifiers),
        _ => modifiers,
    };
    let kind = Kind::Param;
    symbol_definition::T {
        kind,
        name: name.clone(),
        pos: pos.clone(),
        span: pos::btw(param_start, param_end),
        modifiers,
        params: None,
        docblock: None,
        detail: None,
    }
}

fn cons<A>(x: A, mut l: Vec<A>) -> Vec<A> {
    l.insert(0, x);
    l
}

/// `Char.is_whitespace` (Base): space, `\t`, `\n`, `\011`, `\012`, `\r`.
fn is_whitespace(ch: char) -> bool {
    matches!(ch, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r')
}

fn detail_of_fun<Ex, En>(
    source_text: &[u8],
    fun_pos: &Pos,
    sid: &aast::Sid,
    body: &aast::FuncBody<Ex, En>,
) -> String {
    let pos = {
        let start = pos::shrink_to_end(&sid.0);
        let end_ = match body.fb_ast.0.first() {
            Some(aast::Stmt(stmt_pos, _)) if !pos::equal(&pos::NONE, stmt_pos) => {
                pos::shrink_to_start(stmt_pos)
            }
            _ => pos::shrink_to_end(fun_pos),
        };
        pos::btw(&start, &end_)
    };
    let s = "function".to_string() + &get_text_from_pos(source_text, &pos);
    s.trim_end_matches(|ch: char| is_whitespace(ch) || ch == '{' || ch == '}')
        .to_string()
}

/// `summarize_method` of file_outline.ml:214, shadowed at :618 (which calls it with
/// `~source_text:None`).
fn summarize_method_shadowed<Ex, En>(
    source_text: Option<&[u8]>,
    class_name: &str,
    m: &aast::Method_<Ex, En>,
) -> Def {
    let modifiers = modifier_of_fun_kind(vec![], &m.fun_kind);
    let mut modifiers_ = modifiers_to_list(m.final_, &m.visibility, m.abstract_, m.static_);
    modifiers_.extend(modifiers);
    let modifiers = modifiers_;
    let params = Some(m.params.iter().map(summarize_param).collect());
    let name = m.name.1.clone();
    let detail = source_text.map(|source_text| detail_of_fun(source_text, &m.span, &m.name, &m.body));
    symbol_definition::T {
        kind: Kind::Member {
            member_kind: MemberKind::Method,
            class_name: class_name.to_string(),
        },
        name,
        pos: m.name.0.clone(),
        span: m.span.clone(),
        modifiers,
        params,
        docblock: None,
        detail,
    }
}

/// Parser synthesizes AST nodes for implicit properties (defined in constructor
/// parameter lists. We don't want them to show up in outline view
fn params_implicit_fields<Ex, En>(params: &[aast::FunParam<Ex, En>]) -> Vec<String> {
    params
        .iter()
        .filter_map(|p| match p {
            aast::FunParam {
                visibility: Some(_vis),
                name: param_name,
                ..
            } => Some(string_utils::lstrip(param_name, "$").to_string()),
            _ => None,
        })
        .collect()
}

fn class_implicit_fields<Ex, En>(class_: &aast::Class_<Ex, En>) -> Vec<String> {
    class_
        .methods
        .iter()
        .flat_map(|m| {
            let ast_defs::Id(_, name) = &m.name;
            if name == "__construct" {
                params_implicit_fields(&m.params)
            } else {
                vec![]
            }
        })
        .collect()
}

/// `summarize_class` of file_outline.ml:257, shadowed at :622 (which calls it with
/// `~source_text:None`).
fn summarize_class_shadowed<Ex, En>(
    source_text: Option<&[u8]>,
    class_: &aast::Class_<Ex, En>,
    no_children: bool,
) -> Def {
    let class_name = utils::strip_ns(&class_.name.1).to_string();
    let class_name_pos = class_.name.0.clone();
    let c_span = class_.span.clone();
    let modifiers = if class_.final_ { vec![Modifier::Final] } else { vec![] };
    let modifiers = if is_classish_abstract(&class_.kind) {
        cons(Modifier::Abstract, modifiers)
    } else {
        modifiers
    };
    let members = if no_children {
        vec![]
    } else {
        let implicit_props: BTreeSet<String> = class_implicit_fields(class_).into_iter().collect();
        // `acc` is built by consing in OCaml: here the elements are pushed in
        // the same order and the vector is reversed before the sort.
        let mut acc: Vec<Def> = vec![];
        // Summarized class properties
        for cv in &class_.vars {
            let l = maybe_summarize_property(source_text, &class_name, &implicit_props, cv);
            // `List.fold_right ~init:acc ~f:List.cons l`: `l @ acc`.
            for d in l.into_iter().rev() {
                acc.push(d)
            }
        }
        // Summarized xhp_attrs
        for aast::XhpAttr(_, var, _, _) in &class_.xhp_attrs {
            let l = maybe_summarize_property(source_text, &class_name, &implicit_props, var);
            for d in l.into_iter().rev() {
                acc.push(d)
            }
        }
        // Summarized consts
        {
            let source_text_for_class_consts = match &class_.kind {
                ast_defs::ClassishKind::CenumClass(_) => {
                    // The representation of enum classes in the AST is not conducive to us
                    // making a sensible `details` field unless we change our approach significantly.
                    // For now, skip providing `details` for enum classes.
                    // The `id` field for enum class members includes the class name and tag.
                    None
                }
                _ => source_text,
            };
            for c in &class_.consts {
                acc.push(summarize_class_const_shadowed(
                    source_text_for_class_consts,
                    &class_name,
                    c,
                ))
            }
        }
        // Summarized type consts
        for tc in &class_.typeconsts {
            acc.push(summarize_class_typeconst_shadowed(source_text, &class_name, tc))
        }
        // Summarized methods
        for m in &class_.methods {
            acc.push(summarize_method_shadowed(source_text, &class_name, m))
        }
        acc.reverse();
        // `sort_by_line`: `List.sort` is stable, as `sort_by` is.
        acc.sort_by(|x, y| pos::line(&x.pos).cmp(&pos::line(&y.pos)));
        acc
    };
    let classish_kind = match &class_.kind {
        ast_defs::ClassishKind::Cinterface => ClassishKind::Interface,
        ast_defs::ClassishKind::Ctrait => ClassishKind::Trait,
        ast_defs::ClassishKind::CenumClass(_) | ast_defs::ClassishKind::Cenum => ClassishKind::Enum,
        ast_defs::ClassishKind::Cclass(_) => ClassishKind::Class,
    };
    let name = class_name;
    symbol_definition::T {
        kind: Kind::Classish {
            classish_kind,
            members,
        },
        name,
        pos: class_name_pos,
        span: c_span,
        modifiers,
        params: None,
        docblock: None,
        detail: None,
    }
}

/// `Ast_defs.is_classish_abstract`
fn is_classish_abstract(k: &ast_defs::ClassishKind) -> bool {
    matches!(
        k,
        ast_defs::ClassishKind::CenumClass(ast_defs::Abstraction::Abstract)
            | ast_defs::ClassishKind::Cclass(ast_defs::Abstraction::Abstract)
    )
}

/// `summarize_typedef` of file_outline.ml:378, shadowed at :636 (which calls it with
/// `~source_text:None`).
fn summarize_typedef_shadowed<Ex, En>(source_text: Option<&[u8]>, tdef: &aast::Typedef<Ex, En>) -> Def {
    let kind = Kind::Typedef;
    let name = utils::strip_ns(&tdef.name.1).to_string();
    let pos = tdef.name.0.clone();
    let hint_for_end_pos = &tdef.runtime_type;
    let span = pos::btw(&pos, &hint_for_end_pos.0);
    let detail = source_text.map(|source_text| get_text_from_pos(source_text, &span));
    symbol_definition::T {
        kind,
        name,
        pos,
        span,
        modifiers: vec![],
        params: None,
        docblock: None,
        detail,
    }
}

/// `summarize_fun` of file_outline.ml:400, shadowed at :629 (which calls it with
/// `~source_text:None`).
fn summarize_fun_shadowed<Ex, En>(source_text: Option<&[u8]>, fd: &aast::FunDef<Ex, En>) -> Def {
    let f = &fd.fun;
    let modifiers = modifier_of_fun_kind(vec![], &f.fun_kind);
    let params = Some(f.params.iter().map(summarize_param).collect());
    let kind = Kind::Function;
    let name = utils::strip_ns(&fd.name.1).to_string();
    let detail =
        source_text.map(|source_text| detail_of_fun(source_text, &f.span, &fd.name, &f.body));
    symbol_definition::T {
        kind,
        name,
        pos: fd.name.0.clone(),
        span: f.span.clone(),
        modifiers,
        params,
        docblock: None,
        detail,
    }
}

/// `summarize_gconst` of file_outline.ml:421, shadowed at :633 (which calls it with
/// `~source_text:None`).
fn summarize_gconst_shadowed<Ex, En>(source_text: Option<&[u8]>, cst: &aast::Gconst<Ex, En>) -> Def {
    let pos = cst.name.0.clone();
    let gconst_start = match &cst.type_ {
        Some(aast::Hint(p, _)) => p,
        None => &pos,
    };
    let aast::Expr(_, gconst_end, _) = &cst.value;
    let kind = Kind::GlobalConst;
    let name = utils::strip_ns(&cst.name.1).to_string();
    let span = pos::btw(gconst_start, gconst_end);
    let detail = source_text.map(|source_text| get_text_from_pos(source_text, &span));
    symbol_definition::T {
        kind,
        name,
        pos,
        span,
        modifiers: vec![],
        params: None,
        docblock: None,
        detail,
    }
}

pub fn summarize_local<P: Clone>(name: &str, span: &P) -> symbol_definition::T<P> {
    let kind = Kind::LocalVar;
    symbol_definition::T {
        kind,
        name: name.to_string(),
        pos: span.clone(),
        span: span.clone(),
        modifiers: vec![],
        params: None,
        docblock: None,
        detail: None,
    }
}

pub fn summarize_module_def<Ex, En>(md: &aast::ModuleDef<Ex, En>) -> Def {
    let kind = Kind::Module;
    let name = md.name.1.clone();
    let span = md.span.clone();
    let doc_comment = &md.doc_comment;
    let docblock = match doc_comment {
        None => None,
        Some(dc) => Some(dc.1.clone()),
    };
    symbol_definition::T {
        kind,
        name,
        pos: span.clone(),
        span,
        modifiers: vec![],
        params: None,
        docblock,
        detail: None,
    }
}

fn outline_ast<Ex, En>(ast: &[aast::Def<Ex, En>], source_text: Option<&[u8]>) -> Outline {
    let outline: Vec<Def> = ast
        .iter()
        .filter_map(|d| match d {
            aast::Def::Fun(f) => Some(summarize_fun_shadowed(source_text, f)),
            aast::Def::Class(c) => Some(summarize_class_shadowed(source_text, c, false)),
            aast::Def::Typedef(t) => Some(summarize_typedef_shadowed(source_text, t)),
            aast::Def::Constant(c) => Some(summarize_gconst_shadowed(source_text, c)),
            aast::Def::ClassAlias(_)
            | aast::Def::Namespace(_)
            | aast::Def::NamespaceUse(_)
            | aast::Def::SetNamespaceEnv(_)
            | aast::Def::FileAttributes(_)
            | aast::Def::Stmt(_)
            | aast::Def::Module(_)
            | aast::Def::SetModule(_) => None,
        })
        .collect();

    outline.iter().map(symbol_definition::to_absolute).collect()
}

fn should_add_docblock<P>(k: &Kind<P>) -> bool {
    match k {
        Kind::Function
        | Kind::Classish { .. }
        | Kind::Member { .. }
        | Kind::GlobalConst
        | Kind::Typedef
        | Kind::Module => true,
        Kind::LocalVar | Kind::TypeVar | Kind::Param => false,
    }
}

fn add_def_docblock(
    finder: &docblock_finder::Finder,
    previous_def_line: isize,
    def: symbol_definition::T<Absolute>,
) -> (isize, symbol_definition::T<Absolute>) {
    let line = pos::line(&def.pos);
    let docblock = if should_add_docblock(&def.kind) {
        docblock_finder::find_docblock(finder, previous_def_line, line)
    } else {
        None
    };
    (line, symbol_definition::T { docblock, ..def })
}

fn add_docblocks(defs: Outline, comments: &parser_return::Comments) -> Outline {
    let finder = docblock_finder::make_docblock_finder(comments);
    fn map_def(
        finder: &docblock_finder::Finder,
        acc: isize,
        def: symbol_definition::T<Absolute>,
    ) -> (isize, symbol_definition::T<Absolute>) {
        let (acc, mut def) = add_def_docblock(finder, acc, def);
        let kind = std::mem::replace(&mut def.kind, Kind::Function);
        let (acc, kind) = match kind {
            Kind::Classish {
                classish_kind,
                members,
            } => {
                let (acc, members) = map_def_list(finder, acc, members);
                (
                    acc,
                    Kind::Classish {
                        classish_kind,
                        members,
                    },
                )
            }
            kind => (acc, kind),
        };
        (acc, symbol_definition::T { kind, ..def })
    }
    fn map_def_list(
        finder: &docblock_finder::Finder,
        acc: isize,
        defs: Outline,
    ) -> (isize, Outline) {
        let mut acc = acc;
        let mut res = Vec::with_capacity(defs.len());
        for def in defs {
            let (acc_, def) = map_def(finder, acc, def);
            acc = acc_;
            res.push(def);
        }
        (acc, res)
    }
    map_def_list(&finder, 0, defs).1
}

pub fn outline(popt: &ParserOptions, source_text: &[u8]) -> Outline {
    let parser_return::T { ast, comments, .. } = {
        diagnostics::ignore_(|| {
            if ide_parser_cache::is_enabled() {
                ide_parser_cache::with_ide_cache(|| {
                    ide_parser_cache::get_ast(popt, &relative_path::DEFAULT, source_text)
                })
            } else {
                let env = parser::make_env(
                    None,
                    None,
                    None,
                    Some(true),
                    None,
                    None,
                    Some(popt.clone()),
                    None,
                    relative_path::DEFAULT,
                );
                parser::from_text_with_legacy(&env, source_text)
            }
        })
    };
    let result = outline_ast(&ast.0, Some(source_text));
    add_docblocks(result, &comments)
}

pub fn outline_entry_no_comments(popt: &ParserOptions, entry: &provider_context::Entry) -> Outline {
    let source_text = provider_context::get_file_contents_if_present(entry);
    let ast = ast_provider::compute_ast(popt, entry);
    outline_ast(&ast.0, source_text.as_ref().map(|s| s.as_slice()))
}

fn print_def_to<P: pos::APos>(
    out: &mut String,
    short_pos: bool,
    indent: &str,
    def: &symbol_definition::T<P>,
    print_pos: &dyn Fn(&P) -> String,
    print_span: &dyn Fn(&P) -> String,
) {
    let symbol_definition::T {
        name,
        kind,
        pos,
        span,
        modifiers,
        params,
        docblock,
        detail,
    } = def;
    let _ = writeln!(out, "{}{}", indent, name);
    let _ = writeln!(out, "{}  kind: {}", indent, symbol_definition::string_of_kind(kind));
    if let Some(id) = symbol_definition::identifier(def) {
        let _ = writeln!(out, "{}  id: {}", indent, id);
    }
    let _ = writeln!(out, "{}  position: {}", indent, print_pos(pos));
    let _ = writeln!(out, "{}  span: {}", indent, print_span(span));
    let _ = write!(out, "{}  modifiers: ", indent);
    for x in modifiers {
        let _ = write!(out, "{} ", symbol_definition::string_of_modifier(x));
    }
    out.push('\n');
    if let Some(detail) = detail {
        let _ = writeln!(out, "{}  detail: {}", indent, detail);
    }
    if let Some(x) = params {
        let _ = writeln!(out, "{}  params:", indent);
        print_to(out, short_pos, &format!("{}    ", indent), x, print_pos, print_span);
    }
    if let Some(x) = docblock {
        let _ = writeln!(out, "{}  docblock:", indent);
        let _ = writeln!(out, "{}", x);
    }
    out.push('\n');
    match kind {
        Kind::Classish { members, .. } => print_to(
            out,
            short_pos,
            &format!("{}  ", indent),
            members,
            print_pos,
            print_span,
        ),
        _ => {}
    }
}

fn print_to<P: pos::APos>(
    out: &mut String,
    short_pos: bool,
    indent: &str,
    defs: &[symbol_definition::T<P>],
    print_pos: &dyn Fn(&P) -> String,
    print_span: &dyn Fn(&P) -> String,
) {
    for def in defs {
        print_def_to(out, short_pos, indent, def, print_pos, print_span)
    }
}

/// `(print_pos, print_span)` of `print_def`.
fn printers(
    short_pos: bool,
) -> (
    &'static dyn Fn(&Absolute) -> String,
    &'static dyn Fn(&Absolute) -> String,
) {
    if short_pos {
        (
            &|p: &Absolute| pos::string_no_file(p),
            &|p: &Absolute| pos::multiline_string_no_file(p),
        )
    } else {
        (&|p: &Absolute| pos::string(p), &|p: &Absolute| pos::multiline_string(p))
    }
}

/// `print_def ?short_pos indent def`, into a buffer.
pub fn print_def_to_string(short_pos: Option<bool>, indent: &str, def: &symbol_definition::T<Absolute>) -> String {
    let short_pos = short_pos.unwrap_or(false);
    let (print_pos, print_span) = printers(short_pos);
    let mut out = String::new();
    print_def_to(&mut out, short_pos, indent, def, print_pos, print_span);
    out
}

/// `print ?short_pos defs`, into a buffer.
pub fn print_to_string(short_pos: Option<bool>, defs: &[symbol_definition::T<Absolute>]) -> String {
    let short_pos = short_pos.unwrap_or(false);
    let (print_pos, print_span) = printers(short_pos);
    let mut out = String::new();
    print_to(&mut out, short_pos, "", defs, print_pos, print_span);
    out
}

pub fn print_def(short_pos: Option<bool>, indent: &str, def: &symbol_definition::T<Absolute>) {
    let s = print_def_to_string(short_pos, indent, def);
    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(s.as_bytes());
}

pub fn print(short_pos: Option<bool>, defs: &[symbol_definition::T<Absolute>]) {
    let s = print_to_string(short_pos, defs);
    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(s.as_bytes());
}

pub fn summarize_method<Ex, En>(s: &str, meth: &aast::Method_<Ex, En>) -> Def {
    summarize_method_shadowed(None, s, meth)
}

pub fn summarize_class<Ex, En>(class_: &aast::Class_<Ex, En>, no_children: bool) -> Def {
    summarize_class_shadowed(None, class_, no_children)
}

pub fn summarize_fun<Ex, En>(fd: &aast::FunDef<Ex, En>) -> Def {
    summarize_fun_shadowed(None, fd)
}

pub fn summarize_gconst<Ex, En>(cst: &aast::Gconst<Ex, En>) -> Def {
    summarize_gconst_shadowed(None, cst)
}

pub fn summarize_typedef<Ex, En>(tdef: &aast::Typedef<Ex, En>) -> Def {
    summarize_typedef_shadowed(None, tdef)
}

pub fn summarize_property<Ex, En>(class_name: &str, var: &aast::ClassVar<Ex, En>) -> Def {
    summarize_property_shadowed(None, class_name, var)
}

pub fn summarize_class_const<Ex, En>(class_name: &str, c_const: &aast::ClassConst<Ex, En>) -> Def {
    summarize_class_const_shadowed(None, class_name, c_const)
}

pub fn summarize_class_typeconst<Ex, En>(
    class_name: &str,
    tconst_def: &aast::ClassTypeconstDef<Ex, En>,
) -> Def {
    summarize_class_typeconst_shadowed(None, class_name, tconst_def)
}
