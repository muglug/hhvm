// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/autocomplete_service.ml`. See `hh/PORTING.md`.
//!
//! When autocompletion is called, we insert an autocomplete token "AUTO332"
//! at the position of the cursor. For example, if the user has this in their
//! IDE, with | showing their cursor:
//!
//! ```text
//!     $x = new Fo|
//! ```
//!
//! We see the following TAST:
//!
//! ```text
//!     $x = new FoAUTO332
//! ```
//!
//! This allows us to walk the syntax tree and identify the position of the
//! cursor by looking for names containing "AUTO332".
//!
//! The global `ref`s of the OCaml (`autocomplete_items`,
//! `autocomplete_is_complete`, `auto_complete_for_global`) are the fields of a
//! [`State`] that [`go_ctx`] makes (`reset ()`) and threads through every
//! function that reads or writes them. `autocomplete_items` is a list to which
//! `add_res` prepends: here the items are pushed, and the list is the vector
//! reversed.
//!
//! The environment of OCaml is a value: a function that makes a new one
//! (localizing, fresh type variables) and drops it leaves the caller's as it
//! was. Here such a function works on a copy of the caller's environment.

use std::collections::BTreeSet;
use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor;
use oxidized::ast_defs;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::positioned_token::PositionedToken;
use parser_core_types::positioned_trivia::PositionedTrivium;
use parser_core_types::source_text::SourceText;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::syntax_trait::SyntaxTrait;
use parser_core_types::trivia_kind::TriviaKind;
use pos::ToOxidized;

use crate::autocomplete_types::AutocompleteItem;
use crate::autocomplete_types::InsertText;
use crate::autocomplete_types::LegacyAutocompleteContext;
use crate::autocomplete_types::SnippetWithFallback;
use crate::autocomplete_types::AUTOCOMPLETE_TOKEN;
use crate::autocomplete_types::AUTOCOMPLETE_TOKEN_LENGTH;
use crate::decl_entry;
use crate::decl_utils;
use crate::file_content;
use crate::file_info::SiKind;
use crate::folded_class as cls;
use crate::ide_api_types;
use crate::local_id;
use crate::naming_provider;
use crate::naming_special_names::classes::C_STRING;
use crate::naming_table;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path;
use crate::search_types;
use crate::search_types::AutocompleteType;
use crate::search_types::SiComplete;
use crate::search_utils;
use crate::search_utils::SiEnv;
use crate::symbol_index;
use crate::symbol_index_core;
use crate::symbol_occurrence;
use crate::symbol_occurrence::BuiltInTypeHint;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor;
use crate::tast_visitor::IterParams;
use crate::typing_defs;
use crate::typing_defs::DeclTy;
use crate::typing_defs::DeclTy_;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::user_attributes_as_map;
use crate::utils;
use crate::utils::with_complete_flag;

type Res = Result<(), ()>;

/// `Typing_defs.phase_ty`
#[derive(Clone, Debug)]
pub enum PhaseTy {
    DeclTy(DeclTy),
    LoclTy(Ty),
}

/// The global state of the OCaml (`autocomplete_items`,
/// `autocomplete_is_complete`, `auto_complete_for_global`).
#[derive(Debug)]
pub struct State {
    /// `!autocomplete_items`, in the order of the `add_res` calls (the OCaml
    /// list is the reverse).
    items: Vec<AutocompleteItem>,
    is_complete: bool,
    auto_complete_for_global: String,
}

impl State {
    /// `reset ()`
    fn reset() -> Self {
        State {
            items: vec![],
            is_complete: true,
            auto_complete_for_global: String::new(),
        }
    }

    /// `add_res`
    fn add_res(&mut self, res: AutocompleteItem) {
        self.items.push(res)
    }

    /// `!autocomplete_items`, in the order of the list.
    fn items(&self) -> Vec<AutocompleteItem> {
        self.items.iter().rev().cloned().collect()
    }
}

/// Take the results, look them up, and add file position information.
pub fn add_position_to_results(
    ctx: &provider_context::T,
    raw_results: &[search_types::SiItem],
) -> search_utils::Result {
    raw_results
        .iter()
        .filter_map(|r| {
            symbol_index_core::get_pos_for_item_opt(ctx, r).map(|pos| search_utils::Term {
                name: r.fullname.clone(),
                pos,
                result_type: r.kind,
            })
        })
        .collect()
}

pub const MAX_RESULTS: isize = 100;

/// `String_utils.rstrip`
pub(crate) fn rstrip<'a>(s: &'a str, suffix: &str) -> &'a str {
    s.strip_suffix(suffix).unwrap_or(s)
}

/// `String.sub s 0 (String.length s - autocomplete_token_length)` (raises
/// `Invalid_argument` on a string shorter than the token).
fn strip_suffix(s: &str) -> String {
    let len = s.len() as isize - AUTOCOMPLETE_TOKEN_LENGTH;
    if len < 0 {
        panic!("Invalid_argument(\"String.sub / Bytes.sub\")")
    }
    String::from_utf8_lossy(&s.as_bytes()[..len as usize]).into_owned()
}

fn strip_supportdyn_decl(ty: &DeclTy) -> DeclTy {
    match ty.node_ref() {
        DeclTy_::Tapply(x) if x.1.len() == 1 && x.0.id().as_str() == sn::classes::SUPPORT_DYN => {
            x.1[0].clone()
        }
        _ => ty.clone(),
    }
}

fn strip_like_decl(ty: &DeclTy) -> DeclTy {
    match ty.node_ref() {
        DeclTy_::Tlike(ty) => ty.clone(),
        _ => ty.clone(),
    }
}

fn strip_like_ret_type_decl(ty: &DeclTy) -> DeclTy {
    match strip_supportdyn_decl(ty).node_ref() {
        DeclTy_::Tfun(ft) => {
            let mut ft = (**ft).clone();
            ft.ret = strip_like_decl(&ft.ret);
            DeclTy::new(ty.reason().clone(), DeclTy_::Tfun(Box::new(ft)))
        }
        _ => ty.clone(),
    }
}

/// We strip off ~ from types before matching on the underlying structure of
/// the type. Note that we only do this for matching, not pretty-printing of
/// types, as we want to retain ~ when showing types in suggestions.
/// (The first `expand_and_strip_dynamic` of the OCaml, which returns the
/// environment.)
fn expand_and_strip_dynamic_env(env: &mut Env, ty: Ty) -> Ty {
    let ty = tast_env::expand_type(env, ty);
    let ty = tast_env::strip_dynamic(env, ty);
    tast_env::expand_type(env, ty)
}

/// Strip both ~ and supportdyn off a type
fn expand_and_strip_supportdyn(env: &Env, ty: Ty) -> Ty {
    let mut env = env.clone();
    let ty = expand_and_strip_dynamic_env(&mut env, ty);
    let (_, ty) = crate::typing_utils::strip_supportdyn(&mut env, ty);
    ty
}

/// Strip ~ and supportdyn off a type that is expected to be a function type.
/// Also expand splatted tuples to multiple parameters
fn expand_fun(env: &Env, ty: Ty) -> Option<typing_defs::FunType> {
    let ty = expand_and_strip_supportdyn(env, ty);
    let ty = tast_env::expand_splat_param_in_function_type(env, ty);
    match typing_defs::get_node(&ty) {
        Ty_::Tfun(ft) => Some((**ft).clone()),
        _ => None,
    }
}

/// The second `expand_and_strip_dynamic` of the OCaml (drops the
/// environment).
fn expand_and_strip_dynamic(env: &Env, ty: Ty) -> Ty {
    let mut env = env.clone();
    expand_and_strip_dynamic_env(&mut env, ty)
}

fn matches_auto_complete_suffix(x: &str) -> bool {
    x.ends_with(AUTOCOMPLETE_TOKEN)
}

/// Does [str] look like something we should offer code completion on?
fn is_auto_complete(st: &State, str: &str) -> bool {
    let results_without_keywords = st.items.iter().any(|res| res.res_kind != SiKind::SIKeyword);
    if !results_without_keywords {
        matches_auto_complete_suffix(str)
    } else {
        false
    }
}

fn replace_pos_of_id(strip_xhp_colon: bool, (pos, text): (&Pos, &str)) -> ide_api_types::Range {
    let (_, name) = utils::split_ns_from_name(text);
    let name = if matches_auto_complete_suffix(name) {
        strip_suffix(name)
    } else {
        name.to_string()
    };
    let name = if strip_xhp_colon {
        utils::strip_xhp_ns(&name).to_string()
    } else {
        name
    };
    let range = ide_api_types::pos_to_range(pos);
    let ed = file_content::position::move_back(&range.ed, AUTOCOMPLETE_TOKEN_LENGTH);
    let st = file_content::position::move_back(&ed, name.len() as isize);
    ide_api_types::Range { st, ed }
}

/// `replace_pos_of_id` without `~strip_xhp_colon`.
fn replace_pos(id: (&Pos, &str)) -> ide_api_types::Range {
    replace_pos_of_id(false, id)
}

pub fn autocomplete_result_to_json(res: &AutocompleteItem) -> crate::yojson::safe::T {
    use crate::yojson::safe::T as J;
    let name = &res.res_label;
    let pos = &res.res_decl_pos;
    let ty = &res.res_detail;
    J::Assoc(vec![
        ("name".to_string(), J::String(name.clone())),
        ("type".to_string(), J::String(ty.clone())),
        ("pos".to_string(), crate::pos::json(pos)),
        // legacy field, left here in case clients need it
        ("expected_ty".to_string(), J::Bool(false)),
    ])
}

fn autocomplete_id(st: &mut State, id: &ast_defs::Id) {
    if is_auto_complete(st, &id.1) {
        st.auto_complete_for_global = id.1.clone()
    }
}

fn force(ce: &cls::ClassElt) -> DeclTy {
    (*ce.ce_type).clone()
}

fn get_class_elt_types(
    is_method: bool,
    env: &Env,
    class_: &cls::T,
    cid: Option<&oxidized::nast::ClassId_>,
    elts: Vec<(String, cls::ClassElt)>,
) -> Vec<(String, DeclTy)> {
    let is_visible = |elt: &cls::ClassElt| {
        tast_env::is_visible(
            is_method,
            env,
            (&elt.ce_visibility, typing_defs::get_ce_lsb(elt)),
            cid,
            class_,
        )
    };
    elts.into_iter()
        .filter(|(_, elt)| is_visible(elt))
        .map(|(id, elt)| (id, force(&elt)))
        .collect()
}

fn get_class_req_attrs(
    env: &Env,
    classname: &str,
    cid: Option<&oxidized::nast::ClassId_>,
) -> Vec<String> {
    let req_attrs = |cls: &cls::T| -> Vec<String> {
        cls::props(cls)
            .into_iter()
            .filter(|(_, ce)| {
                tast_env::is_visible(
                    false,
                    env,
                    (&ce.ce_visibility, typing_defs::get_ce_lsb(ce)),
                    cid,
                    cls,
                )
            })
            .filter(|(_, ce)| crate::xhp_attribute::opt_is_required(typing_defs::get_ce_xhp_attr(ce)))
            .map(|(name, _)| utils::strip_xhp_ns(&name).to_string())
            .collect()
    };
    match decl_entry::to_option(tast_env::get_class(env, classname)) {
        Some(c) => req_attrs(&c),
        None => vec![],
    }
}

fn get_class_is_child_empty(env: &Env, classname: &str) -> bool {
    match decl_entry::to_option(tast_env::get_class(env, classname)) {
        Some(c) => cls::xhp_marked_empty(&c),
        None => false,
    }
}

fn decl_get_pos(ty: &DeclTy) -> oxidized::pos_or_decl::PosOrDecl {
    decl_utils::get_pos(ty).to_oxidized()
}

/// `Server_pos.resolve`
fn server_pos_resolve(env: &Env, p: &oxidized::pos_or_decl::PosOrDecl) -> Pos {
    naming_provider::resolve_position(&tast_env::get_ctx(env), p)
}

fn get_pos_for(env: &Env, ty: &PhaseTy) -> crate::pos::Absolute {
    let p = match ty {
        PhaseTy::LoclTy(loclt) => typing_defs::get_pos(loclt),
        PhaseTy::DeclTy(declt) => decl_get_pos(declt),
    };
    crate::pos::to_absolute(&server_pos_resolve(env, &p))
}

// ---------------------------------------------------------------------------
// Function parameters, of decl and locl function types (the OCaml functions
// are polymorphic over the phase).

/// What the polymorphic functions read of a `'a fun_param`.
trait ParamLike {
    fn fp_name(&self) -> Option<&str>;
    fn fp_flags(&self) -> oxidized::typing_defs_flags::FunParamFlags;
    /// `param_snippet_prefix param.fp_type`
    fn param_snippet_prefix(&self) -> &'static str;
}

impl ParamLike for typing_defs::FunParam {
    fn fp_name(&self) -> Option<&str> {
        self.name.as_deref()
    }
    fn fp_flags(&self) -> oxidized::typing_defs_flags::FunParamFlags {
        self.flags
    }
    fn param_snippet_prefix(&self) -> &'static str {
        // It is more appropriate to create a label place holder instead of a
        // variable placeholder when the parameter type is an enum class label.
        match typing_defs::get_node(&self.type_) {
            Ty_::Tnewtype(label_kind, _, _) if label_kind == sn::classes::ENUM_CLASS_LABEL => "#",
            _ => "\\$",
        }
    }
}

impl ParamLike for typing_defs::DeclFunParam {
    fn fp_name(&self) -> Option<&str> {
        self.name.as_ref().map(|s| s.as_str())
    }
    fn fp_flags(&self) -> oxidized::typing_defs_flags::FunParamFlags {
        self.flags
    }
    fn param_snippet_prefix(&self) -> &'static str {
        match self.ty.node_ref() {
            DeclTy_::Tapply(x) if x.0.id().as_str() == sn::classes::ENUM_CLASS_LABEL => "#",
            _ => "\\$",
        }
    }
}

/// `Typing_defs.Named_params.name_of_named_param`
fn name_of_named_param<P: ParamLike>(fp: &P) -> Option<String> {
    if fp.fp_flags().contains(oxidized::typing_defs_flags::FunParamFlags::NAMED) {
        fp.fp_name()
            .map(|raw_name| raw_name.strip_prefix('$').unwrap_or(raw_name).to_string())
    } else {
        None
    }
}

/// What the polymorphic functions read of a `'a fun_type`.
trait FunLike {
    type Param: ParamLike + Clone;
    fn ft_params(&self) -> &[Self::Param];
    fn ft_flags(&self) -> oxidized::typing_defs_flags::FunTypeFlags;
}

impl FunLike for typing_defs::FunType {
    type Param = typing_defs::FunParam;
    fn ft_params(&self) -> &[Self::Param] {
        &self.params
    }
    fn ft_flags(&self) -> oxidized::typing_defs_flags::FunTypeFlags {
        self.flags
    }
}

impl FunLike for typing_defs::DeclFunType {
    type Param = typing_defs::DeclFunParam;
    fn ft_params(&self) -> &[Self::Param] {
        &self.params
    }
    fn ft_flags(&self) -> oxidized::typing_defs_flags::FunTypeFlags {
        self.flags
    }
}

/// `Typing_defs.ft_params_without_named_variadic`
fn ft_params_without_named_variadic<F: FunLike>(ft: &F) -> &[F::Param] {
    let params = ft.ft_params();
    if ft.ft_flags().contains(oxidized::typing_defs_flags::FunTypeFlags::NAMED_VARIADIC)
        && !params.is_empty()
    {
        &params[..params.len() - 1]
    } else {
        params
    }
}

/// `Typing_defs.arity_and_names_required`
fn arity_and_names_required<F: FunLike>(ft: &F) -> (isize, BTreeSet<String>) {
    use oxidized::typing_defs_flags::FunParamFlags;
    let mut names_required = BTreeSet::new();
    let mut positional = 0isize;
    for fp in ft_params_without_named_variadic(ft) {
        let flags = fp.fp_flags();
        if flags.contains(FunParamFlags::IS_OPTIONAL) || flags.contains(FunParamFlags::SPLAT) {
            continue;
        }
        match name_of_named_param(fp) {
            Some(name) => {
                names_required.insert(name);
            }
            None => positional += 1,
        }
    }
    let arity_required =
        if ft.ft_flags().contains(oxidized::typing_defs_flags::FunTypeFlags::VARIADIC) {
            positional - 1
        } else {
            positional
        };
    (arity_required, names_required)
}

/// A function call snippet looks like this:
///
///    fun_name(${1:\$first_arg}, ${2:\$second_arg})
///
/// The syntax for snippets is described here:
/// https://code.visualstudio.com/docs/editor/userdefinedsnippets#_variables
fn snippet_for_params<P: ParamLike>(params: &[P]) -> String {
    let param_templates: Vec<String> = params
        .iter()
        .enumerate()
        .map(|(i, param)| {
            let prefix = param.param_snippet_prefix();
            let named_arg_snippet = match name_of_named_param(param) {
                Some(name) => format!("{}=", name),
                None => String::new(),
            };
            let placeholder = match param.fp_name() {
                Some(param_name) => param_name.replacen('$', prefix, 1),
                None => format!("{}{}", prefix, i + 1),
            };
            format!("{}${{{}:{}}}", named_arg_snippet, i + 1, placeholder)
        })
        .collect();
    param_templates.join(", ")
}

fn get_snippet_for_xhp_req_attrs(tag: &str, attrs: &[String], has_children: bool) -> String {
    let content = if !attrs.is_empty() {
        let attr_content = attrs
            .iter()
            .enumerate()
            .map(|(i, name)| format!("{}={{${{{}}}}}", name, i + 1))
            .collect::<Vec<_>>()
            .join(" ");
        format!("{} {}", tag, attr_content)
    } else {
        tag.to_string()
    };
    if has_children {
        format!("{}>$0</{}>", content, tag)
    } else {
        format!("{} />", content)
    }
}

fn insert_text_for_xhp_req_attrs(tag: &str, attrs: &[String], has_children: bool) -> InsertText {
    let content = get_snippet_for_xhp_req_attrs(tag, attrs, has_children);
    let insert_type = !attrs.is_empty() && has_children;
    if insert_type {
        InsertText::InsertAsSnippet(SnippetWithFallback {
            snippet: content,
            fallback: tag.to_string(),
        })
    } else {
        InsertText::InsertLiterally(content)
    }
}

fn required_params_of_fun_type<F: FunLike>(ft: &F) -> Vec<F::Param> {
    let (arity_count, required_named_params) = arity_and_names_required(ft);
    let mut positional_param_count = 0isize;
    let mut required_params = vec![];
    for fp in ft.ft_params() {
        match name_of_named_param(fp) {
            Some(name) if required_named_params.contains(&name) => required_params.push(fp.clone()),
            // optional named param
            Some(_) => {}
            // optional positional param
            None if positional_param_count >= arity_count => positional_param_count += 1,
            None => {
                positional_param_count += 1;
                required_params.push(fp.clone())
            }
        }
    }
    required_params
}

/// If we're autocompleting a call (function or method), insert a template
/// for the arguments as well as function name.
fn insert_text_for_fun_call(
    env: &Env,
    autocomplete_context: &LegacyAutocompleteContext,
    fun_name: &str,
    ft: &typing_defs::FunType,
) -> InsertText {
    if autocomplete_context.char_at_pos == b'(' {
        // Arguments are present already, e.g. the user has ->AUTO332(1, 2).
        // We don't want to insert params when we complete the name, or we
        // end up with ->methName()(1, 2).
        InsertText::InsertLiterally(fun_name.to_string())
    } else {
        let params = if tast_env::is_in_expr_tree(env) {
            // Helper functions in expression trees don't have relevant
            // parameter names on their decl, so don't autofill
            // parameters.
            vec![]
        } else {
            required_params_of_fun_type(ft)
        };
        let fallback = format!("{}()", fun_name);
        if params.is_empty() {
            InsertText::InsertLiterally(fallback)
        } else {
            let snippet = format!("{}({})", fun_name, snippet_for_params(&params));
            InsertText::InsertAsSnippet(SnippetWithFallback { snippet, fallback })
        }
    }
}

fn insert_text_for_ty(
    env: &Env,
    autocomplete_context: &LegacyAutocompleteContext,
    label: &str,
    ty: &PhaseTy,
) -> InsertText {
    let mut env = env.clone();
    let ty = match ty {
        PhaseTy::LoclTy(locl_ty) => locl_ty.clone(),
        PhaseTy::DeclTy(decl_ty) => tast_env::localize_no_subst(&mut env, true, decl_ty),
    };
    // Functions that support dynamic will be wrapped by supportdyn<_>
    match expand_fun(&env, ty) {
        Some(ft) => insert_text_for_fun_call(&env, autocomplete_context, label, &ft),
        _ => InsertText::InsertLiterally(label.to_string()),
    }
}

/// `Str.first_chars s 1` (raises on the empty string).
fn first_char(s: &str) -> String {
    match s.as_bytes().first() {
        Some(c) => String::from_utf8_lossy(&[*c]).into_owned(),
        None => panic!("Invalid_argument(\"String.sub / Bytes.sub\")"),
    }
}

fn make_item(
    res_decl_pos: crate::pos::Absolute,
    res_replace_pos: ide_api_types::Range,
    res_base_class: Option<String>,
    res_detail: String,
    res_label: String,
    res_insert_text: InsertText,
    res_fullname: String,
    res_kind: SiKind,
) -> AutocompleteItem {
    AutocompleteItem {
        res_decl_pos,
        res_replace_pos,
        res_base_class,
        res_detail,
        res_label,
        res_insert_text,
        res_fullname,
        res_kind,
        res_documentation: None,
        res_sort_text: None,
        res_filter_text: None,
        res_additional_edits: vec![],
    }
}

fn absolute_none() -> crate::pos::Absolute {
    crate::pos::to_absolute(&Pos::NONE)
}

fn autocomplete_shape_key(
    st: &mut State,
    autocomplete_context: &LegacyAutocompleteContext,
    fields: &typing_defs::t_shape_map::TShapeMap<typing_defs::ShapeFieldType>,
    id: (&Pos, &str),
) {
    if is_auto_complete(st, id.1) {
        // not the same as `prefix == ""` in namespaces
        let have_prefix = crate::pos::length(id.0) > AUTOCOMPLETE_TOKEN_LENGTH;
        let prefix = strip_suffix(id.1);
        let mut add = |name: &typing_defs::t_shape_map::TShapeField| {
            use crate::typing_defs::TshapeFieldName as F;
            let (code, kind, pos) = match &name.0 {
                F::TSFregexGroup(oxidized::typing_defs_core::PosString(pos, str)) => {
                    (str.clone(), SiKind::SILiteral, pos.clone())
                }
                F::TSFlitStr(oxidized::typing_defs_core::PosByteString(pos, str)) => {
                    let quote = if have_prefix {
                        first_char(&prefix)
                    } else {
                        "'".to_string()
                    };
                    let str = String::from_utf8_lossy(str.as_slice());
                    (format!("{}{}{}", quote, str, quote), SiKind::SILiteral, pos.clone())
                }
                F::TSFclassConst((pos, cid), oxidized::typing_defs_core::PosString(_, mid)) => (format!("{}::{}", cid, mid), SiKind::SIClassConstant, pos.clone()),
            };
            if !have_prefix || code.starts_with(&prefix) {
                let res_insert_text = if autocomplete_context.is_before_apostrophe {
                    rstrip(&code, "'").to_string()
                } else {
                    code.clone()
                };
                let complete = make_item(
                    crate::pos::to_absolute(&crate::pos_or_decl::unsafe_to_raw_pos(pos)),
                    replace_pos(id),
                    None,
                    search_utils::kind_to_string(kind).to_string(),
                    res_insert_text.clone(),
                    InsertText::InsertLiterally(res_insert_text),
                    code,
                    kind,
                );
                st.add_res(complete)
            }
        };
        // `TShapeMap.keys` (a fold that conses): in decreasing order.
        for name in fields.keys().rev() {
            add(name)
        }
    }
}

fn autocomplete_member(
    st: &mut State,
    is_static: bool,
    autocomplete_context: &LegacyAutocompleteContext,
    env: &Env,
    ety_env: &typing_defs::ExpandEnv,
    class_: &cls::T,
    cid: Option<&oxidized::nast::ClassId_>,
    id: (&Pos, &str),
) {
    // This is used for instance "$x->|" and static "Class1::|" members.
    if !is_auto_complete(st, id.1) {
        return;
    }
    // Detect usage of "parent::|" which can use both static and instance
    let parent_receiver = matches!(cid, Some(aast::ClassId_::CIparent));

    let add = |st: &mut State, kind: SiKind, (name, ty): (String, DeclTy)| {
        // Functions that support dynamic will be wrapped by supportdyn<_>
        let ty = strip_supportdyn_decl(&ty);
        let res_detail = match ty.node_ref() {
            DeclTy_::Tfun(_) => rstrip(
                crate::string_utils::lstrip(&tast_env::print_decl_ty(None, env, &ty), "("),
                ")",
            )
            .to_string(),
            _ => tast_env::print_decl_ty(None, env, &ty),
        };
        let ty = PhaseTy::DeclTy(ty);
        let complete = make_item(
            get_pos_for(env, &ty),
            replace_pos(id),
            Some(cls::name(class_)),
            res_detail,
            name.clone(),
            insert_text_for_ty(env, autocomplete_context, &name, &ty),
            name,
            kind,
        );
        st.add_res(complete)
    };

    fn sort<A>(mut list: Vec<(String, A)>) -> Vec<(String, A)> {
        list.sort_by(|(a, _), (b, _)| a.as_bytes().cmp(b.as_bytes()));
        list
    }

    let check_where_constraints = |ft: &typing_defs::DeclFunType| -> bool {
        let mut env = env.clone();
        let (tparam_err_opt, _, explicit_targs) =
            crate::typing_phase::localize_targs_and_check_constraints(
                typing_defs::nonexact(),
                false,
                oxidized::pos_or_decl::PosOrDecl::NONE,
                Pos::NONE,
                Some(false),
                &mut env,
                &ast_defs::Id(Pos::NONE, "autocomplete".to_string()),
                crate::typing_reason::none(),
                &ft.tparams,
                vec![],
            );
        let (ft1_err_opt, ft1) = {
            // if where constraints involve pessimised function types
            // strip the ~ from their return type before localization
            let ft_stripped = {
                let mut ft = ft.clone();
                ft.where_constraints = ft
                    .where_constraints
                    .iter()
                    .map(|ty::decl::WhereConstraint(t1, c, t2)| {
                        ty::decl::WhereConstraint(t1.clone(), *c, strip_like_ret_type_decl(t2))
                    })
                    .collect();
                ft
            };
            let mut ety_env = ety_env.clone();
            ety_env.on_error = None;
            crate::typing_phase::localize_ft(
                Some(crate::typing_phase::MethodInstantiation {
                    use_name: "autocomplete".to_string(),
                    use_pos: Pos::NONE,
                    explicit_targs,
                }),
                &ety_env,
                oxidized::pos_or_decl::PosOrDecl::NONE,
                &mut env,
                &ft_stripped,
            )
        };
        let mut wc_err_opt = None;
        for typing_defs::WhereConstraint(ty, ck, cstr_ty) in &ft1.where_constraints {
            let err = crate::typing_generic_constraint::check_where_constraint(
                true,
                &mut env,
                Pos::NONE,
                oxidized::pos_or_decl::PosOrDecl::NONE,
                *ck,
                cstr_ty.clone(),
                ty.clone(),
            );
            if let Some(e) = err {
                wc_err_opt = Some(e)
            }
        }
        wc_err_opt.is_none() && tparam_err_opt.is_none() && ft1_err_opt.is_none()
    };

    // There's no reason for us to sort -- we can expect our client to do its
    // own sorting of our results -- but having a sorted list here makes our
    // tests more stable.
    if is_static || parent_receiver {
        for x in get_class_elt_types(true, env, class_, cid, sort(cls::smethods(class_))) {
            add(st, SiKind::SIClassMethod, x)
        }
        for x in get_class_elt_types(false, env, class_, cid, sort(cls::sprops(class_))) {
            add(st, SiKind::SIProperty, x)
        }
        for (name, cc) in sort(tast_env::consts(env, class_)) {
            add(st, SiKind::SIClassConstant, (name, cc.ty.clone()))
        }
    }
    if !is_static || parent_receiver {
        for (s, ty) in get_class_elt_types(true, env, class_, cid, sort(cls::methods(class_))) {
            let satisfies_where_constraints = match strip_supportdyn_decl(&ty).node_ref() {
                DeclTy_::Tfun(ft) => check_where_constraints(ft),
                _ => true,
            };
            if satisfies_where_constraints {
                add(st, SiKind::SIClassMethod, (s, ty))
            }
        }
        for x in get_class_elt_types(false, env, class_, cid, sort(cls::props(class_))) {
            add(st, SiKind::SIProperty, x)
        }
    }
    // Only complete __construct() when we see parent::, as we don't
    // allow __construct to be called as e.g. $foo->__construct().
    if parent_receiver {
        let (constructor, _) = tast_env::get_construct(env, class_);
        let constructor: Vec<(String, cls::ClassElt)> = constructor
            .map(|elt| (sn::members::__CONSTRUCT.to_string(), elt))
            .into_iter()
            .collect();
        for x in get_class_elt_types(true, env, class_, cid, constructor) {
            add(st, SiKind::SIClassMethod, x)
        }
    }
}

/// Autocompletion for XHP attribute names in an XHP literal.
fn autocomplete_xhp_attributes(
    st: &mut State,
    env: &Env,
    class_: &cls::T,
    cid: Option<&oxidized::nast::ClassId_>,
    id: (&Pos, &str),
    attrs: &[aast::XhpAttribute<tast::Ty, tast::SavedEnv>],
) {
    // This is used for "<nt:fb:text |" XHP attributes, in which case
    // class_ is ":nt:fb:text" and its attributes are in tc_props.
    if is_auto_complete(st, id.1) && cls::is_xhp(class_) {
        let existing_attr_names: BTreeSet<String> = attrs
            .iter()
            .filter_map(|attr| match attr {
                aast::XhpAttribute::XhpSimple(aast::XhpSimple { name, .. }) => Some(name.1.clone()),
                aast::XhpAttribute::XhpSpread(_) => None,
            })
            .filter(|name| !matches_auto_complete_suffix(name))
            .collect();
        for (name, ty) in get_class_elt_types(false, env, class_, cid, cls::props(class_)) {
            if !existing_attr_names.iter().any(|key| format!(":{}", key) == name) {
                let kind = SiKind::SIProperty;
                let res_detail = tast_env::print_decl_ty(None, env, &ty);
                let ty = PhaseTy::DeclTy(ty);
                let label = crate::string_utils::lstrip(&name, ":").to_string();
                let complete = make_item(
                    get_pos_for(env, &ty),
                    replace_pos(id),
                    Some(cls::name(class_)),
                    res_detail,
                    label.clone(),
                    InsertText::InsertLiterally(label),
                    name,
                    kind,
                );
                st.add_res(complete)
            }
        }
    }
}

fn autocomplete_xhp_bool_value(st: &mut State, attr_ty: &Ty, id_id: (&Pos, &str), env: &Env) {
    if is_auto_complete(st, id_id.1) {
        let is_bool_or_bool_option = |ty: &Ty| -> bool {
            let is_bool = |ty_: &Ty_| matches!(ty_, Ty_::Tprim(ast_defs::Tprim::Tbool));
            let ty = expand_and_strip_dynamic(env, ty.clone());
            match typing_defs::get_node(&ty) {
                Ty_::Toption(ty) => {
                    is_bool(typing_defs::get_node(&expand_and_strip_dynamic(env, ty.clone())))
                }
                ty_ => is_bool(ty_),
            }
        };

        if is_bool_or_bool_option(attr_ty) {
            let kind = SiKind::SILiteral;
            let ty = PhaseTy::LoclTy(attr_ty.clone());
            let complete = make_item(
                get_pos_for(env, &ty),
                replace_pos(id_id),
                None,
                search_utils::kind_to_string(kind).to_string(),
                "true".to_string(),
                InsertText::InsertLiterally("true".to_string()),
                "true".to_string(),
                kind,
            );
            let mut complete_false = complete.clone();
            complete_false.res_label = "false".to_string();
            complete_false.res_insert_text = InsertText::InsertLiterally("false".to_string());
            complete_false.res_fullname = "false".to_string();
            st.add_res(complete);
            st.add_res(complete_false)
        }
    }
}

/// Autocompletion for the value of an attribute in an XHP literals with the
/// enum type, defined with the following syntax:
/// attribute enum {"some value", "some other value"} my-attribute;
fn autocomplete_xhp_enum_attribute_value(
    st: &mut State,
    attr_name: &str,
    ty: &Ty,
    id_id: (&Pos, &str),
    env: &Env,
    cls_: &cls::T,
) {
    if is_auto_complete(st, id_id.1) {
        let attr_origin = cls::prop_origin(cls_, &format!(":{}", attr_name))
            .and_then(|cls_name| decl_entry::to_option(tast_env::get_class(env, &cls_name)));

        let enum_values = match &attr_origin {
            Some(c) => cls::xhp_enum_values(c),
            None => Default::default(),
        };

        let mut add_enum_value_result = |xev: &ast_defs::XhpEnumValue| {
            let name = match xev {
                ast_defs::XhpEnumValue::XEVInt(value) => value.to_string(),
                ast_defs::XhpEnumValue::XEVString(value) => format!("\"{}\"", value),
            };
            let kind = SiKind::SIEnum;
            let ty = PhaseTy::LoclTy(ty.clone());
            let complete = make_item(
                get_pos_for(env, &ty),
                replace_pos(id_id),
                None,
                search_utils::kind_to_string(kind).to_string(),
                name.clone(),
                InsertText::InsertLiterally(name.clone()),
                name,
                kind,
            );
            st.add_res(complete)
        };

        if let Some(enum_values) = enum_values.get(&format!(":{}", attr_name)) {
            for v in enum_values {
                add_enum_value_result(v)
            }
        }
    }
}

/// Autocompletion for the value of an attribute in an XHP literals with type
/// that is an enum class. i.e.
///
///   enum MyEnum {}
///   class :foo {
///     attribute MyEnum my-attribute;
///   }
fn autocomplete_xhp_enum_class_value(st: &mut State, attr_ty: &Ty, id_id: (&Pos, &str), env: &Env) {
    if is_auto_complete(st, id_id.1) {
        fn get_class_name_decl(ty: &DeclTy) -> Option<String> {
            let ty = strip_like_decl(ty);
            match ty.node_ref() {
                DeclTy_::Toption(ty) => get_class_name_decl(ty),
                DeclTy_::Tapply(x) => Some(x.0.id().as_str().to_string()),
                _ => None,
            }
        }
        fn get_class_name(env: &Env, ty: &Ty) -> Option<String> {
            let ty = expand_and_strip_dynamic(env, ty.clone());
            match typing_defs::get_node(&ty) {
                Ty_::Toption(ty) => get_class_name(env, ty),
                Ty_::Tnewtype(name, _, _) => Some(name.clone()),
                _ => None,
            }
        }

        let get_enum_constants = |class_decl: &cls::T| -> Vec<(String, typing_defs::ClassConst)> {
            let all_consts = tast_env::consts(env, class_decl);
            let class_name = cls::name(class_decl);
            all_consts
                .into_iter()
                .filter(|(_, class_const)| {
                    get_class_name_decl(&class_const.ty).as_deref() == Some(class_name.as_str())
                })
                .collect()
        };

        let attr_type_name = get_class_name(env, attr_ty);

        if let Some(class_name) = attr_type_name {
            let enum_class = decl_entry::to_option(tast_env::get_enum(env, &class_name));

            let enum_constants = match &enum_class {
                Some(c) => get_enum_constants(c),
                None => vec![],
            };

            for (const_name, ty) in enum_constants {
                let dty = PhaseTy::DeclTy(ty.ty.clone());
                let name = format!("{}::{}", utils::strip_ns(&class_name), const_name);
                let kind = SiKind::SIEnum;
                let res_base_class = enum_class.as_ref().map(cls::name);

                let complete = make_item(
                    get_pos_for(env, &dty),
                    replace_pos(id_id),
                    res_base_class,
                    search_utils::kind_to_string(kind).to_string(),
                    name.clone(),
                    InsertText::InsertLiterally(name.clone()),
                    name,
                    kind,
                );
                st.add_res(complete)
            }
        }
    }
}

/// Return all the paths of .hhi files.
fn hhi_paths() -> Vec<relative_path::T> {
    hhi::HHI_CONTENTS
        .iter()
        .map(|(fn_, _)| ::pos::RelativePath::new(::pos::Prefix::Hhi, fn_).into())
        .collect()
}

/// Return the fully qualified names of all functions in .hhi files, sorted
/// alphabetically (in reverse).
fn hhi_funs(naming_table: &naming_table::T) -> Vec<String> {
    let mut funs: Vec<String> = hhi_paths()
        .iter()
        .flat_map(|fn_| match naming_table::get_file_info(naming_table, fn_) {
            Some(info) => info.ids.funs.iter().map(|id| id.name.clone()).collect(),
            None => vec![],
        })
        .collect();
    funs.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    funs.reverse();
    funs
}

/// `Utils.strip_hh_lib_ns`
fn strip_hh_lib_ns(s: &str) -> &str {
    let s = s.strip_prefix("\\HH\\Lib\\").unwrap_or(s);
    let s = s.strip_prefix("\\HH\\").unwrap_or(s);
    utils::strip_ns(s)
}

/// Filter function names to those in namespaces can be used with value types.
fn filter_fake_arrow_namespaces(fun_names: Vec<String>) -> Vec<String> {
    let in_relevant_ns = |name: &str| -> bool {
        let name = strip_hh_lib_ns(name);
        name.starts_with("C\\")
            || name.starts_with("Vec\\")
            || name.starts_with("Dict\\")
            || name.starts_with("Keyset\\")
            || name.starts_with("Str\\")
    };
    fun_names.into_iter().filter(|n| in_relevant_ns(n)).collect()
}

/// Create a fresh type variable for every item in [tparams].
fn fresh_tyvars<A>(env: &mut Env, tparams: &[A]) -> Vec<Ty> {
    let mut tvars = vec![];
    for _ in tparams {
        let tvar = tast_env::fresh_type(env, Pos::NONE);
        tvars.insert(0, tvar);
    }
    tvars
}

fn fresh_expand_env(env: &mut Env, tparams: &[typing_defs::DeclTparam]) -> typing_defs::ExpandEnv {
    let tyvars = fresh_tyvars(env, tparams);
    let substs = crate::decl_subst::make_locl(tparams, &tyvars);
    let mut ety_env = typing_defs::empty_expand_env();
    ety_env.substs = substs;
    ety_env
}

/// Does [f] accept [arg_ty] as its first positional argument?
fn fun_accepts_first_arg(env: &Env, f: &typing_defs::FunElt, arg_ty: &Ty) -> bool {
    // Functions that support dynamic will be wrapped by supportdyn<_>
    let ty = strip_supportdyn_decl(&f.ty);
    match ty.node_ref() {
        DeclTy_::Tfun(ft) => match ft.params.iter().find(|fp| !fp.flags.is_named()) {
            Some(first_param) => {
                let mut env = env.clone();
                let ety_env = fresh_expand_env(&mut env, &ft.tparams);
                let first_param = tast_env::localize(&mut env, &ety_env, &first_param.ty);
                match typing_defs::get_node(&first_param) {
                    // Kludge: If inference found a type variable that it couldn't solve,
                    // we've probably violated a where constraint and shouldn't consider
                    // this function to be compatible.
                    Ty_::Tvar(_) => false,
                    _ => {
                        let arg_ty = expand_and_strip_dynamic(&env, arg_ty.clone());
                        let first_param = expand_and_strip_dynamic(&env, first_param);
                        tast_env::can_subtype(&env, &arg_ty, &first_param)
                    }
                }
            }
            _ => false,
        },
        _ => false,
    }
}

/// Attempt to reconstruct the tparam substitution applied to class_ty
fn reconstruct_tparam_subst(env: &Env, class_ty: &Ty, class_: &cls::T) -> typing_defs::ExpandEnv {
    let actual_types = match typing_defs::get_node(&expand_and_strip_supportdyn(env, class_ty.clone()))
    {
        Ty_::Tclass(_, _, tl) => tl.clone(),
        _ => vec![],
    };
    let substs = crate::decl_subst::make_locl(cls::tparams_ref(class_), &actual_types);
    let mut ety_env = typing_defs::empty_expand_env();
    ety_env.substs = substs;
    ety_env
}

/// Fetch decls for all the [fun_names] and filter to those where the first
/// argument is compatible with [arg_ty].
fn compatible_fun_decls(
    env: &Env,
    arg_ty: &Ty,
    fun_names: Vec<String>,
) -> Vec<(String, crate::decl_provider::FunDecl)> {
    fun_names
        .into_iter()
        .filter_map(|fun_name| match tast_env::get_fun(env, &fun_name) {
            decl_entry::T::Found(f) if fun_accepts_first_arg(env, &f, arg_ty) => Some((fun_name, f)),
            _ => None,
        })
        .collect()
}

/// Is [ty] a value type where we want to allow -> to complete to a HSL
/// function?
fn is_fake_arrow_ty(env: &Env, ty: &Ty) -> bool {
    let ty = expand_and_strip_dynamic(env, ty.clone());
    match typing_defs::get_node(&ty) {
        Ty_::Tclass((_, name), _, _) => {
            name == sn::collections::VEC
                || name == sn::collections::DICT
                || name == sn::collections::KEYSET
                || name == C_STRING
        }
        _ => false,
    }
}

/// If the user is completing $v-> and $v is a vec/keyset/dict/string, offer
/// HSL functions like C\count().
fn autocomplete_hack_fake_arrow(
    st: &mut State,
    env: &Env,
    recv: &tast::Expr,
    prop_name: (&Pos, &str),
    naming_table: &naming_table::T,
) {
    let prop_replace_pos = replace_pos(prop_name);
    let prop_start = prop_replace_pos.st;
    let replace_pos = ide_api_types::Range {
        st: file_content::position::move_back(&prop_start, 2),
        ed: prop_replace_pos.ed,
    };

    let aast::Expr(recv_ty, recv_pos, _) = recv;
    if is_fake_arrow_ty(env, recv_ty) && is_auto_complete(st, prop_name.1) {
        let recv_start_pos = crate::pos::shrink_to_start(recv_pos);

        let mut fake_arrow_funs =
            vec!["\\HH\\Lib\\Str\\example_for_testing_named_params_fake_arrow".to_string()];
        // safe to include the above because there will be no decl for it in prod
        fake_arrow_funs.extend(filter_fake_arrow_namespaces(hhi_funs(naming_table)));
        let compatible_funs = compatible_fun_decls(env, recv_ty, fake_arrow_funs);

        for (fun_name, fun_decl) in compatible_funs {
            let name = strip_hh_lib_ns(&fun_name).to_string();
            let kind = SiKind::SIFunction;

            // We want to transform $some_vec-> to e.g.
            //
            //   C\contains(some_vec, ${1:\$value})
            //
            // This requires an additional insertion "C\contains(" before
            // the expression.
            let res_additional_edits = vec![(
                format!("{}(", name),
                ide_api_types::pos_to_range(&recv_start_pos),
            )];

            // Construct a snippet with placeholders for any additional
            // required arguments for this function. For the C\contains()
            // example, this is ", ${1:\$value})".
            let params = match fun_decl.ty.node_ref() {
                DeclTy_::Tfun(ft) => {
                    // We drop the first positional parameter
                    // because the user has already written the receiver
                    let drop_first_positional_param = |params: Vec<typing_defs::DeclFunParam>| {
                        let mut has_dropped_first_positional_param = false;
                        let mut out = vec![];
                        for fp in params {
                            let is_named = name_of_named_param(&fp).is_some();
                            if has_dropped_first_positional_param || is_named {
                                out.push(fp)
                            } else {
                                has_dropped_first_positional_param = true
                            }
                        }
                        out
                    };
                    let required_params = required_params_of_fun_type(&**ft);
                    drop_first_positional_param(required_params)
                }
                _ => vec![],
            };
            let res_insert_text = if params.is_empty() {
                InsertText::InsertLiterally(")".to_string())
            } else {
                let snippet = format!(", {})", snippet_for_params(&params));
                InsertText::InsertAsSnippet(SnippetWithFallback {
                    snippet,
                    fallback: ")".to_string(),
                })
            };

            let complete = AutocompleteItem {
                res_decl_pos: crate::pos::to_absolute(&server_pos_resolve(
                    env,
                    &fun_decl.pos.clone().to_oxidized(),
                )),
                res_replace_pos: replace_pos.clone(),
                res_base_class: None,
                res_detail: tast_env::print_decl_ty(None, env, &fun_decl.ty),
                res_insert_text,
                res_sort_text: None,
                // VS Code uses filter text to decide which items match the current
                // prefix. However, "C\contains" does not start with "->", so VS
                // Code would normally ignore this completion item.
                //
                // We set the filter text to "->contains" so we offer C\contains if
                // the user types e.g. "->" or "->co".
                res_filter_text: Some(format!("->{}", utils::strip_all_ns(&fun_name))),
                res_label: name.clone(),
                res_fullname: name,
                res_kind: kind,
                res_documentation: None,
                res_additional_edits,
            };
            st.add_res(complete)
        }
    }
}

fn autocomplete_typed_member(
    st: &mut State,
    is_static: bool,
    autocomplete_context: &LegacyAutocompleteContext,
    env: &Env,
    class_ty: &Ty,
    cid: Option<&tast::ClassId>,
    mid: (&Pos, &str),
) {
    for cname in tast_env::get_class_ids(env, class_ty.clone()) {
        if let Some(class_) = decl_entry::to_option(tast_env::get_class(env, &cname)) {
            let ety_env = reconstruct_tparam_subst(env, class_ty, &class_);
            let cid = cid.map(|cid| tast::to_nast_class_id_(cid.2.clone()));
            autocomplete_member(
                st,
                is_static,
                autocomplete_context,
                env,
                &ety_env,
                &class_,
                cid.as_ref(),
                mid,
            )
        }
    }
}

fn autocomplete_static_member(
    st: &mut State,
    autocomplete_context: &LegacyAutocompleteContext,
    env: &Env,
    cid: &tast::ClassId,
    mid: (&Pos, &str),
) {
    autocomplete_typed_member(st, true, autocomplete_context, env, &cid.0, Some(cid), mid)
}

fn compatible_enum_class_consts(
    env: &Env,
    cls_: &cls::T,
    pos: &Pos,
    expected_ty: Option<&Ty>,
) -> Vec<(String, typing_defs::ClassConst)> {
    // Ignore ::class, as it's not a normal enum constant.
    let consts: Vec<(String, typing_defs::ClassConst)> = tast_env::consts(env, cls_)
        .into_iter()
        .filter(|(name, _)| name != sn::members::M_CLASS)
        .collect();

    // All the constants that are compatible with [expected_ty].
    let compatible_consts: Vec<(String, typing_defs::ClassConst)> = consts
        .iter()
        .filter(|(_, cc)| {
            let mut env = env.clone();
            let cc_ty = tast_env::localize_no_subst(&mut env, true, &cc.ty);
            match expected_ty {
                Some(expected_ty) => {
                    let cc_other =
                        crate::typing_make_type::locl_like(crate::typing_reason::none(), expected_ty.clone());
                    // The exact callback does not matter provided that `sub_type`
                    // does not discard errors
                    let callback = crate::typing_error::reasons_callback::unify_error_at(pos.clone());
                    let errs = crate::typing_subtype::sub_type(
                        &mut env,
                        None,
                        None,
                        None,
                        None,
                        cc_ty,
                        cc_other,
                        Some(callback),
                    );
                    errs.is_none()
                }
                None => true,
            }
        })
        .cloned()
        .collect();

    if compatible_consts.is_empty() {
        // If we couldn't find any constants that match the expected
        // type, show all constants. We sometimes infer [nothing] for
        // generics when a user hasn't passed all the arguments to a
        // function yet.
        consts
    } else {
        compatible_consts
    }
}

/// If [ty] is a MemberOf, unwrap the inner type, otherwise return the
/// argument unchanged.
///
///   MemberOf<SomeEnum, X> -> X
///   Y -> Y
fn unwrap_enum_memberof(ty: &DeclTy) -> DeclTy {
    let ty = strip_like_decl(ty);
    match ty.node_ref() {
        DeclTy_::Tapply(x) if x.1.len() == 2 && x.0.id().as_str() == sn::classes::MEMBER_OF => {
            x.1[1].clone()
        }
        _ => ty,
    }
}

fn autocomplete_enum_class_label(
    st: &mut State,
    env: &Env,
    opt_cname: Option<&str>,
    pos_labelname: (&Pos, &str),
    expected_ty: Option<&Ty>,
) {
    let mut suggest_members = |cls_: &cls::T| {
        for (name, cc) in compatible_enum_class_consts(env, cls_, pos_labelname.0, expected_ty) {
            let res_detail = tast_env::print_decl_ty(None, env, &unwrap_enum_memberof(&cc.ty));
            let ty = PhaseTy::DeclTy(cc.ty.clone());
            let kind = SiKind::SIClassConstant;
            let complete = make_item(
                get_pos_for(env, &ty),
                replace_pos(pos_labelname),
                Some(cls::name(cls_)),
                res_detail,
                name.clone(),
                InsertText::InsertLiterally(name.clone()),
                name,
                kind,
            );
            st.add_res(complete)
        }
    };
    if let Some(id) = opt_cname {
        if let Some(c) = decl_entry::to_option(tast_env::get_class(env, id)) {
            suggest_members(&c)
        }
    }
}

/// Zip two lists together. If the two lists have different lengths, take
/// the shortest.
fn zip_truncate<'x, 'y, A, B>(xs: &'x [A], ys: &'y [B]) -> Vec<(&'x A, &'y B)> {
    xs.iter().zip(ys.iter()).collect()
}

/// Auto complete for short labels `#Foo` inside a function call.
/// Leverage function type information to infer the right enum class.
fn autocomplete_enum_class_label_call(
    st: &mut State,
    env: &Env,
    f: &tast::Expr,
    args: &[tast::Argument],
) {
    let suggest_members_from_ty =
        |st: &mut State, env: &Env, ty: &Ty, pos_labelname: (&Pos, &str), expected_ty: &Ty| {
            let ty = expand_and_strip_dynamic(env, ty.clone());
            match typing_defs::get_node(&ty) {
                Ty_::Tclass((_, enum_name), _, _)
                    if tast_env::is_enum_class(env, enum_name) =>
                {
                    autocomplete_enum_class_label(
                        st,
                        env,
                        Some(enum_name),
                        pos_labelname,
                        Some(expected_ty),
                    )
                }
                _ => {}
            }
        };
    let is_enum_class_label_ty_name = |name: &str| sn::classes::ENUM_CLASS_LABEL == name;
    let aast::Expr(fty, _, _) = f;
    if let Some(ft) = expand_fun(env, fty.clone()) {
        let ty_args = zip_truncate(args, &ft.params);
        for (arg, arg_ty) in ty_args {
            // If the argument was wrapped in a hole, remove it
            let arg = match crate::aast_utils::arg_to_expr(arg) {
                aast::Expr(_, _, aast::Expr_::Hole(h)) => &h.0,
                e => e,
            };
            let arg_ty_node = expand_and_strip_dynamic(env, arg_ty.type_.clone());
            match (arg, typing_defs::get_node(&arg_ty_node)) {
                (aast::Expr(_, p, aast::Expr_::EnumClassLabel(ecl)), Ty_::Tnewtype(ty_name, targs, _))
                    if ecl.0.is_none()
                        && targs.len() == 2
                        && is_enum_class_label_ty_name(ty_name)
                        && is_auto_complete(st, &ecl.1) =>
                {
                    suggest_members_from_ty(st, env, &targs[0], (p, &ecl.1), &targs[1])
                }
                (_, _) => {}
            }
        }
    }
}

/// Best-effort to find a class associated with this type constant.
fn typeconst_class_name(typeconst: &typing_defs::TypeconstType) -> Option<String> {
    let decl_ty = match &typeconst.kind {
        ty::decl::Typeconst::TCAbstract(atc) => atc.as_constraint.clone(),
        ty::decl::Typeconst::TCConcrete(tc) => Some(tc.ty.clone()),
    };
    match decl_ty {
        Some(decl_ty) => {
            let decl_ty = strip_like_decl(&decl_ty);
            match decl_ty.node_ref() {
                DeclTy_::Tapply(x) => Some(x.0.id().as_str().to_string()),
                _ => None,
            }
        }
        None => None,
    }
}

/// Given a typeconstant `Foo::TBar::TBaz`, if TBaz is a classish, return its
/// decl.
fn typeconst_decl(env: &Env, ids: &[aast::Sid], cls_name: &str) -> Option<cls::T> {
    match tast_env::get_class(env, cls_name) {
        decl_entry::T::Found(cls_decl) => match ids {
            [] => Some(cls_decl),
            [ast_defs::Id(_, id), ids @ ..] => tast_env::get_typeconst(env, &cls_decl, id)
                .and_then(|tc| typeconst_class_name(&tc))
                .and_then(|name| typeconst_decl(env, ids, &name)),
        },
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
    }
}

/// Autocomplete type constants, which look like `MyClass::AUTO332`.
fn autocomplete_class_type_const(st: &mut State, env: &Env, h: &aast::Hint, ids: &[aast::Sid]) {
    match ids.last() {
        Some(ast_defs::Id(sid_pos, id)) if is_auto_complete(st, id) => {
            let prefix = strip_suffix(id);
            let class_name = match &*h.1 {
                aast::Hint_::Happly(ast_defs::Id(_, name), _) => Some(name.clone()),
                aast::Hint_::Hthis => tast_env::get_self_id(env),
                _ => None,
            };
            let class_decl = match class_name {
                Some(class_name) => typeconst_decl(env, &ids[..ids.len() - 1], &class_name),
                None => None,
            };
            if let Some(class_decl) = class_decl {
                let consts = tast_env::consts(env, &class_decl);
                for (name, cc) in consts {
                    if name.starts_with(&prefix) {
                        let complete = make_item(
                            absolute_none(),
                            replace_pos((sid_pos, id)),
                            Some(cc.origin.as_str().to_string()),
                            "const type".to_string(),
                            name.clone(),
                            InsertText::InsertLiterally(name.clone()),
                            name,
                            SiKind::SIClassConstant,
                        );
                        st.add_res(complete)
                    }
                }
            }
        }
        _ => {}
    }
}

/// Get the names of string literal keys in this shape type.
fn shape_string_keys<A>(sm: &typing_defs::t_shape_map::TShapeMap<A>) -> Vec<String> {
    // `TShapeMap.keys` (a fold that conses): in decreasing order.
    sm.keys()
        .rev()
        .filter_map(|field| match &field.0 {
            typing_defs::TshapeFieldName::TSFlitStr(oxidized::typing_defs_core::PosByteString(
                _,
                s,
            )) => Some(String::from_utf8_lossy(s.as_slice()).into_owned()),
            _ => None,
        })
        .collect()
}

fn unwrap_holes(e: &tast::Expr) -> &tast::Expr {
    match &e.2 {
        aast::Expr_::Hole(h) => &h.0,
        aast::Expr_::Invalid(inv) => match &**inv {
            Some(e) => e,
            None => e,
        },
        _ => e,
    }
}

fn autocomplete_named_argument_in_call(
    st: &mut State,
    env: &Env,
    ft: &typing_defs::FunType,
    args: &[tast::Argument],
) {
    let used_names: BTreeSet<String> = args
        .iter()
        .filter_map(typing_defs::named_params::name_of_arg)
        .collect();
    let add_named_argument_results = |st: &mut State, pos: &Pos, id: &str| {
        let prefix = strip_suffix(id);
        let prefix = utils::strip_ns(&prefix);
        let matching_params: Vec<(String, &typing_defs::FunParam)> =
            ft_params_without_named_variadic(ft)
                .iter()
                .filter_map(|fp| name_of_named_param(fp).map(|name| (name, fp)))
                .filter(|(name, _)| name.starts_with(prefix) && !used_names.contains(name))
                .collect();
        for (declaration_index, (name, fp)) in matching_params.into_iter().enumerate() {
            let is_optional = typing_defs::get_fp_is_optional(fp);
            let sort_text = format!("{}{:08}", if is_optional { 1 } else { 0 }, declaration_index);
            let complete = AutocompleteItem {
                res_decl_pos: get_pos_for(env, &PhaseTy::LoclTy(fp.type_.clone())),
                res_replace_pos: replace_pos((pos, id)),
                res_base_class: None,
                res_detail: format!(
                    "{} ({} named parameter)",
                    tast_env::print_ty(env, &fp.type_),
                    if is_optional { "optional" } else { "required" }
                ),
                res_label: name.clone(),
                res_insert_text: InsertText::InsertAsSnippet(SnippetWithFallback {
                    snippet: snippet_for_params(std::slice::from_ref(fp)),
                    fallback: format!("{}=", name),
                }),
                res_fullname: name,
                res_kind: SiKind::SILocalVariable,
                res_documentation: None,
                res_sort_text: Some(sort_text),
                res_filter_text: None,
                res_additional_edits: vec![],
            };
            st.add_res(complete)
        }
    };
    for arg in args {
        match arg {
            aast::Argument::Anormal(arg) => match unwrap_holes(arg) {
                aast::Expr(_, _, aast::Expr_::Id(id)) if is_auto_complete(st, &id.1) => {
                    add_named_argument_results(st, &id.0, &id.1)
                }
                _ => {}
            },
            aast::Argument::Ainout(_, _) | aast::Argument::Anamed(_, _) => {}
        }
    }
}

/// If we see a call to a function that takes a shape argument, offer
/// completions for field names in shape literals.
///
///   takes_shape(shape('x' => 123, '|'));
fn autocomplete_shape_literal_in_call(
    st: &mut State,
    env: &Env,
    ft: &typing_defs::FunType,
    args: &[tast::Argument],
) {
    let add_shape_key_result = |st: &mut State, pos: &Pos, key: &str| {
        let reason = crate::typing_reason::witness(pos.clone());
        let ty = crate::typing_make_type::string(reason);
        let kind = SiKind::SILiteral;
        let lty = PhaseTy::LoclTy(ty);
        let complete = make_item(
            get_pos_for(env, &lty),
            replace_pos((pos, key)),
            None,
            search_utils::kind_to_string(kind).to_string(),
            key.to_string(),
            InsertText::InsertLiterally(key.to_string()),
            key.to_string(),
            kind,
        );
        st.add_res(complete)
    };

    // If this shape field name is of the form "fooAUTO332", return "foo".
    let shape_field_autocomplete_prefix =
        |st: &State, sfn: &ast_defs::ShapeFieldName| -> Option<String> {
            match sfn {
                ast_defs::ShapeFieldName::SFlitStr(name) => {
                    let name = String::from_utf8_lossy(&name.1);
                    if is_auto_complete(st, &name) {
                        Some(strip_suffix(&name))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        };

    let args: Vec<&tast::Expr> = args
        .iter()
        .map(|arg| unwrap_holes(crate::aast_utils::arg_to_expr(arg)))
        .collect();

    for (arg, expected_ty) in args.iter().zip(ft.params.iter()) {
        if let aast::Expr(_, pos, aast::Expr_::Shape(kvs)) = arg {
            // We're passing a shape literal as this function argument.
            for field in kvs {
                let name = match field {
                    aast::ShapeExprField::SFField(name, _val) => name,
                    aast::ShapeExprField::SFSplat(_) => continue,
                };
                if let Some(prefix) = shape_field_autocomplete_prefix(st, name) {
                    // This shape key is being autocompleted.
                    if let Ty_::Tshape(typing_defs::ShapeType::ShapeSimple(s)) =
                        typing_defs::get_node(&expected_ty.type_)
                    {
                        // This parameter is known to be a concrete shape type.
                        let keys = shape_string_keys(&s.fields);
                        let matching_keys: Vec<String> =
                            keys.into_iter().filter(|k| k.starts_with(&prefix)).collect();
                        for k in matching_keys {
                            add_shape_key_result(st, pos, &k)
                        }
                    }
                }
            }
        }
    }
}

fn add_builtin_attribute_result(
    st: &mut State,
    replace_pos: ide_api_types::Range,
    doc: &str,
    name: &str,
) {
    let mut complete = make_item(
        absolute_none(),
        replace_pos,
        None,
        "built-in attribute".to_string(),
        name.to_string(),
        InsertText::InsertLiterally(name.to_string()),
        name.to_string(),
        SiKind::SIClass,
    );
    complete.res_documentation = Some(doc.to_string());
    st.add_res(complete)
}

fn enclosing_class_decl(env: &Env) -> Option<cls::T> {
    match tast_env::get_self_id(env) {
        Some(id) => decl_entry::to_option(tast_env::get_class(env, &id)),
        None => None,
    }
}

/// Return the inherited class methods whose name starts with [prefix] and
/// haven't already been overridden.
fn methods_could_override(cls_: &cls::T, is_static: bool, prefix: &str) -> Vec<(String, cls::ClassElt)> {
    let c_name = cls::name(cls_);
    let methods = if is_static {
        cls::smethods(cls_)
    } else {
        cls::methods(cls_)
    };
    methods
        .into_iter()
        // We're only interested in methods that start with this prefix,
        // and aren't already defined in the current class.
        .filter(|(n, ce)| n.starts_with(prefix) && ce.ce_origin != c_name)
        .collect()
}

/// Autocomplete a partially written override method definition.
///
///   <<__Override>>
///   public static function xAUTO332
fn autocomplete_overriding_method(st: &mut State, env: &Env, m: &tast::Method_) {
    let name = &m.name.1;
    if is_auto_complete(st, name) {
        let prefix = strip_suffix(name);
        let has_override = m
            .user_attributes
            .iter()
            .any(|ua| ua.name.1 == sn::user_attributes::OVERRIDE);
        match enclosing_class_decl(env) {
            Some(cls_) if has_override => {
                for (name, ce) in methods_could_override(&cls_, m.static_, &prefix) {
                    let complete = make_item(
                        absolute_none(),
                        replace_pos((&m.name.0, &m.name.1)),
                        Some(ce.ce_origin.clone()),
                        "method name".to_string(),
                        name.clone(),
                        InsertText::InsertLiterally(name.clone()),
                        name,
                        SiKind::SIClassMethod,
                    );
                    st.add_res(complete)
                }
            }
            _ => {}
        }
    }
}

fn autocomplete_builtin_attribute(st: &mut State, (pos, name): (&Pos, &str), attr_kind: &str) {
    let stripped_name = utils::strip_ns(name);
    if is_auto_complete(st, name) && stripped_name.starts_with('_') {
        let replace_pos = replace_pos((pos, name));
        let prefix = strip_suffix(stripped_name);
        // Built-in attributes that match the prefix the user has typed.
        let possible_attrs = user_attributes_as_map::AS_MAP.iter().filter(|attr_info| {
            attr_info.name.starts_with(&prefix)
                && attr_info.autocomplete
                && attr_info.contexts.contains(&attr_kind)
        });
        // Sort by attribute name. This isn't necessary in the IDE, which
        // does its own sorting, but helps tests. (`AS_MAP` is sorted.)
        let sorted_attrs: Vec<_> = possible_attrs.rev().collect();
        for attr_info in sorted_attrs {
            add_builtin_attribute_result(st, replace_pos.clone(), attr_info.doc, attr_info.name)
        }
    }
}

/// If [name] is an enum, return the list of the constants it defines.
fn enum_consts(env: &Env, name: &str) -> Option<Vec<String>> {
    match tast_env::get_class(env, name) {
        decl_entry::T::Found(cls_) => match cls::kind(&cls_) {
            ast_defs::ClassishKind::Cenum => {
                let consts = tast_env::consts(env, &cls_)
                    .into_iter()
                    .map(|(name, _)| name)
                    .filter(|name| name != sn::members::M_CLASS)
                    .collect();
                Some(consts)
            }
            _ => None,
        },
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
    }
}

fn add_enum_const_result(
    st: &mut State,
    env: &Env,
    pos: &Pos,
    replace_pos: &ide_api_types::Range,
    prefix: &str,
    const_name: &str,
) {
    let reason = crate::typing_reason::witness(pos.clone());
    let ty = crate::typing_make_type::string(reason);
    let kind = SiKind::SIClassConstant;
    let lty = PhaseTy::LoclTy(ty);
    let key = format!("{}{}", prefix, const_name);
    let complete = make_item(
        get_pos_for(env, &lty),
        replace_pos.clone(),
        None,
        search_utils::kind_to_string(kind).to_string(),
        key.clone(),
        InsertText::InsertLiterally(key.clone()),
        key,
        kind,
    );
    st.add_res(complete)
}

fn case_names(expected_enum: &str, cases: &[tast::Case]) -> BTreeSet<String> {
    cases
        .iter()
        .filter_map(|case| match &case.0 .2 {
            aast::Expr_::ClassConst(cc) => {
                let (aast::ClassId(_, _, cid_), (_, variant_name)) = &**cc;
                match cid_ {
                    aast::ClassId_::CI(ast_defs::Id(_, enum_name)) if expected_enum == enum_name => {
                        Some(variant_name.clone())
                    }
                    _ => None,
                }
            }
            _ => None,
        })
        .collect()
}

/// Autocomplete enum values in case statements.
///
///   switch ($enum_value) {
///     case AUTO332
///   }
fn autocomplete_enum_case(st: &mut State, env: &Env, expr: &tast::Expr, cases: &[tast::Case]) {
    for tast::Case(e, _) in cases {
        match e {
            aast::Expr(_, _, aast::Expr_::Id(id)) if is_auto_complete(st, &id.1) => {
                let ast_defs::Id(pos, id) = &**id;
                let aast::Expr(recv_ty, _, _) = expr;
                let ty = expand_and_strip_dynamic(env, recv_ty.clone());
                let replace_pos = replace_pos((pos, id));
                if let Ty_::Tnewtype(name, _, _) = typing_defs::get_node(&ty) {
                    if let Some(consts) = enum_consts(env, name) {
                        let used_consts = case_names(name, cases);
                        let unused_consts: Vec<String> =
                            consts.into_iter().filter(|c| !used_consts.contains(c)).collect();

                        let prefix = format!("{}::", utils::strip_ns(name));
                        for c in unused_consts {
                            add_enum_const_result(st, env, pos, &replace_pos, &prefix, &c)
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Autocomplete enum values in function arguments that are known to be
/// enums.
///
///   takes_enum(AUTO332);
fn autocomplete_enum_value_in_call(
    st: &mut State,
    env: &Env,
    ft: &typing_defs::FunType,
    args: &[tast::Argument],
) {
    let args: Vec<&tast::Expr> = args
        .iter()
        .map(|arg| unwrap_holes(crate::aast_utils::arg_to_expr(arg)))
        .collect();

    for (arg, expected_ty) in args.iter().zip(ft.params.iter()) {
        match &arg.2 {
            aast::Expr_::Id(id) if matches_auto_complete_suffix(&id.1) => {
                let ast_defs::Id(pos, id) = &**id;
                let ty = expand_and_strip_dynamic(env, expected_ty.type_.clone());
                let replace_pos = replace_pos((pos, id));
                if let Ty_::Tnewtype(name, _, _) = typing_defs::get_node(&ty) {
                    if let Some(consts) = enum_consts(env, name) {
                        let prefix = format!("{}::", utils::strip_ns(name));
                        for c in consts {
                            add_enum_const_result(st, env, pos, &replace_pos, &prefix, &c)
                        }
                    }
                }
            }
            aast::Expr_::ClassConst(cc)
                if matches!(cc.0 .2, aast::ClassId_::CI(_)) && matches_auto_complete_suffix(&cc.1 .1) =>
            {
                let (pos, id) = (&cc.1 .0, &cc.1 .1);
                let ty = expand_and_strip_dynamic(env, expected_ty.type_.clone());
                let replace_pos = replace_pos((pos, id));
                if let Ty_::Tnewtype(name, _, _) = typing_defs::get_node(&ty) {
                    if let Some(consts) = enum_consts(env, name) {
                        for c in consts {
                            add_enum_const_result(st, env, pos, &replace_pos, "", &c)
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn builtin_type_hints() -> Vec<(BuiltInTypeHint, &'static str)> {
    use ast_defs::Tprim;
    vec![
        (BuiltInTypeHint::BImixed, "mixed"),
        (BuiltInTypeHint::BIdynamic, "dynamic"),
        (BuiltInTypeHint::BInothing, "nothing"),
        (BuiltInTypeHint::BInonnull, "nonnull"),
        (BuiltInTypeHint::BIshape, "shape"),
        (BuiltInTypeHint::BIstring, "string"),
        (BuiltInTypeHint::BIprimitive(Tprim::Tnull), "null"),
        // TODO: only offer void in return positions.
        (BuiltInTypeHint::BIprimitive(Tprim::Tvoid), "void"),
        (BuiltInTypeHint::BIprimitive(Tprim::Tint), "int"),
        (BuiltInTypeHint::BIprimitive(Tprim::Tbool), "bool"),
        (BuiltInTypeHint::BIprimitive(Tprim::Tfloat), "float"),
        (BuiltInTypeHint::BIprimitive(Tprim::Tresource), "resource"),
        (BuiltInTypeHint::BIprimitive(Tprim::Tnum), "num"),
        (BuiltInTypeHint::BIprimitive(Tprim::Tarraykey), "arraykey"),
        (BuiltInTypeHint::BIprimitive(Tprim::Tnoreturn), "noreturn"),
    ]
}

/// Find global autocomplete results
fn find_global_results(
    st: &mut State,
    env: &Env,
    id: (&Pos, &str),
    completion_type: AutocompleteType,
    autocomplete_context: &LegacyAutocompleteContext,
    sienv_ref: &mut SiEnv,
    pctx: &provider_context::T,
) {
    // First step: Check obvious cases where autocomplete is not warranted.
    //
    // is_after_single_colon : XHP vs switch statements
    // is_after_open_square_bracket : shape field names vs container keys
    // is_after_quote: shape field names vs arbitrary strings
    //
    // We can recognize these cases by whether the prefix is empty.
    // We do this by checking the identifier length, as the string will
    // include the current namespace.
    let have_user_prefix = crate::pos::length(id.0) > AUTOCOMPLETE_TOKEN_LENGTH;

    let tast_env = tast_env::empty(Arc::clone(pctx));
    let ctx = autocomplete_context;
    if !ctx.is_manually_invoked
        && !have_user_prefix
        && (ctx.is_after_single_colon || ctx.is_after_open_square_bracket || ctx.is_after_quote)
    {
    } else if ctx.is_after_double_right_angle_bracket {
        // <<__Override>>AUTO332
    } else if ctx.is_open_curly_without_equals {
        // In the case that we trigger autocompletion with an open curly brace,
        // we only want to perform autocompletion if it is preceded by an equal sign.
        //
        // i.e. if (true) {
        //   --> Do not autocomplete
        //
        // i.e. <foo:bar my-attribute={
        //   --> Allow autocompletion
    } else {
        let query_text = strip_suffix(id.1);
        let query_text = utils::strip_ns(&query_text).to_string();
        st.auto_complete_for_global = query_text.clone();
        let (ns, _) = utils::split_ns_from_name(&query_text);
        let absolute_none = absolute_none();
        let kind_filter = match completion_type {
            AutocompleteType::Acnew => Some(SiKind::SIClass),
            AutocompleteType::ActraitOnly => Some(SiKind::SITrait),
            AutocompleteType::Acclassish
            | AutocompleteType::Acid
            | AutocompleteType::Actype
            | AutocompleteType::AcWorkspaceSymbol => None,
        };

        // Note that we are called by a visitor on the TAST, and the TAST has
        // already done namespace-aliasing elaboration. For instance given
        // source code "Vec\chAUTO332" and .hhconfig
        // auto_namespace_map={"Vec":"FlibSL\\Vec"}, then the TAST will have a
        // node with id "FLibSL\Vec\chAUTO332". This then will be the
        // [query_text] that we send to [find_matching_symbols].
        let (results, is_complete) = symbol_index::find_matching_symbols(
            sienv_ref,
            &query_text,
            MAX_RESULTS,
            completion_type,
            kind_filter,
        );
        st.is_complete = is_complete == SiComplete::Complete;
        // Looking up a function signature using Tast_env.get_fun consumes ~67KB
        // and can cause complex typechecking which can take from 2-100 milliseconds
        // per result.  When tested in summer 2019 it was possible to load 1.4GB of data
        // if get_fun was called on every function in the WWW codebase.
        //
        // Therefore, this feature is only available via the option sie_resolve_signatures
        // - and please be careful not to turn it on unless you really want to consume
        // memory and performance.
        for r in results {
            let (res_label, res_fullname) = (r.name.clone(), r.fullname.clone());
            // Only load func details if the flag sie_resolve_signatures is true
            let (res_detail, res_insert_text) =
                if sienv_ref.sie_resolve_signatures && r.kind == SiKind::SIFunction {
                    let fixed_name = format!("{}{}", ns, r.name);
                    match tast_env::get_fun(&tast_env, &fixed_name) {
                        decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => (
                            search_utils::kind_to_string(r.kind).to_string(),
                            InsertText::InsertLiterally(res_label.clone()),
                        ),
                        decl_entry::T::Found(fe) => {
                            let ty = &fe.ty;
                            let res_detail = tast_env::print_decl_ty(None, &tast_env, ty);
                            (
                                res_detail,
                                insert_text_for_ty(
                                    env,
                                    autocomplete_context,
                                    &res_label,
                                    &PhaseTy::DeclTy(ty.clone()),
                                ),
                            )
                        }
                    }
                } else {
                    (
                        search_utils::kind_to_string(r.kind).to_string(),
                        InsertText::InsertLiterally(res_label.clone()),
                    )
                };
            // Only load exact positions if specially requested
            let res_decl_pos = if sienv_ref.sie_resolve_positions {
                let fixed_name = format!("{}{}", ns, r.name);
                match tast_env::get_fun(&tast_env, &fixed_name) {
                    decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => {
                        absolute_none.clone()
                    }
                    decl_entry::T::Found(fe) => crate::pos::to_absolute(&server_pos_resolve(
                        &tast_env,
                        &decl_get_pos(&fe.ty),
                    )),
                }
            } else {
                absolute_none.clone()
            };
            // Figure out how to display them
            let complete = make_item(
                res_decl_pos,
                replace_pos(id),
                None,
                res_detail,
                res_label,
                res_insert_text,
                res_fullname,
                r.kind,
            );
            st.add_res(complete)
        }

        // Add any builtins that match
        match completion_type {
            AutocompleteType::Acid
            | AutocompleteType::ActraitOnly
            | AutocompleteType::Acclassish
            | AutocompleteType::AcWorkspaceSymbol
            | AutocompleteType::Acnew => {}
            AutocompleteType::Actype => {
                for (hint, name) in builtin_type_hints() {
                    if name.starts_with(&query_text) {
                        let kind = SiKind::SITypedef;
                        let documentation = symbol_occurrence::built_in_type_hover(&hint);
                        let mut complete = make_item(
                            absolute_none.clone(),
                            replace_pos(id),
                            None,
                            "builtin".to_string(),
                            name.to_string(),
                            InsertText::InsertLiterally(name.to_string()),
                            name.to_string(),
                            kind,
                        );
                        complete.res_documentation = Some(documentation);
                        st.add_res(complete)
                    }
                }
            }
        }
    }
}

fn complete_xhp_tag(
    st: &mut State,
    id: &ast_defs::Id,
    does_autocomplete_snippet: bool,
    sienv_ref: &mut SiEnv,
    pctx: &provider_context::T,
) {
    let tast_env = tast_env::empty(Arc::clone(pctx));
    let query_text = strip_suffix(&id.1);
    let query_text = utils::strip_ns(&query_text).to_string();
    st.auto_complete_for_global = query_text.clone();
    let absolute_none = absolute_none();
    let (results, _is_complete) = symbol_index::find_matching_symbols(
        sienv_ref,
        &query_text,
        MAX_RESULTS,
        AutocompleteType::Acid,
        None,
    );
    for r in results {
        let (res_label, res_fullname) =
            (utils::strip_xhp_ns(&r.name).to_string(), utils::add_xhp_ns(&r.fullname));
        let (res_detail, res_insert_text) = (
            search_utils::kind_to_string(r.kind).to_string(),
            InsertText::InsertLiterally(res_label.clone()),
        );
        let res_insert_text = match r.kind {
            SiKind::SIXHP | SiKind::SIClass if does_autocomplete_snippet => {
                let classname = utils::add_ns(&res_fullname);
                let cid = oxidized::nast::ClassId_::CI(id.clone());
                let attrs = get_class_req_attrs(&tast_env, &classname, Some(&cid));
                let has_children = !get_class_is_child_empty(&tast_env, &classname);
                insert_text_for_xhp_req_attrs(&res_label, &attrs, has_children)
            }
            _ => res_insert_text,
        };
        // Figure out how to display them
        let complete = make_item(
            absolute_none.clone(),
            replace_pos_of_id(true, (&id.0, &id.1)),
            None,
            res_detail,
            res_label,
            res_insert_text,
            res_fullname,
            r.kind,
        );
        st.add_res(complete)
    }
    st.is_complete = (st.items.len() as isize) < MAX_RESULTS
}

// ---------------------------------------------------------------------------
// Locals

/// `auto_complete_suffix_finder`: an `Aast.reduce` whose `on_Lvar` says
/// whether the name ends with the token (`zero` false, `plus` ||).
struct AutoCompleteSuffixFinder {
    found: bool,
}

/// The parameters of [`AutoCompleteSuffixFinder`] (an `Aast.reduce` over a
/// TAST, with no environment).
struct SuffixFinderParams;

impl oxidized::aast_visitor::Params for SuffixFinderParams {
    type Context = ();
    type Error = ();
    type Ex = tast::Ty;
    type En = tast::SavedEnv;
}

impl<'a> aast_visitor::Visitor<'a> for AutoCompleteSuffixFinder {
    type Params = SuffixFinderParams;

    fn object(&mut self) -> &mut dyn aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    fn visit_expr_(&mut self, c: &mut (), e: &'a tast::Expr_) -> Result<(), ()> {
        if let aast::Expr_::Lvar(lid) = e {
            if matches_auto_complete_suffix(local_id::get_name(&lid.1)) {
                self.found = true
            }
            return Ok(());
        }
        e.recurse(c, self)
    }
}

fn method_contains_cursor(m: &tast::Method_) -> bool {
    let mut v = AutoCompleteSuffixFinder { found: false };
    let _ = m.recurse(&mut (), &mut v);
    v.found
}

fn fun_contains_cursor(f: &tast::Fun_) -> bool {
    let mut v = AutoCompleteSuffixFinder { found: false };
    let _ = f.recurse(&mut (), &mut v);
    v.found
}

/// Find all the local variables before the cursor, so we can offer them as
/// completion candidates.
struct LocalVars {
    results: local_id::map::T<Ty>,
    id_at_cursor: Option<(Pos, String)>,
}

impl LocalVars {
    fn get_locals(
        mut self,
        ctx: &provider_context::T,
        tast: &[tast::Def],
    ) -> (local_id::map::T<Ty>, Option<(Pos, String)>) {
        tast_visitor::iter::go(&mut self, ctx, tast);
        (self.results, self.id_at_cursor)
    }

    fn add(&mut self, id: local_id::T, ty: Ty) {
        // If we already have a position for this identifier, don't overwrite it with
        // results from after the cursor position.
        if !(self.results.contains_key(&id) && self.id_at_cursor.is_some()) {
            self.results.insert(id, ty);
        }
    }
}

impl<'a> aast_visitor::Visitor<'a> for LocalVars {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::iter_methods!('a; expr_, class_var, expression_tree);

    fn visit_fun_(&mut self, env: &mut Env, f: &'a tast::Fun_) -> Res {
        if fun_contains_cursor(f) {
            tast_visitor::iter::on_fun_(self, env, f)
        } else {
            Ok(())
        }
    }

    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> Res {
        if method_contains_cursor(m) {
            if !m.static_ {
                self.add(typing_defs::this(), tast_env::get_self_ty_exn(env));
            }
            tast_visitor::iter::on_method_(self, env, m)
        } else {
            Ok(())
        }
    }

    fn visit_expr(&mut self, env: &mut Env, e: &'a tast::Expr) -> Res {
        let aast::Expr(ty, _, e_) = e;
        match e_ {
            aast::Expr_::Lvar(lid) => {
                let aast::Lid(pos, id) = &**lid;
                let name = local_id::get_name(id);
                if matches_auto_complete_suffix(name) {
                    self.id_at_cursor = Some((pos.clone(), name.to_string()))
                } else {
                    self.add(id.clone(), ty.clone())
                }
                Ok(())
            }
            aast::Expr_::Assign(a) => {
                let (e1, _, e2) = &**a;
                // Process the rvalue before the lvalue, since the lvalue is annotated
                // with its type after the assignment.
                self.visit_expr(env, e2)?;
                self.visit_expr(env, e1)
            }
            _ => e.recurse(env, self),
        }
    }

    fn visit_fun_param(&mut self, _env: &mut Env, fp: &'a tast::FunParam) -> Res {
        let id = local_id::make_unscoped(&fp.name);
        let ty = fp.annotation.clone();
        self.add(id, ty);
        Ok(())
    }
}

fn compute_complete_local(st: &mut State, env: &Env, ctx: &provider_context::T, tast: &[tast::Def]) {
    let (locals, id_at_cursor) = LocalVars {
        results: Default::default(),
        id_at_cursor: None,
    }
    .get_locals(ctx, tast);
    let id_at_cursor = id_at_cursor.unwrap_or((Pos::NONE, String::new()));
    let replace_pos = replace_pos((&id_at_cursor.0, &id_at_cursor.1));

    let id_prefix = if is_auto_complete(st, &id_at_cursor.1) {
        strip_suffix(&id_at_cursor.1)
    } else {
        String::new()
    };

    for (id, ty) in locals.iter() {
        let kind = SiKind::SILocalVariable;
        let name = local_id::get_name(id);
        if name.starts_with(&id_prefix) {
            let complete = make_item(
                get_pos_for(env, &PhaseTy::LoclTy(ty.clone())),
                replace_pos.clone(),
                None,
                tast_env::print_ty(env, ty),
                name.to_string(),
                InsertText::InsertLiterally(name.to_string()),
                name.to_string(),
                kind,
            );
            st.add_res(complete)
        }
    }
}

// ---------------------------------------------------------------------------
// The visitor

/// Walk the TAST and append autocomplete results for any syntax that
/// contains AUTO332 in its name.
struct Visitor<'s> {
    st: &'s mut State,
    ctx: provider_context::T,
    autocomplete_context: LegacyAutocompleteContext,
    sienv_ref: &'s mut SiEnv,
    naming_table: &'s naming_table::T,
    toplevel_tast: &'s [tast::Def],
}

impl Visitor<'_> {
    fn complete_global(&mut self, env: &Env, id: &ast_defs::Id, completion_type: AutocompleteType) {
        if is_auto_complete(self.st, &id.1) {
            find_global_results(
                self.st,
                env,
                (&id.0, &id.1),
                completion_type,
                &self.autocomplete_context,
                self.sienv_ref,
                &self.ctx,
            )
        }
    }

    fn complete_id(&mut self, env: &Env, id: &ast_defs::Id) {
        self.complete_global(env, id, AutocompleteType::Acid)
    }

    fn builtin_attributes(&mut self, uas: &[tast::UserAttribute], attr_kind: &str) {
        for ua in uas {
            autocomplete_builtin_attribute(self.st, (&ua.name.0, &ua.name.1), attr_kind)
        }
    }

    /// `method! on_expr`, before `super#on_expr`.
    fn on_expr(&mut self, env: &mut Env, expr: &tast::Expr) {
        match &expr.2 {
            aast::Expr_::ArrayGet(ag) if ag.1.is_some() => {
                let (arr, key) = &**ag;
                let aast::Expr(_, pos, key) = key.as_ref().unwrap();
                let ty = expand_and_strip_dynamic(env, arr.0.clone());
                if let Ty_::Tshape(typing_defs::ShapeType::ShapeSimple(s)) = typing_defs::get_node(&ty) {
                    let fields = &s.fields;
                    match key {
                        aast::Expr_::Id(mid) => autocomplete_shape_key(
                            self.st,
                            &self.autocomplete_context,
                            fields,
                            (pos, &mid.1),
                        ),
                        aast::Expr_::String(mid) => {
                            let mid = String::from_utf8_lossy(mid).into_owned();
                            // autocomplete generally assumes that there's a token ending with the suffix;
                            // This isn't the case for `$shape['a`, unless it's at the end of the file
                            match mid.find(AUTOCOMPLETE_TOKEN) {
                                None => autocomplete_shape_key(
                                    self.st,
                                    &self.autocomplete_context,
                                    fields,
                                    (pos, &mid),
                                ),
                                Some(offset) => {
                                    let offset = offset as isize;
                                    let mid = mid[..(offset + AUTOCOMPLETE_TOKEN_LENGTH) as usize]
                                        .to_string();
                                    let (line, bol, start_offset) = crate::pos::line_beg_offset(pos);
                                    let pos = crate::pos::make_from_lnum_bol_offset(
                                        crate::pos::filename(pos),
                                        (line, bol, start_offset),
                                        (
                                            line,
                                            bol,
                                            start_offset + offset + AUTOCOMPLETE_TOKEN_LENGTH,
                                        ),
                                    );
                                    autocomplete_shape_key(
                                        self.st,
                                        &self.autocomplete_context,
                                        fields,
                                        (&pos, &mid),
                                    )
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            aast::Expr_::Call(call) => {
                if let Some(ft) = expand_fun(env, call.func.0.clone()) {
                    autocomplete_named_argument_in_call(self.st, env, &ft, &call.args);
                    autocomplete_shape_literal_in_call(self.st, env, &ft, &call.args);
                    autocomplete_enum_value_in_call(self.st, env, &ft, &call.args)
                }
            }
            aast::Expr_::EnumClassLabel(ecl) if is_auto_complete(self.st, &ecl.1) => {
                let (opt_cname, n) = &**ecl;
                autocomplete_enum_class_label(
                    self.st,
                    env,
                    opt_cname.as_ref().map(|id| id.1.as_str()),
                    (&expr.1, n),
                    None,
                )
            }
            aast::Expr_::Efun(ef) => self.builtin_attributes(
                &ef.fun.user_attributes,
                sn::attribute_kinds::LAMBDA,
            ),
            aast::Expr_::Lfun(lf) => self.builtin_attributes(
                &lf.0.user_attributes,
                sn::attribute_kinds::LAMBDA,
            ),
            _ => {}
        }
    }

    /// `method! on_Xml`, before `super#on_Xml`.
    fn on_xml(&mut self, env: &mut Env, sid: &ast_defs::Id, attrs: &[aast::XhpAttribute<tast::Ty, tast::SavedEnv>]) {
        autocomplete_id(self.st, sid);
        if is_auto_complete(self.st, &sid.1) {
            complete_xhp_tag(self.st, sid, attrs.is_empty(), self.sienv_ref, &self.ctx);
        }

        let cid = oxidized::nast::ClassId_::CI(sid.clone());
        if let Some(c) = decl_entry::to_option(tast_env::get_class(env, &sid.1)) {
            for attr in attrs {
                match attr {
                    aast::XhpAttribute::XhpSimple(aast::XhpSimple {
                        name: id,
                        expr: value,
                        type_: ty,
                    }) => {
                        if let aast::Expr(_, _, aast::Expr_::Id(id_id)) = value {
                            // This handles the situation
                            //   <foo:bar my-attribute={AUTO332}
                            let id_id = (&id_id.0, id_id.1.as_str());
                            autocomplete_xhp_enum_attribute_value(self.st, &id.1, ty, id_id, env, &c);
                            autocomplete_xhp_enum_class_value(self.st, ty, id_id, env);
                            autocomplete_xhp_bool_value(self.st, ty, id_id, env)
                        }
                        if cls::is_xhp(&c) {
                            autocomplete_xhp_attributes(self.st, env, &c, Some(&cid), (&id.0, &id.1), attrs)
                        } else {
                            autocomplete_member(
                                self.st,
                                false,
                                &self.autocomplete_context,
                                env,
                                &typing_defs::empty_expand_env(),
                                &c,
                                Some(&cid),
                                (&id.0, &id.1),
                            )
                        }
                    }
                    aast::XhpAttribute::XhpSpread(_) => {}
                }
            }
        }
    }
}

impl<'a> aast_visitor::Visitor<'a> for Visitor<'_> {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::iter_methods!('a; fun_, expression_tree);

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Res {
        self.on_expr(env, expr);
        expr.recurse(env, self)
    }

    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Res {
        match expr_ {
            aast::Expr_::Id(id) => {
                autocomplete_id(self.st, id);
                self.complete_id(env, id);
            }
            aast::Expr_::Call(call) => {
                autocomplete_enum_class_label_call(self.st, env, &call.func, &call.args)
            }
            aast::Expr_::New(n) => {
                if let aast::ClassId(_, _, aast::ClassId_::CI(id)) = &n.0 {
                    self.complete_global(env, id, AutocompleteType::Acnew)
                }
            }
            aast::Expr_::Nameof(cid) => {
                if let aast::ClassId(_, _, aast::ClassId_::CI(id)) = &**cid {
                    self.complete_global(env, id, AutocompleteType::Acclassish)
                }
            }
            aast::Expr_::Lvar(lid) => {
                if is_auto_complete(self.st, local_id::get_name(&lid.1)) {
                    let ctx = Arc::clone(&self.ctx);
                    compute_complete_local(self.st, env, &ctx, self.toplevel_tast)
                }
            }
            aast::Expr_::ClassGet(cg) => {
                // `method! on_Class_get`: no `super`.
                let (cid, p, _prop_or_method) = &**cg;
                autocomplete_static_member(self.st, &self.autocomplete_context, env, cid, (&p.0, &p.1));
                return Ok(());
            }
            aast::Expr_::ClassConst(cc) => {
                let (cid, mid) = &**cc;
                autocomplete_static_member(self.st, &self.autocomplete_context, env, cid, (&mid.0, &mid.1))
            }
            aast::Expr_::ObjGet(og) => {
                let (obj, mid, _ognf, _) = &**og;
                let ty = expand_and_strip_dynamic(env, obj.0.clone());
                if let aast::Expr(_, _, aast::Expr_::Id(mid)) = mid {
                    autocomplete_hack_fake_arrow(self.st, env, obj, (&mid.0, &mid.1), self.naming_table);
                    autocomplete_typed_member(
                        self.st,
                        false,
                        &self.autocomplete_context,
                        env,
                        &ty,
                        None,
                        (&mid.0, &mid.1),
                    )
                }
            }
            aast::Expr_::Xml(x) => {
                let (sid, attrs, _el) = &**x;
                self.on_xml(env, sid, attrs)
            }
            _ => {}
        }
        tast_visitor::iter::on_expr_(self, env, expr_)
    }

    fn visit_hint_(&mut self, env: &mut Env, hint_: &'a aast::Hint_) -> Res {
        match hint_ {
            aast::Hint_::Happly(sid, _hl) => self.complete_global(env, sid, AutocompleteType::Actype),
            aast::Hint_::Haccess(h, ids) => autocomplete_class_type_const(self.st, env, h, ids),
            _ => {}
        }
        hint_.recurse(env, self)
    }

    fn visit_typedef(&mut self, env: &mut Env, t: &'a tast::Typedef) -> Res {
        self.builtin_attributes(&t.user_attributes, sn::attribute_kinds::TYPE_ALIAS);
        t.recurse(env, self)
    }

    fn visit_fun_def(&mut self, env: &mut Env, fd: &'a tast::FunDef) -> Res {
        self.builtin_attributes(&fd.fun.user_attributes, sn::attribute_kinds::FN);
        fd.recurse(env, self)
    }

    fn visit_fun_param(&mut self, env: &mut Env, fp: &'a tast::FunParam) -> Res {
        self.builtin_attributes(&fp.user_attributes, sn::attribute_kinds::PARAMETER);
        fp.recurse(env, self)
    }

    fn visit_tparam(&mut self, env: &mut Env, tp: &'a tast::Tparam) -> Res {
        self.builtin_attributes(&tp.user_attributes, sn::attribute_kinds::TYPE_PARAM);
        tp.recurse(env, self)
    }

    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> Res {
        autocomplete_overriding_method(self.st, env, m);
        self.builtin_attributes(&m.user_attributes, sn::attribute_kinds::MTHD);
        tast_visitor::iter::on_method_(self, env, m)
    }

    fn visit_class_var(&mut self, env: &mut Env, cv: &'a tast::ClassVar) -> Res {
        self.builtin_attributes(
            &cv.user_attributes,
            if cv.is_static {
                sn::attribute_kinds::STATIC_PROPERTY
            } else {
                sn::attribute_kinds::INST_PROPERTY
            },
        );
        tast_visitor::iter::on_class_var(self, env, cv)
    }

    fn visit_class_typeconst_def(&mut self, env: &mut Env, ctd: &'a tast::ClassTypeconstDef) -> Res {
        self.builtin_attributes(&ctd.user_attributes, sn::attribute_kinds::TYPE_CONST);
        ctd.recurse(env, self)
    }

    fn visit_class_(&mut self, env: &mut Env, cls_: &'a tast::Class_) -> Res {
        self.builtin_attributes(&cls_.user_attributes, sn::attribute_kinds::CLS);

        for hint in &cls_.uses {
            if let aast::Hint_::Happly(id, params) = &*hint.1 {
                self.complete_global(env, id, AutocompleteType::ActraitOnly);
                for h in params {
                    self.visit_hint(env, h)?;
                }
            }
        }

        // Ignore properties on interfaces. They're not legal syntax, but
        // they can occur when we parse partial method definitions.
        let mut cls_ = cls_.clone();
        if let ast_defs::ClassishKind::Cinterface = cls_.kind {
            cls_.vars = vec![];
        }

        // If we don't clear out c_uses we'll end up overwriting the trait
        // completion as soon as we get to on_Happly.
        cls_.uses = vec![];
        cls_.recurse(env, self)
    }

    fn visit_stmt_(&mut self, env: &mut Env, s: &'a tast::Stmt_) -> Res {
        if let aast::Stmt_::Switch(sw) = s {
            let (expr, cases, _default_case) = &**sw;
            autocomplete_enum_case(self.st, env, expr, cases)
        }
        s.recurse(env, self)
    }
}

// ---------------------------------------------------------------------------
// Keywords, from the CST

/// What the keyword functions need to make positions (`filename` and the
/// tokens' source text).
struct KwEnv<'t> {
    filename: Arc<relative_path::T>,
    source_text: &'t SourceText<'t>,
    indexed: parser_core_types::indexed_source_text::IndexedSourceText<'t>,
}

impl KwEnv<'_> {
    /// `Full_fidelity_source_text.relative_pos filename source_text start_offset end_offset`
    fn relative_pos(&self, start_offset: usize, end_offset: usize) -> Pos {
        let pos = self.indexed.relative_pos(start_offset, end_offset);
        Pos::from_lnum_bol_offset(Arc::clone(&self.filename), pos.start, pos.end)
    }

    fn text(&self, s: &PositionedSyntax) -> String {
        s.text(self.source_text).to_string()
    }
}

/// `Syntax.Token.leading t`: the OCaml tree's trivia are lazy, rescanned
/// from the source text (`Rust_lazy_trivia_ffi.scan_leading_php_trivia`, or
/// `_xhp_` in an XHP body), whose `ExtraTokenError` trivia have the right
/// offsets (the parser's own give skipped tokens the offset of the next
/// token).
fn leading_trivia(kw: &KwEnv<'_>, t: &PositionedToken) -> Vec<PositionedTrivium> {
    if t.kind == parser_core_types::token_kind::TokenKind::XHPBody {
        positioned_parser::scan_leading_xhp_trivia(kw.source_text, t.offset, t.leading_width)
    } else {
        positioned_parser::scan_leading_php_trivia(kw.source_text, t.offset, t.leading_width)
    }
}

fn complete_keywords_at(st: &mut State, possible_keywords: &[&str], text: &str, pos: &Pos) {
    if is_auto_complete(st, text) {
        let prefix = strip_suffix(text);
        for keyword in possible_keywords.iter().filter(|kw| kw.starts_with(&prefix)) {
            let kind = SiKind::SIKeyword;
            let complete = make_item(
                absolute_none(),
                replace_pos((pos, text)),
                None,
                search_utils::kind_to_string(kind).to_string(),
                keyword.to_string(),
                InsertText::InsertLiterally(keyword.to_string()),
                keyword.to_string(),
                kind,
            );
            st.add_res(complete)
        }
    }
}

fn complete_keywords_at_token(st: &mut State, kw: &KwEnv<'_>, possible_keywords: &[&str], s: &PositionedSyntax) {
    let token_str = kw.text(s);
    if let SyntaxVariant::Token(t) = &s.syntax {
        let t: &PositionedToken = t;
        let start_offset = t.offset + t.leading_width;
        let end_offset = start_offset + t.width;
        let pos = kw.relative_pos(start_offset, end_offset);
        complete_keywords_at(st, possible_keywords, &token_str, &pos)
    }
}

fn complete_keywords_at_trivia(st: &mut State, kw: &KwEnv<'_>, possible_keywords: &[&str], t: &PositionedTrivium) {
    let trivia_str = String::from_utf8_lossy(t.text_raw(kw.source_text)).into_owned();
    if t.kind == TriviaKind::ExtraTokenError && is_auto_complete(st, &trivia_str) {
        let start_offset = t.offset;
        let end_offset = start_offset + t.width;
        let pos = kw.relative_pos(start_offset, end_offset);
        complete_keywords_at(st, possible_keywords, &trivia_str, &pos)
    }
}

fn def_start_keywords(st: &mut State, kw: &KwEnv<'_>, s: &PositionedSyntax) {
    let possible_keywords = [
        "function",
        // `async` at the top level can occur for functions.
        "async",
        "class",
        "trait",
        "interface",
        "type",
        "newtype",
        "enum",
    ];
    complete_keywords_at_token(st, kw, &possible_keywords, s)
}

fn class_member_start_keywords(
    st: &mut State,
    kw: &KwEnv<'_>,
    s: &PositionedSyntax,
    ctx: Option<ast_defs::ClassishKind>,
) {
    let visibility_keywords = ["public", "protected"];
    let const_type_keywords = ["const", "abstract"];
    // Keywords allowed on class and trait methods, but not allowed on interface methods.
    let concrete_method_keywords = ["private", "final"];
    let trait_member_keywords = ["require extends", "require implements", "require class"];
    let inclusion_keywords = ["use"];

    let possible_keywords: Vec<&str> = match ctx {
        Some(ast_defs::ClassishKind::Cclass(_)) => [
            &visibility_keywords[..],
            &const_type_keywords,
            &concrete_method_keywords,
            &inclusion_keywords,
        ]
        .concat(),
        Some(ast_defs::ClassishKind::Cinterface) => {
            [&visibility_keywords[..], &const_type_keywords].concat()
        }
        Some(ast_defs::ClassishKind::Ctrait) => [
            &visibility_keywords[..],
            &const_type_keywords,
            &concrete_method_keywords,
            &trait_member_keywords,
            &inclusion_keywords,
        ]
        .concat(),
        _ => vec![],
    };

    complete_keywords_at_token(st, kw, &possible_keywords, s)
}

/// Drop the items from [possible_keywords] if they're already in
/// [existing_modifiers], and drop visibility keywords if we already have any
/// visibility keyword.
fn available_keywords<'k>(
    kw: &KwEnv<'_>,
    existing_modifiers: &PositionedSyntax,
    possible_keywords: &[&'k str],
) -> Vec<&'k str> {
    let current_modifiers: Vec<String> = existing_modifiers
        .syntax_node_to_list()
        .filter_map(|s| match &s.syntax {
            SyntaxVariant::Token(_) => Some(kw.text(s)),
            _ => None,
        })
        .collect();
    let visibility_modifiers = ["public", "protected", "private"];
    let has_visibility = current_modifiers
        .iter()
        .any(|kw| visibility_modifiers.contains(&kw.as_str()));
    possible_keywords
        .iter()
        .filter(|kw| {
            !current_modifiers.iter().any(|m| m == **kw)
                && !(visibility_modifiers.contains(kw) && has_visibility)
        })
        .copied()
        .collect()
}

fn class_keywords(st: &mut State, kw: &KwEnv<'_>, existing_modifiers: &PositionedSyntax, s: &PositionedSyntax) {
    let possible_keywords = available_keywords(kw, existing_modifiers, &["final", "abstract", "class"]);
    complete_keywords_at_token(st, kw, &possible_keywords, s)
}

fn method_keywords(st: &mut State, kw: &KwEnv<'_>, trivia: &PositionedTrivium) {
    complete_keywords_at_trivia(
        st,
        kw,
        &["public", "protected", "private", "static", "abstract", "final", "async"],
        trivia,
    )
}

fn classish_after_name_keywords(
    st: &mut State,
    kw: &KwEnv<'_>,
    ctx: Option<ast_defs::ClassishKind>,
    has_extends: bool,
    trivia: &PositionedTrivium,
) {
    let possible_keywords: &[&str] = match ctx {
        Some(ast_defs::ClassishKind::Cclass(_)) => {
            if has_extends {
                &["implements"]
            } else {
                &["implements", "extends"]
            }
        }
        Some(ast_defs::ClassishKind::Cinterface) => &["extends"],
        Some(ast_defs::ClassishKind::Ctrait) => &["implements"],
        _ => &[],
    };
    complete_keywords_at_trivia(st, kw, possible_keywords, trivia)
}

fn interface_method_keywords(
    st: &mut State,
    kw: &KwEnv<'_>,
    existing_modifiers: &PositionedSyntax,
    s: &PositionedSyntax,
) {
    let possible_keywords = available_keywords(
        kw,
        existing_modifiers,
        &["public", "protected", "private", "static", "function"],
    );
    complete_keywords_at_token(st, kw, &possible_keywords, s)
}

fn property_or_method_keywords(
    st: &mut State,
    kw: &KwEnv<'_>,
    existing_modifiers: &PositionedSyntax,
    s: &PositionedSyntax,
) {
    let possible_keywords = available_keywords(
        kw,
        existing_modifiers,
        &[
            "public",
            "protected",
            "private",
            "static",
            "abstract",
            "final",
            "async",
            "function",
        ],
    );
    complete_keywords_at_token(st, kw, &possible_keywords, s)
}

fn keywords(st: &mut State, kw: &KwEnv<'_>, tree: &PositionedSyntax) {
    fn on_toplevel_defs(st: &mut State, kw: &KwEnv<'_>, defs: &PositionedSyntax) {
        for d in defs.syntax_node_to_list() {
            // If we see AUTO332 at the top-level it's parsed as an
            // expression, but the user is about to write a top-level
            // definition (function, class etc).
            if let SyntaxVariant::ExpressionStatement(es) = &d.syntax {
                def_start_keywords(st, kw, &es.expression_statement_expression)
            }
        }
    }
    fn aux(st: &mut State, kw: &KwEnv<'_>, ctx: Option<ast_defs::ClassishKind>, s: &PositionedSyntax) {
        let mut inner_ctx = ctx;
        match &s.syntax {
            SyntaxVariant::Script(sd) => on_toplevel_defs(st, kw, &sd.script_declarations),
            SyntaxVariant::NamespaceBody(nb) => on_toplevel_defs(st, kw, &nb.namespace_declarations),
            SyntaxVariant::FunctionDeclaration(fd) => {
                if let SyntaxVariant::FunctionDeclarationHeader(fdh) =
                    &fd.function_declaration_header.syntax
                {
                    match &fdh.function_keyword.syntax {
                        SyntaxVariant::Missing => {
                            // The user has written `async AUTO332`, so we're expecting `function`.
                            complete_keywords_at_token(st, kw, &["function"], &fdh.function_name)
                        }
                        _ => {
                            if kw.text(&fdh.function_name).is_empty() {
                                // used for top-level statements and, I suspect, when there are parse errors
                                on_toplevel_defs(st, kw, &fd.function_body)
                            }
                        }
                    }
                }
            }
            SyntaxVariant::ClassishDeclaration(cd) => {
                match &cd.classish_keyword.syntax {
                    SyntaxVariant::Missing => {
                        // The user has written `final AUTO332` or `abstract AUTO332`,
                        // so we're expecting a class, not an interface or trait.
                        class_keywords(st, kw, &cd.classish_modifiers, &cd.classish_name)
                    }
                    SyntaxVariant::Token(_) => match kw.text(&cd.classish_keyword).as_str() {
                        "interface" => inner_ctx = Some(ast_defs::ClassishKind::Cinterface),
                        "class" => {
                            // We're only interested if the context is a class or not,
                            // so arbitrarily consider this a concrete class.
                            inner_ctx = Some(ast_defs::ClassishKind::Cclass(ast_defs::Abstraction::Concrete))
                        }
                        "trait" => inner_ctx = Some(ast_defs::ClassishKind::Ctrait),
                        "enum" => inner_ctx = Some(ast_defs::ClassishKind::Cenum),
                        _ => {}
                    },
                    _ => {}
                }
                if let SyntaxVariant::ClassishBody(cb) = &cd.classish_body.syntax {
                    let has_extends = matches!(cd.classish_extends_keyword.syntax, SyntaxVariant::Token(_));
                    if let SyntaxVariant::Token(t) = &cb.classish_body_left_brace.syntax {
                        // The user has written `class Foo AUTO332`, so we're
                        // expecting `extends` or `implements`.
                        for trivia in &leading_trivia(kw, t) {
                            classish_after_name_keywords(st, kw, inner_ctx, has_extends, trivia)
                        }
                    }
                }
            }
            SyntaxVariant::ClassishBody(cb) => {
                for d in cb.classish_body_elements.syntax_node_to_list() {
                    if let SyntaxVariant::ErrorSyntax(es) = &d.syntax {
                        let error_error = &es.error_error;
                        match (error_error.leading_width(), error_error.trailing_width()) {
                            (0, 0) => {
                                // If there's no leading or trailing whitespace, the
                                // user has their cursor between the curly braces.
                                //
                                //   class Foo {AUTO332}
                                //
                                // We don't want to offer completion here, because it
                                // interferes with pressing enter to insert a
                                // newline.
                            }
                            _ => class_member_start_keywords(st, kw, error_error, inner_ctx),
                        }
                    }
                }
            }
            SyntaxVariant::MethodishDeclaration(md) => {
                if let SyntaxVariant::FunctionDeclarationHeader(fdh) =
                    &md.methodish_function_decl_header.syntax
                {
                    if let SyntaxVariant::Token(t) = &fdh.function_keyword.syntax {
                        // The user has written `public AUTO332 function`, so we're expecting
                        // method modifiers like `static`.
                        for trivia in &leading_trivia(kw, t) {
                            method_keywords(st, kw, trivia)
                        }
                    }
                }
            }
            SyntaxVariant::PropertyDeclaration(pd) => match (&pd.property_type.syntax, ctx) {
                (SyntaxVariant::SimpleTypeSpecifier(sts), Some(ast_defs::ClassishKind::Cinterface)) => {
                    // Interfaces cannot contain properties, and have fewer
                    // modifiers available on methods.
                    interface_method_keywords(st, kw, &pd.property_modifiers, &sts.simple_type_specifier)
                }
                (SyntaxVariant::SimpleTypeSpecifier(sts), _) => {
                    // The user has written `public AUTO332`. This could be a method
                    // `public function foo(): void {}` or a property
                    // `public int $x = 1;`.
                    property_or_method_keywords(st, kw, &pd.property_modifiers, &sts.simple_type_specifier)
                }
                _ => {}
            },
            _ => {}
        }
        for child in s.iter_children() {
            aux(st, kw, inner_ctx, child)
        }
    }

    aux(st, kw, None, tree)
}

/// Main entry point for autocomplete
pub fn go_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    autocomplete_context: &LegacyAutocompleteContext,
    sienv_ref: &mut SiEnv,
    naming_table: &naming_table::T,
) -> with_complete_flag::T<Vec<AutocompleteItem>> {
    let mut st = State::reset();

    let (source_text, tree) = crate::ast_provider::compute_cst(entry);
    {
        let text = crate::full_fidelity_source_text::source_text(&source_text);
        let kw = KwEnv {
            filename: Arc::new(entry.path.clone()),
            source_text: &text,
            indexed: parser_core_types::indexed_source_text::IndexedSourceText::new(text.clone()),
        };
        keywords(&mut st, &kw, &tree);
    }

    let tast_provider::ComputeTast { tast, .. } =
        tast_provider::compute_tast_quarantined(ctx, entry);
    let tast = &tast.under_normal_assumptions;
    {
        let mut v = Visitor {
            st: &mut st,
            ctx: Arc::clone(ctx),
            autocomplete_context: autocomplete_context.clone(),
            sienv_ref,
            naming_table,
            toplevel_tast: tast,
        };
        tast_visitor::iter::go(&mut v, ctx, tast);
    }

    // `Diagnostics.ignore_`
    let start_time = crate::rt::ocaml_unix::gettimeofday();
    let autocomplete_items = st.items();
    let results = with_complete_flag::T {
        is_complete: st.is_complete,
        value: autocomplete_items,
    };
    symbol_index_core::log_symbol_index_search(
        sienv_ref,
        &st.auto_complete_for_global,
        MAX_RESULTS,
        results.value.len() as isize,
        None,
        start_time,
        "AutocompleteService.go",
    );
    results
}
