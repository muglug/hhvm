// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_rename.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F6** (plan §7.3).
//!
//! - `new_name_for_symbol_definition` reads the file with
//!   `File_provider.get_contents`, whose `Shared_memory` branch reads the
//!   file (the empty string when it does not exist): here through the
//!   files of `ctx` (`file_provider::rust_provider_backend::file::get_contents`,
//!   which does the same), so it takes `ctx`; `go_for_single_file` passes it.
//! - `get_dead_unsafe_cast_patches` and `get_lambda_parameter_rewrite_patches`
//!   call E3's `Remove_dead_unsafe_casts` and
//!   `Server_rewrite_lambda_parameters`, not ported yet (`todo!`).
//! - `get_fixme_patches` ports `Fixme_provider.UnusedFixmes` here (module
//!   `unused_fixmes`); it reads the fixme tables of the calling thread
//!   (`diagnostics_state::fixme_provider`, per thread), which the caller must
//!   have filled (the OCaml's are in shared memory).

use oxidized::pos::Pos;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::syntax_trait::SyntaxTrait;

use crate::ast_provider;
use crate::decl_entry;
use crate::decl_provider;
use crate::folded_class;
use crate::full_fidelity_source_text;
use crate::hack_event_logger;
use crate::pos;
use crate::provider_context;
use crate::relative_path;
use crate::search_types::find_refs as sfr;
use crate::server_command_types::done_or_retry;
use crate::server_command_types::find_refs::Action as FrAction;
use crate::server_command_types::find_refs::Member;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_find_refs;
use crate::server_rename_types::Action;
use crate::server_rename_types::DeprecatedWrapperFunctionRef;
use crate::server_rename_types::InsertPatch;
use crate::server_rename_types::Patch;
use crate::server_symbol_definition;
use crate::symbol_definition;
use crate::typing_defs_flags::class_elt as ce_flags;
use crate::utils;

type SourceText<'a> = parser_core_types::source_text::SourceText<'a>;

fn maybe_add_dollar(s: &str) -> String {
    if !s.starts_with('$') {
        format!("${}", s)
    } else {
        s.to_string()
    }
}

pub fn get_fixme_patches(codes: &[isize], env: &Env) -> Vec<Patch> {
    let fixmelist: Vec<(Pos, isize)> =
        crate::diagnostics_state::get_diagnostic_list(Some(false), env.diagnostics.clone())
            .into_iter()
            .filter(|e| e.is_fixmed)
            .map(|e| (crate::user_diagnostic::get_pos(&e), crate::user_diagnostic::get_code(&e)))
            .collect();
    // (The fixme tables are those of the thread that parsed a file, and the
    // files are checked on other threads: each file that has no table here
    // is parsed first. The OCaml tables are in shared memory.)
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    crate::naming_table::fold_with(Some(true), &env.naming_table, (), |fn_, _, ()| {
        use crate::diagnostics_state::fixme_provider;
        if !relative_path::is_hhi(fn_.prefix())
            && fixme_provider::get_fixmes_of_file(fn_).is_none()
            && fixme_provider::get_ignores_of_file(fn_).is_none()
        {
            let _ = crate::diagnostics_state::ignore_(|| crate::ast_provider::get_ast(true, &ctx, fn_));
        }
    });
    let poslist = unused_fixmes::get(codes, &fixmelist, &env.naming_table);
    poslist
        .iter()
        .map(|pos| Patch::Remove(pos::to_absolute(pos)))
        .collect()
}

/// `Fixme_provider.UnusedFixmes` (not ported in `diagnostics_state`, whose
/// `fixme_provider` has the tables): over the fixme tables of this thread.
mod unused_fixmes {
    use std::collections::BTreeMap;
    use std::collections::BTreeSet;

    use oxidized::pos::Pos;

    use crate::diagnostics_state::fixme_provider;
    use crate::naming_table;
    use crate::pos;
    use crate::relative_path;

    /// `FileToLineToCodesMap.t`: mapping error lines to sets of codes, per file
    type FileToLineToCodesMap = BTreeMap<relative_path::T, BTreeMap<isize, BTreeSet<isize>>>;

    fn make(pos_codes: &[(Pos, isize)]) -> FileToLineToCodesMap {
        let mut m = FileToLineToCodesMap::new();
        for (pos, code) in pos_codes {
            let fn_ = pos::filename(pos);
            let (line, _, _) = pos::info_pos(pos);
            m.entry(fn_).or_default().entry(line).or_default().insert(*code);
        }
        m
    }

    fn fixme_was_applied(
        applied_fixmes: &FileToLineToCodesMap,
        fn_: &relative_path::T,
        err_line: isize,
        err_code: isize,
    ) -> bool {
        applied_fixmes
            .get(fn_)
            .and_then(|m| m.get(&err_line))
            .is_some_and(|s| s.contains(&err_code))
    }

    fn code_is_concerned(codes: &[isize], code: isize) -> bool {
        codes.contains(&code)
            || codes.is_empty()
                && (code < 5000 || crate::error_codes::warning::of_enum(code).is_some())
    }

    fn get_unused_fixmes_in_file(
        get_fixmes: fn(&relative_path::T) -> Option<fixme_provider::fixme_map::T>,
        codes: &[isize],
        applied_fixmes: &FileToLineToCodesMap,
        fn_: &relative_path::T,
        mut acc: Vec<Pos>,
    ) -> Vec<Pos> {
        match get_fixmes(fn_) {
            None => acc,
            Some(fixme_map) => {
                // `FixmeMap.fold`: by line, then by code; `fixme_pos :: acc`.
                for (err_line, codes_map) in &fixme_map {
                    for (code, fixme_pos) in codes_map {
                        if code_is_concerned(codes, *code)
                            && !fixme_was_applied(applied_fixmes, fn_, *err_line, *code)
                        {
                            acc.insert(0, fixme_pos.clone());
                        }
                    }
                }
                acc
            }
        }
    }

    pub fn get(
        codes: &[isize],
        applied_fixmes: &[(Pos, isize)],
        files: &naming_table::T,
    ) -> Vec<Pos> {
        let applied_fixmes = make(applied_fixmes);
        naming_table::fold_with(Some(true), files, vec![], |fn_, _, acc| {
            let acc = get_unused_fixmes_in_file(
                fixme_provider::get_fixmes_of_file,
                codes,
                &applied_fixmes,
                fn_,
                acc,
            );
            get_unused_fixmes_in_file(
                fixme_provider::get_ignores_of_file,
                codes,
                &applied_fixmes,
                fn_,
                acc,
            )
        })
    }
}

pub fn get_dead_unsafe_cast_patches(env: &Env) -> Vec<Patch> {
    // `Remove_dead_unsafe_casts.get_patches ~is_test:false
    //    ~fold:(Naming_table.fold ~warn_on_naming_costly_iter:true)
    //    ~files_info:env.naming_table`
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let files: Vec<relative_path::T> =
        crate::naming_table::fold_with(Some(true), &env.naming_table, vec![], |fn_, _, mut acc| {
            acc.push(fn_.clone());
            acc
        });
    crate::remove_dead_unsafe_casts::get_patches(&ctx, Some(false), &files)
        .into_iter()
        .map(|(pos, text)| {
            Patch::Replace(InsertPatch {
                pos: pos::to_absolute(&pos),
                text,
            })
        })
        .collect()
}

pub fn get_lambda_parameter_rewrite_patches(
    ctx: &provider_context::T,
    files: &[String],
) -> Vec<Patch> {
    let _ = (ctx, files);
    // `List.concat_map files ~f:(fun file ->
    //    Server_rewrite_lambda_parameters.get_patches ctx
    //      (Relative_path.from_root ~suffix:file))`
    todo!(
        "Server_rename.get_lambda_parameter_rewrite_patches: Server_rewrite_lambda_parameters (E3) is not ported yet"
    )
}

fn find_def_filename(
    current_filename: &relative_path::T,
    definition: &symbol_definition::T<Pos>,
) -> relative_path::T {
    let def_filename = pos::filename(&definition.pos);
    if def_filename == relative_path::default {
        // When the definition is in an IDE buffer with local changes, the filename
        // in the definition will be empty.
        current_filename.clone()
    } else {
        def_filename
    }
}

/// We construct the text for the deprecated wrapper here.
///
/// Example of deprecated wrapper & its relation to the newly named function:
///
/// ```text
///   <<__Deprecated("Deprecated: Use `newlyNamedFunction` instead")>>
///   public function oldFunctionName(int $x, SomeClass $y, ...$nums): string {
///     return $this->newlyNamedFunction($x, $y, ...$nums);
///   }
///
///   /**
///    * Some docblock
///    *
///    */
///   public function newlyNamedFunction(int $x, SomeClass $y, ...$nums): string {
///     // some function body
///   }
/// ```
fn construct_deprecated_wrapper_stub(
    func_decl_text: &str,
    params_text_list: &[String],
    col_start: isize,
    returns_void: bool,
    is_async: bool,
    func_ref: DeprecatedWrapperFunctionRef,
    new_name: &str,
) -> String {
    // Since the starting column position points to the beginning of the function
    // declaration header, we can use it to figure out the indentation level
    // of the function, and insert whitespace accordingly
    let base_indentation = " ".repeat(std::cmp::max(col_start, 0) as usize);
    let deprecated_header = format!(
        "{}<<__Deprecated(\"Use `{}` instead\")>>",
        base_indentation, new_name
    );
    let func_decl = format!("{}{}", base_indentation, func_decl_text);
    // The immediate body of a function is indented by 2 extra spaces
    let func_body_indentation = " ".repeat(2);
    let return_indentation = format!("{}{}", base_indentation, func_body_indentation);
    let parameter_input = params_text_list.join(", ");
    let maybe_return = if returns_void { "" } else { "return " };
    let maybe_await = if is_async { "await " } else { "" };
    let maybe_this_or_self = match func_ref {
        DeprecatedWrapperFunctionRef::DeprecatedStaticMethodRef => "self::",
        DeprecatedWrapperFunctionRef::DeprecatedNonStaticMethodRef => "$this->",
        DeprecatedWrapperFunctionRef::DeprecatedFunctionRef => "",
    };
    let return_statement = format!(
        "{}{}{}{}{}({});",
        return_indentation, maybe_return, maybe_await, maybe_this_or_self, new_name, parameter_input
    );
    format!(
        "\n{}\n{} {{\n{}\n{}}}\n",
        deprecated_header, func_decl, return_statement, base_indentation
    )
}

fn get_pos_before_docblock_from_cst_node(
    filename: &relative_path::T,
    source_text: &full_fidelity_source_text::T,
    node: &PositionedSyntax,
) -> Pos {
    let start_offset = node.leading_start_offset() as isize;
    full_fidelity_source_text::relative_pos(filename, source_text, start_offset, start_offset)
}

/// Contains just enough information to properly wrap a function
struct WrapperCallSignatureInfo {
    params_text_list: Vec<String>,
    returns_void: bool,
    is_async: bool,
    is_static: bool,
}

/// `text node`
fn text(node: &PositionedSyntax, st: &SourceText<'_>) -> String {
    node.text(st).to_string()
}

/// Identify key information about a function so we can produce a deprecated wrapper
fn get_call_signature_for_wrap(
    func_decl: &PositionedSyntax,
    st: &SourceText<'_>,
) -> WrapperCallSignatureInfo {
    match &func_decl.syntax {
        SyntaxVariant::FunctionDeclarationHeader(h) => {
            let params = &h.function_parameter_list;
            let ret_type = &h.function_type;
            let modifiers = &h.function_modifiers;
            let params_text_list = match &params.syntax {
                SyntaxVariant::SyntaxList(params) => params
                    .iter()
                    .map(|param| {
                        let param = match &param.syntax {
                            SyntaxVariant::ListItem(li) => &li.list_item,
                            _ => panic!("Expected ListItem"),
                        };
                        match &param.syntax {
                            // NOTE:
                            //    `ParameterDeclaration` includes regular params like "$x" and
                            //     _named_ variadic parameters like "...$nums". For the latter case,
                            //     we prepend the name with the ellipsis, in order to construct
                            //     the wrapped call.
                            SyntaxVariant::ParameterDeclaration(p) => match &p.parameter_ellipsis.syntax {
                                SyntaxVariant::Missing => text(&p.parameter_name, st),
                                _ => format!("...{}", text(&p.parameter_name, st)),
                            },
                            _ => panic!("Expected some parameter type"),
                        }
                    })
                    .collect(),
                SyntaxVariant::Missing => vec![],
                _ => vec![],
            };
            let returns_void = match &ret_type.syntax {
                SyntaxVariant::GenericTypeSpecifier(g) => {
                    let type_spec = match &g.generic_argument_list.syntax {
                        SyntaxVariant::TypeArguments(ta) => match &ta.type_arguments_types.syntax {
                            SyntaxVariant::SyntaxList(l) if l.len() == 1 => match &l[0].syntax {
                                SyntaxVariant::ListItem(li) => match &li.list_item.syntax {
                                    SyntaxVariant::SimpleTypeSpecifier(s) => {
                                        Some(&s.simple_type_specifier)
                                    }
                                    _ => None,
                                },
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    };
                    match type_spec {
                        Some(type_spec) => {
                            text(&g.generic_class_type, st) == "Awaitable"
                                && text(type_spec, st) == "void"
                        }
                        None => false,
                    }
                }
                SyntaxVariant::SimpleTypeSpecifier(s) => text(&s.simple_type_specifier, st) == "void",
                _ => false,
            };
            let (is_async, is_static) = match &modifiers.syntax {
                SyntaxVariant::SyntaxList(modifiers) => {
                    let is_async = modifiers.iter().any(|m| text(m, st) == "async");
                    let is_static = modifiers.iter().any(|m| text(m, st) == "static");
                    (is_async, is_static)
                }
                _ => (false, false),
            };
            WrapperCallSignatureInfo {
                params_text_list,
                returns_void,
                is_async,
                is_static,
            }
        }
        _ => WrapperCallSignatureInfo {
            params_text_list: vec![],
            returns_void: false,
            is_async: false,
            is_static: false,
        },
    }
}

fn classish_is_interface(ctx: &provider_context::T, name: &str) -> bool {
    match decl_provider::get_class(None, ctx, &utils::add_ns(name)) {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
        decl_entry::T::Found(cls) => matches!(
            folded_class::kind(&cls),
            oxidized::ast_defs::ClassishKind::Cinterface
        ),
    }
}

/// Produce a "deprecated" version of the old [definition] so that calls to it can be rerouted.
/// If [definition] is None, this is a no-op.
fn get_deprecated_wrapper_patch(
    definition: Option<&symbol_definition::T<Pos>>,
    ctx: &provider_context::T,
    new_name: &str,
) -> Option<Patch> {
    let filename = definition.and_then(|definition| {
        let filename = pos::filename(&definition.pos);
        let is_dummy = filename == relative_path::default;
        if is_dummy {
            hack_event_logger::invariant_violation_bug(
                None,
                None,
                None,
                None,
                None,
                "--refactor has empty filename",
            );
        }
        if !is_dummy { Some(filename) } else { None }
    })?;
    let definition = definition?;
    // We need the number of spaces that the function declaration is offsetted so that we can
    // format our wrapper properly with the correct indent (i.e. we need 0-indexed columns).
    //
    // However, even though column offsets are already indexed accordingly when
    // stored in positions, `destruct_range_one_based` adds 1 in order to
    // return an [inclusive, exclusive) span.
    //
    // Thus, we subtract 1.
    let symbol_definition::T {
        span, pos, kind, ..
    } = definition;
    let (_, col_start_plus1, _, _) = pos::destruct_range_one_based(span);
    let col_start = col_start_plus1 - 1;
    let (_ctx, entry) = provider_context::add_entry_if_missing(ctx, filename.clone());
    let cst_node = server_symbol_definition::get_definition_cst_node_ctx(ctx, &entry, kind, pos)?;
    let source_text = ast_provider::compute_source_text(&entry);
    let st = full_fidelity_source_text::source_text(&source_text);
    let (func_decl_text, params_text_list, returns_void, is_async, func_ref) = match &cst_node.syntax
    {
        SyntaxVariant::MethodishDeclaration(m) => {
            let func_decl = &m.methodish_function_decl_header;
            let call_signature = get_call_signature_for_wrap(func_decl, &st);
            let func_decl_text = text(func_decl, &st);
            let func_ref = if call_signature.is_static {
                DeprecatedWrapperFunctionRef::DeprecatedStaticMethodRef
            } else {
                DeprecatedWrapperFunctionRef::DeprecatedNonStaticMethodRef
            };
            match kind {
                symbol_definition::Kind::Member { class_name, .. }
                    if classish_is_interface(ctx, class_name) =>
                {
                    // We can't add a stub that calls the new name in
                    // interfaces, as methods can't have bodies there.
                    None
                }
                _ => Some((
                    func_decl_text,
                    call_signature.params_text_list,
                    call_signature.returns_void,
                    call_signature.is_async,
                    func_ref,
                )),
            }
        }
        SyntaxVariant::FunctionDeclaration(f) => {
            let func_decl = &f.function_declaration_header;
            let call_signature = get_call_signature_for_wrap(func_decl, &st);
            let func_decl_text = text(func_decl, &st);
            let func_ref = DeprecatedWrapperFunctionRef::DeprecatedFunctionRef;
            Some((
                func_decl_text,
                call_signature.params_text_list,
                call_signature.returns_void,
                call_signature.is_async,
                func_ref,
            ))
        }
        _ => None,
    }?;
    let deprecated_wrapper_stub = construct_deprecated_wrapper_stub(
        &func_decl_text,
        &params_text_list,
        col_start,
        returns_void,
        is_async,
        func_ref,
        new_name,
    );
    let filename = find_def_filename(&filename, definition);
    let deprecated_wrapper_pos =
        get_pos_before_docblock_from_cst_node(&filename, &source_text, &cst_node);
    let patch = InsertPatch {
        pos: pos::to_absolute(&deprecated_wrapper_pos),
        text: deprecated_wrapper_stub,
    };
    Some(Patch::Insert(patch))
}

fn method_might_support_dynamic(
    ctx: &provider_context::T,
    class_name: &str,
    method_name: &str,
) -> bool {
    decl_entry::to_option(decl_provider::get_class(
        None,
        ctx,
        &utils::add_ns(class_name),
    ))
    .and_then(|class_| {
        folded_class::get_smethod(&class_, method_name)
            .or_else(|| folded_class::get_method(&class_, method_name))
    })
    .map(|elt| {
        let flags = elt.ce_flags;
        ce_flags::is_dynamicallycallable(flags) || ce_flags::supports_dynamic_type(flags)
    })
    .unwrap_or(true)
}

/// `Pos.Set`, ordered by `Pos.compare`.
type PosSet = std::collections::BTreeSet<crate::find_refs_service::PosKey>;

/// Does the rename. `definition_for_wrapper` is the definition where a
/// deprecated-wrapper may be generated, or None to suppress any possible
/// generation.
pub fn go(
    ctx: &provider_context::T,
    action: &Action,
    genv: &Genv,
    env: Env,
    definition_for_wrapper: Option<&symbol_definition::T<Pos>>,
) -> (Env, done_or_retry::T<Vec<Patch>>) {
    let (find_refs_action, new_name) = match action {
        Action::ClassRename(old_name, new_name) => (FrAction::ExplicitClass(old_name.clone()), new_name),
        Action::ClassConstRename(class_name, old_name, new_name) => (
            FrAction::Member(class_name.clone(), Member::ClassConst(old_name.clone())),
            new_name,
        ),
        Action::MethodRename {
            class_name,
            old_name,
            new_name,
        } => (
            FrAction::Member(class_name.clone(), Member::Method(old_name.clone())),
            new_name,
        ),
        Action::FunctionRename { old_name, new_name } => {
            (FrAction::Function(old_name.clone()), new_name)
        }
        Action::LocalVarRename {
            filename,
            file_content,
            pos,
            new_name,
        } => (
            FrAction::LocalVar {
                filename: filename.clone(),
                file_content: file_content.clone(),
                pos: *pos,
            },
            new_name,
        ),
    };
    let include_defs = true;
    done_or_retry::map_env(
        |refs: Vec<sfr::T>| {
            let changes = {
                let (_positions, patches) = refs.iter().fold(
                    (PosSet::new(), vec![]),
                    |(mut positions, mut patches), sfr::Result { name: _, pos }| {
                        let key = crate::find_refs_service::PosKey(pos.clone());
                        if positions.contains(&key) {
                            // Don't rename at the same position twice. Double-renames were happening (~~T157645473~~) because
                            // ServerRename uses ServerFindRefs which searches the tast, which thinks Self::TWhatever
                            // is a use of the current class at the position of the declaration of the current class.
                            (positions, patches)
                        } else {
                            positions.insert(key);
                            let replacement = InsertPatch {
                                pos: pos::to_absolute(pos),
                                text: new_name.clone(),
                            };
                            let patch = Patch::Replace(replacement);
                            patches.insert(0, patch);
                            (positions, patches)
                        }
                    },
                );
                patches
            };
            let deprecated_wrapper_patch = match action {
                Action::FunctionRename { .. } => {
                    get_deprecated_wrapper_patch(definition_for_wrapper, ctx, new_name)
                }
                Action::MethodRename {
                    class_name,
                    old_name,
                    ..
                } => {
                    if method_might_support_dynamic(ctx, class_name, old_name) {
                        get_deprecated_wrapper_patch(definition_for_wrapper, ctx, new_name)
                    } else {
                        None
                    }
                }
                Action::ClassRename(..)
                | Action::ClassConstRename(..)
                | Action::LocalVarRename { .. } => None,
            };
            prepend_opt(deprecated_wrapper_patch, changes)
        },
        server_find_refs::go(ctx, &find_refs_action, include_defs, None, &[], genv, env),
    )
}

/// `Option.value_map patch ~default:changes ~f:(fun patch -> patch :: changes)`
fn prepend_opt(patch: Option<Patch>, mut changes: Vec<Patch>) -> Vec<Patch> {
    if let Some(patch) = patch {
        changes.insert(0, patch);
    }
    changes
}

pub fn go_for_localvar(
    ctx: &provider_context::T,
    action: &FrAction,
    new_name: &str,
) -> Result<Option<Vec<Patch>>, FrAction> {
    match action {
        FrAction::LocalVar { .. } => {
            let refs = server_find_refs::go_for_localvar(ctx, action)?;
            let patches = refs.iter().fold(vec![], |mut acc, sfr::Result { name: _, pos }| {
                let replacement = InsertPatch {
                    pos: pos::to_absolute(pos),
                    text: maybe_add_dollar(new_name),
                };
                let patch = Patch::Replace(replacement);
                acc.insert(0, patch);
                acc
            });
            Ok(Some(patches))
        }
        _ => Err(action.clone()),
    }
}

fn new_name_for_symbol_definition(
    ctx: &provider_context::T,
    symbol_definition: &symbol_definition::T<Pos>,
    filename: &relative_path::T,
    pos: &Pos,
    new_name: &str,
) -> String {
    let has_dollar = |s: &str| s.starts_with('$');
    let ensure_dollar = |s: &str| {
        if has_dollar(s) {
            s.to_string()
        } else {
            format!("${}", s)
        }
    };
    let strip_dollar = |s: &str| {
        if has_dollar(s) {
            s[1..].to_string()
        } else {
            s.to_string()
        }
    };
    match &symbol_definition.kind {
        symbol_definition::Kind::Member {
            member_kind: symbol_definition::MemberKind::Property,
            ..
        } => {
            // For static properties: they always have a $-sign prefix.
            // For non-static properties:
            //   - On the definition site they have a $-sign prefix.
            //   - On usage sites they don't have a $-sign prefix.
            //   => We'll use the [old_name] to determine whether we're renaming
            //      the definition/usage site.
            let old_name = crate::file_provider::rust_provider_backend::file::get_contents(ctx, filename)
                .and_then(|content| {
                    let content = String::from_utf8_lossy(&content).into_owned();
                    // `try Some (Pos.get_text_from_pos ~content pos) with Invalid_argument _ -> None`
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        pos::get_text_from_pos(&content, pos)
                    }))
                    .ok()
                });
            let is_static = symbol_definition
                .modifiers
                .iter()
                .any(|m| matches!(m, symbol_definition::Modifier::Static));
            if is_static {
                ensure_dollar(new_name)
            } else if old_name.as_deref().is_some_and(has_dollar) {
                ensure_dollar(new_name)
            } else {
                strip_dollar(new_name)
            }
        }
        symbol_definition::Kind::Function
        | symbol_definition::Kind::Classish { .. }
        | symbol_definition::Kind::Member { .. }
        | symbol_definition::Kind::GlobalConst
        | symbol_definition::Kind::LocalVar
        | symbol_definition::Kind::TypeVar
        | symbol_definition::Kind::Param
        | symbol_definition::Kind::Typedef
        | symbol_definition::Kind::Module => new_name.to_string(),
    }
}

pub fn go_for_single_file(
    ctx: &provider_context::T,
    find_refs_action: &FrAction,
    new_name: &str,
    filename: &relative_path::T,
    symbol_definition: &symbol_definition::T<Pos>,
) -> Result<Vec<Patch>, std::convert::Infallible> {
    let action = match find_refs_action {
        FrAction::Class(str) => {
            // Note that [ServerRename.go] remaps ClassRename to Find_refs.ExplicitClass,
            // so we manually handle that here for parity.
            FrAction::ExplicitClass(str.clone())
        }
        action => action.clone(),
    };
    let refs = server_find_refs::go_for_single_file(ctx, &action, filename);
    let changes = refs.iter().fold(vec![], |mut acc, sfr::Result { name: _, pos }| {
        let replacement = InsertPatch {
            pos: pos::to_absolute(pos),
            text: new_name_for_symbol_definition(ctx, symbol_definition, filename, pos, new_name),
        };
        let patch = Patch::Replace(replacement);
        acc.insert(0, patch);
        acc
    });
    // Context: D46818062
    // When we rename symbols looking at one file at a time we always pass the [SymbolDefinition.t] along.
    // Generating a deprecated_wrapper_patch looks at the symbol definition pos, checks to see if there's a matching
    // CST node and if so, will send back a deprecated wrapper patch to write.
    //
    // However, if we're renaming a symbol in a file where the (method or function) is NOT defined,
    // we should reject any deprecated wrapper patches. We only want a patch IFF the rename action is editing
    // the file matching [symbol_definition.pos.file]
    let should_write_deprecated_wrapper_patch = *filename == pos::filename(&symbol_definition.pos);
    let definition = if should_write_deprecated_wrapper_patch {
        Some(symbol_definition)
    } else {
        None
    };
    let deprecated_wrapper_patch = match find_refs_action {
        FrAction::Function(_) => get_deprecated_wrapper_patch(definition, ctx, new_name),
        FrAction::Member(class_name, Member::Method(old_name)) => {
            if method_might_support_dynamic(ctx, class_name, old_name) {
                get_deprecated_wrapper_patch(definition, ctx, new_name)
            } else {
                None
            }
        }
        FrAction::Class(_)
        | FrAction::Member(..)
        | FrAction::ExplicitClass(_)
        | FrAction::LocalVar { .. }
        | FrAction::GConst(_) => None,
    };
    let rename_patches = if should_write_deprecated_wrapper_patch {
        prepend_opt(deprecated_wrapper_patch, changes)
    } else {
        changes
    };
    Ok(rename_patches)
}

/// Like go_ide, but rather than looking up a symbolDefinition manually from a file and
/// converting a Server_rename_types.action to a Find_refs.action, we supply a Find_refs.action
/// directly.
pub fn go_ide_with_find_refs_action(
    ctx: &provider_context::T,
    find_refs_action: &FrAction,
    new_name: &str,
    symbol_definition: &symbol_definition::T<Pos>,
    genv: &Genv,
    env: Env,
) -> Result<(Env, done_or_retry::T<Vec<Patch>>), String> {
    let include_defs = true;
    let rename_patches = done_or_retry::map_env(
        |refs: Vec<sfr::T>| {
            let changes = refs.iter().fold(vec![], |mut acc, sfr::Result { name: _, pos }| {
                let replacement = InsertPatch {
                    pos: pos::to_absolute(pos),
                    text: new_name.to_string(),
                };
                let patch = Patch::Replace(replacement);
                acc.insert(0, patch);
                acc
            });
            let deprecated_wrapper_patch = match find_refs_action {
                FrAction::Function(_) => {
                    get_deprecated_wrapper_patch(Some(symbol_definition), ctx, new_name)
                }
                FrAction::Member(class_name, Member::Method(old_name)) => {
                    if method_might_support_dynamic(ctx, class_name, old_name) {
                        get_deprecated_wrapper_patch(Some(symbol_definition), ctx, new_name)
                    } else {
                        None
                    }
                }
                FrAction::Class(_)
                | FrAction::Member(..)
                | FrAction::ExplicitClass(_)
                | FrAction::LocalVar { .. }
                | FrAction::GConst(_) => None,
            };
            prepend_opt(deprecated_wrapper_patch, changes)
        },
        server_find_refs::go(ctx, find_refs_action, include_defs, None, &[], genv, env),
    );
    Ok(rename_patches)
}

#[cfg(test)]
mod tests {
    //! The find-refs and refactor cases of `test/integration/common_tests.py`
    //! (`test_find_refs`, `test_refactor_methods`, `test_refactor_classes`)
    //! on the files of `test/integration/data/simple_repo`, typechecked
    //! with the dependency edges recorded, as the daemon does after its
    //! init. The expected positions are those the OCaml daemon gives (the
    //! `.py` file); the order of the patches is the client's business (E2),
    //! so they are compared sorted. Runs in a child process
    //! (`fanout::testing::with_edges`: the graph and `trace` are global).

    use std::path::Path;
    use std::sync::Arc;

    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;
    use crate::ctx::Ctx;
    use crate::fanout::testing::with_edges;
    use crate::typing_deps;
    use crate::typing_deps_mode::T::InMemoryMode;

    static ROOTS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

    const SIMPLE_REPO: &str = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../test/integration/data/simple_repo"
    );

    /// The files of `simple_repo`, with `foo_4.php` replaced when given.
    fn repo_files(foo_4: Option<&str>) -> Vec<(String, String)> {
        let mut files = vec![];
        let mut names: Vec<_> = std::fs::read_dir(SIMPLE_REPO)
            .unwrap()
            .map(|e| e.unwrap().file_name().into_string().unwrap())
            .filter(|n| n.ends_with(".php") || n.ends_with(".hack"))
            .collect();
        names.sort();
        for name in names {
            let contents = match (name.as_str(), foo_4) {
                ("foo_4.php", Some(c)) => c.to_string(),
                _ => std::fs::read_to_string(format!("{SIMPLE_REPO}/{name}")).unwrap(),
            };
            files.push((name, contents));
        }
        files
    }

    /// A daemon after its init: the files declared, the reverse naming
    /// table, every file typechecked with the edges registered, and the env
    /// with the forward naming table.
    fn daemon(files: &[(String, String)]) -> (Genv, Env) {
        // The files are read from the disk (entries of the context), as in
        // the daemon: they are written to a fresh root.
        let root = std::env::temp_dir().join(format!(
            "hh_f6_server_rename_{}_{}",
            std::process::id(),
            ROOTS.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
        ));
        std::fs::create_dir_all(&root).unwrap();
        for (name, contents) in files {
            std::fs::write(root.join(name), contents).unwrap();
        }
        let root = root.canonicalize().unwrap();
        let ctx = Ctx::new(&root, TypecheckerOptions::default()).unwrap();
        let mut paths = ctx.hhi_paths.clone();
        let mut checked = vec![];
        for (name, contents) in files {
            let path = ::pos::RelativePath::new(::pos::Prefix::Root, name.as_str());
            ctx.files.set(path, contents.as_str());
            paths.push(path);
            checked.push(path);
        }
        crate::check::declare_files(&ctx, &paths, &mut crate::check::Stats::default());
        ctx.build_dep_hash_index();
        relative_path::set_path_prefix(relative_path::Prefix::Root, &root);
        relative_path::set_path_prefix(relative_path::Prefix::Hhi, Path::new("/hhi"));
        relative_path::set_path_prefix(relative_path::Prefix::Tmp, Path::new("/tmp"));
        let ctx = Arc::new(ctx);
        crate::hh_single_type_check::install(&ctx);
        crate::ast_provider::set_local_parser_cache_enabled(false);
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .stack_size(256 << 20)
            .build()
            .unwrap();
        pool.install(|| {
            typing_deps::trace.store(true, std::sync::atomic::Ordering::SeqCst);
            let _ = crate::check::check_files_typed_by_file(
                &ctx,
                &checked,
                &mut crate::check::Stats::default(),
            );
            typing_deps::flush_deps(&InMemoryMode(None));
            typing_deps::trace.store(false, std::sync::atomic::Ordering::SeqCst);
        });
        let mut files_info = relative_path::map::T::new();
        for p in &checked {
            let p: relative_path::T = (*p).into();
            let decls = crate::direct_decl_service::direct_decl_parse(&ctx, &p).unwrap();
            files_info.insert(p.clone(), crate::direct_decl_service::decls_to_fileinfo(&p, &decls));
        }
        let genv = crate::server_env_build::default_genv();
        let mut env = crate::server_env_build::make_env(
            "test",
            InMemoryMode(None),
            None,
            &genv.config,
            Path::new("/"),
        );
        env.naming_table = crate::naming_table::create(files_info);
        env.ctx = ctx;
        (genv, env)
    }

    /// `{"char_start", "char_end", "line", "col_start", "col_end",
    /// "patch_type", "replacement"}` of a patch, with its file.
    fn show(p: &Patch) -> String {
        let (ty, ip) = match p {
            Patch::Insert(ip) => ("insert", ip.clone()),
            Patch::Replace(ip) => ("replace", ip.clone()),
            Patch::Remove(pos) => ("remove", InsertPatch { pos: pos.clone(), text: "".into() }),
        };
        let (cs, ce) = pos::info_raw(&ip.pos);
        let (line, c1, c2) = pos::info_pos(&ip.pos);
        format!(
            "/{} {cs}-{ce} line {line} cols {c1}-{c2} {ty} {:?}",
            std::path::Path::new(&pos::filename(&ip.pos)).file_name().unwrap().to_string_lossy(),
            ip.text
        )
    }

    fn rename(files: &[(String, String)], action: Action) -> Vec<String> {
        let (genv, env) = daemon(files);
        let ctx = env.ctx.clone();
        let (_env, r) = go(&ctx, &action, &genv, env, None);
        let mut r: Vec<String> = match r {
            done_or_retry::T::Done(r) => r.iter().map(show).collect(),
            done_or_retry::T::Retry => panic!("retry"),
        };
        r.sort();
        r
    }

    /// `rename` with the definition of the symbol (for the deprecated
    /// wrapper), found as `hh_client --refactor` does: `Server_rename`'s
    /// caller gives `Symbol_definition` of the method.
    fn find_refs(files: &[(String, String)], action: FrAction) -> Vec<String> {
        let (genv, env) = daemon(files);
        let ctx = env.ctx.clone();
        let (_env, r) = server_find_refs::go(&ctx, &action, false, None, &[], &genv, env);
        match r {
            done_or_retry::T::Done(r) => server_find_refs::to_absolute(&r)
                .iter()
                .map(|sfr::Result { name, pos }| {
                    let (line, c1, c2) = pos::info_pos(pos);
                    let file = pos::filename(pos);
                    let file = std::path::Path::new(&file).file_name().unwrap().to_string_lossy().into_owned();
                    format!("File \"/{}\", line {}, characters {}-{}: {}", file, line, c1, c2, name)
                })
                .collect(),
            done_or_retry::T::Retry => panic!("retry"),
        }
    }

    #[test]
    fn common_tests_find_refs() {
        with_edges(module_path!(), "common_tests_find_refs", &[], || {
            let files = repo_files(None);
            assert_eq!(
                find_refs(&files, FrAction::Function("h".into())),
                vec!["File \"/foo_3.php\", line 11, characters 13-13: h"]
            );
            assert_eq!(
                find_refs(
                    &files,
                    FrAction::Member("Foo".into(), Member::Method("__construct".into()))
                ),
                vec!["File \"/foo_3.php\", line 10, characters 17-19: Foo::__construct"]
            );
            assert_eq!(
                find_refs(&files, FrAction::Class("Foo".into())),
                vec!["File \"/foo_3.php\", line 10, characters 17-19: Foo"]
            );
        })
    }

    const FOO_4_METHODS: &str = "<?hh
            <<__SupportDynamicType>>
            class Bar extends Foo {
                public function f(): void {}
                public function g(): void {}
            }
            <<__SupportDynamicType>>
            class Baz extends Bar {
                public function g(): void {
                    $this->f();
                }
            }
            ";

    #[test]
    fn common_tests_refactor_methods() {
        with_edges(module_path!(), "common_tests_refactor_methods", &[], || {
            let files = repo_files(Some(FOO_4_METHODS));
            let (genv, env) = daemon(&files);
            let ctx = env.ctx.clone();
            // `hh_client --refactor Method Bar::f Bar::wat`: the definition of
            // `Bar::f` for the wrapper (`Server_rename.go`'s caller gets it
            // from `Server_symbol_definition`).
            let path: relative_path::T =
                ::pos::RelativePath::new(::pos::Prefix::Root, "foo_4.php").into();
            let (ctx2, entry) = provider_context::add_entry_if_missing(&ctx, path);
            let (def, _action) = server_find_refs::go_from_file_ctx_with_symbol_definition(
                &ctx2,
                &entry,
                &crate::file_content::position::from_one_based(4, 33),
            )
            .unwrap();
            let action = Action::MethodRename {
                class_name: "Bar".into(),
                old_name: "f".into(),
                new_name: "wat".into(),
            };
            let (_env, r) = go(&ctx, &action, &genv, env, Some(&def));
            let mut r: Vec<String> = match r {
                done_or_retry::T::Done(r) => r.iter().map(show).collect(),
                done_or_retry::T::Retry => panic!("retry"),
            };
            r.sort();
            assert_eq!(
                r,
                vec![
                    "/foo_4.php 110-111 line 4 cols 33-33 replace \"wat\"".to_string(),
                    "/foo_4.php 326-327 line 10 cols 28-28 replace \"wat\"".to_string(),
                    "/foo_4.php 78-78 line 4 cols 1-1 insert \"\\n                <<__Deprecated(\\\"Use `wat` instead\\\")>>\\n                public function f(): void {\\n                  $this->wat();\\n                }\\n\"".to_string(),
                ]
            );
        })
    }

    #[test]
    fn common_tests_refactor_classes() {
        with_edges(module_path!(), "common_tests_refactor_classes", &[], || {
            let foo_4 = "<?hh

            class Bar extends Foo {
                const int FOO = 42;

                private static int $val = 0;

                public function f(): void {}
                public function g(): void {}
                public static function h(): void {}
                public static function i(): void {
                    self::h();
                    self::$val = 1;
                    static::$val = 2;
                    $x = self::FOO;
                }
            }

            class Baz extends Bar {
                public function g(): void {
                    $this->f();
                    parent::g();
                }
            }
            ";
            let files = repo_files(Some(foo_4));
            assert_eq!(
                rename(&files, Action::ClassRename("Foo".into(), "Qux".into())),
                vec![
                    "/foo_3.php 161-164 line 10 cols 17-19 replace \"Qux\"",
                    "/foo_3.php 86-89 line 7 cols 15-17 replace \"Qux\"",
                    "/foo_4.php 36-39 line 3 cols 31-33 replace \"Qux\"",
                ]
            );
            assert_eq!(
                rename(&files, Action::ClassRename("Bar".into(), "Quux".into())),
                vec![
                    "/foo_4.php 24-27 line 3 cols 19-21 replace \"Quux\"",
                    "/foo_4.php 522-525 line 19 cols 31-33 replace \"Quux\"",
                ]
            );
            // no double-rename (T157645473)
            let foo_4 = "<?hh
                class Foo {
                  const type TEntry = int;
                  public function main(): self::TEntry {
                    return 3;
                  }
                }

            ";
            let files = repo_files(Some(foo_4));
            let files: Vec<_> = files.into_iter().filter(|(n, _)| n != "foo_3.php").collect();
            assert_eq!(
                rename(&files, Action::ClassRename("Foo".into(), "Bar".into())),
                vec!["/foo_4.php 27-30 line 2 cols 23-25 replace \"Bar\""]
            );
        })
    }

    /// `findrefs_multiworker`: from 10 files on, the files are searched by
    /// buckets (`parallel_find_refs`); with 4 workers the results are those
    /// of one worker (the OCaml's order between buckets depends on which
    /// worker finishes first: compared as sets).
    #[test]
    fn find_refs_by_buckets() {
        with_edges(module_path!(), "find_refs_by_buckets", &[], || {
            let mut files = vec![("f.php".to_string(), "<?hh\nfunction target(): void {}\n".to_string())];
            for i in 0..14 {
                files.push((
                    format!("u{i:02}.php"),
                    format!("<?hh\nfunction use{i}(): void {{\n  target();\n  target();\n}}\n"),
                ));
            }
            let (mut genv, env) = daemon(&files);
            let ctx = env.ctx.clone();
            let action = FrAction::Function("target".into());
            let (env, r1) = server_find_refs::go(&ctx, &action, true, None, &[], &genv, env);
            genv.num_workers = 4;
            let (_env, r4) = server_find_refs::go(&ctx, &action, true, None, &[], &genv, env);
            let show = |r: done_or_retry::T<Vec<sfr::T>>| match r {
                done_or_retry::T::Done(r) => {
                    let mut v: Vec<String> = server_find_refs::to_absolute(&r)
                        .iter()
                        .map(|r| format!("{} {}", pos::string(&r.pos), r.name))
                        .collect();
                    v.sort();
                    v
                }
                done_or_retry::T::Retry => panic!("retry"),
            };
            let (r1, r4) = (show(r1), show(r4));
            assert_eq!(r1.len(), 29);
            assert_eq!(r1, r4);
        })
    }

}
