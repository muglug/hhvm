// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `providers/naming_provider.ml`. See `hh/PORTING.md`.
//!
//! Of each function that matches on the backend, two branches are ported:
//! `Shared_memory`, the backend of `hh_server` and `hh_single_type_check`,
//! and `Local_memory`, the IDE daemon's ([`local_memory`]).
//!
//! The `Shared_memory` lookups look at the entries of the context first
//! (`find_symbol_in_context_with_suppression`), then at `Naming_heap`. The
//! code keeps the shape of the OCaml's `Rust_provider_backend` branch
//! ([`rust_provider_backend`]: `with_ctx_proxy_opt` and hackrs's
//! `NamingTableWithContext`, which also look at the entries first): its
//! fallback is the daemon's reverse naming table of the `Ctx`
//! (`crate::ctx::reverse_naming`, built after the init by
//! `Ctx::build_reverse_naming_table`), which behaves as `Naming_heap`; the batch
//! checker (`hh single`), which has no reverse table, asks the decl stores,
//! whose names are those the init bound.
//!
//! The functions that change the naming table (`add_*`, `remove_*_batch`,
//! `update`) take the `Provider_backend.t` of the OCaml as the context whose
//! backend it is, and change the reverse naming table of the `Ctx` (or the
//! delta of the `Local_memory` backend); so does `get_files`.
//! `db_path_of_ctx` is `crate::db_path_provider::get_naming_db_path` here.

use std::sync::Arc;

use bstr::BString;
use naming_special_names_rust as sn;
use oxidized::decl_reference::DeclReference;
use oxidized::file_info;
use oxidized::file_info::NameType;
use oxidized::naming_types::KindOfType;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use relative_path::RelativePath;

use crate::ast_provider;
use crate::provider_context;
use crate::provider_context::T as Ctx;

/// `Naming_sqlite.to_canon_name_key`
fn naming_sqlite_to_canon_name_key(name: &str) -> String {
    name.to_ascii_lowercase()
}

/// `File_info.get_pos_filename`
fn get_pos_filename(pos: &file_info::Pos) -> RelativePath {
    pos.path().clone()
}

/// `(File_info.pos * File_info.name_type) option`, what the functions that
/// find a symbol answer.
pub type FoundSymbol = Option<(file_info::Pos, NameType)>;

fn attach_name_type_to_tuple((name_type, path): (NameType, RelativePath)) -> (file_info::Pos, NameType) {
    (file_info::Pos::File(name_type, Arc::new(path)), name_type)
}

fn attach_name_type<A>(name_type: NameType, x: A) -> (A, NameType) {
    (x, name_type)
}

fn remove_name_type<A>(x: (A, NameType)) -> A {
    x.0
}

/// `Naming_types.type_kind_to_name_type`
fn kind_to_name_type(kind_of_type: KindOfType) -> NameType {
    NameType::from(kind_of_type)
}

fn name_type_to_kind(name_type: NameType) -> KindOfType {
    // `Naming_types.type_kind_of_name_type`
    match KindOfType::try_from(name_type) {
        Ok(kind_of_type) => kind_of_type,
        // `File_info.show_name_type` (`with_path = false`)
        Err(_) => panic!("Unexpected name type {:?}", name_type),
    }
}

fn find_symbol_in_context(
    ctx: &Ctx,
    get_entry_symbols: impl Fn(&file_info::Ids) -> Vec<(file_info::Id, NameType)>,
    is_symbol: impl Fn(&str) -> bool,
) -> FoundSymbol {
    find_symbol_in_entries(&ctx.entries, provider_context::get_popt(ctx), get_entry_symbols, is_symbol)
}

/// [`find_symbol_in_context`] on the entries and parser options of a
/// context.
fn find_symbol_in_entries(
    entries: &provider_context::Entries,
    popt: &oxidized::parser_options::ParserOptions,
    get_entry_symbols: impl Fn(&file_info::Ids) -> Vec<(file_info::Id, NameType)>,
    is_symbol: impl Fn(&str) -> bool,
) -> FoundSymbol {
    // `Relative_path.Map.filter_map` sees every entry, in order of their
    // paths; `Relative_path.Map.choose_opt` is the first of what it keeps.
    let found: Vec<(file_info::Pos, NameType)> = entries
        .iter()
        .filter_map(|(_path, entry)| {
            // CARE! This obtains names from the AST. They're usually similar to what we get from direct-decl-parser
            // (which is what's used to populate the naming table). But they disagree in cases like
            // "namespace N; namespace M {function f(){} }" where AST says "M\f" and direct-decl says "N\M\f".
            // We can therefore end in situations where if you're walking the AST and find a name, and you ask
            // for it, then Naming_provider will tell you it exists (via the Provider_context entry) but
            // Decl_provider will tell you it doesn't.
            let ids = ast_provider::compute_file_info(popt, entry);
            let symbols = get_entry_symbols(&ids);
            symbols.into_iter().find_map(|(id, kind)| {
                if is_symbol(&id.name) {
                    Some((id.pos, kind))
                } else {
                    None
                }
            })
        })
        .collect();
    found.into_iter().next()
}

fn find_const_in_context(ctx: &Ctx, name: &str) -> FoundSymbol {
    find_symbol_in_context(
        ctx,
        |file_info::Ids { consts, .. }| {
            consts
                .iter()
                .map(|id| attach_name_type(NameType::Const, id.clone()))
                .collect()
        },
        |s| name == s,
    )
}

fn find_fun_in_context(ctx: &Ctx, name: &str) -> FoundSymbol {
    find_symbol_in_context(
        ctx,
        |file_info::Ids { funs, .. }| {
            funs.iter()
                .map(|id| attach_name_type(NameType::Fun, id.clone()))
                .collect()
        },
        |s| name == s,
    )
}

fn compute_fun_canon_name(ctx: &Ctx, path: &RelativePath, name: &str) -> Option<String> {
    let canon_name = |fd: oxidized::nast::FunDef| fd.name.1;
    ast_provider::find_ifun_in_file(ctx, path, name).map(canon_name)
}

fn find_fun_canon_name_in_context(ctx: &Ctx, name: &str) -> Option<String> {
    // `String.lowercase`
    let name = name.to_ascii_lowercase();
    let symbol_opt = find_symbol_in_context(
        ctx,
        |file_info::Ids { funs, .. }| {
            funs.iter()
                .map(|id| attach_name_type(NameType::Fun, id.clone()))
                .collect()
        },
        |symbol_name| naming_sqlite_to_canon_name_key(symbol_name) == name,
    );
    match symbol_opt {
        Some((pos, _name_type)) => compute_fun_canon_name(ctx, &get_pos_filename(&pos), &name),
        None => None,
    }
}

fn get_entry_symbols_for_type(
    file_info::Ids {
        classes, typedefs, ..
    }: &file_info::Ids,
) -> Vec<(file_info::Id, NameType)> {
    let classes = classes
        .iter()
        .map(|id| attach_name_type(NameType::Class, id.clone()));
    let typedefs = typedefs
        .iter()
        .map(|id| attach_name_type(NameType::Typedef, id.clone()));
    classes.chain(typedefs).collect()
}

fn find_type_in_context(ctx: &Ctx, name: &str) -> FoundSymbol {
    find_symbol_in_context(ctx, get_entry_symbols_for_type, |s| name == s)
}

fn compute_type_canon_name(
    ctx: &Ctx,
    path: &RelativePath,
    kind: KindOfType,
    name: &str,
) -> Option<String> {
    match kind {
        KindOfType::TClass => ast_provider::find_iclass_in_file(ctx, path, name)
            .map(|oxidized::nast::Class_ { name, .. }| name.1),
        KindOfType::TTypedef => ast_provider::find_itypedef_in_file(ctx, path, name)
            .map(|oxidized::nast::Typedef { name, .. }| name.1),
    }
}

fn find_type_canon_name_in_context(ctx: &Ctx, name: &str) -> Option<String> {
    // `String.lowercase`
    let name = name.to_ascii_lowercase();
    let symbol_opt = find_symbol_in_context(ctx, get_entry_symbols_for_type, |symbol_name| {
        naming_sqlite_to_canon_name_key(symbol_name) == name
    });
    match symbol_opt {
        Some((pos, name_type)) => compute_type_canon_name(
            ctx,
            &get_pos_filename(&pos),
            name_type_to_kind(name_type),
            &name,
        ),
        None => None,
    }
}

fn find_module_in_context(ctx: &Ctx, name: &str) -> FoundSymbol {
    find_symbol_in_context(
        ctx,
        |file_info::Ids { modules, .. }| {
            modules
                .iter()
                .map(|id| attach_name_type(NameType::Module, id.clone()))
                .collect()
        },
        |s| name == s,
    )
}

/// Not in the OCaml: forget the per-thread memo of the kinds of the type
/// names (see `crate::rt::decl_epoch`).
pub fn forget_thread_memos() {
    rust_provider_backend::naming::types::forget_thread_memos()
}

pub fn get_entry_contents(ctx: &Ctx, filename: &RelativePath) -> Option<BString> {
    match ctx.entries.get(filename) {
        None => None,
        Some(entry) => {
            let source_text = ast_provider::compute_source_text(entry);
            Some(BString::from(crate::full_fidelity_source_text::text(
                &source_text,
            )))
        }
    }
}

fn is_path_in_ctx(ctx: &Ctx, path: &RelativePath) -> bool {
    ctx.entries.contains_key(path)
}

fn is_pos_in_ctx(ctx: &Ctx, pos: &file_info::Pos) -> bool {
    is_path_in_ctx(ctx, &get_pos_filename(pos))
}

pub fn rust_backend_ctx_proxy(ctx: &Ctx) -> Option<rust_provider_backend::CtxProxy> {
    // (`Provider_context.get_entries`, borrowed: copying the map writes its
    // reference count, which every thread shares.)
    if ctx.entries.is_empty() {
        None
    } else {
        let c = |ctx: &Ctx| Arc::clone(ctx);
        Some(rust_provider_backend::CtxProxy {
            get_entry_contents: Box::new({
                let ctx = c(ctx);
                move |filename| get_entry_contents(&ctx, filename)
            }),
            is_pos_in_ctx: Box::new({
                let ctx = c(ctx);
                move |pos| is_pos_in_ctx(&ctx, pos)
            }),
            find_fun_canon_name_in_context: Box::new({
                let ctx = c(ctx);
                move |name| find_fun_canon_name_in_context(&ctx, name)
            }),
            find_type_canon_name_in_context: Box::new({
                let ctx = c(ctx);
                move |name| find_type_canon_name_in_context(&ctx, name)
            }),
            find_const_in_context: Box::new({
                let ctx = c(ctx);
                move |name| find_const_in_context(&ctx, name)
            }),
            find_fun_in_context: Box::new({
                let ctx = c(ctx);
                move |name| find_fun_in_context(&ctx, name)
            }),
            find_type_in_context: Box::new({
                let ctx = c(ctx);
                move |name| find_type_in_context(&ctx, name)
            }),
            find_module_in_context: Box::new({
                let ctx = c(ctx);
                move |name| find_module_in_context(&ctx, name)
            }),
        })
    }
}

/// Look up the position at which the given global constant was declared in
/// the reverse naming table.
pub fn get_const_pos(ctx: &Ctx, name: &str) -> Option<file_info::Pos> {
    if let Some(lm) = ctx.local_memory() {
        return local_memory::get_const_pos(&local_memory::View::of_ctx(ctx, lm), name);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::consts::get_pos(ctx, rust_backend_ctx_proxy(ctx), name)
}

/// Determine whether a global constant with the given name is declared in
/// the reverse naming table.
pub fn const_exists(ctx: &Ctx, name: &str) -> bool {
    get_const_pos(ctx, name).is_some()
}

/// Look up the file path at which the given global constant was declared in
/// the reverse naming table.
pub fn get_const_path(ctx: &Ctx, name: &str) -> Option<RelativePath> {
    get_const_pos(ctx, name).map(|pos| get_pos_filename(&pos))
}

/// Record that a global constant with the given name was declared at the
/// given position.
pub fn add_const(backend: &crate::ctx::Ctx, name: &str, pos: &file_info::Pos) {
    if let Some(lm) = backend.local_memory() {
        return local_memory::add_const(lm, name, pos);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::consts::add(backend, name, pos)
}

/// Remove all global constants with the given names from the reverse naming
/// table.
pub fn remove_const_batch(backend: &crate::ctx::Ctx, names: &[String]) {
    if let Some(lm) = backend.local_memory() {
        return local_memory::remove_const_batch(lm, names);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::consts::remove_batch(backend, names)
}

/// Look up the position at which the given global function was declared in
/// the reverse naming table.
pub fn get_fun_pos(ctx: &Ctx, name: &str) -> Option<file_info::Pos> {
    if let Some(lm) = ctx.local_memory() {
        return local_memory::get_fun_pos(&local_memory::View::of_ctx(ctx, lm), name);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::funs::get_pos(ctx, rust_backend_ctx_proxy(ctx), name)
}

/// Determine whether a global function with the given name is declared in
/// the reverse naming table.
pub fn fun_exists(ctx: &Ctx, name: &str) -> bool {
    get_fun_pos(ctx, name).is_some()
}

/// Look up the file path in which the given global function was declared in
/// the reverse naming table.
pub fn get_fun_path(ctx: &Ctx, name: &str) -> Option<RelativePath> {
    get_fun_pos(ctx, name).map(|pos| get_pos_filename(&pos))
}

/// Look up the canonical name for the given global function.
/// THIS IS A BAD API. The reverse-naming-table should solely be a multimap from
/// symbol name (maybe case insensitive) to filename+type. That's what
/// the other APIs here do. But this API requires us to read the filename
/// and parse it to return the canon name. Moreover, one form of storage
/// (SQL) only stores filenames, while another form of storage (sharedmem)
/// only stores canonical names, which means we can't easily clean up
/// this API.
pub fn get_fun_canon_name(ctx: &Ctx, name: &str) -> Option<String> {
    if let Some(lm) = ctx.local_memory() {
        // `String.lowercase`
        let name = name.to_ascii_lowercase();
        return match find_fun_canon_name_in_context(ctx, &name) {
            name_opt @ Some(_) => name_opt,
            None => local_memory::get_fun_canon_name(ctx, lm, &name),
        };
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::funs::get_canon_name(ctx, rust_backend_ctx_proxy(ctx), name)
}

/// Record that a global function with the given name was declared at the
/// given position.
pub fn add_fun(backend: &crate::ctx::Ctx, name: &str, pos: &file_info::Pos) {
    if let Some(lm) = backend.local_memory() {
        return local_memory::add_fun(lm, name, pos);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::funs::add(backend, name, pos)
}

/// Remove all global functions with the given names from the reverse naming
/// table.
pub fn remove_fun_batch(backend: &crate::ctx::Ctx, names: &[String]) {
    if let Some(lm) = backend.local_memory() {
        return local_memory::remove_fun_batch(lm, names);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::funs::remove_batch(backend, names)
}

/// Record that a type (one of [Naming_types.kind_of_type] was declared at
/// the given position. These types all live in the same namespace, unlike
/// functions and constants.
pub fn add_type(backend: &crate::ctx::Ctx, name: &str, pos: &file_info::Pos, kind: KindOfType) {
    if let Some(lm) = backend.local_memory() {
        return local_memory::add_type(lm, name, pos, kind);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::types::add(backend, name, (pos, kind))
}

/// Remove all types with the given names from the reverse naming table.
pub fn remove_type_batch(backend: &crate::ctx::Ctx, names: &[String]) {
    if let Some(lm) = backend.local_memory() {
        return local_memory::remove_type_batch(lm, names);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::types::remove_batch(backend, names)
}

/// Look up the position and kind with which the given type was declared in
/// the reverse naming table.
pub fn get_type_pos_and_kind(ctx: &Ctx, name: &str) -> Option<(file_info::Pos, KindOfType)> {
    if let Some(lm) = ctx.local_memory() {
        return local_memory::get_type_pos_and_kind(&local_memory::View::of_ctx(ctx, lm), name);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::types::get_pos(ctx, rust_backend_ctx_proxy(ctx), name)
}

/// Look up the position at which the given type was declared in the reverse
/// naming table.
pub fn get_type_pos(ctx: &Ctx, name: &str) -> Option<file_info::Pos> {
    match get_type_pos_and_kind(ctx, name) {
        Some((pos, _kind)) => Some(pos),
        None => None,
    }
}

/// Look up the file path declaring the given type in the reverse naming
/// table.
pub fn get_type_path(ctx: &Ctx, name: &str) -> Option<RelativePath> {
    match get_type_pos_and_kind(ctx, name) {
        Some((pos, _kind)) => Some(get_pos_filename(&pos)),
        None => None,
    }
}

/// Look up the path and kind with which the given type was declared in the
/// reverse naming table.
pub fn get_type_path_and_kind(ctx: &Ctx, name: &str) -> Option<(RelativePath, KindOfType)> {
    match get_type_pos_and_kind(ctx, name) {
        Some((pos, kind)) => Some((get_pos_filename(&pos), kind)),
        None => None,
    }
}

/// Look up the kind with which the given type was declared in the reverse
/// naming table.
pub fn get_type_kind(ctx: &Ctx, name: &str) -> Option<KindOfType> {
    if ctx.local_memory().is_some() {
        return get_type_pos_and_kind(ctx, name).map(|(_pos, kind)| kind);
    }
    // `match get_type_pos_and_kind ctx name with Some (_pos, kind) -> ...`:
    // without the entries of a context, the position is that of the
    // backend's lookup, which is not built only to be dropped.
    rust_provider_backend::naming::types::get_kind(ctx, rust_backend_ctx_proxy(ctx), name)
}

/// Look up the canonical name for the given type.
/// THIS IS A BAD API. The reverse-naming-table should solely be a multimap from
/// symbol name (maybe case insensitive) to filename+type. That's what
/// the other APIs here do. But this API requires us to read the filename
/// and parse it to return the canon name. Moreover, one form of storage
/// (SQL) only stores filenames, while another form of storage (sharedmem)
/// only stores canonical names, which means we can't easily clean up
/// this API.
pub fn get_type_canon_name(ctx: &Ctx, name: &str) -> Option<String> {
    if let Some(lm) = ctx.local_memory() {
        // `String.lowercase`
        let name = name.to_ascii_lowercase();
        return match find_type_canon_name_in_context(ctx, &name) {
            name_opt @ Some(_) => name_opt,
            None => local_memory::get_type_canon_name(ctx, lm, &name),
        };
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::types::get_canon_name(ctx, rust_backend_ctx_proxy(ctx), name)
}

/// Look up the file path declaring the given class in the reverse naming
/// table. Same as calling [get_type_pos] and extracting the path if the result
/// is a [Naming_types.TClass].
pub fn get_class_path(ctx: &Ctx, name: &str) -> Option<RelativePath> {
    match get_type_path_and_kind(ctx, name) {
        Some((fn_, KindOfType::TClass)) => Some(fn_),
        Some((_, KindOfType::TTypedef)) | None => None,
    }
}

/// Record that a class with the given name was declared at the given
/// position. Same as calling [add_type] with [Naming_types.TClass].
pub fn add_class(backend: &crate::ctx::Ctx, name: &str, pos: &file_info::Pos) {
    add_type(backend, name, pos, KindOfType::TClass)
}

/// Look up the file path declaring the given class in the reverse naming
/// table. Same as calling [get_type_pos] and extracting the path if the result
/// is a [Naming_types.TTypedef].
pub fn get_typedef_path(ctx: &Ctx, name: &str) -> Option<RelativePath> {
    // This function is used even for code that typechecks clean, in order to judge
    // whether an opaque typedef is visible (which it is only in the file being typechecked
    match get_type_path_and_kind(ctx, name) {
        Some((fn_, KindOfType::TTypedef)) => Some(fn_),
        Some((_, KindOfType::TClass)) | None => None,
    }
}

/// `get_typedef_path ctx name = Some file` (not in the OCaml): the test of
/// `Typing_env.should_expand_type_alias`, without building the path.
pub fn typedef_path_is(ctx: &Ctx, name: &str, file: &RelativePath) -> bool {
    if ctx.local_memory().is_some() {
        return get_typedef_path(ctx, name).as_ref() == Some(file);
    }
    rust_provider_backend::naming::types::typedef_path_is(ctx, rust_backend_ctx_proxy(ctx), name, file)
}

/// Record that a class with the given name was declared at the given
/// position. Same as calling [add_type] with [Naming_types.TTypedef].
pub fn add_typedef(backend: &crate::ctx::Ctx, name: &str, pos: &file_info::Pos) {
    add_type(backend, name, pos, KindOfType::TTypedef)
}

pub fn get_module_pos(ctx: &Ctx, name: &str) -> Option<file_info::Pos> {
    if let Some(lm) = ctx.local_memory() {
        return local_memory::get_module_pos(&local_memory::View::of_ctx(ctx, lm), name);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::modules::get_pos(ctx, rust_backend_ctx_proxy(ctx), name)
}

pub fn get_module_path(ctx: &Ctx, name: &str) -> Option<RelativePath> {
    get_module_pos(ctx, name).map(|pos| get_pos_filename(&pos))
}

pub fn module_exists(ctx: &Ctx, name: &str) -> bool {
    if name == sn::modules::DEFAULT {
        true
    } else {
        get_module_pos(ctx, name).is_some()
    }
}

pub fn add_module(backend: &crate::ctx::Ctx, name: &str, pos: &file_info::Pos) {
    if let Some(lm) = backend.local_memory() {
        return local_memory::add_module(lm, name, pos);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::modules::add(backend, name, pos)
}

pub fn remove_module_batch(backend: &crate::ctx::Ctx, names: &[String]) {
    if let Some(lm) = backend.local_memory() {
        return local_memory::remove_module_batch(lm, names);
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::modules::remove_batch(backend, names)
}

/// Resolve a decl position to a raw position using a provider context.
pub fn resolve_position(ctx: &Ctx, pos: &PosOrDecl) -> Pos {
    match crate::pos_or_decl::get_raw_pos_or_decl_reference(pos.clone()) {
        crate::pos_or_decl::RawPosOrDeclReference::Raw(pos) => pos,
        crate::pos_or_decl::RawPosOrDeclReference::DeclRef(decl) => {
            let filename = match &decl {
                DeclReference::Function(name) => get_fun_path(ctx, name),
                DeclReference::Type(name) => get_type_path(ctx, name),
                DeclReference::GlobalConstant(name) => get_const_path(ctx, name),
                DeclReference::Module(name) => get_module_path(ctx, name),
            }
            // TODO: what to do if decl not found?
            .unwrap_or(crate::relative_path::DEFAULT);
            crate::pos_or_decl::fill_in_filename(&filename, pos.clone())
        }
    }
}

/// Resolve the given name & File_info.pos into an actual position
pub fn get_module_full_pos_by_parsing_file(
    ctx: &Ctx,
    (pos, name): (&file_info::Pos, &str),
) -> Option<Pos> {
    match pos {
        file_info::Pos::Full(p) => Some(p.clone()),
        file_info::Pos::File(NameType::Module, fn_) => {
            ast_provider::find_module_in_file(false, ctx, fn_, name).map(|md| md.name.0)
        }
        file_info::Pos::File(
            NameType::Fun | NameType::Class | NameType::Typedef | NameType::Const,
            _fn,
        ) => None,
    }
}

/// Resolve the given name+File_info.pos (which might only have filename) into
/// an actual position, by parsing the AST if necessary
pub fn get_const_full_pos_by_parsing_file(
    ctx: &Ctx,
    (pos, name): (&file_info::Pos, &str),
) -> Option<Pos> {
    match pos {
        file_info::Pos::Full(p) => Some(p.clone()),
        file_info::Pos::File(NameType::Const, fn_) => {
            ast_provider::find_gconst_in_file(false, ctx, fn_, name).map(|ast| ast.name.0)
        }
        file_info::Pos::File(
            NameType::Fun | NameType::Class | NameType::Typedef | NameType::Module,
            _fn,
        ) => None,
    }
}

/// Resolve the given name+File_info.pos (which might only have filename) into
/// an actual position, by parsing the AST if necessary
pub fn get_fun_full_pos_by_parsing_file(
    ctx: &Ctx,
    (pos, name): (&file_info::Pos, &str),
) -> Option<Pos> {
    match pos {
        file_info::Pos::Full(p) => Some(p.clone()),
        file_info::Pos::File(NameType::Fun, fn_) => {
            ast_provider::find_fun_in_file(false, ctx, fn_, name).map(|fd| fd.name.0)
        }
        file_info::Pos::File(
            NameType::Class | NameType::Typedef | NameType::Const | NameType::Module,
            _fn,
        ) => None,
    }
}

/// Resolve the given name+File_info.pos (which might only have filename) into
/// an actual position, by parsing the AST if necessary
pub fn get_type_full_pos_by_parsing_file(
    ctx: &Ctx,
    (pos, name): (&file_info::Pos, &str),
) -> Option<Pos> {
    match pos {
        file_info::Pos::Full(p) => Some(p.clone()),
        file_info::Pos::File(name_type, fn_) => match name_type {
            NameType::Class => {
                ast_provider::find_class_in_file(false, ctx, fn_, name).map(|ast| ast.name.0)
            }
            NameType::Typedef => {
                ast_provider::find_typedef_in_file(false, ctx, fn_, name).map(|ast| ast.name.0)
            }
            NameType::Fun | NameType::Const | NameType::Module => None,
        },
    }
}

/// Updates the reverse naming table based on old+new names in this file
pub fn update(
    backend: &crate::ctx::Ctx,
    path: &RelativePath,
    old_ids: Option<&file_info::Ids>,
    new_ids: Option<&file_info::Ids>,
) {
    if let Some(lm) = backend.local_memory() {
        return local_memory::update(lm, path, old_ids, new_ids);
    }
    let strip_positions = |symbols: &[file_info::Id]| -> Vec<String> {
        symbols.iter().map(|id| id.name.clone()).collect()
    };
    // `Provider_backend.Shared_memory` (see the module doc)
    // Remove old entries
    if let Some(old_ids) = old_ids {
        let file_info::Ids {
            classes,
            typedefs,
            funs,
            consts,
            modules,
        } = old_ids;
        remove_type_batch(backend, &strip_positions(classes));
        remove_type_batch(backend, &strip_positions(typedefs));
        remove_fun_batch(backend, &strip_positions(funs));
        remove_const_batch(backend, &strip_positions(consts));
        remove_module_batch(backend, &strip_positions(modules));
    }
    // Add new entries. Note: the caller is expected to have a solution
    // for duplicate names. Note: can't use [Naming_global.ndecl_file_skip_if_already_bound]
    // because it attempts to look up the symbol by doing a file parse, but
    // we have to use the file_info we're given to avoid races.
    if let Some(new_ids) = new_ids {
        let file_info::Ids {
            classes,
            typedefs,
            funs,
            consts,
            modules,
        } = new_ids;
        for id in funs {
            add_fun(backend, &id.name, &id.pos)
        }
        for id in classes {
            add_class(backend, &id.name, &id.pos)
        }
        for id in typedefs {
            add_typedef(backend, &id.name, &id.pos)
        }
        for id in consts {
            add_const(backend, &id.name, &id.pos)
        }
        for id in modules {
            add_module(backend, &id.name, &id.pos)
        }
    }
}

/// `Naming_heap.push_local_changes`: the stacks of the reverse naming table
/// of the installed context (a lookup that falls back to SQLite caches
/// there; a context without a table, `hh single`'s, has nothing to push).
pub fn local_changes_push_sharedmem_stack() {
    crate::naming_heap::push_local_changes()
}

/// `Naming_heap.pop_local_changes`: see [`local_changes_push_sharedmem_stack`].
pub fn local_changes_pop_sharedmem_stack() {
    crate::naming_heap::pop_local_changes()
}

pub fn get_files(ctx: &Ctx, deps: &crate::typing_deps::dep_set::T) -> crate::relative_path::set::T {
    if ctx.local_memory().is_some() {
        let desc = format!("dephash_lookup_{}", crate::provider_backend::t_to_string(&ctx.get_backend()));
        crate::hh_logger::log(&format!("INVARIANT_VIOLATION_BUG [{}]", desc));
        crate::hack_event_logger::invariant_violation_bug(None, None, None, None, None, &desc);
        panic!("need_update_files");
    }
    // `Provider_backend.Shared_memory` (see the module doc)
    rust_provider_backend::naming::get_filenames_by_hash(ctx, deps)
}

/// The `Provider_backend.Local_memory` branches of this module (the IDE
/// daemon's backend: `crate::provider_backend::LocalMemory`): the reverse
/// naming table is the delta of the backend
/// (`Reverse_naming_table_delta`) over the SQLite naming table of
/// `naming_db_path_ref`, with what a lookup finds in SQLite cached in the
/// delta (`get_and_cache`). A context's entries are looked at first, as in
/// the other branches (`find_symbol_in_context_with_suppression`).
///
/// The functions take a [`View`] (the backend, the entries and the parser
/// options of a context) so that the decl caches of the backend, which have
/// no context of their own, can ask them on a miss (`crate::ctx`).
pub mod local_memory {
    use super::*;
    use crate::naming_sqlite;
    use crate::provider_backend::LocalMemory;
    use crate::provider_backend::reverse_naming_table_delta::Map;
    use crate::provider_backend::reverse_naming_table_delta::Pos as DeltaPos;
    use crate::provider_backend::reverse_naming_table_delta::PosOrDeleted;

    /// What the `Local_memory` branches read of a context.
    #[derive(Clone, Copy)]
    pub struct View<'a> {
        pub local_memory: &'a LocalMemory,
        pub entries: &'a provider_context::Entries,
        pub popt: &'a oxidized::parser_options::ParserOptions,
    }

    impl<'a> View<'a> {
        pub fn of_ctx(ctx: &'a crate::ctx::Ctx, local_memory: &'a LocalMemory) -> Self {
            View {
                local_memory,
                entries: &ctx.entries,
                popt: &ctx.parser_env.parser_options,
            }
        }
    }

    /// An exception of `Naming_sqlite` that the OCaml lets through.
    fn raise<A>(result: naming_sqlite::Result<A>) -> A {
        match result {
            Ok(a) => a,
            Err(e) => std::panic::panic_any(e),
        }
    }

    /// `db_path_of_ctx` (`Db_path_provider.get_naming_db_path` of the
    /// backend: `!naming_db_path_ref`).
    pub fn db_path(local_memory: &LocalMemory) -> Option<naming_sqlite::DbPath> {
        local_memory.naming_db_path_ref.lock().unwrap().clone()
    }

    fn find_symbol_in_view(
        v: &View<'_>,
        get_entry_symbols: impl Fn(&file_info::Ids) -> Vec<(file_info::Id, NameType)>,
        is_symbol: impl Fn(&str) -> bool,
    ) -> FoundSymbol {
        find_symbol_in_entries(v.entries, v.popt, get_entry_symbols, is_symbol)
    }

    fn is_pos_in_view(v: &View<'_>, pos: &file_info::Pos) -> bool {
        v.entries.contains_key(&get_pos_filename(pos))
    }

    /// `find_symbol_in_context_with_suppression`
    fn find_symbol_in_context_with_suppression(
        v: &View<'_>,
        from_context: FoundSymbol,
        fallback: impl FnOnce() -> FoundSymbol,
    ) -> FoundSymbol {
        let from_fallback = fallback();
        match (from_context, from_fallback) {
            (None, None) => None,
            (Some((context_pos, context_name_type)), None) => Some((context_pos, context_name_type)),
            (None, Some((fallback_pos, fallback_name_type))) => {
                // If fallback said it thought the symbol was in ctx, but we definitively
                // know that it isn't, then the answer is None.
                if is_pos_in_view(v, &fallback_pos) {
                    None
                } else {
                    Some((fallback_pos, fallback_name_type))
                }
            }
            (Some((context_pos, context_name_type)), Some((fallback_pos, fallback_name_type))) => {
                // The alphabetically first filename wins
                let context_fn = get_pos_filename(&context_pos);
                let fallback_fn = get_pos_filename(&fallback_pos);
                if crate::relative_path::compare(&context_fn, &fallback_fn) != std::cmp::Ordering::Greater {
                    // symbol is either (1) a duplicate in both context and fallback, and context is the winner,
                    // or (2) not a duplicate, and both context and fallback claim it to be defined
                    // in a file that's part of the context, in which case context wins.
                    // This is consistent with the winnor algorithm used by hh_server --
                    // see the comment for [ServerTypeCheck.do_naming].
                    Some((context_pos, context_name_type))
                } else {
                    // symbol is a duplicate in both context and fallback, and fallback is the winner
                    Some((fallback_pos, fallback_name_type))
                }
            }
        }
    }

    /// `get_and_cache ~ctx ~name ~cache ~fallback`
    fn get_and_cache(
        v: &View<'_>,
        name: &str,
        cache: &Map,
        fallback: impl FnOnce(&naming_sqlite::DbPath) -> Option<DeltaPos>,
    ) -> Option<DeltaPos> {
        match cache.lock().unwrap().get(name) {
            Some(PosOrDeleted::Deleted) => return None,
            Some(PosOrDeleted::Pos((name_type, path), _rest)) => return Some((*name_type, path.clone())),
            None => {}
        }
        match db_path(v.local_memory).and_then(|db_path| fallback(&db_path)) {
            None => None,
            Some((name_type, path)) => {
                cache
                    .lock()
                    .unwrap()
                    .insert(name.to_string(), PosOrDeleted::Pos((name_type, path.clone()), vec![]));
                Some((name_type, path))
            }
        }
    }

    /// The `Local_memory` branch of [`super::get_const_pos`].
    pub fn get_const_pos(v: &View<'_>, name: &str) -> Option<file_info::Pos> {
        let from_context = find_symbol_in_view(
            v,
            |ids| ids.consts.iter().map(|id| attach_name_type(NameType::Const, id.clone())).collect(),
            |s| name == s,
        );
        find_symbol_in_context_with_suppression(v, from_context, || {
            get_and_cache(v, name, &v.local_memory.reverse_naming_table_delta.consts, |db_path| {
                raise(naming_sqlite::get_const_path_by_name(db_path, name)).map(|path| (NameType::Const, path))
            })
            .map(attach_name_type_to_tuple)
        })
        .map(remove_name_type)
    }

    /// The `Local_memory` branch of [`super::get_fun_pos`].
    pub fn get_fun_pos(v: &View<'_>, name: &str) -> Option<file_info::Pos> {
        let from_context = find_symbol_in_view(
            v,
            |ids| ids.funs.iter().map(|id| attach_name_type(NameType::Fun, id.clone())).collect(),
            |s| name == s,
        );
        find_symbol_in_context_with_suppression(v, from_context, || {
            get_and_cache(v, name, &v.local_memory.reverse_naming_table_delta.funs, |db_path| {
                raise(naming_sqlite::get_fun_path_by_name(db_path, name)).map(|path| (NameType::Fun, path))
            })
            .map(attach_name_type_to_tuple)
        })
        .map(remove_name_type)
    }

    /// The `Local_memory` branch of [`super::get_type_pos_and_kind`].
    pub fn get_type_pos_and_kind(v: &View<'_>, name: &str) -> Option<(file_info::Pos, KindOfType)> {
        let from_context = find_symbol_in_view(v, get_entry_symbols_for_type, |s| name == s);
        find_symbol_in_context_with_suppression(v, from_context, || {
            get_and_cache(v, name, &v.local_memory.reverse_naming_table_delta.types, |db_path| {
                raise(naming_sqlite::get_type_path_by_name(db_path, name))
                    .map(|(path, kind)| (kind_to_name_type(kind), path))
            })
            .map(|(name_type, path)| (file_info::Pos::File(name_type, Arc::new(path)), name_type))
        })
        .map(|(pos, name_type)| (pos, name_type_to_kind(name_type)))
    }

    pub fn get_module_pos(v: &View<'_>, name: &str) -> Option<file_info::Pos> {
        let from_context = find_symbol_in_view(
            v,
            |ids| ids.modules.iter().map(|id| attach_name_type(NameType::Module, id.clone())).collect(),
            |s| name == s,
        );
        find_symbol_in_context_with_suppression(v, from_context, || {
            get_and_cache(v, name, &v.local_memory.reverse_naming_table_delta.modules, |db_path| {
                raise(naming_sqlite::get_module_path_by_name(db_path, name)).map(|path| (NameType::Module, path))
            })
            .map(attach_name_type_to_tuple)
        })
        .map(remove_name_type)
    }

    /// `get_fun_canon_name`. `name` is lowercased by the caller.
    pub fn get_fun_canon_name(ctx: &Ctx, local_memory: &LocalMemory, name: &str) -> Option<String> {
        let v = View::of_ctx(ctx, local_memory);
        let (_name_type, path) = get_and_cache(
            &v,
            name,
            &local_memory.reverse_naming_table_delta.funs_canon_key,
            |db_path| raise(naming_sqlite::get_ifun_path_by_name(db_path, name)).map(|path| (NameType::Fun, path)),
        )?;
        // If reverse_naming_table_delta thought the symbol was in ctx, but we definitively
        // know that it isn't, then it isn't.
        if is_path_in_ctx(ctx, &path) {
            None
        } else {
            compute_fun_canon_name(ctx, &path, name)
        }
    }

    /// `get_type_canon_name`. `name` is lowercased by the caller.
    pub fn get_type_canon_name(ctx: &Ctx, local_memory: &LocalMemory, name: &str) -> Option<String> {
        let v = View::of_ctx(ctx, local_memory);
        let (name_type, path) = get_and_cache(
            &v,
            name,
            &local_memory.reverse_naming_table_delta.types_canon_key,
            |db_path| {
                raise(naming_sqlite::get_itype_path_by_name(db_path, name))
                    .map(|(path, kind)| (kind_to_name_type(kind), path))
            },
        )?;
        // If reverse_naming_table_delta thought the symbol was in ctx, but we definitively
        // know that it isn't, then it isn't.
        if is_path_in_ctx(ctx, &path) {
            None
        } else {
            compute_type_canon_name(ctx, &path, name_type_to_kind(name_type), name)
        }
    }

    fn insert(map: &Map, name: String, data: PosOrDeleted) {
        map.lock().unwrap().insert(name, data);
    }

    /// The `Local_memory` branch of [`super::add_const`].
    pub fn add_const(local_memory: &LocalMemory, name: &str, pos: &file_info::Pos) {
        let data = PosOrDeleted::Pos((NameType::Const, get_pos_filename(pos)), vec![]);
        insert(&local_memory.reverse_naming_table_delta.consts, name.to_string(), data)
    }

    /// The `Local_memory` branch of [`super::remove_const_batch`].
    pub fn remove_const_batch(local_memory: &LocalMemory, names: &[String]) {
        let mut map = local_memory.reverse_naming_table_delta.consts.lock().unwrap();
        for name in names {
            map.insert(name.clone(), PosOrDeleted::Deleted);
        }
    }

    /// The `Local_memory` branch of [`super::add_fun`].
    pub fn add_fun(local_memory: &LocalMemory, name: &str, pos: &file_info::Pos) {
        let delta = &local_memory.reverse_naming_table_delta;
        let data = PosOrDeleted::Pos((NameType::Fun, get_pos_filename(pos)), vec![]);
        insert(&delta.funs, name.to_string(), data.clone());
        insert(&delta.funs_canon_key, naming_sqlite_to_canon_name_key(name), data);
    }

    /// The `Local_memory` branch of [`super::remove_fun_batch`].
    pub fn remove_fun_batch(local_memory: &LocalMemory, names: &[String]) {
        let delta = &local_memory.reverse_naming_table_delta;
        {
            let mut map = delta.funs.lock().unwrap();
            for name in names {
                map.insert(name.clone(), PosOrDeleted::Deleted);
            }
        }
        let mut map = delta.funs_canon_key.lock().unwrap();
        for name in names {
            map.insert(naming_sqlite_to_canon_name_key(name), PosOrDeleted::Deleted);
        }
    }

    /// The `Local_memory` branch of [`super::add_type`].
    pub fn add_type(local_memory: &LocalMemory, name: &str, pos: &file_info::Pos, kind: KindOfType) {
        let delta = &local_memory.reverse_naming_table_delta;
        let data = PosOrDeleted::Pos((kind_to_name_type(kind), get_pos_filename(pos)), vec![]);
        insert(&delta.types, name.to_string(), data.clone());
        insert(&delta.types_canon_key, naming_sqlite_to_canon_name_key(name), data);
    }

    /// The `Local_memory` branch of [`super::remove_type_batch`].
    pub fn remove_type_batch(local_memory: &LocalMemory, names: &[String]) {
        let delta = &local_memory.reverse_naming_table_delta;
        {
            let mut map = delta.types.lock().unwrap();
            for name in names {
                map.insert(name.clone(), PosOrDeleted::Deleted);
            }
        }
        let mut map = delta.types_canon_key.lock().unwrap();
        for name in names {
            map.insert(naming_sqlite_to_canon_name_key(name), PosOrDeleted::Deleted);
        }
    }

    pub fn add_module(local_memory: &LocalMemory, name: &str, pos: &file_info::Pos) {
        let data = PosOrDeleted::Pos((NameType::Module, get_pos_filename(pos)), vec![]);
        insert(&local_memory.reverse_naming_table_delta.modules, name.to_string(), data)
    }

    pub fn remove_module_batch(local_memory: &LocalMemory, names: &[String]) {
        let mut map = local_memory.reverse_naming_table_delta.modules.lock().unwrap();
        for name in names {
            map.insert(name.clone(), PosOrDeleted::Deleted);
        }
    }

    /// `Relative_path.to_absolute`, for the messages of [`remove`].
    fn to_absolute(path: &RelativePath) -> String {
        crate::relative_path::to_absolute(path)
    }

    /// This removes the name->path mapping from the naming table (i.e. the combination
    /// of sqlite and delta). It is an error to call this method unless name->path exists.
    /// We enforce this with exceptions in some cases where it's cheap enough to verify,
    /// but not in others where enforcing it would involve a sqlite read.
    /// Invariant: this never transitions an entry from Some to None.
    fn remove(
        case_insensitive: bool,
        delta: &mut std::collections::BTreeMap<String, PosOrDeleted>,
        path: &RelativePath,
        name: &str,
    ) {
        let name = if case_insensitive {
            naming_sqlite_to_canon_name_key(name)
        } else {
            name.to_string()
        };
        match delta.get(&name) {
            None => {
                // We've never yet read/cached from sqlite. Presumably the caller is removing
                // the name->path mapping that we assume is present in sqlite. We could read
                // from sqlite right now solely to verify that the user-supplied path matches
                // the one that's in sqlite, but that'd be costly and doesn't seem worth it.
                delta.insert(name, PosOrDeleted::Deleted);
            }
            Some(PosOrDeleted::Deleted) => panic!("removing symbol that's already removed"),
            Some(PosOrDeleted::Pos((_name_type, old_path), rest)) if rest.is_empty() => {
                if !crate::relative_path::equal(path, old_path) {
                    panic!(
                        "Naming_provider invariant failed: symbol {} was in {}, but we're trying to remove {}",
                        name,
                        to_absolute(old_path),
                        to_absolute(path)
                    )
                }
                delta.insert(name, PosOrDeleted::Deleted);
            }
            Some(PosOrDeleted::Pos((name_type, old_path), rest)) => {
                let (name_type, old_path, rest) = (*name_type, old_path.clone(), rest.clone());
                if crate::relative_path::equal(path, &old_path) {
                    let mut rest = rest.into_iter();
                    let rest_hd = rest.next().unwrap();
                    delta.insert(name, PosOrDeleted::Pos(rest_hd, rest.collect()));
                } else {
                    let rest_tl_len = rest.len() - 1;
                    let rest: Vec<DeltaPos> = rest
                        .into_iter()
                        .filter(|(_name_type, rest_path)| !crate::relative_path::equal(path, rest_path))
                        .collect();
                    if rest.len() != rest_tl_len {
                        panic!(
                            "Naming_provider invariant failed: symbol {} was in several files, but we're trying to remove {} which isn't one of them",
                            name,
                            to_absolute(path)
                        )
                    }
                    delta.insert(name, PosOrDeleted::Pos((name_type, old_path), rest));
                }
            }
        }
    }

    /// This adds name->path to the naming table (i.e. the combination of sqlite+delta).
    /// Invariant: if this function causes the delta for this symbol to go from None->Some,
    /// then the result will include the name->path mapping that was present in sqlite (if any),
    /// in addition to the name->path mapping that we wish to add right now.
    fn add(
        case_insensitive: bool,
        db_path: Option<&naming_sqlite::DbPath>,
        delta: &mut std::collections::BTreeMap<String, PosOrDeleted>,
        pos: DeltaPos,
        name: &str,
    ) {
        let name = if case_insensitive {
            naming_sqlite_to_canon_name_key(name)
        } else {
            name.to_string()
        };
        match (delta.get(&name), db_path) {
            (None, None) => {
                delta.insert(name, PosOrDeleted::Pos(pos, vec![]));
            }
            (None, Some(db_path)) => {
                let (name_type, _) = &pos;
                let sqlite_pos = match name_type {
                    NameType::Const => raise(naming_sqlite::get_const_path_by_name(db_path, &name))
                        .map(|sqlite_path| (NameType::Const, sqlite_path)),
                    NameType::Fun => {
                        let pos = if case_insensitive {
                            raise(naming_sqlite::get_ifun_path_by_name(db_path, &name))
                        } else {
                            raise(naming_sqlite::get_fun_path_by_name(db_path, &name))
                        };
                        pos.map(|sqlite_path| (NameType::Fun, sqlite_path))
                    }
                    NameType::Module => raise(naming_sqlite::get_module_path_by_name(db_path, &name))
                        .map(|sqlite_path| (NameType::Module, sqlite_path)),
                    NameType::Class | NameType::Typedef => {
                        let pos = if case_insensitive {
                            raise(naming_sqlite::get_itype_path_by_name(db_path, &name))
                        } else {
                            raise(naming_sqlite::get_type_path_by_name(db_path, &name))
                        };
                        pos.map(|(sqlite_path, sqlite_kind)| (kind_to_name_type(sqlite_kind), sqlite_path))
                    }
                };
                let data = match sqlite_pos {
                    None => PosOrDeleted::Pos(pos, vec![]),
                    Some(sqlite_pos) => PosOrDeleted::Pos(sqlite_pos, vec![pos]),
                };
                delta.insert(name, data);
            }
            (Some(PosOrDeleted::Deleted), _) => {
                delta.insert(name, PosOrDeleted::Pos(pos, vec![]));
            }
            (Some(PosOrDeleted::Pos(old_pos, rest)), _) => {
                let mut new_rest = vec![pos];
                new_rest.extend(rest.iter().cloned());
                let old_pos = old_pos.clone();
                delta.insert(name, PosOrDeleted::Pos(old_pos, new_rest));
            }
        }
    }

    /// `update ~backend:(Local_memory ..) ~path ~old_ids ~new_ids`
    pub fn update(
        local_memory: &LocalMemory,
        path: &RelativePath,
        old_ids: Option<&file_info::Ids>,
        new_ids: Option<&file_info::Ids>,
    ) {
        let strip_positions =
            |symbols: &[file_info::Id]| -> Vec<String> { symbols.iter().map(|id| id.name.clone()).collect() };
        let naming_db_path = db_path(local_memory);
        // helper
        let update = |case_insensitive: bool,
                      olds: &[file_info::Id],
                      news: &[file_info::Id],
                      delta: &Map,
                      name_type: NameType| {
            // The following code has a bug.
            // Given "olds/news", it calculates "added/removed" based on case-sensitive comparison.
            // That's straightforwardly correct for our case-sensitives maps.
            // But how does it work for our case-insensitive maps? e.g. olds={Aa,aA}, news={aa}.
            // Therefore added={aa}, removed={Aa,aA} because we calculated these case-sensitively.
            // (1) it removes the lowercase version of "Aa"
            // (2) it removes the lowercase version of "aA"  <-- failwith
            // (3) it adds the lowercase version of "aa"
            // Correctness requires that removal is idempotent, and that we do adds
            // after removes. Unfortunately removal currently isn't idempotent;
            // if fails if you try to remove the same thing twice.
            let olds_s: std::collections::BTreeSet<String> = strip_positions(olds).into_iter().collect();
            let news_s: std::collections::BTreeSet<String> = strip_positions(news).into_iter().collect();
            let removed: Vec<&String> = olds_s.difference(&news_s).collect();
            let added: Vec<&String> = news_s.difference(&olds_s).collect();
            for name in removed {
                let mut d = delta.lock().unwrap();
                remove(case_insensitive, &mut d, path, name);
            }
            for name in added {
                let mut d = delta.lock().unwrap();
                add(case_insensitive, naming_db_path.as_ref(), &mut d, (name_type, path.clone()), name);
            }
        };
        // do the update
        let empty = crate::file_info::empty_ids();
        let oldfi = old_ids.unwrap_or(&empty);
        let newfi = new_ids.unwrap_or(&empty);
        let deltas = &local_memory.reverse_naming_table_delta;
        update(false, &oldfi.funs, &newfi.funs, &deltas.funs, NameType::Fun);
        update(false, &oldfi.consts, &newfi.consts, &deltas.consts, NameType::Const);
        update(false, &oldfi.classes, &newfi.classes, &deltas.types, NameType::Class);
        update(false, &oldfi.typedefs, &newfi.typedefs, &deltas.types, NameType::Typedef);
        update(false, &oldfi.modules, &newfi.modules, &deltas.modules, NameType::Module);
        // update canon names too
        update(true, &oldfi.funs, &newfi.funs, &deltas.funs_canon_key, NameType::Fun);
        update(true, &oldfi.classes, &newfi.classes, &deltas.types_canon_key, NameType::Class);
        update(true, &oldfi.typedefs, &newfi.typedefs, &deltas.types_canon_key, NameType::Typedef);
    }
}

/// The lookups and changes of the `Shared_memory` branches, in the shape of
/// the part of `Rust_provider_backend` (`providers/rust_provider_backend.ml`)
/// that `Naming_provider` calls (see the module doc).
///
/// The fallback is the daemon's reverse naming table when the `Ctx` has one
/// (`Naming_heap`); otherwise the declarations of the context: the path of a
/// name is the file of its declaration, and when a class and a typedef have
/// the same name, the name is that of the class (as for hackrs's
/// `EagerShallowDeclProvider::get_type_kind`, which class folding goes by,
/// and `crate::decl_provider`). The positions it gives are
/// `File_info.File (name_type, path)`, as those of the OCaml backend.
///
/// The OCaml gives the backend a proxy of the entries of the context
/// (`with_ctx_proxy_opt`), through which it sees the files open in an editor
/// (a context without entries has none). What the backend does with it is
/// that of hh_server's Rust backend, `NamingTableWithContext` in
/// `providers/hackrs_provider_backend/hackrs_provider_backend.rs` (git
/// HEAD): [`naming_table_with_context`], whose fallback, the naming table, is
/// the decl stores here.
pub mod rust_provider_backend {
    use std::cell::Cell;

    use super::*;

    /// `find_symbol_fn`
    pub type FindSymbolFn = Box<dyn Fn(&str) -> FoundSymbol>;

    /// `ctx_proxy`
    pub struct CtxProxy {
        pub get_entry_contents: Box<dyn Fn(&RelativePath) -> Option<BString>>,
        pub is_pos_in_ctx: Box<dyn Fn(&file_info::Pos) -> bool>,
        pub find_fun_canon_name_in_context: Box<dyn Fn(&str) -> Option<String>>,
        pub find_type_canon_name_in_context: Box<dyn Fn(&str) -> Option<String>>,
        pub find_const_in_context: FindSymbolFn,
        pub find_fun_in_context: FindSymbolFn,
        pub find_type_in_context: FindSymbolFn,
        pub find_module_in_context: FindSymbolFn,
    }

    thread_local! {
        /// `Option.is_some !ctx_proxy_ref` (a global `ref` of the OCaml
        /// process; the lookups of a thread are its own).
        static CTX_PROXY_SET: Cell<bool> = const { Cell::new(false) };
    }

    /// Whether this thread is inside [`with_ctx_proxy_opt`] with a proxy:
    /// a naming lookup of a context with entries is in progress. (The local
    /// changes of such a context, `crate::provider_context`,
    /// do not parse a file for a lookup that the naming table makes, as the
    /// OCaml's naming heap does not.)
    pub fn is_ctx_proxy_set() -> bool {
        CTX_PROXY_SET.with(Cell::get)
    }

    /// `ctx_proxy_ref := None` when [`with_ctx_proxy_opt`] returns or raises.
    struct ResetCtxProxy;

    impl Drop for ResetCtxProxy {
        fn drop(&mut self) {
            CTX_PROXY_SET.with(|set| set.set(false));
        }
    }

    /// `with_ctx_proxy_opt t ctx f`: `ctx_proxy_ref := ctx` and
    /// `set_ctx_empty t (Option.is_none ctx)` while `f` runs, then
    /// `ctx_proxy_ref := None` and `set_ctx_empty t true`, whether `f`
    /// returns or raises. The proxy (`None` when the context is empty) is
    /// what `f` is given.
    fn with_ctx_proxy_opt<A>(ctx: Option<CtxProxy>, f: impl FnOnce(Option<&CtxProxy>) -> A) -> A {
        assert!(
            !CTX_PROXY_SET.with(Cell::get),
            "Assert_failure providers/rust_provider_backend.ml"
        );
        CTX_PROXY_SET.with(|set| set.set(ctx.is_some()));
        let _reset = ResetCtxProxy;
        f(ctx.as_ref())
    }

    /// `NamingTableWithContext` of `hackrs_provider_backend.rs`: the naming
    /// queries of the Rust backend, which look at the entries of the context
    /// (through the proxy, when there is one) before its naming table
    /// (`fallback`).
    mod naming_table_with_context {
        use super::*;

        /// `find_symbol_in_context_with_suppression`
        pub fn find_symbol_in_context_with_suppression(
            ctx: Option<&CtxProxy>,
            find_symbol_in_context: impl FnOnce(&CtxProxy) -> FoundSymbol,
            fallback: impl FnOnce() -> FoundSymbol,
        ) -> FoundSymbol {
            match ctx {
                // `if self.ctx_is_empty()`
                None => fallback(),
                Some(ctx) => {
                    let ctx_pos_opt = find_symbol_in_context(ctx);
                    let fallback_pos_opt = fallback();
                    match (ctx_pos_opt, fallback_pos_opt) {
                        (None, None) => None,
                        (Some(ctx_pos), None) => Some(ctx_pos),
                        (None, Some((pos, name_type))) => {
                            if (ctx.is_pos_in_ctx)(&pos) {
                                // If fallback said it thought the symbol was in ctx, but we definitively
                                // know that it isn't, then the answer is None.
                                None
                            } else {
                                Some((pos, name_type))
                            }
                        }
                        (
                            Some((ctx_pos, ctx_name_type)),
                            Some((fallback_pos, fallback_name_type)),
                        ) => {
                            // The alphabetically first filename wins
                            let ctx_fn = ctx_pos.path();
                            let fallback_fn = fallback_pos.path();
                            if crate::relative_path::compare(ctx_fn, fallback_fn)
                                != std::cmp::Ordering::Greater
                            {
                                // symbol is either (1) a duplicate in both context and fallback, and context is the winner,
                                // or (2) not a duplicate, and both context and fallback claim it to be defined
                                // in a file that's part of the context, in which case context wins.
                                Some((ctx_pos, ctx_name_type))
                            } else {
                                // symbol is a duplicate in both context and fallback, and fallback is the winner
                                Some((fallback_pos, fallback_name_type))
                            }
                        }
                    }
                }
            }
        }

        /// `get_canon_type_name` / `get_canon_fun_name`: the name in the
        /// entries of the context, if there are entries and it is there, else
        /// the fallback's.
        pub fn get_canon_name(
            ctx: Option<&CtxProxy>,
            find_canon_name_in_context: impl FnOnce(&CtxProxy) -> Option<String>,
            fallback: impl FnOnce() -> Option<String>,
        ) -> Option<String> {
            if let Some(ctx) = ctx {
                if let name_opt @ Some(..) = find_canon_name_in_context(ctx) {
                    return name_opt;
                }
            }
            fallback()
        }
    }

    /// What a decl store answered: the stores of a `Ctx` do not fail; a read
    /// of a shared-memory heap raises when it does.
    fn store_result<A, E: std::fmt::Display>(what: &str, name: &str, result: Result<A, E>) -> A {
        match result {
            Ok(x) => x,
            Err(err) => panic!("the naming table of the context: {} {}: {}", what, name, err),
        }
    }

    pub mod naming {
        use pos::ConstName;
        use pos::FunName;
        use pos::ModuleName;
        use pos::TypeName;

        use super::*;

        pub mod types {
            use super::*;

            /// `naming_provider().get_type_path_and_kind name`
            fn get_type_path_and_kind(
                backend: &Ctx,
                name: &str,
            ) -> Option<(RelativePath, KindOfType)> {
                let type_name = TypeName(crate::ctx::symbol(name));
                match store_result(
                    "Types.get_pos",
                    name,
                    backend.shallow_decls.get_class(type_name),
                ) {
                    Some(decl) => Some((decl.name.pos().file().into(), KindOfType::TClass)),
                    None => store_result(
                        "Types.get_pos",
                        name,
                        backend.shallow_decls.get_typedef(type_name),
                    )
                    .map(|decl| (decl.pos.file().into(), KindOfType::TTypedef)),
                }
            }

            /// `with_ctx_proxy_opt t ctx @@ fun () -> get_pos t name`: the
            /// backend's `get_type_pos` (`NamingTableWithContext`).
            pub fn get_pos(
                backend: &Ctx,
                ctx: Option<CtxProxy>,
                name: &str,
            ) -> Option<(file_info::Pos, KindOfType)> {
                with_ctx_proxy_opt(ctx, |ctx| {
                    naming_table_with_context::find_symbol_in_context_with_suppression(
                        ctx,
                        |ctx| (ctx.find_type_in_context)(name),
                        || match backend.reverse_naming_table_opt() {
                            Some(table) => table
                                .get_type_pos(name)
                                .map(|(pos, kind)| (pos.to_file_info(), kind_to_name_type(kind))),
                            None => get_type_path_and_kind(backend, name).map(|(path, kind)| {
                                (
                                    file_info::Pos::File(kind_to_name_type(kind), Arc::new(path)),
                                    kind_to_name_type(kind),
                                )
                            }),
                        },
                    )
                    .map(|(pos, name_type)| (pos, KindOfType::try_from(name_type).unwrap()))
                })
            }

            /// The kind of [`get_pos`]. Without a proxy, `get_pos` is the
            /// lookup of [`get_type_path_and_kind`], whose path is not needed
            /// here.
            pub fn get_kind(
                backend: &Ctx,
                ctx: Option<CtxProxy>,
                name: &str,
            ) -> Option<KindOfType> {
                match ctx {
                    None => with_ctx_proxy_opt(None, |_| get_type_kind(backend, name)),
                    Some(_) => get_pos(backend, ctx, name).map(|(_pos, kind)| kind),
                }
            }

            /// Whether `name` is a typedef declared in `file`: the comparison
            /// of [`super::super::get_typedef_path`]'s answer with `file`.
            /// Without a proxy, `get_pos` is the lookup of
            /// [`get_type_path_and_kind`], whose path is compared without
            /// building the `RelativePath` it would return.
            pub fn typedef_path_is(
                backend: &Ctx,
                ctx: Option<CtxProxy>,
                name: &str,
                file: &RelativePath,
            ) -> bool {
                match ctx {
                    None => with_ctx_proxy_opt(None, |_| match get_type_kind_and_file(backend, name) {
                        Some((KindOfType::TTypedef, path)) => {
                            path.prefix() == file.prefix()
                                && paths_equal(path.path(), file.path())
                        }
                        Some((KindOfType::TClass, _)) | None => false,
                    }),
                    Some(_) => match get_pos(backend, ctx, name) {
                        Some((pos, KindOfType::TTypedef)) => get_pos_filename(&pos) == *file,
                        Some((_, KindOfType::TClass)) | None => false,
                    },
                }
            }

            /// `p1 == p2` (`Path`s are equal when their components are):
            /// two paths whose components are their `/`-separated parts
            /// (no empty part, no `.` part, no `/` at the end) have the same
            /// components only if they are the same bytes, so only other
            /// paths are compared by their components, which is slow.
            fn paths_equal(p1: &std::path::Path, p2: &std::path::Path) -> bool {
                fn is_plain(p: &[u8]) -> bool {
                    !p.is_empty()
                        && !p.ends_with(b"/")
                        && !p.ends_with(b"/.")
                        && !p.starts_with(b"./")
                        && p != b"."
                        && !p.windows(2).any(|w| w == b"//")
                        && !p.windows(3).any(|w| w == b"/./")
                }
                use std::os::unix::ffi::OsStrExt;
                let (b1, b2) = (p1.as_os_str().as_bytes(), p2.as_os_str().as_bytes());
                b1 == b2 || (!(is_plain(b1) && is_plain(b2)) && p1 == p2)
            }

            type Kinds = (
                std::sync::Weak<shallow_decl_provider::ShallowDeclStore<crate::ctx::R>>,
                hash::HashMap<String, (KindOfType, pos::RelativePath)>,
            );

            thread_local! {
                /// The memo of [`get_type_kind_and_file`].
                static KINDS: std::cell::RefCell<Kinds> =
                    std::cell::RefCell::new((std::sync::Weak::new(), hash::HashMap::default()));
            }

            /// Forget the memo of [`get_type_kind_and_file`] (the store may
            /// have changed in place: see `crate::rt::decl_epoch`).
            pub(crate) fn forget_thread_memos() {
                KINDS.with_borrow_mut(|(of_store, kinds)| {
                    *of_store = std::sync::Weak::new();
                    *kinds = hash::HashMap::default();
                })
            }

            /// [`get_type_path_and_kind`] without the path.
            fn get_type_kind(backend: &Ctx, name: &str) -> Option<KindOfType> {
                get_type_kind_and_file(backend, name).map(|(kind, _)| kind)
            }

            /// [`get_type_path_and_kind`], with the path as the decl
            /// store has it.
            ///
            /// The answers found are kept per thread, for the decl store
            /// they come from: a store never changes what it has found (a
            /// name it does not have is looked up again). Looking a name up
            /// in the store copies the `Arc` of its declaration, whose
            /// reference count every thread writes.
            fn get_type_kind_and_file(
                backend: &Ctx,
                name: &str,
            ) -> Option<(KindOfType, pos::RelativePath)> {
                // The daemon's reverse naming table, when there is one.
                if let Some(table) = backend.reverse_naming_table_opt() {
                    return table.get_type_pos(name).map(|(pos, kind)| (kind, pos.path()));
                }
                let store = Arc::as_ptr(&backend.shallow_decls);
                if let Some(found) = KINDS.with_borrow_mut(|(of_store, kinds)| {
                    if !std::ptr::eq(of_store.as_ptr(), store) {
                        kinds.clear();
                        *of_store = Arc::downgrade(&backend.shallow_decls);
                    }
                    kinds.get(name).copied()
                }) {
                    return Some(found);
                }
                let found = get_type_kind_uncached(backend, name);
                if let Some(found) = found {
                    KINDS.with_borrow_mut(|(_, kinds)| {
                        if kinds.len() >= 1 << 16 {
                            kinds.clear()
                        }
                        kinds.insert(name.to_string(), found)
                    });
                }
                found
            }

            /// The lookup of [`get_type_path_and_kind`], with the path of the
            /// store.
            fn get_type_kind_uncached(
                backend: &Ctx,
                name: &str,
            ) -> Option<(KindOfType, pos::RelativePath)> {
                let type_name = TypeName(crate::ctx::symbol(name));
                match store_result(
                    "Types.get_pos",
                    name,
                    backend.shallow_decls.get_class(type_name),
                ) {
                    Some(decl) => Some((KindOfType::TClass, decl.name.pos().file())),
                    None => store_result(
                        "Types.get_pos",
                        name,
                        backend.shallow_decls.get_typedef(type_name),
                    )
                    .map(|decl| (KindOfType::TTypedef, decl.pos.file())),
                }
            }

            /// The SQLite fallback of `Naming_heap.Types.get_canon_name ctx
            /// id` (`get_and_cache` of `TypeCanonHeap`, when the table has
            /// a database): the file the database binds the name to (up
            /// to case), parsed for the declared spelling, which is cached.
            pub(crate) fn canon_fallback(backend: &Ctx, id: &str) -> Option<String> {
                let (path, kind) = backend.naming_types_canon_fallback(id)?;
                let found = match kind {
                    KindOfType::TClass => ast_provider::find_iclass_in_file(backend, &path, id).map(|cls| cls.name.1),
                    KindOfType::TTypedef => {
                        ast_provider::find_itypedef_in_file(backend, &path, id).map(|typedef| typedef.name.1)
                    }
                };
                match found {
                    Some(canonical_name) => {
                        backend.naming_types_cache_canon_name(id, &canonical_name, &path, kind);
                        Some(canonical_name)
                    }
                    None => {
                        crate::hh_logger::log(&format!(
                            "Failed to get canonical name for {} in file {}",
                            id,
                            crate::relative_path::storage_to_string(&path)
                        ));
                        None
                    }
                }
            }

            /// `add` (`hh_rust_provider_backend_naming_types_add`)
            pub fn add(backend: &crate::ctx::Ctx, name: &str, (pos, kind): (&file_info::Pos, KindOfType)) {
                backend.naming_types_add(name, pos, kind)
            }

            /// `remove_batch` (`hh_rust_provider_backend_naming_types_remove_batch`)
            pub fn remove_batch(backend: &crate::ctx::Ctx, names: &[String]) {
                backend.naming_types_remove_batch(names)
            }

            /// `with_ctx_proxy_opt t ctx @@ fun () -> get_canon_name t name`
            pub fn get_canon_name(
                backend: &Ctx,
                ctx: Option<CtxProxy>,
                name: &str,
            ) -> Option<String> {
                with_ctx_proxy_opt(ctx, |ctx| {
                    naming_table_with_context::get_canon_name(
                        ctx,
                        |ctx| (ctx.find_type_canon_name_in_context)(name),
                        || {
                            backend
                                .get_type_canon_name(name)
                                .map(|name| name.as_str().to_string())
                                .or_else(|| canon_fallback(backend, name))
                        },
                    )
                })
            }
        }

        pub mod funs {
            use super::*;

            /// The SQLite fallback of `Naming_heap.Funs.get_canon_name ctx
            /// name` (see `types::canon_fallback`).
            pub(crate) fn canon_fallback(backend: &Ctx, name: &str) -> Option<String> {
                let path = backend.naming_funs_canon_fallback(name)?;
                match ast_provider::find_ifun_in_file(backend, &path, name) {
                    Some(f) => {
                        let canonical_name = f.name.1;
                        backend.naming_funs_cache_canon_name(name, &canonical_name, &path);
                        Some(canonical_name)
                    }
                    None => {
                        crate::hh_logger::log(&format!(
                            "Failed to get canonical name for {} in file {}",
                            name,
                            crate::relative_path::storage_to_string(&path)
                        ));
                        None
                    }
                }
            }

            /// `add` (`hh_rust_provider_backend_naming_funs_add`)
            pub fn add(backend: &crate::ctx::Ctx, name: &str, pos: &file_info::Pos) {
                backend.naming_funs_add(name, pos)
            }

            /// `remove_batch` (`hh_rust_provider_backend_naming_funs_remove_batch`)
            pub fn remove_batch(backend: &crate::ctx::Ctx, names: &[String]) {
                backend.naming_funs_remove_batch(names)
            }

            /// `with_ctx_proxy_opt t ctx @@ fun () -> get_pos t name`: the
            /// backend's `get_fun_pos` (`NamingTableWithContext`).
            pub fn get_pos(backend: &Ctx, ctx: Option<CtxProxy>, name: &str) -> Option<file_info::Pos> {
                with_ctx_proxy_opt(ctx, |ctx| {
                    naming_table_with_context::find_symbol_in_context_with_suppression(
                        ctx,
                        |ctx| (ctx.find_fun_in_context)(name),
                        || match backend.reverse_naming_table_opt() {
                            Some(table) => table
                                .get_fun_pos(name)
                                .map(|pos| (pos.to_file_info(), NameType::Fun)),
                            None => store_result(
                                "Funs.get_pos",
                                name,
                                backend.shallow_decls.get_fun(FunName(crate::ctx::symbol(name))),
                            )
                            .map(|decl| {
                                (
                                    file_info::Pos::File(
                                        NameType::Fun,
                                        Arc::new(decl.pos.file().into()),
                                    ),
                                    NameType::Fun,
                                )
                            }),
                        },
                    )
                    .map(|(pos, _)| pos)
                })
            }

            /// `with_ctx_proxy_opt t ctx @@ fun () -> get_canon_name t name`
            pub fn get_canon_name(
                backend: &Ctx,
                ctx: Option<CtxProxy>,
                name: &str,
            ) -> Option<String> {
                with_ctx_proxy_opt(ctx, |ctx| {
                    naming_table_with_context::get_canon_name(
                        ctx,
                        |ctx| (ctx.find_fun_canon_name_in_context)(name),
                        || {
                            backend
                                .get_fun_canon_name(name)
                                .map(|name| name.as_str().to_string())
                                .or_else(|| canon_fallback(backend, name))
                        },
                    )
                })
            }
        }

        pub mod consts {
            use super::*;

            /// `add` (`hh_rust_provider_backend_naming_consts_add`)
            pub fn add(backend: &crate::ctx::Ctx, name: &str, pos: &file_info::Pos) {
                backend.naming_consts_add(name, pos)
            }

            /// `remove_batch` (`hh_rust_provider_backend_naming_consts_remove_batch`)
            pub fn remove_batch(backend: &crate::ctx::Ctx, names: &[String]) {
                backend.naming_consts_remove_batch(names)
            }

            /// `with_ctx_proxy_opt t ctx @@ fun () -> get_pos t name`: the
            /// backend's `get_const_pos` (`NamingTableWithContext`).
            pub fn get_pos(backend: &Ctx, ctx: Option<CtxProxy>, name: &str) -> Option<file_info::Pos> {
                with_ctx_proxy_opt(ctx, |ctx| {
                    naming_table_with_context::find_symbol_in_context_with_suppression(
                        ctx,
                        |ctx| (ctx.find_const_in_context)(name),
                        || match backend.reverse_naming_table_opt() {
                            Some(table) => table
                                .get_const_pos(name)
                                .map(|pos| (pos.to_file_info(), NameType::Const)),
                            None => store_result(
                                "Consts.get_pos",
                                name,
                                backend.shallow_decls.get_const(ConstName(crate::ctx::symbol(name))),
                            )
                            .map(|decl| {
                                (
                                    file_info::Pos::File(
                                        NameType::Const,
                                        Arc::new(decl.pos.file().into()),
                                    ),
                                    NameType::Const,
                                )
                            }),
                        },
                    )
                    .map(|(pos, _)| pos)
                })
            }
        }

        pub mod modules {
            use super::*;

            /// `add` (`hh_rust_provider_backend_naming_modules_add`)
            pub fn add(backend: &crate::ctx::Ctx, name: &str, pos: &file_info::Pos) {
                backend.naming_modules_add(name, pos)
            }

            /// `remove_batch` (`hh_rust_provider_backend_naming_modules_remove_batch`)
            pub fn remove_batch(backend: &crate::ctx::Ctx, names: &[String]) {
                backend.naming_modules_remove_batch(names)
            }

            /// `with_ctx_proxy_opt t ctx @@ fun () -> get_pos t name`: the
            /// backend's `get_module_pos` (`NamingTableWithContext`).
            pub fn get_pos(backend: &Ctx, ctx: Option<CtxProxy>, name: &str) -> Option<file_info::Pos> {
                with_ctx_proxy_opt(ctx, |ctx| {
                    naming_table_with_context::find_symbol_in_context_with_suppression(
                        ctx,
                        |ctx| (ctx.find_module_in_context)(name),
                        || match backend.reverse_naming_table_opt() {
                            Some(table) => table
                                .get_module_pos(name)
                                .map(|pos| (pos.to_file_info(), NameType::Module)),
                            None => store_result(
                                "Modules.get_pos",
                                name,
                                backend.shallow_decls.get_module(ModuleName(crate::ctx::symbol(name))),
                            )
                            .map(|decl| {
                                (
                                    file_info::Pos::File(
                                        NameType::Module,
                                        Arc::new(decl.pos.file().into()),
                                    ),
                                    NameType::Module,
                                )
                            }),
                        },
                    )
                    .map(|(pos, _)| pos)
                })
            }
        }

        /// This function searches all three namespaces (types, funs, consts) to
        /// find which one contains each Dep.t. The earlier functions in this module
        /// only search one specified namespace. Note: this function doesn't
        /// use the sharedmem cache of names - doesn't benefit from it, doesn't
        /// write into it.
        pub fn get_filenames_by_hash(
            backend: &Ctx,
            deps: &crate::typing_deps::dep_set::T,
        ) -> crate::relative_path::set::T {
            // (`hh_rust_provider_backend_naming_get_filenames_by_hash`)
            backend.naming_get_filenames_by_hash(deps)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use oxidized::typechecker_options::TypecheckerOptions;
    use relative_path::Prefix;

    use super::*;

    /// A context that declares one file, as `hh single` does.
    fn ctx_of(src: &str) -> Ctx {
        let ctx = crate::ctx::Ctx::new(Path::new("/"), TypecheckerOptions::default()).unwrap();
        let path = pos::RelativePath::new(pos::Prefix::Root, "test.php");
        ctx.files.set(path, src);
        let mut decl_paths = ctx.hhi_paths.clone();
        decl_paths.push(path);
        crate::check::declare_files(&ctx, &decl_paths, &mut crate::check::Stats::default());
        Arc::new(ctx)
    }

    fn test_php() -> RelativePath {
        RelativePath::make(Prefix::Root, "test.php".into())
    }

    #[test]
    fn names_of_the_declarations() {
        let ctx = ctx_of(
            "<?hh\nclass C {}\ntype T = int;\nfunction f(): void {}\nconst int K = 1;\nnew module m {}\n",
        );
        assert_eq!(get_class_path(&ctx, "\\C"), Some(test_php()));
        assert_eq!(get_typedef_path(&ctx, "\\C"), None);
        assert_eq!(get_typedef_path(&ctx, "\\T"), Some(test_php()));
        assert_eq!(get_type_kind(&ctx, "\\T"), Some(KindOfType::TTypedef));
        assert_eq!(get_type_kind(&ctx, "\\C"), Some(KindOfType::TClass));
        assert_eq!(get_type_kind(&ctx, "\\D"), None);
        assert_eq!(
            get_type_pos(&ctx, "\\C"),
            Some(file_info::Pos::File(NameType::Class, Arc::new(test_php())))
        );
        assert_eq!(get_fun_path(&ctx, "\\f"), Some(test_php()));
        assert!(fun_exists(&ctx, "\\f"));
        assert!(!fun_exists(&ctx, "\\g"));
        assert!(const_exists(&ctx, "\\K"));
        assert_eq!(get_const_path(&ctx, "\\K"), Some(test_php()));
        assert_eq!(get_module_path(&ctx, "m"), Some(test_php()));
        assert!(module_exists(&ctx, "default"));
        assert!(!module_exists(&ctx, "n"));
        assert_eq!(get_type_canon_name(&ctx, "\\c"), Some("\\C".to_string()));
        assert_eq!(get_fun_canon_name(&ctx, "\\F"), Some("\\f".to_string()));
        // `Exception` is declared by the hhi files.
        assert!(get_class_path(&ctx, "\\Exception").is_some());
        assert!(rust_backend_ctx_proxy(&ctx).is_none());
    }

    #[test]
    fn full_positions() {
        let ctx = ctx_of("<?hh\nclass C {}\n");
        let file = file_info::Pos::File(NameType::Fun, Arc::new(test_php()));
        assert_eq!(get_fun_full_pos_by_parsing_file(&ctx, (&file, "\\C")), None);
        let full = file_info::Pos::Full(Pos::NONE);
        assert_eq!(
            get_type_full_pos_by_parsing_file(&ctx, (&full, "\\C")),
            Some(Pos::NONE)
        );
        assert_eq!(resolve_position(&ctx, &Pos::NONE), Pos::NONE);
    }

    /// A context with entries: the backend looks at them first, through the
    /// proxy (`NamingTableWithContext`).
    #[test]
    fn names_of_the_entries() {
        let ctx = ctx_of("<?hh\nclass C {}\nfunction f(): void {}\n");
        // `test.php` as open in an editor: `C` is gone, `D` is new.
        let (ctx, _entry) = provider_context::add_or_overwrite_entry_contents(
            &ctx,
            test_php(),
            BString::from("<?hh\nclass D {}\nfunction f(): void {}\n"),
        );
        assert!(rust_backend_ctx_proxy(&ctx).is_some());
        // Only in the context.
        assert_eq!(get_class_path(&ctx, "\\D"), Some(test_php()));
        assert_eq!(get_type_kind(&ctx, "\\D"), Some(KindOfType::TClass));
        // The naming table has it in a file of the context, which does not
        // declare it.
        assert_eq!(get_class_path(&ctx, "\\C"), None);
        // In both: the position is the one of the context (`Full`).
        assert!(matches!(
            get_fun_pos(&ctx, "\\f"),
            Some(file_info::Pos::Full(_))
        ));
        assert_eq!(get_type_canon_name(&ctx, "\\d"), Some("\\D".to_string()));
        // Neither.
        assert_eq!(get_fun_path(&ctx, "\\g"), None);
    }
}
