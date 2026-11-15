// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.File_info` (`write_symbol_info/file_info.ml`).

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use md5::Digest;
use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::pos::Pos;
use parser_core_types::positioned_syntax::PositionedSyntax;

use super::indexable;
use super::predicate::Failure;
use super::sym_def;
use super::sym_hash::Md5;
use crate::ast_provider;
use crate::decl_entry;
use crate::folded_class;
use crate::full_fidelity_source_text;
use crate::hh_logger;
use crate::identify_symbol_service;
use crate::provider_context;
use crate::relative_path;
use crate::symbol_occurrence;
use crate::tast;
use crate::tast_env;
use crate::tast_provider;
use crate::typing_env;

#[derive(Clone, Debug)]
pub struct Symbol {
    pub occ: symbol_occurrence::T<Pos>,
    pub def: Option<sym_def::T>,
}

#[derive(Clone, Debug)]
pub struct Container {
    pub name: String,
    pub kind: ast_defs::ClassishKind,
}

#[derive(Clone, Debug)]
pub struct Member {
    pub name: String,
}

/// (The lists are built by consing in the OCaml, and so here: their
/// elements are in the OCaml's order.)
#[derive(Clone, Debug)]
pub struct MemberCluster {
    pub container: Container,
    pub methods: Vec<Member>,
    pub properties: Vec<Member>,
    pub class_constants: Vec<Member>,
    pub type_constants: Vec<Member>,
}

/// [fanout] flag is used in incremental mode. It identifies files which are
/// unchanged compared to the base db. Such files don't need to be re-indexed
/// if an identical [sym_hash] exists on the base db. [sym_hash] captures the
/// file path and elements of this [File_info.t] which may be invalidated
/// when *other* files are changed
/// (e.g. referenced symbols, inherited members)
pub struct T {
    /// path to be used in the glean index
    pub path: String,
    pub cst: std::sync::Arc<PositionedSyntax>,
    pub tast: Vec<(tast::Def, Vec<MemberCluster>)>,
    pub source_text: full_fidelity_source_text::T,
    pub symbols: Vec<Symbol>,
    pub sym_hash: Option<Md5>,
    pub fanout: bool,
    pub root_path: String,
}

/// `Md5.digest_string`
pub fn md5_digest_string(s: &[u8]) -> Md5 {
    md5::Md5::digest(s).into()
}

fn concat_hash(str: &str, hash: &Md5) -> Md5 {
    let mut s = hash.to_vec();
    s.extend_from_slice(str.as_bytes());
    md5_digest_string(&s)
}

/// TODO we hash the string representation of the symbol types. We
/// should move a more robust scheme and make sure this is enough to
/// identify files which need reindexing
fn compute_sym_hash(symbols: &[Symbol], init: Md5) -> Md5 {
    let mut cur = init;
    for Symbol { occ, def } in symbols {
        let full_name = def.as_ref().map(sym_def::show).unwrap_or_default();
        let str = format!(
            "{}{}{}",
            occ.name,
            symbol_occurrence::show_kind(&occ.type_),
            full_name
        );
        cur = concat_hash(&str, &cur);
    }
    cur
}

fn compute_member_clusters_hash(hash: Md5, member_clusters: &[MemberCluster]) -> Md5 {
    let hash_container = |hash: &Md5, c: &Container| {
        let kind = crate::format::asprintf(|f| {
            let unit = |_: &mut crate::format::Formatter, _: &()| ();
            let mut p = crate::ast_show::P::new(f, &unit, &unit);
            crate::ast_show::ast_defs::pp_classish_kind(&mut p, &c.kind)
        });
        concat_hash(&c.name, &concat_hash(&kind, hash))
    };
    let hash_member_cluster = |hash: &Md5, mc: &MemberCluster| {
        let members = mc
            .methods
            .iter()
            .chain(mc.properties.iter())
            .chain(mc.class_constants.iter())
            .chain(mc.type_constants.iter());
        let mut hash = hash_container(hash, &mc.container);
        for m in members {
            hash = concat_hash(&m.name, &hash)
        }
        hash
    };
    let mut hash = hash;
    for mc in member_clusters {
        hash = hash_member_cluster(&hash, mc)
    }
    hash
}

/// We fetch the class for things that are already found in the decl store. So
/// it should never be the case that the decl doesn't exist.
fn get_class_exn(tast_env: &tast_env::Env, class_name: &str) -> Result<folded_class::T, Failure> {
    decl_entry::to_option(typing_env::get_class(tast_env, class_name)).ok_or_else(|| {
        Failure(format!(
            "Impossible happened. {} does not have a decl",
            class_name
        ))
    })
}

/// Use the folded decl of a container definition (class/interface/trait) to
/// collect inherited members of that definition. Particularly, we collect
/// methods, properties, class constants, and type constants.
fn collect_inherited_members(
    ctx: &provider_context::T,
    tast_def: tast::Def,
) -> Result<(tast::Def, Vec<MemberCluster>), Failure> {
    let def = tast_def;
    let tast_env = tast_env::def_env(ctx, &def);
    let empty_member_cluster = |container: Container| MemberCluster {
        container,
        methods: vec![],
        properties: vec![],
        type_constants: vec![],
        class_constants: vec![],
    };
    // `S_map`: the clusters by the name of their container.
    let update_member_cluster = |add: &dyn Fn(Member, &mut MemberCluster),
                                 name: &str,
                                 origin: &str,
                                 mcs: &mut BTreeMap<String, MemberCluster>|
     -> Result<(), Failure> {
        let origin_decl = get_class_exn(&tast_env, origin)?;
        let kind = folded_class::kind(&origin_decl);
        let container = Container {
            name: origin.to_string(),
            kind,
        };
        let mc = mcs
            .entry(container.name.clone())
            .or_insert_with(|| empty_member_cluster(container));
        add(
            Member {
                name: name.to_string(),
            },
            mc,
        );
        Ok(())
    };
    // All enums/enum classes inherit the same members which CodeHub currently
    // doesn't index (and is not particularly interesting), so we're only
    // interested in container definitions: classes, interfaces, and traits.
    let has_proper_inherited_members = |c: &tast::Class_| match c.kind {
        ast_defs::ClassishKind::Cclass(_) | ast_defs::ClassishKind::Cinterface | ast_defs::ClassishKind::Ctrait => {
            true
        }
        ast_defs::ClassishKind::Cenum | ast_defs::ClassishKind::CenumClass(_) => false,
    };
    let inherited_member_clusters = |def: &tast::Def| -> Result<Vec<MemberCluster>, Failure> {
        match def {
            aast::Def::Class(class_) if has_proper_inherited_members(class_) => {
                let class_name = &class_.name.1;
                let class_decl = get_class_exn(&tast_env, class_name)?;
                // Collect members indexed by their origin
                let mut mcs: BTreeMap<String, MemberCluster> = BTreeMap::new();
                let add_method = |m: Member, mc: &mut MemberCluster| mc.methods.insert(0, m);
                for (name, elt) in folded_class::methods(&class_decl)
                    .into_iter()
                    .chain(folded_class::smethods(&class_decl))
                {
                    let origin = &elt.ce_origin;
                    // Skip if not inherited
                    if origin != class_name {
                        update_member_cluster(&add_method, &name, origin, &mut mcs)?
                    }
                }
                let add_property = |p: Member, mc: &mut MemberCluster| mc.properties.insert(0, p);
                for (name, elt) in folded_class::props(&class_decl)
                    .into_iter()
                    .chain(folded_class::sprops(&class_decl))
                {
                    let origin = &elt.ce_origin;
                    // Skip if not inherited
                    if origin != class_name {
                        update_member_cluster(&add_property, &name, origin, &mut mcs)?
                    }
                }
                let mut type_constants = BTreeSet::new();
                let add_type_constant = |tc: Member, mc: &mut MemberCluster| mc.type_constants.insert(0, tc);
                for (name, elt) in folded_class::typeconsts(&class_decl) {
                    let origin = elt.origin.as_str();
                    // Skip if not inherited
                    if origin != class_name {
                        update_member_cluster(&add_type_constant, &name, origin, &mut mcs)?;
                        type_constants.insert(name);
                    }
                }
                let add_class_constant = |cc: Member, mc: &mut MemberCluster| mc.class_constants.insert(0, cc);
                for (name, elt) in typing_env::consts(&tast_env, &class_decl) {
                    let origin = elt.origin.as_str();
                    // Skip if
                    //   - not inherited
                    //   - `::class` which is a "synthesised" member that exists in
                    //      every class
                    //   - is a type constant (we already collected those separately
                    if origin == class_name || name == sn::members::M_CLASS || type_constants.contains(&name) {
                    } else {
                        update_member_cluster(&add_class_constant, &name, origin, &mut mcs)?
                    }
                }
                // `S_map.values`: in decreasing order of the names.
                Ok(mcs.into_values().rev().collect())
            }
            _ => Ok(vec![]),
        }
    };
    let index_inherited_members = ctx.tco.symbol_write_index_inherited_members;
    let inherited_member_clusters = if index_inherited_members {
        inherited_member_clusters(&def)?
    } else {
        vec![]
    };
    Ok((def, inherited_member_clusters))
}

/// `create` (before it is wrapped by `create_or_file_too_big`).
fn create_(
    ctx: &provider_context::T,
    indexable: &indexable::T,
    gen_sym_hash: bool,
    root_path: &str,
    hhi_path: &str,
) -> Result<T, Failure> {
    let indexable::T { path, fanout } = indexable;
    let start_time = std::time::Instant::now();
    let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
    let path_str = relative_path::to_absolute_with_prefix(
        // (`Path.make_unsafe`)
        std::path::Path::new(root_path),
        std::path::Path::new(hhi_path),
        path,
    );
    let source_text = ast_provider::compute_source_text(&entry);
    // (`Full_fidelity_source_text.make`, in `compute_source_text`, resets the
    // global state of `Line_break_map`: see `Util.NamespacePos`. The OCaml
    // also looks up the positions of the syntax errors of the file in it,
    // as it parses: not emulated, see the report.)
    super::util::line_break_map::reset_global_state();
    let tast_provider::ComputeTast { tast, .. } = tast_provider::compute_tast_unquarantined(&ctx, &entry);
    let tast = tast.under_normal_assumptions;
    let tast_elapsed_s = start_time.elapsed().as_secs_f64();
    if tast_elapsed_s >= 240. {
        // `Unix.gmtime tast_elapsed_s`: the minutes and seconds of the hour.
        let secs = tast_elapsed_s as u64;
        hh_logger::log(&format!("tast: {} {}m{}s", path_str, (secs / 60) % 60, secs % 60));
    }
    let (_, cst) = ast_provider::compute_cst(&entry);
    // Compute all symbol occurrences in the file. Two passes:
    //   - Get SymbolOccurrrence.t values, repurposing `hh` SymbolService
    //   - Get missing information using `Sym_def.resolve`
    //
    // TODO: do it in one pass using a dedicated visitor
    let symbol_occs = identify_symbol_service::all_symbols(&ctx, &tast);
    let symbols: Vec<Symbol> = symbol_occs
        .into_iter()
        .map(|occ| {
            let def = sym_def::resolve(&ctx, &occ);
            Symbol { occ, def }
        })
        .collect();
    let tast = tast
        .into_iter()
        .map(|def| collect_inherited_members(&ctx, def))
        .collect::<Result<Vec<_>, _>>()?;
    let sym_hash = if gen_sym_hash {
        let init = compute_sym_hash(&symbols, md5_digest_string(path_str.as_bytes()));
        let mut h = init;
        for (_, member_clusters) in &tast {
            h = compute_member_clusters_hash(h, member_clusters)
        }
        Some(h)
    } else {
        None
    };
    Ok(T {
        path: path_str,
        tast,
        source_text,
        cst,
        symbols,
        sym_hash,
        fanout: *fanout,
        root_path: root_path.to_string(),
    })
}

const FILE_LIMIT_MB: u64 = 5;

const MB: u64 = 1024 * 1024;

const FILE_LIMIT_BYTES: u64 = FILE_LIMIT_MB * MB;

fn file_too_big_or_error(path: &relative_path::T) -> bool {
    match std::fs::metadata(relative_path::to_absolute(path)) {
        Ok(m) => m.len() >= FILE_LIMIT_BYTES,
        Err(_) => true,
    }
}

/// If [gen_sym_hash] is true, computes the [sym_hash] for this file. This
/// is needed for incremental indexing, when indexing bases, or increments.
/// If [gen_references] is true, computes the path of all referenced symbols.
///
/// (`create_or_file_too_big`, which the OCaml names `create`.)
pub fn create(
    ctx: &provider_context::T,
    indexable: &indexable::T,
    gen_sym_hash: bool,
    root_path: &str,
    hhi_path: &str,
) -> Result<Option<T>, Failure> {
    if file_too_big_or_error(&indexable.path) {
        hh_logger::log(&format!(
            "Skipping file {} because it is greater than {} MB",
            indexable.path.path_str(),
            FILE_LIMIT_MB
        ));
        Ok(None)
    } else {
        Ok(Some(create_(ctx, indexable, gen_sym_hash, root_path, hhi_path)?))
    }
}

/// all the root (i.e. non-hhi) files referenced by t through xrefs.
pub fn referenced(ctx: &provider_context::T, t: &T) -> BTreeSet<String> {
    let path = |sym: &Symbol| -> Option<String> {
        let def = sym.def.as_ref()?;
        match sym_def::filename(ctx, def) {
            Some(path) if relative_path::is_root(path.prefix()) => Some(relative_path::to_absolute(&path)),
            _ => None,
        }
    };
    t.symbols.iter().filter_map(path).collect()
}
