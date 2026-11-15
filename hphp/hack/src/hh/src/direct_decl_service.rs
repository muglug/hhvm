// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/direct_decl_service.ml`: parse the decls of files in
//! parallel (rayon, for the OCaml's workers) and make their `File_info.t`;
//! with the parts of `providers/direct_decl_utils.ml` it calls
//! (`direct_decl_parse`, `direct_decl_parse_and_cache`, whose `cache_decls`
//! is `Ctx::add_shallow_decls`), and
//! `Direct_decl_parser.decls_to_fileinfo`.

use std::sync::Arc;

use bstr::BString;
use oxidized::direct_decl_parser::ParsedFileWithHashes;
use rayon::prelude::*;
use ty::decl::shallow::NamedDecl;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::file_info;
use crate::relative_path::RelativePath;

type RPMap<A> = crate::relative_path::map::T<A>;

/// `direct_decl_mode`: whether the decls parsed are also cached in the decl
/// stores.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DirectDeclMode {
    Normal,
    Cached,
}

/// `Direct_decl_utils.get_file_contents ~ignore_file_content_caches:false`
fn get_file_contents(ctx: &Arc<Ctx>, filename: &RelativePath) -> Option<BString> {
    match crate::naming_provider::get_entry_contents(ctx, filename) {
        Some(contents) => Some(contents),
        None => crate::file_provider::rust_provider_backend::file::get_contents(ctx, filename),
    }
}

/// `Direct_decl_utils.direct_decl_parse ctx file`
/// (`Direct_decl_parser.parse_and_hash_decls` with the options of the
/// context's parser).
pub fn direct_decl_parse(ctx: &Arc<Ctx>, file: &RelativePath) -> Option<ParsedFileWithHashes> {
    let contents = get_file_contents(ctx, file)?;
    Some(ctx.decl_parser.parse_impl(file.into(), &contents))
}

/// `Direct_decl_utils.direct_decl_parse_and_cache ctx file` (`Shared_memory`
/// branch: `direct_decl_parse`, then `cache_decls`, which is
/// [`Ctx::add_shallow_decls`]).
pub fn direct_decl_parse_and_cache(
    ctx: &Arc<Ctx>,
    file: &RelativePath,
) -> Option<ParsedFileWithHashes> {
    let contents = get_file_contents(ctx, file)?;
    let path: pos::RelativePath = file.into();
    let hashed_file = ctx.decl_parser.parse_impl(path, &contents);
    ctx.add_shallow_decls(
        path,
        hashed_file
            .iter()
            .map(|(name, decl, _)| NamedDecl::from((name.clone(), decl.clone())))
            .collect(),
    );
    Some(hashed_file)
}

/// `Direct_decl_parser.decls_to_fileinfo fn parsed_file`: the ids in
/// lexical order, at the positions of their decls, with the hashes.
pub fn decls_to_fileinfo(fn_: &RelativePath, parsed_file: &ParsedFileWithHashes) -> file_info::T {
    use oxidized::shallow_decl_defs::Decl;
    let _ = fn_;
    let mut ids = file_info::empty_ids();
    for (name, decl, hash) in parsed_file.iter() {
        let pos = |p: &oxidized::pos_or_decl::PosOrDecl| file_info::Pos::Full(p.clone());
        let info = |pos| file_info::Id {
            pos,
            name: name.clone(),
            decl_hash: Some(hash.as_u64() as i64),
        };
        match decl {
            Decl::Class(c) => ids.classes.push(info(pos(&c.name.0))),
            Decl::Fun(f) => ids.funs.push(info(pos(&f.pos))),
            Decl::Typedef(tf) => ids.typedefs.push(info(pos(&tf.pos))),
            Decl::Const(c) => ids.consts.push(info(pos(&c.pos))),
            Decl::Module(m) => ids.modules.push(info(pos(&m.mdt_pos))),
        }
    }
    file_info::T {
        ids,
        position_free_decl_hash: file_info::HashType(Some(parsed_file.file_decls_hash.as_u64() as i64)),
        file_mode: parsed_file.mode,
        comments: None,
    }
}

/// The `File_info.t` of the decls of a file as `Ctx::declare_file` gets
/// them (hackrs decls, in lexical order): what [`decls_to_fileinfo`] gives,
/// without the hashes, which these decls do not have (`decl_hash` and
/// `position_free_decl_hash` are `None`; nothing the daemon does reads
/// them: they are for saved states).
pub fn file_info_of_decls(
    path: pos::RelativePath,
    decls: &[NamedDecl<R>],
    mode: Option<file_info::Mode>,
) -> file_info::T {
    let _ = path;
    let mut ids = file_info::empty_ids();
    for decl in decls {
        let info = |name: &str, pos: &pos::BPos| file_info::Id {
            pos: file_info::Pos::Full(pos.clone().into()),
            name: name.to_string(),
            decl_hash: None,
        };
        match decl {
            NamedDecl::Class(name, c) => ids.classes.push(info(name.as_str(), c.name.pos())),
            NamedDecl::Fun(name, f) => ids.funs.push(info(name.as_str(), &f.pos)),
            NamedDecl::Typedef(name, tf) => ids.typedefs.push(info(name.as_str(), &tf.pos)),
            NamedDecl::Const(name, c) => ids.consts.push(info(name.as_str(), &c.pos)),
            NamedDecl::Module(name, m) => ids.modules.push(info(name.as_str(), &m.pos)),
        }
    }
    file_info::T {
        ids,
        position_free_decl_hash: file_info::HashType(None),
        file_mode: mode,
        comments: None,
    }
}

/// `parse ctx ~trace ~decl_mode acc fn`, without the accumulator.
fn parse(
    ctx: &Arc<Ctx>,
    trace: bool,
    decl_mode: DirectDeclMode,
    fn_: &RelativePath,
) -> Option<(RelativePath, file_info::T)> {
    if !crate::find_utils::path_filter(fn_) {
        None
    } else {
        let start_parse_time = crate::rt::ocaml_unix::gettimeofday();
        let parsed_file_opt = match decl_mode {
            DirectDeclMode::Normal => direct_decl_parse(ctx, fn_),
            DirectDeclMode::Cached => direct_decl_parse_and_cache(ctx, fn_),
        };
        match parsed_file_opt {
            None => None,
            Some(parsed_file) => {
                let end_parse_time = crate::rt::ocaml_unix::gettimeofday();
                let fileinfo = decls_to_fileinfo(fn_, &parsed_file);
                if trace {
                    crate::hh_logger::log(&format!(
                        "[{:.1}ms] {} - {}",
                        (end_parse_time - start_parse_time) * 1000.0,
                        crate::relative_path::suffix(fn_),
                        file_info::to_string(&fileinfo)
                    ));
                }
                Some((fn_.clone(), fileinfo))
            }
        }
    }
}

/// `Direct_decl_service.go ctx ~trace ~decl_mode workers ~get_next`: the
/// files are parsed on the rayon pool (the OCaml's workers), and the
/// results merged into one map.
pub fn go(
    ctx: &Arc<Ctx>,
    files: &[RelativePath],
    trace: bool,
    decl_mode: DirectDeclMode,
) -> RPMap<file_info::T> {
    // On the workers when the process has some (`Multi_worker.call workers
    // ~job:parse_batch ~merge ~next`).
    #[cfg(feature = "server")]
    {
        return crate::multi_worker::call_service::<ParseBatchJob, _>(
            ctx,
            (trace, decl_mode == DirectDeclMode::Cached),
            files,
            |out: Vec<(RelativePath, file_info::T)>, mut acc: RPMap<file_info::T>| {
                acc.extend(out);
                acc
            },
            RPMap::new(),
            || false,
            |_| go_threads(ctx, files, trace, decl_mode),
        );
    }
    #[cfg(not(feature = "server"))]
    go_threads(ctx, files, trace, decl_mode)
}

/// The job of [`go`] on the workers: `parse_batch`.
#[cfg(feature = "server")]
pub struct ParseBatchJob;

#[cfg(feature = "server")]
impl crate::multi_worker::ServiceJob for ParseBatchJob {
    const NAME: &'static str = "Direct_decl_service.parse_batch";
    /// `trace`, and whether the decls are cached.
    type Params = (bool, bool);
    type Item = RelativePath;
    type Output = Vec<(RelativePath, file_info::T)>;
    fn run(ctx: &Arc<Ctx>, (trace, cached): &(bool, bool), files: Vec<RelativePath>) -> Self::Output {
        let decl_mode = if *cached { DirectDeclMode::Cached } else { DirectDeclMode::Normal };
        files.iter().filter_map(|fn_| parse(ctx, *trace, decl_mode, fn_)).collect()
    }
}

/// [`go`] on the threads of the pool.
fn go_threads(
    ctx: &Arc<Ctx>,
    files: &[RelativePath],
    trace: bool,
    decl_mode: DirectDeclMode,
) -> RPMap<file_info::T> {
    let parsed: Vec<(RelativePath, file_info::T)> = files
        .par_iter()
        .filter_map(|fn_| parse(ctx, trace, decl_mode, fn_))
        .collect();
    parsed.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;

    #[test]
    fn file_infos() {
        // (`Find_utils.path_filter` strips the root.)
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, Path::new("/nonexistent"));
        let ctx = Arc::new(Ctx::new(Path::new("/nonexistent"), TypecheckerOptions::default()).unwrap());
        let a = crate::relative_path::from_root("a.php");
        let src = "<?hh\nfunction f(): void {}\nclass C {}\ntype T = int;\nconst int K = 1;\nclass D {}\nnew module m {}\n";
        ctx.files.set((&a).into(), src);
        let infos = go(&ctx, &[a.clone(), crate::relative_path::from_root("gone.php")], false, DirectDeclMode::Normal);
        let fi = infos.get(&a).unwrap();
        let names = |ids: &[file_info::Id]| ids.iter().map(|id| id.name.clone()).collect::<Vec<_>>();
        assert_eq!(names(&fi.ids.classes), vec!["\\C", "\\D"]);
        assert_eq!(names(&fi.ids.funs), vec!["\\f"]);
        assert_eq!(names(&fi.ids.typedefs), vec!["\\T"]);
        assert_eq!(names(&fi.ids.consts), vec!["\\K"]);
        assert_eq!(names(&fi.ids.modules), vec!["m"]);
        assert!(fi.position_free_decl_hash.0.is_some());
        assert_eq!(fi.file_mode, Some(file_info::Mode::Mstrict));
        // A file that does not exist reads as "" (`File_provider`), which
        // declares nothing.
        let gone = infos.get(&crate::relative_path::from_root("gone.php")).unwrap();
        assert_eq!(gone.ids, file_info::empty_ids());
        // The same ids, positions and order from the hackrs decls.
        let decls = ctx.decl_parser.parse((&a).into()).unwrap();
        let fi2 = file_info_of_decls((&a).into(), &decls, fi.file_mode);
        assert_eq!(fi2.ids.classes.iter().map(|id| &id.pos).collect::<Vec<_>>(), fi.ids.classes.iter().map(|id| &id.pos).collect::<Vec<_>>());
        assert_eq!(names(&fi2.ids.classes), names(&fi.ids.classes));
        assert_eq!(fi2.ids.funs[0].pos, fi.ids.funs[0].pos);
        assert_eq!(fi2.ids.modules[0].pos, fi.ids.modules[0].pos);
    }
}
