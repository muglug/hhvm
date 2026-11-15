// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_is_subtype.ml`.
//!
//! `Yojson.Safe.Util.member` and `to_string_option` raise `Type_error` on
//! JSON of the wrong shape, an exception the OCaml does not catch: here a
//! panic with the same message.

use std::sync::Arc;

use crate::ctx::Ctx;
use crate::decl_entry;
use crate::file_content::position;
use crate::format;
use crate::provider_utils;
use crate::relative_path;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_printf;
use crate::server_env;
use crate::server_infer_type;
use crate::server_infer_type_batch;
use crate::tast;
use crate::tast_with_dynamic;
use crate::typing_defs::DeserializationError;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_env;
use crate::typing_env_types;
use crate::typing_print;
use crate::typing_subtype;
use crate::yojson::safe as yojson;

pub type Pos = (relative_path::T, position::T);

pub enum TypeSpec {
    TSpos(Pos),
    TSjson(yojson::T),
}

pub enum Query {
    PosJson(Pos, yojson::T),
    JsonPos(yojson::T, Pos),
    JsonJson(yojson::T, yojson::T),
}

fn expand_path(file: &str) -> Result<String, String> {
    let path = crate::path::make(file);
    if crate::path::file_exists(&path) {
        Ok(crate::path::to_string(&path))
    } else {
        let cwd = std::env::current_dir()
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_default();
        let file = ocaml_filename::concat(&cwd, file);
        let path = crate::path::make(&file);
        if crate::path::file_exists(&path) {
            Ok(crate::path::to_string(&path))
        } else {
            Err(format!("File not found: {}", file))
        }
    }
}

fn get_type_at_pos(
    ctx: &Arc<Ctx>,
    tast_map: &relative_path::map::T<tast_with_dynamic::T<tast::Program>>,
    pos: &Pos,
) -> Result<(typing_env_types::Env, Ty), String> {
    let (path, pos) = pos;
    let tast = match tast_map.get(path) {
        Some(tast) => tast,
        None => panic!("Not_found"),
    };
    match server_infer_type::type_at_pos(ctx, tast, pos) {
        Some(info) => Ok((
            server_infer_type::get_env(&info).clone(),
            server_infer_type::get_type(&info).clone(),
        )),
        _ => Err(format!(
            "Failed to get type for pos {}:{}",
            relative_path::to_absolute(path),
            position::to_string_one_based(pos)
        )),
    }
}

/// Returns list of error strings
fn validate_free_type(env: &typing_env_types::Env, locl_ty: &Ty) -> Vec<String> {
    match get_node(locl_ty) {
        // notably, we don't validate arity of the type arguments
        // Extra args appear to be ignored when subtyping and
        // missing args only result in "true" if both types are missing that arg
        Ty_::Tclass(pos_id, _exact, tyargs) => {
            let class_id = &pos_id.1;
            match typing_env::get_class(env, class_id) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                    vec![format!("Unbound class name {}", class_id)]
                }
                decl_entry::T::Found(_) => validate_l(env, tyargs),
            }
        }
        Ty_::Ttuple(TupleType {
            required,
            optional,
            extra,
        }) => {
            let mut l = validate_l(env, required);
            l.extend(validate_l(env, optional));
            l.extend(match extra {
                TupleExtra::Tvariadic(t_variadic) => validate_free_type(env, t_variadic),
                TupleExtra::Tsplat(t_splat) => validate_free_type(env, t_splat),
            });
            l
        }
        Ty_::Tunion(tyargs) | Ty_::Tintersection(tyargs) => validate_l(env, tyargs),
        Ty_::Toption(locl_ty) => validate_free_type(env, locl_ty),
        Ty_::Tnonnull | Ty_::Tdynamic(_) | Ty_::Tprim(_) | Ty_::Tany(_) => vec![],
        Ty_::TvecOrDict(kty, vty) => {
            let mut l = validate_free_type(env, kty);
            l.extend(validate_free_type(env, vty));
            l
        }
        Ty_::Tfun(tfun) => {
            let tys: Vec<Ty> = tfun.params.iter().map(|fp| fp.type_.clone()).collect();
            let mut l = validate_l(env, &tys);
            l.extend(validate_free_type(env, &tfun.ret));
            l
        }
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            unknown_value,
            fields: fm,
            ..
        })) => {
            let field_tys: Vec<Ty> = fm.values().map(|field| field.ty.clone()).collect();
            let mut l = validate_free_type(env, unknown_value);
            l.extend(validate_l(env, &field_tys));
            l
        }
        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => validate_l(env, ss_elems),
        Ty_::Tnewtype(_name, tyargs, _) => validate_l(env, tyargs),
        Ty_::TclassPtr(ty) => validate_free_type(env, ty),
        // These aren't even created by Typing_json.to_locl_ty
        Ty_::Tneg(_)
        | Ty_::Tvar(_)
        | Ty_::Taccess(_)
        | Ty_::Tdependent(..)
        // Unsupported b/c relative/erroneous
        | Ty_::Tlabel(_)
        | Ty_::Tgeneric(_) => vec![format!(
            "Unsupported free type {}",
            typing_print::full(true, env, locl_ty)
        )],
    }
}

fn validate_l(env: &typing_env_types::Env, locl_tyl: &[Ty]) -> Vec<String> {
    locl_tyl
        .iter()
        .flat_map(|ty| validate_free_type(env, ty))
        .collect()
}

/// `show_deserialization_error` (`[@@deriving show]`)
fn show_deserialization_error(e: &DeserializationError) -> String {
    let (ctor, s) = match e {
        DeserializationError::WrongPhase(s) => ("Typing_defs.Wrong_phase", s),
        DeserializationError::NotSupported(s) => ("Typing_defs.Not_supported", s),
        DeserializationError::DeserializationError(s) => ("Typing_defs.Deserialization_error", s),
    };
    format::asprintf(|fmt| {
        // "(@[<2>Ctor@ %S@])"
        format::pp_print_string(fmt, "(");
        format::pp_open_box(fmt, 2);
        format::pp_print_string(fmt, ctor);
        format::pp_print_space(fmt);
        format::pp_print_string(fmt, &ocaml_printf::sprintf_s(s));
        format::pp_close_box(fmt);
        format::pp_print_string(fmt, ")");
    })
}

fn empty_env(ctx: &Arc<Ctx>) -> typing_env_types::Env {
    typing_env_types::empty(None, None, Arc::clone(ctx), Arc::new(relative_path::DEFAULT), None)
}

fn get_type_from_json(ctx: &Arc<Ctx>, json: &yojson::T) -> Result<Ty, Vec<String>> {
    let locl_ty = crate::typing_json::to_locl_ty(Some(vec![]), ctx, json);
    match locl_ty {
        Ok(locl_ty) => {
            let env = empty_env(ctx);
            let errl = validate_free_type(&env, &locl_ty);
            if errl.is_empty() { Ok(locl_ty) } else { Err(errl) }
        }
        Err(err) => Err(vec![show_deserialization_error(&err)]),
    }
}

/// `Yojson.Safe.Util.member name js`
fn member<'j>(name: &str, js: &'j yojson::T) -> &'j yojson::T {
    match js {
        yojson::T::Assoc(l) => match l.iter().find(|(k, _)| k == name) {
            Some((_, v)) => v,
            None => &yojson::T::Null,
        },
        js => panic!(
            "Yojson.Safe.Util.Type_error(\"Can't get member '{}' of non-object type {}\")",
            name,
            crate::yojson::safe::util::typeof_(js)
        ),
    }
}

/// `Yojson.Safe.Util.to_string_option js`
fn to_string_option(js: &yojson::T) -> Option<&str> {
    match js {
        yojson::T::String(s) => Some(s),
        yojson::T::Null => None,
        js => panic!(
            "Yojson.Safe.Util.Type_error(\"Expected string or null, got {}\")",
            crate::yojson::safe::util::typeof_(js)
        ),
    }
}

/// `int_of_string` (raises `Failure "int_of_string"`), with the panic payload
/// `Printexc.to_string` gives, as the other exceptions of this module.
fn int_of_string(s: &str) -> isize {
    match crate::rt::ocaml_stdlib::int_of_string_opt(s) {
        Some(i) => i,
        None => panic!("Failure(\"int_of_string\")"),
    }
}

fn get_type_spec_from_json(json: &yojson::T) -> Result<TypeSpec, String> {
    match to_string_option(member("kind", json)) {
        None => Err("Missing or non-string 'kind' field".to_string()),
        Some(value) => match value {
            "type" => match member("type", json) {
                yojson::T::Null => Err("Missing 'type' field".to_string()),
                type_json => Ok(TypeSpec::TSjson(type_json.clone())),
            },
            "pos" => match to_string_option(member("pos", json)) {
                None => Err("Missing or non-string 'pos' field".to_string()),
                Some(pos_str) => {
                    // `String.split ~on:':'`
                    let parts: Vec<&str> = pos_str.split(':').collect();
                    match parts[..] {
                        [file, line, col] => match expand_path(file) {
                            Ok(file) => {
                                let path = relative_path::create_detect_prefix(&file);
                                let pos = position::from_one_based(int_of_string(line), int_of_string(col));
                                Ok(TypeSpec::TSpos((path, pos)))
                            }
                            Err(e) => Err(e),
                        },
                        _ => Err(format!(
                            "Position {} is malformed. Expected file:line:column",
                            pos_str
                        )),
                    }
                }
            },
            bad_kind => Err(format!("Unexpected kind {}", bad_kind)),
        },
    }
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct IsSubtypeResult {
    pub is_subtype: bool,
    pub ty_left: String,
    pub ty_right: String,
}

fn is_subtype(env: &typing_env_types::Env, l_ty: &Ty, r_ty: &Ty) -> IsSubtypeResult {
    IsSubtypeResult {
        is_subtype: typing_subtype::is_sub_type(env, l_ty, r_ty),
        ty_left: typing_print::full(true, env, l_ty),
        ty_right: typing_print::full(true, env, r_ty),
    }
}

/// `Result.combine a b ~ok ~err`
fn combine<A, B, C, E>(
    a: Result<A, E>,
    b: Result<B, E>,
    ok: impl FnOnce(A, B) -> C,
    err: impl FnOnce(E, E) -> E,
) -> Result<C, E> {
    match (a, b) {
        (Ok(a), Ok(b)) => Ok(ok(a, b)),
        (Err(a), Err(b)) => Err(err(a, b)),
        (Err(e), Ok(_)) | (Ok(_), Err(e)) => Err(e),
    }
}

fn concat(mut a: Vec<String>, b: Vec<String>) -> Vec<String> {
    a.extend(b);
    a
}

type QueryWithPath = (usize, Option<relative_path::T>, Query);

fn helper(
    acc: Vec<(usize, Result<IsSubtypeResult, Vec<String>>)>,
    ctx: &Arc<Ctx>,
    query_with_path_alist: &[QueryWithPath],
) -> Vec<(usize, Result<IsSubtypeResult, Vec<String>>)> {
    let (ctx, tast_map) = {
        let paths: Vec<relative_path::T> = query_with_path_alist
            .iter()
            .filter_map(|(_, path_opt, _)| path_opt.clone())
            .collect();
        server_infer_type_batch::get_tast_map(ctx, &paths)
    };
    let mut res: Vec<(usize, Result<IsSubtypeResult, Vec<String>>)> = query_with_path_alist
        .iter()
        .map(|(i, _path_opt, query)| {
            let result = match query {
                Query::JsonJson(json_l, json_r) => combine(
                    get_type_from_json(&ctx, json_l),
                    get_type_from_json(&ctx, json_r),
                    |l, r| {
                        let env = empty_env(&ctx);
                        is_subtype(&env, &l, &r)
                    },
                    concat,
                ),
                Query::JsonPos(json, pos) => combine(
                    get_type_from_json(&ctx, json),
                    get_type_at_pos(&ctx, &tast_map, pos).map_err(|e| vec![e]),
                    |l, (env, r)| is_subtype(&env, &l, &r),
                    concat,
                ),
                Query::PosJson(pos, json) => combine(
                    get_type_at_pos(&ctx, &tast_map, pos).map_err(|e| vec![e]),
                    get_type_from_json(&ctx, json),
                    |(env, l), r| is_subtype(&env, &l, &r),
                    concat,
                ),
            };
            (*i, result)
        })
        .collect();
    res.extend(acc);
    res
}

/// `parallel_helper workers ctx query_with_path_alist`: the queries with a
/// path, by file, then those without one, in buckets (see
/// `Server_infer_type_batch.multi_worker_call_rev_append`). The order of the
/// results does not matter: they are put back in the order of the queries.
fn parallel_helper(
    num_workers: isize,
    ctx: &Arc<Ctx>,
    query_with_path_alist: Vec<QueryWithPath>,
) -> Vec<(usize, Result<IsSubtypeResult, Vec<String>>)> {
    let (some, none): (Vec<_>, Vec<_>) = query_with_path_alist
        .into_iter()
        .partition(|(_, path_opt, _)| path_opt.is_some());
    let mut by_file: relative_path::map::T<Vec<usize>> = relative_path::map::T::new();
    for (k, (_, path_opt, _)) in some.iter().enumerate() {
        let path = path_opt.clone().unwrap();
        match by_file.get_mut(&path) {
            None => {
                by_file.insert(path, vec![k]);
            }
            Some(others) => others.insert(0, k),
        }
    }
    let mut some: Vec<Option<QueryWithPath>> = some.into_iter().map(Some).collect();
    // (`Relative_path.Map.values`: decreasing order of the keys.)
    let mut groups: Vec<Vec<QueryWithPath>> = by_file
        .into_iter()
        .rev()
        .map(|(_, ks)| ks.into_iter().map(|k| some[k].take().unwrap()).collect())
        .collect();
    groups.push(none);
    let groups: Vec<Vec<SerQueryWithPath>> =
        groups.into_iter().map(|g| g.into_iter().map(ser_query_with_path).collect()).collect();
    let buckets = {
        let mut next = crate::bucket::make_list(num_workers, None, None, groups);
        let mut buckets = vec![];
        loop {
            let bucket = next();
            if bucket.is_empty() {
                // `Hh_bucket.Done`
                break;
            }
            buckets.push(bucket);
        }
        buckets
    };
    crate::multi_worker::call_service_buckets::<IsSubtypeJob, _>(
        ctx,
        (),
        buckets,
        // `List.rev_append`
        |res: Vec<(usize, Result<IsSubtypeResult, Vec<String>>)>, acc| {
            let mut merged: Vec<_> = res.into_iter().rev().collect();
            merged.extend(acc);
            merged
        },
        vec![],
        |buckets, acc| {
            // (The threads of the master, without workers.)
            use rayon::prelude::*;
            let results: Vec<Vec<_>> = buckets
                .into_par_iter()
                .map(|bucket| {
                    crate::rt::decl_epoch::sync_thread();
                    IsSubtypeJob::run_bucket(ctx, bucket)
                })
                .collect();
            results.into_iter().fold(acc, |acc, res| {
                let mut merged: Vec<_> = res.into_iter().rev().collect();
                merged.extend(acc);
                merged
            })
        },
    )
}

/// A query as the job's input carries it: the JSON as its text (the OCaml
/// marshals the `Yojson.Safe.t`; the text is parsed again in the clone).
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub enum SerQuery {
    PosJson(Pos, String),
    JsonPos(String, Pos),
    JsonJson(String, String),
}

pub type SerQueryWithPath = (usize, Option<relative_path::T>, SerQuery);

fn ser_query_with_path((i, path, query): QueryWithPath) -> SerQueryWithPath {
    let text = |j: &yojson::T| yojson::to_string(j);
    let query = match query {
        Query::PosJson(pos, json) => SerQuery::PosJson(pos, text(&json)),
        Query::JsonPos(json, pos) => SerQuery::JsonPos(text(&json), pos),
        Query::JsonJson(l, r) => SerQuery::JsonJson(text(&l), text(&r)),
    };
    (i, path, query)
}

fn de_query_with_path((i, path, query): SerQueryWithPath) -> QueryWithPath {
    let json = |t: &str| yojson::from_string(t).expect("Server_is_subtype: the JSON of a query");
    let query = match query {
        SerQuery::PosJson(pos, j) => Query::PosJson(pos, json(&j)),
        SerQuery::JsonPos(j, pos) => Query::JsonPos(json(&j), pos),
        SerQuery::JsonJson(l, r) => Query::JsonJson(json(&l), json(&r)),
    };
    (i, path, query)
}

/// The job of [`parallel_helper`] on the workers: `helper` on the queries of
/// a bucket of groups.
pub struct IsSubtypeJob;

impl IsSubtypeJob {
    fn run_bucket(
        ctx: &Arc<Ctx>,
        bucket: Vec<Vec<SerQueryWithPath>>,
    ) -> Vec<(usize, Result<IsSubtypeResult, Vec<String>>)> {
        let queries: Vec<QueryWithPath> = bucket.into_iter().flatten().map(de_query_with_path).collect();
        helper(vec![], ctx, &queries)
    }
}

impl crate::multi_worker::ServiceJob for IsSubtypeJob {
    const NAME: &'static str = "Server_is_subtype.helper";
    type Params = ();
    type Item = Vec<SerQueryWithPath>;
    type Output = Vec<(usize, Result<IsSubtypeResult, Vec<String>>)>;
    fn run(ctx: &Arc<Ctx>, (): &(), bucket: Vec<Vec<SerQueryWithPath>>) -> Self::Output {
        Self::run_bucket(ctx, bucket)
    }
}

pub fn check(num_workers: isize, str: &str, env: &server_env::Env) -> Result<String, String> {
    let ctx = provider_utils::ctx_from_server_env(env);
    match yojson::from_string(str) {
        Err(crate::yojson::JsonError(message)) => Err(format!("Invalid JSON input: {}", message)),
        Ok(yojson::T::List(json_l)) => {
            let spec_pair_result_alist: Vec<(usize, Result<(TypeSpec, TypeSpec), Vec<String>>)> = json_l
                .iter()
                .enumerate()
                .map(|(i, json)| {
                    let pair = match json {
                        yojson::T::List(l) if l.len() == 2 => {
                            let get_type_spec_from_json_with_el =
                                |json| get_type_spec_from_json(json).map_err(|e| vec![e]);
                            // (OCaml evaluates the arguments from the last one.)
                            let r = get_type_spec_from_json_with_el(&l[1]);
                            let l = get_type_spec_from_json_with_el(&l[0]);
                            combine(l, r, |l, r| (l, r), concat)
                        }
                        _ => Err(vec!["Expected JSON array of size 2".to_string()]),
                    };
                    (i, pair)
                })
                .collect();
            let mut query_with_path_alist: Vec<QueryWithPath> = vec![];
            let mut error_alist: Vec<(usize, Result<IsSubtypeResult, Vec<String>>)> = vec![];
            for (i, x) in spec_pair_result_alist {
                match x {
                    Ok((TypeSpec::TSpos(pos), TypeSpec::TSjson(json))) => {
                        let path = pos.0.clone();
                        query_with_path_alist.push((i, Some(path), Query::PosJson(pos, json)))
                    }
                    Ok((TypeSpec::TSjson(json_l), TypeSpec::TSjson(json_r))) => {
                        query_with_path_alist.push((i, None, Query::JsonJson(json_l, json_r)))
                    }
                    Ok((TypeSpec::TSjson(json), TypeSpec::TSpos(pos))) => {
                        let path = pos.0.clone();
                        query_with_path_alist.push((i, Some(path), Query::JsonPos(json, pos)))
                    }
                    Ok((TypeSpec::TSpos(_), TypeSpec::TSpos(_))) => error_alist.push((
                        i,
                        Err(vec!["Cannot provide a position for the both types".to_string()]),
                    )),
                    Err(e) => error_alist.push((i, Err(e))),
                }
            }
            let num_files = query_with_path_alist
                .iter()
                .filter_map(|(_, path_opt, _)| path_opt.clone())
                .collect::<std::collections::BTreeSet<_>>()
                .len();
            // TODO: Should we removes duplicates of the same query?
            // Or somehow even avoid multiple type-at-pos lookups for positions
            // that appear in multiplle distinct queries?
            let result_alist = if num_files < 10 {
                helper(vec![], &ctx, &query_with_path_alist)
            } else {
                parallel_helper(num_workers, &ctx, query_with_path_alist)
            };
            let mut result_map_by_i: std::collections::BTreeMap<usize, Result<IsSubtypeResult, Vec<String>>> =
                std::collections::BTreeMap::new();
            for (i, r) in result_alist.into_iter().chain(error_alist) {
                // `Int.Map.of_alist_exn`
                if result_map_by_i.insert(i, r).is_some() {
                    panic!("Map.of_alist_exn: duplicate key");
                }
            }
            let json_result_list: Vec<yojson::T> = (0..json_l.len())
                .map(|i| {
                    let res = result_map_by_i.remove(&i).expect("Map.find_exn");
                    let (status, value) = match res {
                        Ok(is_subtype_result) => (
                            "ok",
                            yojson::T::Assoc(vec![
                                ("is_subtype".to_string(), yojson::T::Bool(is_subtype_result.is_subtype)),
                                ("left".to_string(), yojson::T::String(is_subtype_result.ty_left)),
                                ("right".to_string(), yojson::T::String(is_subtype_result.ty_right)),
                            ]),
                        ),
                        Err(l) => ("errors", yojson::T::List(l.into_iter().map(yojson::T::String).collect())),
                    };
                    yojson::T::Assoc(vec![(status.to_string(), value)])
                })
                .collect();
            Ok(yojson::to_string(&yojson::T::List(json_result_list)))
        }
        Ok(_) => Err("Expected JSON array".to_string()),
    }
}
