// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_is_subtype.ml`. See `hh/PORTING.md`.
//!
//! `Multi_worker.call` is not used: the queries are all handled by `helper`.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::decl_entry;
use crate::file_content::position;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_env;
use crate::server_infer_type;
use crate::tast;
use crate::tast_with_dynamic;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_env_types::Env;
use crate::yojson::safe as yojson;

type Pos = (RelativePath, position::T);

enum TypeSpec {
    TSpos(Pos),
    TSjson(yojson::T),
}

enum Query {
    PosJson(Pos, yojson::T),
    JsonPos(yojson::T, Pos),
    JsonJson(yojson::T, yojson::T),
}

fn expand_path(file: &str) -> Result<String, String> {
    let path = crate::path::make(file);
    if crate::path::file_exists(&path) {
        Ok(crate::path::to_string(&path))
    } else {
        let cwd = std::env::current_dir().map(|d| d.to_string_lossy().into_owned()).unwrap_or_default();
        let file = crate::rt::ocaml_filename::concat(&cwd, file);
        let path = crate::path::make(&file);
        if crate::path::file_exists(&path) {
            Ok(crate::path::to_string(&path))
        } else {
            Err(format!("File not found: {}", file))
        }
    }
}

type TastMap = BTreeMap<RelativePath, tast_with_dynamic::T<tast::Program>>;

fn get_type_at_pos(ctx: &provider_context::T, tast_map: &TastMap, pos: &Pos) -> Result<(Env, Ty), String> {
    let (path, pos) = pos;
    // `Relative_path.Map.find tast_map path`
    let tast = match tast_map.get(path) {
        Some(tast) => tast,
        None => panic!("Not_found"),
    };
    match server_infer_type::type_at_pos(ctx, tast, pos) {
        Some(info) => Ok((
            server_infer_type::get_env(&info).clone(),
            server_infer_type::get_type(&info).clone(),
        )),
        None => Err(format!(
            "Failed to get type for pos {}:{}",
            relative_path::to_absolute(path),
            position::to_string_one_based(pos)
        )),
    }
}

fn validate_free_type(env: &Env, locl_ty: &Ty) -> Vec<String> {
    match get_node(locl_ty) {
        // notably, we don't validate arity of the type arguments
        // Extra args appear to be ignored when subtyping and
        // missing args only result in "true" if both types are missing that arg
        Ty_::Tclass(id, _exact, tyargs) => match crate::typing_env::get_class(env, &id.1) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                vec![format!("Unbound class name {}", id.1)]
            }
            decl_entry::T::Found(_) => validate_l(env, tyargs),
        },
        Ty_::Ttuple(t) => {
            let mut errs = validate_l(env, &t.required);
            errs.extend(validate_l(env, &t.optional));
            errs.extend(match &t.extra {
                TupleExtra::Tvariadic(t_variadic) => validate_free_type(env, t_variadic),
                TupleExtra::Tsplat(t_splat) => validate_free_type(env, t_splat),
            });
            errs
        }
        Ty_::Tunion(tyargs) | Ty_::Tintersection(tyargs) => validate_l(env, tyargs),
        Ty_::Toption(locl_ty) => validate_free_type(env, locl_ty),
        Ty_::Tnonnull | Ty_::Tdynamic(_) | Ty_::Tprim(_) | Ty_::Tany(_) => vec![],
        Ty_::TvecOrDict(kty, vty) => {
            let mut errs = validate_free_type(env, kty);
            errs.extend(validate_free_type(env, vty));
            errs
        }
        Ty_::Tfun(tfun) => {
            let params: Vec<Ty> = tfun.params.iter().map(|fp| fp.type_.clone()).collect();
            let mut errs = validate_l(env, &params);
            errs.extend(validate_free_type(env, &tfun.ret));
            errs
        }
        Ty_::Tshape(ShapeType::ShapeSimple(s)) => {
            let field_tys: Vec<Ty> = s.fields.values().map(|field| field.ty.clone()).collect();
            let mut errs = validate_free_type(env, &s.unknown_value);
            errs.extend(validate_l(env, &field_tys));
            errs
        }
        Ty_::Tshape(ShapeType::ShapeSplat(s)) => validate_l(env, &s.ss_elems),
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
            crate::typing_print::full(true, env, locl_ty)
        )],
    }
}

fn validate_l(env: &Env, locl_tyl: &[Ty]) -> Vec<String> {
    locl_tyl.iter().flat_map(|ty| validate_free_type(env, ty)).collect()
}

/// `Typing_env_types.empty ctx Relative_path.default ~droot:None`
fn empty_env(ctx: &provider_context::T) -> Env {
    crate::typing_env_types::empty(
        None,
        None,
        Arc::clone(ctx),
        Arc::new(relative_path::default.clone()),
        None,
    )
}

/// `show_deserialization_error` (`[@@deriving show]`)
fn show_deserialization_error(err: &oxidized::typing_defs::DeserializationError) -> String {
    use oxidized::typing_defs::DeserializationError as E;
    let (ctor, msg) = match err {
        E::WrongPhase(msg) => ("Wrong_phase", msg),
        E::NotSupported(msg) => ("Not_supported", msg),
        E::DeserializationError(msg) => ("Deserialization_error", msg),
    };
    format!("(Typing_defs.{} {})", ctor, crate::rt::ocaml_printf::sprintf_S(msg))
}

fn get_type_from_json(ctx: &provider_context::T, json: &yojson::T) -> Result<Ty, Vec<String>> {
    match crate::typing_json::to_locl_ty(Some(Default::default()), ctx, json) {
        Ok(locl_ty) => {
            let env = empty_env(ctx);
            let errl = validate_free_type(&env, &locl_ty);
            if errl.is_empty() { Ok(locl_ty) } else { Err(errl) }
        }
        Err(err) => Err(vec![show_deserialization_error(&err)]),
    }
}

/// `json |> member name` of `Yojson.Safe.Util` (`Null` for a missing member;
/// a `Type_error` for a value that is not an object).
fn member<'a>(name: &str, json: &'a yojson::T) -> &'a yojson::T {
    static NULL: yojson::T = yojson::T::Null;
    match json {
        yojson::T::Assoc(fields) => fields.iter().find(|(k, _)| k == name).map(|(_, v)| v).unwrap_or(&NULL),
        _ => panic!("Yojson.Safe.Util.Type_error(\"Can't get member '{}' of non-object type\")", name),
    }
}

/// `to_string_option`
fn to_string_option(json: &yojson::T) -> Option<String> {
    match json {
        yojson::T::String(s) => Some(s.clone()),
        yojson::T::Null => None,
        _ => panic!("Yojson.Safe.Util.Type_error(\"Expected string or null\")"),
    }
}

fn get_type_spec_from_json(json: &yojson::T) -> Result<TypeSpec, String> {
    match to_string_option(member("kind", json)) {
        None => Err("Missing or non-string 'kind' field".to_string()),
        Some(value) => match value.as_str() {
            "type" => match member("type", json) {
                yojson::T::Null => Err("Missing 'type' field".to_string()),
                type_json => Ok(TypeSpec::TSjson(type_json.clone())),
            },
            "pos" => match to_string_option(member("pos", json)) {
                None => Err("Missing or non-string 'pos' field".to_string()),
                Some(pos_str) => match pos_str.split(':').collect::<Vec<_>>().as_slice() {
                    [file, line, col] => {
                        let file = expand_path(file)?;
                        let path = relative_path::create_detect_prefix(&file);
                        let int_of_string = |s: &str| match crate::rt::ocaml_arg::int_of_string_opt(s) {
                            Some(i) => i,
                            None => panic!("Failure(\"int_of_string\")"),
                        };
                        let pos = position::from_one_based(int_of_string(line), int_of_string(col));
                        Ok(TypeSpec::TSpos((path, pos)))
                    }
                    _ => Err(format!(
                        "Position {} is malformed. Expected file:line:column",
                        pos_str
                    )),
                },
            },
            bad_kind => Err(format!("Unexpected kind {}", bad_kind)),
        },
    }
}

struct IsSubtypeResult {
    is_subtype: bool,
    ty_left: String,
    ty_right: String,
}

fn is_subtype(env: &Env, l_ty: &Ty, r_ty: &Ty) -> IsSubtypeResult {
    IsSubtypeResult {
        is_subtype: crate::typing_subtype::is_sub_type(env, l_ty, r_ty),
        ty_left: crate::typing_print::full(true, env, l_ty),
        ty_right: crate::typing_print::full(true, env, r_ty),
    }
}

/// `Result.combine a b ~ok ~err:(fun a b -> a @ b)`
fn combine<A, B, C>(
    a: Result<A, Vec<String>>,
    b: Result<B, Vec<String>>,
    ok: impl FnOnce(A, B) -> C,
) -> Result<C, Vec<String>> {
    match (a, b) {
        (Ok(a), Ok(b)) => Ok(ok(a, b)),
        (Err(a), Ok(_)) => Err(a),
        (Ok(_), Err(b)) => Err(b),
        (Err(mut a), Err(b)) => {
            a.extend(b);
            Err(a)
        }
    }
}

type ResultAlist = Vec<(usize, Result<IsSubtypeResult, Vec<String>>)>;

fn helper(
    acc: ResultAlist,
    ctx: &provider_context::T,
    query_with_path_alist: Vec<(usize, Option<RelativePath>, Query)>,
) -> ResultAlist {
    let paths: Vec<RelativePath> = query_with_path_alist
        .iter()
        .filter_map(|(_, path_opt, _)| path_opt.clone())
        .collect();
    let (ctx, tast_map) = crate::server_infer_type_batch::get_tast_map(ctx, &paths);
    let ctx = &ctx;
    let mut results: ResultAlist = query_with_path_alist
        .into_iter()
        .map(|(i, _path_opt, query)| {
            let result = match query {
                Query::JsonJson(json_l, json_r) => combine(
                    get_type_from_json(ctx, &json_l),
                    get_type_from_json(ctx, &json_r),
                    |l, r| {
                        let env = empty_env(ctx);
                        is_subtype(&env, &l, &r)
                    },
                ),
                Query::JsonPos(json, pos) => combine(
                    get_type_from_json(ctx, &json),
                    get_type_at_pos(ctx, &tast_map, &pos).map_err(|e| vec![e]),
                    |l, (env, r)| is_subtype(&env, &l, &r),
                ),
                Query::PosJson(pos, json) => combine(
                    get_type_at_pos(ctx, &tast_map, &pos).map_err(|e| vec![e]),
                    get_type_from_json(ctx, &json),
                    |(env, l), r| is_subtype(&env, &l, &r),
                ),
            };
            (i, result)
        })
        .collect();
    results.extend(acc);
    results
}

pub fn check(str: &str, env: &server_env::Env) -> Result<String, String> {
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let json = match yojson::from_string(str) {
        Ok(json) => json,
        Err(e) => return Err(format!("Invalid JSON input: {}", e.0)),
    };
    match json {
        yojson::T::List(json_l) => {
            let mut query_with_path_alist = vec![];
            let mut error_alist: ResultAlist = vec![];
            for (i, json) in json_l.iter().enumerate() {
                let pair: Result<(TypeSpec, TypeSpec), Vec<String>> = match json {
                    yojson::T::List(pair) if pair.len() == 2 => combine(
                        get_type_spec_from_json(&pair[0]).map_err(|e| vec![e]),
                        get_type_spec_from_json(&pair[1]).map_err(|e| vec![e]),
                        |l, r| (l, r),
                    ),
                    _ => Err(vec!["Expected JSON array of size 2".to_string()]),
                };
                match pair {
                    Ok((TypeSpec::TSpos(pos), TypeSpec::TSjson(json))) => {
                        query_with_path_alist.push((i, Some(pos.0.clone()), Query::PosJson(pos, json)))
                    }
                    Ok((TypeSpec::TSjson(json_l), TypeSpec::TSjson(json_r))) => {
                        query_with_path_alist.push((i, None, Query::JsonJson(json_l, json_r)))
                    }
                    Ok((TypeSpec::TSjson(json), TypeSpec::TSpos(pos))) => {
                        query_with_path_alist.push((i, Some(pos.0.clone()), Query::JsonPos(json, pos)))
                    }
                    Ok((TypeSpec::TSpos(_), TypeSpec::TSpos(_))) => error_alist.push((
                        i,
                        Err(vec!["Cannot provide a position for the both types".to_string()]),
                    )),
                    Err(e) => error_alist.push((i, Err(e))),
                }
            }
            // TODO: Should we removes duplicates of the same query?
            // Or somehow even avoid multiple type-at-pos lookups for positions
            // that appear in multiplle distinct queries?
            let mut result_alist = helper(vec![], &ctx, query_with_path_alist);
            result_alist.extend(error_alist);
            let mut result_map_by_i: BTreeMap<usize, Result<IsSubtypeResult, Vec<String>>> = BTreeMap::new();
            for (i, r) in result_alist {
                if result_map_by_i.insert(i, r).is_some() {
                    panic!("Map.of_alist_exn: duplicate key")
                }
            }
            let json_result_list: Vec<yojson::T> = (0..json_l.len())
                .map(|i| {
                    let res = result_map_by_i.get(&i).expect("Map.find_exn");
                    let (status, value) = match res {
                        Ok(is_subtype_result) => (
                            "ok",
                            yojson::T::Assoc(vec![
                                ("is_subtype".to_string(), yojson::T::Bool(is_subtype_result.is_subtype)),
                                ("left".to_string(), yojson::T::String(is_subtype_result.ty_left.clone())),
                                ("right".to_string(), yojson::T::String(is_subtype_result.ty_right.clone())),
                            ]),
                        ),
                        Err(l) => (
                            "errors",
                            yojson::T::List(l.iter().map(|s| yojson::T::String(s.clone())).collect()),
                        ),
                    };
                    yojson::T::Assoc(vec![(status.to_string(), value)])
                })
                .collect();
            Ok(yojson::to_string(&yojson::T::List(json_result_list)))
        }
        _ => Err("Expected JSON array".to_string()),
    }
}
