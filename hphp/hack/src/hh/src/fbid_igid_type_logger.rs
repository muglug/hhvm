// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `fbid_igid_type_logger.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::aast::Expr;
use oxidized::ast_defs::Tprim;

use crate::aast_defs;
use crate::aast_utils;
use crate::ctx::Ctx;
use crate::hh_logger;
use crate::pos;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs::mk;
use crate::typing_make_type as tm;
use crate::typing_reason as tr;
use crate::typing_utils;
use crate::yojson::safe as yojson;

pub fn name(ty: &Ty) -> String {
    match get_node(ty) {
        Ty_::Tnewtype(s, _, _) => s.clone(),
        Ty_::Tprim(tp) => aast_defs::string_of_tprim(*tp),
        _ => "".to_string(),
    }
}

pub fn is_int(ty: &Ty) -> bool {
    typing_defs::is_prim(Tprim::Tint, ty)
}

pub fn is_igid_of_meta_ent_instagram_user(env: &Env, ty: &Ty) -> bool {
    let bound = tm::mixed(tr::none());
    let meta_ent_instagram_user =
        tm::class_type(tr::none(), "\\IMETAEntInstagramUser".to_string(), vec![]);
    let in_igid_range = tm::class_type(tr::none(), "\\InIGIDRange".to_string(), vec![]);
    let base_igid = mk((
        tr::none(),
        Ty_::Tnewtype(
            "\\BaseIGID".to_string(),
            vec![meta_ent_instagram_user, in_igid_range],
            bound,
        ),
    ));
    tast_env::is_sub_type(env, ty, &base_igid)
}

pub fn is_fbid_of_meta_ent_instagram_user(env: &Env, ty: &Ty) -> bool {
    let bound = tm::mixed(tr::none());
    let meta_ent_instagram_user =
        tm::class_type(tr::none(), "\\IMETAEntInstagramUser".to_string(), vec![]);
    let in_fbid_range = tm::class_type(tr::none(), "\\IN_FBID_RANGE".to_string(), vec![]);
    let fbid_forbids_zero = tm::class_type(tr::none(), "\\FBID_FORBIDS_ZERO".to_string(), vec![]);
    let base_fbid = mk((
        tr::none(),
        Ty_::Tnewtype(
            "\\BaseFBID".to_string(),
            vec![meta_ent_instagram_user, in_fbid_range, fbid_forbids_zero],
            bound,
        ),
    ));
    tast_env::is_sub_type(env, ty, &base_fbid)
}

/// BaseFBID<
///   IGEntMedia,
///   IN_OID_RANGE,
///   FBID_FORBIDS_ZERO
/// >
pub fn is_fbid_or_igid_of_media_id(env: &Env, ty: &Ty) -> bool {
    let bound = tm::mixed(tr::none());
    let media_ent = tm::class_type(tr::none(), "\\IGEntMedia".to_string(), vec![]);
    let in_oid_range = tm::class_type(tr::none(), "\\IN_OID_RANGE".to_string(), vec![]);
    let fbid_forbids_zero = tm::class_type(tr::none(), "\\FBID_FORBIDS_ZERO".to_string(), vec![]);
    let base_media_id = mk((
        tr::none(),
        Ty_::Tnewtype(
            "\\BaseFBID".to_string(),
            vec![media_ent, in_oid_range, fbid_forbids_zero],
            bound,
        ),
    ));
    tast_env::is_sub_type(env, ty, &base_media_id)
}

pub fn log_json(
    env: &Env,
    kind: &str,
    message: &str,
    arg_ty: &Ty,
    param_ty: &Ty,
    param_name: &Option<String>,
    pos: &pos::Absolute,
) {
    // The elements of the list are evaluated right to left, as in OCaml.
    let pos_json = pos::json(pos);
    let param_type = tast_env::ty_to_json(env, None, param_ty);
    let full_param_text = format!(
        "{} {}",
        name(param_ty),
        param_name.as_deref().unwrap_or("None")
    );
    let arg_type = tast_env::ty_to_json(env, None, arg_ty);
    let json = yojson::T::Assoc(vec![
        (
            "message".to_string(),
            yojson::T::String(message.to_string()),
        ),
        ("kind".to_string(), yojson::T::String(kind.to_string())),
        ("arg_type".to_string(), arg_type),
        (
            "full_param_text".to_string(),
            yojson::T::String(full_param_text),
        ),
        ("param_type".to_string(), param_type),
        ("pos".to_string(), pos_json),
    ]);
    // unsorted: telemetry/logging, not snapshot-tested
    hh_logger::log(&format!(
        "[FBID_IGID_type_logger] {}",
        yojson::to_string(&json)
    ))
}

pub fn check_args(env: &Env, params: &[(Option<String>, Ty)], args: &[Ty], pos: &pos::Absolute) {
    fn loop_(env: &Env, p: &[(Option<String>, Ty)], a: &[Ty], pos: &pos::Absolute) {
        match (p, a) {
            ([], _) => {}
            (_, []) => {}
            ([_, param_tail @ ..], [arg_ty, arg_tail @ ..])
                if typing_utils::is_dynamic(env, arg_ty) =>
            {
                // Skip dynamic types as they're likely false positives
                loop_(env, param_tail, arg_tail, pos)
            }
            ([(param_name, param_ty), param_tail @ ..], [arg_ty, arg_tail @ ..])
                if is_int(param_ty) && is_igid_of_meta_ent_instagram_user(env, arg_ty) =>
            {
                log_json(
                    env,
                    "IGID",
                    "IGID type erasure detected, is this an IGID or an FBID? How will you know?",
                    arg_ty,
                    param_ty,
                    param_name,
                    pos,
                );
                loop_(env, param_tail, arg_tail, pos)
            }
            ([(param_name, param_ty), param_tail @ ..], [arg_ty, arg_tail @ ..])
                if is_int(param_ty) && is_fbid_of_meta_ent_instagram_user(env, arg_ty) =>
            {
                log_json(
                    env,
                    "FBID",
                    "FBID type erasure detected, is this an IGID or an FBID? How will you know?",
                    arg_ty,
                    param_ty,
                    param_name,
                    pos,
                );
                loop_(env, param_tail, arg_tail, pos)
            }
            ([(param_name, param_ty), param_tail @ ..], [arg_ty, arg_tail @ ..])
                if is_int(param_ty) && is_fbid_or_igid_of_media_id(env, arg_ty) =>
            {
                log_json(
                    env,
                    "MediaID",
                    "MediaID type weakening detected",
                    arg_ty,
                    param_ty,
                    param_name,
                    pos,
                );
                loop_(env, param_tail, arg_tail, pos)
            }
            ([_, param_tail @ ..], [_, arg_tail @ ..]) => loop_(env, param_tail, arg_tail, pos),
        }
    }
    loop_(env, params, args, pos)
}

/// The handler of `create_handler`.
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    #[allow(non_snake_case)]
    fn at_Call(&mut self, env: &Env, call: &'a tast::CallExpr) {
        let tast::CallExpr {
            func: Expr(fx_ty, pos, _),
            args,
            ..
        } = call;
        let extract_param_types = |param: &typing_defs::FunParam| -> Ty { param.type_.clone() };
        let extract_arg_types = |arg_exp: &tast::Argument| -> Ty {
            tast::get_type(aast_utils::arg_to_expr(arg_exp)).clone()
        };
        let check = |(_, ft): (tr::T, std::rc::Rc<typing_defs::FunType>)| {
            let param_names_and_types: Vec<(Option<String>, Ty)> = ft
                .params
                .iter()
                .map(|p| (p.name.clone(), extract_param_types(p)))
                .collect();
            let arg_types: Vec<Ty> = args.iter().map(|a| extract_arg_types(a)).collect();
            check_args(
                env,
                &param_names_and_types,
                &arg_types,
                &pos::to_relative_string(pos),
            )
        };
        if let Some(x) = tast_env::get_underlying_function_type(env, fx_ty.clone()) {
            check(x)
        }
    }
}

pub fn create_handler<'a>(_ctx: &Arc<Ctx>) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
