// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `shape_field_check.ml`. See `hh/PORTING.md`.

use bstr::BString;
use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::aast_utils;
use crate::lint;
use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::*;
use crate::typing_error;
use crate::typing_error::NothingOrUndefined;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_make_type;
/// `Reason` (`Typing_defs.Reason`, which is `Typing_reason`)
use crate::typing_reason as reason;

fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, msg.into()))
        .collect()
}

/// The status that [`shapes_key_exists`] returns: OCaml's ``[ `DoesExist of
/// Pos_or_decl.t | `DoesNotExist of Pos_or_decl.t * [ `Nothing of ... |
/// `Undefined ] | `Unknown ]``.
#[derive(Clone, Debug)]
enum KeyStatus {
    DoesExist(PosOrDecl),
    DoesNotExist(PosOrDecl, NothingOrUndefined),
    Unknown,
}

/// Returns the status `DoesExists, `DoesNotExist or `Unknown along with
/// a boolean to track if the shape was optional or not.
fn shapes_key_exists(env: &Env, shape: &Ty, field_name: &TshapeFieldName) -> (KeyStatus, bool) {
    let check = |env: &Env,
                 pos: PosOrDecl,
                 shape_kind: &Ty,
                 fields: &t_shape_map::T<ShapeFieldType>|
     -> KeyStatus {
        match fields.get(&t_shape_map::TShapeField(field_name.clone())) {
            None => {
                if is_nothing(shape_kind) {
                    KeyStatus::DoesNotExist(pos, NothingOrUndefined::Undefined)
                } else {
                    KeyStatus::Unknown
                }
            }
            Some(ShapeFieldType {
                optional: sft_optional,
                ty: sft_ty,
            }) => {
                if !*sft_optional {
                    KeyStatus::DoesExist(get_pos(sft_ty))
                } else {
                    let nothing = typing_make_type::nothing(reason::none());
                    if tast_env::is_sub_type(env, sft_ty, &nothing) {
                        let r = get_reason(sft_ty).clone();
                        KeyStatus::DoesNotExist(
                            pos,
                            NothingOrUndefined::Nothing(typing_error::Lazy::new(move || {
                                messages(reason::to_string("It is nothing", &r))
                            })),
                        )
                    } else {
                        KeyStatus::Unknown
                    }
                }
            }
        }
    };
    fn loop_(
        check: &dyn Fn(&Env, PosOrDecl, &Ty, &t_shape_map::T<ShapeFieldType>) -> KeyStatus,
        env: &mut Env,
        shape: Ty,
        was_optional: bool,
    ) -> (KeyStatus, bool) {
        let shape = tast_env::strip_dynamic(env, shape);
        let (_, shape) = tast_env::strip_supportdyn(env, shape);
        let shape = tast_env::expand_type(env, shape);
        match get_node(&shape) {
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value: shape_kind,
                fields,
            })) => (
                check(env, get_pos(&shape), shape_kind, fields),
                was_optional,
            ),
            Ty_::Tshape(ShapeType::ShapeSplat(_)) => (KeyStatus::Unknown, was_optional),
            Ty_::Toption(maybe_shape) => {
                let shape = tast_env::expand_type(env, maybe_shape.clone());
                loop_(check, env, shape, true)
            }
            _ => (KeyStatus::Unknown, was_optional),
        }
    }
    loop_(&check, &mut env.clone(), shape.clone(), false)
}

fn trivial_shapes_key_exists_check(pos1: &Pos, env: &Env, shape: &Ty, field_name: &PosByteString) {
    let (status, optional) =
        shapes_key_exists(env, shape, &TshapeFieldName::TSFlitStr(field_name.clone()));
    // Shapes::keyExists only supports non optional shapes, so an error
    // would already have been raised.
    if !optional {
        match status {
            KeyStatus::DoesExist(decl_pos) => typing_error_utils::add_typing_error(
                &typing_error::shape(primary::shape::T::Shapes_key_exists_always_true {
                    pos: pos1.clone(),
                    field_name: field_name.1.to_string(),
                    decl_pos,
                }),
                env,
            ),
            KeyStatus::DoesNotExist(decl_pos, reason) => typing_error_utils::add_typing_error(
                &typing_error::shape(primary::shape::T::Shapes_key_exists_always_false {
                    pos: pos1.clone(),
                    field_name: field_name.1.to_string(),
                    decl_pos,
                    reason,
                }),
                env,
            ),
            KeyStatus::Unknown => {}
        }
    }
}

fn shapes_method_access_with_non_existent_field(
    pos1: &Pos,
    env: &Env,
    method_name: &str,
    shape: &Ty,
    field_name: &PosByteString,
) {
    let (status, optional_shape) =
        shapes_key_exists(env, shape, &TshapeFieldName::TSFlitStr(field_name.clone()));
    match (status, optional_shape) {
        (KeyStatus::DoesExist(_), false) => {
            lint::shape_idx_access_required_field(pos1.clone(), &field_name.1.to_string())
        }
        (KeyStatus::DoesNotExist(decl_pos, reason), _) => typing_error_utils::add_typing_error(
            &typing_error::shape(
                primary::shape::T::Shapes_method_access_with_non_existent_field {
                    pos: pos1.clone(),
                    field_name: field_name.1.to_string(),
                    decl_pos,
                    method_name: method_name.to_string(),
                    reason,
                },
            ),
            env,
        ),
        (KeyStatus::DoesExist(_), true) | (KeyStatus::Unknown, _) => {}
    }
}

fn shape_access_with_non_existent_field(
    pos1: &Pos,
    env: &Env,
    shape: &Ty,
    field_name: &PosByteString,
) {
    let (status, optional) =
        shapes_key_exists(env, shape, &TshapeFieldName::TSFlitStr(field_name.clone()));
    match (status, optional) {
        (KeyStatus::DoesNotExist(decl_pos, reason), _) => typing_error_utils::add_typing_error(
            &typing_error::shape(primary::shape::T::Shapes_access_with_non_existent_field {
                pos: pos1.clone(),
                field_name: field_name.1.to_string(),
                decl_pos,
                reason,
            }),
            env,
        ),
        (KeyStatus::DoesExist(_), _) | (KeyStatus::Unknown, _) => {}
    }
}

fn dest_args<'a>(
    arg1: &'a tast::Argument,
    arg2: &'a tast::Argument,
) -> Option<(&'a Ty, &'a Pos, &'a BString)> {
    match (aast_utils::arg_to_expr(arg1), aast_utils::arg_to_expr(arg2)) {
        (aast::Expr(ty, _, _), aast::Expr(_, pos, aast::Expr_::String(field_name))) => {
            Some((ty, pos, field_name))
        }
        _ => None,
    }
}

/// The class name, the method name and the arguments of
/// `Call { func = (_, _, Class_const ((_, _, CI (_, class_name)), (_,
/// method_name))); args; unpacked_arg = None; _ }`.
fn class_const_call(call: &tast::CallExpr) -> Option<(&str, &str, &[tast::Argument])> {
    match call {
        aast::CallExpr {
            func: aast::Expr(_, _, aast::Expr_::ClassConst(cc)),
            args,
            unpacked_arg: None,
            ..
        } => match &**cc {
            (
                aast::ClassId(_, _, aast::ClassId_::CI(ast_defs::Id(_, class_name))),
                (_, method_name),
            ) => Some((class_name.as_str(), method_name.as_str(), args.as_slice())),
            _ => None,
        },
        _ => None,
    }
}

/// `let handler = object inherit Tast_visitor.handler_base ... end`
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        let aast::Expr(_, p, e_) = e;
        let class_const_call = match e_ {
            aast::Expr_::Call(call) => class_const_call(call),
            _ => None,
        };
        match (e_, class_const_call) {
            (_, Some((class_name, method_name, [arg1, arg2])))
                if class_name == sn::shapes::SHAPES && method_name == sn::shapes::KEY_EXISTS =>
            {
                match dest_args(arg1, arg2) {
                    Some((ty, pos, field_name)) => {
                        let mut env = env.clone();
                        let tyl =
                            tast_env::get_concrete_supertypes(None, false, &mut env, ty.clone());
                        let field =
                            PosByteString(pos_or_decl::of_raw_pos(pos.clone()), field_name.clone());
                        let trivial_shapes_key_exists_check =
                            |ty: &Ty| trivial_shapes_key_exists_check(p, &env, ty, &field);
                        tyl.iter().for_each(trivial_shapes_key_exists_check)
                    }
                    None => {}
                }
            }
            (_, Some((class_name, method_name, [arg1, arg2, _])))
            | (_, Some((class_name, method_name, [arg1, arg2])))
                if class_name == sn::shapes::SHAPES
                    && (method_name == sn::shapes::IDX || method_name == sn::shapes::AT) =>
            {
                match dest_args(arg1, arg2) {
                    Some((ty, pos, field_name)) => {
                        let mut env = env.clone();
                        let tyl =
                            tast_env::get_concrete_supertypes(None, false, &mut env, ty.clone());
                        let field =
                            PosByteString(pos_or_decl::of_raw_pos(pos.clone()), field_name.clone());
                        let shapes_method_access_with_non_existent_field = |ty: &Ty| {
                            shapes_method_access_with_non_existent_field(
                                pos,
                                &env,
                                method_name,
                                ty,
                                &field,
                            )
                        };
                        tyl.iter()
                            .for_each(shapes_method_access_with_non_existent_field)
                    }
                    None => {}
                }
            }
            (aast::Expr_::Binop(binop), _)
                if matches!(binop.bop, ast_defs::Bop::QuestionQuestion) =>
            {
                let exp = &binop.lhs;
                fn check_nested_accesses(env: &Env, p: &Pos, e: &tast::Expr) {
                    match e {
                        aast::Expr(_, _, aast::Expr_::ArrayGet(ag)) if ag.1.is_some() => {
                            let (exp, indexing_expr) = &**ag;
                            let indexing_expr = indexing_expr.as_ref().unwrap();
                            let aast::Expr(ty, _, _) = exp;
                            match indexing_expr {
                                aast::Expr(_, pos, aast::Expr_::String(field_name)) => {
                                    let mut env = env.clone();
                                    let tyl = tast_env::get_concrete_supertypes(
                                        None,
                                        false,
                                        &mut env,
                                        ty.clone(),
                                    );
                                    let field = PosByteString(
                                        pos_or_decl::of_raw_pos(pos.clone()),
                                        field_name.clone(),
                                    );
                                    let shape_access_with_non_existent_field = |ty: &Ty| {
                                        shape_access_with_non_existent_field(p, &env, ty, &field)
                                    };
                                    tyl.iter().for_each(shape_access_with_non_existent_field)
                                }
                                _ => {}
                            };
                            check_nested_accesses(env, p, exp)
                        }
                        _ => {}
                    }
                }
                check_nested_accesses(env, p, exp)
            }
            _ => {}
        }
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}
